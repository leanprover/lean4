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
uint8_t l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken_beq(lean_object* v_x_384_, lean_object* v_x_385_){
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
LEAN_EXPORT void l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_384_ = stack[0].m_obj;
lean_object* v_x_385_ = stack[1].m_obj;
uint8_t v_res_398_;
v_res_398_ = l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken_beq(v_x_384_, v_x_385_);
stack->m_num = v_res_398_;
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
uint64_t l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken_hash(lean_object* v_x_405_){
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
LEAN_EXPORT void l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_405_ = stack[0].m_obj;
uint64_t v_res_419_;
v_res_419_ = l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken_hash(v_x_405_);
stack->m_num = v_res_419_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken_hash___boxed(lean_object* v_x_420_){
_start:
{
uint64_t v_res_421_; lean_object* v_r_422_; 
v_res_421_ = l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken_hash(v_x_420_);
lean_dec_ref(v_x_420_);
v_r_422_ = lean_box_uint64(v_res_421_);
return v_r_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__0(lean_object* v_j_425_, lean_object* v_k_426_){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = l_Lean_Json_getObjValD(v_j_425_, v_k_426_);
v___x_428_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__0___boxed(lean_object* v_j_429_, lean_object* v_k_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__0(v_j_429_, v_k_430_);
lean_dec_ref(v_k_430_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__1(lean_object* v_j_432_, lean_object* v_k_433_){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = l_Lean_Json_getObjValD(v_j_432_, v_k_433_);
v___x_435_ = l_Lean_Lsp_instFromJsonSemanticTokenType_fromJson(v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__1___boxed(lean_object* v_j_436_, lean_object* v_k_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__1(v_j_436_, v_k_437_);
lean_dec_ref(v_k_437_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__2(lean_object* v_j_439_, lean_object* v_k_440_){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = l_Lean_Json_getObjValD(v_j_439_, v_k_440_);
v___x_442_ = l_Lean_Json_getNat_x3f(v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__2___boxed(lean_object* v_j_443_, lean_object* v_k_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__2(v_j_443_, v_k_444_);
lean_dec_ref(v_k_444_);
return v_res_445_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__5(void){
_start:
{
uint8_t v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_455_ = 1;
v___x_456_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__4));
v___x_457_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_456_, v___x_455_);
return v___x_457_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_459_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__6));
v___x_460_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__5, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__5_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__5);
v___x_461_ = lean_string_append(v___x_460_, v___x_459_);
return v___x_461_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__9(void){
_start:
{
uint8_t v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_464_ = 1;
v___x_465_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__8));
v___x_466_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_465_, v___x_464_);
return v___x_466_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__10(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_467_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__9, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__9_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__9);
v___x_468_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7);
v___x_469_ = lean_string_append(v___x_468_, v___x_467_);
return v___x_469_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__12(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_471_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__11));
v___x_472_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__10, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__10_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__10);
v___x_473_ = lean_string_append(v___x_472_, v___x_471_);
return v___x_473_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__15(void){
_start:
{
uint8_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_477_ = 1;
v___x_478_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__14));
v___x_479_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_478_, v___x_477_);
return v___x_479_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__16(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_480_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__15, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__15_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__15);
v___x_481_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7);
v___x_482_ = lean_string_append(v___x_481_, v___x_480_);
return v___x_482_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__17(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_483_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__11));
v___x_484_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__16, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__16_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__16);
v___x_485_ = lean_string_append(v___x_484_, v___x_483_);
return v___x_485_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__19(void){
_start:
{
uint8_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = 1;
v___x_489_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__18));
v___x_490_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_489_, v___x_488_);
return v___x_490_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__20(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_491_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__19, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__19_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__19);
v___x_492_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7);
v___x_493_ = lean_string_append(v___x_492_, v___x_491_);
return v___x_493_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__21(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_494_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__11));
v___x_495_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__20, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__20_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__20);
v___x_496_ = lean_string_append(v___x_495_, v___x_494_);
return v___x_496_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__24(void){
_start:
{
uint8_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_500_ = 1;
v___x_501_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__23));
v___x_502_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_501_, v___x_500_);
return v___x_502_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__25(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_503_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__24, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__24_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__24);
v___x_504_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7);
v___x_505_ = lean_string_append(v___x_504_, v___x_503_);
return v___x_505_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__26(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_506_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__11));
v___x_507_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__25, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__25_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__25);
v___x_508_ = lean_string_append(v___x_507_, v___x_506_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson(lean_object* v_json_509_){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__0));
lean_inc(v_json_509_);
v___x_511_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__0(v_json_509_, v___x_510_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_521_; 
lean_dec(v_json_509_);
v_a_512_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_521_ == 0)
{
v___x_514_ = v___x_511_;
v_isShared_515_ = v_isSharedCheck_521_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_511_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_521_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_516_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__12, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__12_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__12);
v___x_517_ = lean_string_append(v___x_516_, v_a_512_);
lean_dec(v_a_512_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_517_);
v___x_519_ = v___x_514_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
else
{
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_dec(v_json_509_);
v_a_522_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_511_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_511_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
lean_ctor_set_tag(v___x_524_, 0);
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
else
{
lean_object* v_a_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v_a_530_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_530_);
lean_dec_ref_known(v___x_511_, 1);
v___x_531_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__13));
lean_inc(v_json_509_);
v___x_532_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__0(v_json_509_, v___x_531_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_542_; 
lean_dec(v_a_530_);
lean_dec(v_json_509_);
v_a_533_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_542_ == 0)
{
v___x_535_ = v___x_532_;
v_isShared_536_ = v_isSharedCheck_542_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_532_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_542_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_537_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__17, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__17_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__17);
v___x_538_ = lean_string_append(v___x_537_, v_a_533_);
lean_dec(v_a_533_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v___x_538_);
v___x_540_ = v___x_535_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
else
{
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
lean_dec(v_a_530_);
lean_dec(v_json_509_);
v_a_543_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_532_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_532_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
lean_ctor_set_tag(v___x_545_, 0);
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
else
{
lean_object* v_a_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v_a_551_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v___x_532_, 1);
v___x_552_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds___closed__5));
lean_inc(v_json_509_);
v___x_553_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__1(v_json_509_, v___x_552_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_563_; 
lean_dec(v_a_551_);
lean_dec(v_a_530_);
lean_dec(v_json_509_);
v_a_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_563_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_563_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_563_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_558_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__21, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__21_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__21);
v___x_559_ = lean_string_append(v___x_558_, v_a_554_);
lean_dec(v_a_554_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v___x_559_);
v___x_561_ = v___x_556_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
else
{
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
lean_dec(v_a_551_);
lean_dec(v_a_530_);
lean_dec(v_json_509_);
v_a_564_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_553_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_553_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
lean_ctor_set_tag(v___x_566_, 0);
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
else
{
lean_object* v_a_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v_a_572_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_572_);
lean_dec_ref_known(v___x_553_, 1);
v___x_573_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__22));
v___x_574_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__2(v_json_509_, v___x_573_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_584_; 
lean_dec(v_a_572_);
lean_dec(v_a_551_);
lean_dec(v_a_530_);
v_a_575_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_584_ == 0)
{
v___x_577_ = v___x_574_;
v_isShared_578_ = v_isSharedCheck_584_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_574_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_584_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
v___x_579_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__26, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__26_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__26);
v___x_580_ = lean_string_append(v___x_579_, v_a_575_);
lean_dec(v_a_575_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_580_);
v___x_582_ = v___x_577_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
else
{
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
lean_dec(v_a_572_);
lean_dec(v_a_551_);
lean_dec(v_a_530_);
v_a_585_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_574_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_574_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
lean_ctor_set_tag(v___x_587_, 0);
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_602_; 
v_a_593_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_602_ == 0)
{
v___x_595_ = v___x_574_;
v_isShared_596_ = v_isSharedCheck_602_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_574_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_602_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; uint8_t v___x_598_; lean_object* v___x_600_; 
v___x_597_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_597_, 0, v_a_530_);
lean_ctor_set(v___x_597_, 1, v_a_551_);
lean_ctor_set(v___x_597_, 2, v_a_593_);
v___x_598_ = lean_unbox(v_a_572_);
lean_dec(v_a_572_);
lean_ctor_set_uint8(v___x_597_, sizeof(void*)*3, v___x_598_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_597_);
v___x_600_ = v___x_595_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_597_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson_spec__0(lean_object* v_a_605_, lean_object* v_a_606_){
_start:
{
if (lean_obj_tag(v_a_605_) == 0)
{
lean_object* v___x_607_; 
v___x_607_ = lean_array_to_list(v_a_606_);
return v___x_607_;
}
else
{
lean_object* v_head_608_; lean_object* v_tail_609_; lean_object* v___x_610_; 
v_head_608_ = lean_ctor_get(v_a_605_, 0);
lean_inc(v_head_608_);
v_tail_609_ = lean_ctor_get(v_a_605_, 1);
lean_inc(v_tail_609_);
lean_dec_ref_known(v_a_605_, 2);
v___x_610_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_606_, v_head_608_);
v_a_605_ = v_tail_609_;
v_a_606_ = v___x_610_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson(lean_object* v_x_614_){
_start:
{
lean_object* v_pos_615_; lean_object* v_tailPos_616_; uint8_t v_type_617_; lean_object* v_priority_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v_pos_615_ = lean_ctor_get(v_x_614_, 0);
lean_inc_ref(v_pos_615_);
v_tailPos_616_ = lean_ctor_get(v_x_614_, 1);
lean_inc_ref(v_tailPos_616_);
v_type_617_ = lean_ctor_get_uint8(v_x_614_, sizeof(void*)*3);
v_priority_618_ = lean_ctor_get(v_x_614_, 2);
lean_inc(v_priority_618_);
lean_dec_ref(v_x_614_);
v___x_619_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__0));
v___x_620_ = l_Lean_Lsp_instToJsonPosition_toJson(v_pos_615_);
v___x_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_619_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = lean_box(0);
v___x_623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__13));
v___x_625_ = l_Lean_Lsp_instToJsonPosition_toJson(v_tailPos_616_);
v___x_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_624_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v___x_622_);
v___x_628_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds___closed__5));
v___x_629_ = l_Lean_Lsp_instToJsonSemanticTokenType_toJson(v_type_617_);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_628_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
lean_ctor_set(v___x_631_, 1, v___x_622_);
v___x_632_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__22));
v___x_633_ = l_Lean_JsonNumber_fromNat(v_priority_618_);
v___x_634_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_632_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
lean_ctor_set(v___x_636_, 1, v___x_622_);
v___x_637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v___x_622_);
v___x_638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_631_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_627_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_623_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = ((lean_object*)(l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson___closed__0));
v___x_642_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson_spec__0(v___x_640_, v___x_641_);
v___x_643_ = l_Lean_Json_mkObj(v___x_642_);
lean_dec(v___x_642_);
return v___x_643_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(lean_object* v_text_646_, lean_object* v_beginPos_647_, lean_object* v_endPos_x3f_648_, lean_object* v_as_649_, size_t v_i_650_, size_t v_stop_651_, lean_object* v_b_652_){
_start:
{
lean_object* v___y_654_; uint8_t v___x_658_; 
v___x_658_ = lean_usize_dec_eq(v_i_650_, v_stop_651_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; lean_object* v_stx_660_; uint8_t v_type_661_; lean_object* v_priority_662_; lean_object* v___x_663_; 
v___x_659_ = lean_array_uget_borrowed(v_as_649_, v_i_650_);
v_stx_660_ = lean_ctor_get(v___x_659_, 0);
v_type_661_ = lean_ctor_get_uint8(v___x_659_, sizeof(void*)*2);
v_priority_662_ = lean_ctor_get(v___x_659_, 1);
v___x_663_ = l_Lean_Syntax_getPos_x3f(v_stx_660_, v___x_658_);
if (lean_obj_tag(v___x_663_) == 0)
{
v___y_654_ = v_b_652_;
goto v___jp_653_;
}
else
{
lean_object* v_val_664_; lean_object* v___x_665_; 
v_val_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_val_664_);
lean_dec_ref_known(v___x_663_, 1);
v___x_665_ = l_Lean_Syntax_getTailPos_x3f(v_stx_660_, v___x_658_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_dec(v_val_664_);
v___y_654_ = v_b_652_;
goto v___jp_653_;
}
else
{
lean_object* v_val_666_; uint8_t v___y_668_; uint8_t v___x_676_; 
v_val_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_val_666_);
lean_dec_ref_known(v___x_665_, 1);
v___x_676_ = lean_nat_dec_le(v_beginPos_647_, v_val_664_);
if (v___x_676_ == 0)
{
lean_dec(v_val_666_);
lean_dec(v_val_664_);
v___y_654_ = v_b_652_;
goto v___jp_653_;
}
else
{
if (lean_obj_tag(v_endPos_x3f_648_) == 0)
{
v___y_668_ = v___x_676_;
goto v___jp_667_;
}
else
{
lean_object* v_val_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v_val_677_ = lean_ctor_get(v_endPos_x3f_648_, 0);
v___x_678_ = lean_unsigned_to_nat(1u);
v___x_679_ = lean_nat_add(v_val_664_, v___x_678_);
v___x_680_ = lean_nat_dec_le(v___x_679_, v_val_677_);
lean_dec(v___x_679_);
v___y_668_ = v___x_680_;
goto v___jp_667_;
}
}
v___jp_667_:
{
if (v___y_668_ == 0)
{
lean_dec(v_val_666_);
lean_dec(v_val_664_);
v___y_654_ = v_b_652_;
goto v___jp_653_;
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_669_ = lean_unsigned_to_nat(1u);
v___x_670_ = lean_nat_add(v_val_664_, v___x_669_);
v___x_671_ = lean_nat_dec_le(v___x_670_, v_val_666_);
lean_dec(v___x_670_);
if (v___x_671_ == 0)
{
lean_dec(v_val_666_);
lean_dec(v_val_664_);
v___y_654_ = v_b_652_;
goto v___jp_653_;
}
else
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
lean_inc_ref_n(v_text_646_, 2);
v___x_672_ = l_Lean_FileMap_utf8PosToLspPos(v_text_646_, v_val_664_);
lean_dec(v_val_664_);
v___x_673_ = l_Lean_FileMap_utf8PosToLspPos(v_text_646_, v_val_666_);
lean_dec(v_val_666_);
lean_inc(v_priority_662_);
v___x_674_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_674_, 0, v___x_672_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
lean_ctor_set(v___x_674_, 2, v_priority_662_);
lean_ctor_set_uint8(v___x_674_, sizeof(void*)*3, v_type_661_);
v___x_675_ = lean_array_push(v_b_652_, v___x_674_);
v___y_654_ = v___x_675_;
goto v___jp_653_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_text_646_);
return v_b_652_;
}
v___jp_653_:
{
size_t v___x_655_; size_t v___x_656_; 
v___x_655_ = ((size_t)1ULL);
v___x_656_ = lean_usize_add(v_i_650_, v___x_655_);
v_i_650_ = v___x_656_;
v_b_652_ = v___y_654_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_text_646_ = stack[0].m_obj;
lean_object* v_beginPos_647_ = stack[1].m_obj;
lean_object* v_endPos_x3f_648_ = stack[2].m_obj;
lean_object* v_as_649_ = stack[3].m_obj;
size_t v_i_650_ = stack[4].m_num;
size_t v_stop_651_ = stack[5].m_num;
lean_object* v_b_652_ = stack[6].m_obj;
lean_object* v_res_681_;
v_res_681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(v_text_646_, v_beginPos_647_, v_endPos_x3f_648_, v_as_649_, v_i_650_, v_stop_651_, v_b_652_);
stack->m_obj
 = v_res_681_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0___boxed(lean_object* v_text_682_, lean_object* v_beginPos_683_, lean_object* v_endPos_x3f_684_, lean_object* v_as_685_, lean_object* v_i_686_, lean_object* v_stop_687_, lean_object* v_b_688_){
_start:
{
size_t v_i_boxed_689_; size_t v_stop_boxed_690_; lean_object* v_res_691_; 
v_i_boxed_689_ = lean_unbox_usize(v_i_686_);
lean_dec(v_i_686_);
v_stop_boxed_690_ = lean_unbox_usize(v_stop_687_);
lean_dec(v_stop_687_);
v_res_691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(v_text_682_, v_beginPos_683_, v_endPos_x3f_684_, v_as_685_, v_i_boxed_689_, v_stop_boxed_690_, v_b_688_);
lean_dec_ref(v_as_685_);
lean_dec(v_endPos_x3f_684_);
lean_dec(v_beginPos_683_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0(lean_object* v_text_694_, lean_object* v_beginPos_695_, lean_object* v_endPos_x3f_696_, lean_object* v_as_697_, lean_object* v_start_698_, lean_object* v_stop_699_){
_start:
{
lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_700_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0___closed__0));
v___x_701_ = lean_nat_dec_lt(v_start_698_, v_stop_699_);
if (v___x_701_ == 0)
{
lean_dec_ref(v_text_694_);
return v___x_700_;
}
else
{
lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_702_ = lean_array_get_size(v_as_697_);
v___x_703_ = lean_nat_dec_le(v_stop_699_, v___x_702_);
if (v___x_703_ == 0)
{
uint8_t v___x_704_; 
v___x_704_ = lean_nat_dec_lt(v_start_698_, v___x_702_);
if (v___x_704_ == 0)
{
lean_dec_ref(v_text_694_);
return v___x_700_;
}
else
{
size_t v___x_705_; size_t v___x_706_; lean_object* v___x_707_; 
v___x_705_ = lean_usize_of_nat(v_start_698_);
v___x_706_ = lean_usize_of_nat(v___x_702_);
v___x_707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(v_text_694_, v_beginPos_695_, v_endPos_x3f_696_, v_as_697_, v___x_705_, v___x_706_, v___x_700_);
return v___x_707_;
}
}
else
{
size_t v___x_708_; size_t v___x_709_; lean_object* v___x_710_; 
v___x_708_ = lean_usize_of_nat(v_start_698_);
v___x_709_ = lean_usize_of_nat(v_stop_699_);
v___x_710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(v_text_694_, v_beginPos_695_, v_endPos_x3f_696_, v_as_697_, v___x_708_, v___x_709_, v___x_700_);
return v___x_710_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0___boxed(lean_object* v_text_711_, lean_object* v_beginPos_712_, lean_object* v_endPos_x3f_713_, lean_object* v_as_714_, lean_object* v_start_715_, lean_object* v_stop_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0(v_text_711_, v_beginPos_712_, v_endPos_x3f_713_, v_as_714_, v_start_715_, v_stop_716_);
lean_dec(v_stop_716_);
lean_dec(v_start_715_);
lean_dec_ref(v_as_714_);
lean_dec(v_endPos_x3f_713_);
lean_dec(v_beginPos_712_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(lean_object* v_text_718_, lean_object* v_beginPos_719_, lean_object* v_endPos_x3f_720_, lean_object* v_tokens_721_){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_722_ = lean_unsigned_to_nat(0u);
v___x_723_ = lean_array_get_size(v_tokens_721_);
v___x_724_ = l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0(v_text_718_, v_beginPos_719_, v_endPos_x3f_720_, v_tokens_721_, v___x_722_, v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens___boxed(lean_object* v_text_725_, lean_object* v_beginPos_726_, lean_object* v_endPos_x3f_727_, lean_object* v_tokens_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(v_text_725_, v_beginPos_726_, v_endPos_x3f_727_, v_tokens_728_);
lean_dec_ref(v_tokens_728_);
lean_dec(v_endPos_x3f_727_);
lean_dec(v_beginPos_726_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding_go(lean_object* v_s_738_, lean_object* v_x_739_){
_start:
{
if (lean_obj_tag(v_x_739_) == 0)
{
lean_object* v___x_740_; 
v___x_740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_740_, 0, v_s_738_);
lean_ctor_set(v___x_740_, 1, v_x_739_);
return v___x_740_;
}
else
{
lean_object* v_head_741_; lean_object* v_tail_742_; lean_object* v_tailPos_743_; lean_object* v_tailPos_744_; uint8_t v___x_745_; 
v_head_741_ = lean_ctor_get(v_x_739_, 0);
v_tail_742_ = lean_ctor_get(v_x_739_, 1);
v_tailPos_743_ = lean_ctor_get(v_s_738_, 1);
v_tailPos_744_ = lean_ctor_get(v_head_741_, 1);
v___x_745_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_743_, v_tailPos_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; 
v___x_746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_746_, 0, v_s_738_);
lean_ctor_set(v___x_746_, 1, v_x_739_);
return v___x_746_;
}
else
{
lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_754_; 
lean_inc(v_tail_742_);
lean_inc(v_head_741_);
v_isSharedCheck_754_ = !lean_is_exclusive(v_x_739_);
if (v_isSharedCheck_754_ == 0)
{
lean_object* v_unused_755_; lean_object* v_unused_756_; 
v_unused_755_ = lean_ctor_get(v_x_739_, 1);
lean_dec(v_unused_755_);
v_unused_756_ = lean_ctor_get(v_x_739_, 0);
lean_dec(v_unused_756_);
v___x_748_ = v_x_739_;
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
else
{
lean_dec(v_x_739_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_750_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding_go(v_s_738_, v_tail_742_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v___x_750_);
v___x_752_ = v___x_748_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_head_741_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(lean_object* v_st_757_, lean_object* v_s_758_){
_start:
{
lean_object* v_nonOverlapping_759_; lean_object* v_current_x3f_760_; lean_object* v_surrounding_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_769_; 
v_nonOverlapping_759_ = lean_ctor_get(v_st_757_, 0);
v_current_x3f_760_ = lean_ctor_get(v_st_757_, 1);
v_surrounding_761_ = lean_ctor_get(v_st_757_, 2);
v_isSharedCheck_769_ = !lean_is_exclusive(v_st_757_);
if (v_isSharedCheck_769_ == 0)
{
v___x_763_ = v_st_757_;
v_isShared_764_ = v_isSharedCheck_769_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_surrounding_761_);
lean_inc(v_current_x3f_760_);
lean_inc(v_nonOverlapping_759_);
lean_dec(v_st_757_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_769_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_765_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding_go(v_s_758_, v_surrounding_761_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 2, v___x_765_);
v___x_767_ = v___x_763_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_nonOverlapping_759_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_current_x3f_760_);
lean_ctor_set(v_reuseFailAlloc_768_, 2, v___x_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
uint8_t l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better(lean_object* v_t_770_, lean_object* v_soFar_771_){
_start:
{
lean_object* v_tailPos_772_; lean_object* v_priority_773_; lean_object* v_tailPos_774_; lean_object* v_priority_775_; uint8_t v___x_776_; 
v_tailPos_772_ = lean_ctor_get(v_soFar_771_, 1);
v_priority_773_ = lean_ctor_get(v_soFar_771_, 2);
v_tailPos_774_ = lean_ctor_get(v_t_770_, 1);
v_priority_775_ = lean_ctor_get(v_t_770_, 2);
v___x_776_ = lean_nat_dec_lt(v_priority_773_, v_priority_775_);
if (v___x_776_ == 0)
{
uint8_t v___x_777_; 
v___x_777_ = lean_nat_dec_eq(v_priority_775_, v_priority_773_);
if (v___x_777_ == 0)
{
return v___x_777_;
}
else
{
uint8_t v___x_778_; 
v___x_778_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_774_, v_tailPos_772_);
if (v___x_778_ == 0)
{
return v___x_777_;
}
else
{
return v___x_776_;
}
}
}
else
{
return v___x_776_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_770_ = stack[0].m_obj;
lean_object* v_soFar_771_ = stack[1].m_obj;
uint8_t v_res_779_;
v_res_779_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better(v_t_770_, v_soFar_771_);
stack->m_num = v_res_779_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better___boxed(lean_object* v_t_780_, lean_object* v_soFar_781_){
_start:
{
uint8_t v_res_782_; lean_object* v_r_783_; 
v_res_782_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better(v_t_780_, v_soFar_781_);
lean_dec_ref(v_soFar_781_);
lean_dec_ref(v_t_780_);
v_r_783_ = lean_box(v_res_782_);
return v_r_783_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0(lean_object* v_x_784_, lean_object* v_x_785_){
_start:
{
if (lean_obj_tag(v_x_785_) == 0)
{
return v_x_784_;
}
else
{
if (lean_obj_tag(v_x_784_) == 0)
{
lean_object* v_head_786_; lean_object* v_tail_787_; lean_object* v___x_788_; 
v_head_786_ = lean_ctor_get(v_x_785_, 0);
v_tail_787_ = lean_ctor_get(v_x_785_, 1);
lean_inc(v_head_786_);
v___x_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_788_, 0, v_head_786_);
v_x_784_ = v___x_788_;
v_x_785_ = v_tail_787_;
goto _start;
}
else
{
lean_object* v_head_790_; lean_object* v_tail_791_; lean_object* v_val_792_; uint8_t v___x_793_; 
v_head_790_ = lean_ctor_get(v_x_785_, 0);
v_tail_791_ = lean_ctor_get(v_x_785_, 1);
v_val_792_ = lean_ctor_get(v_x_784_, 0);
v___x_793_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better(v_head_790_, v_val_792_);
if (v___x_793_ == 0)
{
v_x_785_ = v_tail_791_;
goto _start;
}
else
{
lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_802_; 
v_isSharedCheck_802_ = !lean_is_exclusive(v_x_784_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v_x_784_, 0);
lean_dec(v_unused_803_);
v___x_796_ = v_x_784_;
v_isShared_797_ = v_isSharedCheck_802_;
goto v_resetjp_795_;
}
else
{
lean_dec(v_x_784_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_802_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
lean_inc(v_head_790_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v_head_790_);
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_head_790_);
v___x_799_ = v_reuseFailAlloc_801_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
v_x_784_ = v___x_799_;
v_x_785_ = v_tail_791_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0___boxed(lean_object* v_x_804_, lean_object* v_x_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0(v_x_804_, v_x_805_);
lean_dec(v_x_805_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(lean_object* v_toks_807_){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = lean_box(0);
v___x_809_ = l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0(v___x_808_, v_toks_807_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest___boxed(lean_object* v_toks_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(v_toks_810_);
lean_dec(v_toks_810_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(lean_object* v_val_812_, lean_object* v_x_813_){
_start:
{
if (lean_obj_tag(v_x_813_) == 0)
{
return v_x_813_;
}
else
{
lean_object* v_head_814_; lean_object* v_tail_815_; lean_object* v_tailPos_816_; lean_object* v_tailPos_817_; uint8_t v___x_818_; 
v_head_814_ = lean_ctor_get(v_x_813_, 0);
v_tail_815_ = lean_ctor_get(v_x_813_, 1);
v_tailPos_816_ = lean_ctor_get(v_head_814_, 1);
v_tailPos_817_ = lean_ctor_get(v_val_812_, 1);
v___x_818_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_816_, v_tailPos_817_);
if (v___x_818_ == 2)
{
lean_inc_ref(v_x_813_);
return v_x_813_;
}
else
{
v_x_813_ = v_tail_815_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0___boxed(lean_object* v_val_820_, lean_object* v_x_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(v_val_820_, v_x_821_);
lean_dec(v_x_821_);
lean_dec_ref(v_val_820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(lean_object* v_nextToken_x3f_823_, lean_object* v_a_824_){
_start:
{
lean_object* v_current_x3f_825_; 
v_current_x3f_825_ = lean_ctor_get(v_a_824_, 1);
if (lean_obj_tag(v_current_x3f_825_) == 1)
{
lean_object* v_nonOverlapping_826_; lean_object* v_surrounding_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_868_; 
lean_inc_ref(v_current_x3f_825_);
v_nonOverlapping_826_ = lean_ctor_get(v_a_824_, 0);
v_surrounding_827_ = lean_ctor_get(v_a_824_, 2);
v_isSharedCheck_868_ = !lean_is_exclusive(v_a_824_);
if (v_isSharedCheck_868_ == 0)
{
lean_object* v_unused_869_; 
v_unused_869_ = lean_ctor_get(v_a_824_, 1);
lean_dec(v_unused_869_);
v___x_829_ = v_a_824_;
v_isShared_830_ = v_isSharedCheck_868_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_surrounding_827_);
lean_inc(v_nonOverlapping_826_);
lean_dec(v_a_824_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_868_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v_val_831_; lean_object* v___x_832_; lean_object* v___y_834_; lean_object* v___y_835_; 
v_val_831_ = lean_ctor_get(v_current_x3f_825_, 0);
v___x_832_ = l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(v_val_831_, v_surrounding_827_);
lean_dec(v_surrounding_827_);
if (lean_obj_tag(v_nextToken_x3f_823_) == 1)
{
lean_object* v_val_863_; lean_object* v_tailPos_864_; lean_object* v_pos_865_; uint8_t v___x_866_; 
v_val_863_ = lean_ctor_get(v_nextToken_x3f_823_, 0);
v_tailPos_864_ = lean_ctor_get(v_val_831_, 1);
v_pos_865_ = lean_ctor_get(v_val_863_, 0);
v___x_866_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_864_, v_pos_865_);
if (v___x_866_ == 2)
{
lean_object* v___x_867_; 
lean_del_object(v___x_829_);
v___x_867_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_867_, 0, v_nonOverlapping_826_);
lean_ctor_set(v___x_867_, 1, v_current_x3f_825_);
lean_ctor_set(v___x_867_, 2, v___x_832_);
return v___x_867_;
}
else
{
lean_inc(v_val_831_);
lean_dec_ref_known(v_current_x3f_825_, 1);
goto v___jp_840_;
}
}
else
{
lean_inc(v_val_831_);
lean_dec_ref_known(v_current_x3f_825_, 1);
goto v___jp_840_;
}
v___jp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 2, v___x_832_);
lean_ctor_set(v___x_829_, 1, v___y_835_);
lean_ctor_set(v___x_829_, 0, v___y_834_);
v___x_837_ = v___x_829_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___y_834_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v___y_835_);
lean_ctor_set(v_reuseFailAlloc_839_, 2, v___x_832_);
v___x_837_ = v_reuseFailAlloc_839_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
v_a_824_ = v___x_837_;
goto _start;
}
}
v___jp_840_:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
lean_inc(v_val_831_);
v___x_841_ = lean_array_push(v_nonOverlapping_826_, v_val_831_);
v___x_842_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(v___x_832_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_dec(v_val_831_);
v___y_834_ = v___x_841_;
v___y_835_ = v___x_842_;
goto v___jp_833_;
}
else
{
lean_object* v_val_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_862_; 
v_val_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_862_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_862_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_val_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_862_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v_tailPos_847_; lean_object* v_tailPos_848_; uint8_t v_type_849_; lean_object* v_priority_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_860_; 
v_tailPos_847_ = lean_ctor_get(v_val_831_, 1);
lean_inc_ref(v_tailPos_847_);
lean_dec(v_val_831_);
v_tailPos_848_ = lean_ctor_get(v_val_843_, 1);
v_type_849_ = lean_ctor_get_uint8(v_val_843_, sizeof(void*)*3);
v_priority_850_ = lean_ctor_get(v_val_843_, 2);
v_isSharedCheck_860_ = !lean_is_exclusive(v_val_843_);
if (v_isSharedCheck_860_ == 0)
{
lean_object* v_unused_861_; 
v_unused_861_ = lean_ctor_get(v_val_843_, 0);
lean_dec(v_unused_861_);
v___x_852_ = v_val_843_;
v_isShared_853_ = v_isSharedCheck_860_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_priority_850_);
lean_inc(v_tailPos_848_);
lean_dec(v_val_843_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_860_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v_tailPos_847_);
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_tailPos_847_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v_tailPos_848_);
lean_ctor_set(v_reuseFailAlloc_859_, 2, v_priority_850_);
lean_ctor_set_uint8(v_reuseFailAlloc_859_, sizeof(void*)*3, v_type_849_);
v___x_855_ = v_reuseFailAlloc_859_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_857_; 
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_855_);
v___x_857_ = v___x_845_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
v___y_834_ = v___x_841_;
v___y_835_ = v___x_857_;
goto v___jp_833_;
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
lean_object* v_nonOverlapping_870_; lean_object* v_surrounding_871_; lean_object* v___x_872_; 
v_nonOverlapping_870_ = lean_ctor_get(v_a_824_, 0);
v_surrounding_871_ = lean_ctor_get(v_a_824_, 2);
v___x_872_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(v_surrounding_871_);
if (lean_obj_tag(v___x_872_) == 1)
{
lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_880_; 
lean_inc(v_surrounding_871_);
lean_inc_ref(v_nonOverlapping_870_);
v_isSharedCheck_880_ = !lean_is_exclusive(v_a_824_);
if (v_isSharedCheck_880_ == 0)
{
lean_object* v_unused_881_; lean_object* v_unused_882_; lean_object* v_unused_883_; 
v_unused_881_ = lean_ctor_get(v_a_824_, 2);
lean_dec(v_unused_881_);
v_unused_882_ = lean_ctor_get(v_a_824_, 1);
lean_dec(v_unused_882_);
v_unused_883_ = lean_ctor_get(v_a_824_, 0);
lean_dec(v_unused_883_);
v___x_874_ = v_a_824_;
v_isShared_875_ = v_isSharedCheck_880_;
goto v_resetjp_873_;
}
else
{
lean_dec(v_a_824_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_880_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 1, v___x_872_);
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_nonOverlapping_870_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_879_, 2, v_surrounding_871_);
v___x_877_ = v_reuseFailAlloc_879_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
v_a_824_ = v___x_877_;
goto _start;
}
}
}
else
{
lean_dec(v___x_872_);
return v_a_824_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg___boxed(lean_object* v_nextToken_x3f_884_, lean_object* v_a_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v_nextToken_x3f_884_, v_a_885_);
lean_dec(v_nextToken_x3f_884_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken(lean_object* v_st_887_, lean_object* v_nextToken_x3f_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v_nextToken_x3f_888_, v_st_887_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken___boxed(lean_object* v_st_890_, lean_object* v_nextToken_x3f_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken(v_st_890_, v_nextToken_x3f_891_);
lean_dec(v_nextToken_x3f_891_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1(lean_object* v_nextToken_x3f_893_, lean_object* v_inst_894_, lean_object* v_a_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v_nextToken_x3f_893_, v_a_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___boxed(lean_object* v_nextToken_x3f_897_, lean_object* v_inst_898_, lean_object* v_a_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1(v_nextToken_x3f_897_, v_inst_898_, v_a_899_);
lean_dec(v_nextToken_x3f_897_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_token(lean_object* v_st_901_, lean_object* v_t_902_){
_start:
{
lean_object* v___x_903_; lean_object* v_st_904_; lean_object* v_current_x3f_905_; 
lean_inc_ref(v_t_902_);
v___x_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_903_, 0, v_t_902_);
v_st_904_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v___x_903_, v_st_901_);
v_current_x3f_905_ = lean_ctor_get(v_st_904_, 1);
if (lean_obj_tag(v_current_x3f_905_) == 1)
{
lean_object* v_val_906_; lean_object* v_nonOverlapping_907_; lean_object* v_surrounding_908_; lean_object* v_pos_909_; lean_object* v_tailPos_910_; lean_object* v_priority_911_; lean_object* v_pos_912_; lean_object* v_tailPos_913_; uint8_t v_type_914_; lean_object* v_priority_915_; lean_object* v___y_917_; uint8_t v___y_926_; uint8_t v___x_928_; 
v_val_906_ = lean_ctor_get(v_current_x3f_905_, 0);
v_nonOverlapping_907_ = lean_ctor_get(v_st_904_, 0);
v_surrounding_908_ = lean_ctor_get(v_st_904_, 2);
v_pos_909_ = lean_ctor_get(v_t_902_, 0);
v_tailPos_910_ = lean_ctor_get(v_t_902_, 1);
v_priority_911_ = lean_ctor_get(v_t_902_, 2);
v_pos_912_ = lean_ctor_get(v_val_906_, 0);
v_tailPos_913_ = lean_ctor_get(v_val_906_, 1);
v_type_914_ = lean_ctor_get_uint8(v_val_906_, sizeof(void*)*3);
v_priority_915_ = lean_ctor_get(v_val_906_, 2);
v___x_928_ = lean_nat_dec_lt(v_priority_911_, v_priority_915_);
if (v___x_928_ == 0)
{
uint8_t v___x_929_; 
v___x_929_ = lean_nat_dec_eq(v_priority_915_, v_priority_911_);
if (v___x_929_ == 0)
{
lean_inc_ref(v_tailPos_910_);
lean_inc_ref(v_pos_909_);
lean_inc(v_surrounding_908_);
lean_inc_ref(v_nonOverlapping_907_);
lean_inc(v_val_906_);
lean_dec_ref(v_st_904_);
lean_dec_ref(v_t_902_);
goto v___jp_921_;
}
else
{
uint8_t v___x_930_; 
v___x_930_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_912_, v_pos_909_);
if (v___x_930_ == 0)
{
lean_inc_ref(v_tailPos_910_);
lean_inc_ref(v_pos_909_);
lean_inc(v_surrounding_908_);
lean_inc_ref(v_nonOverlapping_907_);
lean_inc(v_val_906_);
lean_dec_ref(v_st_904_);
lean_dec_ref(v_t_902_);
goto v___jp_921_;
}
else
{
uint8_t v___x_931_; 
v___x_931_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_913_, v_tailPos_910_);
if (v___x_931_ == 0)
{
v___y_926_ = v___x_930_;
goto v___jp_925_;
}
else
{
v___y_926_ = v___x_928_;
goto v___jp_925_;
}
}
}
}
else
{
lean_object* v___x_932_; 
lean_dec_ref_known(v___x_903_, 1);
v___x_932_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_904_, v_t_902_);
return v___x_932_;
}
v___jp_916_:
{
lean_object* v_st_918_; uint8_t v___x_919_; 
v_st_918_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_st_918_, 0, v___y_917_);
lean_ctor_set(v_st_918_, 1, v___x_903_);
lean_ctor_set(v_st_918_, 2, v_surrounding_908_);
v___x_919_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_910_, v_tailPos_913_);
lean_dec_ref(v_tailPos_910_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; 
v___x_920_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_918_, v_val_906_);
return v___x_920_;
}
else
{
lean_dec(v_val_906_);
return v_st_918_;
}
}
v___jp_921_:
{
uint8_t v___x_922_; 
v___x_922_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_912_, v_pos_909_);
if (v___x_922_ == 0)
{
lean_object* v_curr_923_; lean_object* v___x_924_; 
lean_inc(v_priority_915_);
lean_inc_ref(v_pos_912_);
v_curr_923_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_curr_923_, 0, v_pos_912_);
lean_ctor_set(v_curr_923_, 1, v_pos_909_);
lean_ctor_set(v_curr_923_, 2, v_priority_915_);
lean_ctor_set_uint8(v_curr_923_, sizeof(void*)*3, v_type_914_);
v___x_924_ = lean_array_push(v_nonOverlapping_907_, v_curr_923_);
v___y_917_ = v___x_924_;
goto v___jp_916_;
}
else
{
lean_dec_ref(v_pos_909_);
v___y_917_ = v_nonOverlapping_907_;
goto v___jp_916_;
}
}
v___jp_925_:
{
if (v___y_926_ == 0)
{
lean_inc_ref(v_tailPos_910_);
lean_inc_ref(v_pos_909_);
lean_inc(v_surrounding_908_);
lean_inc_ref(v_nonOverlapping_907_);
lean_inc(v_val_906_);
lean_dec_ref(v_st_904_);
lean_dec_ref(v_t_902_);
goto v___jp_921_;
}
else
{
lean_object* v___x_927_; 
lean_dec_ref_known(v___x_903_, 1);
v___x_927_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_904_, v_t_902_);
return v___x_927_;
}
}
}
else
{
lean_object* v_nonOverlapping_933_; lean_object* v_surrounding_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
lean_dec_ref(v_t_902_);
v_nonOverlapping_933_ = lean_ctor_get(v_st_904_, 0);
v_surrounding_934_ = lean_ctor_get(v_st_904_, 2);
v_isSharedCheck_941_ = !lean_is_exclusive(v_st_904_);
if (v_isSharedCheck_941_ == 0)
{
lean_object* v_unused_942_; 
v_unused_942_ = lean_ctor_get(v_st_904_, 1);
lean_dec(v_unused_942_);
v___x_936_ = v_st_904_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_surrounding_934_);
lean_inc(v_nonOverlapping_933_);
lean_dec(v_st_904_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 1, v___x_903_);
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_nonOverlapping_933_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_940_, 2, v_surrounding_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
uint8_t l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0(lean_object* v_x_943_, lean_object* v_x_944_){
_start:
{
lean_object* v_pos_945_; lean_object* v_tailPos_946_; lean_object* v_pos_947_; lean_object* v_tailPos_948_; uint8_t v___x_949_; 
v_pos_945_ = lean_ctor_get(v_x_943_, 0);
v_tailPos_946_ = lean_ctor_get(v_x_943_, 1);
v_pos_947_ = lean_ctor_get(v_x_944_, 0);
v_tailPos_948_ = lean_ctor_get(v_x_944_, 1);
v___x_949_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_945_, v_pos_947_);
if (v___x_949_ == 0)
{
uint8_t v___x_950_; 
v___x_950_ = 1;
return v___x_950_;
}
else
{
uint8_t v___x_951_; 
v___x_951_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_945_, v_pos_947_);
if (v___x_951_ == 0)
{
return v___x_951_;
}
else
{
uint8_t v___x_952_; 
v___x_952_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_946_, v_tailPos_948_);
if (v___x_952_ == 2)
{
uint8_t v___x_953_; 
v___x_953_ = 0;
return v___x_953_;
}
else
{
return v___x_951_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_943_ = stack[0].m_obj;
lean_object* v_x_944_ = stack[1].m_obj;
uint8_t v_res_954_;
v_res_954_ = l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0(v_x_943_, v_x_944_);
stack->m_num = v_res_954_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0___boxed(lean_object* v_x_955_, lean_object* v_x_956_){
_start:
{
uint8_t v_res_957_; lean_object* v_r_958_; 
v_res_957_ = l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0(v_x_955_, v_x_956_);
lean_dec_ref(v_x_956_);
lean_dec_ref(v_x_955_);
v_r_958_ = lean_box(v_res_957_);
return v_r_958_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(lean_object* v_as_x27_959_, lean_object* v_b_960_){
_start:
{
if (lean_obj_tag(v_as_x27_959_) == 0)
{
return v_b_960_;
}
else
{
lean_object* v_head_961_; lean_object* v_tail_962_; lean_object* v___x_963_; 
v_head_961_ = lean_ctor_get(v_as_x27_959_, 0);
v_tail_962_ = lean_ctor_get(v_as_x27_959_, 1);
lean_inc(v_head_961_);
v___x_963_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_token(v_b_960_, v_head_961_);
v_as_x27_959_ = v_tail_962_;
v_b_960_ = v___x_963_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg___boxed(lean_object* v_as_x27_965_, lean_object* v_b_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(v_as_x27_965_, v_b_966_);
lean_dec(v_as_x27_965_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleOverlappingSemanticTokens(lean_object* v_tokens_969_){
_start:
{
lean_object* v___f_970_; lean_object* v_count_971_; lean_object* v___x_972_; lean_object* v_tokens_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v_st_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v_nonOverlapping_984_; 
v___f_970_ = ((lean_object*)(l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___closed__0));
v_count_971_ = lean_array_get_size(v_tokens_969_);
v___x_972_ = lean_array_to_list(v_tokens_969_);
v_tokens_973_ = l_List_mergeSort___redArg(v___x_972_, v___f_970_);
v___x_974_ = lean_unsigned_to_nat(11u);
v___x_975_ = lean_nat_mul(v_count_971_, v___x_974_);
v___x_976_ = lean_unsigned_to_nat(10u);
v___x_977_ = lean_nat_div(v___x_975_, v___x_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_mk_empty_array_with_capacity(v___x_977_);
lean_dec(v___x_977_);
v___x_979_ = lean_box(0);
v___x_980_ = lean_box(0);
v_st_981_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_st_981_, 0, v___x_978_);
lean_ctor_set(v_st_981_, 1, v___x_979_);
lean_ctor_set(v_st_981_, 2, v___x_980_);
v___x_982_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(v_tokens_973_, v_st_981_);
lean_dec(v_tokens_973_);
v___x_983_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v___x_979_, v___x_982_);
v_nonOverlapping_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc_ref(v_nonOverlapping_984_);
lean_dec_ref(v___x_983_);
return v_nonOverlapping_984_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0(lean_object* v_as_985_, lean_object* v_as_x27_986_, lean_object* v_b_987_, lean_object* v_a_988_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(v_as_x27_986_, v_b_987_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___boxed(lean_object* v_as_990_, lean_object* v_as_x27_991_, lean_object* v_b_992_, lean_object* v_a_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0(v_as_990_, v_as_x27_991_, v_b_992_, v_a_993_);
lean_dec(v_as_x27_991_);
lean_dec(v_as_990_);
return v_res_994_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(uint8_t v___x_995_, lean_object* v_x_996_, lean_object* v_x_997_){
_start:
{
lean_object* v_pos_998_; lean_object* v_tailPos_999_; lean_object* v_pos_1000_; lean_object* v_tailPos_1001_; uint8_t v___x_1002_; 
v_pos_998_ = lean_ctor_get(v_x_996_, 0);
v_tailPos_999_ = lean_ctor_get(v_x_996_, 1);
v_pos_1000_ = lean_ctor_get(v_x_997_, 0);
v_tailPos_1001_ = lean_ctor_get(v_x_997_, 1);
v___x_1002_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_998_, v_pos_1000_);
if (v___x_1002_ == 0)
{
return v___x_995_;
}
else
{
uint8_t v___x_1003_; 
v___x_1003_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_998_, v_pos_1000_);
if (v___x_1003_ == 0)
{
return v___x_1003_;
}
else
{
uint8_t v___x_1004_; 
v___x_1004_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_999_, v_tailPos_1001_);
if (v___x_1004_ == 2)
{
uint8_t v___x_1005_; 
v___x_1005_ = 0;
return v___x_1005_;
}
else
{
return v___x_1003_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_995_ = stack[0].m_num;
lean_object* v_x_996_ = stack[1].m_obj;
lean_object* v_x_997_ = stack[2].m_obj;
uint8_t v_res_1006_;
v_res_1006_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_995_, v_x_996_, v_x_997_);
stack->m_num = v_res_1006_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0___boxed(lean_object* v___x_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_){
_start:
{
uint8_t v___x_1131__boxed_1010_; uint8_t v_res_1011_; lean_object* v_r_1012_; 
v___x_1131__boxed_1010_ = lean_unbox(v___x_1007_);
v_res_1011_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1131__boxed_1010_, v_x_1008_, v_x_1009_);
lean_dec_ref(v_x_1009_);
lean_dec_ref(v_x_1008_);
v_r_1012_ = lean_box(v_res_1011_);
return v_r_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(lean_object* v_hi_1013_, lean_object* v_pivot_1014_, lean_object* v_as_1015_, lean_object* v_i_1016_, lean_object* v_k_1017_){
_start:
{
uint8_t v___y_1025_; uint8_t v___x_1029_; 
v___x_1029_ = lean_nat_dec_lt(v_k_1017_, v_hi_1013_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
lean_dec(v_k_1017_);
v___x_1030_ = lean_array_fswap(v_as_1015_, v_i_1016_, v_hi_1013_);
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v_i_1016_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
return v___x_1031_;
}
else
{
lean_object* v___x_1032_; lean_object* v_pos_1033_; lean_object* v_tailPos_1034_; lean_object* v_pos_1035_; lean_object* v_tailPos_1036_; uint8_t v___y_1038_; uint8_t v___x_1041_; 
v___x_1032_ = lean_array_fget_borrowed(v_as_1015_, v_k_1017_);
v_pos_1033_ = lean_ctor_get(v___x_1032_, 0);
v_tailPos_1034_ = lean_ctor_get(v___x_1032_, 1);
v_pos_1035_ = lean_ctor_get(v_pivot_1014_, 0);
v_tailPos_1036_ = lean_ctor_get(v_pivot_1014_, 1);
v___x_1041_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_1033_, v_pos_1035_);
if (v___x_1041_ == 0)
{
if (v___x_1029_ == 0)
{
v___y_1038_ = v___x_1029_;
goto v___jp_1037_;
}
else
{
goto v___jp_1018_;
}
}
else
{
uint8_t v___x_1042_; 
v___x_1042_ = 0;
v___y_1038_ = v___x_1042_;
goto v___jp_1037_;
}
v___jp_1037_:
{
uint8_t v___x_1039_; 
v___x_1039_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_1033_, v_pos_1035_);
if (v___x_1039_ == 0)
{
v___y_1025_ = v___x_1039_;
goto v___jp_1024_;
}
else
{
uint8_t v___x_1040_; 
v___x_1040_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_1034_, v_tailPos_1036_);
if (v___x_1040_ == 2)
{
v___y_1025_ = v___y_1038_;
goto v___jp_1024_;
}
else
{
v___y_1025_ = v___x_1039_;
goto v___jp_1024_;
}
}
}
}
v___jp_1018_:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1019_ = lean_array_fswap(v_as_1015_, v_i_1016_, v_k_1017_);
v___x_1020_ = lean_unsigned_to_nat(1u);
v___x_1021_ = lean_nat_add(v_i_1016_, v___x_1020_);
lean_dec(v_i_1016_);
v___x_1022_ = lean_nat_add(v_k_1017_, v___x_1020_);
lean_dec(v_k_1017_);
v_as_1015_ = v___x_1019_;
v_i_1016_ = v___x_1021_;
v_k_1017_ = v___x_1022_;
goto _start;
}
v___jp_1024_:
{
if (v___y_1025_ == 0)
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = lean_unsigned_to_nat(1u);
v___x_1027_ = lean_nat_add(v_k_1017_, v___x_1026_);
lean_dec(v_k_1017_);
v_k_1017_ = v___x_1027_;
goto _start;
}
else
{
goto v___jp_1018_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg___boxed(lean_object* v_hi_1043_, lean_object* v_pivot_1044_, lean_object* v_as_1045_, lean_object* v_i_1046_, lean_object* v_k_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(v_hi_1043_, v_pivot_1044_, v_as_1045_, v_i_1046_, v_k_1047_);
lean_dec_ref(v_pivot_1044_);
lean_dec(v_hi_1043_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(lean_object* v_n_1049_, lean_object* v_as_1050_, lean_object* v_lo_1051_, lean_object* v_hi_1052_){
_start:
{
lean_object* v___y_1054_; uint8_t v___x_1064_; 
v___x_1064_ = lean_nat_dec_lt(v_lo_1051_, v_hi_1052_);
if (v___x_1064_ == 0)
{
lean_dec(v_lo_1051_);
return v_as_1050_;
}
else
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v_mid_1067_; lean_object* v___y_1069_; lean_object* v___y_1075_; lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1065_ = lean_nat_add(v_lo_1051_, v_hi_1052_);
v___x_1066_ = lean_unsigned_to_nat(1u);
v_mid_1067_ = lean_nat_shiftr(v___x_1065_, v___x_1066_);
lean_dec(v___x_1065_);
v___x_1080_ = lean_array_fget_borrowed(v_as_1050_, v_mid_1067_);
v___x_1081_ = lean_array_fget_borrowed(v_as_1050_, v_lo_1051_);
v___x_1082_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1064_, v___x_1080_, v___x_1081_);
if (v___x_1082_ == 0)
{
v___y_1075_ = v_as_1050_;
goto v___jp_1074_;
}
else
{
lean_object* v___x_1083_; 
v___x_1083_ = lean_array_fswap(v_as_1050_, v_lo_1051_, v_mid_1067_);
v___y_1075_ = v___x_1083_;
goto v___jp_1074_;
}
v___jp_1068_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; 
v___x_1070_ = lean_array_fget_borrowed(v___y_1069_, v_mid_1067_);
v___x_1071_ = lean_array_fget_borrowed(v___y_1069_, v_hi_1052_);
v___x_1072_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1064_, v___x_1070_, v___x_1071_);
if (v___x_1072_ == 0)
{
lean_dec(v_mid_1067_);
v___y_1054_ = v___y_1069_;
goto v___jp_1053_;
}
else
{
lean_object* v___x_1073_; 
v___x_1073_ = lean_array_fswap(v___y_1069_, v_mid_1067_, v_hi_1052_);
lean_dec(v_mid_1067_);
v___y_1054_ = v___x_1073_;
goto v___jp_1053_;
}
}
v___jp_1074_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v___x_1076_ = lean_array_fget_borrowed(v___y_1075_, v_hi_1052_);
v___x_1077_ = lean_array_fget_borrowed(v___y_1075_, v_lo_1051_);
v___x_1078_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1064_, v___x_1076_, v___x_1077_);
if (v___x_1078_ == 0)
{
v___y_1069_ = v___y_1075_;
goto v___jp_1068_;
}
else
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_array_fswap(v___y_1075_, v_lo_1051_, v_hi_1052_);
v___y_1069_ = v___x_1079_;
goto v___jp_1068_;
}
}
}
v___jp_1053_:
{
lean_object* v_pivot_1055_; lean_object* v___x_1056_; lean_object* v_fst_1057_; lean_object* v_snd_1058_; uint8_t v___x_1059_; 
v_pivot_1055_ = lean_array_fget(v___y_1054_, v_hi_1052_);
lean_inc_n(v_lo_1051_, 2);
v___x_1056_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(v_hi_1052_, v_pivot_1055_, v___y_1054_, v_lo_1051_, v_lo_1051_);
lean_dec(v_pivot_1055_);
v_fst_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_fst_1057_);
v_snd_1058_ = lean_ctor_get(v___x_1056_, 1);
lean_inc(v_snd_1058_);
lean_dec_ref(v___x_1056_);
v___x_1059_ = lean_nat_dec_le(v_hi_1052_, v_fst_1057_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1060_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_n_1049_, v_snd_1058_, v_lo_1051_, v_fst_1057_);
v___x_1061_ = lean_unsigned_to_nat(1u);
v___x_1062_ = lean_nat_add(v_fst_1057_, v___x_1061_);
lean_dec(v_fst_1057_);
v_as_1050_ = v___x_1060_;
v_lo_1051_ = v___x_1062_;
goto _start;
}
else
{
lean_dec(v_fst_1057_);
lean_dec(v_lo_1051_);
return v_snd_1058_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___boxed(lean_object* v_n_1084_, lean_object* v_as_1085_, lean_object* v_lo_1086_, lean_object* v_hi_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_n_1084_, v_as_1085_, v_lo_1086_, v_hi_1087_);
lean_dec(v_hi_1087_);
lean_dec(v_n_1084_);
return v_res_1088_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(lean_object* v_as_1089_, size_t v_sz_1090_, size_t v_i_1091_, lean_object* v_b_1092_){
_start:
{
uint8_t v___x_1093_; 
v___x_1093_ = lean_usize_dec_lt(v_i_1091_, v_sz_1090_);
if (v___x_1093_ == 0)
{
return v_b_1092_;
}
else
{
lean_object* v_a_1094_; lean_object* v_pos_1095_; lean_object* v_snd_1096_; lean_object* v_tailPos_1097_; uint8_t v_type_1098_; lean_object* v_fst_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1130_; 
v_a_1094_ = lean_array_uget_borrowed(v_as_1089_, v_i_1091_);
v_pos_1095_ = lean_ctor_get(v_a_1094_, 0);
v_snd_1096_ = lean_ctor_get(v_b_1092_, 1);
lean_inc(v_snd_1096_);
v_tailPos_1097_ = lean_ctor_get(v_a_1094_, 1);
v_type_1098_ = lean_ctor_get_uint8(v_a_1094_, sizeof(void*)*3);
v_fst_1099_ = lean_ctor_get(v_b_1092_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_b_1092_);
if (v_isSharedCheck_1130_ == 0)
{
lean_object* v_unused_1131_; 
v_unused_1131_ = lean_ctor_get(v_b_1092_, 1);
lean_dec(v_unused_1131_);
v___x_1101_ = v_b_1092_;
v_isShared_1102_ = v_isSharedCheck_1130_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_fst_1099_);
lean_dec(v_b_1092_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1130_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v_line_1103_; lean_object* v_character_1104_; lean_object* v_line_1105_; lean_object* v_character_1106_; lean_object* v_tokenModifiers_1107_; lean_object* v___x_1108_; lean_object* v___y_1110_; uint8_t v___x_1129_; 
v_line_1103_ = lean_ctor_get(v_pos_1095_, 0);
v_character_1104_ = lean_ctor_get(v_pos_1095_, 1);
v_line_1105_ = lean_ctor_get(v_snd_1096_, 0);
lean_inc(v_line_1105_);
v_character_1106_ = lean_ctor_get(v_snd_1096_, 1);
lean_inc(v_character_1106_);
lean_dec(v_snd_1096_);
v_tokenModifiers_1107_ = lean_unsigned_to_nat(0u);
v___x_1108_ = lean_nat_sub(v_line_1103_, v_line_1105_);
v___x_1129_ = lean_nat_dec_eq(v_line_1103_, v_line_1105_);
lean_dec(v_line_1105_);
if (v___x_1129_ == 0)
{
lean_dec(v_character_1106_);
v___y_1110_ = v_tokenModifiers_1107_;
goto v___jp_1109_;
}
else
{
v___y_1110_ = v_character_1106_;
goto v___jp_1109_;
}
v___jp_1109_:
{
lean_object* v_character_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1124_; 
v_character_1111_ = lean_ctor_get(v_tailPos_1097_, 1);
v___x_1112_ = lean_nat_sub(v_character_1104_, v___y_1110_);
lean_dec(v___y_1110_);
v___x_1113_ = lean_nat_sub(v_character_1111_, v_character_1104_);
v___x_1114_ = l_Lean_Lsp_SemanticTokenType_toNat(v_type_1098_);
v___x_1115_ = lean_unsigned_to_nat(5u);
v___x_1116_ = lean_mk_empty_array_with_capacity(v___x_1115_);
v___x_1117_ = lean_array_push(v___x_1116_, v___x_1108_);
v___x_1118_ = lean_array_push(v___x_1117_, v___x_1112_);
v___x_1119_ = lean_array_push(v___x_1118_, v___x_1113_);
v___x_1120_ = lean_array_push(v___x_1119_, v___x_1114_);
v___x_1121_ = lean_array_push(v___x_1120_, v_tokenModifiers_1107_);
v___x_1122_ = l_Array_append___redArg(v_fst_1099_, v___x_1121_);
lean_dec_ref(v___x_1121_);
lean_inc_ref(v_pos_1095_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 1, v_pos_1095_);
lean_ctor_set(v___x_1101_, 0, v___x_1122_);
v___x_1124_ = v___x_1101_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1122_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_pos_1095_);
v___x_1124_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
size_t v___x_1125_; size_t v___x_1126_; 
v___x_1125_ = ((size_t)1ULL);
v___x_1126_ = lean_usize_add(v_i_1091_, v___x_1125_);
v_i_1091_ = v___x_1126_;
v_b_1092_ = v___x_1124_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1089_ = stack[0].m_obj;
size_t v_sz_1090_ = stack[1].m_num;
size_t v_i_1091_ = stack[2].m_num;
lean_object* v_b_1092_ = stack[3].m_obj;
lean_object* v_res_1132_;
v_res_1132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(v_as_1089_, v_sz_1090_, v_i_1091_, v_b_1092_);
stack->m_obj
 = v_res_1132_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0___boxed(lean_object* v_as_1133_, lean_object* v_sz_1134_, lean_object* v_i_1135_, lean_object* v_b_1136_){
_start:
{
size_t v_sz_boxed_1137_; size_t v_i_boxed_1138_; lean_object* v_res_1139_; 
v_sz_boxed_1137_ = lean_unbox_usize(v_sz_1134_);
lean_dec(v_sz_1134_);
v_i_boxed_1138_ = lean_unbox_usize(v_i_1135_);
lean_dec(v_i_1135_);
v_res_1139_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(v_as_1133_, v_sz_boxed_1137_, v_i_boxed_1138_, v_b_1136_);
lean_dec_ref(v_as_1133_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(lean_object* v_tokens_1142_){
_start:
{
lean_object* v_tokenModifiers_1143_; lean_object* v___y_1145_; lean_object* v___x_1165_; lean_object* v___y_1167_; lean_object* v___y_1168_; uint8_t v___x_1170_; 
v_tokenModifiers_1143_ = lean_unsigned_to_nat(0u);
v___x_1165_ = lean_array_get_size(v_tokens_1142_);
v___x_1170_ = lean_nat_dec_eq(v___x_1165_, v_tokenModifiers_1143_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___y_1174_; uint8_t v___x_1176_; 
v___x_1171_ = lean_unsigned_to_nat(1u);
v___x_1172_ = lean_nat_sub(v___x_1165_, v___x_1171_);
v___x_1176_ = lean_nat_dec_le(v_tokenModifiers_1143_, v___x_1172_);
if (v___x_1176_ == 0)
{
lean_inc(v___x_1172_);
v___y_1174_ = v___x_1172_;
goto v___jp_1173_;
}
else
{
v___y_1174_ = v_tokenModifiers_1143_;
goto v___jp_1173_;
}
v___jp_1173_:
{
uint8_t v___x_1175_; 
v___x_1175_ = lean_nat_dec_le(v___y_1174_, v___x_1172_);
if (v___x_1175_ == 0)
{
lean_dec(v___x_1172_);
lean_inc(v___y_1174_);
v___y_1167_ = v___y_1174_;
v___y_1168_ = v___y_1174_;
goto v___jp_1166_;
}
else
{
v___y_1167_ = v___y_1174_;
v___y_1168_ = v___x_1172_;
goto v___jp_1166_;
}
}
}
else
{
v___y_1145_ = v_tokens_1142_;
goto v___jp_1144_;
}
v___jp_1144_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v_data_1149_; lean_object* v_lastPos_1150_; lean_object* v___x_1151_; size_t v_sz_1152_; size_t v___x_1153_; lean_object* v___x_1154_; lean_object* v_fst_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1163_; 
v___x_1146_ = lean_unsigned_to_nat(5u);
v___x_1147_ = lean_array_get_size(v___y_1145_);
v___x_1148_ = lean_nat_mul(v___x_1146_, v___x_1147_);
v_data_1149_ = lean_mk_empty_array_with_capacity(v___x_1148_);
lean_dec(v___x_1148_);
v_lastPos_1150_ = ((lean_object*)(l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens___closed__0));
v___x_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1151_, 0, v_data_1149_);
lean_ctor_set(v___x_1151_, 1, v_lastPos_1150_);
v_sz_1152_ = lean_array_size(v___y_1145_);
v___x_1153_ = ((size_t)0ULL);
v___x_1154_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(v___y_1145_, v_sz_1152_, v___x_1153_, v___x_1151_);
lean_dec_ref(v___y_1145_);
v_fst_1155_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1163_ == 0)
{
lean_object* v_unused_1164_; 
v_unused_1164_ = lean_ctor_get(v___x_1154_, 1);
lean_dec(v_unused_1164_);
v___x_1157_ = v___x_1154_;
v_isShared_1158_ = v_isSharedCheck_1163_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_fst_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1163_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1159_ = lean_box(0);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 1, v_fst_1155_);
lean_ctor_set(v___x_1157_, 0, v___x_1159_);
v___x_1161_ = v___x_1157_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1159_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_fst_1155_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
v___jp_1166_:
{
lean_object* v___x_1169_; 
v___x_1169_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v___x_1165_, v_tokens_1142_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1168_);
v___y_1145_ = v___x_1169_;
goto v___jp_1144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1(lean_object* v_n_1177_, lean_object* v_as_1178_, lean_object* v_lo_1179_, lean_object* v_hi_1180_, lean_object* v_w_1181_, lean_object* v_hlo_1182_, lean_object* v_hhi_1183_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_n_1177_, v_as_1178_, v_lo_1179_, v_hi_1180_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___boxed(lean_object* v_n_1185_, lean_object* v_as_1186_, lean_object* v_lo_1187_, lean_object* v_hi_1188_, lean_object* v_w_1189_, lean_object* v_hlo_1190_, lean_object* v_hhi_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1(v_n_1185_, v_as_1186_, v_lo_1187_, v_hi_1188_, v_w_1189_, v_hlo_1190_, v_hhi_1191_);
lean_dec(v_hi_1188_);
lean_dec(v_n_1185_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1(lean_object* v_n_1193_, lean_object* v_lo_1194_, lean_object* v_hi_1195_, lean_object* v_hhi_1196_, lean_object* v_pivot_1197_, lean_object* v_as_1198_, lean_object* v_i_1199_, lean_object* v_k_1200_, lean_object* v_ilo_1201_, lean_object* v_ik_1202_, lean_object* v_w_1203_){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(v_hi_1195_, v_pivot_1197_, v_as_1198_, v_i_1199_, v_k_1200_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___boxed(lean_object* v_n_1205_, lean_object* v_lo_1206_, lean_object* v_hi_1207_, lean_object* v_hhi_1208_, lean_object* v_pivot_1209_, lean_object* v_as_1210_, lean_object* v_i_1211_, lean_object* v_k_1212_, lean_object* v_ilo_1213_, lean_object* v_ik_1214_, lean_object* v_w_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1(v_n_1205_, v_lo_1206_, v_hi_1207_, v_hhi_1208_, v_pivot_1209_, v_as_1210_, v_i_1211_, v_k_1212_, v_ilo_1213_, v_ik_1214_, v_w_1215_);
lean_dec_ref(v_pivot_1209_);
lean_dec(v_hi_1207_);
lean_dec(v_lo_1206_);
lean_dec(v_n_1205_);
return v_res_1216_;
}
}
lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(lean_object* v_tk_1217_, uint8_t v_k_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v___y_1221_; 
if (v_k_1218_ == 18)
{
lean_object* v___x_1226_; 
v___x_1226_ = lean_unsigned_to_nat(3u);
v___y_1221_ = v___x_1226_;
goto v___jp_1220_;
}
else
{
lean_object* v___x_1227_; 
v___x_1227_ = lean_unsigned_to_nat(5u);
v___y_1221_ = v___x_1227_;
goto v___jp_1220_;
}
v___jp_1220_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1222_ = lean_box(0);
v___x_1223_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1223_, 0, v_tk_1217_);
lean_ctor_set(v___x_1223_, 1, v___y_1221_);
lean_ctor_set_uint8(v___x_1223_, sizeof(void*)*2, v_k_1218_);
v___x_1224_ = lean_array_push(v_a_1219_, v___x_1223_);
v___x_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1222_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
return v___x_1225_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok_0interp(lean_interpreter_value* stack)
{
lean_object* v_tk_1217_ = stack[0].m_obj;
uint8_t v_k_1218_ = stack[1].m_num;
lean_object* v_a_1219_ = stack[2].m_obj;
lean_object* v_res_1228_;
v_res_1228_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_1217_, v_k_1218_, v_a_1219_);
stack->m_obj
 = v_res_1228_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok___boxed(lean_object* v_tk_1229_, lean_object* v_k_1230_, lean_object* v_a_1231_){
_start:
{
uint8_t v_k_boxed_1232_; lean_object* v_res_1233_; 
v_k_boxed_1232_ = lean_unbox(v_k_1230_);
v_res_1233_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_1229_, v_k_boxed_1232_, v_a_1231_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine(lean_object* v_line_1235_, lean_object* v_value_1236_){
_start:
{
uint8_t v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = 0;
v___x_1238_ = l_Lean_Syntax_getRange_x3f(v_line_1235_, v___x_1237_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v___x_1239_; 
v___x_1239_ = lean_box(0);
return v___x_1239_;
}
else
{
lean_object* v_val_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1272_; 
v_val_1240_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1242_ = v___x_1238_;
v_isShared_1243_ = v_isSharedCheck_1272_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_val_1240_);
lean_dec(v___x_1238_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1272_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v_start_1244_; lean_object* v_stop_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1271_; 
v_start_1244_ = lean_ctor_get(v_val_1240_, 0);
v_stop_1245_ = lean_ctor_get(v_val_1240_, 1);
v_isSharedCheck_1271_ = !lean_is_exclusive(v_val_1240_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1247_ = v_val_1240_;
v_isShared_1248_ = v_isSharedCheck_1271_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_stop_1245_);
lean_inc(v_start_1244_);
lean_dec(v_val_1240_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1271_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
uint8_t v___y_1250_; lean_object* v___y_1251_; uint8_t v___y_1260_; lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
v___x_1264_ = lean_string_utf8_byte_size(v_value_1236_);
v___x_1265_ = lean_unsigned_to_nat(1u);
v___x_1266_ = lean_nat_dec_le(v___x_1265_, v___x_1264_);
if (v___x_1266_ == 0)
{
v___y_1260_ = v___x_1266_;
goto v___jp_1259_;
}
else
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1267_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0));
v___x_1268_ = lean_unsigned_to_nat(0u);
v___x_1269_ = lean_nat_sub(v___x_1264_, v___x_1265_);
v___x_1270_ = lean_string_memcmp(v_value_1236_, v___x_1267_, v___x_1269_, v___x_1268_, v___x_1265_);
lean_dec(v___x_1269_);
v___y_1260_ = v___x_1270_;
goto v___jp_1259_;
}
v___jp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 1, v___y_1251_);
v___x_1253_ = v___x_1247_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_start_1244_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v___y_1251_);
v___x_1253_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1254_ = l_Lean_Syntax_ofRange(v___x_1253_, v___y_1250_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v___x_1254_);
v___x_1256_ = v___x_1242_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
v___jp_1259_:
{
uint8_t v___x_1261_; 
v___x_1261_ = 1;
if (v___y_1260_ == 0)
{
v___y_1250_ = v___x_1261_;
v___y_1251_ = v_stop_1245_;
goto v___jp_1249_;
}
else
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = lean_unsigned_to_nat(1u);
v___x_1263_ = lean_nat_sub(v_stop_1245_, v___x_1262_);
lean_dec(v_stop_1245_);
v___y_1250_ = v___x_1261_;
v___y_1251_ = v___x_1263_;
goto v___jp_1249_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___boxed(lean_object* v_line_1273_, lean_object* v_value_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine(v_line_1273_, v_value_1274_);
lean_dec_ref(v_value_1274_);
lean_dec(v_line_1273_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goArg(lean_object* v_arg_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Lean_Doc_ArgView_of(v_arg_1276_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = lean_box(0);
v___x_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
lean_ctor_set(v___x_1280_, 1, v_a_1277_);
return v___x_1280_;
}
else
{
lean_object* v_val_1281_; 
v_val_1281_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_val_1281_);
lean_dec_ref_known(v___x_1278_, 1);
switch(lean_obj_tag(v_val_1281_))
{
case 0:
{
lean_object* v_val_1282_; uint8_t v___x_1283_; lean_object* v___x_1284_; 
v_val_1282_ = lean_ctor_get(v_val_1281_, 1);
lean_inc(v_val_1282_);
lean_dec_ref_known(v_val_1281_, 2);
v___x_1283_ = 11;
v___x_1284_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_val_1282_, v___x_1283_, v_a_1277_);
return v___x_1284_;
}
case 1:
{
lean_object* v_parens_1285_; lean_object* v_name_1286_; lean_object* v_assign_1287_; lean_object* v_val_1288_; lean_object* v___y_1290_; 
v_parens_1285_ = lean_ctor_get(v_val_1281_, 1);
lean_inc(v_parens_1285_);
v_name_1286_ = lean_ctor_get(v_val_1281_, 2);
lean_inc(v_name_1286_);
v_assign_1287_ = lean_ctor_get(v_val_1281_, 3);
lean_inc(v_assign_1287_);
v_val_1288_ = lean_ctor_get(v_val_1281_, 4);
lean_inc(v_val_1288_);
lean_dec_ref_known(v_val_1281_, 5);
if (lean_obj_tag(v_parens_1285_) == 1)
{
lean_object* v_val_1313_; lean_object* v_fst_1314_; uint8_t v___x_1315_; lean_object* v___x_1316_; lean_object* v_snd_1317_; 
v_val_1313_ = lean_ctor_get(v_parens_1285_, 0);
v_fst_1314_ = lean_ctor_get(v_val_1313_, 0);
v___x_1315_ = 0;
lean_inc(v_fst_1314_);
v___x_1316_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_fst_1314_, v___x_1315_, v_a_1277_);
v_snd_1317_ = lean_ctor_get(v___x_1316_, 1);
lean_inc(v_snd_1317_);
lean_dec_ref(v___x_1316_);
v___y_1290_ = v_snd_1317_;
goto v___jp_1289_;
}
else
{
v___y_1290_ = v_a_1277_;
goto v___jp_1289_;
}
v___jp_1289_:
{
uint8_t v___x_1291_; lean_object* v___x_1292_; lean_object* v_snd_1293_; uint8_t v___x_1294_; lean_object* v___x_1295_; lean_object* v_snd_1296_; uint8_t v___x_1297_; lean_object* v___x_1298_; 
v___x_1291_ = 2;
v___x_1292_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1286_, v___x_1291_, v___y_1290_);
v_snd_1293_ = lean_ctor_get(v___x_1292_, 1);
lean_inc(v_snd_1293_);
lean_dec_ref(v___x_1292_);
v___x_1294_ = 0;
v___x_1295_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_assign_1287_, v___x_1294_, v_snd_1293_);
v_snd_1296_ = lean_ctor_get(v___x_1295_, 1);
lean_inc(v_snd_1296_);
lean_dec_ref(v___x_1295_);
v___x_1297_ = 11;
v___x_1298_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_val_1288_, v___x_1297_, v_snd_1296_);
if (lean_obj_tag(v_parens_1285_) == 1)
{
lean_object* v_val_1299_; lean_object* v_snd_1300_; lean_object* v_snd_1301_; lean_object* v___x_1302_; 
v_val_1299_ = lean_ctor_get(v_parens_1285_, 0);
lean_inc(v_val_1299_);
lean_dec_ref_known(v_parens_1285_, 1);
v_snd_1300_ = lean_ctor_get(v___x_1298_, 1);
lean_inc(v_snd_1300_);
lean_dec_ref(v___x_1298_);
v_snd_1301_ = lean_ctor_get(v_val_1299_, 1);
lean_inc(v_snd_1301_);
lean_dec(v_val_1299_);
v___x_1302_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_snd_1301_, v___x_1294_, v_snd_1300_);
return v___x_1302_;
}
else
{
lean_object* v_snd_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1311_; 
lean_dec(v_parens_1285_);
v_snd_1303_ = lean_ctor_get(v___x_1298_, 1);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1311_ == 0)
{
lean_object* v_unused_1312_; 
v_unused_1312_ = lean_ctor_get(v___x_1298_, 0);
lean_dec(v_unused_1312_);
v___x_1305_ = v___x_1298_;
v_isShared_1306_ = v_isSharedCheck_1311_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_snd_1303_);
lean_dec(v___x_1298_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1311_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1307_; lean_object* v___x_1309_; 
v___x_1307_ = lean_box(0);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 0, v___x_1307_);
v___x_1309_ = v___x_1305_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_snd_1303_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
default: 
{
lean_object* v_sign_1318_; lean_object* v_name_1319_; uint8_t v___x_1320_; lean_object* v___x_1321_; lean_object* v_snd_1322_; uint8_t v___x_1323_; lean_object* v___x_1324_; 
v_sign_1318_ = lean_ctor_get(v_val_1281_, 1);
lean_inc(v_sign_1318_);
v_name_1319_ = lean_ctor_get(v_val_1281_, 2);
lean_inc(v_name_1319_);
lean_dec_ref_known(v_val_1281_, 3);
v___x_1320_ = 0;
v___x_1321_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_sign_1318_, v___x_1320_, v_a_1277_);
v_snd_1322_ = lean_ctor_get(v___x_1321_, 1);
lean_inc(v_snd_1322_);
lean_dec_ref(v___x_1321_);
v___x_1323_ = 2;
v___x_1324_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1319_, v___x_1323_, v_snd_1322_);
return v___x_1324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goTarget(lean_object* v_tgt_1325_, lean_object* v_a_1326_){
_start:
{
if (lean_obj_tag(v_tgt_1325_) == 0)
{
lean_object* v_opener_1327_; lean_object* v_url_1328_; lean_object* v_closer_1329_; uint8_t v___x_1330_; lean_object* v___x_1331_; lean_object* v_snd_1332_; uint8_t v___x_1333_; lean_object* v___x_1334_; lean_object* v_snd_1335_; lean_object* v___x_1336_; 
v_opener_1327_ = lean_ctor_get(v_tgt_1325_, 1);
lean_inc(v_opener_1327_);
v_url_1328_ = lean_ctor_get(v_tgt_1325_, 2);
lean_inc(v_url_1328_);
v_closer_1329_ = lean_ctor_get(v_tgt_1325_, 3);
lean_inc(v_closer_1329_);
lean_dec_ref_known(v_tgt_1325_, 4);
v___x_1330_ = 0;
v___x_1331_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1327_, v___x_1330_, v_a_1326_);
v_snd_1332_ = lean_ctor_get(v___x_1331_, 1);
lean_inc(v_snd_1332_);
lean_dec_ref(v___x_1331_);
v___x_1333_ = 18;
v___x_1334_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_url_1328_, v___x_1333_, v_snd_1332_);
v_snd_1335_ = lean_ctor_get(v___x_1334_, 1);
lean_inc(v_snd_1335_);
lean_dec_ref(v___x_1334_);
v___x_1336_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1329_, v___x_1330_, v_snd_1335_);
return v___x_1336_;
}
else
{
lean_object* v_opener_1337_; lean_object* v_name_1338_; lean_object* v_closer_1339_; uint8_t v___x_1340_; lean_object* v___x_1341_; lean_object* v_snd_1342_; uint8_t v___x_1343_; lean_object* v___x_1344_; lean_object* v_snd_1345_; lean_object* v___x_1346_; 
v_opener_1337_ = lean_ctor_get(v_tgt_1325_, 1);
lean_inc(v_opener_1337_);
v_name_1338_ = lean_ctor_get(v_tgt_1325_, 2);
lean_inc(v_name_1338_);
v_closer_1339_ = lean_ctor_get(v_tgt_1325_, 3);
lean_inc(v_closer_1339_);
lean_dec_ref_known(v_tgt_1325_, 4);
v___x_1340_ = 0;
v___x_1341_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1337_, v___x_1340_, v_a_1326_);
v_snd_1342_ = lean_ctor_get(v___x_1341_, 1);
lean_inc(v_snd_1342_);
lean_dec_ref(v___x_1341_);
v___x_1343_ = 2;
v___x_1344_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1338_, v___x_1343_, v_snd_1342_);
v_snd_1345_ = lean_ctor_get(v___x_1344_, 1);
lean_inc(v_snd_1345_);
lean_dec_ref(v___x_1344_);
v___x_1346_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1339_, v___x_1340_, v_snd_1345_);
return v___x_1346_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode_spec__0(lean_object* v_as_1347_, size_t v_sz_1348_, size_t v_i_1349_, lean_object* v_b_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v_a_1353_; lean_object* v_snd_1354_; uint8_t v___x_1358_; 
v___x_1358_ = lean_usize_dec_lt(v_i_1349_, v_sz_1348_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; 
v___x_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1359_, 0, v_b_1350_);
lean_ctor_set(v___x_1359_, 1, v___y_1351_);
return v___x_1359_;
}
else
{
lean_object* v___x_1360_; lean_object* v_a_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1360_ = lean_box(0);
v_a_1361_ = lean_array_uget_borrowed(v_as_1347_, v_i_1349_);
v___x_1362_ = l_Lean_TSyntax_getVersoCodeLine(v_a_1361_);
v___x_1363_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine(v_a_1361_, v___x_1362_);
lean_dec_ref(v___x_1362_);
if (lean_obj_tag(v___x_1363_) == 1)
{
lean_object* v_val_1364_; uint8_t v___x_1365_; lean_object* v___x_1366_; lean_object* v_snd_1367_; 
v_val_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_val_1364_);
lean_dec_ref_known(v___x_1363_, 1);
v___x_1365_ = 18;
v___x_1366_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_val_1364_, v___x_1365_, v___y_1351_);
v_snd_1367_ = lean_ctor_get(v___x_1366_, 1);
lean_inc(v_snd_1367_);
lean_dec_ref(v___x_1366_);
v_a_1353_ = v___x_1360_;
v_snd_1354_ = v_snd_1367_;
goto v___jp_1352_;
}
else
{
lean_dec(v___x_1363_);
v_a_1353_ = v___x_1360_;
v_snd_1354_ = v___y_1351_;
goto v___jp_1352_;
}
}
v___jp_1352_:
{
size_t v___x_1355_; size_t v___x_1356_; 
v___x_1355_ = ((size_t)1ULL);
v___x_1356_ = lean_usize_add(v_i_1349_, v___x_1355_);
v_i_1349_ = v___x_1356_;
v_b_1350_ = v_a_1353_;
v___y_1351_ = v_snd_1354_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1347_ = stack[0].m_obj;
size_t v_sz_1348_ = stack[1].m_num;
size_t v_i_1349_ = stack[2].m_num;
lean_object* v_b_1350_ = stack[3].m_obj;
lean_object* v___y_1351_ = stack[4].m_obj;
lean_object* v_res_1368_;
v_res_1368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode_spec__0(v_as_1347_, v_sz_1348_, v_i_1349_, v_b_1350_, v___y_1351_);
stack->m_obj
 = v_res_1368_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode_spec__0___boxed(lean_object* v_as_1369_, lean_object* v_sz_1370_, lean_object* v_i_1371_, lean_object* v_b_1372_, lean_object* v___y_1373_){
_start:
{
size_t v_sz_boxed_1374_; size_t v_i_boxed_1375_; lean_object* v_res_1376_; 
v_sz_boxed_1374_ = lean_unbox_usize(v_sz_1370_);
lean_dec(v_sz_1370_);
v_i_boxed_1375_ = lean_unbox_usize(v_i_1371_);
lean_dec(v_i_1371_);
v_res_1376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode_spec__0(v_as_1369_, v_sz_boxed_1374_, v_i_boxed_1375_, v_b_1372_, v___y_1373_);
lean_dec_ref(v_as_1369_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode(lean_object* v_code_1377_, lean_object* v_a_1378_){
_start:
{
lean_object* v_opener_1379_; lean_object* v_content_1380_; lean_object* v_closer_1381_; uint8_t v___x_1382_; lean_object* v___x_1383_; lean_object* v_snd_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; size_t v_sz_1387_; size_t v___x_1388_; lean_object* v___x_1389_; lean_object* v_snd_1390_; lean_object* v___x_1391_; 
v_opener_1379_ = lean_ctor_get(v_code_1377_, 1);
lean_inc(v_opener_1379_);
v_content_1380_ = lean_ctor_get(v_code_1377_, 2);
lean_inc(v_content_1380_);
v_closer_1381_ = lean_ctor_get(v_code_1377_, 3);
lean_inc(v_closer_1381_);
lean_dec_ref(v_code_1377_);
v___x_1382_ = 0;
v___x_1383_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1379_, v___x_1382_, v_a_1378_);
v_snd_1384_ = lean_ctor_get(v___x_1383_, 1);
lean_inc(v_snd_1384_);
lean_dec_ref(v___x_1383_);
v___x_1385_ = l_Lean_TSyntax_getVersoCodeLines(v_content_1380_);
lean_dec(v_content_1380_);
v___x_1386_ = lean_box(0);
v_sz_1387_ = lean_array_size(v___x_1385_);
v___x_1388_ = ((size_t)0ULL);
v___x_1389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode_spec__0(v___x_1385_, v_sz_1387_, v___x_1388_, v___x_1386_, v_snd_1384_);
lean_dec_ref(v___x_1385_);
v_snd_1390_ = lean_ctor_get(v___x_1389_, 1);
lean_inc(v_snd_1390_);
lean_dec_ref(v___x_1389_);
v___x_1391_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1381_, v___x_1382_, v_snd_1390_);
return v___x_1391_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(lean_object* v_as_1392_, size_t v_sz_1393_, size_t v_i_1394_, lean_object* v_b_1395_, lean_object* v___y_1396_){
_start:
{
uint8_t v___x_1397_; 
v___x_1397_ = lean_usize_dec_lt(v_i_1394_, v_sz_1393_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; 
v___x_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1398_, 0, v_b_1395_);
lean_ctor_set(v___x_1398_, 1, v___y_1396_);
return v___x_1398_;
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1400_; lean_object* v_snd_1401_; lean_object* v___x_1402_; size_t v___x_1403_; size_t v___x_1404_; 
v_a_1399_ = lean_array_uget_borrowed(v_as_1392_, v_i_1394_);
lean_inc(v_a_1399_);
v___x_1400_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goArg(v_a_1399_, v___y_1396_);
v_snd_1401_ = lean_ctor_get(v___x_1400_, 1);
lean_inc(v_snd_1401_);
lean_dec_ref(v___x_1400_);
v___x_1402_ = lean_box(0);
v___x_1403_ = ((size_t)1ULL);
v___x_1404_ = lean_usize_add(v_i_1394_, v___x_1403_);
v_i_1394_ = v___x_1404_;
v_b_1395_ = v___x_1402_;
v___y_1396_ = v_snd_1401_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1392_ = stack[0].m_obj;
size_t v_sz_1393_ = stack[1].m_num;
size_t v_i_1394_ = stack[2].m_num;
lean_object* v_b_1395_ = stack[3].m_obj;
lean_object* v___y_1396_ = stack[4].m_obj;
lean_object* v_res_1406_;
v_res_1406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(v_as_1392_, v_sz_1393_, v_i_1394_, v_b_1395_, v___y_1396_);
stack->m_obj
 = v_res_1406_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2___boxed(lean_object* v_as_1407_, lean_object* v_sz_1408_, lean_object* v_i_1409_, lean_object* v_b_1410_, lean_object* v___y_1411_){
_start:
{
size_t v_sz_boxed_1412_; size_t v_i_boxed_1413_; lean_object* v_res_1414_; 
v_sz_boxed_1412_ = lean_unbox_usize(v_sz_1408_);
lean_dec(v_sz_1408_);
v_i_boxed_1413_ = lean_unbox_usize(v_i_1409_);
lean_dec(v_i_1409_);
v_res_1414_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(v_as_1407_, v_sz_boxed_1412_, v_i_boxed_1413_, v_b_1410_, v___y_1411_);
lean_dec_ref(v_as_1407_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem(lean_object* v_getTokens_1415_, lean_object* v_marker_1416_, lean_object* v_contents_1417_, lean_object* v_a_1418_){
_start:
{
uint8_t v___x_1419_; lean_object* v___x_1420_; lean_object* v_snd_1421_; lean_object* v___x_1422_; size_t v_sz_1423_; size_t v___x_1424_; lean_object* v___x_1425_; lean_object* v_snd_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
v___x_1419_ = 0;
v___x_1420_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_marker_1416_, v___x_1419_, v_a_1418_);
v_snd_1421_ = lean_ctor_get(v___x_1420_, 1);
lean_inc(v_snd_1421_);
lean_dec_ref(v___x_1420_);
v___x_1422_ = lean_box(0);
v_sz_1423_ = lean_array_size(v_contents_1417_);
v___x_1424_ = ((size_t)0ULL);
v___x_1425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1415_, v_contents_1417_, v_sz_1423_, v___x_1424_, v___x_1422_, v_snd_1421_);
v_snd_1426_ = lean_ctor_get(v___x_1425_, 1);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1433_ == 0)
{
lean_object* v_unused_1434_; 
v_unused_1434_ = lean_ctor_get(v___x_1425_, 0);
lean_dec(v_unused_1434_);
v___x_1428_ = v___x_1425_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_snd_1426_);
lean_dec(v___x_1425_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 0, v___x_1422_);
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_snd_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3(lean_object* v_getTokens_1435_, lean_object* v_as_1436_, size_t v_sz_1437_, size_t v_i_1438_, lean_object* v_b_1439_, lean_object* v___y_1440_){
_start:
{
uint8_t v___x_1441_; 
v___x_1441_ = lean_usize_dec_lt(v_i_1438_, v_sz_1437_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1442_; 
lean_dec_ref(v_getTokens_1435_);
v___x_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1442_, 0, v_b_1439_);
lean_ctor_set(v___x_1442_, 1, v___y_1440_);
return v___x_1442_;
}
else
{
lean_object* v_a_1443_; lean_object* v_marker_1444_; lean_object* v_contents_1445_; lean_object* v___x_1446_; lean_object* v_snd_1447_; lean_object* v___x_1448_; size_t v___x_1449_; size_t v___x_1450_; 
v_a_1443_ = lean_array_uget_borrowed(v_as_1436_, v_i_1438_);
v_marker_1444_ = lean_ctor_get(v_a_1443_, 1);
v_contents_1445_ = lean_ctor_get(v_a_1443_, 2);
lean_inc(v_marker_1444_);
lean_inc_ref(v_getTokens_1435_);
v___x_1446_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem(v_getTokens_1435_, v_marker_1444_, v_contents_1445_, v___y_1440_);
v_snd_1447_ = lean_ctor_get(v___x_1446_, 1);
lean_inc(v_snd_1447_);
lean_dec_ref(v___x_1446_);
v___x_1448_ = lean_box(0);
v___x_1449_ = ((size_t)1ULL);
v___x_1450_ = lean_usize_add(v_i_1438_, v___x_1449_);
v_i_1438_ = v___x_1450_;
v_b_1439_ = v___x_1448_;
v___y_1440_ = v_snd_1447_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_getTokens_1435_ = stack[0].m_obj;
lean_object* v_as_1436_ = stack[1].m_obj;
size_t v_sz_1437_ = stack[2].m_num;
size_t v_i_1438_ = stack[3].m_num;
lean_object* v_b_1439_ = stack[4].m_obj;
lean_object* v___y_1440_ = stack[5].m_obj;
lean_object* v_res_1452_;
v_res_1452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3(v_getTokens_1435_, v_as_1436_, v_sz_1437_, v_i_1438_, v_b_1439_, v___y_1440_);
stack->m_obj
 = v_res_1452_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__4(lean_object* v_getTokens_1453_, lean_object* v_as_1454_, size_t v_sz_1455_, size_t v_i_1456_, lean_object* v_b_1457_, lean_object* v___y_1458_){
_start:
{
uint8_t v___x_1459_; 
v___x_1459_ = lean_usize_dec_lt(v_i_1456_, v_sz_1455_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; 
lean_dec_ref(v_getTokens_1453_);
v___x_1460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1460_, 0, v_b_1457_);
lean_ctor_set(v___x_1460_, 1, v___y_1458_);
return v___x_1460_;
}
else
{
lean_object* v_a_1461_; lean_object* v_marker_1462_; lean_object* v_contents_1463_; lean_object* v___x_1464_; lean_object* v_snd_1465_; lean_object* v___x_1466_; size_t v___x_1467_; size_t v___x_1468_; 
v_a_1461_ = lean_array_uget_borrowed(v_as_1454_, v_i_1456_);
v_marker_1462_ = lean_ctor_get(v_a_1461_, 1);
v_contents_1463_ = lean_ctor_get(v_a_1461_, 2);
lean_inc(v_marker_1462_);
lean_inc_ref(v_getTokens_1453_);
v___x_1464_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem(v_getTokens_1453_, v_marker_1462_, v_contents_1463_, v___y_1458_);
v_snd_1465_ = lean_ctor_get(v___x_1464_, 1);
lean_inc(v_snd_1465_);
lean_dec_ref(v___x_1464_);
v___x_1466_ = lean_box(0);
v___x_1467_ = ((size_t)1ULL);
v___x_1468_ = lean_usize_add(v_i_1456_, v___x_1467_);
v_i_1456_ = v___x_1468_;
v_b_1457_ = v___x_1466_;
v___y_1458_ = v_snd_1465_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_getTokens_1453_ = stack[0].m_obj;
lean_object* v_as_1454_ = stack[1].m_obj;
size_t v_sz_1455_ = stack[2].m_num;
size_t v_i_1456_ = stack[3].m_num;
lean_object* v_b_1457_ = stack[4].m_obj;
lean_object* v___y_1458_ = stack[5].m_obj;
lean_object* v_res_1470_;
v_res_1470_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__4(v_getTokens_1453_, v_as_1454_, v_sz_1455_, v_i_1456_, v_b_1457_, v___y_1458_);
stack->m_obj
 = v_res_1470_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDesc(lean_object* v_getTokens_1471_, lean_object* v_item_1472_, lean_object* v_a_1473_){
_start:
{
lean_object* v_marker_1474_; lean_object* v_term_1475_; lean_object* v_desc_1476_; uint8_t v___x_1477_; lean_object* v___x_1478_; lean_object* v_snd_1479_; lean_object* v___x_1480_; size_t v_sz_1481_; size_t v___x_1482_; lean_object* v___x_1483_; lean_object* v_snd_1484_; size_t v_sz_1485_; lean_object* v___x_1486_; lean_object* v_snd_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
v_marker_1474_ = lean_ctor_get(v_item_1472_, 1);
lean_inc(v_marker_1474_);
v_term_1475_ = lean_ctor_get(v_item_1472_, 2);
lean_inc_ref(v_term_1475_);
v_desc_1476_ = lean_ctor_get(v_item_1472_, 3);
lean_inc_ref(v_desc_1476_);
lean_dec_ref(v_item_1472_);
v___x_1477_ = 0;
v___x_1478_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_marker_1474_, v___x_1477_, v_a_1473_);
v_snd_1479_ = lean_ctor_get(v___x_1478_, 1);
lean_inc(v_snd_1479_);
lean_dec_ref(v___x_1478_);
v___x_1480_ = lean_box(0);
v_sz_1481_ = lean_array_size(v_term_1475_);
v___x_1482_ = ((size_t)0ULL);
lean_inc_ref(v_getTokens_1471_);
v___x_1483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1471_, v_term_1475_, v_sz_1481_, v___x_1482_, v___x_1480_, v_snd_1479_);
lean_dec_ref(v_term_1475_);
v_snd_1484_ = lean_ctor_get(v___x_1483_, 1);
lean_inc(v_snd_1484_);
lean_dec_ref(v___x_1483_);
v_sz_1485_ = lean_array_size(v_desc_1476_);
v___x_1486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1471_, v_desc_1476_, v_sz_1485_, v___x_1482_, v___x_1480_, v_snd_1484_);
lean_dec_ref(v_desc_1476_);
v_snd_1487_ = lean_ctor_get(v___x_1486_, 1);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1494_ == 0)
{
lean_object* v_unused_1495_; 
v_unused_1495_ = lean_ctor_get(v___x_1486_, 0);
lean_dec(v_unused_1495_);
v___x_1489_ = v___x_1486_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_snd_1487_);
lean_dec(v___x_1486_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 0, v___x_1480_);
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1480_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v_snd_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__5(lean_object* v_getTokens_1496_, lean_object* v_as_1497_, size_t v_sz_1498_, size_t v_i_1499_, lean_object* v_b_1500_, lean_object* v___y_1501_){
_start:
{
uint8_t v___x_1502_; 
v___x_1502_ = lean_usize_dec_lt(v_i_1499_, v_sz_1498_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1503_; 
lean_dec_ref(v_getTokens_1496_);
v___x_1503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1503_, 0, v_b_1500_);
lean_ctor_set(v___x_1503_, 1, v___y_1501_);
return v___x_1503_;
}
else
{
lean_object* v_a_1504_; lean_object* v___x_1505_; lean_object* v_snd_1506_; lean_object* v___x_1507_; size_t v___x_1508_; size_t v___x_1509_; 
v_a_1504_ = lean_array_uget_borrowed(v_as_1497_, v_i_1499_);
lean_inc(v_a_1504_);
lean_inc_ref(v_getTokens_1496_);
v___x_1505_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDesc(v_getTokens_1496_, v_a_1504_, v___y_1501_);
v_snd_1506_ = lean_ctor_get(v___x_1505_, 1);
lean_inc(v_snd_1506_);
lean_dec_ref(v___x_1505_);
v___x_1507_ = lean_box(0);
v___x_1508_ = ((size_t)1ULL);
v___x_1509_ = lean_usize_add(v_i_1499_, v___x_1508_);
v_i_1499_ = v___x_1509_;
v_b_1500_ = v___x_1507_;
v___y_1501_ = v_snd_1506_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_getTokens_1496_ = stack[0].m_obj;
lean_object* v_as_1497_ = stack[1].m_obj;
size_t v_sz_1498_ = stack[2].m_num;
size_t v_i_1499_ = stack[3].m_num;
lean_object* v_b_1500_ = stack[4].m_obj;
lean_object* v___y_1501_ = stack[5].m_obj;
lean_object* v_res_1511_;
v_res_1511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__5(v_getTokens_1496_, v_as_1497_, v_sz_1498_, v_i_1499_, v_b_1500_, v___y_1501_);
stack->m_obj
 = v_res_1511_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6(lean_object* v_getTokens_1512_, lean_object* v_as_1513_, size_t v_i_1514_, size_t v_stop_1515_, lean_object* v_b_1516_, lean_object* v___y_1517_){
_start:
{
uint8_t v___x_1518_; 
v___x_1518_ = lean_usize_dec_eq(v_i_1514_, v_stop_1515_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v_fst_1521_; lean_object* v_snd_1522_; size_t v___x_1523_; size_t v___x_1524_; 
v___x_1519_ = lean_array_uget_borrowed(v_as_1513_, v_i_1514_);
lean_inc(v___x_1519_);
lean_inc_ref(v_getTokens_1512_);
v___x_1520_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_getTokens_1512_, v___x_1519_, v___y_1517_);
v_fst_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_fst_1521_);
v_snd_1522_ = lean_ctor_get(v___x_1520_, 1);
lean_inc(v_snd_1522_);
lean_dec_ref(v___x_1520_);
v___x_1523_ = ((size_t)1ULL);
v___x_1524_ = lean_usize_add(v_i_1514_, v___x_1523_);
v_i_1514_ = v___x_1524_;
v_b_1516_ = v_fst_1521_;
v___y_1517_ = v_snd_1522_;
goto _start;
}
else
{
lean_object* v___x_1526_; 
lean_dec_ref(v_getTokens_1512_);
v___x_1526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1526_, 0, v_b_1516_);
lean_ctor_set(v___x_1526_, 1, v___y_1517_);
return v___x_1526_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_getTokens_1512_ = stack[0].m_obj;
lean_object* v_as_1513_ = stack[1].m_obj;
size_t v_i_1514_ = stack[2].m_num;
size_t v_stop_1515_ = stack[3].m_num;
lean_object* v_b_1516_ = stack[4].m_obj;
lean_object* v___y_1517_ = stack[5].m_obj;
lean_object* v_res_1527_;
v_res_1527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6(v_getTokens_1512_, v_as_1513_, v_i_1514_, v_stop_1515_, v_b_1516_, v___y_1517_);
stack->m_obj
 = v_res_1527_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(lean_object* v_getTokens_1528_, lean_object* v_stx_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v___x_1531_; 
lean_inc(v_stx_1529_);
v___x_1531_ = l_Lean_Doc_InlineView_of(v_stx_1529_);
if (lean_obj_tag(v___x_1531_) == 1)
{
lean_object* v_val_1532_; 
lean_dec(v_stx_1529_);
v_val_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_val_1532_);
lean_dec_ref_known(v___x_1531_, 1);
switch(lean_obj_tag(v_val_1532_))
{
case 1:
{
lean_object* v_view_1533_; lean_object* v_opener_1534_; lean_object* v_content_1535_; lean_object* v_closer_1536_; lean_object* v___x_1537_; 
v_view_1533_ = lean_ctor_get(v_val_1532_, 0);
lean_inc_ref(v_view_1533_);
lean_dec_ref_known(v_val_1532_, 1);
v_opener_1534_ = lean_ctor_get(v_view_1533_, 1);
lean_inc(v_opener_1534_);
v_content_1535_ = lean_ctor_get(v_view_1533_, 2);
lean_inc_ref(v_content_1535_);
v_closer_1536_ = lean_ctor_get(v_view_1533_, 3);
lean_inc(v_closer_1536_);
lean_dec_ref(v_view_1533_);
v___x_1537_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDelimited(v_getTokens_1528_, v_opener_1534_, v_closer_1536_, v_content_1535_, v_a_1530_);
lean_dec_ref(v_content_1535_);
return v___x_1537_;
}
case 2:
{
lean_object* v_view_1538_; lean_object* v_opener_1539_; lean_object* v_content_1540_; lean_object* v_closer_1541_; lean_object* v___x_1542_; 
v_view_1538_ = lean_ctor_get(v_val_1532_, 0);
lean_inc_ref(v_view_1538_);
lean_dec_ref_known(v_val_1532_, 1);
v_opener_1539_ = lean_ctor_get(v_view_1538_, 1);
lean_inc(v_opener_1539_);
v_content_1540_ = lean_ctor_get(v_view_1538_, 2);
lean_inc_ref(v_content_1540_);
v_closer_1541_ = lean_ctor_get(v_view_1538_, 3);
lean_inc(v_closer_1541_);
lean_dec_ref(v_view_1538_);
v___x_1542_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDelimited(v_getTokens_1528_, v_opener_1539_, v_closer_1541_, v_content_1540_, v_a_1530_);
lean_dec_ref(v_content_1540_);
return v___x_1542_;
}
case 3:
{
lean_object* v_view_1543_; lean_object* v___x_1544_; 
lean_dec_ref(v_getTokens_1528_);
v_view_1543_ = lean_ctor_get(v_val_1532_, 0);
lean_inc_ref(v_view_1543_);
lean_dec_ref_known(v_val_1532_, 1);
v___x_1544_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode(v_view_1543_, v_a_1530_);
return v___x_1544_;
}
case 4:
{
lean_object* v_view_1545_; lean_object* v_marker_1546_; lean_object* v_code_1547_; uint8_t v___x_1548_; lean_object* v___x_1549_; lean_object* v_snd_1550_; lean_object* v___x_1551_; 
lean_dec_ref(v_getTokens_1528_);
v_view_1545_ = lean_ctor_get(v_val_1532_, 0);
lean_inc_ref(v_view_1545_);
lean_dec_ref_known(v_val_1532_, 1);
v_marker_1546_ = lean_ctor_get(v_view_1545_, 1);
lean_inc(v_marker_1546_);
v_code_1547_ = lean_ctor_get(v_view_1545_, 2);
lean_inc_ref(v_code_1547_);
lean_dec_ref(v_view_1545_);
v___x_1548_ = 0;
v___x_1549_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_marker_1546_, v___x_1548_, v_a_1530_);
v_snd_1550_ = lean_ctor_get(v___x_1549_, 1);
lean_inc(v_snd_1550_);
lean_dec_ref(v___x_1549_);
v___x_1551_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode(v_code_1547_, v_snd_1550_);
return v___x_1551_;
}
case 5:
{
lean_object* v_view_1552_; lean_object* v_opener_1553_; lean_object* v_content_1554_; lean_object* v_closer_1555_; lean_object* v_target_1556_; lean_object* v___x_1557_; lean_object* v_snd_1558_; lean_object* v___x_1559_; 
v_view_1552_ = lean_ctor_get(v_val_1532_, 0);
lean_inc_ref(v_view_1552_);
lean_dec_ref_known(v_val_1532_, 1);
v_opener_1553_ = lean_ctor_get(v_view_1552_, 1);
lean_inc(v_opener_1553_);
v_content_1554_ = lean_ctor_get(v_view_1552_, 2);
lean_inc_ref(v_content_1554_);
v_closer_1555_ = lean_ctor_get(v_view_1552_, 3);
lean_inc(v_closer_1555_);
v_target_1556_ = lean_ctor_get(v_view_1552_, 4);
lean_inc_ref(v_target_1556_);
lean_dec_ref(v_view_1552_);
v___x_1557_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDelimited(v_getTokens_1528_, v_opener_1553_, v_closer_1555_, v_content_1554_, v_a_1530_);
lean_dec_ref(v_content_1554_);
v_snd_1558_ = lean_ctor_get(v___x_1557_, 1);
lean_inc(v_snd_1558_);
lean_dec_ref(v___x_1557_);
v___x_1559_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goTarget(v_target_1556_, v_snd_1558_);
return v___x_1559_;
}
case 6:
{
lean_object* v_view_1560_; lean_object* v_opener_1561_; lean_object* v_alt_1562_; lean_object* v_closer_1563_; lean_object* v_target_1564_; uint8_t v___x_1565_; lean_object* v___x_1566_; lean_object* v_snd_1567_; uint8_t v___x_1568_; lean_object* v___x_1569_; lean_object* v_snd_1570_; lean_object* v___x_1571_; lean_object* v_snd_1572_; lean_object* v___x_1573_; 
lean_dec_ref(v_getTokens_1528_);
v_view_1560_ = lean_ctor_get(v_val_1532_, 0);
lean_inc_ref(v_view_1560_);
lean_dec_ref_known(v_val_1532_, 1);
v_opener_1561_ = lean_ctor_get(v_view_1560_, 1);
lean_inc(v_opener_1561_);
v_alt_1562_ = lean_ctor_get(v_view_1560_, 2);
lean_inc(v_alt_1562_);
v_closer_1563_ = lean_ctor_get(v_view_1560_, 3);
lean_inc(v_closer_1563_);
v_target_1564_ = lean_ctor_get(v_view_1560_, 4);
lean_inc_ref(v_target_1564_);
lean_dec_ref(v_view_1560_);
v___x_1565_ = 0;
v___x_1566_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1561_, v___x_1565_, v_a_1530_);
v_snd_1567_ = lean_ctor_get(v___x_1566_, 1);
lean_inc(v_snd_1567_);
lean_dec_ref(v___x_1566_);
v___x_1568_ = 18;
v___x_1569_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_alt_1562_, v___x_1568_, v_snd_1567_);
v_snd_1570_ = lean_ctor_get(v___x_1569_, 1);
lean_inc(v_snd_1570_);
lean_dec_ref(v___x_1569_);
v___x_1571_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1563_, v___x_1565_, v_snd_1570_);
v_snd_1572_ = lean_ctor_get(v___x_1571_, 1);
lean_inc(v_snd_1572_);
lean_dec_ref(v___x_1571_);
v___x_1573_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goTarget(v_target_1564_, v_snd_1572_);
return v___x_1573_;
}
case 7:
{
lean_object* v_view_1574_; lean_object* v_opener_1575_; lean_object* v_name_1576_; lean_object* v_closer_1577_; uint8_t v___x_1578_; lean_object* v___x_1579_; lean_object* v_snd_1580_; uint8_t v___x_1581_; lean_object* v___x_1582_; lean_object* v_snd_1583_; lean_object* v___x_1584_; 
lean_dec_ref(v_getTokens_1528_);
v_view_1574_ = lean_ctor_get(v_val_1532_, 0);
lean_inc_ref(v_view_1574_);
lean_dec_ref_known(v_val_1532_, 1);
v_opener_1575_ = lean_ctor_get(v_view_1574_, 1);
lean_inc(v_opener_1575_);
v_name_1576_ = lean_ctor_get(v_view_1574_, 2);
lean_inc(v_name_1576_);
v_closer_1577_ = lean_ctor_get(v_view_1574_, 3);
lean_inc(v_closer_1577_);
lean_dec_ref(v_view_1574_);
v___x_1578_ = 0;
v___x_1579_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1575_, v___x_1578_, v_a_1530_);
v_snd_1580_ = lean_ctor_get(v___x_1579_, 1);
lean_inc(v_snd_1580_);
lean_dec_ref(v___x_1579_);
v___x_1581_ = 2;
v___x_1582_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1576_, v___x_1581_, v_snd_1580_);
v_snd_1583_ = lean_ctor_get(v___x_1582_, 1);
lean_inc(v_snd_1583_);
lean_dec_ref(v___x_1582_);
v___x_1584_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1577_, v___x_1578_, v_snd_1583_);
return v___x_1584_;
}
case 9:
{
lean_object* v_view_1585_; lean_object* v_braceOpen_1586_; lean_object* v_name_1587_; lean_object* v_args_1588_; lean_object* v_braceClose_1589_; lean_object* v_brackets_1590_; lean_object* v_content_1591_; uint8_t v___x_1592_; lean_object* v___x_1593_; lean_object* v_snd_1594_; uint8_t v___x_1595_; lean_object* v___x_1596_; lean_object* v_snd_1597_; lean_object* v___x_1598_; lean_object* v___y_1600_; size_t v_sz_1617_; size_t v___x_1618_; lean_object* v___x_1619_; lean_object* v_snd_1620_; lean_object* v___x_1621_; 
v_view_1585_ = lean_ctor_get(v_val_1532_, 0);
lean_inc_ref(v_view_1585_);
lean_dec_ref_known(v_val_1532_, 1);
v_braceOpen_1586_ = lean_ctor_get(v_view_1585_, 1);
lean_inc(v_braceOpen_1586_);
v_name_1587_ = lean_ctor_get(v_view_1585_, 2);
lean_inc(v_name_1587_);
v_args_1588_ = lean_ctor_get(v_view_1585_, 3);
lean_inc_ref(v_args_1588_);
v_braceClose_1589_ = lean_ctor_get(v_view_1585_, 4);
lean_inc(v_braceClose_1589_);
v_brackets_1590_ = lean_ctor_get(v_view_1585_, 5);
lean_inc(v_brackets_1590_);
v_content_1591_ = lean_ctor_get(v_view_1585_, 6);
lean_inc_ref(v_content_1591_);
lean_dec_ref(v_view_1585_);
v___x_1592_ = 0;
v___x_1593_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_braceOpen_1586_, v___x_1592_, v_a_1530_);
v_snd_1594_ = lean_ctor_get(v___x_1593_, 1);
lean_inc(v_snd_1594_);
lean_dec_ref(v___x_1593_);
v___x_1595_ = 3;
v___x_1596_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1587_, v___x_1595_, v_snd_1594_);
v_snd_1597_ = lean_ctor_get(v___x_1596_, 1);
lean_inc(v_snd_1597_);
lean_dec_ref(v___x_1596_);
v___x_1598_ = lean_box(0);
v_sz_1617_ = lean_array_size(v_args_1588_);
v___x_1618_ = ((size_t)0ULL);
v___x_1619_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(v_args_1588_, v_sz_1617_, v___x_1618_, v___x_1598_, v_snd_1597_);
lean_dec_ref(v_args_1588_);
v_snd_1620_ = lean_ctor_get(v___x_1619_, 1);
lean_inc(v_snd_1620_);
lean_dec_ref(v___x_1619_);
v___x_1621_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_braceClose_1589_, v___x_1592_, v_snd_1620_);
if (lean_obj_tag(v_brackets_1590_) == 1)
{
lean_object* v_val_1622_; lean_object* v_snd_1623_; lean_object* v_fst_1624_; lean_object* v___x_1625_; lean_object* v_snd_1626_; 
v_val_1622_ = lean_ctor_get(v_brackets_1590_, 0);
v_snd_1623_ = lean_ctor_get(v___x_1621_, 1);
lean_inc(v_snd_1623_);
lean_dec_ref(v___x_1621_);
v_fst_1624_ = lean_ctor_get(v_val_1622_, 0);
lean_inc(v_fst_1624_);
v___x_1625_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_fst_1624_, v___x_1592_, v_snd_1623_);
v_snd_1626_ = lean_ctor_get(v___x_1625_, 1);
lean_inc(v_snd_1626_);
lean_dec_ref(v___x_1625_);
v___y_1600_ = v_snd_1626_;
goto v___jp_1599_;
}
else
{
lean_object* v_snd_1627_; 
v_snd_1627_ = lean_ctor_get(v___x_1621_, 1);
lean_inc(v_snd_1627_);
lean_dec_ref(v___x_1621_);
v___y_1600_ = v_snd_1627_;
goto v___jp_1599_;
}
v___jp_1599_:
{
size_t v_sz_1601_; size_t v___x_1602_; lean_object* v___x_1603_; 
v_sz_1601_ = lean_array_size(v_content_1591_);
v___x_1602_ = ((size_t)0ULL);
v___x_1603_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1528_, v_content_1591_, v_sz_1601_, v___x_1602_, v___x_1598_, v___y_1600_);
lean_dec_ref(v_content_1591_);
if (lean_obj_tag(v_brackets_1590_) == 1)
{
lean_object* v_val_1604_; lean_object* v_snd_1605_; lean_object* v_snd_1606_; lean_object* v___x_1607_; 
v_val_1604_ = lean_ctor_get(v_brackets_1590_, 0);
lean_inc(v_val_1604_);
lean_dec_ref_known(v_brackets_1590_, 1);
v_snd_1605_ = lean_ctor_get(v___x_1603_, 1);
lean_inc(v_snd_1605_);
lean_dec_ref(v___x_1603_);
v_snd_1606_ = lean_ctor_get(v_val_1604_, 1);
lean_inc(v_snd_1606_);
lean_dec(v_val_1604_);
v___x_1607_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_snd_1606_, v___x_1592_, v_snd_1605_);
return v___x_1607_;
}
else
{
lean_object* v_snd_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
lean_dec(v_brackets_1590_);
v_snd_1608_ = lean_ctor_get(v___x_1603_, 1);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1615_ == 0)
{
lean_object* v_unused_1616_; 
v_unused_1616_ = lean_ctor_get(v___x_1603_, 0);
lean_dec(v_unused_1616_);
v___x_1610_ = v___x_1603_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_snd_1608_);
lean_dec(v___x_1603_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v___x_1598_);
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_snd_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
}
default: 
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
lean_dec(v_val_1532_);
lean_dec_ref(v_getTokens_1528_);
v___x_1628_ = lean_box(0);
v___x_1629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
lean_ctor_set(v___x_1629_, 1, v_a_1530_);
return v___x_1629_;
}
}
}
else
{
lean_object* v___x_1630_; 
lean_dec(v___x_1531_);
lean_inc(v_stx_1529_);
v___x_1630_ = l_Lean_Doc_BlockView_of(v_stx_1529_);
if (lean_obj_tag(v___x_1630_) == 1)
{
lean_object* v_val_1631_; 
lean_dec(v_stx_1529_);
v_val_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_val_1631_);
lean_dec_ref_known(v___x_1630_, 1);
switch(lean_obj_tag(v_val_1631_))
{
case 0:
{
lean_object* v_view_1632_; lean_object* v_content_1633_; lean_object* v___x_1634_; size_t v_sz_1635_; size_t v___x_1636_; lean_object* v___x_1637_; lean_object* v_snd_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
v_view_1632_ = lean_ctor_get(v_val_1631_, 0);
lean_inc_ref(v_view_1632_);
lean_dec_ref_known(v_val_1631_, 1);
v_content_1633_ = lean_ctor_get(v_view_1632_, 1);
lean_inc_ref(v_content_1633_);
lean_dec_ref(v_view_1632_);
v___x_1634_ = lean_box(0);
v_sz_1635_ = lean_array_size(v_content_1633_);
v___x_1636_ = ((size_t)0ULL);
v___x_1637_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1528_, v_content_1633_, v_sz_1635_, v___x_1636_, v___x_1634_, v_a_1530_);
lean_dec_ref(v_content_1633_);
v_snd_1638_ = lean_ctor_get(v___x_1637_, 1);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1645_ == 0)
{
lean_object* v_unused_1646_; 
v_unused_1646_ = lean_ctor_get(v___x_1637_, 0);
lean_dec(v_unused_1646_);
v___x_1640_ = v___x_1637_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_snd_1638_);
lean_dec(v___x_1637_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v___x_1634_);
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1634_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_snd_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
case 1:
{
lean_object* v_view_1647_; lean_object* v_items_1648_; lean_object* v___x_1649_; size_t v_sz_1650_; size_t v___x_1651_; lean_object* v___x_1652_; lean_object* v_snd_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
v_view_1647_ = lean_ctor_get(v_val_1631_, 0);
lean_inc_ref(v_view_1647_);
lean_dec_ref_known(v_val_1631_, 1);
v_items_1648_ = lean_ctor_get(v_view_1647_, 1);
lean_inc_ref(v_items_1648_);
lean_dec_ref(v_view_1647_);
v___x_1649_ = lean_box(0);
v_sz_1650_ = lean_array_size(v_items_1648_);
v___x_1651_ = ((size_t)0ULL);
v___x_1652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3(v_getTokens_1528_, v_items_1648_, v_sz_1650_, v___x_1651_, v___x_1649_, v_a_1530_);
lean_dec_ref(v_items_1648_);
v_snd_1653_ = lean_ctor_get(v___x_1652_, 1);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1660_ == 0)
{
lean_object* v_unused_1661_; 
v_unused_1661_ = lean_ctor_get(v___x_1652_, 0);
lean_dec(v_unused_1661_);
v___x_1655_ = v___x_1652_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_snd_1653_);
lean_dec(v___x_1652_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1649_);
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1649_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v_snd_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
case 2:
{
lean_object* v_view_1662_; lean_object* v_items_1663_; lean_object* v___x_1664_; size_t v_sz_1665_; size_t v___x_1666_; lean_object* v___x_1667_; lean_object* v_snd_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
v_view_1662_ = lean_ctor_get(v_val_1631_, 0);
lean_inc_ref(v_view_1662_);
lean_dec_ref_known(v_val_1631_, 1);
v_items_1663_ = lean_ctor_get(v_view_1662_, 2);
lean_inc_ref(v_items_1663_);
lean_dec_ref(v_view_1662_);
v___x_1664_ = lean_box(0);
v_sz_1665_ = lean_array_size(v_items_1663_);
v___x_1666_ = ((size_t)0ULL);
v___x_1667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__4(v_getTokens_1528_, v_items_1663_, v_sz_1665_, v___x_1666_, v___x_1664_, v_a_1530_);
lean_dec_ref(v_items_1663_);
v_snd_1668_ = lean_ctor_get(v___x_1667_, 1);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1675_ == 0)
{
lean_object* v_unused_1676_; 
v_unused_1676_ = lean_ctor_get(v___x_1667_, 0);
lean_dec(v_unused_1676_);
v___x_1670_ = v___x_1667_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_snd_1668_);
lean_dec(v___x_1667_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v___x_1664_);
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1664_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v_snd_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
case 3:
{
lean_object* v_view_1677_; lean_object* v_items_1678_; lean_object* v___x_1679_; size_t v_sz_1680_; size_t v___x_1681_; lean_object* v___x_1682_; lean_object* v_snd_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
v_view_1677_ = lean_ctor_get(v_val_1631_, 0);
lean_inc_ref(v_view_1677_);
lean_dec_ref_known(v_val_1631_, 1);
v_items_1678_ = lean_ctor_get(v_view_1677_, 1);
lean_inc_ref(v_items_1678_);
lean_dec_ref(v_view_1677_);
v___x_1679_ = lean_box(0);
v_sz_1680_ = lean_array_size(v_items_1678_);
v___x_1681_ = ((size_t)0ULL);
v___x_1682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__5(v_getTokens_1528_, v_items_1678_, v_sz_1680_, v___x_1681_, v___x_1679_, v_a_1530_);
lean_dec_ref(v_items_1678_);
v_snd_1683_ = lean_ctor_get(v___x_1682_, 1);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1690_ == 0)
{
lean_object* v_unused_1691_; 
v_unused_1691_ = lean_ctor_get(v___x_1682_, 0);
lean_dec(v_unused_1691_);
v___x_1685_ = v___x_1682_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_snd_1683_);
lean_dec(v___x_1682_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 0, v___x_1679_);
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v_snd_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
case 4:
{
lean_object* v_view_1692_; lean_object* v_marker_1693_; lean_object* v_content_1694_; uint8_t v___x_1695_; lean_object* v___x_1696_; lean_object* v_snd_1697_; lean_object* v___x_1698_; size_t v_sz_1699_; size_t v___x_1700_; lean_object* v___x_1701_; lean_object* v_snd_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
v_view_1692_ = lean_ctor_get(v_val_1631_, 0);
lean_inc_ref(v_view_1692_);
lean_dec_ref_known(v_val_1631_, 1);
v_marker_1693_ = lean_ctor_get(v_view_1692_, 1);
lean_inc(v_marker_1693_);
v_content_1694_ = lean_ctor_get(v_view_1692_, 2);
lean_inc_ref(v_content_1694_);
lean_dec_ref(v_view_1692_);
v___x_1695_ = 0;
v___x_1696_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_marker_1693_, v___x_1695_, v_a_1530_);
v_snd_1697_ = lean_ctor_get(v___x_1696_, 1);
lean_inc(v_snd_1697_);
lean_dec_ref(v___x_1696_);
v___x_1698_ = lean_box(0);
v_sz_1699_ = lean_array_size(v_content_1694_);
v___x_1700_ = ((size_t)0ULL);
v___x_1701_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1528_, v_content_1694_, v_sz_1699_, v___x_1700_, v___x_1698_, v_snd_1697_);
lean_dec_ref(v_content_1694_);
v_snd_1702_ = lean_ctor_get(v___x_1701_, 1);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1709_ == 0)
{
lean_object* v_unused_1710_; 
v_unused_1710_ = lean_ctor_get(v___x_1701_, 0);
lean_dec(v_unused_1710_);
v___x_1704_ = v___x_1701_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_snd_1702_);
lean_dec(v___x_1701_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 0, v___x_1698_);
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1698_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v_snd_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
case 5:
{
lean_object* v_view_1711_; lean_object* v_openFence_1712_; lean_object* v_name_x3f_1713_; lean_object* v_args_1714_; lean_object* v_content_1715_; lean_object* v_closeFence_1716_; uint8_t v___x_1717_; lean_object* v___y_1719_; lean_object* v___x_1727_; 
lean_dec_ref(v_getTokens_1528_);
v_view_1711_ = lean_ctor_get(v_val_1631_, 0);
lean_inc_ref(v_view_1711_);
lean_dec_ref_known(v_val_1631_, 1);
v_openFence_1712_ = lean_ctor_get(v_view_1711_, 1);
lean_inc(v_openFence_1712_);
v_name_x3f_1713_ = lean_ctor_get(v_view_1711_, 2);
lean_inc(v_name_x3f_1713_);
v_args_1714_ = lean_ctor_get(v_view_1711_, 3);
lean_inc_ref(v_args_1714_);
v_content_1715_ = lean_ctor_get(v_view_1711_, 4);
lean_inc(v_content_1715_);
v_closeFence_1716_ = lean_ctor_get(v_view_1711_, 5);
lean_inc(v_closeFence_1716_);
lean_dec_ref(v_view_1711_);
v___x_1717_ = 0;
v___x_1727_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_openFence_1712_, v___x_1717_, v_a_1530_);
if (lean_obj_tag(v_name_x3f_1713_) == 1)
{
lean_object* v_snd_1728_; lean_object* v_val_1729_; uint8_t v___x_1730_; lean_object* v___x_1731_; lean_object* v_snd_1732_; lean_object* v___x_1733_; size_t v_sz_1734_; size_t v___x_1735_; lean_object* v___x_1736_; lean_object* v_snd_1737_; 
v_snd_1728_ = lean_ctor_get(v___x_1727_, 1);
lean_inc(v_snd_1728_);
lean_dec_ref(v___x_1727_);
v_val_1729_ = lean_ctor_get(v_name_x3f_1713_, 0);
lean_inc(v_val_1729_);
lean_dec_ref_known(v_name_x3f_1713_, 1);
v___x_1730_ = 3;
v___x_1731_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_val_1729_, v___x_1730_, v_snd_1728_);
v_snd_1732_ = lean_ctor_get(v___x_1731_, 1);
lean_inc(v_snd_1732_);
lean_dec_ref(v___x_1731_);
v___x_1733_ = lean_box(0);
v_sz_1734_ = lean_array_size(v_args_1714_);
v___x_1735_ = ((size_t)0ULL);
v___x_1736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(v_args_1714_, v_sz_1734_, v___x_1735_, v___x_1733_, v_snd_1732_);
lean_dec_ref(v_args_1714_);
v_snd_1737_ = lean_ctor_get(v___x_1736_, 1);
lean_inc(v_snd_1737_);
lean_dec_ref(v___x_1736_);
v___y_1719_ = v_snd_1737_;
goto v___jp_1718_;
}
else
{
lean_object* v_snd_1738_; 
lean_dec_ref(v_args_1714_);
lean_dec(v_name_x3f_1713_);
v_snd_1738_ = lean_ctor_get(v___x_1727_, 1);
lean_inc(v_snd_1738_);
lean_dec_ref(v___x_1727_);
v___y_1719_ = v_snd_1738_;
goto v___jp_1718_;
}
v___jp_1718_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; size_t v_sz_1722_; size_t v___x_1723_; lean_object* v___x_1724_; lean_object* v_snd_1725_; lean_object* v___x_1726_; 
v___x_1720_ = l_Lean_TSyntax_getVersoCodeBlockLines(v_content_1715_);
lean_dec(v_content_1715_);
v___x_1721_ = lean_box(0);
v_sz_1722_ = lean_array_size(v___x_1720_);
v___x_1723_ = ((size_t)0ULL);
v___x_1724_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode_spec__0(v___x_1720_, v_sz_1722_, v___x_1723_, v___x_1721_, v___y_1719_);
lean_dec_ref(v___x_1720_);
v_snd_1725_ = lean_ctor_get(v___x_1724_, 1);
lean_inc(v_snd_1725_);
lean_dec_ref(v___x_1724_);
v___x_1726_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closeFence_1716_, v___x_1717_, v_snd_1725_);
return v___x_1726_;
}
}
case 6:
{
lean_object* v_view_1739_; lean_object* v_opener_1740_; lean_object* v_name_1741_; lean_object* v_args_1742_; lean_object* v_content_1743_; lean_object* v_closer_1744_; uint8_t v___x_1745_; lean_object* v___x_1746_; lean_object* v_snd_1747_; uint8_t v___x_1748_; lean_object* v___x_1749_; lean_object* v_snd_1750_; lean_object* v___x_1751_; size_t v_sz_1752_; size_t v___x_1753_; lean_object* v___x_1754_; lean_object* v_snd_1755_; size_t v_sz_1756_; lean_object* v___x_1757_; lean_object* v_snd_1758_; lean_object* v___x_1759_; 
v_view_1739_ = lean_ctor_get(v_val_1631_, 0);
lean_inc_ref(v_view_1739_);
lean_dec_ref_known(v_val_1631_, 1);
v_opener_1740_ = lean_ctor_get(v_view_1739_, 1);
lean_inc(v_opener_1740_);
v_name_1741_ = lean_ctor_get(v_view_1739_, 2);
lean_inc(v_name_1741_);
v_args_1742_ = lean_ctor_get(v_view_1739_, 3);
lean_inc_ref(v_args_1742_);
v_content_1743_ = lean_ctor_get(v_view_1739_, 4);
lean_inc_ref(v_content_1743_);
v_closer_1744_ = lean_ctor_get(v_view_1739_, 5);
lean_inc(v_closer_1744_);
lean_dec_ref(v_view_1739_);
v___x_1745_ = 0;
v___x_1746_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1740_, v___x_1745_, v_a_1530_);
v_snd_1747_ = lean_ctor_get(v___x_1746_, 1);
lean_inc(v_snd_1747_);
lean_dec_ref(v___x_1746_);
v___x_1748_ = 3;
v___x_1749_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1741_, v___x_1748_, v_snd_1747_);
v_snd_1750_ = lean_ctor_get(v___x_1749_, 1);
lean_inc(v_snd_1750_);
lean_dec_ref(v___x_1749_);
v___x_1751_ = lean_box(0);
v_sz_1752_ = lean_array_size(v_args_1742_);
v___x_1753_ = ((size_t)0ULL);
v___x_1754_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(v_args_1742_, v_sz_1752_, v___x_1753_, v___x_1751_, v_snd_1750_);
lean_dec_ref(v_args_1742_);
v_snd_1755_ = lean_ctor_get(v___x_1754_, 1);
lean_inc(v_snd_1755_);
lean_dec_ref(v___x_1754_);
v_sz_1756_ = lean_array_size(v_content_1743_);
v___x_1757_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1528_, v_content_1743_, v_sz_1756_, v___x_1753_, v___x_1751_, v_snd_1755_);
lean_dec_ref(v_content_1743_);
v_snd_1758_ = lean_ctor_get(v___x_1757_, 1);
lean_inc(v_snd_1758_);
lean_dec_ref(v___x_1757_);
v___x_1759_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1744_, v___x_1745_, v_snd_1758_);
return v___x_1759_;
}
case 7:
{
lean_object* v_view_1760_; lean_object* v_braceOpen_1761_; lean_object* v_name_1762_; lean_object* v_args_1763_; lean_object* v_braceClose_1764_; uint8_t v___x_1765_; lean_object* v___x_1766_; lean_object* v_snd_1767_; uint8_t v___x_1768_; lean_object* v___x_1769_; lean_object* v_snd_1770_; lean_object* v___x_1771_; size_t v_sz_1772_; size_t v___x_1773_; lean_object* v___x_1774_; lean_object* v_snd_1775_; lean_object* v___x_1776_; 
lean_dec_ref(v_getTokens_1528_);
v_view_1760_ = lean_ctor_get(v_val_1631_, 0);
lean_inc_ref(v_view_1760_);
lean_dec_ref_known(v_val_1631_, 1);
v_braceOpen_1761_ = lean_ctor_get(v_view_1760_, 1);
lean_inc(v_braceOpen_1761_);
v_name_1762_ = lean_ctor_get(v_view_1760_, 2);
lean_inc(v_name_1762_);
v_args_1763_ = lean_ctor_get(v_view_1760_, 3);
lean_inc_ref(v_args_1763_);
v_braceClose_1764_ = lean_ctor_get(v_view_1760_, 4);
lean_inc(v_braceClose_1764_);
lean_dec_ref(v_view_1760_);
v___x_1765_ = 0;
v___x_1766_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_braceOpen_1761_, v___x_1765_, v_a_1530_);
v_snd_1767_ = lean_ctor_get(v___x_1766_, 1);
lean_inc(v_snd_1767_);
lean_dec_ref(v___x_1766_);
v___x_1768_ = 3;
v___x_1769_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1762_, v___x_1768_, v_snd_1767_);
v_snd_1770_ = lean_ctor_get(v___x_1769_, 1);
lean_inc(v_snd_1770_);
lean_dec_ref(v___x_1769_);
v___x_1771_ = lean_box(0);
v_sz_1772_ = lean_array_size(v_args_1763_);
v___x_1773_ = ((size_t)0ULL);
v___x_1774_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(v_args_1763_, v_sz_1772_, v___x_1773_, v___x_1771_, v_snd_1770_);
lean_dec_ref(v_args_1763_);
v_snd_1775_ = lean_ctor_get(v___x_1774_, 1);
lean_inc(v_snd_1775_);
lean_dec_ref(v___x_1774_);
v___x_1776_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_braceClose_1764_, v___x_1765_, v_snd_1775_);
return v___x_1776_;
}
case 8:
{
lean_object* v_view_1777_; lean_object* v_marker_1778_; lean_object* v_content_1779_; uint8_t v___x_1780_; lean_object* v___x_1781_; lean_object* v_snd_1782_; lean_object* v___x_1783_; size_t v_sz_1784_; size_t v___x_1785_; lean_object* v___x_1786_; lean_object* v_snd_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
v_view_1777_ = lean_ctor_get(v_val_1631_, 0);
lean_inc_ref(v_view_1777_);
lean_dec_ref_known(v_val_1631_, 1);
v_marker_1778_ = lean_ctor_get(v_view_1777_, 1);
lean_inc(v_marker_1778_);
v_content_1779_ = lean_ctor_get(v_view_1777_, 3);
lean_inc_ref(v_content_1779_);
lean_dec_ref(v_view_1777_);
v___x_1780_ = 0;
v___x_1781_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_marker_1778_, v___x_1780_, v_a_1530_);
v_snd_1782_ = lean_ctor_get(v___x_1781_, 1);
lean_inc(v_snd_1782_);
lean_dec_ref(v___x_1781_);
v___x_1783_ = lean_box(0);
v_sz_1784_ = lean_array_size(v_content_1779_);
v___x_1785_ = ((size_t)0ULL);
v___x_1786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1528_, v_content_1779_, v_sz_1784_, v___x_1785_, v___x_1783_, v_snd_1782_);
lean_dec_ref(v_content_1779_);
v_snd_1787_ = lean_ctor_get(v___x_1786_, 1);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1794_ == 0)
{
lean_object* v_unused_1795_; 
v_unused_1795_ = lean_ctor_get(v___x_1786_, 0);
lean_dec(v_unused_1795_);
v___x_1789_ = v___x_1786_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_snd_1787_);
lean_dec(v___x_1786_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1783_);
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1783_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v_snd_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
case 9:
{
lean_object* v_view_1796_; lean_object* v_opener_1797_; lean_object* v_name_1798_; lean_object* v_closer_1799_; lean_object* v_url_1800_; uint8_t v___x_1801_; lean_object* v___x_1802_; lean_object* v_snd_1803_; uint8_t v___x_1804_; lean_object* v___x_1805_; lean_object* v_snd_1806_; lean_object* v___x_1807_; lean_object* v_snd_1808_; uint8_t v___x_1809_; lean_object* v___x_1810_; 
lean_dec_ref(v_getTokens_1528_);
v_view_1796_ = lean_ctor_get(v_val_1631_, 0);
lean_inc_ref(v_view_1796_);
lean_dec_ref_known(v_val_1631_, 1);
v_opener_1797_ = lean_ctor_get(v_view_1796_, 1);
lean_inc(v_opener_1797_);
v_name_1798_ = lean_ctor_get(v_view_1796_, 2);
lean_inc(v_name_1798_);
v_closer_1799_ = lean_ctor_get(v_view_1796_, 3);
lean_inc(v_closer_1799_);
v_url_1800_ = lean_ctor_get(v_view_1796_, 4);
lean_inc(v_url_1800_);
lean_dec_ref(v_view_1796_);
v___x_1801_ = 0;
v___x_1802_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1797_, v___x_1801_, v_a_1530_);
v_snd_1803_ = lean_ctor_get(v___x_1802_, 1);
lean_inc(v_snd_1803_);
lean_dec_ref(v___x_1802_);
v___x_1804_ = 2;
v___x_1805_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1798_, v___x_1804_, v_snd_1803_);
v_snd_1806_ = lean_ctor_get(v___x_1805_, 1);
lean_inc(v_snd_1806_);
lean_dec_ref(v___x_1805_);
v___x_1807_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1799_, v___x_1801_, v_snd_1806_);
v_snd_1808_ = lean_ctor_get(v___x_1807_, 1);
lean_inc(v_snd_1808_);
lean_dec_ref(v___x_1807_);
v___x_1809_ = 18;
v___x_1810_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_url_1800_, v___x_1809_, v_snd_1808_);
return v___x_1810_;
}
case 10:
{
lean_object* v_view_1811_; lean_object* v_opener_1812_; lean_object* v_name_1813_; lean_object* v_closer_1814_; lean_object* v_content_1815_; uint8_t v___x_1816_; lean_object* v___x_1817_; lean_object* v_snd_1818_; uint8_t v___x_1819_; lean_object* v___x_1820_; lean_object* v_snd_1821_; lean_object* v___x_1822_; lean_object* v_snd_1823_; lean_object* v___x_1824_; size_t v_sz_1825_; size_t v___x_1826_; lean_object* v___x_1827_; lean_object* v_snd_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1835_; 
v_view_1811_ = lean_ctor_get(v_val_1631_, 0);
lean_inc_ref(v_view_1811_);
lean_dec_ref_known(v_val_1631_, 1);
v_opener_1812_ = lean_ctor_get(v_view_1811_, 1);
lean_inc(v_opener_1812_);
v_name_1813_ = lean_ctor_get(v_view_1811_, 2);
lean_inc(v_name_1813_);
v_closer_1814_ = lean_ctor_get(v_view_1811_, 3);
lean_inc(v_closer_1814_);
v_content_1815_ = lean_ctor_get(v_view_1811_, 4);
lean_inc_ref(v_content_1815_);
lean_dec_ref(v_view_1811_);
v___x_1816_ = 0;
v___x_1817_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1812_, v___x_1816_, v_a_1530_);
v_snd_1818_ = lean_ctor_get(v___x_1817_, 1);
lean_inc(v_snd_1818_);
lean_dec_ref(v___x_1817_);
v___x_1819_ = 2;
v___x_1820_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1813_, v___x_1819_, v_snd_1818_);
v_snd_1821_ = lean_ctor_get(v___x_1820_, 1);
lean_inc(v_snd_1821_);
lean_dec_ref(v___x_1820_);
v___x_1822_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1814_, v___x_1816_, v_snd_1821_);
v_snd_1823_ = lean_ctor_get(v___x_1822_, 1);
lean_inc(v_snd_1823_);
lean_dec_ref(v___x_1822_);
v___x_1824_ = lean_box(0);
v_sz_1825_ = lean_array_size(v_content_1815_);
v___x_1826_ = ((size_t)0ULL);
v___x_1827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1528_, v_content_1815_, v_sz_1825_, v___x_1826_, v___x_1824_, v_snd_1823_);
lean_dec_ref(v_content_1815_);
v_snd_1828_ = lean_ctor_get(v___x_1827_, 1);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1835_ == 0)
{
lean_object* v_unused_1836_; 
v_unused_1836_ = lean_ctor_get(v___x_1827_, 0);
lean_dec(v_unused_1836_);
v___x_1830_ = v___x_1827_;
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_snd_1828_);
lean_dec(v___x_1827_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 0, v___x_1824_);
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1824_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v_snd_1828_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
default: 
{
lean_object* v_view_1837_; lean_object* v_opener_1838_; lean_object* v_contents_1839_; lean_object* v_closer_1840_; uint8_t v___x_1841_; lean_object* v___x_1842_; lean_object* v_snd_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v_view_1837_ = lean_ctor_get(v_val_1631_, 0);
lean_inc_ref(v_view_1837_);
lean_dec_ref_known(v_val_1631_, 1);
v_opener_1838_ = lean_ctor_get(v_view_1837_, 1);
lean_inc(v_opener_1838_);
v_contents_1839_ = lean_ctor_get(v_view_1837_, 2);
lean_inc(v_contents_1839_);
v_closer_1840_ = lean_ctor_get(v_view_1837_, 3);
lean_inc(v_closer_1840_);
lean_dec_ref(v_view_1837_);
v___x_1841_ = 0;
v___x_1842_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1838_, v___x_1841_, v_a_1530_);
v_snd_1843_ = lean_ctor_get(v___x_1842_, 1);
lean_inc(v_snd_1843_);
lean_dec_ref(v___x_1842_);
v___x_1844_ = lean_apply_1(v_getTokens_1528_, v_contents_1839_);
v___x_1845_ = l_Array_append___redArg(v_snd_1843_, v___x_1844_);
lean_dec_ref(v___x_1844_);
v___x_1846_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1840_, v___x_1841_, v___x_1845_);
return v___x_1846_;
}
}
}
else
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; uint8_t v___x_1851_; 
lean_dec(v___x_1630_);
v___x_1847_ = l_Lean_Syntax_getArgs(v_stx_1529_);
lean_dec(v_stx_1529_);
v___x_1848_ = lean_unsigned_to_nat(0u);
v___x_1849_ = lean_array_get_size(v___x_1847_);
v___x_1850_ = lean_box(0);
v___x_1851_ = lean_nat_dec_lt(v___x_1848_, v___x_1849_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; 
lean_dec_ref(v___x_1847_);
lean_dec_ref(v_getTokens_1528_);
v___x_1852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1850_);
lean_ctor_set(v___x_1852_, 1, v_a_1530_);
return v___x_1852_;
}
else
{
uint8_t v___x_1853_; 
v___x_1853_ = lean_nat_dec_le(v___x_1849_, v___x_1849_);
if (v___x_1853_ == 0)
{
if (v___x_1851_ == 0)
{
lean_object* v___x_1854_; 
lean_dec_ref(v___x_1847_);
lean_dec_ref(v_getTokens_1528_);
v___x_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1850_);
lean_ctor_set(v___x_1854_, 1, v_a_1530_);
return v___x_1854_;
}
else
{
size_t v___x_1855_; size_t v___x_1856_; lean_object* v___x_1857_; 
v___x_1855_ = ((size_t)0ULL);
v___x_1856_ = lean_usize_of_nat(v___x_1849_);
v___x_1857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6(v_getTokens_1528_, v___x_1847_, v___x_1855_, v___x_1856_, v___x_1850_, v_a_1530_);
lean_dec_ref(v___x_1847_);
return v___x_1857_;
}
}
else
{
size_t v___x_1858_; size_t v___x_1859_; lean_object* v___x_1860_; 
v___x_1858_ = ((size_t)0ULL);
v___x_1859_ = lean_usize_of_nat(v___x_1849_);
v___x_1860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6(v_getTokens_1528_, v___x_1847_, v___x_1858_, v___x_1859_, v___x_1850_, v_a_1530_);
lean_dec_ref(v___x_1847_);
return v___x_1860_;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(lean_object* v_getTokens_1861_, lean_object* v_as_1862_, size_t v_sz_1863_, size_t v_i_1864_, lean_object* v_b_1865_, lean_object* v___y_1866_){
_start:
{
uint8_t v___x_1867_; 
v___x_1867_ = lean_usize_dec_lt(v_i_1864_, v_sz_1863_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; 
lean_dec_ref(v_getTokens_1861_);
v___x_1868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1868_, 0, v_b_1865_);
lean_ctor_set(v___x_1868_, 1, v___y_1866_);
return v___x_1868_;
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1870_; lean_object* v_snd_1871_; lean_object* v___x_1872_; size_t v___x_1873_; size_t v___x_1874_; 
v_a_1869_ = lean_array_uget_borrowed(v_as_1862_, v_i_1864_);
lean_inc(v_a_1869_);
lean_inc_ref(v_getTokens_1861_);
v___x_1870_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_getTokens_1861_, v_a_1869_, v___y_1866_);
v_snd_1871_ = lean_ctor_get(v___x_1870_, 1);
lean_inc(v_snd_1871_);
lean_dec_ref(v___x_1870_);
v___x_1872_ = lean_box(0);
v___x_1873_ = ((size_t)1ULL);
v___x_1874_ = lean_usize_add(v_i_1864_, v___x_1873_);
v_i_1864_ = v___x_1874_;
v_b_1865_ = v___x_1872_;
v___y_1866_ = v_snd_1871_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_getTokens_1861_ = stack[0].m_obj;
lean_object* v_as_1862_ = stack[1].m_obj;
size_t v_sz_1863_ = stack[2].m_num;
size_t v_i_1864_ = stack[3].m_num;
lean_object* v_b_1865_ = stack[4].m_obj;
lean_object* v___y_1866_ = stack[5].m_obj;
lean_object* v_res_1876_;
v_res_1876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1861_, v_as_1862_, v_sz_1863_, v_i_1864_, v_b_1865_, v___y_1866_);
stack->m_obj
 = v_res_1876_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDelimited(lean_object* v_getTokens_1877_, lean_object* v_opener_1878_, lean_object* v_closer_1879_, lean_object* v_content_1880_, lean_object* v_a_1881_){
_start:
{
uint8_t v___x_1882_; lean_object* v___x_1883_; lean_object* v_snd_1884_; lean_object* v___x_1885_; size_t v_sz_1886_; size_t v___x_1887_; lean_object* v___x_1888_; lean_object* v_snd_1889_; lean_object* v___x_1890_; 
v___x_1882_ = 0;
v___x_1883_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1878_, v___x_1882_, v_a_1881_);
v_snd_1884_ = lean_ctor_get(v___x_1883_, 1);
lean_inc(v_snd_1884_);
lean_dec_ref(v___x_1883_);
v___x_1885_ = lean_box(0);
v_sz_1886_ = lean_array_size(v_content_1880_);
v___x_1887_ = ((size_t)0ULL);
v___x_1888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1877_, v_content_1880_, v_sz_1886_, v___x_1887_, v___x_1885_, v_snd_1884_);
v_snd_1889_ = lean_ctor_get(v___x_1888_, 1);
lean_inc(v_snd_1889_);
lean_dec_ref(v___x_1888_);
v___x_1890_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1879_, v___x_1882_, v_snd_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDelimited___boxed(lean_object* v_getTokens_1891_, lean_object* v_opener_1892_, lean_object* v_closer_1893_, lean_object* v_content_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDelimited(v_getTokens_1891_, v_opener_1892_, v_closer_1893_, v_content_1894_, v_a_1895_);
lean_dec_ref(v_content_1894_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem___boxed(lean_object* v_getTokens_1897_, lean_object* v_marker_1898_, lean_object* v_contents_1899_, lean_object* v_a_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem(v_getTokens_1897_, v_marker_1898_, v_contents_1899_, v_a_1900_);
lean_dec_ref(v_contents_1899_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6___boxed(lean_object* v_getTokens_1902_, lean_object* v_as_1903_, lean_object* v_i_1904_, lean_object* v_stop_1905_, lean_object* v_b_1906_, lean_object* v___y_1907_){
_start:
{
size_t v_i_boxed_1908_; size_t v_stop_boxed_1909_; lean_object* v_res_1910_; 
v_i_boxed_1908_ = lean_unbox_usize(v_i_1904_);
lean_dec(v_i_1904_);
v_stop_boxed_1909_ = lean_unbox_usize(v_stop_1905_);
lean_dec(v_stop_1905_);
v_res_1910_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6(v_getTokens_1902_, v_as_1903_, v_i_boxed_1908_, v_stop_boxed_1909_, v_b_1906_, v___y_1907_);
lean_dec_ref(v_as_1903_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__5___boxed(lean_object* v_getTokens_1911_, lean_object* v_as_1912_, lean_object* v_sz_1913_, lean_object* v_i_1914_, lean_object* v_b_1915_, lean_object* v___y_1916_){
_start:
{
size_t v_sz_boxed_1917_; size_t v_i_boxed_1918_; lean_object* v_res_1919_; 
v_sz_boxed_1917_ = lean_unbox_usize(v_sz_1913_);
lean_dec(v_sz_1913_);
v_i_boxed_1918_ = lean_unbox_usize(v_i_1914_);
lean_dec(v_i_1914_);
v_res_1919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__5(v_getTokens_1911_, v_as_1912_, v_sz_boxed_1917_, v_i_boxed_1918_, v_b_1915_, v___y_1916_);
lean_dec_ref(v_as_1912_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0___boxed(lean_object* v_getTokens_1920_, lean_object* v_as_1921_, lean_object* v_sz_1922_, lean_object* v_i_1923_, lean_object* v_b_1924_, lean_object* v___y_1925_){
_start:
{
size_t v_sz_boxed_1926_; size_t v_i_boxed_1927_; lean_object* v_res_1928_; 
v_sz_boxed_1926_ = lean_unbox_usize(v_sz_1922_);
lean_dec(v_sz_1922_);
v_i_boxed_1927_ = lean_unbox_usize(v_i_1923_);
lean_dec(v_i_1923_);
v_res_1928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1920_, v_as_1921_, v_sz_boxed_1926_, v_i_boxed_1927_, v_b_1924_, v___y_1925_);
lean_dec_ref(v_as_1921_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3___boxed(lean_object* v_getTokens_1929_, lean_object* v_as_1930_, lean_object* v_sz_1931_, lean_object* v_i_1932_, lean_object* v_b_1933_, lean_object* v___y_1934_){
_start:
{
size_t v_sz_boxed_1935_; size_t v_i_boxed_1936_; lean_object* v_res_1937_; 
v_sz_boxed_1935_ = lean_unbox_usize(v_sz_1931_);
lean_dec(v_sz_1931_);
v_i_boxed_1936_ = lean_unbox_usize(v_i_1932_);
lean_dec(v_i_1932_);
v_res_1937_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3(v_getTokens_1929_, v_as_1930_, v_sz_boxed_1935_, v_i_boxed_1936_, v_b_1933_, v___y_1934_);
lean_dec_ref(v_as_1930_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__4___boxed(lean_object* v_getTokens_1938_, lean_object* v_as_1939_, lean_object* v_sz_1940_, lean_object* v_i_1941_, lean_object* v_b_1942_, lean_object* v___y_1943_){
_start:
{
size_t v_sz_boxed_1944_; size_t v_i_boxed_1945_; lean_object* v_res_1946_; 
v_sz_boxed_1944_ = lean_unbox_usize(v_sz_1940_);
lean_dec(v_sz_1940_);
v_i_boxed_1945_ = lean_unbox_usize(v_i_1941_);
lean_dec(v_i_1941_);
v_res_1946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__4(v_getTokens_1938_, v_as_1939_, v_sz_boxed_1944_, v_i_boxed_1945_, v_b_1942_, v___y_1943_);
lean_dec_ref(v_as_1939_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(lean_object* v_stx_1949_, lean_object* v_getTokens_1950_){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v_snd_1953_; 
v___x_1951_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
v___x_1952_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_getTokens_1950_, v_stx_1949_, v___x_1951_);
v_snd_1953_ = lean_ctor_get(v___x_1952_, 1);
lean_inc(v_snd_1953_);
lean_dec_ref(v___x_1952_);
return v_snd_1953_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(lean_object* v_s_1954_){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; uint8_t v_decide_1957_; 
v___x_1955_ = lean_unsigned_to_nat(0u);
v___x_1956_ = lean_string_utf8_byte_size(v_s_1954_);
v_decide_1957_ = lean_nat_dec_eq(v___x_1955_, v___x_1956_);
if (v_decide_1957_ == 0)
{
uint32_t v___x_1958_; uint32_t v___x_1959_; uint8_t v___x_1960_; 
v___x_1958_ = 35;
v___x_1959_ = lean_string_utf8_get_fast(v_s_1954_, v___x_1955_);
v___x_1960_ = lean_uint32_dec_eq(v___x_1959_, v___x_1958_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; 
lean_dec_ref(v_s_1954_);
v___x_1961_ = lean_box(0);
return v___x_1961_;
}
else
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1962_ = lean_string_utf8_next_fast(v_s_1954_, v___x_1955_);
v___x_1963_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1963_, 0, v_s_1954_);
lean_ctor_set(v___x_1963_, 1, v___x_1962_);
lean_ctor_set(v___x_1963_, 2, v___x_1956_);
v___x_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
return v___x_1964_;
}
}
else
{
lean_object* v___x_1965_; 
lean_dec_ref(v_s_1954_);
v___x_1965_ = lean_box(0);
return v___x_1965_;
}
}
}
lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(lean_object* v_s_1966_, uint32_t v_pat_1967_){
_start:
{
lean_object* v___x_1968_; 
v___x_1968_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v_s_1966_);
return v___x_1968_;
}
}
LEAN_EXPORT void l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1966_ = stack[0].m_obj;
uint32_t v_pat_1967_ = stack[1].m_num;
lean_object* v_res_1969_;
v_res_1969_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_s_1966_, v_pat_1967_);
stack->m_obj
 = v_res_1969_;
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___boxed(lean_object* v_s_1970_, lean_object* v_pat_1971_){
_start:
{
uint32_t v_pat_boxed_1972_; lean_object* v_res_1973_; 
v_pat_boxed_1972_ = lean_unbox_uint32(v_pat_1971_);
lean_dec(v_pat_1971_);
v_res_1973_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_s_1970_, v_pat_boxed_1972_);
return v_res_1973_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(lean_object* v_a_1974_, lean_object* v_as_1975_, size_t v_i_1976_, size_t v_stop_1977_){
_start:
{
uint8_t v___x_1978_; 
v___x_1978_ = lean_usize_dec_eq(v_i_1976_, v_stop_1977_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; uint8_t v___x_1980_; 
v___x_1979_ = lean_array_uget_borrowed(v_as_1975_, v_i_1976_);
v___x_1980_ = lean_name_eq(v_a_1974_, v___x_1979_);
if (v___x_1980_ == 0)
{
size_t v___x_1981_; size_t v___x_1982_; 
v___x_1981_ = ((size_t)1ULL);
v___x_1982_ = lean_usize_add(v_i_1976_, v___x_1981_);
v_i_1976_ = v___x_1982_;
goto _start;
}
else
{
return v___x_1980_;
}
}
else
{
uint8_t v___x_1984_; 
v___x_1984_ = 0;
return v___x_1984_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1974_ = stack[0].m_obj;
lean_object* v_as_1975_ = stack[1].m_obj;
size_t v_i_1976_ = stack[2].m_num;
size_t v_stop_1977_ = stack[3].m_num;
uint8_t v_res_1985_;
v_res_1985_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(v_a_1974_, v_as_1975_, v_i_1976_, v_stop_1977_);
stack->m_num = v_res_1985_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0___boxed(lean_object* v_a_1986_, lean_object* v_as_1987_, lean_object* v_i_1988_, lean_object* v_stop_1989_){
_start:
{
size_t v_i_boxed_1990_; size_t v_stop_boxed_1991_; uint8_t v_res_1992_; lean_object* v_r_1993_; 
v_i_boxed_1990_ = lean_unbox_usize(v_i_1988_);
lean_dec(v_i_1988_);
v_stop_boxed_1991_ = lean_unbox_usize(v_stop_1989_);
lean_dec(v_stop_1989_);
v_res_1992_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(v_a_1986_, v_as_1987_, v_i_boxed_1990_, v_stop_boxed_1991_);
lean_dec_ref(v_as_1987_);
lean_dec(v_a_1986_);
v_r_1993_ = lean_box(v_res_1992_);
return v_r_1993_;
}
}
uint8_t l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(lean_object* v_as_1994_, lean_object* v_a_1995_){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; 
v___x_1996_ = lean_unsigned_to_nat(0u);
v___x_1997_ = lean_array_get_size(v_as_1994_);
v___x_1998_ = lean_nat_dec_lt(v___x_1996_, v___x_1997_);
if (v___x_1998_ == 0)
{
return v___x_1998_;
}
else
{
if (v___x_1998_ == 0)
{
return v___x_1998_;
}
else
{
size_t v___x_1999_; size_t v___x_2000_; uint8_t v___x_2001_; 
v___x_1999_ = ((size_t)0ULL);
v___x_2000_ = lean_usize_of_nat(v___x_1997_);
v___x_2001_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(v_a_1995_, v_as_1994_, v___x_1999_, v___x_2000_);
return v___x_2001_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1994_ = stack[0].m_obj;
lean_object* v_a_1995_ = stack[1].m_obj;
uint8_t v_res_2002_;
v_res_2002_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v_as_1994_, v_a_1995_);
stack->m_num = v_res_2002_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0___boxed(lean_object* v_as_2003_, lean_object* v_a_2004_){
_start:
{
uint8_t v_res_2005_; lean_object* v_r_2006_; 
v_res_2005_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v_as_2003_, v_a_2004_);
lean_dec(v_a_2004_);
lean_dec_ref(v_as_2003_);
v_r_2006_ = lean_box(v_res_2005_);
return v_r_2006_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(lean_object* v_as_2007_, size_t v_i_2008_, size_t v_stop_2009_, lean_object* v_b_2010_){
_start:
{
uint8_t v___x_2011_; 
v___x_2011_ = lean_usize_dec_eq(v_i_2008_, v_stop_2009_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; lean_object* v___x_2013_; size_t v___x_2014_; size_t v___x_2015_; 
v___x_2012_ = lean_array_uget_borrowed(v_as_2007_, v_i_2008_);
v___x_2013_ = l_Array_append___redArg(v_b_2010_, v___x_2012_);
v___x_2014_ = ((size_t)1ULL);
v___x_2015_ = lean_usize_add(v_i_2008_, v___x_2014_);
v_i_2008_ = v___x_2015_;
v_b_2010_ = v___x_2013_;
goto _start;
}
else
{
return v_b_2010_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2007_ = stack[0].m_obj;
size_t v_i_2008_ = stack[1].m_num;
size_t v_stop_2009_ = stack[2].m_num;
lean_object* v_b_2010_ = stack[3].m_obj;
lean_object* v_res_2017_;
v_res_2017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v_as_2007_, v_i_2008_, v_stop_2009_, v_b_2010_);
stack->m_obj
 = v_res_2017_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4___boxed(lean_object* v_as_2018_, lean_object* v_i_2019_, lean_object* v_stop_2020_, lean_object* v_b_2021_){
_start:
{
size_t v_i_boxed_2022_; size_t v_stop_boxed_2023_; lean_object* v_res_2024_; 
v_i_boxed_2022_ = lean_unbox_usize(v_i_2019_);
lean_dec(v_i_2019_);
v_stop_boxed_2023_ = lean_unbox_usize(v_stop_2020_);
lean_dec(v_stop_2020_);
v_res_2024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v_as_2018_, v_i_boxed_2022_, v_stop_boxed_2023_, v_b_2021_);
lean_dec_ref(v_as_2018_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(lean_object* v_t_2025_, lean_object* v_k_2026_, lean_object* v_fallback_2027_){
_start:
{
if (lean_obj_tag(v_t_2025_) == 0)
{
lean_object* v_k_2028_; lean_object* v_v_2029_; lean_object* v_l_2030_; lean_object* v_r_2031_; uint8_t v___x_2032_; 
v_k_2028_ = lean_ctor_get(v_t_2025_, 1);
v_v_2029_ = lean_ctor_get(v_t_2025_, 2);
v_l_2030_ = lean_ctor_get(v_t_2025_, 3);
v_r_2031_ = lean_ctor_get(v_t_2025_, 4);
v___x_2032_ = lean_string_compare(v_k_2026_, v_k_2028_);
switch(v___x_2032_)
{
case 0:
{
v_t_2025_ = v_l_2030_;
goto _start;
}
case 1:
{
lean_inc(v_v_2029_);
return v_v_2029_;
}
default: 
{
v_t_2025_ = v_r_2031_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2027_);
return v_fallback_2027_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg___boxed(lean_object* v_t_2035_, lean_object* v_k_2036_, lean_object* v_fallback_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v_t_2035_, v_k_2036_, v_fallback_2037_);
lean_dec(v_fallback_2037_);
lean_dec_ref(v_k_2036_);
lean_dec(v_t_2035_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(lean_object* v_text_2065_, lean_object* v_x_2066_){
_start:
{
lean_object* v___y_2068_; lean_object* v___y_2069_; uint8_t v___y_2070_; lean_object* v___y_2080_; lean_object* v___y_2081_; uint8_t v___y_2082_; lean_object* v___y_2092_; lean_object* v___y_2093_; uint8_t v___y_2094_; lean_object* v___y_2104_; lean_object* v___y_2105_; uint8_t v___y_2106_; uint8_t v___y_2116_; uint8_t v___y_2117_; lean_object* v___y_2118_; uint8_t v___y_2119_; lean_object* v___y_2120_; uint8_t v___y_2121_; uint8_t v___y_2123_; lean_object* v___y_2124_; uint8_t v___y_2125_; lean_object* v___y_2126_; uint8_t v___y_2127_; uint8_t v___y_2128_; uint8_t v___y_2130_; lean_object* v___y_2131_; uint8_t v___y_2132_; lean_object* v___y_2133_; uint32_t v___y_2134_; uint8_t v___y_2135_; uint8_t v___y_2140_; lean_object* v___y_2141_; uint8_t v___y_2142_; lean_object* v___y_2143_; uint32_t v___y_2144_; uint8_t v___y_2145_; lean_object* v___y_2151_; lean_object* v___y_2152_; uint8_t v___y_2153_; lean_object* v___x_2162_; uint8_t v___x_2163_; 
v___x_2162_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1));
lean_inc(v_x_2066_);
v___x_2163_ = l_Lean_Syntax_isOfKind(v_x_2066_, v___x_2162_);
if (v___x_2163_ == 0)
{
lean_object* v___x_2164_; uint8_t v___x_2165_; uint8_t v___y_2167_; uint8_t v___y_2168_; lean_object* v___y_2169_; lean_object* v___y_2170_; uint8_t v___y_2171_; uint8_t v___y_2173_; uint8_t v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2176_; uint8_t v___y_2177_; uint8_t v___y_2179_; uint8_t v___y_2180_; uint32_t v___y_2181_; lean_object* v___y_2182_; lean_object* v___y_2183_; uint8_t v___y_2188_; uint8_t v___y_2189_; uint32_t v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; 
v___x_2164_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3));
lean_inc(v_x_2066_);
v___x_2165_ = l_Lean_Syntax_isOfKind(v_x_2066_, v___x_2164_);
if (v___x_2165_ == 0)
{
lean_object* v___x_2197_; lean_object* v___x_2198_; uint8_t v___x_2199_; 
v___x_2197_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2066_);
v___x_2198_ = l_Lean_Syntax_getKind(v_x_2066_);
v___x_2199_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2197_, v___x_2198_);
if (v___x_2199_ == 0)
{
lean_object* v___x_2200_; uint8_t v___x_2201_; lean_object* v___y_2203_; lean_object* v___y_2204_; uint8_t v___y_2205_; uint8_t v___y_2207_; lean_object* v___y_2208_; lean_object* v___y_2209_; uint8_t v___y_2210_; lean_object* v___y_2212_; uint8_t v___y_2213_; lean_object* v___y_2214_; uint32_t v___y_2215_; uint8_t v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; uint32_t v___y_2223_; lean_object* v___y_2229_; lean_object* v___y_2230_; uint8_t v___y_2231_; uint32_t v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; uint32_t v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2261_; 
v___x_2200_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2201_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2200_, v___x_2198_);
lean_dec(v___x_2198_);
if (v___x_2201_ == 0)
{
lean_object* v___x_2276_; uint8_t v___x_2277_; 
v___x_2276_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2066_);
v___x_2277_ = l_Lean_Syntax_isOfKind(v_x_2066_, v___x_2276_);
if (v___x_2277_ == 0)
{
lean_object* v___x_2278_; size_t v_sz_2279_; size_t v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; uint8_t v___x_2285_; 
v___x_2278_ = l_Lean_Syntax_getArgs(v_x_2066_);
v_sz_2279_ = lean_array_size(v___x_2278_);
v___x_2280_ = ((size_t)0ULL);
v___x_2281_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2065_, v_sz_2279_, v___x_2280_, v___x_2278_);
v___x_2282_ = lean_unsigned_to_nat(0u);
v___x_2283_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2284_ = lean_array_get_size(v___x_2281_);
v___x_2285_ = lean_nat_dec_lt(v___x_2282_, v___x_2284_);
if (v___x_2285_ == 0)
{
lean_dec_ref(v___x_2281_);
v___y_2261_ = v___x_2283_;
goto v___jp_2260_;
}
else
{
size_t v___x_2286_; lean_object* v___x_2287_; 
v___x_2286_ = lean_usize_of_nat(v___x_2284_);
v___x_2287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2281_, v___x_2280_, v___x_2286_, v___x_2283_);
lean_dec_ref(v___x_2281_);
v___y_2261_ = v___x_2287_;
goto v___jp_2260_;
}
}
else
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2288_ = lean_unsigned_to_nat(0u);
v___x_2289_ = l_Lean_Syntax_getArg(v_x_2066_, v___x_2288_);
v___x_2290_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2065_, v___x_2289_);
v___y_2261_ = v___x_2290_;
goto v___jp_2260_;
}
}
else
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; uint8_t v___x_2294_; 
v___x_2291_ = lean_unsigned_to_nat(1u);
v___x_2292_ = l_Lean_Syntax_getArg(v_x_2066_, v___x_2291_);
lean_dec(v_x_2066_);
v___x_2293_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v___x_2292_);
v___x_2294_ = l_Lean_Syntax_isOfKind(v___x_2292_, v___x_2293_);
if (v___x_2294_ == 0)
{
lean_object* v___x_2295_; 
lean_dec(v___x_2292_);
lean_dec_ref(v_text_2065_);
v___x_2295_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2295_;
}
else
{
lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2296_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2296_, 0, v_text_2065_);
v___x_2297_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v___x_2292_, v___x_2296_);
return v___x_2297_;
}
}
v___jp_2202_:
{
if (v___y_2205_ == 0)
{
lean_dec_ref(v___y_2203_);
lean_dec(v_x_2066_);
return v___y_2204_;
}
else
{
v___y_2080_ = v___y_2203_;
v___y_2081_ = v___y_2204_;
v___y_2082_ = v___x_2201_;
goto v___jp_2079_;
}
}
v___jp_2206_:
{
if (v___y_2207_ == 0)
{
v___y_2203_ = v___y_2208_;
v___y_2204_ = v___y_2209_;
v___y_2205_ = v___y_2210_;
goto v___jp_2202_;
}
else
{
if (v___x_2201_ == 0)
{
v___y_2080_ = v___y_2208_;
v___y_2081_ = v___y_2209_;
v___y_2082_ = v___x_2201_;
goto v___jp_2079_;
}
else
{
v___y_2203_ = v___y_2208_;
v___y_2204_ = v___y_2209_;
v___y_2205_ = v___y_2210_;
goto v___jp_2202_;
}
}
}
v___jp_2211_:
{
uint32_t v___x_2216_; uint8_t v___x_2217_; 
v___x_2216_ = 95;
v___x_2217_ = lean_uint32_dec_eq(v___y_2215_, v___x_2216_);
if (v___x_2217_ == 0)
{
uint8_t v___x_2218_; 
v___x_2218_ = l_Lean_isLetterLike(v___y_2215_);
v___y_2207_ = v___y_2213_;
v___y_2208_ = v___y_2212_;
v___y_2209_ = v___y_2214_;
v___y_2210_ = v___x_2218_;
goto v___jp_2206_;
}
else
{
v___y_2207_ = v___y_2213_;
v___y_2208_ = v___y_2212_;
v___y_2209_ = v___y_2214_;
v___y_2210_ = v___x_2217_;
goto v___jp_2206_;
}
}
v___jp_2219_:
{
uint32_t v___x_2224_; uint8_t v___x_2225_; 
v___x_2224_ = 97;
v___x_2225_ = lean_uint32_dec_le(v___x_2224_, v___y_2223_);
if (v___x_2225_ == 0)
{
v___y_2212_ = v___y_2221_;
v___y_2213_ = v___y_2220_;
v___y_2214_ = v___y_2222_;
v___y_2215_ = v___y_2223_;
goto v___jp_2211_;
}
else
{
uint32_t v___x_2226_; uint8_t v___x_2227_; 
v___x_2226_ = 122;
v___x_2227_ = lean_uint32_dec_le(v___y_2223_, v___x_2226_);
if (v___x_2227_ == 0)
{
v___y_2212_ = v___y_2221_;
v___y_2213_ = v___y_2220_;
v___y_2214_ = v___y_2222_;
v___y_2215_ = v___y_2223_;
goto v___jp_2211_;
}
else
{
v___y_2207_ = v___y_2220_;
v___y_2208_ = v___y_2221_;
v___y_2209_ = v___y_2222_;
v___y_2210_ = v___x_2227_;
goto v___jp_2206_;
}
}
}
v___jp_2228_:
{
lean_object* v___x_2232_; 
lean_inc_ref(v___y_2229_);
v___x_2232_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2229_);
if (lean_obj_tag(v___x_2232_) == 0)
{
v___y_2207_ = v___y_2231_;
v___y_2208_ = v___y_2229_;
v___y_2209_ = v___y_2230_;
v___y_2210_ = v___x_2201_;
goto v___jp_2206_;
}
else
{
lean_object* v_val_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v_val_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_val_2233_);
lean_dec_ref_known(v___x_2232_, 1);
v___x_2234_ = lean_unsigned_to_nat(0u);
v___x_2235_ = l_String_Slice_Pos_get_x3f(v_val_2233_, v___x_2234_);
lean_dec(v_val_2233_);
if (lean_obj_tag(v___x_2235_) == 0)
{
v___y_2207_ = v___y_2231_;
v___y_2208_ = v___y_2229_;
v___y_2209_ = v___y_2230_;
v___y_2210_ = v___x_2201_;
goto v___jp_2206_;
}
else
{
lean_object* v_val_2236_; uint32_t v___x_2237_; uint32_t v___x_2238_; uint8_t v___x_2239_; 
v_val_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_val_2236_);
lean_dec_ref_known(v___x_2235_, 1);
v___x_2237_ = 65;
v___x_2238_ = lean_unbox_uint32(v_val_2236_);
v___x_2239_ = lean_uint32_dec_le(v___x_2237_, v___x_2238_);
if (v___x_2239_ == 0)
{
uint32_t v___x_2240_; 
v___x_2240_ = lean_unbox_uint32(v_val_2236_);
lean_dec(v_val_2236_);
v___y_2220_ = v___y_2231_;
v___y_2221_ = v___y_2229_;
v___y_2222_ = v___y_2230_;
v___y_2223_ = v___x_2240_;
goto v___jp_2219_;
}
else
{
uint32_t v___x_2241_; uint32_t v___x_2242_; uint8_t v___x_2243_; 
v___x_2241_ = 90;
v___x_2242_ = lean_unbox_uint32(v_val_2236_);
v___x_2243_ = lean_uint32_dec_le(v___x_2242_, v___x_2241_);
if (v___x_2243_ == 0)
{
uint32_t v___x_2244_; 
v___x_2244_ = lean_unbox_uint32(v_val_2236_);
lean_dec(v_val_2236_);
v___y_2220_ = v___y_2231_;
v___y_2221_ = v___y_2229_;
v___y_2222_ = v___y_2230_;
v___y_2223_ = v___x_2244_;
goto v___jp_2219_;
}
else
{
lean_dec(v_val_2236_);
v___y_2207_ = v___y_2231_;
v___y_2208_ = v___y_2229_;
v___y_2209_ = v___y_2230_;
v___y_2210_ = v___x_2243_;
goto v___jp_2206_;
}
}
}
}
}
v___jp_2245_:
{
uint32_t v___x_2249_; uint8_t v___x_2250_; 
v___x_2249_ = 95;
v___x_2250_ = lean_uint32_dec_eq(v___y_2246_, v___x_2249_);
if (v___x_2250_ == 0)
{
uint8_t v___x_2251_; 
v___x_2251_ = l_Lean_isLetterLike(v___y_2246_);
v___y_2229_ = v___y_2247_;
v___y_2230_ = v___y_2248_;
v___y_2231_ = v___x_2251_;
goto v___jp_2228_;
}
else
{
v___y_2229_ = v___y_2247_;
v___y_2230_ = v___y_2248_;
v___y_2231_ = v___x_2250_;
goto v___jp_2228_;
}
}
v___jp_2252_:
{
uint32_t v___x_2256_; uint8_t v___x_2257_; 
v___x_2256_ = 97;
v___x_2257_ = lean_uint32_dec_le(v___x_2256_, v___y_2253_);
if (v___x_2257_ == 0)
{
v___y_2246_ = v___y_2253_;
v___y_2247_ = v___y_2254_;
v___y_2248_ = v___y_2255_;
goto v___jp_2245_;
}
else
{
uint32_t v___x_2258_; uint8_t v___x_2259_; 
v___x_2258_ = 122;
v___x_2259_ = lean_uint32_dec_le(v___y_2253_, v___x_2258_);
if (v___x_2259_ == 0)
{
v___y_2246_ = v___y_2253_;
v___y_2247_ = v___y_2254_;
v___y_2248_ = v___y_2255_;
goto v___jp_2245_;
}
else
{
v___y_2229_ = v___y_2254_;
v___y_2230_ = v___y_2255_;
v___y_2231_ = v___x_2259_;
goto v___jp_2228_;
}
}
}
v___jp_2260_:
{
if (lean_obj_tag(v_x_2066_) == 2)
{
lean_object* v_val_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v_val_2262_ = lean_ctor_get(v_x_2066_, 1);
v___x_2263_ = lean_unsigned_to_nat(0u);
v___x_2264_ = lean_string_utf8_byte_size(v_val_2262_);
lean_inc_ref(v_val_2262_);
v___x_2265_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2265_, 0, v_val_2262_);
lean_ctor_set(v___x_2265_, 1, v___x_2263_);
lean_ctor_set(v___x_2265_, 2, v___x_2264_);
v___x_2266_ = l_String_Slice_Pos_get_x3f(v___x_2265_, v___x_2263_);
lean_dec_ref_known(v___x_2265_, 3);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_inc_ref(v_val_2262_);
v___y_2229_ = v_val_2262_;
v___y_2230_ = v___y_2261_;
v___y_2231_ = v___x_2201_;
goto v___jp_2228_;
}
else
{
lean_object* v_val_2267_; uint32_t v___x_2268_; uint32_t v___x_2269_; uint8_t v___x_2270_; 
v_val_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_val_2267_);
lean_dec_ref_known(v___x_2266_, 1);
v___x_2268_ = 65;
v___x_2269_ = lean_unbox_uint32(v_val_2267_);
v___x_2270_ = lean_uint32_dec_le(v___x_2268_, v___x_2269_);
if (v___x_2270_ == 0)
{
uint32_t v___x_2271_; 
v___x_2271_ = lean_unbox_uint32(v_val_2267_);
lean_dec(v_val_2267_);
lean_inc_ref(v_val_2262_);
v___y_2253_ = v___x_2271_;
v___y_2254_ = v_val_2262_;
v___y_2255_ = v___y_2261_;
goto v___jp_2252_;
}
else
{
uint32_t v___x_2272_; uint32_t v___x_2273_; uint8_t v___x_2274_; 
v___x_2272_ = 90;
v___x_2273_ = lean_unbox_uint32(v_val_2267_);
v___x_2274_ = lean_uint32_dec_le(v___x_2273_, v___x_2272_);
if (v___x_2274_ == 0)
{
uint32_t v___x_2275_; 
v___x_2275_ = lean_unbox_uint32(v_val_2267_);
lean_dec(v_val_2267_);
lean_inc_ref(v_val_2262_);
v___y_2253_ = v___x_2275_;
v___y_2254_ = v_val_2262_;
v___y_2255_ = v___y_2261_;
goto v___jp_2252_;
}
else
{
lean_dec(v_val_2267_);
lean_inc_ref(v_val_2262_);
v___y_2229_ = v_val_2262_;
v___y_2230_ = v___y_2261_;
v___y_2231_ = v___x_2274_;
goto v___jp_2228_;
}
}
}
}
else
{
lean_dec(v_x_2066_);
return v___y_2261_;
}
}
}
else
{
lean_object* v___x_2298_; 
lean_dec(v___x_2198_);
lean_dec(v_x_2066_);
lean_dec_ref(v_text_2065_);
v___x_2298_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2298_;
}
}
else
{
lean_object* v___x_2299_; uint8_t v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2303_; uint8_t v___y_2304_; uint8_t v___y_2318_; lean_object* v___y_2319_; uint32_t v___y_2320_; lean_object* v___y_2321_; uint8_t v___y_2326_; lean_object* v___y_2327_; uint32_t v___y_2328_; lean_object* v___y_2329_; uint8_t v___y_2335_; lean_object* v___y_2336_; uint8_t v___y_2351_; lean_object* v___y_2352_; uint8_t v___y_2353_; lean_object* v___y_2354_; uint8_t v___y_2355_; uint8_t v___y_2369_; uint32_t v___y_2370_; lean_object* v___y_2371_; uint8_t v___y_2372_; lean_object* v___y_2373_; uint8_t v___y_2378_; uint32_t v___y_2379_; lean_object* v___y_2380_; uint8_t v___y_2381_; lean_object* v___y_2382_; uint8_t v___y_2388_; uint8_t v___y_2389_; lean_object* v___y_2390_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2299_ = lean_unsigned_to_nat(0u);
v___x_2404_ = l_Lean_Syntax_getArg(v_x_2066_, v___x_2299_);
v___x_2405_ = lean_unsigned_to_nat(1u);
v___x_2406_ = lean_unsigned_to_nat(2u);
v___x_2407_ = l_Lean_Syntax_getArg(v_x_2066_, v___x_2406_);
if (v___x_2163_ == 0)
{
lean_object* v___x_2468_; uint8_t v___x_2469_; 
v___x_2468_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__10));
lean_inc(v___x_2407_);
v___x_2469_ = l_Lean_Syntax_isOfKind(v___x_2407_, v___x_2468_);
if (v___x_2469_ == 0)
{
lean_object* v___x_2470_; lean_object* v___x_2471_; uint8_t v___x_2472_; 
lean_dec(v___x_2407_);
v___x_2470_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2066_);
v___x_2471_ = l_Lean_Syntax_getKind(v_x_2066_);
v___x_2472_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2470_, v___x_2471_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; uint8_t v___x_2474_; lean_object* v___y_2476_; lean_object* v___y_2477_; uint8_t v___y_2478_; uint8_t v___y_2479_; lean_object* v___y_2481_; lean_object* v___y_2482_; uint8_t v___y_2483_; uint8_t v___y_2484_; lean_object* v___y_2486_; uint32_t v___y_2487_; lean_object* v___y_2488_; uint8_t v___y_2489_; lean_object* v___y_2494_; uint32_t v___y_2495_; lean_object* v___y_2496_; uint8_t v___y_2497_; lean_object* v___y_2503_; lean_object* v___y_2504_; uint8_t v___y_2505_; lean_object* v___y_2519_; lean_object* v___y_2520_; uint32_t v___y_2521_; lean_object* v___y_2526_; lean_object* v___y_2527_; uint32_t v___y_2528_; lean_object* v___y_2534_; 
v___x_2473_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2474_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2473_, v___x_2471_);
lean_dec(v___x_2471_);
if (v___x_2474_ == 0)
{
lean_object* v___x_2548_; uint8_t v___x_2549_; 
v___x_2548_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2066_);
v___x_2549_ = l_Lean_Syntax_isOfKind(v_x_2066_, v___x_2548_);
if (v___x_2549_ == 0)
{
lean_object* v___x_2550_; size_t v_sz_2551_; size_t v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; uint8_t v___x_2556_; 
lean_dec(v___x_2404_);
v___x_2550_ = l_Lean_Syntax_getArgs(v_x_2066_);
v_sz_2551_ = lean_array_size(v___x_2550_);
v___x_2552_ = ((size_t)0ULL);
v___x_2553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2065_, v_sz_2551_, v___x_2552_, v___x_2550_);
v___x_2554_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2555_ = lean_array_get_size(v___x_2553_);
v___x_2556_ = lean_nat_dec_lt(v___x_2299_, v___x_2555_);
if (v___x_2556_ == 0)
{
lean_dec_ref(v___x_2553_);
v___y_2534_ = v___x_2554_;
goto v___jp_2533_;
}
else
{
size_t v___x_2557_; lean_object* v___x_2558_; 
v___x_2557_ = lean_usize_of_nat(v___x_2555_);
v___x_2558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2553_, v___x_2552_, v___x_2557_, v___x_2554_);
lean_dec_ref(v___x_2553_);
v___y_2534_ = v___x_2558_;
goto v___jp_2533_;
}
}
else
{
lean_object* v___x_2559_; 
v___x_2559_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2065_, v___x_2404_);
v___y_2534_ = v___x_2559_;
goto v___jp_2533_;
}
}
else
{
lean_object* v___x_2560_; lean_object* v___x_2561_; uint8_t v___x_2562_; 
lean_dec(v___x_2404_);
v___x_2560_ = l_Lean_Syntax_getArg(v_x_2066_, v___x_2405_);
lean_dec(v_x_2066_);
v___x_2561_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v___x_2560_);
v___x_2562_ = l_Lean_Syntax_isOfKind(v___x_2560_, v___x_2561_);
if (v___x_2562_ == 0)
{
lean_object* v___x_2563_; 
lean_dec(v___x_2560_);
lean_dec_ref(v_text_2065_);
v___x_2563_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2563_;
}
else
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2564_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2564_, 0, v_text_2065_);
v___x_2565_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v___x_2560_, v___x_2564_);
return v___x_2565_;
}
}
v___jp_2475_:
{
if (v___y_2479_ == 0)
{
v___y_2151_ = v___y_2476_;
v___y_2152_ = v___y_2477_;
v___y_2153_ = v___x_2474_;
goto v___jp_2150_;
}
else
{
if (v___y_2478_ == 0)
{
v___y_2151_ = v___y_2476_;
v___y_2152_ = v___y_2477_;
v___y_2153_ = v___x_2165_;
goto v___jp_2150_;
}
else
{
v___y_2151_ = v___y_2476_;
v___y_2152_ = v___y_2477_;
v___y_2153_ = v___x_2474_;
goto v___jp_2150_;
}
}
}
v___jp_2480_:
{
if (v___y_2483_ == 0)
{
v___y_2476_ = v___y_2481_;
v___y_2477_ = v___y_2482_;
v___y_2478_ = v___y_2484_;
v___y_2479_ = v___x_2165_;
goto v___jp_2475_;
}
else
{
v___y_2476_ = v___y_2481_;
v___y_2477_ = v___y_2482_;
v___y_2478_ = v___y_2484_;
v___y_2479_ = v___x_2474_;
goto v___jp_2475_;
}
}
v___jp_2485_:
{
uint32_t v___x_2490_; uint8_t v___x_2491_; 
v___x_2490_ = 95;
v___x_2491_ = lean_uint32_dec_eq(v___y_2487_, v___x_2490_);
if (v___x_2491_ == 0)
{
uint8_t v___x_2492_; 
v___x_2492_ = l_Lean_isLetterLike(v___y_2487_);
v___y_2481_ = v___y_2486_;
v___y_2482_ = v___y_2488_;
v___y_2483_ = v___y_2489_;
v___y_2484_ = v___x_2492_;
goto v___jp_2480_;
}
else
{
v___y_2481_ = v___y_2486_;
v___y_2482_ = v___y_2488_;
v___y_2483_ = v___y_2489_;
v___y_2484_ = v___x_2491_;
goto v___jp_2480_;
}
}
v___jp_2493_:
{
uint32_t v___x_2498_; uint8_t v___x_2499_; 
v___x_2498_ = 97;
v___x_2499_ = lean_uint32_dec_le(v___x_2498_, v___y_2495_);
if (v___x_2499_ == 0)
{
v___y_2486_ = v___y_2494_;
v___y_2487_ = v___y_2495_;
v___y_2488_ = v___y_2496_;
v___y_2489_ = v___y_2497_;
goto v___jp_2485_;
}
else
{
uint32_t v___x_2500_; uint8_t v___x_2501_; 
v___x_2500_ = 122;
v___x_2501_ = lean_uint32_dec_le(v___y_2495_, v___x_2500_);
if (v___x_2501_ == 0)
{
v___y_2486_ = v___y_2494_;
v___y_2487_ = v___y_2495_;
v___y_2488_ = v___y_2496_;
v___y_2489_ = v___y_2497_;
goto v___jp_2485_;
}
else
{
v___y_2481_ = v___y_2494_;
v___y_2482_ = v___y_2496_;
v___y_2483_ = v___y_2497_;
v___y_2484_ = v___x_2501_;
goto v___jp_2480_;
}
}
}
v___jp_2502_:
{
lean_object* v___x_2506_; 
lean_inc_ref(v___y_2503_);
v___x_2506_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2503_);
if (lean_obj_tag(v___x_2506_) == 0)
{
v___y_2481_ = v___y_2503_;
v___y_2482_ = v___y_2504_;
v___y_2483_ = v___y_2505_;
v___y_2484_ = v___x_2474_;
goto v___jp_2480_;
}
else
{
lean_object* v_val_2507_; lean_object* v___x_2508_; 
v_val_2507_ = lean_ctor_get(v___x_2506_, 0);
lean_inc(v_val_2507_);
lean_dec_ref_known(v___x_2506_, 1);
v___x_2508_ = l_String_Slice_Pos_get_x3f(v_val_2507_, v___x_2299_);
lean_dec(v_val_2507_);
if (lean_obj_tag(v___x_2508_) == 0)
{
v___y_2481_ = v___y_2503_;
v___y_2482_ = v___y_2504_;
v___y_2483_ = v___y_2505_;
v___y_2484_ = v___x_2474_;
goto v___jp_2480_;
}
else
{
lean_object* v_val_2509_; uint32_t v___x_2510_; uint32_t v___x_2511_; uint8_t v___x_2512_; 
v_val_2509_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_val_2509_);
lean_dec_ref_known(v___x_2508_, 1);
v___x_2510_ = 65;
v___x_2511_ = lean_unbox_uint32(v_val_2509_);
v___x_2512_ = lean_uint32_dec_le(v___x_2510_, v___x_2511_);
if (v___x_2512_ == 0)
{
uint32_t v___x_2513_; 
v___x_2513_ = lean_unbox_uint32(v_val_2509_);
lean_dec(v_val_2509_);
v___y_2494_ = v___y_2503_;
v___y_2495_ = v___x_2513_;
v___y_2496_ = v___y_2504_;
v___y_2497_ = v___y_2505_;
goto v___jp_2493_;
}
else
{
uint32_t v___x_2514_; uint32_t v___x_2515_; uint8_t v___x_2516_; 
v___x_2514_ = 90;
v___x_2515_ = lean_unbox_uint32(v_val_2509_);
v___x_2516_ = lean_uint32_dec_le(v___x_2515_, v___x_2514_);
if (v___x_2516_ == 0)
{
uint32_t v___x_2517_; 
v___x_2517_ = lean_unbox_uint32(v_val_2509_);
lean_dec(v_val_2509_);
v___y_2494_ = v___y_2503_;
v___y_2495_ = v___x_2517_;
v___y_2496_ = v___y_2504_;
v___y_2497_ = v___y_2505_;
goto v___jp_2493_;
}
else
{
lean_dec(v_val_2509_);
v___y_2481_ = v___y_2503_;
v___y_2482_ = v___y_2504_;
v___y_2483_ = v___y_2505_;
v___y_2484_ = v___x_2516_;
goto v___jp_2480_;
}
}
}
}
}
v___jp_2518_:
{
uint32_t v___x_2522_; uint8_t v___x_2523_; 
v___x_2522_ = 95;
v___x_2523_ = lean_uint32_dec_eq(v___y_2521_, v___x_2522_);
if (v___x_2523_ == 0)
{
uint8_t v___x_2524_; 
v___x_2524_ = l_Lean_isLetterLike(v___y_2521_);
v___y_2503_ = v___y_2519_;
v___y_2504_ = v___y_2520_;
v___y_2505_ = v___x_2524_;
goto v___jp_2502_;
}
else
{
v___y_2503_ = v___y_2519_;
v___y_2504_ = v___y_2520_;
v___y_2505_ = v___x_2523_;
goto v___jp_2502_;
}
}
v___jp_2525_:
{
uint32_t v___x_2529_; uint8_t v___x_2530_; 
v___x_2529_ = 97;
v___x_2530_ = lean_uint32_dec_le(v___x_2529_, v___y_2528_);
if (v___x_2530_ == 0)
{
v___y_2519_ = v___y_2526_;
v___y_2520_ = v___y_2527_;
v___y_2521_ = v___y_2528_;
goto v___jp_2518_;
}
else
{
uint32_t v___x_2531_; uint8_t v___x_2532_; 
v___x_2531_ = 122;
v___x_2532_ = lean_uint32_dec_le(v___y_2528_, v___x_2531_);
if (v___x_2532_ == 0)
{
v___y_2519_ = v___y_2526_;
v___y_2520_ = v___y_2527_;
v___y_2521_ = v___y_2528_;
goto v___jp_2518_;
}
else
{
v___y_2503_ = v___y_2526_;
v___y_2504_ = v___y_2527_;
v___y_2505_ = v___x_2532_;
goto v___jp_2502_;
}
}
}
v___jp_2533_:
{
if (lean_obj_tag(v_x_2066_) == 2)
{
lean_object* v_val_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
v_val_2535_ = lean_ctor_get(v_x_2066_, 1);
v___x_2536_ = lean_string_utf8_byte_size(v_val_2535_);
lean_inc_ref(v_val_2535_);
v___x_2537_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2537_, 0, v_val_2535_);
lean_ctor_set(v___x_2537_, 1, v___x_2299_);
lean_ctor_set(v___x_2537_, 2, v___x_2536_);
v___x_2538_ = l_String_Slice_Pos_get_x3f(v___x_2537_, v___x_2299_);
lean_dec_ref_known(v___x_2537_, 3);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_inc_ref(v_val_2535_);
v___y_2503_ = v_val_2535_;
v___y_2504_ = v___y_2534_;
v___y_2505_ = v___x_2474_;
goto v___jp_2502_;
}
else
{
lean_object* v_val_2539_; uint32_t v___x_2540_; uint32_t v___x_2541_; uint8_t v___x_2542_; 
v_val_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_val_2539_);
lean_dec_ref_known(v___x_2538_, 1);
v___x_2540_ = 65;
v___x_2541_ = lean_unbox_uint32(v_val_2539_);
v___x_2542_ = lean_uint32_dec_le(v___x_2540_, v___x_2541_);
if (v___x_2542_ == 0)
{
uint32_t v___x_2543_; 
v___x_2543_ = lean_unbox_uint32(v_val_2539_);
lean_dec(v_val_2539_);
lean_inc_ref(v_val_2535_);
v___y_2526_ = v_val_2535_;
v___y_2527_ = v___y_2534_;
v___y_2528_ = v___x_2543_;
goto v___jp_2525_;
}
else
{
uint32_t v___x_2544_; uint32_t v___x_2545_; uint8_t v___x_2546_; 
v___x_2544_ = 90;
v___x_2545_ = lean_unbox_uint32(v_val_2539_);
v___x_2546_ = lean_uint32_dec_le(v___x_2545_, v___x_2544_);
if (v___x_2546_ == 0)
{
uint32_t v___x_2547_; 
v___x_2547_ = lean_unbox_uint32(v_val_2539_);
lean_dec(v_val_2539_);
lean_inc_ref(v_val_2535_);
v___y_2526_ = v_val_2535_;
v___y_2527_ = v___y_2534_;
v___y_2528_ = v___x_2547_;
goto v___jp_2525_;
}
else
{
lean_dec(v_val_2539_);
lean_inc_ref(v_val_2535_);
v___y_2503_ = v_val_2535_;
v___y_2504_ = v___y_2534_;
v___y_2505_ = v___x_2546_;
goto v___jp_2502_;
}
}
}
}
else
{
lean_dec(v_x_2066_);
return v___y_2534_;
}
}
}
else
{
lean_object* v___x_2566_; 
lean_dec(v___x_2471_);
lean_dec(v___x_2404_);
lean_dec(v_x_2066_);
lean_dec_ref(v_text_2065_);
v___x_2566_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2566_;
}
}
else
{
goto v___jp_2408_;
}
}
else
{
goto v___jp_2408_;
}
v___jp_2300_:
{
lean_object* v___x_2305_; 
lean_inc_ref(v___y_2302_);
v___x_2305_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2302_);
if (lean_obj_tag(v___x_2305_) == 0)
{
v___y_2173_ = v___y_2304_;
v___y_2174_ = v___y_2301_;
v___y_2175_ = v___y_2302_;
v___y_2176_ = v___y_2303_;
v___y_2177_ = v___y_2301_;
goto v___jp_2172_;
}
else
{
lean_object* v_val_2306_; lean_object* v___x_2307_; 
v_val_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_val_2306_);
lean_dec_ref_known(v___x_2305_, 1);
v___x_2307_ = l_String_Slice_Pos_get_x3f(v_val_2306_, v___x_2299_);
lean_dec(v_val_2306_);
if (lean_obj_tag(v___x_2307_) == 0)
{
v___y_2173_ = v___y_2304_;
v___y_2174_ = v___y_2301_;
v___y_2175_ = v___y_2302_;
v___y_2176_ = v___y_2303_;
v___y_2177_ = v___y_2301_;
goto v___jp_2172_;
}
else
{
lean_object* v_val_2308_; uint32_t v___x_2309_; uint32_t v___x_2310_; uint8_t v___x_2311_; 
v_val_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_val_2308_);
lean_dec_ref_known(v___x_2307_, 1);
v___x_2309_ = 65;
v___x_2310_ = lean_unbox_uint32(v_val_2308_);
v___x_2311_ = lean_uint32_dec_le(v___x_2309_, v___x_2310_);
if (v___x_2311_ == 0)
{
uint32_t v___x_2312_; 
v___x_2312_ = lean_unbox_uint32(v_val_2308_);
lean_dec(v_val_2308_);
v___y_2188_ = v___y_2304_;
v___y_2189_ = v___y_2301_;
v___y_2190_ = v___x_2312_;
v___y_2191_ = v___y_2302_;
v___y_2192_ = v___y_2303_;
goto v___jp_2187_;
}
else
{
uint32_t v___x_2313_; uint32_t v___x_2314_; uint8_t v___x_2315_; 
v___x_2313_ = 90;
v___x_2314_ = lean_unbox_uint32(v_val_2308_);
v___x_2315_ = lean_uint32_dec_le(v___x_2314_, v___x_2313_);
if (v___x_2315_ == 0)
{
uint32_t v___x_2316_; 
v___x_2316_ = lean_unbox_uint32(v_val_2308_);
lean_dec(v_val_2308_);
v___y_2188_ = v___y_2304_;
v___y_2189_ = v___y_2301_;
v___y_2190_ = v___x_2316_;
v___y_2191_ = v___y_2302_;
v___y_2192_ = v___y_2303_;
goto v___jp_2187_;
}
else
{
lean_dec(v_val_2308_);
v___y_2173_ = v___y_2304_;
v___y_2174_ = v___y_2301_;
v___y_2175_ = v___y_2302_;
v___y_2176_ = v___y_2303_;
v___y_2177_ = v___x_2315_;
goto v___jp_2172_;
}
}
}
}
}
v___jp_2317_:
{
uint32_t v___x_2322_; uint8_t v___x_2323_; 
v___x_2322_ = 95;
v___x_2323_ = lean_uint32_dec_eq(v___y_2320_, v___x_2322_);
if (v___x_2323_ == 0)
{
uint8_t v___x_2324_; 
v___x_2324_ = l_Lean_isLetterLike(v___y_2320_);
v___y_2301_ = v___y_2318_;
v___y_2302_ = v___y_2319_;
v___y_2303_ = v___y_2321_;
v___y_2304_ = v___x_2324_;
goto v___jp_2300_;
}
else
{
v___y_2301_ = v___y_2318_;
v___y_2302_ = v___y_2319_;
v___y_2303_ = v___y_2321_;
v___y_2304_ = v___x_2323_;
goto v___jp_2300_;
}
}
v___jp_2325_:
{
uint32_t v___x_2330_; uint8_t v___x_2331_; 
v___x_2330_ = 97;
v___x_2331_ = lean_uint32_dec_le(v___x_2330_, v___y_2328_);
if (v___x_2331_ == 0)
{
v___y_2318_ = v___y_2326_;
v___y_2319_ = v___y_2327_;
v___y_2320_ = v___y_2328_;
v___y_2321_ = v___y_2329_;
goto v___jp_2317_;
}
else
{
uint32_t v___x_2332_; uint8_t v___x_2333_; 
v___x_2332_ = 122;
v___x_2333_ = lean_uint32_dec_le(v___y_2328_, v___x_2332_);
if (v___x_2333_ == 0)
{
v___y_2318_ = v___y_2326_;
v___y_2319_ = v___y_2327_;
v___y_2320_ = v___y_2328_;
v___y_2321_ = v___y_2329_;
goto v___jp_2317_;
}
else
{
v___y_2301_ = v___y_2326_;
v___y_2302_ = v___y_2327_;
v___y_2303_ = v___y_2329_;
v___y_2304_ = v___x_2333_;
goto v___jp_2300_;
}
}
}
v___jp_2334_:
{
if (lean_obj_tag(v_x_2066_) == 2)
{
lean_object* v_val_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
v_val_2337_ = lean_ctor_get(v_x_2066_, 1);
v___x_2338_ = lean_string_utf8_byte_size(v_val_2337_);
lean_inc_ref(v_val_2337_);
v___x_2339_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2339_, 0, v_val_2337_);
lean_ctor_set(v___x_2339_, 1, v___x_2299_);
lean_ctor_set(v___x_2339_, 2, v___x_2338_);
v___x_2340_ = l_String_Slice_Pos_get_x3f(v___x_2339_, v___x_2299_);
lean_dec_ref_known(v___x_2339_, 3);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_inc_ref(v_val_2337_);
v___y_2301_ = v___y_2335_;
v___y_2302_ = v_val_2337_;
v___y_2303_ = v___y_2336_;
v___y_2304_ = v___y_2335_;
goto v___jp_2300_;
}
else
{
lean_object* v_val_2341_; uint32_t v___x_2342_; uint32_t v___x_2343_; uint8_t v___x_2344_; 
v_val_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_val_2341_);
lean_dec_ref_known(v___x_2340_, 1);
v___x_2342_ = 65;
v___x_2343_ = lean_unbox_uint32(v_val_2341_);
v___x_2344_ = lean_uint32_dec_le(v___x_2342_, v___x_2343_);
if (v___x_2344_ == 0)
{
uint32_t v___x_2345_; 
v___x_2345_ = lean_unbox_uint32(v_val_2341_);
lean_dec(v_val_2341_);
lean_inc_ref(v_val_2337_);
v___y_2326_ = v___y_2335_;
v___y_2327_ = v_val_2337_;
v___y_2328_ = v___x_2345_;
v___y_2329_ = v___y_2336_;
goto v___jp_2325_;
}
else
{
uint32_t v___x_2346_; uint32_t v___x_2347_; uint8_t v___x_2348_; 
v___x_2346_ = 90;
v___x_2347_ = lean_unbox_uint32(v_val_2341_);
v___x_2348_ = lean_uint32_dec_le(v___x_2347_, v___x_2346_);
if (v___x_2348_ == 0)
{
uint32_t v___x_2349_; 
v___x_2349_ = lean_unbox_uint32(v_val_2341_);
lean_dec(v_val_2341_);
lean_inc_ref(v_val_2337_);
v___y_2326_ = v___y_2335_;
v___y_2327_ = v_val_2337_;
v___y_2328_ = v___x_2349_;
v___y_2329_ = v___y_2336_;
goto v___jp_2325_;
}
else
{
lean_dec(v_val_2341_);
lean_inc_ref(v_val_2337_);
v___y_2301_ = v___y_2335_;
v___y_2302_ = v_val_2337_;
v___y_2303_ = v___y_2336_;
v___y_2304_ = v___x_2348_;
goto v___jp_2300_;
}
}
}
}
else
{
lean_dec(v_x_2066_);
return v___y_2336_;
}
}
v___jp_2350_:
{
lean_object* v___x_2356_; 
lean_inc_ref(v___y_2354_);
v___x_2356_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2354_);
if (lean_obj_tag(v___x_2356_) == 0)
{
v___y_2123_ = v___y_2351_;
v___y_2124_ = v___y_2352_;
v___y_2125_ = v___y_2353_;
v___y_2126_ = v___y_2354_;
v___y_2127_ = v___y_2355_;
v___y_2128_ = v___y_2351_;
goto v___jp_2122_;
}
else
{
lean_object* v_val_2357_; lean_object* v___x_2358_; 
v_val_2357_ = lean_ctor_get(v___x_2356_, 0);
lean_inc(v_val_2357_);
lean_dec_ref_known(v___x_2356_, 1);
v___x_2358_ = l_String_Slice_Pos_get_x3f(v_val_2357_, v___x_2299_);
lean_dec(v_val_2357_);
if (lean_obj_tag(v___x_2358_) == 0)
{
v___y_2123_ = v___y_2351_;
v___y_2124_ = v___y_2352_;
v___y_2125_ = v___y_2353_;
v___y_2126_ = v___y_2354_;
v___y_2127_ = v___y_2355_;
v___y_2128_ = v___y_2351_;
goto v___jp_2122_;
}
else
{
lean_object* v_val_2359_; uint32_t v___x_2360_; uint32_t v___x_2361_; uint8_t v___x_2362_; 
v_val_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_val_2359_);
lean_dec_ref_known(v___x_2358_, 1);
v___x_2360_ = 65;
v___x_2361_ = lean_unbox_uint32(v_val_2359_);
v___x_2362_ = lean_uint32_dec_le(v___x_2360_, v___x_2361_);
if (v___x_2362_ == 0)
{
uint32_t v___x_2363_; 
v___x_2363_ = lean_unbox_uint32(v_val_2359_);
lean_dec(v_val_2359_);
v___y_2140_ = v___y_2351_;
v___y_2141_ = v___y_2352_;
v___y_2142_ = v___y_2353_;
v___y_2143_ = v___y_2354_;
v___y_2144_ = v___x_2363_;
v___y_2145_ = v___y_2355_;
goto v___jp_2139_;
}
else
{
uint32_t v___x_2364_; uint32_t v___x_2365_; uint8_t v___x_2366_; 
v___x_2364_ = 90;
v___x_2365_ = lean_unbox_uint32(v_val_2359_);
v___x_2366_ = lean_uint32_dec_le(v___x_2365_, v___x_2364_);
if (v___x_2366_ == 0)
{
uint32_t v___x_2367_; 
v___x_2367_ = lean_unbox_uint32(v_val_2359_);
lean_dec(v_val_2359_);
v___y_2140_ = v___y_2351_;
v___y_2141_ = v___y_2352_;
v___y_2142_ = v___y_2353_;
v___y_2143_ = v___y_2354_;
v___y_2144_ = v___x_2367_;
v___y_2145_ = v___y_2355_;
goto v___jp_2139_;
}
else
{
lean_dec(v_val_2359_);
v___y_2123_ = v___y_2351_;
v___y_2124_ = v___y_2352_;
v___y_2125_ = v___y_2353_;
v___y_2126_ = v___y_2354_;
v___y_2127_ = v___y_2355_;
v___y_2128_ = v___x_2366_;
goto v___jp_2122_;
}
}
}
}
}
v___jp_2368_:
{
uint32_t v___x_2374_; uint8_t v___x_2375_; 
v___x_2374_ = 95;
v___x_2375_ = lean_uint32_dec_eq(v___y_2370_, v___x_2374_);
if (v___x_2375_ == 0)
{
uint8_t v___x_2376_; 
v___x_2376_ = l_Lean_isLetterLike(v___y_2370_);
v___y_2351_ = v___y_2369_;
v___y_2352_ = v___y_2371_;
v___y_2353_ = v___y_2372_;
v___y_2354_ = v___y_2373_;
v___y_2355_ = v___x_2376_;
goto v___jp_2350_;
}
else
{
v___y_2351_ = v___y_2369_;
v___y_2352_ = v___y_2371_;
v___y_2353_ = v___y_2372_;
v___y_2354_ = v___y_2373_;
v___y_2355_ = v___x_2375_;
goto v___jp_2350_;
}
}
v___jp_2377_:
{
uint32_t v___x_2383_; uint8_t v___x_2384_; 
v___x_2383_ = 97;
v___x_2384_ = lean_uint32_dec_le(v___x_2383_, v___y_2379_);
if (v___x_2384_ == 0)
{
v___y_2369_ = v___y_2378_;
v___y_2370_ = v___y_2379_;
v___y_2371_ = v___y_2380_;
v___y_2372_ = v___y_2381_;
v___y_2373_ = v___y_2382_;
goto v___jp_2368_;
}
else
{
uint32_t v___x_2385_; uint8_t v___x_2386_; 
v___x_2385_ = 122;
v___x_2386_ = lean_uint32_dec_le(v___y_2379_, v___x_2385_);
if (v___x_2386_ == 0)
{
v___y_2369_ = v___y_2378_;
v___y_2370_ = v___y_2379_;
v___y_2371_ = v___y_2380_;
v___y_2372_ = v___y_2381_;
v___y_2373_ = v___y_2382_;
goto v___jp_2368_;
}
else
{
v___y_2351_ = v___y_2378_;
v___y_2352_ = v___y_2380_;
v___y_2353_ = v___y_2381_;
v___y_2354_ = v___y_2382_;
v___y_2355_ = v___x_2386_;
goto v___jp_2350_;
}
}
}
v___jp_2387_:
{
if (lean_obj_tag(v_x_2066_) == 2)
{
lean_object* v_val_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v_val_2391_ = lean_ctor_get(v_x_2066_, 1);
v___x_2392_ = lean_string_utf8_byte_size(v_val_2391_);
lean_inc_ref(v_val_2391_);
v___x_2393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2393_, 0, v_val_2391_);
lean_ctor_set(v___x_2393_, 1, v___x_2299_);
lean_ctor_set(v___x_2393_, 2, v___x_2392_);
v___x_2394_ = l_String_Slice_Pos_get_x3f(v___x_2393_, v___x_2299_);
lean_dec_ref_known(v___x_2393_, 3);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_inc_ref(v_val_2391_);
v___y_2351_ = v___y_2388_;
v___y_2352_ = v___y_2390_;
v___y_2353_ = v___y_2389_;
v___y_2354_ = v_val_2391_;
v___y_2355_ = v___y_2388_;
goto v___jp_2350_;
}
else
{
lean_object* v_val_2395_; uint32_t v___x_2396_; uint32_t v___x_2397_; uint8_t v___x_2398_; 
v_val_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_val_2395_);
lean_dec_ref_known(v___x_2394_, 1);
v___x_2396_ = 65;
v___x_2397_ = lean_unbox_uint32(v_val_2395_);
v___x_2398_ = lean_uint32_dec_le(v___x_2396_, v___x_2397_);
if (v___x_2398_ == 0)
{
uint32_t v___x_2399_; 
v___x_2399_ = lean_unbox_uint32(v_val_2395_);
lean_dec(v_val_2395_);
lean_inc_ref(v_val_2391_);
v___y_2378_ = v___y_2388_;
v___y_2379_ = v___x_2399_;
v___y_2380_ = v___y_2390_;
v___y_2381_ = v___y_2389_;
v___y_2382_ = v_val_2391_;
goto v___jp_2377_;
}
else
{
uint32_t v___x_2400_; uint32_t v___x_2401_; uint8_t v___x_2402_; 
v___x_2400_ = 90;
v___x_2401_ = lean_unbox_uint32(v_val_2395_);
v___x_2402_ = lean_uint32_dec_le(v___x_2401_, v___x_2400_);
if (v___x_2402_ == 0)
{
uint32_t v___x_2403_; 
v___x_2403_ = lean_unbox_uint32(v_val_2395_);
lean_dec(v_val_2395_);
lean_inc_ref(v_val_2391_);
v___y_2378_ = v___y_2388_;
v___y_2379_ = v___x_2403_;
v___y_2380_ = v___y_2390_;
v___y_2381_ = v___y_2389_;
v___y_2382_ = v_val_2391_;
goto v___jp_2377_;
}
else
{
lean_dec(v_val_2395_);
lean_inc_ref(v_val_2391_);
v___y_2351_ = v___y_2388_;
v___y_2352_ = v___y_2390_;
v___y_2353_ = v___y_2389_;
v___y_2354_ = v_val_2391_;
v___y_2355_ = v___x_2402_;
goto v___jp_2350_;
}
}
}
}
else
{
lean_dec(v_x_2066_);
return v___y_2390_;
}
}
v___jp_2408_:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; uint8_t v___x_2411_; 
v___x_2409_ = lean_unsigned_to_nat(3u);
v___x_2410_ = l_Lean_Syntax_getArg(v_x_2066_, v___x_2409_);
v___x_2411_ = l_Lean_Syntax_matchesNull(v___x_2410_, v___x_2299_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; lean_object* v___x_2413_; uint8_t v___x_2414_; 
lean_dec(v___x_2407_);
v___x_2412_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2066_);
v___x_2413_ = l_Lean_Syntax_getKind(v_x_2066_);
v___x_2414_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2412_, v___x_2413_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; uint8_t v___x_2416_; 
v___x_2415_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2416_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2415_, v___x_2413_);
lean_dec(v___x_2413_);
if (v___x_2416_ == 0)
{
lean_object* v___x_2417_; uint8_t v___x_2418_; 
v___x_2417_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2066_);
v___x_2418_ = l_Lean_Syntax_isOfKind(v_x_2066_, v___x_2417_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; size_t v_sz_2420_; size_t v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; uint8_t v___x_2425_; 
lean_dec(v___x_2404_);
v___x_2419_ = l_Lean_Syntax_getArgs(v_x_2066_);
v_sz_2420_ = lean_array_size(v___x_2419_);
v___x_2421_ = ((size_t)0ULL);
v___x_2422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2065_, v_sz_2420_, v___x_2421_, v___x_2419_);
v___x_2423_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2424_ = lean_array_get_size(v___x_2422_);
v___x_2425_ = lean_nat_dec_lt(v___x_2299_, v___x_2424_);
if (v___x_2425_ == 0)
{
lean_dec_ref(v___x_2422_);
v___y_2335_ = v___x_2416_;
v___y_2336_ = v___x_2423_;
goto v___jp_2334_;
}
else
{
size_t v___x_2426_; lean_object* v___x_2427_; 
v___x_2426_ = lean_usize_of_nat(v___x_2424_);
v___x_2427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2422_, v___x_2421_, v___x_2426_, v___x_2423_);
lean_dec_ref(v___x_2422_);
v___y_2335_ = v___x_2416_;
v___y_2336_ = v___x_2427_;
goto v___jp_2334_;
}
}
else
{
lean_object* v___x_2428_; 
v___x_2428_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2065_, v___x_2404_);
v___y_2335_ = v___x_2416_;
v___y_2336_ = v___x_2428_;
goto v___jp_2334_;
}
}
else
{
lean_object* v___x_2429_; lean_object* v___x_2430_; uint8_t v___x_2431_; 
lean_dec(v___x_2404_);
v___x_2429_ = l_Lean_Syntax_getArg(v_x_2066_, v___x_2405_);
lean_dec(v_x_2066_);
v___x_2430_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v___x_2429_);
v___x_2431_ = l_Lean_Syntax_isOfKind(v___x_2429_, v___x_2430_);
if (v___x_2431_ == 0)
{
lean_object* v___x_2432_; 
lean_dec(v___x_2429_);
lean_dec_ref(v_text_2065_);
v___x_2432_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2432_;
}
else
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2433_, 0, v_text_2065_);
v___x_2434_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v___x_2429_, v___x_2433_);
return v___x_2434_;
}
}
}
else
{
lean_object* v___x_2435_; 
lean_dec(v___x_2413_);
lean_dec(v___x_2404_);
lean_dec(v_x_2066_);
lean_dec_ref(v_text_2065_);
v___x_2435_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2435_;
}
}
else
{
lean_object* v___x_2436_; lean_object* v___x_2437_; uint8_t v___x_2438_; 
v___x_2436_ = lean_unsigned_to_nat(4u);
v___x_2437_ = l_Lean_Syntax_getArg(v_x_2066_, v___x_2436_);
v___x_2438_ = l_Lean_Syntax_matchesNull(v___x_2437_, v___x_2299_);
if (v___x_2438_ == 0)
{
lean_object* v___x_2439_; lean_object* v___x_2440_; uint8_t v___x_2441_; 
lean_dec(v___x_2407_);
v___x_2439_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2066_);
v___x_2440_ = l_Lean_Syntax_getKind(v_x_2066_);
v___x_2441_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2439_, v___x_2440_);
if (v___x_2441_ == 0)
{
lean_object* v___x_2442_; uint8_t v___x_2443_; 
v___x_2442_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2443_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2442_, v___x_2440_);
lean_dec(v___x_2440_);
if (v___x_2443_ == 0)
{
lean_object* v___x_2444_; uint8_t v___x_2445_; 
v___x_2444_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2066_);
v___x_2445_ = l_Lean_Syntax_isOfKind(v_x_2066_, v___x_2444_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2446_; size_t v_sz_2447_; size_t v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; uint8_t v___x_2452_; 
lean_dec(v___x_2404_);
v___x_2446_ = l_Lean_Syntax_getArgs(v_x_2066_);
v_sz_2447_ = lean_array_size(v___x_2446_);
v___x_2448_ = ((size_t)0ULL);
v___x_2449_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2065_, v_sz_2447_, v___x_2448_, v___x_2446_);
v___x_2450_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2451_ = lean_array_get_size(v___x_2449_);
v___x_2452_ = lean_nat_dec_lt(v___x_2299_, v___x_2451_);
if (v___x_2452_ == 0)
{
lean_dec_ref(v___x_2449_);
v___y_2388_ = v___x_2443_;
v___y_2389_ = v___x_2411_;
v___y_2390_ = v___x_2450_;
goto v___jp_2387_;
}
else
{
size_t v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = lean_usize_of_nat(v___x_2451_);
v___x_2454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2449_, v___x_2448_, v___x_2453_, v___x_2450_);
lean_dec_ref(v___x_2449_);
v___y_2388_ = v___x_2443_;
v___y_2389_ = v___x_2411_;
v___y_2390_ = v___x_2454_;
goto v___jp_2387_;
}
}
else
{
lean_object* v___x_2455_; 
v___x_2455_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2065_, v___x_2404_);
v___y_2388_ = v___x_2443_;
v___y_2389_ = v___x_2411_;
v___y_2390_ = v___x_2455_;
goto v___jp_2387_;
}
}
else
{
lean_object* v___x_2456_; lean_object* v___x_2457_; uint8_t v___x_2458_; 
lean_dec(v___x_2404_);
v___x_2456_ = l_Lean_Syntax_getArg(v_x_2066_, v___x_2405_);
lean_dec(v_x_2066_);
v___x_2457_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v___x_2456_);
v___x_2458_ = l_Lean_Syntax_isOfKind(v___x_2456_, v___x_2457_);
if (v___x_2458_ == 0)
{
lean_object* v___x_2459_; 
lean_dec(v___x_2456_);
lean_dec_ref(v_text_2065_);
v___x_2459_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2459_;
}
else
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2460_, 0, v_text_2065_);
v___x_2461_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v___x_2456_, v___x_2460_);
return v___x_2461_;
}
}
}
else
{
lean_object* v___x_2462_; 
lean_dec(v___x_2440_);
lean_dec(v___x_2404_);
lean_dec(v_x_2066_);
lean_dec_ref(v_text_2065_);
v___x_2462_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2462_;
}
}
else
{
lean_object* v_tokens_2463_; uint8_t v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
lean_dec(v_x_2066_);
v_tokens_2463_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2065_, v___x_2404_);
v___x_2464_ = 2;
v___x_2465_ = lean_unsigned_to_nat(5u);
v___x_2466_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2466_, 0, v___x_2407_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
lean_ctor_set_uint8(v___x_2466_, sizeof(void*)*2, v___x_2464_);
v___x_2467_ = lean_array_push(v_tokens_2463_, v___x_2466_);
return v___x_2467_;
}
}
}
}
v___jp_2166_:
{
if (v___y_2171_ == 0)
{
v___y_2092_ = v___y_2169_;
v___y_2093_ = v___y_2170_;
v___y_2094_ = v___y_2168_;
goto v___jp_2091_;
}
else
{
if (v___y_2167_ == 0)
{
v___y_2092_ = v___y_2169_;
v___y_2093_ = v___y_2170_;
v___y_2094_ = v___x_2165_;
goto v___jp_2091_;
}
else
{
v___y_2092_ = v___y_2169_;
v___y_2093_ = v___y_2170_;
v___y_2094_ = v___y_2168_;
goto v___jp_2091_;
}
}
}
v___jp_2172_:
{
if (v___y_2173_ == 0)
{
v___y_2167_ = v___y_2177_;
v___y_2168_ = v___y_2174_;
v___y_2169_ = v___y_2175_;
v___y_2170_ = v___y_2176_;
v___y_2171_ = v___x_2165_;
goto v___jp_2166_;
}
else
{
v___y_2167_ = v___y_2177_;
v___y_2168_ = v___y_2174_;
v___y_2169_ = v___y_2175_;
v___y_2170_ = v___y_2176_;
v___y_2171_ = v___y_2174_;
goto v___jp_2166_;
}
}
v___jp_2178_:
{
uint32_t v___x_2184_; uint8_t v___x_2185_; 
v___x_2184_ = 95;
v___x_2185_ = lean_uint32_dec_eq(v___y_2181_, v___x_2184_);
if (v___x_2185_ == 0)
{
uint8_t v___x_2186_; 
v___x_2186_ = l_Lean_isLetterLike(v___y_2181_);
v___y_2173_ = v___y_2180_;
v___y_2174_ = v___y_2179_;
v___y_2175_ = v___y_2182_;
v___y_2176_ = v___y_2183_;
v___y_2177_ = v___x_2186_;
goto v___jp_2172_;
}
else
{
v___y_2173_ = v___y_2180_;
v___y_2174_ = v___y_2179_;
v___y_2175_ = v___y_2182_;
v___y_2176_ = v___y_2183_;
v___y_2177_ = v___x_2185_;
goto v___jp_2172_;
}
}
v___jp_2187_:
{
uint32_t v___x_2193_; uint8_t v___x_2194_; 
v___x_2193_ = 97;
v___x_2194_ = lean_uint32_dec_le(v___x_2193_, v___y_2190_);
if (v___x_2194_ == 0)
{
v___y_2179_ = v___y_2189_;
v___y_2180_ = v___y_2188_;
v___y_2181_ = v___y_2190_;
v___y_2182_ = v___y_2191_;
v___y_2183_ = v___y_2192_;
goto v___jp_2178_;
}
else
{
uint32_t v___x_2195_; uint8_t v___x_2196_; 
v___x_2195_ = 122;
v___x_2196_ = lean_uint32_dec_le(v___y_2190_, v___x_2195_);
if (v___x_2196_ == 0)
{
v___y_2179_ = v___y_2189_;
v___y_2180_ = v___y_2188_;
v___y_2181_ = v___y_2190_;
v___y_2182_ = v___y_2191_;
v___y_2183_ = v___y_2192_;
goto v___jp_2178_;
}
else
{
v___y_2173_ = v___y_2188_;
v___y_2174_ = v___y_2189_;
v___y_2175_ = v___y_2191_;
v___y_2176_ = v___y_2192_;
v___y_2177_ = v___x_2196_;
goto v___jp_2172_;
}
}
}
}
else
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; 
v___x_2567_ = lean_unsigned_to_nat(0u);
v___x_2568_ = lean_unsigned_to_nat(2u);
v___x_2569_ = l_Lean_Syntax_getArg(v_x_2066_, v___x_2568_);
v___x_2570_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__10));
lean_inc(v___x_2569_);
v___x_2571_ = l_Lean_Syntax_isOfKind(v___x_2569_, v___x_2570_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2572_; lean_object* v___x_2573_; uint8_t v___x_2574_; 
lean_dec(v___x_2569_);
v___x_2572_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2066_);
v___x_2573_ = l_Lean_Syntax_getKind(v_x_2066_);
v___x_2574_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2572_, v___x_2573_);
if (v___x_2574_ == 0)
{
lean_object* v___x_2575_; uint8_t v___x_2576_; lean_object* v___y_2578_; uint8_t v___y_2579_; lean_object* v___y_2580_; uint8_t v___y_2581_; lean_object* v___y_2583_; uint8_t v___y_2584_; lean_object* v___y_2585_; uint8_t v___y_2586_; lean_object* v___y_2588_; uint8_t v___y_2589_; uint32_t v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2596_; uint8_t v___y_2597_; uint32_t v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2605_; lean_object* v___y_2606_; uint8_t v___y_2607_; lean_object* v___y_2621_; uint32_t v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2628_; uint32_t v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2636_; 
v___x_2575_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2576_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2575_, v___x_2573_);
lean_dec(v___x_2573_);
if (v___x_2576_ == 0)
{
lean_object* v___x_2650_; uint8_t v___x_2651_; 
v___x_2650_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2066_);
v___x_2651_ = l_Lean_Syntax_isOfKind(v_x_2066_, v___x_2650_);
if (v___x_2651_ == 0)
{
lean_object* v___x_2652_; size_t v_sz_2653_; size_t v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; uint8_t v___x_2658_; 
v___x_2652_ = l_Lean_Syntax_getArgs(v_x_2066_);
v_sz_2653_ = lean_array_size(v___x_2652_);
v___x_2654_ = ((size_t)0ULL);
v___x_2655_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2065_, v_sz_2653_, v___x_2654_, v___x_2652_);
v___x_2656_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2657_ = lean_array_get_size(v___x_2655_);
v___x_2658_ = lean_nat_dec_lt(v___x_2567_, v___x_2657_);
if (v___x_2658_ == 0)
{
lean_dec_ref(v___x_2655_);
v___y_2636_ = v___x_2656_;
goto v___jp_2635_;
}
else
{
size_t v___x_2659_; lean_object* v___x_2660_; 
v___x_2659_ = lean_usize_of_nat(v___x_2657_);
v___x_2660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2655_, v___x_2654_, v___x_2659_, v___x_2656_);
lean_dec_ref(v___x_2655_);
v___y_2636_ = v___x_2660_;
goto v___jp_2635_;
}
}
else
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2661_ = l_Lean_Syntax_getArg(v_x_2066_, v___x_2567_);
v___x_2662_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2065_, v___x_2661_);
v___y_2636_ = v___x_2662_;
goto v___jp_2635_;
}
}
else
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; uint8_t v___x_2666_; 
v___x_2663_ = lean_unsigned_to_nat(1u);
v___x_2664_ = l_Lean_Syntax_getArg(v_x_2066_, v___x_2663_);
lean_dec(v_x_2066_);
v___x_2665_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v___x_2664_);
v___x_2666_ = l_Lean_Syntax_isOfKind(v___x_2664_, v___x_2665_);
if (v___x_2666_ == 0)
{
lean_object* v___x_2667_; 
lean_dec(v___x_2664_);
lean_dec_ref(v_text_2065_);
v___x_2667_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2667_;
}
else
{
lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2668_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2668_, 0, v_text_2065_);
v___x_2669_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v___x_2664_, v___x_2668_);
return v___x_2669_;
}
}
v___jp_2577_:
{
if (v___y_2581_ == 0)
{
v___y_2068_ = v___y_2578_;
v___y_2069_ = v___y_2580_;
v___y_2070_ = v___x_2576_;
goto v___jp_2067_;
}
else
{
if (v___y_2579_ == 0)
{
v___y_2068_ = v___y_2578_;
v___y_2069_ = v___y_2580_;
v___y_2070_ = v___x_2163_;
goto v___jp_2067_;
}
else
{
v___y_2068_ = v___y_2578_;
v___y_2069_ = v___y_2580_;
v___y_2070_ = v___x_2576_;
goto v___jp_2067_;
}
}
}
v___jp_2582_:
{
if (v___y_2584_ == 0)
{
v___y_2578_ = v___y_2583_;
v___y_2579_ = v___y_2586_;
v___y_2580_ = v___y_2585_;
v___y_2581_ = v___x_2163_;
goto v___jp_2577_;
}
else
{
v___y_2578_ = v___y_2583_;
v___y_2579_ = v___y_2586_;
v___y_2580_ = v___y_2585_;
v___y_2581_ = v___x_2576_;
goto v___jp_2577_;
}
}
v___jp_2587_:
{
uint32_t v___x_2592_; uint8_t v___x_2593_; 
v___x_2592_ = 95;
v___x_2593_ = lean_uint32_dec_eq(v___y_2590_, v___x_2592_);
if (v___x_2593_ == 0)
{
uint8_t v___x_2594_; 
v___x_2594_ = l_Lean_isLetterLike(v___y_2590_);
v___y_2583_ = v___y_2588_;
v___y_2584_ = v___y_2589_;
v___y_2585_ = v___y_2591_;
v___y_2586_ = v___x_2594_;
goto v___jp_2582_;
}
else
{
v___y_2583_ = v___y_2588_;
v___y_2584_ = v___y_2589_;
v___y_2585_ = v___y_2591_;
v___y_2586_ = v___x_2593_;
goto v___jp_2582_;
}
}
v___jp_2595_:
{
uint32_t v___x_2600_; uint8_t v___x_2601_; 
v___x_2600_ = 97;
v___x_2601_ = lean_uint32_dec_le(v___x_2600_, v___y_2598_);
if (v___x_2601_ == 0)
{
v___y_2588_ = v___y_2596_;
v___y_2589_ = v___y_2597_;
v___y_2590_ = v___y_2598_;
v___y_2591_ = v___y_2599_;
goto v___jp_2587_;
}
else
{
uint32_t v___x_2602_; uint8_t v___x_2603_; 
v___x_2602_ = 122;
v___x_2603_ = lean_uint32_dec_le(v___y_2598_, v___x_2602_);
if (v___x_2603_ == 0)
{
v___y_2588_ = v___y_2596_;
v___y_2589_ = v___y_2597_;
v___y_2590_ = v___y_2598_;
v___y_2591_ = v___y_2599_;
goto v___jp_2587_;
}
else
{
v___y_2583_ = v___y_2596_;
v___y_2584_ = v___y_2597_;
v___y_2585_ = v___y_2599_;
v___y_2586_ = v___x_2603_;
goto v___jp_2582_;
}
}
}
v___jp_2604_:
{
lean_object* v___x_2608_; 
lean_inc_ref(v___y_2605_);
v___x_2608_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2605_);
if (lean_obj_tag(v___x_2608_) == 0)
{
v___y_2583_ = v___y_2605_;
v___y_2584_ = v___y_2607_;
v___y_2585_ = v___y_2606_;
v___y_2586_ = v___x_2576_;
goto v___jp_2582_;
}
else
{
lean_object* v_val_2609_; lean_object* v___x_2610_; 
v_val_2609_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_val_2609_);
lean_dec_ref_known(v___x_2608_, 1);
v___x_2610_ = l_String_Slice_Pos_get_x3f(v_val_2609_, v___x_2567_);
lean_dec(v_val_2609_);
if (lean_obj_tag(v___x_2610_) == 0)
{
v___y_2583_ = v___y_2605_;
v___y_2584_ = v___y_2607_;
v___y_2585_ = v___y_2606_;
v___y_2586_ = v___x_2576_;
goto v___jp_2582_;
}
else
{
lean_object* v_val_2611_; uint32_t v___x_2612_; uint32_t v___x_2613_; uint8_t v___x_2614_; 
v_val_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_val_2611_);
lean_dec_ref_known(v___x_2610_, 1);
v___x_2612_ = 65;
v___x_2613_ = lean_unbox_uint32(v_val_2611_);
v___x_2614_ = lean_uint32_dec_le(v___x_2612_, v___x_2613_);
if (v___x_2614_ == 0)
{
uint32_t v___x_2615_; 
v___x_2615_ = lean_unbox_uint32(v_val_2611_);
lean_dec(v_val_2611_);
v___y_2596_ = v___y_2605_;
v___y_2597_ = v___y_2607_;
v___y_2598_ = v___x_2615_;
v___y_2599_ = v___y_2606_;
goto v___jp_2595_;
}
else
{
uint32_t v___x_2616_; uint32_t v___x_2617_; uint8_t v___x_2618_; 
v___x_2616_ = 90;
v___x_2617_ = lean_unbox_uint32(v_val_2611_);
v___x_2618_ = lean_uint32_dec_le(v___x_2617_, v___x_2616_);
if (v___x_2618_ == 0)
{
uint32_t v___x_2619_; 
v___x_2619_ = lean_unbox_uint32(v_val_2611_);
lean_dec(v_val_2611_);
v___y_2596_ = v___y_2605_;
v___y_2597_ = v___y_2607_;
v___y_2598_ = v___x_2619_;
v___y_2599_ = v___y_2606_;
goto v___jp_2595_;
}
else
{
lean_dec(v_val_2611_);
v___y_2583_ = v___y_2605_;
v___y_2584_ = v___y_2607_;
v___y_2585_ = v___y_2606_;
v___y_2586_ = v___x_2618_;
goto v___jp_2582_;
}
}
}
}
}
v___jp_2620_:
{
uint32_t v___x_2624_; uint8_t v___x_2625_; 
v___x_2624_ = 95;
v___x_2625_ = lean_uint32_dec_eq(v___y_2622_, v___x_2624_);
if (v___x_2625_ == 0)
{
uint8_t v___x_2626_; 
v___x_2626_ = l_Lean_isLetterLike(v___y_2622_);
v___y_2605_ = v___y_2621_;
v___y_2606_ = v___y_2623_;
v___y_2607_ = v___x_2626_;
goto v___jp_2604_;
}
else
{
v___y_2605_ = v___y_2621_;
v___y_2606_ = v___y_2623_;
v___y_2607_ = v___x_2625_;
goto v___jp_2604_;
}
}
v___jp_2627_:
{
uint32_t v___x_2631_; uint8_t v___x_2632_; 
v___x_2631_ = 97;
v___x_2632_ = lean_uint32_dec_le(v___x_2631_, v___y_2629_);
if (v___x_2632_ == 0)
{
v___y_2621_ = v___y_2628_;
v___y_2622_ = v___y_2629_;
v___y_2623_ = v___y_2630_;
goto v___jp_2620_;
}
else
{
uint32_t v___x_2633_; uint8_t v___x_2634_; 
v___x_2633_ = 122;
v___x_2634_ = lean_uint32_dec_le(v___y_2629_, v___x_2633_);
if (v___x_2634_ == 0)
{
v___y_2621_ = v___y_2628_;
v___y_2622_ = v___y_2629_;
v___y_2623_ = v___y_2630_;
goto v___jp_2620_;
}
else
{
v___y_2605_ = v___y_2628_;
v___y_2606_ = v___y_2630_;
v___y_2607_ = v___x_2634_;
goto v___jp_2604_;
}
}
}
v___jp_2635_:
{
if (lean_obj_tag(v_x_2066_) == 2)
{
lean_object* v_val_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v_val_2637_ = lean_ctor_get(v_x_2066_, 1);
v___x_2638_ = lean_string_utf8_byte_size(v_val_2637_);
lean_inc_ref(v_val_2637_);
v___x_2639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2639_, 0, v_val_2637_);
lean_ctor_set(v___x_2639_, 1, v___x_2567_);
lean_ctor_set(v___x_2639_, 2, v___x_2638_);
v___x_2640_ = l_String_Slice_Pos_get_x3f(v___x_2639_, v___x_2567_);
lean_dec_ref_known(v___x_2639_, 3);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_inc_ref(v_val_2637_);
v___y_2605_ = v_val_2637_;
v___y_2606_ = v___y_2636_;
v___y_2607_ = v___x_2576_;
goto v___jp_2604_;
}
else
{
lean_object* v_val_2641_; uint32_t v___x_2642_; uint32_t v___x_2643_; uint8_t v___x_2644_; 
v_val_2641_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_val_2641_);
lean_dec_ref_known(v___x_2640_, 1);
v___x_2642_ = 65;
v___x_2643_ = lean_unbox_uint32(v_val_2641_);
v___x_2644_ = lean_uint32_dec_le(v___x_2642_, v___x_2643_);
if (v___x_2644_ == 0)
{
uint32_t v___x_2645_; 
v___x_2645_ = lean_unbox_uint32(v_val_2641_);
lean_dec(v_val_2641_);
lean_inc_ref(v_val_2637_);
v___y_2628_ = v_val_2637_;
v___y_2629_ = v___x_2645_;
v___y_2630_ = v___y_2636_;
goto v___jp_2627_;
}
else
{
uint32_t v___x_2646_; uint32_t v___x_2647_; uint8_t v___x_2648_; 
v___x_2646_ = 90;
v___x_2647_ = lean_unbox_uint32(v_val_2641_);
v___x_2648_ = lean_uint32_dec_le(v___x_2647_, v___x_2646_);
if (v___x_2648_ == 0)
{
uint32_t v___x_2649_; 
v___x_2649_ = lean_unbox_uint32(v_val_2641_);
lean_dec(v_val_2641_);
lean_inc_ref(v_val_2637_);
v___y_2628_ = v_val_2637_;
v___y_2629_ = v___x_2649_;
v___y_2630_ = v___y_2636_;
goto v___jp_2627_;
}
else
{
lean_dec(v_val_2641_);
lean_inc_ref(v_val_2637_);
v___y_2605_ = v_val_2637_;
v___y_2606_ = v___y_2636_;
v___y_2607_ = v___x_2648_;
goto v___jp_2604_;
}
}
}
}
else
{
lean_dec(v_x_2066_);
return v___y_2636_;
}
}
}
else
{
lean_object* v___x_2670_; 
lean_dec(v___x_2573_);
lean_dec(v_x_2066_);
lean_dec_ref(v_text_2065_);
v___x_2670_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2670_;
}
}
else
{
lean_object* v___x_2671_; lean_object* v_tokens_2672_; uint8_t v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2671_ = l_Lean_Syntax_getArg(v_x_2066_, v___x_2567_);
lean_dec(v_x_2066_);
v_tokens_2672_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2065_, v___x_2671_);
v___x_2673_ = 2;
v___x_2674_ = lean_unsigned_to_nat(5u);
v___x_2675_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2675_, 0, v___x_2569_);
lean_ctor_set(v___x_2675_, 1, v___x_2674_);
lean_ctor_set_uint8(v___x_2675_, sizeof(void*)*2, v___x_2673_);
v___x_2676_ = lean_array_push(v_tokens_2672_, v___x_2675_);
return v___x_2676_;
}
}
v___jp_2067_:
{
if (v___y_2070_ == 0)
{
lean_object* v___x_2071_; uint8_t v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; lean_object* v___x_2078_; 
v___x_2071_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2072_ = 0;
v___x_2073_ = lean_box(v___x_2072_);
v___x_2074_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2071_, v___y_2068_, v___x_2073_);
lean_dec(v___x_2073_);
lean_dec_ref(v___y_2068_);
v___x_2075_ = lean_unsigned_to_nat(5u);
v___x_2076_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2076_, 0, v_x_2066_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
v___x_2077_ = lean_unbox(v___x_2074_);
lean_dec(v___x_2074_);
lean_ctor_set_uint8(v___x_2076_, sizeof(void*)*2, v___x_2077_);
v___x_2078_ = lean_array_push(v___y_2069_, v___x_2076_);
return v___x_2078_;
}
else
{
lean_dec_ref(v___y_2068_);
lean_dec(v_x_2066_);
return v___y_2069_;
}
}
v___jp_2079_:
{
if (v___y_2082_ == 0)
{
lean_object* v___x_2083_; uint8_t v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; lean_object* v___x_2090_; 
v___x_2083_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2084_ = 0;
v___x_2085_ = lean_box(v___x_2084_);
v___x_2086_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2083_, v___y_2080_, v___x_2085_);
lean_dec(v___x_2085_);
lean_dec_ref(v___y_2080_);
v___x_2087_ = lean_unsigned_to_nat(5u);
v___x_2088_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2088_, 0, v_x_2066_);
lean_ctor_set(v___x_2088_, 1, v___x_2087_);
v___x_2089_ = lean_unbox(v___x_2086_);
lean_dec(v___x_2086_);
lean_ctor_set_uint8(v___x_2088_, sizeof(void*)*2, v___x_2089_);
v___x_2090_ = lean_array_push(v___y_2081_, v___x_2088_);
return v___x_2090_;
}
else
{
lean_dec_ref(v___y_2080_);
lean_dec(v_x_2066_);
return v___y_2081_;
}
}
v___jp_2091_:
{
if (v___y_2094_ == 0)
{
lean_object* v___x_2095_; uint8_t v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; uint8_t v___x_2101_; lean_object* v___x_2102_; 
v___x_2095_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2096_ = 0;
v___x_2097_ = lean_box(v___x_2096_);
v___x_2098_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2095_, v___y_2092_, v___x_2097_);
lean_dec(v___x_2097_);
lean_dec_ref(v___y_2092_);
v___x_2099_ = lean_unsigned_to_nat(5u);
v___x_2100_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2100_, 0, v_x_2066_);
lean_ctor_set(v___x_2100_, 1, v___x_2099_);
v___x_2101_ = lean_unbox(v___x_2098_);
lean_dec(v___x_2098_);
lean_ctor_set_uint8(v___x_2100_, sizeof(void*)*2, v___x_2101_);
v___x_2102_ = lean_array_push(v___y_2093_, v___x_2100_);
return v___x_2102_;
}
else
{
lean_dec_ref(v___y_2092_);
lean_dec(v_x_2066_);
return v___y_2093_;
}
}
v___jp_2103_:
{
if (v___y_2106_ == 0)
{
lean_object* v___x_2107_; uint8_t v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; lean_object* v___x_2114_; 
v___x_2107_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2108_ = 0;
v___x_2109_ = lean_box(v___x_2108_);
v___x_2110_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2107_, v___y_2105_, v___x_2109_);
lean_dec(v___x_2109_);
lean_dec_ref(v___y_2105_);
v___x_2111_ = lean_unsigned_to_nat(5u);
v___x_2112_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2112_, 0, v_x_2066_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
v___x_2113_ = lean_unbox(v___x_2110_);
lean_dec(v___x_2110_);
lean_ctor_set_uint8(v___x_2112_, sizeof(void*)*2, v___x_2113_);
v___x_2114_ = lean_array_push(v___y_2104_, v___x_2112_);
return v___x_2114_;
}
else
{
lean_dec_ref(v___y_2105_);
lean_dec(v_x_2066_);
return v___y_2104_;
}
}
v___jp_2115_:
{
if (v___y_2121_ == 0)
{
v___y_2104_ = v___y_2118_;
v___y_2105_ = v___y_2120_;
v___y_2106_ = v___y_2116_;
goto v___jp_2103_;
}
else
{
if (v___y_2117_ == 0)
{
v___y_2104_ = v___y_2118_;
v___y_2105_ = v___y_2120_;
v___y_2106_ = v___y_2119_;
goto v___jp_2103_;
}
else
{
v___y_2104_ = v___y_2118_;
v___y_2105_ = v___y_2120_;
v___y_2106_ = v___y_2116_;
goto v___jp_2103_;
}
}
}
v___jp_2122_:
{
if (v___y_2127_ == 0)
{
v___y_2116_ = v___y_2123_;
v___y_2117_ = v___y_2128_;
v___y_2118_ = v___y_2124_;
v___y_2119_ = v___y_2125_;
v___y_2120_ = v___y_2126_;
v___y_2121_ = v___y_2125_;
goto v___jp_2115_;
}
else
{
v___y_2116_ = v___y_2123_;
v___y_2117_ = v___y_2128_;
v___y_2118_ = v___y_2124_;
v___y_2119_ = v___y_2125_;
v___y_2120_ = v___y_2126_;
v___y_2121_ = v___y_2123_;
goto v___jp_2115_;
}
}
v___jp_2129_:
{
uint32_t v___x_2136_; uint8_t v___x_2137_; 
v___x_2136_ = 95;
v___x_2137_ = lean_uint32_dec_eq(v___y_2134_, v___x_2136_);
if (v___x_2137_ == 0)
{
uint8_t v___x_2138_; 
v___x_2138_ = l_Lean_isLetterLike(v___y_2134_);
v___y_2123_ = v___y_2130_;
v___y_2124_ = v___y_2131_;
v___y_2125_ = v___y_2132_;
v___y_2126_ = v___y_2133_;
v___y_2127_ = v___y_2135_;
v___y_2128_ = v___x_2138_;
goto v___jp_2122_;
}
else
{
v___y_2123_ = v___y_2130_;
v___y_2124_ = v___y_2131_;
v___y_2125_ = v___y_2132_;
v___y_2126_ = v___y_2133_;
v___y_2127_ = v___y_2135_;
v___y_2128_ = v___x_2137_;
goto v___jp_2122_;
}
}
v___jp_2139_:
{
uint32_t v___x_2146_; uint8_t v___x_2147_; 
v___x_2146_ = 97;
v___x_2147_ = lean_uint32_dec_le(v___x_2146_, v___y_2144_);
if (v___x_2147_ == 0)
{
v___y_2130_ = v___y_2140_;
v___y_2131_ = v___y_2141_;
v___y_2132_ = v___y_2142_;
v___y_2133_ = v___y_2143_;
v___y_2134_ = v___y_2144_;
v___y_2135_ = v___y_2145_;
goto v___jp_2129_;
}
else
{
uint32_t v___x_2148_; uint8_t v___x_2149_; 
v___x_2148_ = 122;
v___x_2149_ = lean_uint32_dec_le(v___y_2144_, v___x_2148_);
if (v___x_2149_ == 0)
{
v___y_2130_ = v___y_2140_;
v___y_2131_ = v___y_2141_;
v___y_2132_ = v___y_2142_;
v___y_2133_ = v___y_2143_;
v___y_2134_ = v___y_2144_;
v___y_2135_ = v___y_2145_;
goto v___jp_2129_;
}
else
{
v___y_2123_ = v___y_2140_;
v___y_2124_ = v___y_2141_;
v___y_2125_ = v___y_2142_;
v___y_2126_ = v___y_2143_;
v___y_2127_ = v___y_2145_;
v___y_2128_ = v___x_2149_;
goto v___jp_2122_;
}
}
}
v___jp_2150_:
{
if (v___y_2153_ == 0)
{
lean_object* v___x_2154_; uint8_t v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; uint8_t v___x_2160_; lean_object* v___x_2161_; 
v___x_2154_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2155_ = 0;
v___x_2156_ = lean_box(v___x_2155_);
v___x_2157_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2154_, v___y_2151_, v___x_2156_);
lean_dec(v___x_2156_);
lean_dec_ref(v___y_2151_);
v___x_2158_ = lean_unsigned_to_nat(5u);
v___x_2159_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2159_, 0, v_x_2066_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = lean_unbox(v___x_2157_);
lean_dec(v___x_2157_);
lean_ctor_set_uint8(v___x_2159_, sizeof(void*)*2, v___x_2160_);
v___x_2161_ = lean_array_push(v___y_2152_, v___x_2159_);
return v___x_2161_;
}
else
{
lean_dec_ref(v___y_2151_);
lean_dec(v_x_2066_);
return v___y_2152_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(lean_object* v_text_2677_, size_t v_sz_2678_, size_t v_i_2679_, lean_object* v_bs_2680_){
_start:
{
uint8_t v___x_2681_; 
v___x_2681_ = lean_usize_dec_lt(v_i_2679_, v_sz_2678_);
if (v___x_2681_ == 0)
{
lean_dec_ref(v_text_2677_);
return v_bs_2680_;
}
else
{
lean_object* v_v_2682_; lean_object* v___x_2683_; lean_object* v_bs_x27_2684_; lean_object* v___x_2685_; size_t v___x_2686_; size_t v___x_2687_; lean_object* v___x_2688_; 
v_v_2682_ = lean_array_uget(v_bs_2680_, v_i_2679_);
v___x_2683_ = lean_unsigned_to_nat(0u);
v_bs_x27_2684_ = lean_array_uset(v_bs_2680_, v_i_2679_, v___x_2683_);
lean_inc_ref(v_text_2677_);
v___x_2685_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2677_, v_v_2682_);
v___x_2686_ = ((size_t)1ULL);
v___x_2687_ = lean_usize_add(v_i_2679_, v___x_2686_);
v___x_2688_ = lean_array_uset(v_bs_x27_2684_, v_i_2679_, v___x_2685_);
v_i_2679_ = v___x_2687_;
v_bs_2680_ = v___x_2688_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_text_2677_ = stack[0].m_obj;
size_t v_sz_2678_ = stack[1].m_num;
size_t v_i_2679_ = stack[2].m_num;
lean_object* v_bs_2680_ = stack[3].m_obj;
lean_object* v_res_2690_;
v_res_2690_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2677_, v_sz_2678_, v_i_2679_, v_bs_2680_);
stack->m_obj
 = v_res_2690_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3___boxed(lean_object* v_text_2691_, lean_object* v_sz_2692_, lean_object* v_i_2693_, lean_object* v_bs_2694_){
_start:
{
size_t v_sz_boxed_2695_; size_t v_i_boxed_2696_; lean_object* v_res_2697_; 
v_sz_boxed_2695_ = lean_unbox_usize(v_sz_2692_);
lean_dec(v_sz_2692_);
v_i_boxed_2696_ = lean_unbox_usize(v_i_2693_);
lean_dec(v_i_2693_);
v_res_2697_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2691_, v_sz_boxed_2695_, v_i_boxed_2696_, v_bs_2694_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(lean_object* v_00_u03b4_2698_, lean_object* v_t_2699_, lean_object* v_k_2700_, lean_object* v_fallback_2701_){
_start:
{
lean_object* v___x_2702_; 
v___x_2702_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v_t_2699_, v_k_2700_, v_fallback_2701_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___boxed(lean_object* v_00_u03b4_2703_, lean_object* v_t_2704_, lean_object* v_k_2705_, lean_object* v_fallback_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(v_00_u03b4_2703_, v_t_2704_, v_k_2705_, v_fallback_2706_);
lean_dec(v_fallback_2706_);
lean_dec_ref(v_k_2705_);
lean_dec(v_t_2704_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(lean_object* v_x_2708_, lean_object* v_info_2709_, lean_object* v_x_2710_){
_start:
{
if (lean_obj_tag(v_info_2709_) == 1)
{
lean_object* v_i_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2755_; 
v_i_2711_ = lean_ctor_get(v_info_2709_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v_info_2709_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2713_ = v_info_2709_;
v_isShared_2714_ = v_isSharedCheck_2755_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_i_2711_);
lean_dec(v_info_2709_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2755_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v_toElabInfo_2715_; lean_object* v_lctx_2716_; lean_object* v_expr_2717_; uint8_t v_isBinder_2718_; lean_object* v_stx_2719_; lean_object* v___x_2736_; 
v_toElabInfo_2715_ = lean_ctor_get(v_i_2711_, 0);
lean_inc_ref(v_toElabInfo_2715_);
v_lctx_2716_ = lean_ctor_get(v_i_2711_, 1);
lean_inc_ref(v_lctx_2716_);
v_expr_2717_ = lean_ctor_get(v_i_2711_, 3);
lean_inc_ref(v_expr_2717_);
v_isBinder_2718_ = lean_ctor_get_uint8(v_i_2711_, sizeof(void*)*4);
lean_dec_ref(v_i_2711_);
v_stx_2719_ = lean_ctor_get(v_toElabInfo_2715_, 1);
lean_inc(v_stx_2719_);
lean_dec_ref(v_toElabInfo_2715_);
v___x_2736_ = l_Lean_Syntax_getHeadInfo(v_stx_2719_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v___x_2737_; uint8_t v___x_2738_; 
lean_dec_ref_known(v___x_2736_, 4);
v___x_2737_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__10));
lean_inc(v_stx_2719_);
v___x_2738_ = l_Lean_Syntax_isOfKind(v_stx_2719_, v___x_2737_);
if (v___x_2738_ == 0)
{
lean_dec_ref(v_expr_2717_);
lean_dec_ref(v_lctx_2716_);
lean_del_object(v___x_2713_);
goto v___jp_2727_;
}
else
{
if (lean_obj_tag(v_expr_2717_) == 1)
{
lean_object* v_fvarId_2739_; lean_object* v___x_2740_; 
v_fvarId_2739_ = lean_ctor_get(v_expr_2717_, 0);
lean_inc(v_fvarId_2739_);
lean_dec_ref_known(v_expr_2717_, 1);
v___x_2740_ = lean_local_ctx_find(v_lctx_2716_, v_fvarId_2739_);
if (lean_obj_tag(v___x_2740_) == 1)
{
lean_object* v_val_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2753_; 
v_val_2741_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2743_ = v___x_2740_;
v_isShared_2744_ = v_isSharedCheck_2753_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_val_2741_);
lean_dec(v___x_2740_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2753_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
uint8_t v___x_2745_; 
v___x_2745_ = l_Lean_LocalDecl_isAuxDecl(v_val_2741_);
if (v___x_2745_ == 0)
{
uint8_t v___x_2746_; 
lean_del_object(v___x_2743_);
v___x_2746_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2741_);
lean_dec(v_val_2741_);
if (v___x_2746_ == 0)
{
goto v___jp_2720_;
}
else
{
if (v___x_2745_ == 0)
{
lean_del_object(v___x_2713_);
goto v___jp_2727_;
}
else
{
goto v___jp_2720_;
}
}
}
else
{
lean_dec(v_val_2741_);
lean_del_object(v___x_2713_);
if (v_isBinder_2718_ == 0)
{
lean_del_object(v___x_2743_);
goto v___jp_2727_;
}
else
{
uint8_t v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2751_; 
v___x_2747_ = 3;
v___x_2748_ = lean_unsigned_to_nat(5u);
v___x_2749_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2749_, 0, v_stx_2719_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
lean_ctor_set_uint8(v___x_2749_, sizeof(void*)*2, v___x_2747_);
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 0, v___x_2749_);
v___x_2751_ = v___x_2743_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v___x_2749_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
}
else
{
lean_dec(v___x_2740_);
lean_del_object(v___x_2713_);
goto v___jp_2727_;
}
}
else
{
lean_dec_ref(v_expr_2717_);
lean_dec_ref(v_lctx_2716_);
lean_del_object(v___x_2713_);
goto v___jp_2727_;
}
}
}
else
{
lean_object* v___x_2754_; 
lean_dec(v___x_2736_);
lean_dec(v_stx_2719_);
lean_dec_ref(v_expr_2717_);
lean_dec_ref(v_lctx_2716_);
lean_del_object(v___x_2713_);
v___x_2754_ = lean_box(0);
return v___x_2754_;
}
v___jp_2720_:
{
uint8_t v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2725_; 
v___x_2721_ = 1;
v___x_2722_ = lean_unsigned_to_nat(5u);
v___x_2723_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2723_, 0, v_stx_2719_);
lean_ctor_set(v___x_2723_, 1, v___x_2722_);
lean_ctor_set_uint8(v___x_2723_, sizeof(void*)*2, v___x_2721_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 0, v___x_2723_);
v___x_2725_ = v___x_2713_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2723_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
v___jp_2727_:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; uint8_t v___x_2730_; 
lean_inc(v_stx_2719_);
v___x_2728_ = l_Lean_Syntax_getKind(v_stx_2719_);
v___x_2729_ = l_Lean_Parser_Term_identProjKind;
v___x_2730_ = lean_name_eq(v___x_2728_, v___x_2729_);
lean_dec(v___x_2728_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2731_; 
lean_dec(v_stx_2719_);
v___x_2731_ = lean_box(0);
return v___x_2731_;
}
else
{
uint8_t v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2732_ = 2;
v___x_2733_ = lean_unsigned_to_nat(5u);
v___x_2734_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2734_, 0, v_stx_2719_);
lean_ctor_set(v___x_2734_, 1, v___x_2733_);
lean_ctor_set_uint8(v___x_2734_, sizeof(void*)*2, v___x_2732_);
v___x_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2734_);
return v___x_2735_;
}
}
}
}
else
{
lean_object* v___x_2756_; 
lean_dec_ref(v_info_2709_);
v___x_2756_ = lean_box(0);
return v___x_2756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0___boxed(lean_object* v_x_2757_, lean_object* v_info_2758_, lean_object* v_x_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(v_x_2757_, v_info_2758_, v_x_2759_);
lean_dec_ref(v_x_2759_);
lean_dec_ref(v_x_2757_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(lean_object* v_i_2762_){
_start:
{
lean_object* v___f_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___f_2763_ = ((lean_object*)(l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___closed__0));
v___x_2764_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_2763_, v_i_2762_);
v___x_2765_ = lean_array_mk(v___x_2764_);
return v___x_2765_;
}
}
uint8_t l_Lean_Server_FileWorker_dbgShowTokens___lam__0(lean_object* v_x_2766_, lean_object* v_y_2767_){
_start:
{
lean_object* v_fst_2768_; lean_object* v_fst_2769_; uint8_t v___x_2770_; 
v_fst_2768_ = lean_ctor_get(v_x_2766_, 0);
v_fst_2769_ = lean_ctor_get(v_y_2767_, 0);
v___x_2770_ = lean_nat_dec_le(v_fst_2768_, v_fst_2769_);
return v___x_2770_;
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_dbgShowTokens___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2766_ = stack[0].m_obj;
lean_object* v_y_2767_ = stack[1].m_obj;
uint8_t v_res_2771_;
v_res_2771_ = l_Lean_Server_FileWorker_dbgShowTokens___lam__0(v_x_2766_, v_y_2767_);
stack->m_num = v_res_2771_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___lam__0___boxed(lean_object* v_x_2772_, lean_object* v_y_2773_){
_start:
{
uint8_t v_res_2774_; lean_object* v_r_2775_; 
v_res_2774_ = l_Lean_Server_FileWorker_dbgShowTokens___lam__0(v_x_2772_, v_y_2773_);
lean_dec_ref(v_y_2773_);
lean_dec_ref(v_x_2772_);
v_r_2775_ = lean_box(v_res_2774_);
return v_r_2775_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(lean_object* v_x_2776_, lean_object* v_x_2777_){
_start:
{
if (lean_obj_tag(v_x_2777_) == 0)
{
lean_inc(v_x_2776_);
return v_x_2776_;
}
else
{
lean_object* v_key_2778_; lean_object* v_value_2779_; lean_object* v_tail_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v_key_2778_ = lean_ctor_get(v_x_2777_, 0);
v_value_2779_ = lean_ctor_get(v_x_2777_, 1);
v_tail_2780_ = lean_ctor_get(v_x_2777_, 2);
v___x_2781_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_2776_, v_tail_2780_);
lean_inc(v_value_2779_);
lean_inc(v_key_2778_);
v___x_2782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2782_, 0, v_key_2778_);
lean_ctor_set(v___x_2782_, 1, v_value_2779_);
v___x_2783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2782_);
lean_ctor_set(v___x_2783_, 1, v___x_2781_);
return v___x_2783_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5___boxed(lean_object* v_x_2784_, lean_object* v_x_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_2784_, v_x_2785_);
lean_dec(v_x_2785_);
lean_dec(v_x_2784_);
return v_res_2786_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(lean_object* v_as_2787_, size_t v_i_2788_, size_t v_stop_2789_, lean_object* v_b_2790_){
_start:
{
uint8_t v___x_2791_; 
v___x_2791_ = lean_usize_dec_eq(v_i_2788_, v_stop_2789_);
if (v___x_2791_ == 0)
{
size_t v___x_2792_; size_t v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2792_ = ((size_t)1ULL);
v___x_2793_ = lean_usize_sub(v_i_2788_, v___x_2792_);
v___x_2794_ = lean_array_uget_borrowed(v_as_2787_, v___x_2793_);
v___x_2795_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_b_2790_, v___x_2794_);
lean_dec(v_b_2790_);
v_i_2788_ = v___x_2793_;
v_b_2790_ = v___x_2795_;
goto _start;
}
else
{
return v_b_2790_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2787_ = stack[0].m_obj;
size_t v_i_2788_ = stack[1].m_num;
size_t v_stop_2789_ = stack[2].m_num;
lean_object* v_b_2790_ = stack[3].m_obj;
lean_object* v_res_2797_;
v_res_2797_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_as_2787_, v_i_2788_, v_stop_2789_, v_b_2790_);
stack->m_obj
 = v_res_2797_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6___boxed(lean_object* v_as_2798_, lean_object* v_i_2799_, lean_object* v_stop_2800_, lean_object* v_b_2801_){
_start:
{
size_t v_i_boxed_2802_; size_t v_stop_boxed_2803_; lean_object* v_res_2804_; 
v_i_boxed_2802_ = lean_unbox_usize(v_i_2799_);
lean_dec(v_i_2799_);
v_stop_boxed_2803_ = lean_unbox_usize(v_stop_2800_);
lean_dec(v_stop_2800_);
v_res_2804_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_as_2798_, v_i_boxed_2802_, v_stop_boxed_2803_, v_b_2801_);
lean_dec_ref(v_as_2798_);
return v_res_2804_;
}
}
uint8_t l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(lean_object* v_x_2805_, lean_object* v_y_2806_){
_start:
{
lean_object* v_fst_2807_; lean_object* v_fst_2808_; uint8_t v___x_2809_; 
v_fst_2807_ = lean_ctor_get(v_x_2805_, 0);
v_fst_2808_ = lean_ctor_get(v_y_2806_, 0);
v___x_2809_ = lean_nat_dec_le(v_fst_2807_, v_fst_2808_);
return v___x_2809_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2805_ = stack[0].m_obj;
lean_object* v_y_2806_ = stack[1].m_obj;
uint8_t v_res_2810_;
v_res_2810_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(v_x_2805_, v_y_2806_);
stack->m_num = v_res_2810_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0___boxed(lean_object* v_x_2811_, lean_object* v_y_2812_){
_start:
{
uint8_t v_res_2813_; lean_object* v_r_2814_; 
v_res_2813_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(v_x_2811_, v_y_2812_);
lean_dec_ref(v_y_2812_);
lean_dec_ref(v_x_2811_);
v_r_2814_ = lean_box(v_res_2813_);
return v_r_2814_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(lean_object* v_x_2818_, lean_object* v_x_2819_){
_start:
{
if (lean_obj_tag(v_x_2819_) == 0)
{
return v_x_2818_;
}
else
{
lean_object* v_head_2820_; lean_object* v_snd_2821_; lean_object* v_snd_2822_; lean_object* v_tail_2823_; lean_object* v_fst_2824_; lean_object* v_fst_2825_; lean_object* v_fst_2826_; lean_object* v_snd_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; uint8_t v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v_fst_2837_; lean_object* v_snd_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v_head_2820_ = lean_ctor_get(v_x_2819_, 0);
lean_inc(v_head_2820_);
v_snd_2821_ = lean_ctor_get(v_head_2820_, 1);
lean_inc(v_snd_2821_);
v_snd_2822_ = lean_ctor_get(v_snd_2821_, 1);
lean_inc(v_snd_2822_);
v_tail_2823_ = lean_ctor_get(v_x_2819_, 1);
lean_inc(v_tail_2823_);
lean_dec_ref_known(v_x_2819_, 2);
v_fst_2824_ = lean_ctor_get(v_head_2820_, 0);
lean_inc(v_fst_2824_);
lean_dec(v_head_2820_);
v_fst_2825_ = lean_ctor_get(v_snd_2821_, 0);
lean_inc(v_fst_2825_);
lean_dec(v_snd_2821_);
v_fst_2826_ = lean_ctor_get(v_snd_2822_, 0);
lean_inc(v_fst_2826_);
v_snd_2827_ = lean_ctor_get(v_snd_2822_, 1);
lean_inc(v_snd_2827_);
lean_dec(v_snd_2822_);
v___x_2828_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_2829_ = l_Nat_reprFast(v_fst_2824_);
v___x_2830_ = lean_string_append(v___x_2828_, v___x_2829_);
lean_dec_ref(v___x_2829_);
v___x_2831_ = lean_box(0);
v___x_2832_ = 0;
v___x_2833_ = l_Lean_Syntax_formatStx(v_fst_2826_, v___x_2831_, v___x_2832_);
v___x_2834_ = l_Std_Format_defWidth;
v___x_2835_ = lean_unsigned_to_nat(0u);
v___x_2836_ = l_Std_Format_pretty(v___x_2833_, v___x_2834_, v___x_2835_, v___x_2835_);
v_fst_2837_ = lean_ctor_get(v_snd_2827_, 0);
lean_inc(v_fst_2837_);
v_snd_2838_ = lean_ctor_get(v_snd_2827_, 1);
lean_inc(v_snd_2838_);
lean_dec(v_snd_2827_);
v___x_2839_ = l_Nat_reprFast(v_fst_2825_);
v___x_2840_ = lean_string_append(v___x_2828_, v___x_2839_);
lean_dec_ref(v___x_2839_);
v___x_2841_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_2842_ = lean_string_append(v_x_2818_, v___x_2841_);
v___x_2843_ = lean_string_append(v___x_2830_, v___x_2841_);
v___x_2844_ = lean_string_append(v___x_2840_, v___x_2841_);
v___x_2845_ = lean_string_append(v___x_2828_, v___x_2836_);
lean_dec_ref(v___x_2836_);
v___x_2846_ = lean_string_append(v___x_2845_, v___x_2841_);
v___x_2847_ = lean_unsigned_to_nat(80u);
v___x_2848_ = l_Lean_Json_pretty(v_fst_2837_, v___x_2847_);
v___x_2849_ = lean_string_append(v___x_2828_, v___x_2848_);
lean_dec_ref(v___x_2848_);
v___x_2850_ = lean_string_append(v___x_2849_, v___x_2841_);
v___x_2851_ = l_Nat_reprFast(v_snd_2838_);
v___x_2852_ = lean_string_append(v___x_2850_, v___x_2851_);
lean_dec_ref(v___x_2851_);
v___x_2853_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_2854_ = lean_string_append(v___x_2852_, v___x_2853_);
v___x_2855_ = lean_string_append(v___x_2846_, v___x_2854_);
lean_dec_ref(v___x_2854_);
v___x_2856_ = lean_string_append(v___x_2855_, v___x_2853_);
v___x_2857_ = lean_string_append(v___x_2844_, v___x_2856_);
lean_dec_ref(v___x_2856_);
v___x_2858_ = lean_string_append(v___x_2857_, v___x_2853_);
v___x_2859_ = lean_string_append(v___x_2843_, v___x_2858_);
lean_dec_ref(v___x_2858_);
v___x_2860_ = lean_string_append(v___x_2859_, v___x_2853_);
v___x_2861_ = lean_string_append(v___x_2842_, v___x_2860_);
lean_dec_ref(v___x_2860_);
v_x_2818_ = v___x_2861_;
v_x_2819_ = v_tail_2823_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(lean_object* v_x_2866_){
_start:
{
if (lean_obj_tag(v_x_2866_) == 0)
{
lean_object* v___x_2867_; 
v___x_2867_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__0));
return v___x_2867_;
}
else
{
lean_object* v_tail_2868_; 
v_tail_2868_ = lean_ctor_get(v_x_2866_, 1);
if (lean_obj_tag(v_tail_2868_) == 0)
{
lean_object* v_head_2869_; lean_object* v_snd_2870_; lean_object* v_snd_2871_; lean_object* v_fst_2872_; lean_object* v_fst_2873_; lean_object* v_fst_2874_; lean_object* v_snd_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; uint8_t v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v_fst_2885_; lean_object* v_snd_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v_head_2869_ = lean_ctor_get(v_x_2866_, 0);
lean_inc(v_head_2869_);
lean_dec_ref_known(v_x_2866_, 2);
v_snd_2870_ = lean_ctor_get(v_head_2869_, 1);
lean_inc(v_snd_2870_);
v_snd_2871_ = lean_ctor_get(v_snd_2870_, 1);
lean_inc(v_snd_2871_);
v_fst_2872_ = lean_ctor_get(v_head_2869_, 0);
lean_inc(v_fst_2872_);
lean_dec(v_head_2869_);
v_fst_2873_ = lean_ctor_get(v_snd_2870_, 0);
lean_inc(v_fst_2873_);
lean_dec(v_snd_2870_);
v_fst_2874_ = lean_ctor_get(v_snd_2871_, 0);
lean_inc(v_fst_2874_);
v_snd_2875_ = lean_ctor_get(v_snd_2871_, 1);
lean_inc(v_snd_2875_);
lean_dec(v_snd_2871_);
v___x_2876_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_2877_ = l_Nat_reprFast(v_fst_2872_);
v___x_2878_ = lean_string_append(v___x_2876_, v___x_2877_);
lean_dec_ref(v___x_2877_);
v___x_2879_ = lean_box(0);
v___x_2880_ = 0;
v___x_2881_ = l_Lean_Syntax_formatStx(v_fst_2874_, v___x_2879_, v___x_2880_);
v___x_2882_ = l_Std_Format_defWidth;
v___x_2883_ = lean_unsigned_to_nat(0u);
v___x_2884_ = l_Std_Format_pretty(v___x_2881_, v___x_2882_, v___x_2883_, v___x_2883_);
v_fst_2885_ = lean_ctor_get(v_snd_2875_, 0);
lean_inc(v_fst_2885_);
v_snd_2886_ = lean_ctor_get(v_snd_2875_, 1);
lean_inc(v_snd_2886_);
lean_dec(v_snd_2875_);
v___x_2887_ = l_Nat_reprFast(v_fst_2873_);
v___x_2888_ = lean_string_append(v___x_2876_, v___x_2887_);
lean_dec_ref(v___x_2887_);
v___x_2889_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_2890_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_2891_ = lean_string_append(v___x_2878_, v___x_2890_);
v___x_2892_ = lean_string_append(v___x_2888_, v___x_2890_);
v___x_2893_ = lean_string_append(v___x_2876_, v___x_2884_);
lean_dec_ref(v___x_2884_);
v___x_2894_ = lean_string_append(v___x_2893_, v___x_2890_);
v___x_2895_ = lean_unsigned_to_nat(80u);
v___x_2896_ = l_Lean_Json_pretty(v_fst_2885_, v___x_2895_);
v___x_2897_ = lean_string_append(v___x_2876_, v___x_2896_);
lean_dec_ref(v___x_2896_);
v___x_2898_ = lean_string_append(v___x_2897_, v___x_2890_);
v___x_2899_ = l_Nat_reprFast(v_snd_2886_);
v___x_2900_ = lean_string_append(v___x_2898_, v___x_2899_);
lean_dec_ref(v___x_2899_);
v___x_2901_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_2902_ = lean_string_append(v___x_2900_, v___x_2901_);
v___x_2903_ = lean_string_append(v___x_2894_, v___x_2902_);
lean_dec_ref(v___x_2902_);
v___x_2904_ = lean_string_append(v___x_2903_, v___x_2901_);
v___x_2905_ = lean_string_append(v___x_2892_, v___x_2904_);
lean_dec_ref(v___x_2904_);
v___x_2906_ = lean_string_append(v___x_2905_, v___x_2901_);
v___x_2907_ = lean_string_append(v___x_2891_, v___x_2906_);
lean_dec_ref(v___x_2906_);
v___x_2908_ = lean_string_append(v___x_2907_, v___x_2901_);
v___x_2909_ = lean_string_append(v___x_2889_, v___x_2908_);
lean_dec_ref(v___x_2908_);
v___x_2910_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__2));
v___x_2911_ = lean_string_append(v___x_2909_, v___x_2910_);
return v___x_2911_;
}
else
{
lean_object* v_head_2912_; lean_object* v_snd_2913_; lean_object* v_snd_2914_; lean_object* v_fst_2915_; lean_object* v_fst_2916_; lean_object* v_fst_2917_; lean_object* v_snd_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; uint8_t v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v_fst_2928_; lean_object* v_snd_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; uint32_t v___x_2954_; lean_object* v___x_2955_; 
lean_inc(v_tail_2868_);
v_head_2912_ = lean_ctor_get(v_x_2866_, 0);
lean_inc(v_head_2912_);
lean_dec_ref_known(v_x_2866_, 2);
v_snd_2913_ = lean_ctor_get(v_head_2912_, 1);
lean_inc(v_snd_2913_);
v_snd_2914_ = lean_ctor_get(v_snd_2913_, 1);
lean_inc(v_snd_2914_);
v_fst_2915_ = lean_ctor_get(v_head_2912_, 0);
lean_inc(v_fst_2915_);
lean_dec(v_head_2912_);
v_fst_2916_ = lean_ctor_get(v_snd_2913_, 0);
lean_inc(v_fst_2916_);
lean_dec(v_snd_2913_);
v_fst_2917_ = lean_ctor_get(v_snd_2914_, 0);
lean_inc(v_fst_2917_);
v_snd_2918_ = lean_ctor_get(v_snd_2914_, 1);
lean_inc(v_snd_2918_);
lean_dec(v_snd_2914_);
v___x_2919_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_2920_ = l_Nat_reprFast(v_fst_2915_);
v___x_2921_ = lean_string_append(v___x_2919_, v___x_2920_);
lean_dec_ref(v___x_2920_);
v___x_2922_ = lean_box(0);
v___x_2923_ = 0;
v___x_2924_ = l_Lean_Syntax_formatStx(v_fst_2917_, v___x_2922_, v___x_2923_);
v___x_2925_ = l_Std_Format_defWidth;
v___x_2926_ = lean_unsigned_to_nat(0u);
v___x_2927_ = l_Std_Format_pretty(v___x_2924_, v___x_2925_, v___x_2926_, v___x_2926_);
v_fst_2928_ = lean_ctor_get(v_snd_2918_, 0);
lean_inc(v_fst_2928_);
v_snd_2929_ = lean_ctor_get(v_snd_2918_, 1);
lean_inc(v_snd_2929_);
lean_dec(v_snd_2918_);
v___x_2930_ = l_Nat_reprFast(v_fst_2916_);
v___x_2931_ = lean_string_append(v___x_2919_, v___x_2930_);
lean_dec_ref(v___x_2930_);
v___x_2932_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_2933_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_2934_ = lean_string_append(v___x_2921_, v___x_2933_);
v___x_2935_ = lean_string_append(v___x_2931_, v___x_2933_);
v___x_2936_ = lean_string_append(v___x_2919_, v___x_2927_);
lean_dec_ref(v___x_2927_);
v___x_2937_ = lean_string_append(v___x_2936_, v___x_2933_);
v___x_2938_ = lean_unsigned_to_nat(80u);
v___x_2939_ = l_Lean_Json_pretty(v_fst_2928_, v___x_2938_);
v___x_2940_ = lean_string_append(v___x_2919_, v___x_2939_);
lean_dec_ref(v___x_2939_);
v___x_2941_ = lean_string_append(v___x_2940_, v___x_2933_);
v___x_2942_ = l_Nat_reprFast(v_snd_2929_);
v___x_2943_ = lean_string_append(v___x_2941_, v___x_2942_);
lean_dec_ref(v___x_2942_);
v___x_2944_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_2945_ = lean_string_append(v___x_2943_, v___x_2944_);
v___x_2946_ = lean_string_append(v___x_2937_, v___x_2945_);
lean_dec_ref(v___x_2945_);
v___x_2947_ = lean_string_append(v___x_2946_, v___x_2944_);
v___x_2948_ = lean_string_append(v___x_2935_, v___x_2947_);
lean_dec_ref(v___x_2947_);
v___x_2949_ = lean_string_append(v___x_2948_, v___x_2944_);
v___x_2950_ = lean_string_append(v___x_2934_, v___x_2949_);
lean_dec_ref(v___x_2949_);
v___x_2951_ = lean_string_append(v___x_2950_, v___x_2944_);
v___x_2952_ = lean_string_append(v___x_2932_, v___x_2951_);
lean_dec_ref(v___x_2951_);
v___x_2953_ = l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(v___x_2952_, v_tail_2868_);
v___x_2954_ = 93;
v___x_2955_ = lean_string_push(v___x_2953_, v___x_2954_);
return v___x_2955_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(lean_object* v_a_2956_, lean_object* v_a_2957_){
_start:
{
if (lean_obj_tag(v_a_2956_) == 0)
{
lean_object* v___x_2958_; 
v___x_2958_ = l_List_reverse___redArg(v_a_2957_);
return v___x_2958_;
}
else
{
lean_object* v_head_2959_; lean_object* v_snd_2960_; lean_object* v_snd_2961_; lean_object* v_tail_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2994_; 
v_head_2959_ = lean_ctor_get(v_a_2956_, 0);
lean_inc(v_head_2959_);
v_snd_2960_ = lean_ctor_get(v_head_2959_, 1);
lean_inc(v_snd_2960_);
v_snd_2961_ = lean_ctor_get(v_snd_2960_, 1);
lean_inc(v_snd_2961_);
v_tail_2962_ = lean_ctor_get(v_a_2956_, 1);
v_isSharedCheck_2994_ = !lean_is_exclusive(v_a_2956_);
if (v_isSharedCheck_2994_ == 0)
{
lean_object* v_unused_2995_; 
v_unused_2995_ = lean_ctor_get(v_a_2956_, 0);
lean_dec(v_unused_2995_);
v___x_2964_ = v_a_2956_;
v_isShared_2965_ = v_isSharedCheck_2994_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_tail_2962_);
lean_dec(v_a_2956_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2994_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v_fst_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2992_; 
v_fst_2966_ = lean_ctor_get(v_head_2959_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v_head_2959_);
if (v_isSharedCheck_2992_ == 0)
{
lean_object* v_unused_2993_; 
v_unused_2993_ = lean_ctor_get(v_head_2959_, 1);
lean_dec(v_unused_2993_);
v___x_2968_ = v_head_2959_;
v_isShared_2969_ = v_isSharedCheck_2992_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_fst_2966_);
lean_dec(v_head_2959_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2992_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v_fst_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2990_; 
v_fst_2970_ = lean_ctor_get(v_snd_2960_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v_snd_2960_);
if (v_isSharedCheck_2990_ == 0)
{
lean_object* v_unused_2991_; 
v_unused_2991_ = lean_ctor_get(v_snd_2960_, 1);
lean_dec(v_unused_2991_);
v___x_2972_ = v_snd_2960_;
v_isShared_2973_ = v_isSharedCheck_2990_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_fst_2970_);
lean_dec(v_snd_2960_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2990_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v_stx_2974_; uint8_t v_type_2975_; lean_object* v_priority_2976_; lean_object* v___x_2977_; lean_object* v___x_2979_; 
v_stx_2974_ = lean_ctor_get(v_snd_2961_, 0);
lean_inc(v_stx_2974_);
v_type_2975_ = lean_ctor_get_uint8(v_snd_2961_, sizeof(void*)*2);
v_priority_2976_ = lean_ctor_get(v_snd_2961_, 1);
lean_inc(v_priority_2976_);
lean_dec(v_snd_2961_);
v___x_2977_ = l_Lean_Lsp_instToJsonSemanticTokenType_toJson(v_type_2975_);
if (v_isShared_2973_ == 0)
{
lean_ctor_set(v___x_2972_, 1, v_priority_2976_);
lean_ctor_set(v___x_2972_, 0, v___x_2977_);
v___x_2979_ = v___x_2972_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v___x_2977_);
lean_ctor_set(v_reuseFailAlloc_2989_, 1, v_priority_2976_);
v___x_2979_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
lean_object* v___x_2981_; 
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 1, v___x_2979_);
lean_ctor_set(v___x_2968_, 0, v_stx_2974_);
v___x_2981_ = v___x_2968_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_stx_2974_);
lean_ctor_set(v_reuseFailAlloc_2988_, 1, v___x_2979_);
v___x_2981_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2985_; 
v___x_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2982_, 0, v_fst_2970_);
lean_ctor_set(v___x_2982_, 1, v___x_2981_);
v___x_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2983_, 0, v_fst_2966_);
lean_ctor_set(v___x_2983_, 1, v___x_2982_);
if (v_isShared_2965_ == 0)
{
lean_ctor_set(v___x_2964_, 1, v_a_2957_);
lean_ctor_set(v___x_2964_, 0, v___x_2983_);
v___x_2985_ = v___x_2964_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2983_);
lean_ctor_set(v_reuseFailAlloc_2987_, 1, v_a_2957_);
v___x_2985_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
v_a_2956_ = v_tail_2962_;
v_a_2957_ = v___x_2985_;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(lean_object* v_as_x27_2998_, lean_object* v_b_2999_){
_start:
{
if (lean_obj_tag(v_as_x27_2998_) == 0)
{
return v_b_2999_;
}
else
{
lean_object* v_head_3000_; lean_object* v_tail_3001_; lean_object* v_fst_3002_; lean_object* v_snd_3003_; lean_object* v___f_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v_head_3000_ = lean_ctor_get(v_as_x27_2998_, 0);
v_tail_3001_ = lean_ctor_get(v_as_x27_2998_, 1);
v_fst_3002_ = lean_ctor_get(v_head_3000_, 0);
v_snd_3003_ = lean_ctor_get(v_head_3000_, 1);
v___f_3004_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__0));
lean_inc(v_snd_3003_);
v___x_3005_ = lean_array_to_list(v_snd_3003_);
v___x_3006_ = l_List_mergeSort___redArg(v___x_3005_, v___f_3004_);
lean_inc(v_fst_3002_);
v___x_3007_ = l_Nat_reprFast(v_fst_3002_);
v___x_3008_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__1));
v___x_3009_ = lean_string_append(v___x_3007_, v___x_3008_);
v___x_3010_ = lean_box(0);
v___x_3011_ = l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(v___x_3006_, v___x_3010_);
v___x_3012_ = l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(v___x_3011_);
v___x_3013_ = lean_string_append(v___x_3009_, v___x_3012_);
lean_dec_ref(v___x_3012_);
v___x_3014_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0));
v___x_3015_ = lean_string_append(v___x_3013_, v___x_3014_);
v___x_3016_ = lean_string_append(v_b_2999_, v___x_3015_);
lean_dec_ref(v___x_3015_);
v_as_x27_2998_ = v_tail_3001_;
v_b_2999_ = v___x_3016_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___boxed(lean_object* v_as_x27_3018_, lean_object* v_b_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v_as_x27_3018_, v_b_3019_);
lean_dec(v_as_x27_3018_);
return v_res_3020_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(lean_object* v_a_3021_, lean_object* v_x_3022_){
_start:
{
if (lean_obj_tag(v_x_3022_) == 0)
{
uint8_t v___x_3023_; 
v___x_3023_ = 0;
return v___x_3023_;
}
else
{
lean_object* v_key_3024_; lean_object* v_tail_3025_; uint8_t v___x_3026_; 
v_key_3024_ = lean_ctor_get(v_x_3022_, 0);
v_tail_3025_ = lean_ctor_get(v_x_3022_, 2);
v___x_3026_ = lean_nat_dec_eq(v_key_3024_, v_a_3021_);
if (v___x_3026_ == 0)
{
v_x_3022_ = v_tail_3025_;
goto _start;
}
else
{
return v___x_3026_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3021_ = stack[0].m_obj;
lean_object* v_x_3022_ = stack[1].m_obj;
uint8_t v_res_3028_;
v_res_3028_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3021_, v_x_3022_);
stack->m_num = v_res_3028_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg___boxed(lean_object* v_a_3029_, lean_object* v_x_3030_){
_start:
{
uint8_t v_res_3031_; lean_object* v_r_3032_; 
v_res_3031_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3029_, v_x_3030_);
lean_dec(v_x_3030_);
lean_dec(v_a_3029_);
v_r_3032_ = lean_box(v_res_3031_);
return v_r_3032_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(lean_object* v_x_3033_, lean_object* v_x_3034_){
_start:
{
if (lean_obj_tag(v_x_3034_) == 0)
{
return v_x_3033_;
}
else
{
lean_object* v_key_3035_; lean_object* v_value_3036_; lean_object* v_tail_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3060_; 
v_key_3035_ = lean_ctor_get(v_x_3034_, 0);
v_value_3036_ = lean_ctor_get(v_x_3034_, 1);
v_tail_3037_ = lean_ctor_get(v_x_3034_, 2);
v_isSharedCheck_3060_ = !lean_is_exclusive(v_x_3034_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3039_ = v_x_3034_;
v_isShared_3040_ = v_isSharedCheck_3060_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_tail_3037_);
lean_inc(v_value_3036_);
lean_inc(v_key_3035_);
lean_dec(v_x_3034_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3060_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3041_; uint64_t v___x_3042_; uint64_t v___x_3043_; uint64_t v___x_3044_; uint64_t v_fold_3045_; uint64_t v___x_3046_; uint64_t v___x_3047_; uint64_t v___x_3048_; size_t v___x_3049_; size_t v___x_3050_; size_t v___x_3051_; size_t v___x_3052_; size_t v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3056_; 
v___x_3041_ = lean_array_get_size(v_x_3033_);
v___x_3042_ = lean_uint64_of_nat(v_key_3035_);
v___x_3043_ = 32ULL;
v___x_3044_ = lean_uint64_shift_right(v___x_3042_, v___x_3043_);
v_fold_3045_ = lean_uint64_xor(v___x_3042_, v___x_3044_);
v___x_3046_ = 16ULL;
v___x_3047_ = lean_uint64_shift_right(v_fold_3045_, v___x_3046_);
v___x_3048_ = lean_uint64_xor(v_fold_3045_, v___x_3047_);
v___x_3049_ = lean_uint64_to_usize(v___x_3048_);
v___x_3050_ = lean_usize_of_nat(v___x_3041_);
v___x_3051_ = ((size_t)1ULL);
v___x_3052_ = lean_usize_sub(v___x_3050_, v___x_3051_);
v___x_3053_ = lean_usize_land(v___x_3049_, v___x_3052_);
v___x_3054_ = lean_array_uget_borrowed(v_x_3033_, v___x_3053_);
lean_inc(v___x_3054_);
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 2, v___x_3054_);
v___x_3056_ = v___x_3039_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_key_3035_);
lean_ctor_set(v_reuseFailAlloc_3059_, 1, v_value_3036_);
lean_ctor_set(v_reuseFailAlloc_3059_, 2, v___x_3054_);
v___x_3056_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
lean_object* v___x_3057_; 
v___x_3057_ = lean_array_uset(v_x_3033_, v___x_3053_, v___x_3056_);
v_x_3033_ = v___x_3057_;
v_x_3034_ = v_tail_3037_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(lean_object* v_i_3061_, lean_object* v_source_3062_, lean_object* v_target_3063_){
_start:
{
lean_object* v___x_3064_; uint8_t v___x_3065_; 
v___x_3064_ = lean_array_get_size(v_source_3062_);
v___x_3065_ = lean_nat_dec_lt(v_i_3061_, v___x_3064_);
if (v___x_3065_ == 0)
{
lean_dec_ref(v_source_3062_);
lean_dec(v_i_3061_);
return v_target_3063_;
}
else
{
lean_object* v_es_3066_; lean_object* v___x_3067_; lean_object* v_source_3068_; lean_object* v_target_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v_es_3066_ = lean_array_fget(v_source_3062_, v_i_3061_);
v___x_3067_ = lean_box(0);
v_source_3068_ = lean_array_fset(v_source_3062_, v_i_3061_, v___x_3067_);
v_target_3069_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_target_3063_, v_es_3066_);
v___x_3070_ = lean_unsigned_to_nat(1u);
v___x_3071_ = lean_nat_add(v_i_3061_, v___x_3070_);
lean_dec(v_i_3061_);
v_i_3061_ = v___x_3071_;
v_source_3062_ = v_source_3068_;
v_target_3063_ = v_target_3069_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(lean_object* v_data_3073_){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v_nbuckets_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3074_ = lean_array_get_size(v_data_3073_);
v___x_3075_ = lean_unsigned_to_nat(2u);
v_nbuckets_3076_ = lean_nat_mul(v___x_3074_, v___x_3075_);
v___x_3077_ = lean_unsigned_to_nat(0u);
v___x_3078_ = lean_box(0);
v___x_3079_ = lean_mk_array(v_nbuckets_3076_, v___x_3078_);
v___x_3080_ = lean_array_propagate_mark(v_data_3073_, v___x_3079_);
v___x_3081_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v___x_3077_, v_data_3073_, v___x_3080_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(lean_object* v_character_3084_, lean_object* v_a_3085_, lean_object* v_character_3086_, lean_object* v_x_x3f_3087_){
_start:
{
lean_object* v___y_3089_; 
if (lean_obj_tag(v_x_x3f_3087_) == 0)
{
lean_object* v___x_3094_; 
v___x_3094_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___y_3089_ = v___x_3094_;
goto v___jp_3088_;
}
else
{
lean_object* v_val_3095_; 
v_val_3095_ = lean_ctor_get(v_x_x3f_3087_, 0);
lean_inc(v_val_3095_);
lean_dec_ref_known(v_x_x3f_3087_, 1);
v___y_3089_ = v_val_3095_;
goto v___jp_3088_;
}
v___jp_3088_:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3090_, 0, v_character_3084_);
lean_ctor_set(v___x_3090_, 1, v_a_3085_);
v___x_3091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3091_, 0, v_character_3086_);
lean_ctor_set(v___x_3091_, 1, v___x_3090_);
v___x_3092_ = lean_array_push(v___y_3089_, v___x_3091_);
v___x_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3092_);
return v___x_3093_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(lean_object* v_character_3096_, lean_object* v_a_3097_, lean_object* v_character_3098_, lean_object* v_a_3099_, lean_object* v_x_3100_){
_start:
{
if (lean_obj_tag(v_x_3100_) == 0)
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v_val_3103_; lean_object* v___x_3104_; 
v___x_3101_ = lean_box(0);
v___x_3102_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_3096_, v_a_3097_, v_character_3098_, v___x_3101_);
v_val_3103_ = lean_ctor_get(v___x_3102_, 0);
lean_inc(v_val_3103_);
lean_dec(v___x_3102_);
v___x_3104_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3104_, 0, v_a_3099_);
lean_ctor_set(v___x_3104_, 1, v_val_3103_);
lean_ctor_set(v___x_3104_, 2, v_x_3100_);
return v___x_3104_;
}
else
{
lean_object* v_key_3105_; lean_object* v_value_3106_; lean_object* v_tail_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3122_; 
v_key_3105_ = lean_ctor_get(v_x_3100_, 0);
v_value_3106_ = lean_ctor_get(v_x_3100_, 1);
v_tail_3107_ = lean_ctor_get(v_x_3100_, 2);
v_isSharedCheck_3122_ = !lean_is_exclusive(v_x_3100_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3109_ = v_x_3100_;
v_isShared_3110_ = v_isSharedCheck_3122_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_tail_3107_);
lean_inc(v_value_3106_);
lean_inc(v_key_3105_);
lean_dec(v_x_3100_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3122_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
uint8_t v___x_3111_; 
v___x_3111_ = lean_nat_dec_eq(v_key_3105_, v_a_3099_);
if (v___x_3111_ == 0)
{
lean_object* v_tail_3112_; lean_object* v___x_3114_; 
v_tail_3112_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_3096_, v_a_3097_, v_character_3098_, v_a_3099_, v_tail_3107_);
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 2, v_tail_3112_);
v___x_3114_ = v___x_3109_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_key_3105_);
lean_ctor_set(v_reuseFailAlloc_3115_, 1, v_value_3106_);
lean_ctor_set(v_reuseFailAlloc_3115_, 2, v_tail_3112_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
else
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v_val_3118_; lean_object* v___x_3120_; 
lean_dec(v_key_3105_);
v___x_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3116_, 0, v_value_3106_);
v___x_3117_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_3096_, v_a_3097_, v_character_3098_, v___x_3116_);
v_val_3118_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_val_3118_);
lean_dec(v___x_3117_);
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 1, v_val_3118_);
lean_ctor_set(v___x_3109_, 0, v_a_3099_);
v___x_3120_ = v___x_3109_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3099_);
lean_ctor_set(v_reuseFailAlloc_3121_, 1, v_val_3118_);
lean_ctor_set(v_reuseFailAlloc_3121_, 2, v_tail_3107_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(lean_object* v_character_3123_, lean_object* v_a_3124_, lean_object* v_character_3125_, lean_object* v_m_3126_, lean_object* v_a_3127_){
_start:
{
lean_object* v_size_3128_; lean_object* v_buckets_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3181_; 
v_size_3128_ = lean_ctor_get(v_m_3126_, 0);
v_buckets_3129_ = lean_ctor_get(v_m_3126_, 1);
v_isSharedCheck_3181_ = !lean_is_exclusive(v_m_3126_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3131_ = v_m_3126_;
v_isShared_3132_ = v_isSharedCheck_3181_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_buckets_3129_);
lean_inc(v_size_3128_);
lean_dec(v_m_3126_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3181_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3133_; uint64_t v___x_3134_; uint64_t v___x_3135_; uint64_t v___x_3136_; uint64_t v_fold_3137_; uint64_t v___x_3138_; uint64_t v___x_3139_; uint64_t v___x_3140_; size_t v___x_3141_; size_t v___x_3142_; size_t v___x_3143_; size_t v___x_3144_; size_t v___x_3145_; lean_object* v_bkt_3146_; uint8_t v___x_3147_; 
v___x_3133_ = lean_array_get_size(v_buckets_3129_);
v___x_3134_ = lean_uint64_of_nat(v_a_3127_);
v___x_3135_ = 32ULL;
v___x_3136_ = lean_uint64_shift_right(v___x_3134_, v___x_3135_);
v_fold_3137_ = lean_uint64_xor(v___x_3134_, v___x_3136_);
v___x_3138_ = 16ULL;
v___x_3139_ = lean_uint64_shift_right(v_fold_3137_, v___x_3138_);
v___x_3140_ = lean_uint64_xor(v_fold_3137_, v___x_3139_);
v___x_3141_ = lean_uint64_to_usize(v___x_3140_);
v___x_3142_ = lean_usize_of_nat(v___x_3133_);
v___x_3143_ = ((size_t)1ULL);
v___x_3144_ = lean_usize_sub(v___x_3142_, v___x_3143_);
v___x_3145_ = lean_usize_land(v___x_3141_, v___x_3144_);
v_bkt_3146_ = lean_array_uget_borrowed(v_buckets_3129_, v___x_3145_);
v___x_3147_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3127_, v_bkt_3146_);
if (v___x_3147_ == 0)
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v_size_x27_3153_; lean_object* v___x_3154_; lean_object* v_buckets_x27_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; uint8_t v___x_3161_; 
v___x_3148_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___x_3149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3149_, 0, v_character_3123_);
lean_ctor_set(v___x_3149_, 1, v_a_3124_);
v___x_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3150_, 0, v_character_3125_);
lean_ctor_set(v___x_3150_, 1, v___x_3149_);
v___x_3151_ = lean_array_push(v___x_3148_, v___x_3150_);
v___x_3152_ = lean_unsigned_to_nat(1u);
v_size_x27_3153_ = lean_nat_add(v_size_3128_, v___x_3152_);
lean_dec(v_size_3128_);
lean_inc(v_bkt_3146_);
v___x_3154_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3154_, 0, v_a_3127_);
lean_ctor_set(v___x_3154_, 1, v___x_3151_);
lean_ctor_set(v___x_3154_, 2, v_bkt_3146_);
v_buckets_x27_3155_ = lean_array_uset(v_buckets_3129_, v___x_3145_, v___x_3154_);
v___x_3156_ = lean_unsigned_to_nat(4u);
v___x_3157_ = lean_nat_mul(v_size_x27_3153_, v___x_3156_);
v___x_3158_ = lean_unsigned_to_nat(3u);
v___x_3159_ = lean_nat_div(v___x_3157_, v___x_3158_);
lean_dec(v___x_3157_);
v___x_3160_ = lean_array_get_size(v_buckets_x27_3155_);
v___x_3161_ = lean_nat_dec_le(v___x_3159_, v___x_3160_);
lean_dec(v___x_3159_);
if (v___x_3161_ == 0)
{
lean_object* v_val_3162_; lean_object* v___x_3164_; 
v_val_3162_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_buckets_x27_3155_);
if (v_isShared_3132_ == 0)
{
lean_ctor_set(v___x_3131_, 1, v_val_3162_);
lean_ctor_set(v___x_3131_, 0, v_size_x27_3153_);
v___x_3164_ = v___x_3131_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_size_x27_3153_);
lean_ctor_set(v_reuseFailAlloc_3165_, 1, v_val_3162_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
else
{
lean_object* v___x_3167_; 
if (v_isShared_3132_ == 0)
{
lean_ctor_set(v___x_3131_, 1, v_buckets_x27_3155_);
lean_ctor_set(v___x_3131_, 0, v_size_x27_3153_);
v___x_3167_ = v___x_3131_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_size_x27_3153_);
lean_ctor_set(v_reuseFailAlloc_3168_, 1, v_buckets_x27_3155_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
else
{
lean_object* v___x_3169_; lean_object* v_buckets_x27_3170_; lean_object* v_bkt_x27_3171_; lean_object* v___y_3173_; uint8_t v___x_3178_; 
lean_inc(v_bkt_3146_);
v___x_3169_ = lean_box(0);
v_buckets_x27_3170_ = lean_array_uset(v_buckets_3129_, v___x_3145_, v___x_3169_);
lean_inc(v_a_3127_);
v_bkt_x27_3171_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_3123_, v_a_3124_, v_character_3125_, v_a_3127_, v_bkt_3146_);
v___x_3178_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3127_, v_bkt_x27_3171_);
lean_dec(v_a_3127_);
if (v___x_3178_ == 0)
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3179_ = lean_unsigned_to_nat(1u);
v___x_3180_ = lean_nat_sub(v_size_3128_, v___x_3179_);
lean_dec(v_size_3128_);
v___y_3173_ = v___x_3180_;
goto v___jp_3172_;
}
else
{
v___y_3173_ = v_size_3128_;
goto v___jp_3172_;
}
v___jp_3172_:
{
lean_object* v___x_3174_; lean_object* v___x_3176_; 
v___x_3174_ = lean_array_uset(v_buckets_x27_3170_, v___x_3145_, v_bkt_x27_3171_);
if (v_isShared_3132_ == 0)
{
lean_ctor_set(v___x_3131_, 1, v___x_3174_);
lean_ctor_set(v___x_3131_, 0, v___y_3173_);
v___x_3176_ = v___x_3131_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v___y_3173_);
lean_ctor_set(v_reuseFailAlloc_3177_, 1, v___x_3174_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(lean_object* v_text_3182_, lean_object* v_as_3183_, size_t v_sz_3184_, size_t v_i_3185_, lean_object* v_b_3186_){
_start:
{
lean_object* v_a_3188_; uint8_t v___x_3192_; 
v___x_3192_ = lean_usize_dec_lt(v_i_3185_, v_sz_3184_);
if (v___x_3192_ == 0)
{
lean_dec_ref(v_text_3182_);
return v_b_3186_;
}
else
{
lean_object* v_a_3193_; lean_object* v_stx_3194_; uint8_t v___x_3195_; lean_object* v___x_3196_; 
v_a_3193_ = lean_array_uget_borrowed(v_as_3183_, v_i_3185_);
v_stx_3194_ = lean_ctor_get(v_a_3193_, 0);
v___x_3195_ = 0;
lean_inc_ref(v_text_3182_);
v___x_3196_ = l_Lean_FileMap_lspRangeOfStx_x3f(v_text_3182_, v_stx_3194_, v___x_3195_);
if (lean_obj_tag(v___x_3196_) == 1)
{
lean_object* v_val_3197_; lean_object* v_start_3198_; lean_object* v_end_3199_; lean_object* v_line_3200_; lean_object* v_character_3201_; lean_object* v_character_3202_; lean_object* v___x_3203_; 
v_val_3197_ = lean_ctor_get(v___x_3196_, 0);
lean_inc(v_val_3197_);
lean_dec_ref_known(v___x_3196_, 1);
v_start_3198_ = lean_ctor_get(v_val_3197_, 0);
lean_inc_ref(v_start_3198_);
v_end_3199_ = lean_ctor_get(v_val_3197_, 1);
lean_inc_ref(v_end_3199_);
lean_dec(v_val_3197_);
v_line_3200_ = lean_ctor_get(v_start_3198_, 0);
lean_inc(v_line_3200_);
v_character_3201_ = lean_ctor_get(v_start_3198_, 1);
lean_inc(v_character_3201_);
lean_dec_ref(v_start_3198_);
v_character_3202_ = lean_ctor_get(v_end_3199_, 1);
lean_inc(v_character_3202_);
lean_dec_ref(v_end_3199_);
lean_inc(v_a_3193_);
v___x_3203_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(v_character_3202_, v_a_3193_, v_character_3201_, v_b_3186_, v_line_3200_);
v_a_3188_ = v___x_3203_;
goto v___jp_3187_;
}
else
{
lean_dec(v___x_3196_);
v_a_3188_ = v_b_3186_;
goto v___jp_3187_;
}
}
v___jp_3187_:
{
size_t v___x_3189_; size_t v___x_3190_; 
v___x_3189_ = ((size_t)1ULL);
v___x_3190_ = lean_usize_add(v_i_3185_, v___x_3189_);
v_i_3185_ = v___x_3190_;
v_b_3186_ = v_a_3188_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_text_3182_ = stack[0].m_obj;
lean_object* v_as_3183_ = stack[1].m_obj;
size_t v_sz_3184_ = stack[2].m_num;
size_t v_i_3185_ = stack[3].m_num;
lean_object* v_b_3186_ = stack[4].m_obj;
lean_object* v_res_3204_;
v_res_3204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3182_, v_as_3183_, v_sz_3184_, v_i_3185_, v_b_3186_);
stack->m_obj
 = v_res_3204_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3___boxed(lean_object* v_text_3205_, lean_object* v_as_3206_, lean_object* v_sz_3207_, lean_object* v_i_3208_, lean_object* v_b_3209_){
_start:
{
size_t v_sz_boxed_3210_; size_t v_i_boxed_3211_; lean_object* v_res_3212_; 
v_sz_boxed_3210_ = lean_unbox_usize(v_sz_3207_);
lean_dec(v_sz_3207_);
v_i_boxed_3211_ = lean_unbox_usize(v_i_3208_);
lean_dec(v_i_3208_);
v_res_3212_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3205_, v_as_3206_, v_sz_boxed_3210_, v_i_boxed_3211_, v_b_3209_);
lean_dec_ref(v_as_3206_);
return v_res_3212_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0(void){
_start:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3213_ = lean_box(0);
v___x_3214_ = lean_unsigned_to_nat(16u);
v___x_3215_ = lean_mk_array(v___x_3214_, v___x_3213_);
return v___x_3215_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1(void){
_start:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v_byLine_3218_; 
v___x_3216_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__0, &l_Lean_Server_FileWorker_dbgShowTokens___closed__0_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0);
v___x_3217_ = lean_unsigned_to_nat(0u);
v_byLine_3218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byLine_3218_, 0, v___x_3217_);
lean_ctor_set(v_byLine_3218_, 1, v___x_3216_);
return v_byLine_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens(lean_object* v_text_3221_, lean_object* v_toks_3222_){
_start:
{
lean_object* v___x_3223_; lean_object* v_byLine_3224_; size_t v_sz_3225_; size_t v___x_3226_; lean_object* v___x_3227_; lean_object* v_buckets_3228_; lean_object* v___f_3229_; lean_object* v___x_3230_; lean_object* v___y_3232_; lean_object* v___x_3235_; lean_object* v___x_3236_; uint8_t v___x_3237_; 
v___x_3223_ = lean_unsigned_to_nat(0u);
v_byLine_3224_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__1, &l_Lean_Server_FileWorker_dbgShowTokens___closed__1_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1);
v_sz_3225_ = lean_array_size(v_toks_3222_);
v___x_3226_ = ((size_t)0ULL);
v___x_3227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3221_, v_toks_3222_, v_sz_3225_, v___x_3226_, v_byLine_3224_);
v_buckets_3228_ = lean_ctor_get(v___x_3227_, 1);
lean_inc_ref(v_buckets_3228_);
lean_dec_ref(v___x_3227_);
v___f_3229_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__2));
v___x_3230_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__3));
v___x_3235_ = lean_box(0);
v___x_3236_ = lean_array_get_size(v_buckets_3228_);
v___x_3237_ = lean_nat_dec_lt(v___x_3223_, v___x_3236_);
if (v___x_3237_ == 0)
{
lean_dec_ref(v_buckets_3228_);
v___y_3232_ = v___x_3235_;
goto v___jp_3231_;
}
else
{
size_t v___x_3238_; lean_object* v___x_3239_; 
v___x_3238_ = lean_usize_of_nat(v___x_3236_);
v___x_3239_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_buckets_3228_, v___x_3238_, v___x_3226_, v___x_3235_);
lean_dec_ref(v_buckets_3228_);
v___y_3232_ = v___x_3239_;
goto v___jp_3231_;
}
v___jp_3231_:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3233_ = l_List_mergeSort___redArg(v___y_3232_, v___f_3229_);
v___x_3234_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v___x_3233_, v___x_3230_);
lean_dec(v___x_3233_);
return v___x_3234_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___boxed(lean_object* v_text_3240_, lean_object* v_toks_3241_){
_start:
{
lean_object* v_res_3242_; 
v_res_3242_ = l_Lean_Server_FileWorker_dbgShowTokens(v_text_3240_, v_toks_3241_);
lean_dec_ref(v_toks_3241_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(lean_object* v_as_3243_, lean_object* v_as_x27_3244_, lean_object* v_b_3245_, lean_object* v_a_3246_){
_start:
{
lean_object* v___x_3247_; 
v___x_3247_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v_as_x27_3244_, v_b_3245_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___boxed(lean_object* v_as_3248_, lean_object* v_as_x27_3249_, lean_object* v_b_3250_, lean_object* v_a_3251_){
_start:
{
lean_object* v_res_3252_; 
v_res_3252_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(v_as_3248_, v_as_x27_3249_, v_b_3250_, v_a_3251_);
lean_dec(v_as_x27_3249_);
lean_dec(v_as_3248_);
return v_res_3252_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(lean_object* v_00_u03b2_3253_, lean_object* v_a_3254_, lean_object* v_x_3255_){
_start:
{
uint8_t v___x_3256_; 
v___x_3256_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3254_, v_x_3255_);
return v___x_3256_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3254_ = stack[1].m_obj;
lean_object* v_x_3255_ = stack[2].m_obj;
uint8_t v_res_3257_;
v_res_3257_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(lean_box(0), v_a_3254_, v_x_3255_);
stack->m_num = v_res_3257_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3258_, lean_object* v_a_3259_, lean_object* v_x_3260_){
_start:
{
uint8_t v_res_3261_; lean_object* v_r_3262_; 
v_res_3261_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(v_00_u03b2_3258_, v_a_3259_, v_x_3260_);
lean_dec(v_x_3260_);
lean_dec(v_a_3259_);
v_r_3262_ = lean_box(v_res_3261_);
return v_r_3262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4(lean_object* v_00_u03b2_3263_, lean_object* v_data_3264_){
_start:
{
lean_object* v___x_3265_; 
v___x_3265_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_data_3264_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3266_, lean_object* v_i_3267_, lean_object* v_source_3268_, lean_object* v_target_3269_){
_start:
{
lean_object* v___x_3270_; 
v___x_3270_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v_i_3267_, v_source_3268_, v_target_3269_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10(lean_object* v_00_u03b2_3271_, lean_object* v_x_3272_, lean_object* v_x_3273_){
_start:
{
lean_object* v___x_3274_; 
v___x_3274_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_x_3272_, v_x_3273_);
return v___x_3274_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(lean_object* v_beginPos_3275_, lean_object* v_doc_3276_, lean_object* v_as_x27_3277_, lean_object* v_b_3278_, lean_object* v___y_3279_){
_start:
{
if (lean_obj_tag(v_as_x27_3277_) == 0)
{
lean_object* v___x_3281_; 
lean_dec_ref(v_doc_3276_);
v___x_3281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3281_, 0, v_b_3278_);
return v___x_3281_;
}
else
{
lean_object* v_head_3282_; lean_object* v_tail_3283_; lean_object* v___x_3284_; uint8_t v___x_3285_; 
v_head_3282_ = lean_ctor_get(v_as_x27_3277_, 0);
v_tail_3283_ = lean_ctor_get(v_as_x27_3277_, 1);
v___x_3284_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_head_3282_);
v___x_3285_ = lean_nat_dec_le(v___x_3284_, v_beginPos_3275_);
lean_dec(v___x_3284_);
if (v___x_3285_ == 0)
{
lean_object* v_toEditableDocumentCore_3286_; lean_object* v_meta_3287_; lean_object* v_text_3288_; lean_object* v_stx_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
v_toEditableDocumentCore_3286_ = lean_ctor_get(v_doc_3276_, 0);
v_meta_3287_ = lean_ctor_get(v_toEditableDocumentCore_3286_, 0);
v_text_3288_ = lean_ctor_get(v_meta_3287_, 3);
v_stx_3289_ = lean_ctor_get(v_head_3282_, 0);
lean_inc(v_stx_3289_);
lean_inc_ref(v_text_3288_);
v___x_3290_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_3288_, v_stx_3289_);
lean_inc(v_head_3282_);
v___x_3291_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_head_3282_);
v___x_3292_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(v___x_3291_);
v___x_3293_ = l_Array_append___redArg(v_b_3278_, v___x_3290_);
lean_dec_ref(v___x_3290_);
v___x_3294_ = l_Array_append___redArg(v___x_3293_, v___x_3292_);
lean_dec_ref(v___x_3292_);
v___x_3295_ = l_Lean_Server_RequestM_checkCancelled(v___y_3279_);
if (lean_obj_tag(v___x_3295_) == 0)
{
lean_dec_ref_known(v___x_3295_, 1);
v_as_x27_3277_ = v_tail_3283_;
v_b_3278_ = v___x_3294_;
goto _start;
}
else
{
lean_object* v_a_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3304_; 
lean_dec_ref(v___x_3294_);
lean_dec_ref(v_doc_3276_);
v_a_3297_ = lean_ctor_get(v___x_3295_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3299_ = v___x_3295_;
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_a_3297_);
lean_dec(v___x_3295_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v___x_3302_; 
if (v_isShared_3300_ == 0)
{
v___x_3302_ = v___x_3299_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3297_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
}
else
{
v_as_x27_3277_ = v_tail_3283_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_beginPos_3275_ = stack[0].m_obj;
lean_object* v_doc_3276_ = stack[1].m_obj;
lean_object* v_as_x27_3277_ = stack[2].m_obj;
lean_object* v_b_3278_ = stack[3].m_obj;
lean_object* v___y_3279_ = stack[4].m_obj;
lean_object* v_res_3306_;
v_res_3306_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3275_, v_doc_3276_, v_as_x27_3277_, v_b_3278_, v___y_3279_);
stack->m_obj
 = v_res_3306_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg___boxed(lean_object* v_beginPos_3307_, lean_object* v_doc_3308_, lean_object* v_as_x27_3309_, lean_object* v_b_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3307_, v_doc_3308_, v_as_x27_3309_, v_b_3310_, v___y_3311_);
lean_dec_ref(v___y_3311_);
lean_dec(v_as_x27_3309_);
lean_dec(v_beginPos_3307_);
return v_res_3313_;
}
}
lean_object* l_Lean_Server_FileWorker_computeSemanticTokens(lean_object* v_doc_3314_, lean_object* v_beginPos_3315_, lean_object* v_endPos_x3f_3316_, lean_object* v_snaps_3317_, lean_object* v_a_3318_){
_start:
{
lean_object* v_leanSemanticTokens_3320_; lean_object* v___x_3321_; 
v_leanSemanticTokens_3320_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
lean_inc_ref(v_doc_3314_);
v___x_3321_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3315_, v_doc_3314_, v_snaps_3317_, v_leanSemanticTokens_3320_, v_a_3318_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_object* v_toEditableDocumentCore_3322_; lean_object* v_meta_3323_; lean_object* v_a_3324_; lean_object* v_text_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v_toEditableDocumentCore_3322_ = lean_ctor_get(v_doc_3314_, 0);
lean_inc_ref(v_toEditableDocumentCore_3322_);
lean_dec_ref(v_doc_3314_);
v_meta_3323_ = lean_ctor_get(v_toEditableDocumentCore_3322_, 0);
lean_inc_ref(v_meta_3323_);
lean_dec_ref(v_toEditableDocumentCore_3322_);
v_a_3324_ = lean_ctor_get(v___x_3321_, 0);
lean_inc(v_a_3324_);
lean_dec_ref_known(v___x_3321_, 1);
v_text_3325_ = lean_ctor_get(v_meta_3323_, 3);
lean_inc_ref(v_text_3325_);
lean_dec_ref(v_meta_3323_);
v___x_3326_ = l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(v_text_3325_, v_beginPos_3315_, v_endPos_x3f_3316_, v_a_3324_);
lean_dec(v_a_3324_);
v___x_3327_ = l_Lean_Server_RequestM_checkCancelled(v_a_3318_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
lean_dec_ref_known(v___x_3327_, 1);
v___x_3328_ = l_Lean_Server_FileWorker_handleOverlappingSemanticTokens(v___x_3326_);
v___x_3329_ = l_Lean_Server_RequestM_checkCancelled(v_a_3318_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3337_; 
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3337_ == 0)
{
lean_object* v_unused_3338_; 
v_unused_3338_ = lean_ctor_get(v___x_3329_, 0);
lean_dec(v_unused_3338_);
v___x_3331_ = v___x_3329_;
v_isShared_3332_ = v_isSharedCheck_3337_;
goto v_resetjp_3330_;
}
else
{
lean_dec(v___x_3329_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3337_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3333_; lean_object* v___x_3335_; 
v___x_3333_ = l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(v___x_3328_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 0, v___x_3333_);
v___x_3335_ = v___x_3331_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3333_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
else
{
lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3346_; 
lean_dec_ref(v___x_3328_);
v_a_3339_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3341_ = v___x_3329_;
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_dec(v___x_3329_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3344_; 
if (v_isShared_3342_ == 0)
{
v___x_3344_ = v___x_3341_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3339_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
}
else
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3354_; 
lean_dec_ref(v___x_3326_);
v_a_3347_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3349_ = v___x_3327_;
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3327_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3352_; 
if (v_isShared_3350_ == 0)
{
v___x_3352_ = v___x_3349_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_a_3347_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
}
else
{
lean_object* v_a_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3362_; 
lean_dec_ref(v_doc_3314_);
v_a_3355_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3357_ = v___x_3321_;
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_a_3355_);
lean_dec(v___x_3321_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3360_; 
if (v_isShared_3358_ == 0)
{
v___x_3360_ = v___x_3357_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_a_3355_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_computeSemanticTokens_0interp(lean_interpreter_value* stack)
{
lean_object* v_doc_3314_ = stack[0].m_obj;
lean_object* v_beginPos_3315_ = stack[1].m_obj;
lean_object* v_endPos_x3f_3316_ = stack[2].m_obj;
lean_object* v_snaps_3317_ = stack[3].m_obj;
lean_object* v_a_3318_ = stack[4].m_obj;
lean_object* v_res_3363_;
v_res_3363_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_doc_3314_, v_beginPos_3315_, v_endPos_x3f_3316_, v_snaps_3317_, v_a_3318_);
stack->m_obj
 = v_res_3363_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens___boxed(lean_object* v_doc_3364_, lean_object* v_beginPos_3365_, lean_object* v_endPos_x3f_3366_, lean_object* v_snaps_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_doc_3364_, v_beginPos_3365_, v_endPos_x3f_3366_, v_snaps_3367_, v_a_3368_);
lean_dec_ref(v_a_3368_);
lean_dec(v_snaps_3367_);
lean_dec(v_endPos_x3f_3366_);
lean_dec(v_beginPos_3365_);
return v_res_3370_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(lean_object* v_beginPos_3371_, lean_object* v_doc_3372_, lean_object* v_as_3373_, lean_object* v_as_x27_3374_, lean_object* v_b_3375_, lean_object* v_a_3376_, lean_object* v___y_3377_){
_start:
{
lean_object* v___x_3379_; 
v___x_3379_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3371_, v_doc_3372_, v_as_x27_3374_, v_b_3375_, v___y_3377_);
return v___x_3379_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_beginPos_3371_ = stack[0].m_obj;
lean_object* v_doc_3372_ = stack[1].m_obj;
lean_object* v_as_3373_ = stack[2].m_obj;
lean_object* v_as_x27_3374_ = stack[3].m_obj;
lean_object* v_b_3375_ = stack[4].m_obj;
lean_object* v___y_3377_ = stack[6].m_obj;
lean_object* v_res_3380_;
v_res_3380_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(v_beginPos_3371_, v_doc_3372_, v_as_3373_, v_as_x27_3374_, v_b_3375_, lean_box(0), v___y_3377_);
stack->m_obj
 = v_res_3380_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___boxed(lean_object* v_beginPos_3381_, lean_object* v_doc_3382_, lean_object* v_as_3383_, lean_object* v_as_x27_3384_, lean_object* v_b_3385_, lean_object* v_a_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_){
_start:
{
lean_object* v_res_3389_; 
v_res_3389_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(v_beginPos_3381_, v_doc_3382_, v_as_3383_, v_as_x27_3384_, v_b_3385_, v_a_3386_, v___y_3387_);
lean_dec_ref(v___y_3387_);
lean_dec(v_as_x27_3384_);
lean_dec(v_as_3383_);
lean_dec(v_beginPos_3381_);
return v_res_3389_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState_default(void){
_start:
{
lean_object* v___x_3398_; 
v___x_3398_ = lean_box(0);
return v___x_3398_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState(void){
_start:
{
lean_object* v___x_3399_; 
v___x_3399_ = lean_box(0);
return v___x_3399_;
}
}
lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(lean_object* v___y_3400_){
_start:
{
lean_object* v_doc_3402_; lean_object* v___x_3403_; 
v_doc_3402_ = lean_ctor_get(v___y_3400_, 1);
lean_inc_ref(v_doc_3402_);
v___x_3403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3403_, 0, v_doc_3402_);
return v___x_3403_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3400_ = stack[0].m_obj;
lean_object* v_res_3404_;
v_res_3404_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v___y_3400_);
stack->m_obj
 = v_res_3404_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0___boxed(lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v___y_3405_);
lean_dec_ref(v___y_3405_);
return v_res_3407_;
}
}
lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(lean_object* v_a_3408_){
_start:
{
lean_object* v___x_3410_; lean_object* v_a_3411_; lean_object* v_toEditableDocumentCore_3412_; lean_object* v_cmdSnaps_3413_; lean_object* v_cancelTk_3414_; uint32_t v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v_snd_3418_; lean_object* v_fst_3419_; lean_object* v_snd_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3449_; 
v___x_3410_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_3408_);
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
lean_inc(v_a_3411_);
lean_dec_ref(v___x_3410_);
v_toEditableDocumentCore_3412_ = lean_ctor_get(v_a_3411_, 0);
v_cmdSnaps_3413_ = lean_ctor_get(v_toEditableDocumentCore_3412_, 2);
v_cancelTk_3414_ = lean_ctor_get(v_a_3408_, 4);
v___x_3415_ = 3000;
v___x_3416_ = l_Lean_Server_RequestCancellationToken_cancellationTasks(v_cancelTk_3414_);
lean_inc(v_cmdSnaps_3413_);
v___x_3417_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(v_cmdSnaps_3413_, v___x_3415_, v___x_3416_);
v_snd_3418_ = lean_ctor_get(v___x_3417_, 1);
lean_inc(v_snd_3418_);
v_fst_3419_ = lean_ctor_get(v___x_3417_, 0);
lean_inc(v_fst_3419_);
lean_dec_ref(v___x_3417_);
v_snd_3420_ = lean_ctor_get(v_snd_3418_, 1);
v_isSharedCheck_3449_ = !lean_is_exclusive(v_snd_3418_);
if (v_isSharedCheck_3449_ == 0)
{
lean_object* v_unused_3450_; 
v_unused_3450_ = lean_ctor_get(v_snd_3418_, 0);
lean_dec(v_unused_3450_);
v___x_3422_ = v_snd_3418_;
v_isShared_3423_ = v_isSharedCheck_3449_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_snd_3420_);
lean_dec(v_snd_3418_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3449_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3424_ = lean_unsigned_to_nat(0u);
v___x_3425_ = lean_box(0);
v___x_3426_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_3411_, v___x_3424_, v___x_3425_, v_fst_3419_, v_a_3408_);
lean_dec(v_fst_3419_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3440_; 
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3429_ = v___x_3426_;
v_isShared_3430_ = v_isSharedCheck_3440_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3426_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3440_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3431_; uint8_t v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3435_; 
v___x_3431_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3431_, 0, v_a_3427_);
v___x_3432_ = lean_unbox(v_snd_3420_);
lean_dec(v_snd_3420_);
lean_ctor_set_uint8(v___x_3431_, sizeof(void*)*1, v___x_3432_);
v___x_3433_ = lean_box(0);
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 1, v___x_3433_);
lean_ctor_set(v___x_3422_, 0, v___x_3431_);
v___x_3435_ = v___x_3422_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3431_);
lean_ctor_set(v_reuseFailAlloc_3439_, 1, v___x_3433_);
v___x_3435_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
lean_object* v___x_3437_; 
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 0, v___x_3435_);
v___x_3437_ = v___x_3429_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v___x_3435_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
}
else
{
lean_object* v_a_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3448_; 
lean_del_object(v___x_3422_);
lean_dec(v_snd_3420_);
v_a_3441_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3443_ = v___x_3426_;
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v___x_3426_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3446_; 
if (v_isShared_3444_ == 0)
{
v___x_3446_ = v___x_3443_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_a_3441_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3408_ = stack[0].m_obj;
lean_object* v_res_3451_;
v_res_3451_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_3408_);
stack->m_obj
 = v_res_3451_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg___boxed(lean_object* v_a_3452_, lean_object* v_a_3453_){
_start:
{
lean_object* v_res_3454_; 
v_res_3454_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_3452_);
lean_dec_ref(v_a_3452_);
return v_res_3454_;
}
}
lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull(lean_object* v_x_3455_, lean_object* v_x_3456_, lean_object* v_a_3457_){
_start:
{
lean_object* v___x_3459_; 
v___x_3459_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_3457_);
return v___x_3459_;
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_handleSemanticTokensFull_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3455_ = stack[0].m_obj;
lean_object* v_x_3456_ = stack[1].m_obj;
lean_object* v_a_3457_ = stack[2].m_obj;
lean_object* v_res_3460_;
v_res_3460_ = l_Lean_Server_FileWorker_handleSemanticTokensFull(v_x_3455_, v_x_3456_, v_a_3457_);
stack->m_obj
 = v_res_3460_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___boxed(lean_object* v_x_3461_, lean_object* v_x_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_){
_start:
{
lean_object* v_res_3465_; 
v_res_3465_ = l_Lean_Server_FileWorker_handleSemanticTokensFull(v_x_3461_, v_x_3462_, v_a_3463_);
lean_dec_ref(v_a_3463_);
lean_dec_ref(v_x_3461_);
return v_res_3465_;
}
}
lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(lean_object* v_a_3466_){
_start:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3468_ = lean_box(0);
v___x_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3468_);
lean_ctor_set(v___x_3469_, 1, v_a_3466_);
v___x_3470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3469_);
return v___x_3470_;
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3466_ = stack[0].m_obj;
lean_object* v_res_3471_;
v_res_3471_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_3466_);
stack->m_obj
 = v_res_3471_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg___boxed(lean_object* v_a_3472_, lean_object* v_a_3473_){
_start:
{
lean_object* v_res_3474_; 
v_res_3474_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_3472_);
return v_res_3474_;
}
}
lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange(lean_object* v_x_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_){
_start:
{
lean_object* v___x_3479_; 
v___x_3479_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_3476_);
return v___x_3479_;
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_handleSemanticTokensDidChange_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3475_ = stack[0].m_obj;
lean_object* v_a_3476_ = stack[1].m_obj;
lean_object* v_a_3477_ = stack[2].m_obj;
lean_object* v_res_3480_;
v_res_3480_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange(v_x_3475_, v_a_3476_, v_a_3477_);
stack->m_obj
 = v_res_3480_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___boxed(lean_object* v_x_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange(v_x_3481_, v_a_3482_, v_a_3483_);
lean_dec_ref(v_a_3483_);
lean_dec_ref(v_x_3481_);
return v_res_3485_;
}
}
uint8_t l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(lean_object* v___x_3486_, lean_object* v_x_3487_){
_start:
{
lean_object* v___x_3488_; uint8_t v___x_3489_; 
v___x_3488_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_x_3487_);
v___x_3489_ = lean_nat_dec_le(v___x_3486_, v___x_3488_);
lean_dec(v___x_3488_);
return v___x_3489_;
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3486_ = stack[0].m_obj;
lean_object* v_x_3487_ = stack[1].m_obj;
uint8_t v_res_3490_;
v_res_3490_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(v___x_3486_, v_x_3487_);
stack->m_num = v_res_3490_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed(lean_object* v___x_3491_, lean_object* v_x_3492_){
_start:
{
uint8_t v_res_3493_; lean_object* v_r_3494_; 
v_res_3493_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(v___x_3491_, v_x_3492_);
lean_dec_ref(v_x_3492_);
lean_dec(v___x_3491_);
v_r_3494_ = lean_box(v_res_3493_);
return v_r_3494_;
}
}
lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(lean_object* v___x_3495_, lean_object* v_a_3496_, lean_object* v___x_3497_, lean_object* v_x_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v_fst_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v_fst_3501_ = lean_ctor_get(v_x_3498_, 0);
v___x_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3495_);
v___x_3503_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_3496_, v___x_3497_, v___x_3502_, v_fst_3501_, v___y_3499_);
lean_dec_ref_known(v___x_3502_, 1);
return v___x_3503_;
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3495_ = stack[0].m_obj;
lean_object* v_a_3496_ = stack[1].m_obj;
lean_object* v___x_3497_ = stack[2].m_obj;
lean_object* v_x_3498_ = stack[3].m_obj;
lean_object* v___y_3499_ = stack[4].m_obj;
lean_object* v_res_3504_;
v_res_3504_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(v___x_3495_, v_a_3496_, v___x_3497_, v_x_3498_, v___y_3499_);
stack->m_obj
 = v_res_3504_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed(lean_object* v___x_3505_, lean_object* v_a_3506_, lean_object* v___x_3507_, lean_object* v_x_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_){
_start:
{
lean_object* v_res_3511_; 
v_res_3511_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(v___x_3505_, v_a_3506_, v___x_3507_, v_x_3508_, v___y_3509_);
lean_dec_ref(v___y_3509_);
lean_dec_ref(v_x_3508_);
lean_dec(v___x_3507_);
return v_res_3511_;
}
}
lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange(lean_object* v_p_3512_, lean_object* v_a_3513_){
_start:
{
lean_object* v___x_3515_; lean_object* v_a_3516_; lean_object* v_toEditableDocumentCore_3517_; lean_object* v_meta_3518_; lean_object* v_range_3519_; lean_object* v_cmdSnaps_3520_; lean_object* v_text_3521_; lean_object* v_start_3522_; lean_object* v_end_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___f_3526_; lean_object* v___f_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3515_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_3513_);
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3516_);
lean_dec_ref(v___x_3515_);
v_toEditableDocumentCore_3517_ = lean_ctor_get(v_a_3516_, 0);
v_meta_3518_ = lean_ctor_get(v_toEditableDocumentCore_3517_, 0);
v_range_3519_ = lean_ctor_get(v_p_3512_, 1);
lean_inc_ref(v_range_3519_);
lean_dec_ref(v_p_3512_);
v_cmdSnaps_3520_ = lean_ctor_get(v_toEditableDocumentCore_3517_, 2);
lean_inc(v_cmdSnaps_3520_);
v_text_3521_ = lean_ctor_get(v_meta_3518_, 3);
v_start_3522_ = lean_ctor_get(v_range_3519_, 0);
lean_inc_ref(v_start_3522_);
v_end_3523_ = lean_ctor_get(v_range_3519_, 1);
lean_inc_ref(v_end_3523_);
lean_dec_ref(v_range_3519_);
v___x_3524_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_3521_, v_start_3522_);
v___x_3525_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_3521_, v_end_3523_);
lean_inc(v___x_3525_);
v___f_3526_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3526_, 0, v___x_3525_);
v___f_3527_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3527_, 0, v___x_3525_);
lean_closure_set(v___f_3527_, 1, v_a_3516_);
lean_closure_set(v___f_3527_, 2, v___x_3524_);
v___x_3528_ = l_Lean_AsyncList_waitUntil___redArg(v___f_3526_, v_cmdSnaps_3520_);
v___x_3529_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_3528_, v___f_3527_, v_a_3513_);
return v___x_3529_;
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_handleSemanticTokensRange_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3512_ = stack[0].m_obj;
lean_object* v_a_3513_ = stack[1].m_obj;
lean_object* v_res_3530_;
v_res_3530_ = l_Lean_Server_FileWorker_handleSemanticTokensRange(v_p_3512_, v_a_3513_);
stack->m_obj
 = v_res_3530_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___boxed(lean_object* v_p_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_){
_start:
{
lean_object* v_res_3534_; 
v_res_3534_ = l_Lean_Server_FileWorker_handleSemanticTokensRange(v_p_3531_, v_a_3532_);
lean_dec_ref(v_a_3532_);
return v_res_3534_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_keys_3535_, lean_object* v_i_3536_, lean_object* v_k_3537_){
_start:
{
lean_object* v___x_3538_; uint8_t v___x_3539_; 
v___x_3538_ = lean_array_get_size(v_keys_3535_);
v___x_3539_ = lean_nat_dec_lt(v_i_3536_, v___x_3538_);
if (v___x_3539_ == 0)
{
lean_dec(v_i_3536_);
return v___x_3539_;
}
else
{
lean_object* v_k_x27_3540_; uint8_t v___x_3541_; 
v_k_x27_3540_ = lean_array_fget_borrowed(v_keys_3535_, v_i_3536_);
v___x_3541_ = lean_string_dec_eq(v_k_3537_, v_k_x27_3540_);
if (v___x_3541_ == 0)
{
lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3542_ = lean_unsigned_to_nat(1u);
v___x_3543_ = lean_nat_add(v_i_3536_, v___x_3542_);
lean_dec(v_i_3536_);
v_i_3536_ = v___x_3543_;
goto _start;
}
else
{
lean_dec(v_i_3536_);
return v___x_3539_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_3535_ = stack[0].m_obj;
lean_object* v_i_3536_ = stack[1].m_obj;
lean_object* v_k_3537_ = stack[2].m_obj;
uint8_t v_res_3545_;
v_res_3545_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_3535_, v_i_3536_, v_k_3537_);
stack->m_num = v_res_3545_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_keys_3546_, lean_object* v_i_3547_, lean_object* v_k_3548_){
_start:
{
uint8_t v_res_3549_; lean_object* v_r_3550_; 
v_res_3549_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_3546_, v_i_3547_, v_k_3548_);
lean_dec_ref(v_k_3548_);
lean_dec_ref(v_keys_3546_);
v_r_3550_ = lean_box(v_res_3549_);
return v_r_3550_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(lean_object* v_x_3551_, size_t v_x_3552_, lean_object* v_x_3553_){
_start:
{
if (lean_obj_tag(v_x_3551_) == 0)
{
lean_object* v_es_3554_; lean_object* v___x_3555_; size_t v___x_3556_; size_t v___x_3557_; lean_object* v_j_3558_; lean_object* v___x_3559_; 
v_es_3554_ = lean_ctor_get(v_x_3551_, 0);
v___x_3555_ = lean_box(2);
v___x_3556_ = ((size_t)31ULL);
v___x_3557_ = lean_usize_land(v_x_3552_, v___x_3556_);
v_j_3558_ = lean_usize_to_nat(v___x_3557_);
v___x_3559_ = lean_array_get_borrowed(v___x_3555_, v_es_3554_, v_j_3558_);
lean_dec(v_j_3558_);
switch(lean_obj_tag(v___x_3559_))
{
case 0:
{
lean_object* v_key_3560_; uint8_t v___x_3561_; 
v_key_3560_ = lean_ctor_get(v___x_3559_, 0);
v___x_3561_ = lean_string_dec_eq(v_x_3553_, v_key_3560_);
return v___x_3561_;
}
case 1:
{
lean_object* v_node_3562_; size_t v___x_3563_; size_t v___x_3564_; 
v_node_3562_ = lean_ctor_get(v___x_3559_, 0);
v___x_3563_ = ((size_t)5ULL);
v___x_3564_ = lean_usize_shift_right(v_x_3552_, v___x_3563_);
v_x_3551_ = v_node_3562_;
v_x_3552_ = v___x_3564_;
goto _start;
}
default: 
{
uint8_t v___x_3566_; 
v___x_3566_ = 0;
return v___x_3566_;
}
}
}
else
{
lean_object* v_ks_3567_; lean_object* v___x_3568_; uint8_t v___x_3569_; 
v_ks_3567_ = lean_ctor_get(v_x_3551_, 0);
v___x_3568_ = lean_unsigned_to_nat(0u);
v___x_3569_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_ks_3567_, v___x_3568_, v_x_3553_);
return v___x_3569_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3551_ = stack[0].m_obj;
size_t v_x_3552_ = stack[1].m_num;
lean_object* v_x_3553_ = stack[2].m_obj;
uint8_t v_res_3570_;
v_res_3570_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_3551_, v_x_3552_, v_x_3553_);
stack->m_num = v_res_3570_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_x_3571_, lean_object* v_x_3572_, lean_object* v_x_3573_){
_start:
{
size_t v_x_2481__boxed_3574_; uint8_t v_res_3575_; lean_object* v_r_3576_; 
v_x_2481__boxed_3574_ = lean_unbox_usize(v_x_3572_);
lean_dec(v_x_3572_);
v_res_3575_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_3571_, v_x_2481__boxed_3574_, v_x_3573_);
lean_dec_ref(v_x_3573_);
lean_dec_ref(v_x_3571_);
v_r_3576_ = lean_box(v_res_3575_);
return v_r_3576_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_x_3577_, lean_object* v_x_3578_){
_start:
{
uint64_t v___x_3579_; size_t v___x_3580_; uint8_t v___x_3581_; 
v___x_3579_ = lean_string_hash(v_x_3578_);
v___x_3580_ = lean_uint64_to_usize(v___x_3579_);
v___x_3581_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_3577_, v___x_3580_, v_x_3578_);
return v___x_3581_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3577_ = stack[0].m_obj;
lean_object* v_x_3578_ = stack[1].m_obj;
uint8_t v_res_3582_;
v_res_3582_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_3577_, v_x_3578_);
stack->m_num = v_res_3582_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object* v_x_3583_, lean_object* v_x_3584_){
_start:
{
uint8_t v_res_3585_; lean_object* v_r_3586_; 
v_res_3585_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_3583_, v_x_3584_);
lean_dec_ref(v_x_3584_);
lean_dec_ref(v_x_3583_);
v_r_3586_ = lean_box(v_res_3585_);
return v_r_3586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(lean_object* v___x_3587_, lean_object* v_x_3588_){
_start:
{
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4___boxed(lean_object* v___x_3589_, lean_object* v_x_3590_){
_start:
{
lean_object* v_res_3591_; 
v_res_3591_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(v___x_3589_, v_x_3590_);
lean_dec_ref(v_x_3590_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(lean_object* v_x_3592_, lean_object* v_x_3593_, lean_object* v_x_3594_, lean_object* v_x_3595_){
_start:
{
lean_object* v_ks_3596_; lean_object* v_vs_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3621_; 
v_ks_3596_ = lean_ctor_get(v_x_3592_, 0);
v_vs_3597_ = lean_ctor_get(v_x_3592_, 1);
v_isSharedCheck_3621_ = !lean_is_exclusive(v_x_3592_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3599_ = v_x_3592_;
v_isShared_3600_ = v_isSharedCheck_3621_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_vs_3597_);
lean_inc(v_ks_3596_);
lean_dec(v_x_3592_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3621_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3601_; uint8_t v___x_3602_; 
v___x_3601_ = lean_array_get_size(v_ks_3596_);
v___x_3602_ = lean_nat_dec_lt(v_x_3593_, v___x_3601_);
if (v___x_3602_ == 0)
{
lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3606_; 
lean_dec(v_x_3593_);
v___x_3603_ = lean_array_push(v_ks_3596_, v_x_3594_);
v___x_3604_ = lean_array_push(v_vs_3597_, v_x_3595_);
if (v_isShared_3600_ == 0)
{
lean_ctor_set(v___x_3599_, 1, v___x_3604_);
lean_ctor_set(v___x_3599_, 0, v___x_3603_);
v___x_3606_ = v___x_3599_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v___x_3603_);
lean_ctor_set(v_reuseFailAlloc_3607_, 1, v___x_3604_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
else
{
lean_object* v_k_x27_3608_; uint8_t v___x_3609_; 
v_k_x27_3608_ = lean_array_fget_borrowed(v_ks_3596_, v_x_3593_);
v___x_3609_ = lean_string_dec_eq(v_x_3594_, v_k_x27_3608_);
if (v___x_3609_ == 0)
{
lean_object* v___x_3611_; 
if (v_isShared_3600_ == 0)
{
v___x_3611_ = v___x_3599_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_ks_3596_);
lean_ctor_set(v_reuseFailAlloc_3615_, 1, v_vs_3597_);
v___x_3611_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3612_ = lean_unsigned_to_nat(1u);
v___x_3613_ = lean_nat_add(v_x_3593_, v___x_3612_);
lean_dec(v_x_3593_);
v_x_3592_ = v___x_3611_;
v_x_3593_ = v___x_3613_;
goto _start;
}
}
else
{
lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3619_; 
v___x_3616_ = lean_array_fset(v_ks_3596_, v_x_3593_, v_x_3594_);
v___x_3617_ = lean_array_fset(v_vs_3597_, v_x_3593_, v_x_3595_);
lean_dec(v_x_3593_);
if (v_isShared_3600_ == 0)
{
lean_ctor_set(v___x_3599_, 1, v___x_3617_);
lean_ctor_set(v___x_3599_, 0, v___x_3616_);
v___x_3619_ = v___x_3599_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3616_);
lean_ctor_set(v_reuseFailAlloc_3620_, 1, v___x_3617_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(lean_object* v_n_3622_, lean_object* v_k_3623_, lean_object* v_v_3624_){
_start:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3625_ = lean_unsigned_to_nat(0u);
v___x_3626_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_n_3622_, v___x_3625_, v_k_3623_, v_v_3624_);
return v___x_3626_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_3627_; 
v___x_3627_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_3627_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(lean_object* v_x_3628_, size_t v_x_3629_, size_t v_x_3630_, lean_object* v_x_3631_, lean_object* v_x_3632_){
_start:
{
if (lean_obj_tag(v_x_3628_) == 0)
{
lean_object* v_es_3633_; size_t v___x_3634_; size_t v___x_3635_; lean_object* v_j_3636_; lean_object* v___x_3637_; uint8_t v___x_3638_; 
v_es_3633_ = lean_ctor_get(v_x_3628_, 0);
v___x_3634_ = ((size_t)31ULL);
v___x_3635_ = lean_usize_land(v_x_3629_, v___x_3634_);
v_j_3636_ = lean_usize_to_nat(v___x_3635_);
v___x_3637_ = lean_array_get_size(v_es_3633_);
v___x_3638_ = lean_nat_dec_lt(v_j_3636_, v___x_3637_);
if (v___x_3638_ == 0)
{
lean_dec(v_j_3636_);
lean_dec(v_x_3632_);
lean_dec_ref(v_x_3631_);
return v_x_3628_;
}
else
{
lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3677_; 
lean_inc_ref(v_es_3633_);
v_isSharedCheck_3677_ = !lean_is_exclusive(v_x_3628_);
if (v_isSharedCheck_3677_ == 0)
{
lean_object* v_unused_3678_; 
v_unused_3678_ = lean_ctor_get(v_x_3628_, 0);
lean_dec(v_unused_3678_);
v___x_3640_ = v_x_3628_;
v_isShared_3641_ = v_isSharedCheck_3677_;
goto v_resetjp_3639_;
}
else
{
lean_dec(v_x_3628_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3677_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v_v_3642_; lean_object* v___x_3643_; lean_object* v_xs_x27_3644_; lean_object* v___y_3646_; 
v_v_3642_ = lean_array_fget(v_es_3633_, v_j_3636_);
v___x_3643_ = lean_box(0);
v_xs_x27_3644_ = lean_array_fset(v_es_3633_, v_j_3636_, v___x_3643_);
switch(lean_obj_tag(v_v_3642_))
{
case 0:
{
lean_object* v_key_3651_; lean_object* v_val_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3662_; 
v_key_3651_ = lean_ctor_get(v_v_3642_, 0);
v_val_3652_ = lean_ctor_get(v_v_3642_, 1);
v_isSharedCheck_3662_ = !lean_is_exclusive(v_v_3642_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3654_ = v_v_3642_;
v_isShared_3655_ = v_isSharedCheck_3662_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_val_3652_);
lean_inc(v_key_3651_);
lean_dec(v_v_3642_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3662_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
uint8_t v___x_3656_; 
v___x_3656_ = lean_string_dec_eq(v_x_3631_, v_key_3651_);
if (v___x_3656_ == 0)
{
lean_object* v___x_3657_; lean_object* v___x_3658_; 
lean_del_object(v___x_3654_);
v___x_3657_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3651_, v_val_3652_, v_x_3631_, v_x_3632_);
v___x_3658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3658_, 0, v___x_3657_);
v___y_3646_ = v___x_3658_;
goto v___jp_3645_;
}
else
{
lean_object* v___x_3660_; 
lean_dec(v_val_3652_);
lean_dec(v_key_3651_);
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 1, v_x_3632_);
lean_ctor_set(v___x_3654_, 0, v_x_3631_);
v___x_3660_ = v___x_3654_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_x_3631_);
lean_ctor_set(v_reuseFailAlloc_3661_, 1, v_x_3632_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
v___y_3646_ = v___x_3660_;
goto v___jp_3645_;
}
}
}
}
case 1:
{
lean_object* v_node_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3675_; 
v_node_3663_ = lean_ctor_get(v_v_3642_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v_v_3642_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3665_ = v_v_3642_;
v_isShared_3666_ = v_isSharedCheck_3675_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_node_3663_);
lean_dec(v_v_3642_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3675_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
size_t v___x_3667_; size_t v___x_3668_; size_t v___x_3669_; size_t v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3673_; 
v___x_3667_ = ((size_t)5ULL);
v___x_3668_ = lean_usize_shift_right(v_x_3629_, v___x_3667_);
v___x_3669_ = ((size_t)1ULL);
v___x_3670_ = lean_usize_add(v_x_3630_, v___x_3669_);
v___x_3671_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_node_3663_, v___x_3668_, v___x_3670_, v_x_3631_, v_x_3632_);
if (v_isShared_3666_ == 0)
{
lean_ctor_set(v___x_3665_, 0, v___x_3671_);
v___x_3673_ = v___x_3665_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3671_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
v___y_3646_ = v___x_3673_;
goto v___jp_3645_;
}
}
}
default: 
{
lean_object* v___x_3676_; 
v___x_3676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3676_, 0, v_x_3631_);
lean_ctor_set(v___x_3676_, 1, v_x_3632_);
v___y_3646_ = v___x_3676_;
goto v___jp_3645_;
}
}
v___jp_3645_:
{
lean_object* v___x_3647_; lean_object* v___x_3649_; 
v___x_3647_ = lean_array_fset(v_xs_x27_3644_, v_j_3636_, v___y_3646_);
lean_dec(v_j_3636_);
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 0, v___x_3647_);
v___x_3649_ = v___x_3640_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3647_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
}
}
else
{
lean_object* v_ks_3679_; lean_object* v_vs_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3698_; 
v_ks_3679_ = lean_ctor_get(v_x_3628_, 0);
v_vs_3680_ = lean_ctor_get(v_x_3628_, 1);
v_isSharedCheck_3698_ = !lean_is_exclusive(v_x_3628_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3682_ = v_x_3628_;
v_isShared_3683_ = v_isSharedCheck_3698_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_vs_3680_);
lean_inc(v_ks_3679_);
lean_dec(v_x_3628_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3698_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3685_; 
if (v_isShared_3683_ == 0)
{
v___x_3685_ = v___x_3682_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_ks_3679_);
lean_ctor_set(v_reuseFailAlloc_3697_, 1, v_vs_3680_);
v___x_3685_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
lean_object* v_newNode_3686_; size_t v___x_3687_; uint8_t v___x_3688_; 
v_newNode_3686_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v___x_3685_, v_x_3631_, v_x_3632_);
v___x_3687_ = ((size_t)7ULL);
v___x_3688_ = lean_usize_dec_le(v___x_3687_, v_x_3630_);
if (v___x_3688_ == 0)
{
lean_object* v___x_3689_; lean_object* v___x_3690_; uint8_t v___x_3691_; 
v___x_3689_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3686_);
v___x_3690_ = lean_unsigned_to_nat(4u);
v___x_3691_ = lean_nat_dec_lt(v___x_3689_, v___x_3690_);
lean_dec(v___x_3689_);
if (v___x_3691_ == 0)
{
lean_object* v_ks_3692_; lean_object* v_vs_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v_ks_3692_ = lean_ctor_get(v_newNode_3686_, 0);
lean_inc_ref(v_ks_3692_);
v_vs_3693_ = lean_ctor_get(v_newNode_3686_, 1);
lean_inc_ref(v_vs_3693_);
lean_dec_ref(v_newNode_3686_);
v___x_3694_ = lean_unsigned_to_nat(0u);
v___x_3695_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0);
v___x_3696_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_x_3630_, v_ks_3692_, v_vs_3693_, v___x_3694_, v___x_3695_);
lean_dec_ref(v_vs_3693_);
lean_dec_ref(v_ks_3692_);
return v___x_3696_;
}
else
{
return v_newNode_3686_;
}
}
else
{
return v_newNode_3686_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3628_ = stack[0].m_obj;
size_t v_x_3629_ = stack[1].m_num;
size_t v_x_3630_ = stack[2].m_num;
lean_object* v_x_3631_ = stack[3].m_obj;
lean_object* v_x_3632_ = stack[4].m_obj;
lean_object* v_res_3699_;
v_res_3699_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_3628_, v_x_3629_, v_x_3630_, v_x_3631_, v_x_3632_);
stack->m_obj
 = v_res_3699_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(size_t v_depth_3700_, lean_object* v_keys_3701_, lean_object* v_vals_3702_, lean_object* v_i_3703_, lean_object* v_entries_3704_){
_start:
{
lean_object* v___x_3705_; uint8_t v___x_3706_; 
v___x_3705_ = lean_array_get_size(v_keys_3701_);
v___x_3706_ = lean_nat_dec_lt(v_i_3703_, v___x_3705_);
if (v___x_3706_ == 0)
{
lean_dec(v_i_3703_);
return v_entries_3704_;
}
else
{
lean_object* v_k_3707_; lean_object* v_v_3708_; uint64_t v___x_3709_; size_t v_h_3710_; size_t v___x_3711_; lean_object* v___x_3712_; size_t v___x_3713_; size_t v___x_3714_; size_t v___x_3715_; size_t v_h_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v_k_3707_ = lean_array_fget_borrowed(v_keys_3701_, v_i_3703_);
v_v_3708_ = lean_array_fget_borrowed(v_vals_3702_, v_i_3703_);
v___x_3709_ = lean_string_hash(v_k_3707_);
v_h_3710_ = lean_uint64_to_usize(v___x_3709_);
v___x_3711_ = ((size_t)5ULL);
v___x_3712_ = lean_unsigned_to_nat(1u);
v___x_3713_ = ((size_t)1ULL);
v___x_3714_ = lean_usize_sub(v_depth_3700_, v___x_3713_);
v___x_3715_ = lean_usize_mul(v___x_3711_, v___x_3714_);
v_h_3716_ = lean_usize_shift_right(v_h_3710_, v___x_3715_);
v___x_3717_ = lean_nat_add(v_i_3703_, v___x_3712_);
lean_dec(v_i_3703_);
lean_inc(v_v_3708_);
lean_inc(v_k_3707_);
v___x_3718_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_entries_3704_, v_h_3716_, v_depth_3700_, v_k_3707_, v_v_3708_);
v_i_3703_ = v___x_3717_;
v_entries_3704_ = v___x_3718_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_3700_ = stack[0].m_num;
lean_object* v_keys_3701_ = stack[1].m_obj;
lean_object* v_vals_3702_ = stack[2].m_obj;
lean_object* v_i_3703_ = stack[3].m_obj;
lean_object* v_entries_3704_ = stack[4].m_obj;
lean_object* v_res_3720_;
v_res_3720_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_3700_, v_keys_3701_, v_vals_3702_, v_i_3703_, v_entries_3704_);
stack->m_obj
 = v_res_3720_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_depth_3721_, lean_object* v_keys_3722_, lean_object* v_vals_3723_, lean_object* v_i_3724_, lean_object* v_entries_3725_){
_start:
{
size_t v_depth_boxed_3726_; lean_object* v_res_3727_; 
v_depth_boxed_3726_ = lean_unbox_usize(v_depth_3721_);
lean_dec(v_depth_3721_);
v_res_3727_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_boxed_3726_, v_keys_3722_, v_vals_3723_, v_i_3724_, v_entries_3725_);
lean_dec_ref(v_vals_3723_);
lean_dec_ref(v_keys_3722_);
return v_res_3727_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(lean_object* v_x_3728_, lean_object* v_x_3729_, lean_object* v_x_3730_, lean_object* v_x_3731_, lean_object* v_x_3732_){
_start:
{
size_t v_x_2679__boxed_3733_; size_t v_x_2680__boxed_3734_; lean_object* v_res_3735_; 
v_x_2679__boxed_3733_ = lean_unbox_usize(v_x_3729_);
lean_dec(v_x_3729_);
v_x_2680__boxed_3734_ = lean_unbox_usize(v_x_3730_);
lean_dec(v_x_3730_);
v_res_3735_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_3728_, v_x_2679__boxed_3733_, v_x_2680__boxed_3734_, v_x_3731_, v_x_3732_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(lean_object* v_x_3736_, lean_object* v_x_3737_, lean_object* v_x_3738_){
_start:
{
uint64_t v___x_3739_; size_t v___x_3740_; size_t v___x_3741_; lean_object* v___x_3742_; 
v___x_3739_ = lean_string_hash(v_x_3737_);
v___x_3740_ = lean_uint64_to_usize(v___x_3739_);
v___x_3741_ = ((size_t)1ULL);
v___x_3742_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_3736_, v___x_3740_, v___x_3741_, v_x_3737_, v_x_3738_);
return v___x_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(lean_object* v_params_3744_){
_start:
{
lean_object* v___x_3745_; 
lean_inc(v_params_3744_);
v___x_3745_ = l_Lean_Lsp_instFromJsonSemanticTokensParams_fromJson(v_params_3744_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3761_; 
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3748_ = v___x_3745_;
v_isShared_3749_ = v_isSharedCheck_3761_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3745_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3761_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
uint8_t v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3759_; 
v___x_3750_ = 3;
v___x_3751_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_3752_ = l_Lean_Json_compress(v_params_3744_);
v___x_3753_ = lean_string_append(v___x_3751_, v___x_3752_);
lean_dec_ref(v___x_3752_);
v___x_3754_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0));
v___x_3755_ = lean_string_append(v___x_3753_, v___x_3754_);
v___x_3756_ = lean_string_append(v___x_3755_, v_a_3746_);
lean_dec(v_a_3746_);
v___x_3757_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3757_, 0, v___x_3756_);
lean_ctor_set_uint8(v___x_3757_, sizeof(void*)*1, v___x_3750_);
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 0, v___x_3757_);
v___x_3759_ = v___x_3748_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3757_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
else
{
lean_object* v_a_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3769_; 
lean_dec(v_params_3744_);
v_a_3762_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3764_ = v___x_3745_;
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_a_3762_);
lean_dec(v___x_3745_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3767_; 
if (v_isShared_3765_ == 0)
{
v___x_3767_ = v___x_3764_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_a_3762_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
}
}
lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(lean_object* v_params_3770_){
_start:
{
lean_object* v___x_3772_; 
v___x_3772_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_params_3770_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_object* v_a_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3780_; 
v_a_3773_ = lean_ctor_get(v___x_3772_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3772_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3775_ = v___x_3772_;
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_a_3773_);
lean_dec(v___x_3772_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v___x_3778_; 
if (v_isShared_3776_ == 0)
{
lean_ctor_set_tag(v___x_3775_, 1);
v___x_3778_ = v___x_3775_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_a_3773_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
else
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3788_; 
v_a_3781_ = lean_ctor_get(v___x_3772_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3772_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3772_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3772_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3786_; 
if (v_isShared_3784_ == 0)
{
lean_ctor_set_tag(v___x_3783_, 0);
v___x_3786_ = v___x_3783_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_a_3781_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_3770_ = stack[0].m_obj;
lean_object* v_res_3789_;
v_res_3789_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_3770_);
stack->m_obj
 = v_res_3789_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg___boxed(lean_object* v_params_3790_, lean_object* v_a_3791_){
_start:
{
lean_object* v_res_3792_; 
v_res_3792_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_3790_);
return v_res_3792_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(lean_object* v_method_3793_, lean_object* v_inst_3794_, lean_object* v_handler_3795_, lean_object* v_param_3796_, lean_object* v_state_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v___x_3800_; 
v___x_3800_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_param_3796_);
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_object* v_a_3801_; lean_object* v___x_3802_; 
v_a_3801_ = lean_ctor_get(v___x_3800_, 0);
lean_inc(v_a_3801_);
lean_dec_ref_known(v___x_3800_, 1);
v___x_3802_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_3793_, v_state_3797_, lean_box(0), v_inst_3794_, v___y_3798_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v_a_3803_; lean_object* v___x_3804_; 
v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
lean_inc(v_a_3803_);
lean_dec_ref_known(v___x_3802_, 1);
lean_inc_ref(v___y_3798_);
v___x_3804_ = lean_apply_4(v_handler_3795_, v_a_3801_, v_a_3803_, v___y_3798_, lean_box(0));
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3828_; 
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3807_ = v___x_3804_;
v_isShared_3808_ = v_isSharedCheck_3828_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3804_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3828_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v_fst_3809_; lean_object* v_snd_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3827_; 
v_fst_3809_ = lean_ctor_get(v_a_3805_, 0);
v_snd_3810_ = lean_ctor_get(v_a_3805_, 1);
v_isSharedCheck_3827_ = !lean_is_exclusive(v_a_3805_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3812_ = v_a_3805_;
v_isShared_3813_ = v_isSharedCheck_3827_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_snd_3810_);
lean_inc(v_fst_3809_);
lean_dec(v_a_3805_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3827_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v_response_3814_; uint8_t v_isComplete_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3821_; 
v_response_3814_ = lean_ctor_get(v_fst_3809_, 0);
lean_inc(v_response_3814_);
v_isComplete_3815_ = lean_ctor_get_uint8(v_fst_3809_, sizeof(void*)*1);
lean_dec(v_fst_3809_);
v___x_3816_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_response_3814_);
lean_inc(v___x_3816_);
v___x_3817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3816_);
v___x_3818_ = l_Lean_Json_compress(v___x_3816_);
v___x_3819_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3819_, 0, v___x_3817_);
lean_ctor_set(v___x_3819_, 1, v___x_3818_);
lean_ctor_set_uint8(v___x_3819_, sizeof(void*)*2, v_isComplete_3815_);
if (v_isShared_3813_ == 0)
{
lean_ctor_set(v___x_3812_, 0, v_inst_3794_);
v___x_3821_ = v___x_3812_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_inst_3794_);
lean_ctor_set(v_reuseFailAlloc_3826_, 1, v_snd_3810_);
v___x_3821_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
lean_object* v___x_3822_; lean_object* v___x_3824_; 
v___x_3822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3819_);
lean_ctor_set(v___x_3822_, 1, v___x_3821_);
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 0, v___x_3822_);
v___x_3824_ = v___x_3807_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v___x_3822_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
}
}
else
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3836_; 
lean_dec(v_inst_3794_);
v_a_3829_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3831_ = v___x_3804_;
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___x_3804_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3834_; 
if (v_isShared_3832_ == 0)
{
v___x_3834_ = v___x_3831_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_a_3829_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
}
else
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3844_; 
lean_dec(v_a_3801_);
lean_dec_ref(v_handler_3795_);
lean_dec(v_inst_3794_);
v_a_3837_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3839_ = v___x_3802_;
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3802_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
if (v_isShared_3840_ == 0)
{
v___x_3842_ = v___x_3839_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
return v___x_3842_;
}
}
}
}
else
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3852_; 
lean_dec_ref(v_handler_3795_);
lean_dec(v_inst_3794_);
v_a_3845_ = lean_ctor_get(v___x_3800_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3800_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3847_ = v___x_3800_;
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3800_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3850_; 
if (v_isShared_3848_ == 0)
{
v___x_3850_ = v___x_3847_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3845_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_3793_ = stack[0].m_obj;
lean_object* v_inst_3794_ = stack[1].m_obj;
lean_object* v_handler_3795_ = stack[2].m_obj;
lean_object* v_param_3796_ = stack[3].m_obj;
lean_object* v_state_3797_ = stack[4].m_obj;
lean_object* v___y_3798_ = stack[5].m_obj;
lean_object* v_res_3853_;
v_res_3853_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(v_method_3793_, v_inst_3794_, v_handler_3795_, v_param_3796_, v_state_3797_, v___y_3798_);
stack->m_obj
 = v_res_3853_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed(lean_object* v_method_3854_, lean_object* v_inst_3855_, lean_object* v_handler_3856_, lean_object* v_param_3857_, lean_object* v_state_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_){
_start:
{
lean_object* v_res_3861_; 
v_res_3861_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(v_method_3854_, v_inst_3855_, v_handler_3856_, v_param_3857_, v_state_3858_, v___y_3859_);
lean_dec_ref(v___y_3859_);
lean_dec(v_state_3858_);
lean_dec_ref(v_method_3854_);
return v_res_3861_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(lean_object* v_mutex_3862_, lean_object* v_a_x3f_3863_){
_start:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; 
v___x_3865_ = lean_io_basemutex_unlock(v_mutex_3862_);
v___x_3866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3866_, 0, v___x_3865_);
return v___x_3866_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_3862_ = stack[0].m_obj;
lean_object* v_a_x3f_3863_ = stack[1].m_obj;
lean_object* v_res_3867_;
v_res_3867_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_3862_, v_a_x3f_3863_);
stack->m_obj
 = v_res_3867_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0___boxed(lean_object* v_mutex_3868_, lean_object* v_a_x3f_3869_, lean_object* v___y_3870_){
_start:
{
lean_object* v_res_3871_; 
v_res_3871_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_3868_, v_a_x3f_3869_);
lean_dec(v_a_x3f_3869_);
lean_dec(v_mutex_3868_);
return v_res_3871_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(lean_object* v_mutex_3872_, lean_object* v_k_3873_, lean_object* v___y_3874_){
_start:
{
lean_object* v_ref_3876_; lean_object* v_mutex_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
v_ref_3876_ = lean_ctor_get(v_mutex_3872_, 0);
lean_inc(v_ref_3876_);
v_mutex_3877_ = lean_ctor_get(v_mutex_3872_, 1);
lean_inc(v_mutex_3877_);
lean_dec_ref(v_mutex_3872_);
v___x_3878_ = lean_io_basemutex_lock(v_mutex_3877_);
lean_inc_ref(v___y_3874_);
v___x_3879_ = lean_apply_3(v_k_3873_, v_ref_3876_, v___y_3874_, lean_box(0));
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3896_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3882_ = v___x_3879_;
v_isShared_3883_ = v_isSharedCheck_3896_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3879_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3896_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
lean_inc(v_a_3880_);
if (v_isShared_3883_ == 0)
{
lean_ctor_set_tag(v___x_3882_, 1);
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_a_3880_);
v___x_3885_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
lean_object* v___x_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3893_; 
v___x_3886_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_3877_, v___x_3885_);
lean_dec_ref(v___x_3885_);
lean_dec(v_mutex_3877_);
v_isSharedCheck_3893_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3893_ == 0)
{
lean_object* v_unused_3894_; 
v_unused_3894_ = lean_ctor_get(v___x_3886_, 0);
lean_dec(v_unused_3894_);
v___x_3888_ = v___x_3886_;
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
else
{
lean_dec(v___x_3886_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3891_; 
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 0, v_a_3880_);
v___x_3891_ = v___x_3888_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v_a_3880_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
return v___x_3891_;
}
}
}
}
}
else
{
lean_object* v_a_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3906_; 
v_a_3897_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3897_);
lean_dec_ref_known(v___x_3879_, 1);
v___x_3898_ = lean_box(0);
v___x_3899_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_3877_, v___x_3898_);
lean_dec(v_mutex_3877_);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3906_ == 0)
{
lean_object* v_unused_3907_; 
v_unused_3907_ = lean_ctor_get(v___x_3899_, 0);
lean_dec(v_unused_3907_);
v___x_3901_ = v___x_3899_;
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
else
{
lean_dec(v___x_3899_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3904_; 
if (v_isShared_3902_ == 0)
{
lean_ctor_set_tag(v___x_3901_, 1);
lean_ctor_set(v___x_3901_, 0, v_a_3897_);
v___x_3904_ = v___x_3901_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_a_3897_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_3872_ = stack[0].m_obj;
lean_object* v_k_3873_ = stack[1].m_obj;
lean_object* v___y_3874_ = stack[2].m_obj;
lean_object* v_res_3908_;
v_res_3908_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_3872_, v_k_3873_, v___y_3874_);
stack->m_obj
 = v_res_3908_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_mutex_3909_, lean_object* v_k_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_){
_start:
{
lean_object* v_res_3913_; 
v_res_3913_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_3909_, v_k_3910_, v___y_3911_);
lean_dec_ref(v___y_3911_);
return v_res_3913_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(lean_object* v_val_3914_, lean_object* v___f_3915_, lean_object* v_param_3916_, lean_object* v___x_3917_, lean_object* v_x_3918_, lean_object* v___y_3919_){
_start:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3921_ = lean_st_ref_get(v_val_3914_);
lean_inc_ref(v___y_3919_);
v___x_3922_ = lean_apply_4(v___f_3915_, v_param_3916_, v___x_3921_, v___y_3919_, lean_box(0));
if (lean_obj_tag(v___x_3922_) == 0)
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3932_; 
v_a_3923_ = lean_ctor_get(v___x_3922_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3922_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3925_ = v___x_3922_;
v_isShared_3926_ = v_isSharedCheck_3932_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3922_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3932_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v_snd_3927_; lean_object* v___x_3928_; lean_object* v___x_3930_; 
v_snd_3927_ = lean_ctor_get(v_a_3923_, 1);
lean_inc(v_snd_3927_);
lean_dec(v_a_3923_);
v___x_3928_ = lean_st_ref_swap(v_val_3914_, v_snd_3927_);
lean_dec(v___x_3928_);
if (v_isShared_3926_ == 0)
{
lean_ctor_set(v___x_3925_, 0, v___x_3917_);
v___x_3930_ = v___x_3925_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v___x_3917_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
else
{
lean_object* v_a_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3940_; 
v_a_3933_ = lean_ctor_get(v___x_3922_, 0);
v_isSharedCheck_3940_ = !lean_is_exclusive(v___x_3922_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3935_ = v___x_3922_;
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_a_3933_);
lean_dec(v___x_3922_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v___x_3938_; 
if (v_isShared_3936_ == 0)
{
v___x_3938_ = v___x_3935_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_a_3933_);
v___x_3938_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
return v___x_3938_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_3914_ = stack[0].m_obj;
lean_object* v___f_3915_ = stack[1].m_obj;
lean_object* v_param_3916_ = stack[2].m_obj;
lean_object* v___x_3917_ = stack[3].m_obj;
lean_object* v_x_3918_ = stack[4].m_obj;
lean_object* v___y_3919_ = stack[5].m_obj;
lean_object* v_res_3941_;
v_res_3941_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(v_val_3914_, v___f_3915_, v_param_3916_, v___x_3917_, v_x_3918_, v___y_3919_);
stack->m_obj
 = v_res_3941_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed(lean_object* v_val_3942_, lean_object* v___f_3943_, lean_object* v_param_3944_, lean_object* v___x_3945_, lean_object* v_x_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
lean_object* v_res_3949_; 
v_res_3949_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(v_val_3942_, v___f_3943_, v_param_3944_, v___x_3945_, v_x_3946_, v___y_3947_);
lean_dec_ref(v___y_3947_);
lean_dec(v_val_3942_);
return v_res_3949_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(lean_object* v___f_3950_, lean_object* v___f_3951_, lean_object* v___x_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3956_ = lean_st_ref_get(v___y_3953_);
v___x_3957_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_3956_, v___f_3950_, v___y_3954_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v_a_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3967_; 
v_a_3958_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_3967_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3960_ = v___x_3957_;
v_isShared_3961_ = v_isSharedCheck_3967_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_a_3958_);
lean_dec(v___x_3957_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3967_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3965_; 
v___x_3962_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_3951_, v_a_3958_);
v___x_3963_ = lean_st_ref_swap(v___y_3953_, v___x_3962_);
lean_dec(v___x_3963_);
if (v_isShared_3961_ == 0)
{
lean_ctor_set(v___x_3960_, 0, v___x_3952_);
v___x_3965_ = v___x_3960_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v___x_3952_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
}
else
{
lean_object* v_a_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_3975_; 
lean_dec_ref(v___f_3951_);
v_a_3968_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_3975_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_3975_ == 0)
{
v___x_3970_ = v___x_3957_;
v_isShared_3971_ = v_isSharedCheck_3975_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_a_3968_);
lean_dec(v___x_3957_);
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
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_3950_ = stack[0].m_obj;
lean_object* v___f_3951_ = stack[1].m_obj;
lean_object* v___x_3952_ = stack[2].m_obj;
lean_object* v___y_3953_ = stack[3].m_obj;
lean_object* v___y_3954_ = stack[4].m_obj;
lean_object* v_res_3976_;
v_res_3976_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(v___f_3950_, v___f_3951_, v___x_3952_, v___y_3953_, v___y_3954_);
stack->m_obj
 = v_res_3976_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed(lean_object* v___f_3977_, lean_object* v___f_3978_, lean_object* v___x_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(v___f_3977_, v___f_3978_, v___x_3979_, v___y_3980_, v___y_3981_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
return v_res_3983_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(lean_object* v_val_3984_, lean_object* v___f_3985_, lean_object* v___x_3986_, lean_object* v___f_3987_, lean_object* v_val_3988_, lean_object* v_param_3989_, lean_object* v___y_3990_){
_start:
{
lean_object* v___f_3992_; lean_object* v___f_3993_; lean_object* v___x_3994_; 
v___f_3992_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed), 7, 4);
lean_closure_set(v___f_3992_, 0, v_val_3984_);
lean_closure_set(v___f_3992_, 1, v___f_3985_);
lean_closure_set(v___f_3992_, 2, v_param_3989_);
lean_closure_set(v___f_3992_, 3, v___x_3986_);
v___f_3993_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed), 6, 3);
lean_closure_set(v___f_3993_, 0, v___f_3992_);
lean_closure_set(v___f_3993_, 1, v___f_3987_);
lean_closure_set(v___f_3993_, 2, v___x_3986_);
v___x_3994_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_3988_, v___f_3993_, v___y_3990_);
return v___x_3994_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_3984_ = stack[0].m_obj;
lean_object* v___f_3985_ = stack[1].m_obj;
lean_object* v___x_3986_ = stack[2].m_obj;
lean_object* v___f_3987_ = stack[3].m_obj;
lean_object* v_val_3988_ = stack[4].m_obj;
lean_object* v_param_3989_ = stack[5].m_obj;
lean_object* v___y_3990_ = stack[6].m_obj;
lean_object* v_res_3995_;
v_res_3995_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(v_val_3984_, v___f_3985_, v___x_3986_, v___f_3987_, v_val_3988_, v_param_3989_, v___y_3990_);
stack->m_obj
 = v_res_3995_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed(lean_object* v_val_3996_, lean_object* v___f_3997_, lean_object* v___x_3998_, lean_object* v___f_3999_, lean_object* v_val_4000_, lean_object* v_param_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_){
_start:
{
lean_object* v_res_4004_; 
v_res_4004_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(v_val_3996_, v___f_3997_, v___x_3998_, v___f_3999_, v_val_4000_, v_param_4001_, v___y_4002_);
lean_dec_ref(v___y_4002_);
return v_res_4004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(lean_object* v___x_4005_, lean_object* v_x_4006_){
_start:
{
return v___x_4005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3___boxed(lean_object* v___x_4007_, lean_object* v_x_4008_){
_start:
{
lean_object* v_res_4009_; 
v_res_4009_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(v___x_4007_, v_x_4008_);
lean_dec_ref(v_x_4008_);
return v_res_4009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__0(lean_object* v_j_4010_){
_start:
{
lean_object* v___x_4011_; 
v___x_4011_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_j_4010_);
if (lean_obj_tag(v___x_4011_) == 0)
{
lean_object* v_a_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4019_; 
v_a_4012_ = lean_ctor_get(v___x_4011_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4014_ = v___x_4011_;
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_a_4012_);
lean_dec(v___x_4011_);
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
v_reuseFailAlloc_4018_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4027_; 
v_a_4020_ = lean_ctor_get(v___x_4011_, 0);
v_isSharedCheck_4027_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4022_ = v___x_4011_;
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_a_4020_);
lean_dec(v___x_4011_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4025_; 
if (v_isShared_4023_ == 0)
{
v___x_4025_ = v___x_4022_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_a_4020_);
v___x_4025_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
return v___x_4025_;
}
}
}
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(lean_object* v_val_4028_, lean_object* v___f_4029_, lean_object* v_param_4030_, lean_object* v_x_4031_, lean_object* v___y_4032_){
_start:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4034_ = lean_st_ref_get(v_val_4028_);
lean_inc_ref(v___y_4032_);
v___x_4035_ = lean_apply_4(v___f_4029_, v_param_4030_, v___x_4034_, v___y_4032_, lean_box(0));
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v_a_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4046_; 
v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4038_ = v___x_4035_;
v_isShared_4039_ = v_isSharedCheck_4046_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_a_4036_);
lean_dec(v___x_4035_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4046_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v_fst_4040_; lean_object* v_snd_4041_; lean_object* v___x_4042_; lean_object* v___x_4044_; 
v_fst_4040_ = lean_ctor_get(v_a_4036_, 0);
lean_inc(v_fst_4040_);
v_snd_4041_ = lean_ctor_get(v_a_4036_, 1);
lean_inc(v_snd_4041_);
lean_dec(v_a_4036_);
v___x_4042_ = lean_st_ref_swap(v_val_4028_, v_snd_4041_);
lean_dec(v___x_4042_);
if (v_isShared_4039_ == 0)
{
lean_ctor_set(v___x_4038_, 0, v_fst_4040_);
v___x_4044_ = v___x_4038_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_fst_4040_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
}
}
}
else
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4054_; 
v_a_4047_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4049_ = v___x_4035_;
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_4035_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v___x_4052_; 
if (v_isShared_4050_ == 0)
{
v___x_4052_ = v___x_4049_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_a_4047_);
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
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_4028_ = stack[0].m_obj;
lean_object* v___f_4029_ = stack[1].m_obj;
lean_object* v_param_4030_ = stack[2].m_obj;
lean_object* v_x_4031_ = stack[3].m_obj;
lean_object* v___y_4032_ = stack[4].m_obj;
lean_object* v_res_4055_;
v_res_4055_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(v_val_4028_, v___f_4029_, v_param_4030_, v_x_4031_, v___y_4032_);
stack->m_obj
 = v_res_4055_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed(lean_object* v_val_4056_, lean_object* v___f_4057_, lean_object* v_param_4058_, lean_object* v_x_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v_res_4062_; 
v_res_4062_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(v_val_4056_, v___f_4057_, v_param_4058_, v_x_4059_, v___y_4060_);
lean_dec_ref(v___y_4060_);
lean_dec(v_val_4056_);
return v_res_4062_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(lean_object* v___f_4063_, lean_object* v___f_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
lean_object* v___x_4068_; lean_object* v___x_4069_; 
v___x_4068_ = lean_st_ref_get(v___y_4065_);
v___x_4069_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4068_, v___f_4063_, v___y_4066_);
if (lean_obj_tag(v___x_4069_) == 0)
{
lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4079_; 
v_a_4070_ = lean_ctor_get(v___x_4069_, 0);
v_isSharedCheck_4079_ = !lean_is_exclusive(v___x_4069_);
if (v_isSharedCheck_4079_ == 0)
{
v___x_4072_ = v___x_4069_;
v_isShared_4073_ = v_isSharedCheck_4079_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v___x_4069_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4079_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4077_; 
lean_inc(v_a_4070_);
v___x_4074_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4064_, v_a_4070_);
v___x_4075_ = lean_st_ref_swap(v___y_4065_, v___x_4074_);
lean_dec(v___x_4075_);
if (v_isShared_4073_ == 0)
{
v___x_4077_ = v___x_4072_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v_a_4070_);
v___x_4077_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
return v___x_4077_;
}
}
}
else
{
lean_dec_ref(v___f_4064_);
return v___x_4069_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_4063_ = stack[0].m_obj;
lean_object* v___f_4064_ = stack[1].m_obj;
lean_object* v___y_4065_ = stack[2].m_obj;
lean_object* v___y_4066_ = stack[3].m_obj;
lean_object* v_res_4080_;
v_res_4080_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(v___f_4063_, v___f_4064_, v___y_4065_, v___y_4066_);
stack->m_obj
 = v_res_4080_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed(lean_object* v___f_4081_, lean_object* v___f_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_){
_start:
{
lean_object* v_res_4086_; 
v_res_4086_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(v___f_4081_, v___f_4082_, v___y_4083_, v___y_4084_);
lean_dec_ref(v___y_4084_);
lean_dec(v___y_4083_);
return v_res_4086_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(lean_object* v_val_4087_, lean_object* v___f_4088_, lean_object* v___f_4089_, lean_object* v_val_4090_, lean_object* v_param_4091_, lean_object* v___y_4092_){
_start:
{
lean_object* v___f_4094_; lean_object* v___f_4095_; lean_object* v___x_4096_; 
v___f_4094_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_4094_, 0, v_val_4087_);
lean_closure_set(v___f_4094_, 1, v___f_4088_);
lean_closure_set(v___f_4094_, 2, v_param_4091_);
v___f_4095_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed), 5, 2);
lean_closure_set(v___f_4095_, 0, v___f_4094_);
lean_closure_set(v___f_4095_, 1, v___f_4089_);
v___x_4096_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_4090_, v___f_4095_, v___y_4092_);
return v___x_4096_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_4087_ = stack[0].m_obj;
lean_object* v___f_4088_ = stack[1].m_obj;
lean_object* v___f_4089_ = stack[2].m_obj;
lean_object* v_val_4090_ = stack[3].m_obj;
lean_object* v_param_4091_ = stack[4].m_obj;
lean_object* v___y_4092_ = stack[5].m_obj;
lean_object* v_res_4097_;
v_res_4097_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(v_val_4087_, v___f_4088_, v___f_4089_, v_val_4090_, v_param_4091_, v___y_4092_);
stack->m_obj
 = v_res_4097_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed(lean_object* v_val_4098_, lean_object* v___f_4099_, lean_object* v___f_4100_, lean_object* v_val_4101_, lean_object* v_param_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_){
_start:
{
lean_object* v_res_4105_; 
v_res_4105_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(v_val_4098_, v___f_4099_, v___f_4100_, v_val_4101_, v_param_4102_, v___y_4103_);
lean_dec_ref(v___y_4103_);
return v_res_4105_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(lean_object* v_method_4106_, lean_object* v_inst_4107_, lean_object* v_onDidChange_4108_, lean_object* v_param_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_){
_start:
{
lean_object* v___x_4113_; 
v___x_4113_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_4106_, v___y_4110_, lean_box(0), v_inst_4107_, v___y_4111_);
if (lean_obj_tag(v___x_4113_) == 0)
{
lean_object* v_a_4114_; lean_object* v___x_4115_; 
v_a_4114_ = lean_ctor_get(v___x_4113_, 0);
lean_inc(v_a_4114_);
lean_dec_ref_known(v___x_4113_, 1);
lean_inc_ref(v___y_4111_);
v___x_4115_ = lean_apply_4(v_onDidChange_4108_, v_param_4109_, v_a_4114_, v___y_4111_, lean_box(0));
if (lean_obj_tag(v___x_4115_) == 0)
{
lean_object* v_a_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4134_; 
v_a_4116_ = lean_ctor_get(v___x_4115_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4115_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4118_ = v___x_4115_;
v_isShared_4119_ = v_isSharedCheck_4134_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_a_4116_);
lean_dec(v___x_4115_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4134_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v_snd_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4132_; 
v_snd_4120_ = lean_ctor_get(v_a_4116_, 1);
v_isSharedCheck_4132_ = !lean_is_exclusive(v_a_4116_);
if (v_isSharedCheck_4132_ == 0)
{
lean_object* v_unused_4133_; 
v_unused_4133_ = lean_ctor_get(v_a_4116_, 0);
lean_dec(v_unused_4133_);
v___x_4122_ = v_a_4116_;
v_isShared_4123_ = v_isSharedCheck_4132_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_snd_4120_);
lean_dec(v_a_4116_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4132_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___x_4125_; 
if (v_isShared_4123_ == 0)
{
lean_ctor_set(v___x_4122_, 0, v_inst_4107_);
v___x_4125_ = v___x_4122_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_inst_4107_);
lean_ctor_set(v_reuseFailAlloc_4131_, 1, v_snd_4120_);
v___x_4125_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4129_; 
v___x_4126_ = lean_box(0);
v___x_4127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4126_);
lean_ctor_set(v___x_4127_, 1, v___x_4125_);
if (v_isShared_4119_ == 0)
{
lean_ctor_set(v___x_4118_, 0, v___x_4127_);
v___x_4129_ = v___x_4118_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v___x_4127_);
v___x_4129_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
return v___x_4129_;
}
}
}
}
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4142_; 
lean_dec(v_inst_4107_);
v_a_4135_ = lean_ctor_get(v___x_4115_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4115_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4137_ = v___x_4115_;
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4115_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4140_; 
if (v_isShared_4138_ == 0)
{
v___x_4140_ = v___x_4137_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_a_4135_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
else
{
lean_object* v_a_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4150_; 
lean_dec_ref(v_param_4109_);
lean_dec_ref(v_onDidChange_4108_);
lean_dec(v_inst_4107_);
v_a_4143_ = lean_ctor_get(v___x_4113_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v___x_4113_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4145_ = v___x_4113_;
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_a_4143_);
lean_dec(v___x_4113_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4148_; 
if (v_isShared_4146_ == 0)
{
v___x_4148_ = v___x_4145_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v_a_4143_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
return v___x_4148_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_4106_ = stack[0].m_obj;
lean_object* v_inst_4107_ = stack[1].m_obj;
lean_object* v_onDidChange_4108_ = stack[2].m_obj;
lean_object* v_param_4109_ = stack[3].m_obj;
lean_object* v___y_4110_ = stack[4].m_obj;
lean_object* v___y_4111_ = stack[5].m_obj;
lean_object* v_res_4151_;
v_res_4151_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(v_method_4106_, v_inst_4107_, v_onDidChange_4108_, v_param_4109_, v___y_4110_, v___y_4111_);
stack->m_obj
 = v_res_4151_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed(lean_object* v_method_4152_, lean_object* v_inst_4153_, lean_object* v_onDidChange_4154_, lean_object* v_param_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_){
_start:
{
lean_object* v_res_4159_; 
v_res_4159_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(v_method_4152_, v_inst_4153_, v_onDidChange_4154_, v_param_4155_, v___y_4156_, v___y_4157_);
lean_dec_ref(v___y_4157_);
lean_dec(v___y_4156_);
lean_dec_ref(v_method_4152_);
return v_res_4159_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_4167_; lean_object* v___x_4168_; 
v___x_4167_ = lean_box(0);
v___x_4168_ = lean_task_pure(v___x_4167_);
return v___x_4168_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(lean_object* v_method_4169_, lean_object* v_completeness_4170_, lean_object* v_inst_4171_, lean_object* v_initState_4172_, lean_object* v_handler_4173_, lean_object* v_onDidChange_4174_){
_start:
{
lean_object* v___f_4176_; lean_object* v___f_4177_; lean_object* v___f_4178_; uint8_t v___x_4179_; 
v___f_4176_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0));
lean_inc_n(v_inst_4171_, 2);
lean_inc_ref_n(v_method_4169_, 2);
v___f_4177_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4177_, 0, v_method_4169_);
lean_closure_set(v___f_4177_, 1, v_inst_4171_);
lean_closure_set(v___f_4177_, 2, v_handler_4173_);
v___f_4178_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4178_, 0, v_method_4169_);
lean_closure_set(v___f_4178_, 1, v_inst_4171_);
lean_closure_set(v___f_4178_, 2, v_onDidChange_4174_);
v___x_4179_ = l_Lean_initializing();
if (v___x_4179_ == 0)
{
lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; 
lean_dec_ref(v___f_4178_);
lean_dec_ref(v___f_4177_);
lean_dec(v_initState_4172_);
lean_dec(v_inst_4171_);
lean_dec(v_completeness_4170_);
v___x_4180_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1));
v___x_4181_ = lean_string_append(v___x_4180_, v_method_4169_);
lean_dec_ref(v_method_4169_);
v___x_4182_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2));
v___x_4183_ = lean_string_append(v___x_4181_, v___x_4182_);
v___x_4184_ = lean_mk_io_user_error(v___x_4183_);
v___x_4185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4184_);
return v___x_4185_;
}
else
{
lean_object* v___x_4186_; lean_object* v___f_4187_; lean_object* v___f_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___f_4193_; lean_object* v___f_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4186_ = lean_box(0);
v___f_4187_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__3));
v___f_4188_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__4));
v___x_4189_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5);
v___x_4190_ = l_Std_Mutex_new___redArg(v___x_4189_);
v___x_4191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4191_, 0, v_inst_4171_);
lean_ctor_set(v___x_4191_, 1, v_initState_4172_);
lean_inc_ref(v___x_4191_);
v___x_4192_ = lean_st_mk_ref(v___x_4191_);
lean_inc_ref_n(v___x_4190_, 2);
lean_inc_ref(v___f_4177_);
lean_inc_n(v___x_4192_, 2);
v___f_4193_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_4193_, 0, v___x_4192_);
lean_closure_set(v___f_4193_, 1, v___f_4177_);
lean_closure_set(v___f_4193_, 2, v___f_4187_);
lean_closure_set(v___f_4193_, 3, v___x_4190_);
lean_inc_ref(v___f_4178_);
v___f_4194_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed), 8, 5);
lean_closure_set(v___f_4194_, 0, v___x_4192_);
lean_closure_set(v___f_4194_, 1, v___f_4178_);
lean_closure_set(v___f_4194_, 2, v___x_4186_);
lean_closure_set(v___f_4194_, 3, v___f_4188_);
lean_closure_set(v___f_4194_, 4, v___x_4190_);
v___x_4195_ = l_Lean_Server_statefulRequestHandlers;
v___x_4196_ = lean_st_ref_take(v___x_4195_);
v___x_4197_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4197_, 0, v___f_4176_);
lean_ctor_set(v___x_4197_, 1, v___f_4177_);
lean_ctor_set(v___x_4197_, 2, v___f_4193_);
lean_ctor_set(v___x_4197_, 3, v___f_4178_);
lean_ctor_set(v___x_4197_, 4, v___f_4194_);
lean_ctor_set(v___x_4197_, 5, v___x_4190_);
lean_ctor_set(v___x_4197_, 6, v___x_4191_);
lean_ctor_set(v___x_4197_, 7, v___x_4192_);
lean_ctor_set(v___x_4197_, 8, v_completeness_4170_);
v___x_4198_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_4196_, v_method_4169_, v___x_4197_);
v___x_4199_ = lean_st_ref_put(v___x_4195_, v___x_4198_);
v___x_4200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4200_, 0, v___x_4199_);
return v___x_4200_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_4169_ = stack[0].m_obj;
lean_object* v_completeness_4170_ = stack[1].m_obj;
lean_object* v_inst_4171_ = stack[2].m_obj;
lean_object* v_initState_4172_ = stack[3].m_obj;
lean_object* v_handler_4173_ = stack[4].m_obj;
lean_object* v_onDidChange_4174_ = stack[5].m_obj;
lean_object* v_res_4201_;
v_res_4201_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4169_, v_completeness_4170_, v_inst_4171_, v_initState_4172_, v_handler_4173_, v_onDidChange_4174_);
stack->m_obj
 = v_res_4201_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___boxed(lean_object* v_method_4202_, lean_object* v_completeness_4203_, lean_object* v_inst_4204_, lean_object* v_initState_4205_, lean_object* v_handler_4206_, lean_object* v_onDidChange_4207_, lean_object* v_a_4208_){
_start:
{
lean_object* v_res_4209_; 
v_res_4209_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4202_, v_completeness_4203_, v_inst_4204_, v_initState_4205_, v_handler_4206_, v_onDidChange_4207_);
return v_res_4209_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(lean_object* v_method_4211_, lean_object* v_completeness_4212_, lean_object* v_inst_4213_, lean_object* v_initState_4214_, lean_object* v_handler_4215_, lean_object* v_onDidChange_4216_){
_start:
{
lean_object* v___x_4218_; lean_object* v___x_4219_; uint8_t v___x_4220_; 
v___x_4218_ = l_Lean_Server_requestHandlers;
v___x_4219_ = lean_st_ref_get(v___x_4218_);
v___x_4220_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_4219_, v_method_4211_);
lean_dec(v___x_4219_);
if (v___x_4220_ == 0)
{
lean_object* v___x_4221_; 
v___x_4221_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4211_, v_completeness_4212_, v_inst_4213_, v_initState_4214_, v_handler_4215_, v_onDidChange_4216_);
return v___x_4221_;
}
else
{
lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
lean_dec_ref(v_onDidChange_4216_);
lean_dec_ref(v_handler_4215_);
lean_dec(v_initState_4214_);
lean_dec(v_inst_4213_);
lean_dec(v_completeness_4212_);
v___x_4222_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1));
v___x_4223_ = lean_string_append(v___x_4222_, v_method_4211_);
lean_dec_ref(v_method_4211_);
v___x_4224_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_4225_ = lean_string_append(v___x_4223_, v___x_4224_);
v___x_4226_ = lean_mk_io_user_error(v___x_4225_);
v___x_4227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4227_, 0, v___x_4226_);
return v___x_4227_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_4211_ = stack[0].m_obj;
lean_object* v_completeness_4212_ = stack[1].m_obj;
lean_object* v_inst_4213_ = stack[2].m_obj;
lean_object* v_initState_4214_ = stack[3].m_obj;
lean_object* v_handler_4215_ = stack[4].m_obj;
lean_object* v_onDidChange_4216_ = stack[5].m_obj;
lean_object* v_res_4228_;
v_res_4228_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4211_, v_completeness_4212_, v_inst_4213_, v_initState_4214_, v_handler_4215_, v_onDidChange_4216_);
stack->m_obj
 = v_res_4228_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___boxed(lean_object* v_method_4229_, lean_object* v_completeness_4230_, lean_object* v_inst_4231_, lean_object* v_initState_4232_, lean_object* v_handler_4233_, lean_object* v_onDidChange_4234_, lean_object* v_a_4235_){
_start:
{
lean_object* v_res_4236_; 
v_res_4236_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4229_, v_completeness_4230_, v_inst_4231_, v_initState_4232_, v_handler_4233_, v_onDidChange_4234_);
return v_res_4236_;
}
}
lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(lean_object* v_method_4237_, lean_object* v_refreshMethod_4238_, lean_object* v_refreshIntervalMs_4239_, lean_object* v_inst_4240_, lean_object* v_initState_4241_, lean_object* v_handler_4242_, lean_object* v_onDidChange_4243_){
_start:
{
lean_object* v___x_4245_; lean_object* v___x_4246_; 
v___x_4245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4245_, 0, v_refreshMethod_4238_);
lean_ctor_set(v___x_4245_, 1, v_refreshIntervalMs_4239_);
v___x_4246_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4237_, v___x_4245_, v_inst_4240_, v_initState_4241_, v_handler_4242_, v_onDidChange_4243_);
return v___x_4246_;
}
}
LEAN_EXPORT void l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_4237_ = stack[0].m_obj;
lean_object* v_refreshMethod_4238_ = stack[1].m_obj;
lean_object* v_refreshIntervalMs_4239_ = stack[2].m_obj;
lean_object* v_inst_4240_ = stack[3].m_obj;
lean_object* v_initState_4241_ = stack[4].m_obj;
lean_object* v_handler_4242_ = stack[5].m_obj;
lean_object* v_onDidChange_4243_ = stack[6].m_obj;
lean_object* v_res_4247_;
v_res_4247_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_4237_, v_refreshMethod_4238_, v_refreshIntervalMs_4239_, v_inst_4240_, v_initState_4241_, v_handler_4242_, v_onDidChange_4243_);
stack->m_obj
 = v_res_4247_;
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_method_4248_, lean_object* v_refreshMethod_4249_, lean_object* v_refreshIntervalMs_4250_, lean_object* v_inst_4251_, lean_object* v_initState_4252_, lean_object* v_handler_4253_, lean_object* v_onDidChange_4254_, lean_object* v_a_4255_){
_start:
{
lean_object* v_res_4256_; 
v_res_4256_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_4248_, v_refreshMethod_4249_, v_refreshIntervalMs_4250_, v_inst_4251_, v_initState_4252_, v_handler_4253_, v_onDidChange_4254_);
return v_res_4256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_params_4257_){
_start:
{
lean_object* v___x_4258_; 
lean_inc(v_params_4257_);
v___x_4258_ = l_Lean_Lsp_instFromJsonSemanticTokensRangeParams_fromJson(v_params_4257_);
if (lean_obj_tag(v___x_4258_) == 0)
{
lean_object* v_a_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4274_; 
v_a_4259_ = lean_ctor_get(v___x_4258_, 0);
v_isSharedCheck_4274_ = !lean_is_exclusive(v___x_4258_);
if (v_isSharedCheck_4274_ == 0)
{
v___x_4261_ = v___x_4258_;
v_isShared_4262_ = v_isSharedCheck_4274_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_a_4259_);
lean_dec(v___x_4258_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4274_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
uint8_t v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4272_; 
v___x_4263_ = 3;
v___x_4264_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_4265_ = l_Lean_Json_compress(v_params_4257_);
v___x_4266_ = lean_string_append(v___x_4264_, v___x_4265_);
lean_dec_ref(v___x_4265_);
v___x_4267_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0));
v___x_4268_ = lean_string_append(v___x_4266_, v___x_4267_);
v___x_4269_ = lean_string_append(v___x_4268_, v_a_4259_);
lean_dec(v_a_4259_);
v___x_4270_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4270_, 0, v___x_4269_);
lean_ctor_set_uint8(v___x_4270_, sizeof(void*)*1, v___x_4263_);
if (v_isShared_4262_ == 0)
{
lean_ctor_set(v___x_4261_, 0, v___x_4270_);
v___x_4272_ = v___x_4261_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v___x_4270_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
}
}
}
else
{
lean_object* v_a_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4282_; 
lean_dec(v_params_4257_);
v_a_4275_ = lean_ctor_get(v___x_4258_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___x_4258_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4277_ = v___x_4258_;
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_a_4275_);
lean_dec(v___x_4258_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
lean_object* v___x_4280_; 
if (v_isShared_4278_ == 0)
{
v___x_4280_ = v___x_4277_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_a_4275_);
v___x_4280_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
return v___x_4280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__0(lean_object* v_j_4283_){
_start:
{
lean_object* v___x_4284_; 
v___x_4284_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_j_4283_);
if (lean_obj_tag(v___x_4284_) == 0)
{
lean_object* v_a_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4292_; 
v_a_4285_ = lean_ctor_get(v___x_4284_, 0);
v_isSharedCheck_4292_ = !lean_is_exclusive(v___x_4284_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4287_ = v___x_4284_;
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_a_4285_);
lean_dec(v___x_4284_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
lean_object* v___x_4290_; 
if (v_isShared_4288_ == 0)
{
v___x_4290_ = v___x_4287_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v_a_4285_);
v___x_4290_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
return v___x_4290_;
}
}
}
else
{
lean_object* v_a_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4301_; 
v_a_4293_ = lean_ctor_get(v___x_4284_, 0);
v_isSharedCheck_4301_ = !lean_is_exclusive(v___x_4284_);
if (v_isSharedCheck_4301_ == 0)
{
v___x_4295_ = v___x_4284_;
v_isShared_4296_ = v_isSharedCheck_4301_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_a_4293_);
lean_dec(v___x_4284_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4301_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v_textDocument_4297_; lean_object* v___x_4299_; 
v_textDocument_4297_ = lean_ctor_get(v_a_4293_, 0);
lean_inc_ref(v_textDocument_4297_);
lean_dec(v_a_4293_);
if (v_isShared_4296_ == 0)
{
lean_ctor_set(v___x_4295_, 0, v_textDocument_4297_);
v___x_4299_ = v___x_4295_;
goto v_reusejp_4298_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_textDocument_4297_);
v___x_4299_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4298_;
}
v_reusejp_4298_:
{
return v___x_4299_;
}
}
}
}
}
lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(lean_object* v_serialize_x3f_4302_, uint8_t v_val_4303_, lean_object* v___y_4304_){
_start:
{
if (lean_obj_tag(v___y_4304_) == 0)
{
lean_object* v_a_4305_; lean_object* v___x_4307_; uint8_t v_isShared_4308_; uint8_t v_isSharedCheck_4312_; 
lean_dec(v_serialize_x3f_4302_);
v_a_4305_ = lean_ctor_get(v___y_4304_, 0);
v_isSharedCheck_4312_ = !lean_is_exclusive(v___y_4304_);
if (v_isSharedCheck_4312_ == 0)
{
v___x_4307_ = v___y_4304_;
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
else
{
lean_inc(v_a_4305_);
lean_dec(v___y_4304_);
v___x_4307_ = lean_box(0);
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
v_resetjp_4306_:
{
lean_object* v___x_4310_; 
if (v_isShared_4308_ == 0)
{
v___x_4310_ = v___x_4307_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v_a_4305_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
return v___x_4310_;
}
}
}
else
{
if (lean_obj_tag(v_serialize_x3f_4302_) == 1)
{
lean_object* v_a_4313_; lean_object* v___x_4315_; uint8_t v_isShared_4316_; uint8_t v_isSharedCheck_4324_; 
v_a_4313_ = lean_ctor_get(v___y_4304_, 0);
v_isSharedCheck_4324_ = !lean_is_exclusive(v___y_4304_);
if (v_isSharedCheck_4324_ == 0)
{
v___x_4315_ = v___y_4304_;
v_isShared_4316_ = v_isSharedCheck_4324_;
goto v_resetjp_4314_;
}
else
{
lean_inc(v_a_4313_);
lean_dec(v___y_4304_);
v___x_4315_ = lean_box(0);
v_isShared_4316_ = v_isSharedCheck_4324_;
goto v_resetjp_4314_;
}
v_resetjp_4314_:
{
lean_object* v_val_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4322_; 
v_val_4317_ = lean_ctor_get(v_serialize_x3f_4302_, 0);
lean_inc(v_val_4317_);
lean_dec_ref_known(v_serialize_x3f_4302_, 1);
v___x_4318_ = lean_box(0);
v___x_4319_ = lean_apply_1(v_val_4317_, v_a_4313_);
v___x_4320_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4320_, 0, v___x_4318_);
lean_ctor_set(v___x_4320_, 1, v___x_4319_);
lean_ctor_set_uint8(v___x_4320_, sizeof(void*)*2, v_val_4303_);
if (v_isShared_4316_ == 0)
{
lean_ctor_set(v___x_4315_, 0, v___x_4320_);
v___x_4322_ = v___x_4315_;
goto v_reusejp_4321_;
}
else
{
lean_object* v_reuseFailAlloc_4323_; 
v_reuseFailAlloc_4323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4323_, 0, v___x_4320_);
v___x_4322_ = v_reuseFailAlloc_4323_;
goto v_reusejp_4321_;
}
v_reusejp_4321_:
{
return v___x_4322_;
}
}
}
else
{
lean_object* v_a_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4336_; 
lean_dec(v_serialize_x3f_4302_);
v_a_4325_ = lean_ctor_get(v___y_4304_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v___y_4304_);
if (v_isSharedCheck_4336_ == 0)
{
v___x_4327_ = v___y_4304_;
v_isShared_4328_ = v_isSharedCheck_4336_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_a_4325_);
lean_dec(v___y_4304_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4336_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4334_; 
v___x_4329_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_a_4325_);
lean_inc(v___x_4329_);
v___x_4330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4330_, 0, v___x_4329_);
v___x_4331_ = l_Lean_Json_compress(v___x_4329_);
v___x_4332_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4332_, 0, v___x_4330_);
lean_ctor_set(v___x_4332_, 1, v___x_4331_);
lean_ctor_set_uint8(v___x_4332_, sizeof(void*)*2, v_val_4303_);
if (v_isShared_4328_ == 0)
{
lean_ctor_set(v___x_4327_, 0, v___x_4332_);
v___x_4334_ = v___x_4327_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v___x_4332_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
return v___x_4334_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_serialize_x3f_4302_ = stack[0].m_obj;
uint8_t v_val_4303_ = stack[1].m_num;
lean_object* v___y_4304_ = stack[2].m_obj;
lean_object* v_res_4337_;
v_res_4337_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(v_serialize_x3f_4302_, v_val_4303_, v___y_4304_);
stack->m_obj
 = v_res_4337_;
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object* v_serialize_x3f_4338_, lean_object* v_val_4339_, lean_object* v___y_4340_){
_start:
{
uint8_t v_val_4274__boxed_4341_; lean_object* v_res_4342_; 
v_val_4274__boxed_4341_ = lean_unbox(v_val_4339_);
v_res_4342_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(v_serialize_x3f_4338_, v_val_4274__boxed_4341_, v___y_4340_);
return v_res_4342_;
}
}
lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_params_4343_){
_start:
{
lean_object* v___x_4345_; 
v___x_4345_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_params_4343_);
if (lean_obj_tag(v___x_4345_) == 0)
{
lean_object* v_a_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4353_; 
v_a_4346_ = lean_ctor_get(v___x_4345_, 0);
v_isSharedCheck_4353_ = !lean_is_exclusive(v___x_4345_);
if (v_isSharedCheck_4353_ == 0)
{
v___x_4348_ = v___x_4345_;
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
else
{
lean_inc(v_a_4346_);
lean_dec(v___x_4345_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v___x_4351_; 
if (v_isShared_4349_ == 0)
{
lean_ctor_set_tag(v___x_4348_, 1);
v___x_4351_ = v___x_4348_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v_a_4346_);
v___x_4351_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
return v___x_4351_;
}
}
}
else
{
lean_object* v_a_4354_; lean_object* v___x_4356_; uint8_t v_isShared_4357_; uint8_t v_isSharedCheck_4361_; 
v_a_4354_ = lean_ctor_get(v___x_4345_, 0);
v_isSharedCheck_4361_ = !lean_is_exclusive(v___x_4345_);
if (v_isSharedCheck_4361_ == 0)
{
v___x_4356_ = v___x_4345_;
v_isShared_4357_ = v_isSharedCheck_4361_;
goto v_resetjp_4355_;
}
else
{
lean_inc(v_a_4354_);
lean_dec(v___x_4345_);
v___x_4356_ = lean_box(0);
v_isShared_4357_ = v_isSharedCheck_4361_;
goto v_resetjp_4355_;
}
v_resetjp_4355_:
{
lean_object* v___x_4359_; 
if (v_isShared_4357_ == 0)
{
lean_ctor_set_tag(v___x_4356_, 0);
v___x_4359_ = v___x_4356_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v_a_4354_);
v___x_4359_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4358_;
}
v_reusejp_4358_:
{
return v___x_4359_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_4343_ = stack[0].m_obj;
lean_object* v_res_4362_;
v_res_4362_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_4343_);
stack->m_obj
 = v_res_4362_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_params_4363_, lean_object* v_a_4364_){
_start:
{
lean_object* v_res_4365_; 
v_res_4365_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_4363_);
return v_res_4365_;
}
}
lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(lean_object* v_handler_4366_, lean_object* v___f_4367_, lean_object* v_j_4368_, lean_object* v___y_4369_){
_start:
{
lean_object* v___x_4371_; 
v___x_4371_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_j_4368_);
if (lean_obj_tag(v___x_4371_) == 0)
{
lean_object* v_a_4372_; lean_object* v___x_4373_; 
v_a_4372_ = lean_ctor_get(v___x_4371_, 0);
lean_inc(v_a_4372_);
lean_dec_ref_known(v___x_4371_, 1);
lean_inc_ref(v___y_4369_);
v___x_4373_ = lean_apply_3(v_handler_4366_, v_a_4372_, v___y_4369_, lean_box(0));
if (lean_obj_tag(v___x_4373_) == 0)
{
lean_object* v_a_4374_; lean_object* v___x_4376_; uint8_t v_isShared_4377_; uint8_t v_isSharedCheck_4382_; 
v_a_4374_ = lean_ctor_get(v___x_4373_, 0);
v_isSharedCheck_4382_ = !lean_is_exclusive(v___x_4373_);
if (v_isSharedCheck_4382_ == 0)
{
v___x_4376_ = v___x_4373_;
v_isShared_4377_ = v_isSharedCheck_4382_;
goto v_resetjp_4375_;
}
else
{
lean_inc(v_a_4374_);
lean_dec(v___x_4373_);
v___x_4376_ = lean_box(0);
v_isShared_4377_ = v_isSharedCheck_4382_;
goto v_resetjp_4375_;
}
v_resetjp_4375_:
{
lean_object* v___x_4378_; lean_object* v___x_4380_; 
v___x_4378_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4367_, v_a_4374_);
if (v_isShared_4377_ == 0)
{
lean_ctor_set(v___x_4376_, 0, v___x_4378_);
v___x_4380_ = v___x_4376_;
goto v_reusejp_4379_;
}
else
{
lean_object* v_reuseFailAlloc_4381_; 
v_reuseFailAlloc_4381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4381_, 0, v___x_4378_);
v___x_4380_ = v_reuseFailAlloc_4381_;
goto v_reusejp_4379_;
}
v_reusejp_4379_:
{
return v___x_4380_;
}
}
}
else
{
lean_object* v_a_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4390_; 
lean_dec_ref(v___f_4367_);
v_a_4383_ = lean_ctor_get(v___x_4373_, 0);
v_isSharedCheck_4390_ = !lean_is_exclusive(v___x_4373_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4385_ = v___x_4373_;
v_isShared_4386_ = v_isSharedCheck_4390_;
goto v_resetjp_4384_;
}
else
{
lean_inc(v_a_4383_);
lean_dec(v___x_4373_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4390_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
lean_object* v___x_4388_; 
if (v_isShared_4386_ == 0)
{
v___x_4388_ = v___x_4385_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_a_4383_);
v___x_4388_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
return v___x_4388_;
}
}
}
}
else
{
lean_object* v_a_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4398_; 
lean_dec_ref(v___f_4367_);
lean_dec_ref(v_handler_4366_);
v_a_4391_ = lean_ctor_get(v___x_4371_, 0);
v_isSharedCheck_4398_ = !lean_is_exclusive(v___x_4371_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4393_ = v___x_4371_;
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_a_4391_);
lean_dec(v___x_4371_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___x_4396_; 
if (v_isShared_4394_ == 0)
{
v___x_4396_ = v___x_4393_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_a_4391_);
v___x_4396_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
return v___x_4396_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_handler_4366_ = stack[0].m_obj;
lean_object* v___f_4367_ = stack[1].m_obj;
lean_object* v_j_4368_ = stack[2].m_obj;
lean_object* v___y_4369_ = stack[3].m_obj;
lean_object* v_res_4399_;
v_res_4399_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(v_handler_4366_, v___f_4367_, v_j_4368_, v___y_4369_);
stack->m_obj
 = v_res_4399_;
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object* v_handler_4400_, lean_object* v___f_4401_, lean_object* v_j_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_){
_start:
{
lean_object* v_res_4405_; 
v_res_4405_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(v_handler_4400_, v___f_4401_, v_j_4402_, v___y_4403_);
lean_dec_ref(v___y_4403_);
return v_res_4405_;
}
}
lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(lean_object* v_method_4408_, lean_object* v_handler_4409_, lean_object* v_serialize_x3f_4410_){
_start:
{
lean_object* v___f_4412_; uint8_t v___x_4413_; 
v___f_4412_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0));
v___x_4413_ = l_Lean_initializing();
if (v___x_4413_ == 0)
{
lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; 
lean_dec(v_serialize_x3f_4410_);
lean_dec_ref(v_handler_4409_);
v___x_4414_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1));
v___x_4415_ = lean_string_append(v___x_4414_, v_method_4408_);
lean_dec_ref(v_method_4408_);
v___x_4416_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2));
v___x_4417_ = lean_string_append(v___x_4415_, v___x_4416_);
v___x_4418_ = lean_mk_io_user_error(v___x_4417_);
v___x_4419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4419_, 0, v___x_4418_);
return v___x_4419_;
}
else
{
lean_object* v___x_4420_; lean_object* v___f_4421_; lean_object* v___f_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; uint8_t v___x_4425_; 
v___x_4420_ = lean_box(v___x_4413_);
v___f_4421_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed), 3, 2);
lean_closure_set(v___f_4421_, 0, v_serialize_x3f_4410_);
lean_closure_set(v___f_4421_, 1, v___x_4420_);
v___f_4422_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_4422_, 0, v_handler_4409_);
lean_closure_set(v___f_4422_, 1, v___f_4421_);
v___x_4423_ = l_Lean_Server_requestHandlers;
v___x_4424_ = lean_st_ref_get(v___x_4423_);
v___x_4425_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_4424_, v_method_4408_);
lean_dec(v___x_4424_);
if (v___x_4425_ == 0)
{
lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; 
v___x_4426_ = lean_st_ref_take(v___x_4423_);
v___x_4427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4427_, 0, v___f_4412_);
lean_ctor_set(v___x_4427_, 1, v___f_4422_);
v___x_4428_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_4426_, v_method_4408_, v___x_4427_);
v___x_4429_ = lean_st_ref_put(v___x_4423_, v___x_4428_);
v___x_4430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4430_, 0, v___x_4429_);
return v___x_4430_;
}
else
{
lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; 
lean_dec_ref(v___f_4422_);
v___x_4431_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1));
v___x_4432_ = lean_string_append(v___x_4431_, v_method_4408_);
lean_dec_ref(v_method_4408_);
v___x_4433_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_4434_ = lean_string_append(v___x_4432_, v___x_4433_);
v___x_4435_ = lean_mk_io_user_error(v___x_4434_);
v___x_4436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4436_, 0, v___x_4435_);
return v___x_4436_;
}
}
}
}
LEAN_EXPORT void l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_4408_ = stack[0].m_obj;
lean_object* v_handler_4409_ = stack[1].m_obj;
lean_object* v_serialize_x3f_4410_ = stack[2].m_obj;
lean_object* v_res_4437_;
v_res_4437_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v_method_4408_, v_handler_4409_, v_serialize_x3f_4410_);
stack->m_obj
 = v_res_4437_;
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_4438_, lean_object* v_handler_4439_, lean_object* v_serialize_x3f_4440_, lean_object* v_a_4441_){
_start:
{
lean_object* v_res_4442_; 
v_res_4442_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v_method_4438_, v_handler_4439_, v_serialize_x3f_4440_);
return v_res_4442_;
}
}
lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4450_ = ((lean_object*)(l_Lean_Server_FileWorker_instImpl_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7_));
v___x_4451_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4452_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4453_ = lean_box(0);
v___x_4454_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v___x_4451_, v___x_4452_, v___x_4453_);
if (lean_obj_tag(v___x_4454_) == 0)
{
lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; 
lean_dec_ref_known(v___x_4454_, 1);
v___x_4455_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4456_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4457_ = lean_unsigned_to_nat(2000u);
v___x_4458_ = lean_box(0);
v___x_4459_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__4_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4460_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__5_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4461_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v___x_4455_, v___x_4456_, v___x_4457_, v___x_4450_, v___x_4458_, v___x_4459_, v___x_4460_);
return v___x_4461_;
}
else
{
return v___x_4454_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4462_;
v_res_4462_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_();
stack->m_obj
 = v_res_4462_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2____boxed(lean_object* v_a_4463_){
_start:
{
lean_object* v_res_4464_; 
v_res_4464_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_();
return v_res_4464_;
}
}
lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(lean_object* v_method_4465_, lean_object* v_refreshMethod_4466_, lean_object* v_refreshIntervalMs_4467_, lean_object* v_stateType_4468_, lean_object* v_inst_4469_, lean_object* v_initState_4470_, lean_object* v_handler_4471_, lean_object* v_onDidChange_4472_){
_start:
{
lean_object* v___x_4474_; 
v___x_4474_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_4465_, v_refreshMethod_4466_, v_refreshIntervalMs_4467_, v_inst_4469_, v_initState_4470_, v_handler_4471_, v_onDidChange_4472_);
return v___x_4474_;
}
}
LEAN_EXPORT void l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_4465_ = stack[0].m_obj;
lean_object* v_refreshMethod_4466_ = stack[1].m_obj;
lean_object* v_refreshIntervalMs_4467_ = stack[2].m_obj;
lean_object* v_inst_4469_ = stack[4].m_obj;
lean_object* v_initState_4470_ = stack[5].m_obj;
lean_object* v_handler_4471_ = stack[6].m_obj;
lean_object* v_onDidChange_4472_ = stack[7].m_obj;
lean_object* v_res_4475_;
v_res_4475_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(v_method_4465_, v_refreshMethod_4466_, v_refreshIntervalMs_4467_, lean_box(0), v_inst_4469_, v_initState_4470_, v_handler_4471_, v_onDidChange_4472_);
stack->m_obj
 = v_res_4475_;
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___boxed(lean_object* v_method_4476_, lean_object* v_refreshMethod_4477_, lean_object* v_refreshIntervalMs_4478_, lean_object* v_stateType_4479_, lean_object* v_inst_4480_, lean_object* v_initState_4481_, lean_object* v_handler_4482_, lean_object* v_onDidChange_4483_, lean_object* v_a_4484_){
_start:
{
lean_object* v_res_4485_; 
v_res_4485_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(v_method_4476_, v_refreshMethod_4477_, v_refreshIntervalMs_4478_, v_stateType_4479_, v_inst_4480_, v_initState_4481_, v_handler_4482_, v_onDidChange_4483_);
return v_res_4485_;
}
}
lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_params_4486_, lean_object* v_a_4487_){
_start:
{
lean_object* v___x_4489_; 
v___x_4489_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_4486_);
return v___x_4489_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_4486_ = stack[0].m_obj;
lean_object* v_a_4487_ = stack[1].m_obj;
lean_object* v_res_4490_;
v_res_4490_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(v_params_4486_, v_a_4487_);
stack->m_obj
 = v_res_4490_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_params_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_){
_start:
{
lean_object* v_res_4494_; 
v_res_4494_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(v_params_4491_, v_a_4492_);
lean_dec_ref(v_a_4492_);
return v_res_4494_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_4495_, lean_object* v_x_4496_, lean_object* v_x_4497_){
_start:
{
uint8_t v___x_4498_; 
v___x_4498_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_4496_, v_x_4497_);
return v___x_4498_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4496_ = stack[1].m_obj;
lean_object* v_x_4497_ = stack[2].m_obj;
uint8_t v_res_4499_;
v_res_4499_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(lean_box(0), v_x_4496_, v_x_4497_);
stack->m_num = v_res_4499_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object* v_00_u03b2_4500_, lean_object* v_x_4501_, lean_object* v_x_4502_){
_start:
{
uint8_t v_res_4503_; lean_object* v_r_4504_; 
v_res_4503_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(v_00_u03b2_4500_, v_x_4501_, v_x_4502_);
lean_dec_ref(v_x_4502_);
lean_dec_ref(v_x_4501_);
v_r_4504_ = lean_box(v_res_4503_);
return v_r_4504_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3(lean_object* v_00_u03b2_4505_, lean_object* v_x_4506_, lean_object* v_x_4507_, lean_object* v_x_4508_){
_start:
{
lean_object* v___x_4509_; 
v___x_4509_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v_x_4506_, v_x_4507_, v_x_4508_);
return v___x_4509_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(lean_object* v_method_4510_, lean_object* v_completeness_4511_, lean_object* v_stateType_4512_, lean_object* v_inst_4513_, lean_object* v_initState_4514_, lean_object* v_handler_4515_, lean_object* v_onDidChange_4516_){
_start:
{
lean_object* v___x_4518_; 
v___x_4518_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4510_, v_completeness_4511_, v_inst_4513_, v_initState_4514_, v_handler_4515_, v_onDidChange_4516_);
return v___x_4518_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_4510_ = stack[0].m_obj;
lean_object* v_completeness_4511_ = stack[1].m_obj;
lean_object* v_inst_4513_ = stack[3].m_obj;
lean_object* v_initState_4514_ = stack[4].m_obj;
lean_object* v_handler_4515_ = stack[5].m_obj;
lean_object* v_onDidChange_4516_ = stack[6].m_obj;
lean_object* v_res_4519_;
v_res_4519_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(v_method_4510_, v_completeness_4511_, lean_box(0), v_inst_4513_, v_initState_4514_, v_handler_4515_, v_onDidChange_4516_);
stack->m_obj
 = v_res_4519_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object* v_method_4520_, lean_object* v_completeness_4521_, lean_object* v_stateType_4522_, lean_object* v_inst_4523_, lean_object* v_initState_4524_, lean_object* v_handler_4525_, lean_object* v_onDidChange_4526_, lean_object* v_a_4527_){
_start:
{
lean_object* v_res_4528_; 
v_res_4528_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(v_method_4520_, v_completeness_4521_, v_stateType_4522_, v_inst_4523_, v_initState_4524_, v_handler_4525_, v_onDidChange_4526_);
return v_res_4528_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(lean_object* v_00_u03b2_4529_, lean_object* v_x_4530_, size_t v_x_4531_, lean_object* v_x_4532_){
_start:
{
uint8_t v___x_4533_; 
v___x_4533_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_4530_, v_x_4531_, v_x_4532_);
return v___x_4533_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4530_ = stack[1].m_obj;
size_t v_x_4531_ = stack[2].m_num;
lean_object* v_x_4532_ = stack[3].m_obj;
uint8_t v_res_4534_;
v_res_4534_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(lean_box(0), v_x_4530_, v_x_4531_, v_x_4532_);
stack->m_num = v_res_4534_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4535_, lean_object* v_x_4536_, lean_object* v_x_4537_, lean_object* v_x_4538_){
_start:
{
size_t v_x_4753__boxed_4539_; uint8_t v_res_4540_; lean_object* v_r_4541_; 
v_x_4753__boxed_4539_ = lean_unbox_usize(v_x_4537_);
lean_dec(v_x_4537_);
v_res_4540_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(v_00_u03b2_4535_, v_x_4536_, v_x_4753__boxed_4539_, v_x_4538_);
lean_dec_ref(v_x_4538_);
lean_dec_ref(v_x_4536_);
v_r_4541_ = lean_box(v_res_4540_);
return v_r_4541_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_object* v_00_u03b2_4542_, lean_object* v_x_4543_, size_t v_x_4544_, size_t v_x_4545_, lean_object* v_x_4546_, lean_object* v_x_4547_){
_start:
{
lean_object* v___x_4548_; 
v___x_4548_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_4543_, v_x_4544_, v_x_4545_, v_x_4546_, v_x_4547_);
return v___x_4548_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4543_ = stack[1].m_obj;
size_t v_x_4544_ = stack[2].m_num;
size_t v_x_4545_ = stack[3].m_num;
lean_object* v_x_4546_ = stack[4].m_obj;
lean_object* v_x_4547_ = stack[5].m_obj;
lean_object* v_res_4549_;
v_res_4549_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_box(0), v_x_4543_, v_x_4544_, v_x_4545_, v_x_4546_, v_x_4547_);
stack->m_obj
 = v_res_4549_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4550_, lean_object* v_x_4551_, lean_object* v_x_4552_, lean_object* v_x_4553_, lean_object* v_x_4554_, lean_object* v_x_4555_){
_start:
{
size_t v_x_4771__boxed_4556_; size_t v_x_4772__boxed_4557_; lean_object* v_res_4558_; 
v_x_4771__boxed_4556_ = lean_unbox_usize(v_x_4552_);
lean_dec(v_x_4552_);
v_x_4772__boxed_4557_ = lean_unbox_usize(v_x_4553_);
lean_dec(v_x_4553_);
v_res_4558_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(v_00_u03b2_4550_, v_x_4551_, v_x_4771__boxed_4556_, v_x_4772__boxed_4557_, v_x_4554_, v_x_4555_);
return v_res_4558_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(lean_object* v_00_u03b1_4559_, lean_object* v_00_u03b2_4560_, lean_object* v_mutex_4561_, lean_object* v_k_4562_, lean_object* v___y_4563_){
_start:
{
lean_object* v___x_4565_; 
v___x_4565_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_4561_, v_k_4562_, v___y_4563_);
return v___x_4565_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_4561_ = stack[2].m_obj;
lean_object* v_k_4562_ = stack[3].m_obj;
lean_object* v___y_4563_ = stack[4].m_obj;
lean_object* v_res_4566_;
v_res_4566_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(lean_box(0), lean_box(0), v_mutex_4561_, v_k_4562_, v___y_4563_);
stack->m_obj
 = v_res_4566_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b1_4567_, lean_object* v_00_u03b2_4568_, lean_object* v_mutex_4569_, lean_object* v_k_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_){
_start:
{
lean_object* v_res_4573_; 
v_res_4573_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(v_00_u03b1_4567_, v_00_u03b2_4568_, v_mutex_4569_, v_k_4570_, v___y_4571_);
lean_dec_ref(v___y_4571_);
return v_res_4573_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(lean_object* v_method_4574_, lean_object* v_completeness_4575_, lean_object* v_stateType_4576_, lean_object* v_inst_4577_, lean_object* v_initState_4578_, lean_object* v_handler_4579_, lean_object* v_onDidChange_4580_){
_start:
{
lean_object* v___x_4582_; 
v___x_4582_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4574_, v_completeness_4575_, v_inst_4577_, v_initState_4578_, v_handler_4579_, v_onDidChange_4580_);
return v___x_4582_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_4574_ = stack[0].m_obj;
lean_object* v_completeness_4575_ = stack[1].m_obj;
lean_object* v_inst_4577_ = stack[3].m_obj;
lean_object* v_initState_4578_ = stack[4].m_obj;
lean_object* v_handler_4579_ = stack[5].m_obj;
lean_object* v_onDidChange_4580_ = stack[6].m_obj;
lean_object* v_res_4583_;
v_res_4583_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(v_method_4574_, v_completeness_4575_, lean_box(0), v_inst_4577_, v_initState_4578_, v_handler_4579_, v_onDidChange_4580_);
stack->m_obj
 = v_res_4583_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___boxed(lean_object* v_method_4584_, lean_object* v_completeness_4585_, lean_object* v_stateType_4586_, lean_object* v_inst_4587_, lean_object* v_initState_4588_, lean_object* v_handler_4589_, lean_object* v_onDidChange_4590_, lean_object* v_a_4591_){
_start:
{
lean_object* v_res_4592_; 
v_res_4592_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(v_method_4584_, v_completeness_4585_, v_stateType_4586_, v_inst_4587_, v_initState_4588_, v_handler_4589_, v_onDidChange_4590_);
return v_res_4592_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_4593_, lean_object* v_keys_4594_, lean_object* v_vals_4595_, lean_object* v_heq_4596_, lean_object* v_i_4597_, lean_object* v_k_4598_){
_start:
{
uint8_t v___x_4599_; 
v___x_4599_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_4594_, v_i_4597_, v_k_4598_);
return v___x_4599_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_4594_ = stack[1].m_obj;
lean_object* v_vals_4595_ = stack[2].m_obj;
lean_object* v_i_4597_ = stack[4].m_obj;
lean_object* v_k_4598_ = stack[5].m_obj;
uint8_t v_res_4600_;
v_res_4600_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(lean_box(0), v_keys_4594_, v_vals_4595_, lean_box(0), v_i_4597_, v_k_4598_);
stack->m_num = v_res_4600_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4601_, lean_object* v_keys_4602_, lean_object* v_vals_4603_, lean_object* v_heq_4604_, lean_object* v_i_4605_, lean_object* v_k_4606_){
_start:
{
uint8_t v_res_4607_; lean_object* v_r_4608_; 
v_res_4607_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(v_00_u03b2_4601_, v_keys_4602_, v_vals_4603_, v_heq_4604_, v_i_4605_, v_k_4606_);
lean_dec_ref(v_k_4606_);
lean_dec_ref(v_vals_4603_);
lean_dec_ref(v_keys_4602_);
v_r_4608_ = lean_box(v_res_4607_);
return v_r_4608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_4609_, lean_object* v_n_4610_, lean_object* v_k_4611_, lean_object* v_v_4612_){
_start:
{
lean_object* v___x_4613_; 
v___x_4613_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_n_4610_, v_k_4611_, v_v_4612_);
return v___x_4613_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_4614_, size_t v_depth_4615_, lean_object* v_keys_4616_, lean_object* v_vals_4617_, lean_object* v_heq_4618_, lean_object* v_i_4619_, lean_object* v_entries_4620_){
_start:
{
lean_object* v___x_4621_; 
v___x_4621_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_4615_, v_keys_4616_, v_vals_4617_, v_i_4619_, v_entries_4620_);
return v___x_4621_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9_0interp(lean_interpreter_value* stack)
{
size_t v_depth_4615_ = stack[1].m_num;
lean_object* v_keys_4616_ = stack[2].m_obj;
lean_object* v_vals_4617_ = stack[3].m_obj;
lean_object* v_i_4619_ = stack[5].m_obj;
lean_object* v_entries_4620_ = stack[6].m_obj;
lean_object* v_res_4622_;
v_res_4622_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(lean_box(0), v_depth_4615_, v_keys_4616_, v_vals_4617_, lean_box(0), v_i_4619_, v_entries_4620_);
stack->m_obj
 = v_res_4622_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_4623_, lean_object* v_depth_4624_, lean_object* v_keys_4625_, lean_object* v_vals_4626_, lean_object* v_heq_4627_, lean_object* v_i_4628_, lean_object* v_entries_4629_){
_start:
{
size_t v_depth_boxed_4630_; lean_object* v_res_4631_; 
v_depth_boxed_4630_ = lean_unbox_usize(v_depth_4624_);
lean_dec(v_depth_4624_);
v_res_4631_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(v_00_u03b2_4623_, v_depth_boxed_4630_, v_keys_4625_, v_vals_4626_, v_heq_4627_, v_i_4628_, v_entries_4629_);
lean_dec_ref(v_vals_4626_);
lean_dec_ref(v_keys_4625_);
return v_res_4631_;
}
}
lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(lean_object* v_params_4632_, lean_object* v_a_4633_){
_start:
{
lean_object* v___x_4635_; 
v___x_4635_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_4632_);
return v___x_4635_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_4632_ = stack[0].m_obj;
lean_object* v_a_4633_ = stack[1].m_obj;
lean_object* v_res_4636_;
v_res_4636_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(v_params_4632_, v_a_4633_);
stack->m_obj
 = v_res_4636_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___boxed(lean_object* v_params_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_){
_start:
{
lean_object* v_res_4640_; 
v_res_4640_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(v_params_4637_, v_a_4638_);
lean_dec_ref(v_a_4638_);
return v_res_4640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_4641_, lean_object* v_x_4642_, lean_object* v_x_4643_, lean_object* v_x_4644_, lean_object* v_x_4645_){
_start:
{
lean_object* v___x_4646_; 
v___x_4646_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_x_4642_, v_x_4643_, v_x_4644_, v_x_4645_);
return v___x_4646_;
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
