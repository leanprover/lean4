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
lean_object* v___y_2049_; lean_object* v___y_2050_; uint8_t v___y_2051_; lean_object* v___y_2061_; lean_object* v___y_2062_; uint8_t v___y_2063_; lean_object* v___y_2073_; lean_object* v___y_2074_; uint8_t v___y_2075_; lean_object* v___y_2085_; lean_object* v___y_2086_; uint8_t v___y_2087_; uint8_t v___y_2097_; lean_object* v___y_2098_; uint8_t v___y_2099_; uint8_t v___y_2100_; lean_object* v___y_2101_; uint8_t v___y_2102_; lean_object* v___y_2104_; uint8_t v___y_2105_; uint8_t v___y_2106_; uint8_t v___y_2107_; lean_object* v___y_2108_; uint8_t v___y_2109_; lean_object* v___y_2111_; uint8_t v___y_2112_; uint8_t v___y_2113_; uint8_t v___y_2114_; lean_object* v___y_2115_; uint32_t v___y_2116_; lean_object* v___y_2121_; uint8_t v___y_2122_; uint8_t v___y_2123_; uint8_t v___y_2124_; lean_object* v___y_2125_; uint32_t v___y_2126_; lean_object* v___y_2132_; lean_object* v___y_2133_; uint8_t v___y_2134_; lean_object* v___x_2143_; uint8_t v___x_2144_; 
v___x_2143_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1));
lean_inc(v_x_2047_);
v___x_2144_ = l_Lean_Syntax_isOfKind(v_x_2047_, v___x_2143_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; uint8_t v___x_2146_; uint8_t v___y_2148_; uint8_t v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; uint8_t v___y_2152_; uint8_t v___y_2154_; uint8_t v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; uint8_t v___y_2158_; uint8_t v___y_2160_; uint32_t v___y_2161_; lean_object* v___y_2162_; uint8_t v___y_2163_; lean_object* v___y_2164_; uint8_t v___y_2169_; uint32_t v___y_2170_; uint8_t v___y_2171_; lean_object* v___y_2172_; lean_object* v___y_2173_; 
v___x_2145_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3));
lean_inc(v_x_2047_);
v___x_2146_ = l_Lean_Syntax_isOfKind(v_x_2047_, v___x_2145_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; 
v___x_2178_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2047_);
v___x_2179_ = l_Lean_Syntax_getKind(v_x_2047_);
v___x_2180_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2178_, v___x_2179_);
if (v___x_2180_ == 0)
{
lean_object* v___x_2181_; uint8_t v___x_2182_; lean_object* v___y_2184_; uint8_t v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2188_; uint8_t v___y_2189_; lean_object* v___y_2190_; uint8_t v___y_2191_; lean_object* v___y_2193_; uint32_t v___y_2194_; uint8_t v___y_2195_; lean_object* v___y_2196_; lean_object* v___y_2201_; uint32_t v___y_2202_; uint8_t v___y_2203_; lean_object* v___y_2204_; lean_object* v___y_2210_; lean_object* v___y_2211_; uint8_t v___y_2212_; lean_object* v___y_2227_; uint32_t v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2234_; uint32_t v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2242_; 
v___x_2181_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2182_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2181_, v___x_2179_);
lean_dec(v___x_2179_);
if (v___x_2182_ == 0)
{
lean_object* v___x_2257_; uint8_t v___x_2258_; 
v___x_2257_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2047_);
v___x_2258_ = l_Lean_Syntax_isOfKind(v_x_2047_, v___x_2257_);
if (v___x_2258_ == 0)
{
lean_object* v___x_2259_; size_t v_sz_2260_; size_t v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; uint8_t v___x_2266_; 
v___x_2259_ = l_Lean_Syntax_getArgs(v_x_2047_);
v_sz_2260_ = lean_array_size(v___x_2259_);
v___x_2261_ = ((size_t)0ULL);
v___x_2262_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2046_, v_sz_2260_, v___x_2261_, v___x_2259_);
v___x_2263_ = lean_unsigned_to_nat(0u);
v___x_2264_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2265_ = lean_array_get_size(v___x_2262_);
v___x_2266_ = lean_nat_dec_lt(v___x_2263_, v___x_2265_);
if (v___x_2266_ == 0)
{
lean_dec_ref(v___x_2262_);
v___y_2242_ = v___x_2264_;
goto v___jp_2241_;
}
else
{
size_t v___x_2267_; lean_object* v___x_2268_; 
v___x_2267_ = lean_usize_of_nat(v___x_2265_);
v___x_2268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2262_, v___x_2261_, v___x_2267_, v___x_2264_);
lean_dec_ref(v___x_2262_);
v___y_2242_ = v___x_2268_;
goto v___jp_2241_;
}
}
else
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2269_ = lean_unsigned_to_nat(0u);
v___x_2270_ = l_Lean_Syntax_getArg(v_x_2047_, v___x_2269_);
v___x_2271_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2046_, v___x_2270_);
v___y_2242_ = v___x_2271_;
goto v___jp_2241_;
}
}
else
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; uint8_t v___x_2275_; 
v___x_2272_ = lean_unsigned_to_nat(1u);
v___x_2273_ = l_Lean_Syntax_getArg(v_x_2047_, v___x_2272_);
lean_dec(v_x_2047_);
v___x_2274_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v___x_2273_);
v___x_2275_ = l_Lean_Syntax_isOfKind(v___x_2273_, v___x_2274_);
if (v___x_2275_ == 0)
{
lean_object* v___x_2276_; 
lean_dec(v___x_2273_);
lean_dec_ref(v_text_2046_);
v___x_2276_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2276_;
}
else
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2277_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2277_, 0, v_text_2046_);
v___x_2278_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v___x_2273_, v___x_2277_);
return v___x_2278_;
}
}
v___jp_2183_:
{
if (v___y_2185_ == 0)
{
lean_dec_ref(v___y_2186_);
lean_dec(v_x_2047_);
return v___y_2184_;
}
else
{
v___y_2061_ = v___y_2184_;
v___y_2062_ = v___y_2186_;
v___y_2063_ = v___x_2182_;
goto v___jp_2060_;
}
}
v___jp_2187_:
{
if (v___y_2189_ == 0)
{
v___y_2184_ = v___y_2188_;
v___y_2185_ = v___y_2191_;
v___y_2186_ = v___y_2190_;
goto v___jp_2183_;
}
else
{
if (v___x_2182_ == 0)
{
v___y_2061_ = v___y_2188_;
v___y_2062_ = v___y_2190_;
v___y_2063_ = v___x_2182_;
goto v___jp_2060_;
}
else
{
v___y_2184_ = v___y_2188_;
v___y_2185_ = v___y_2191_;
v___y_2186_ = v___y_2190_;
goto v___jp_2183_;
}
}
}
v___jp_2192_:
{
uint32_t v___x_2197_; uint8_t v___x_2198_; 
v___x_2197_ = 95;
v___x_2198_ = lean_uint32_dec_eq(v___y_2194_, v___x_2197_);
if (v___x_2198_ == 0)
{
uint8_t v___x_2199_; 
v___x_2199_ = l_Lean_isLetterLike(v___y_2194_);
v___y_2188_ = v___y_2193_;
v___y_2189_ = v___y_2195_;
v___y_2190_ = v___y_2196_;
v___y_2191_ = v___x_2199_;
goto v___jp_2187_;
}
else
{
v___y_2188_ = v___y_2193_;
v___y_2189_ = v___y_2195_;
v___y_2190_ = v___y_2196_;
v___y_2191_ = v___x_2198_;
goto v___jp_2187_;
}
}
v___jp_2200_:
{
uint32_t v___x_2205_; uint8_t v___x_2206_; 
v___x_2205_ = 97;
v___x_2206_ = lean_uint32_dec_le(v___x_2205_, v___y_2202_);
if (v___x_2206_ == 0)
{
v___y_2193_ = v___y_2201_;
v___y_2194_ = v___y_2202_;
v___y_2195_ = v___y_2203_;
v___y_2196_ = v___y_2204_;
goto v___jp_2192_;
}
else
{
uint32_t v___x_2207_; uint8_t v___x_2208_; 
v___x_2207_ = 122;
v___x_2208_ = lean_uint32_dec_le(v___y_2202_, v___x_2207_);
if (v___x_2208_ == 0)
{
v___y_2193_ = v___y_2201_;
v___y_2194_ = v___y_2202_;
v___y_2195_ = v___y_2203_;
v___y_2196_ = v___y_2204_;
goto v___jp_2192_;
}
else
{
v___y_2188_ = v___y_2201_;
v___y_2189_ = v___y_2203_;
v___y_2190_ = v___y_2204_;
v___y_2191_ = v___x_2208_;
goto v___jp_2187_;
}
}
}
v___jp_2209_:
{
lean_object* v___x_2213_; 
lean_inc_ref(v___y_2211_);
v___x_2213_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2211_);
if (lean_obj_tag(v___x_2213_) == 0)
{
v___y_2188_ = v___y_2210_;
v___y_2189_ = v___y_2212_;
v___y_2190_ = v___y_2211_;
v___y_2191_ = v___x_2182_;
goto v___jp_2187_;
}
else
{
lean_object* v_val_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v_val_2214_ = lean_ctor_get(v___x_2213_, 0);
lean_inc(v_val_2214_);
lean_dec_ref_known(v___x_2213_, 1);
v___x_2215_ = lean_unsigned_to_nat(0u);
v___x_2216_ = l_String_Slice_Pos_get_x3f(v_val_2214_, v___x_2215_);
lean_dec(v_val_2214_);
if (lean_obj_tag(v___x_2216_) == 0)
{
v___y_2188_ = v___y_2210_;
v___y_2189_ = v___y_2212_;
v___y_2190_ = v___y_2211_;
v___y_2191_ = v___x_2182_;
goto v___jp_2187_;
}
else
{
lean_object* v_val_2217_; uint32_t v___x_2218_; uint32_t v___x_2219_; uint8_t v___x_2220_; 
v_val_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_val_2217_);
lean_dec_ref_known(v___x_2216_, 1);
v___x_2218_ = 65;
v___x_2219_ = lean_unbox_uint32(v_val_2217_);
v___x_2220_ = lean_uint32_dec_le(v___x_2218_, v___x_2219_);
if (v___x_2220_ == 0)
{
uint32_t v___x_2221_; 
v___x_2221_ = lean_unbox_uint32(v_val_2217_);
lean_dec(v_val_2217_);
v___y_2201_ = v___y_2210_;
v___y_2202_ = v___x_2221_;
v___y_2203_ = v___y_2212_;
v___y_2204_ = v___y_2211_;
goto v___jp_2200_;
}
else
{
uint32_t v___x_2222_; uint32_t v___x_2223_; uint8_t v___x_2224_; 
v___x_2222_ = 90;
v___x_2223_ = lean_unbox_uint32(v_val_2217_);
v___x_2224_ = lean_uint32_dec_le(v___x_2223_, v___x_2222_);
if (v___x_2224_ == 0)
{
uint32_t v___x_2225_; 
v___x_2225_ = lean_unbox_uint32(v_val_2217_);
lean_dec(v_val_2217_);
v___y_2201_ = v___y_2210_;
v___y_2202_ = v___x_2225_;
v___y_2203_ = v___y_2212_;
v___y_2204_ = v___y_2211_;
goto v___jp_2200_;
}
else
{
lean_dec(v_val_2217_);
v___y_2188_ = v___y_2210_;
v___y_2189_ = v___y_2212_;
v___y_2190_ = v___y_2211_;
v___y_2191_ = v___x_2224_;
goto v___jp_2187_;
}
}
}
}
}
v___jp_2226_:
{
uint32_t v___x_2230_; uint8_t v___x_2231_; 
v___x_2230_ = 95;
v___x_2231_ = lean_uint32_dec_eq(v___y_2228_, v___x_2230_);
if (v___x_2231_ == 0)
{
uint8_t v___x_2232_; 
v___x_2232_ = l_Lean_isLetterLike(v___y_2228_);
v___y_2210_ = v___y_2227_;
v___y_2211_ = v___y_2229_;
v___y_2212_ = v___x_2232_;
goto v___jp_2209_;
}
else
{
v___y_2210_ = v___y_2227_;
v___y_2211_ = v___y_2229_;
v___y_2212_ = v___x_2231_;
goto v___jp_2209_;
}
}
v___jp_2233_:
{
uint32_t v___x_2237_; uint8_t v___x_2238_; 
v___x_2237_ = 97;
v___x_2238_ = lean_uint32_dec_le(v___x_2237_, v___y_2235_);
if (v___x_2238_ == 0)
{
v___y_2227_ = v___y_2234_;
v___y_2228_ = v___y_2235_;
v___y_2229_ = v___y_2236_;
goto v___jp_2226_;
}
else
{
uint32_t v___x_2239_; uint8_t v___x_2240_; 
v___x_2239_ = 122;
v___x_2240_ = lean_uint32_dec_le(v___y_2235_, v___x_2239_);
if (v___x_2240_ == 0)
{
v___y_2227_ = v___y_2234_;
v___y_2228_ = v___y_2235_;
v___y_2229_ = v___y_2236_;
goto v___jp_2226_;
}
else
{
v___y_2210_ = v___y_2234_;
v___y_2211_ = v___y_2236_;
v___y_2212_ = v___x_2240_;
goto v___jp_2209_;
}
}
}
v___jp_2241_:
{
if (lean_obj_tag(v_x_2047_) == 2)
{
lean_object* v_val_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v_val_2243_ = lean_ctor_get(v_x_2047_, 1);
v___x_2244_ = lean_unsigned_to_nat(0u);
v___x_2245_ = lean_string_utf8_byte_size(v_val_2243_);
lean_inc_ref(v_val_2243_);
v___x_2246_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2246_, 0, v_val_2243_);
lean_ctor_set(v___x_2246_, 1, v___x_2244_);
lean_ctor_set(v___x_2246_, 2, v___x_2245_);
v___x_2247_ = l_String_Slice_Pos_get_x3f(v___x_2246_, v___x_2244_);
lean_dec_ref_known(v___x_2246_, 3);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_inc_ref(v_val_2243_);
v___y_2210_ = v___y_2242_;
v___y_2211_ = v_val_2243_;
v___y_2212_ = v___x_2182_;
goto v___jp_2209_;
}
else
{
lean_object* v_val_2248_; uint32_t v___x_2249_; uint32_t v___x_2250_; uint8_t v___x_2251_; 
v_val_2248_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_val_2248_);
lean_dec_ref_known(v___x_2247_, 1);
v___x_2249_ = 65;
v___x_2250_ = lean_unbox_uint32(v_val_2248_);
v___x_2251_ = lean_uint32_dec_le(v___x_2249_, v___x_2250_);
if (v___x_2251_ == 0)
{
uint32_t v___x_2252_; 
v___x_2252_ = lean_unbox_uint32(v_val_2248_);
lean_dec(v_val_2248_);
lean_inc_ref(v_val_2243_);
v___y_2234_ = v___y_2242_;
v___y_2235_ = v___x_2252_;
v___y_2236_ = v_val_2243_;
goto v___jp_2233_;
}
else
{
uint32_t v___x_2253_; uint32_t v___x_2254_; uint8_t v___x_2255_; 
v___x_2253_ = 90;
v___x_2254_ = lean_unbox_uint32(v_val_2248_);
v___x_2255_ = lean_uint32_dec_le(v___x_2254_, v___x_2253_);
if (v___x_2255_ == 0)
{
uint32_t v___x_2256_; 
v___x_2256_ = lean_unbox_uint32(v_val_2248_);
lean_dec(v_val_2248_);
lean_inc_ref(v_val_2243_);
v___y_2234_ = v___y_2242_;
v___y_2235_ = v___x_2256_;
v___y_2236_ = v_val_2243_;
goto v___jp_2233_;
}
else
{
lean_dec(v_val_2248_);
lean_inc_ref(v_val_2243_);
v___y_2210_ = v___y_2242_;
v___y_2211_ = v_val_2243_;
v___y_2212_ = v___x_2255_;
goto v___jp_2209_;
}
}
}
}
else
{
lean_dec(v_x_2047_);
return v___y_2242_;
}
}
}
else
{
lean_object* v___x_2279_; 
lean_dec(v___x_2179_);
lean_dec(v_x_2047_);
lean_dec_ref(v_text_2046_);
v___x_2279_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2279_;
}
}
else
{
lean_object* v___x_2280_; uint8_t v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2284_; uint8_t v___y_2285_; uint8_t v___y_2299_; uint32_t v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; uint8_t v___y_2307_; uint32_t v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; uint8_t v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2332_; uint8_t v___y_2333_; uint8_t v___y_2334_; lean_object* v___y_2335_; uint8_t v___y_2336_; lean_object* v___y_2350_; uint8_t v___y_2351_; uint8_t v___y_2352_; lean_object* v___y_2353_; uint32_t v___y_2354_; lean_object* v___y_2359_; uint8_t v___y_2360_; uint8_t v___y_2361_; lean_object* v___y_2362_; uint32_t v___y_2363_; uint8_t v___y_2369_; uint8_t v___y_2370_; lean_object* v___y_2371_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2280_ = lean_unsigned_to_nat(0u);
v___x_2385_ = l_Lean_Syntax_getArg(v_x_2047_, v___x_2280_);
v___x_2386_ = lean_unsigned_to_nat(1u);
v___x_2387_ = lean_unsigned_to_nat(2u);
v___x_2388_ = l_Lean_Syntax_getArg(v_x_2047_, v___x_2387_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2449_; uint8_t v___x_2450_; 
v___x_2449_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__10));
lean_inc(v___x_2388_);
v___x_2450_ = l_Lean_Syntax_isOfKind(v___x_2388_, v___x_2449_);
if (v___x_2450_ == 0)
{
lean_object* v___x_2451_; lean_object* v___x_2452_; uint8_t v___x_2453_; 
lean_dec(v___x_2388_);
v___x_2451_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2047_);
v___x_2452_ = l_Lean_Syntax_getKind(v_x_2047_);
v___x_2453_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2451_, v___x_2452_);
if (v___x_2453_ == 0)
{
lean_object* v___x_2454_; uint8_t v___x_2455_; uint8_t v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; uint8_t v___y_2460_; lean_object* v___y_2462_; uint8_t v___y_2463_; lean_object* v___y_2464_; uint8_t v___y_2465_; lean_object* v___y_2467_; lean_object* v___y_2468_; uint8_t v___y_2469_; uint32_t v___y_2470_; lean_object* v___y_2475_; uint8_t v___y_2476_; lean_object* v___y_2477_; uint32_t v___y_2478_; lean_object* v___y_2484_; lean_object* v___y_2485_; uint8_t v___y_2486_; lean_object* v___y_2500_; lean_object* v___y_2501_; uint32_t v___y_2502_; lean_object* v___y_2507_; lean_object* v___y_2508_; uint32_t v___y_2509_; lean_object* v___y_2515_; 
v___x_2454_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2455_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2454_, v___x_2452_);
lean_dec(v___x_2452_);
if (v___x_2455_ == 0)
{
lean_object* v___x_2529_; uint8_t v___x_2530_; 
v___x_2529_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2047_);
v___x_2530_ = l_Lean_Syntax_isOfKind(v_x_2047_, v___x_2529_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; size_t v_sz_2532_; size_t v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; uint8_t v___x_2537_; 
lean_dec(v___x_2385_);
v___x_2531_ = l_Lean_Syntax_getArgs(v_x_2047_);
v_sz_2532_ = lean_array_size(v___x_2531_);
v___x_2533_ = ((size_t)0ULL);
v___x_2534_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2046_, v_sz_2532_, v___x_2533_, v___x_2531_);
v___x_2535_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2536_ = lean_array_get_size(v___x_2534_);
v___x_2537_ = lean_nat_dec_lt(v___x_2280_, v___x_2536_);
if (v___x_2537_ == 0)
{
lean_dec_ref(v___x_2534_);
v___y_2515_ = v___x_2535_;
goto v___jp_2514_;
}
else
{
size_t v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = lean_usize_of_nat(v___x_2536_);
v___x_2539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2534_, v___x_2533_, v___x_2538_, v___x_2535_);
lean_dec_ref(v___x_2534_);
v___y_2515_ = v___x_2539_;
goto v___jp_2514_;
}
}
else
{
lean_object* v___x_2540_; 
v___x_2540_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2046_, v___x_2385_);
v___y_2515_ = v___x_2540_;
goto v___jp_2514_;
}
}
else
{
lean_object* v___x_2541_; lean_object* v___x_2542_; uint8_t v___x_2543_; 
lean_dec(v___x_2385_);
v___x_2541_ = l_Lean_Syntax_getArg(v_x_2047_, v___x_2386_);
lean_dec(v_x_2047_);
v___x_2542_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v___x_2541_);
v___x_2543_ = l_Lean_Syntax_isOfKind(v___x_2541_, v___x_2542_);
if (v___x_2543_ == 0)
{
lean_object* v___x_2544_; 
lean_dec(v___x_2541_);
lean_dec_ref(v_text_2046_);
v___x_2544_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2544_;
}
else
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2545_, 0, v_text_2046_);
v___x_2546_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v___x_2541_, v___x_2545_);
return v___x_2546_;
}
}
v___jp_2456_:
{
if (v___y_2460_ == 0)
{
v___y_2132_ = v___y_2458_;
v___y_2133_ = v___y_2459_;
v___y_2134_ = v___x_2455_;
goto v___jp_2131_;
}
else
{
if (v___y_2457_ == 0)
{
v___y_2132_ = v___y_2458_;
v___y_2133_ = v___y_2459_;
v___y_2134_ = v___x_2146_;
goto v___jp_2131_;
}
else
{
v___y_2132_ = v___y_2458_;
v___y_2133_ = v___y_2459_;
v___y_2134_ = v___x_2455_;
goto v___jp_2131_;
}
}
}
v___jp_2461_:
{
if (v___y_2463_ == 0)
{
v___y_2457_ = v___y_2465_;
v___y_2458_ = v___y_2462_;
v___y_2459_ = v___y_2464_;
v___y_2460_ = v___x_2146_;
goto v___jp_2456_;
}
else
{
v___y_2457_ = v___y_2465_;
v___y_2458_ = v___y_2462_;
v___y_2459_ = v___y_2464_;
v___y_2460_ = v___x_2455_;
goto v___jp_2456_;
}
}
v___jp_2466_:
{
uint32_t v___x_2471_; uint8_t v___x_2472_; 
v___x_2471_ = 95;
v___x_2472_ = lean_uint32_dec_eq(v___y_2470_, v___x_2471_);
if (v___x_2472_ == 0)
{
uint8_t v___x_2473_; 
v___x_2473_ = l_Lean_isLetterLike(v___y_2470_);
v___y_2462_ = v___y_2467_;
v___y_2463_ = v___y_2469_;
v___y_2464_ = v___y_2468_;
v___y_2465_ = v___x_2473_;
goto v___jp_2461_;
}
else
{
v___y_2462_ = v___y_2467_;
v___y_2463_ = v___y_2469_;
v___y_2464_ = v___y_2468_;
v___y_2465_ = v___x_2472_;
goto v___jp_2461_;
}
}
v___jp_2474_:
{
uint32_t v___x_2479_; uint8_t v___x_2480_; 
v___x_2479_ = 97;
v___x_2480_ = lean_uint32_dec_le(v___x_2479_, v___y_2478_);
if (v___x_2480_ == 0)
{
v___y_2467_ = v___y_2475_;
v___y_2468_ = v___y_2477_;
v___y_2469_ = v___y_2476_;
v___y_2470_ = v___y_2478_;
goto v___jp_2466_;
}
else
{
uint32_t v___x_2481_; uint8_t v___x_2482_; 
v___x_2481_ = 122;
v___x_2482_ = lean_uint32_dec_le(v___y_2478_, v___x_2481_);
if (v___x_2482_ == 0)
{
v___y_2467_ = v___y_2475_;
v___y_2468_ = v___y_2477_;
v___y_2469_ = v___y_2476_;
v___y_2470_ = v___y_2478_;
goto v___jp_2466_;
}
else
{
v___y_2462_ = v___y_2475_;
v___y_2463_ = v___y_2476_;
v___y_2464_ = v___y_2477_;
v___y_2465_ = v___x_2482_;
goto v___jp_2461_;
}
}
}
v___jp_2483_:
{
lean_object* v___x_2487_; 
lean_inc_ref(v___y_2484_);
v___x_2487_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2484_);
if (lean_obj_tag(v___x_2487_) == 0)
{
v___y_2462_ = v___y_2484_;
v___y_2463_ = v___y_2486_;
v___y_2464_ = v___y_2485_;
v___y_2465_ = v___x_2455_;
goto v___jp_2461_;
}
else
{
lean_object* v_val_2488_; lean_object* v___x_2489_; 
v_val_2488_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_val_2488_);
lean_dec_ref_known(v___x_2487_, 1);
v___x_2489_ = l_String_Slice_Pos_get_x3f(v_val_2488_, v___x_2280_);
lean_dec(v_val_2488_);
if (lean_obj_tag(v___x_2489_) == 0)
{
v___y_2462_ = v___y_2484_;
v___y_2463_ = v___y_2486_;
v___y_2464_ = v___y_2485_;
v___y_2465_ = v___x_2455_;
goto v___jp_2461_;
}
else
{
lean_object* v_val_2490_; uint32_t v___x_2491_; uint32_t v___x_2492_; uint8_t v___x_2493_; 
v_val_2490_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_val_2490_);
lean_dec_ref_known(v___x_2489_, 1);
v___x_2491_ = 65;
v___x_2492_ = lean_unbox_uint32(v_val_2490_);
v___x_2493_ = lean_uint32_dec_le(v___x_2491_, v___x_2492_);
if (v___x_2493_ == 0)
{
uint32_t v___x_2494_; 
v___x_2494_ = lean_unbox_uint32(v_val_2490_);
lean_dec(v_val_2490_);
v___y_2475_ = v___y_2484_;
v___y_2476_ = v___y_2486_;
v___y_2477_ = v___y_2485_;
v___y_2478_ = v___x_2494_;
goto v___jp_2474_;
}
else
{
uint32_t v___x_2495_; uint32_t v___x_2496_; uint8_t v___x_2497_; 
v___x_2495_ = 90;
v___x_2496_ = lean_unbox_uint32(v_val_2490_);
v___x_2497_ = lean_uint32_dec_le(v___x_2496_, v___x_2495_);
if (v___x_2497_ == 0)
{
uint32_t v___x_2498_; 
v___x_2498_ = lean_unbox_uint32(v_val_2490_);
lean_dec(v_val_2490_);
v___y_2475_ = v___y_2484_;
v___y_2476_ = v___y_2486_;
v___y_2477_ = v___y_2485_;
v___y_2478_ = v___x_2498_;
goto v___jp_2474_;
}
else
{
lean_dec(v_val_2490_);
v___y_2462_ = v___y_2484_;
v___y_2463_ = v___y_2486_;
v___y_2464_ = v___y_2485_;
v___y_2465_ = v___x_2497_;
goto v___jp_2461_;
}
}
}
}
}
v___jp_2499_:
{
uint32_t v___x_2503_; uint8_t v___x_2504_; 
v___x_2503_ = 95;
v___x_2504_ = lean_uint32_dec_eq(v___y_2502_, v___x_2503_);
if (v___x_2504_ == 0)
{
uint8_t v___x_2505_; 
v___x_2505_ = l_Lean_isLetterLike(v___y_2502_);
v___y_2484_ = v___y_2500_;
v___y_2485_ = v___y_2501_;
v___y_2486_ = v___x_2505_;
goto v___jp_2483_;
}
else
{
v___y_2484_ = v___y_2500_;
v___y_2485_ = v___y_2501_;
v___y_2486_ = v___x_2504_;
goto v___jp_2483_;
}
}
v___jp_2506_:
{
uint32_t v___x_2510_; uint8_t v___x_2511_; 
v___x_2510_ = 97;
v___x_2511_ = lean_uint32_dec_le(v___x_2510_, v___y_2509_);
if (v___x_2511_ == 0)
{
v___y_2500_ = v___y_2507_;
v___y_2501_ = v___y_2508_;
v___y_2502_ = v___y_2509_;
goto v___jp_2499_;
}
else
{
uint32_t v___x_2512_; uint8_t v___x_2513_; 
v___x_2512_ = 122;
v___x_2513_ = lean_uint32_dec_le(v___y_2509_, v___x_2512_);
if (v___x_2513_ == 0)
{
v___y_2500_ = v___y_2507_;
v___y_2501_ = v___y_2508_;
v___y_2502_ = v___y_2509_;
goto v___jp_2499_;
}
else
{
v___y_2484_ = v___y_2507_;
v___y_2485_ = v___y_2508_;
v___y_2486_ = v___x_2513_;
goto v___jp_2483_;
}
}
}
v___jp_2514_:
{
if (lean_obj_tag(v_x_2047_) == 2)
{
lean_object* v_val_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v_val_2516_ = lean_ctor_get(v_x_2047_, 1);
v___x_2517_ = lean_string_utf8_byte_size(v_val_2516_);
lean_inc_ref(v_val_2516_);
v___x_2518_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2518_, 0, v_val_2516_);
lean_ctor_set(v___x_2518_, 1, v___x_2280_);
lean_ctor_set(v___x_2518_, 2, v___x_2517_);
v___x_2519_ = l_String_Slice_Pos_get_x3f(v___x_2518_, v___x_2280_);
lean_dec_ref_known(v___x_2518_, 3);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_inc_ref(v_val_2516_);
v___y_2484_ = v_val_2516_;
v___y_2485_ = v___y_2515_;
v___y_2486_ = v___x_2455_;
goto v___jp_2483_;
}
else
{
lean_object* v_val_2520_; uint32_t v___x_2521_; uint32_t v___x_2522_; uint8_t v___x_2523_; 
v_val_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_val_2520_);
lean_dec_ref_known(v___x_2519_, 1);
v___x_2521_ = 65;
v___x_2522_ = lean_unbox_uint32(v_val_2520_);
v___x_2523_ = lean_uint32_dec_le(v___x_2521_, v___x_2522_);
if (v___x_2523_ == 0)
{
uint32_t v___x_2524_; 
v___x_2524_ = lean_unbox_uint32(v_val_2520_);
lean_dec(v_val_2520_);
lean_inc_ref(v_val_2516_);
v___y_2507_ = v_val_2516_;
v___y_2508_ = v___y_2515_;
v___y_2509_ = v___x_2524_;
goto v___jp_2506_;
}
else
{
uint32_t v___x_2525_; uint32_t v___x_2526_; uint8_t v___x_2527_; 
v___x_2525_ = 90;
v___x_2526_ = lean_unbox_uint32(v_val_2520_);
v___x_2527_ = lean_uint32_dec_le(v___x_2526_, v___x_2525_);
if (v___x_2527_ == 0)
{
uint32_t v___x_2528_; 
v___x_2528_ = lean_unbox_uint32(v_val_2520_);
lean_dec(v_val_2520_);
lean_inc_ref(v_val_2516_);
v___y_2507_ = v_val_2516_;
v___y_2508_ = v___y_2515_;
v___y_2509_ = v___x_2528_;
goto v___jp_2506_;
}
else
{
lean_dec(v_val_2520_);
lean_inc_ref(v_val_2516_);
v___y_2484_ = v_val_2516_;
v___y_2485_ = v___y_2515_;
v___y_2486_ = v___x_2527_;
goto v___jp_2483_;
}
}
}
}
else
{
lean_dec(v_x_2047_);
return v___y_2515_;
}
}
}
else
{
lean_object* v___x_2547_; 
lean_dec(v___x_2452_);
lean_dec(v___x_2385_);
lean_dec(v_x_2047_);
lean_dec_ref(v_text_2046_);
v___x_2547_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2547_;
}
}
else
{
goto v___jp_2389_;
}
}
else
{
goto v___jp_2389_;
}
v___jp_2281_:
{
lean_object* v___x_2286_; 
lean_inc_ref(v___y_2284_);
v___x_2286_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2284_);
if (lean_obj_tag(v___x_2286_) == 0)
{
v___y_2154_ = v___y_2282_;
v___y_2155_ = v___y_2285_;
v___y_2156_ = v___y_2283_;
v___y_2157_ = v___y_2284_;
v___y_2158_ = v___y_2282_;
goto v___jp_2153_;
}
else
{
lean_object* v_val_2287_; lean_object* v___x_2288_; 
v_val_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_val_2287_);
lean_dec_ref_known(v___x_2286_, 1);
v___x_2288_ = l_String_Slice_Pos_get_x3f(v_val_2287_, v___x_2280_);
lean_dec(v_val_2287_);
if (lean_obj_tag(v___x_2288_) == 0)
{
v___y_2154_ = v___y_2282_;
v___y_2155_ = v___y_2285_;
v___y_2156_ = v___y_2283_;
v___y_2157_ = v___y_2284_;
v___y_2158_ = v___y_2282_;
goto v___jp_2153_;
}
else
{
lean_object* v_val_2289_; uint32_t v___x_2290_; uint32_t v___x_2291_; uint8_t v___x_2292_; 
v_val_2289_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_val_2289_);
lean_dec_ref_known(v___x_2288_, 1);
v___x_2290_ = 65;
v___x_2291_ = lean_unbox_uint32(v_val_2289_);
v___x_2292_ = lean_uint32_dec_le(v___x_2290_, v___x_2291_);
if (v___x_2292_ == 0)
{
uint32_t v___x_2293_; 
v___x_2293_ = lean_unbox_uint32(v_val_2289_);
lean_dec(v_val_2289_);
v___y_2169_ = v___y_2282_;
v___y_2170_ = v___x_2293_;
v___y_2171_ = v___y_2285_;
v___y_2172_ = v___y_2283_;
v___y_2173_ = v___y_2284_;
goto v___jp_2168_;
}
else
{
uint32_t v___x_2294_; uint32_t v___x_2295_; uint8_t v___x_2296_; 
v___x_2294_ = 90;
v___x_2295_ = lean_unbox_uint32(v_val_2289_);
v___x_2296_ = lean_uint32_dec_le(v___x_2295_, v___x_2294_);
if (v___x_2296_ == 0)
{
uint32_t v___x_2297_; 
v___x_2297_ = lean_unbox_uint32(v_val_2289_);
lean_dec(v_val_2289_);
v___y_2169_ = v___y_2282_;
v___y_2170_ = v___x_2297_;
v___y_2171_ = v___y_2285_;
v___y_2172_ = v___y_2283_;
v___y_2173_ = v___y_2284_;
goto v___jp_2168_;
}
else
{
lean_dec(v_val_2289_);
v___y_2154_ = v___y_2282_;
v___y_2155_ = v___y_2285_;
v___y_2156_ = v___y_2283_;
v___y_2157_ = v___y_2284_;
v___y_2158_ = v___x_2296_;
goto v___jp_2153_;
}
}
}
}
}
v___jp_2298_:
{
uint32_t v___x_2303_; uint8_t v___x_2304_; 
v___x_2303_ = 95;
v___x_2304_ = lean_uint32_dec_eq(v___y_2300_, v___x_2303_);
if (v___x_2304_ == 0)
{
uint8_t v___x_2305_; 
v___x_2305_ = l_Lean_isLetterLike(v___y_2300_);
v___y_2282_ = v___y_2299_;
v___y_2283_ = v___y_2301_;
v___y_2284_ = v___y_2302_;
v___y_2285_ = v___x_2305_;
goto v___jp_2281_;
}
else
{
v___y_2282_ = v___y_2299_;
v___y_2283_ = v___y_2301_;
v___y_2284_ = v___y_2302_;
v___y_2285_ = v___x_2304_;
goto v___jp_2281_;
}
}
v___jp_2306_:
{
uint32_t v___x_2311_; uint8_t v___x_2312_; 
v___x_2311_ = 97;
v___x_2312_ = lean_uint32_dec_le(v___x_2311_, v___y_2308_);
if (v___x_2312_ == 0)
{
v___y_2299_ = v___y_2307_;
v___y_2300_ = v___y_2308_;
v___y_2301_ = v___y_2309_;
v___y_2302_ = v___y_2310_;
goto v___jp_2298_;
}
else
{
uint32_t v___x_2313_; uint8_t v___x_2314_; 
v___x_2313_ = 122;
v___x_2314_ = lean_uint32_dec_le(v___y_2308_, v___x_2313_);
if (v___x_2314_ == 0)
{
v___y_2299_ = v___y_2307_;
v___y_2300_ = v___y_2308_;
v___y_2301_ = v___y_2309_;
v___y_2302_ = v___y_2310_;
goto v___jp_2298_;
}
else
{
v___y_2282_ = v___y_2307_;
v___y_2283_ = v___y_2309_;
v___y_2284_ = v___y_2310_;
v___y_2285_ = v___x_2314_;
goto v___jp_2281_;
}
}
}
v___jp_2315_:
{
if (lean_obj_tag(v_x_2047_) == 2)
{
lean_object* v_val_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v_val_2318_ = lean_ctor_get(v_x_2047_, 1);
v___x_2319_ = lean_string_utf8_byte_size(v_val_2318_);
lean_inc_ref(v_val_2318_);
v___x_2320_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2320_, 0, v_val_2318_);
lean_ctor_set(v___x_2320_, 1, v___x_2280_);
lean_ctor_set(v___x_2320_, 2, v___x_2319_);
v___x_2321_ = l_String_Slice_Pos_get_x3f(v___x_2320_, v___x_2280_);
lean_dec_ref_known(v___x_2320_, 3);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_inc_ref(v_val_2318_);
v___y_2282_ = v___y_2316_;
v___y_2283_ = v___y_2317_;
v___y_2284_ = v_val_2318_;
v___y_2285_ = v___y_2316_;
goto v___jp_2281_;
}
else
{
lean_object* v_val_2322_; uint32_t v___x_2323_; uint32_t v___x_2324_; uint8_t v___x_2325_; 
v_val_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_val_2322_);
lean_dec_ref_known(v___x_2321_, 1);
v___x_2323_ = 65;
v___x_2324_ = lean_unbox_uint32(v_val_2322_);
v___x_2325_ = lean_uint32_dec_le(v___x_2323_, v___x_2324_);
if (v___x_2325_ == 0)
{
uint32_t v___x_2326_; 
v___x_2326_ = lean_unbox_uint32(v_val_2322_);
lean_dec(v_val_2322_);
lean_inc_ref(v_val_2318_);
v___y_2307_ = v___y_2316_;
v___y_2308_ = v___x_2326_;
v___y_2309_ = v___y_2317_;
v___y_2310_ = v_val_2318_;
goto v___jp_2306_;
}
else
{
uint32_t v___x_2327_; uint32_t v___x_2328_; uint8_t v___x_2329_; 
v___x_2327_ = 90;
v___x_2328_ = lean_unbox_uint32(v_val_2322_);
v___x_2329_ = lean_uint32_dec_le(v___x_2328_, v___x_2327_);
if (v___x_2329_ == 0)
{
uint32_t v___x_2330_; 
v___x_2330_ = lean_unbox_uint32(v_val_2322_);
lean_dec(v_val_2322_);
lean_inc_ref(v_val_2318_);
v___y_2307_ = v___y_2316_;
v___y_2308_ = v___x_2330_;
v___y_2309_ = v___y_2317_;
v___y_2310_ = v_val_2318_;
goto v___jp_2306_;
}
else
{
lean_dec(v_val_2322_);
lean_inc_ref(v_val_2318_);
v___y_2282_ = v___y_2316_;
v___y_2283_ = v___y_2317_;
v___y_2284_ = v_val_2318_;
v___y_2285_ = v___x_2329_;
goto v___jp_2281_;
}
}
}
}
else
{
lean_dec(v_x_2047_);
return v___y_2317_;
}
}
v___jp_2331_:
{
lean_object* v___x_2337_; 
lean_inc_ref(v___y_2332_);
v___x_2337_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2332_);
if (lean_obj_tag(v___x_2337_) == 0)
{
v___y_2104_ = v___y_2332_;
v___y_2105_ = v___y_2336_;
v___y_2106_ = v___y_2334_;
v___y_2107_ = v___y_2333_;
v___y_2108_ = v___y_2335_;
v___y_2109_ = v___y_2334_;
goto v___jp_2103_;
}
else
{
lean_object* v_val_2338_; lean_object* v___x_2339_; 
v_val_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_val_2338_);
lean_dec_ref_known(v___x_2337_, 1);
v___x_2339_ = l_String_Slice_Pos_get_x3f(v_val_2338_, v___x_2280_);
lean_dec(v_val_2338_);
if (lean_obj_tag(v___x_2339_) == 0)
{
v___y_2104_ = v___y_2332_;
v___y_2105_ = v___y_2336_;
v___y_2106_ = v___y_2334_;
v___y_2107_ = v___y_2333_;
v___y_2108_ = v___y_2335_;
v___y_2109_ = v___y_2334_;
goto v___jp_2103_;
}
else
{
lean_object* v_val_2340_; uint32_t v___x_2341_; uint32_t v___x_2342_; uint8_t v___x_2343_; 
v_val_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_val_2340_);
lean_dec_ref_known(v___x_2339_, 1);
v___x_2341_ = 65;
v___x_2342_ = lean_unbox_uint32(v_val_2340_);
v___x_2343_ = lean_uint32_dec_le(v___x_2341_, v___x_2342_);
if (v___x_2343_ == 0)
{
uint32_t v___x_2344_; 
v___x_2344_ = lean_unbox_uint32(v_val_2340_);
lean_dec(v_val_2340_);
v___y_2121_ = v___y_2332_;
v___y_2122_ = v___y_2336_;
v___y_2123_ = v___y_2334_;
v___y_2124_ = v___y_2333_;
v___y_2125_ = v___y_2335_;
v___y_2126_ = v___x_2344_;
goto v___jp_2120_;
}
else
{
uint32_t v___x_2345_; uint32_t v___x_2346_; uint8_t v___x_2347_; 
v___x_2345_ = 90;
v___x_2346_ = lean_unbox_uint32(v_val_2340_);
v___x_2347_ = lean_uint32_dec_le(v___x_2346_, v___x_2345_);
if (v___x_2347_ == 0)
{
uint32_t v___x_2348_; 
v___x_2348_ = lean_unbox_uint32(v_val_2340_);
lean_dec(v_val_2340_);
v___y_2121_ = v___y_2332_;
v___y_2122_ = v___y_2336_;
v___y_2123_ = v___y_2334_;
v___y_2124_ = v___y_2333_;
v___y_2125_ = v___y_2335_;
v___y_2126_ = v___x_2348_;
goto v___jp_2120_;
}
else
{
lean_dec(v_val_2340_);
v___y_2104_ = v___y_2332_;
v___y_2105_ = v___y_2336_;
v___y_2106_ = v___y_2334_;
v___y_2107_ = v___y_2333_;
v___y_2108_ = v___y_2335_;
v___y_2109_ = v___x_2347_;
goto v___jp_2103_;
}
}
}
}
}
v___jp_2349_:
{
uint32_t v___x_2355_; uint8_t v___x_2356_; 
v___x_2355_ = 95;
v___x_2356_ = lean_uint32_dec_eq(v___y_2354_, v___x_2355_);
if (v___x_2356_ == 0)
{
uint8_t v___x_2357_; 
v___x_2357_ = l_Lean_isLetterLike(v___y_2354_);
v___y_2332_ = v___y_2350_;
v___y_2333_ = v___y_2352_;
v___y_2334_ = v___y_2351_;
v___y_2335_ = v___y_2353_;
v___y_2336_ = v___x_2357_;
goto v___jp_2331_;
}
else
{
v___y_2332_ = v___y_2350_;
v___y_2333_ = v___y_2352_;
v___y_2334_ = v___y_2351_;
v___y_2335_ = v___y_2353_;
v___y_2336_ = v___x_2356_;
goto v___jp_2331_;
}
}
v___jp_2358_:
{
uint32_t v___x_2364_; uint8_t v___x_2365_; 
v___x_2364_ = 97;
v___x_2365_ = lean_uint32_dec_le(v___x_2364_, v___y_2363_);
if (v___x_2365_ == 0)
{
v___y_2350_ = v___y_2359_;
v___y_2351_ = v___y_2361_;
v___y_2352_ = v___y_2360_;
v___y_2353_ = v___y_2362_;
v___y_2354_ = v___y_2363_;
goto v___jp_2349_;
}
else
{
uint32_t v___x_2366_; uint8_t v___x_2367_; 
v___x_2366_ = 122;
v___x_2367_ = lean_uint32_dec_le(v___y_2363_, v___x_2366_);
if (v___x_2367_ == 0)
{
v___y_2350_ = v___y_2359_;
v___y_2351_ = v___y_2361_;
v___y_2352_ = v___y_2360_;
v___y_2353_ = v___y_2362_;
v___y_2354_ = v___y_2363_;
goto v___jp_2349_;
}
else
{
v___y_2332_ = v___y_2359_;
v___y_2333_ = v___y_2360_;
v___y_2334_ = v___y_2361_;
v___y_2335_ = v___y_2362_;
v___y_2336_ = v___x_2367_;
goto v___jp_2331_;
}
}
}
v___jp_2368_:
{
if (lean_obj_tag(v_x_2047_) == 2)
{
lean_object* v_val_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v_val_2372_ = lean_ctor_get(v_x_2047_, 1);
v___x_2373_ = lean_string_utf8_byte_size(v_val_2372_);
lean_inc_ref(v_val_2372_);
v___x_2374_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2374_, 0, v_val_2372_);
lean_ctor_set(v___x_2374_, 1, v___x_2280_);
lean_ctor_set(v___x_2374_, 2, v___x_2373_);
v___x_2375_ = l_String_Slice_Pos_get_x3f(v___x_2374_, v___x_2280_);
lean_dec_ref_known(v___x_2374_, 3);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_inc_ref(v_val_2372_);
v___y_2332_ = v_val_2372_;
v___y_2333_ = v___y_2370_;
v___y_2334_ = v___y_2369_;
v___y_2335_ = v___y_2371_;
v___y_2336_ = v___y_2369_;
goto v___jp_2331_;
}
else
{
lean_object* v_val_2376_; uint32_t v___x_2377_; uint32_t v___x_2378_; uint8_t v___x_2379_; 
v_val_2376_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_val_2376_);
lean_dec_ref_known(v___x_2375_, 1);
v___x_2377_ = 65;
v___x_2378_ = lean_unbox_uint32(v_val_2376_);
v___x_2379_ = lean_uint32_dec_le(v___x_2377_, v___x_2378_);
if (v___x_2379_ == 0)
{
uint32_t v___x_2380_; 
v___x_2380_ = lean_unbox_uint32(v_val_2376_);
lean_dec(v_val_2376_);
lean_inc_ref(v_val_2372_);
v___y_2359_ = v_val_2372_;
v___y_2360_ = v___y_2370_;
v___y_2361_ = v___y_2369_;
v___y_2362_ = v___y_2371_;
v___y_2363_ = v___x_2380_;
goto v___jp_2358_;
}
else
{
uint32_t v___x_2381_; uint32_t v___x_2382_; uint8_t v___x_2383_; 
v___x_2381_ = 90;
v___x_2382_ = lean_unbox_uint32(v_val_2376_);
v___x_2383_ = lean_uint32_dec_le(v___x_2382_, v___x_2381_);
if (v___x_2383_ == 0)
{
uint32_t v___x_2384_; 
v___x_2384_ = lean_unbox_uint32(v_val_2376_);
lean_dec(v_val_2376_);
lean_inc_ref(v_val_2372_);
v___y_2359_ = v_val_2372_;
v___y_2360_ = v___y_2370_;
v___y_2361_ = v___y_2369_;
v___y_2362_ = v___y_2371_;
v___y_2363_ = v___x_2384_;
goto v___jp_2358_;
}
else
{
lean_dec(v_val_2376_);
lean_inc_ref(v_val_2372_);
v___y_2332_ = v_val_2372_;
v___y_2333_ = v___y_2370_;
v___y_2334_ = v___y_2369_;
v___y_2335_ = v___y_2371_;
v___y_2336_ = v___x_2383_;
goto v___jp_2331_;
}
}
}
}
else
{
lean_dec(v_x_2047_);
return v___y_2371_;
}
}
v___jp_2389_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; uint8_t v___x_2392_; 
v___x_2390_ = lean_unsigned_to_nat(3u);
v___x_2391_ = l_Lean_Syntax_getArg(v_x_2047_, v___x_2390_);
v___x_2392_ = l_Lean_Syntax_matchesNull(v___x_2391_, v___x_2280_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; lean_object* v___x_2394_; uint8_t v___x_2395_; 
lean_dec(v___x_2388_);
v___x_2393_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2047_);
v___x_2394_ = l_Lean_Syntax_getKind(v_x_2047_);
v___x_2395_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2393_, v___x_2394_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; uint8_t v___x_2397_; 
v___x_2396_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2397_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2396_, v___x_2394_);
lean_dec(v___x_2394_);
if (v___x_2397_ == 0)
{
lean_object* v___x_2398_; uint8_t v___x_2399_; 
v___x_2398_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2047_);
v___x_2399_ = l_Lean_Syntax_isOfKind(v_x_2047_, v___x_2398_);
if (v___x_2399_ == 0)
{
lean_object* v___x_2400_; size_t v_sz_2401_; size_t v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; uint8_t v___x_2406_; 
lean_dec(v___x_2385_);
v___x_2400_ = l_Lean_Syntax_getArgs(v_x_2047_);
v_sz_2401_ = lean_array_size(v___x_2400_);
v___x_2402_ = ((size_t)0ULL);
v___x_2403_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2046_, v_sz_2401_, v___x_2402_, v___x_2400_);
v___x_2404_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2405_ = lean_array_get_size(v___x_2403_);
v___x_2406_ = lean_nat_dec_lt(v___x_2280_, v___x_2405_);
if (v___x_2406_ == 0)
{
lean_dec_ref(v___x_2403_);
v___y_2316_ = v___x_2397_;
v___y_2317_ = v___x_2404_;
goto v___jp_2315_;
}
else
{
size_t v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = lean_usize_of_nat(v___x_2405_);
v___x_2408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2403_, v___x_2402_, v___x_2407_, v___x_2404_);
lean_dec_ref(v___x_2403_);
v___y_2316_ = v___x_2397_;
v___y_2317_ = v___x_2408_;
goto v___jp_2315_;
}
}
else
{
lean_object* v___x_2409_; 
v___x_2409_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2046_, v___x_2385_);
v___y_2316_ = v___x_2397_;
v___y_2317_ = v___x_2409_;
goto v___jp_2315_;
}
}
else
{
lean_object* v___x_2410_; lean_object* v___x_2411_; uint8_t v___x_2412_; 
lean_dec(v___x_2385_);
v___x_2410_ = l_Lean_Syntax_getArg(v_x_2047_, v___x_2386_);
lean_dec(v_x_2047_);
v___x_2411_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v___x_2410_);
v___x_2412_ = l_Lean_Syntax_isOfKind(v___x_2410_, v___x_2411_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; 
lean_dec(v___x_2410_);
lean_dec_ref(v_text_2046_);
v___x_2413_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2413_;
}
else
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2414_, 0, v_text_2046_);
v___x_2415_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v___x_2410_, v___x_2414_);
return v___x_2415_;
}
}
}
else
{
lean_object* v___x_2416_; 
lean_dec(v___x_2394_);
lean_dec(v___x_2385_);
lean_dec(v_x_2047_);
lean_dec_ref(v_text_2046_);
v___x_2416_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2416_;
}
}
else
{
lean_object* v___x_2417_; lean_object* v___x_2418_; uint8_t v___x_2419_; 
v___x_2417_ = lean_unsigned_to_nat(4u);
v___x_2418_ = l_Lean_Syntax_getArg(v_x_2047_, v___x_2417_);
v___x_2419_ = l_Lean_Syntax_matchesNull(v___x_2418_, v___x_2280_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; lean_object* v___x_2421_; uint8_t v___x_2422_; 
lean_dec(v___x_2388_);
v___x_2420_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2047_);
v___x_2421_ = l_Lean_Syntax_getKind(v_x_2047_);
v___x_2422_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2420_, v___x_2421_);
if (v___x_2422_ == 0)
{
lean_object* v___x_2423_; uint8_t v___x_2424_; 
v___x_2423_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2424_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2423_, v___x_2421_);
lean_dec(v___x_2421_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; uint8_t v___x_2426_; 
v___x_2425_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2047_);
v___x_2426_ = l_Lean_Syntax_isOfKind(v_x_2047_, v___x_2425_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; size_t v_sz_2428_; size_t v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; uint8_t v___x_2433_; 
lean_dec(v___x_2385_);
v___x_2427_ = l_Lean_Syntax_getArgs(v_x_2047_);
v_sz_2428_ = lean_array_size(v___x_2427_);
v___x_2429_ = ((size_t)0ULL);
v___x_2430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2046_, v_sz_2428_, v___x_2429_, v___x_2427_);
v___x_2431_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2432_ = lean_array_get_size(v___x_2430_);
v___x_2433_ = lean_nat_dec_lt(v___x_2280_, v___x_2432_);
if (v___x_2433_ == 0)
{
lean_dec_ref(v___x_2430_);
v___y_2369_ = v___x_2424_;
v___y_2370_ = v___x_2392_;
v___y_2371_ = v___x_2431_;
goto v___jp_2368_;
}
else
{
size_t v___x_2434_; lean_object* v___x_2435_; 
v___x_2434_ = lean_usize_of_nat(v___x_2432_);
v___x_2435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2430_, v___x_2429_, v___x_2434_, v___x_2431_);
lean_dec_ref(v___x_2430_);
v___y_2369_ = v___x_2424_;
v___y_2370_ = v___x_2392_;
v___y_2371_ = v___x_2435_;
goto v___jp_2368_;
}
}
else
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2046_, v___x_2385_);
v___y_2369_ = v___x_2424_;
v___y_2370_ = v___x_2392_;
v___y_2371_ = v___x_2436_;
goto v___jp_2368_;
}
}
else
{
lean_object* v___x_2437_; lean_object* v___x_2438_; uint8_t v___x_2439_; 
lean_dec(v___x_2385_);
v___x_2437_ = l_Lean_Syntax_getArg(v_x_2047_, v___x_2386_);
lean_dec(v_x_2047_);
v___x_2438_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v___x_2437_);
v___x_2439_ = l_Lean_Syntax_isOfKind(v___x_2437_, v___x_2438_);
if (v___x_2439_ == 0)
{
lean_object* v___x_2440_; 
lean_dec(v___x_2437_);
lean_dec_ref(v_text_2046_);
v___x_2440_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2440_;
}
else
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2441_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2441_, 0, v_text_2046_);
v___x_2442_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v___x_2437_, v___x_2441_);
return v___x_2442_;
}
}
}
else
{
lean_object* v___x_2443_; 
lean_dec(v___x_2421_);
lean_dec(v___x_2385_);
lean_dec(v_x_2047_);
lean_dec_ref(v_text_2046_);
v___x_2443_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2443_;
}
}
else
{
lean_object* v_tokens_2444_; uint8_t v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
lean_dec(v_x_2047_);
v_tokens_2444_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2046_, v___x_2385_);
v___x_2445_ = 2;
v___x_2446_ = lean_unsigned_to_nat(5u);
v___x_2447_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2447_, 0, v___x_2388_);
lean_ctor_set(v___x_2447_, 1, v___x_2446_);
lean_ctor_set_uint8(v___x_2447_, sizeof(void*)*2, v___x_2445_);
v___x_2448_ = lean_array_push(v_tokens_2444_, v___x_2447_);
return v___x_2448_;
}
}
}
}
v___jp_2147_:
{
if (v___y_2152_ == 0)
{
v___y_2073_ = v___y_2150_;
v___y_2074_ = v___y_2151_;
v___y_2075_ = v___y_2148_;
goto v___jp_2072_;
}
else
{
if (v___y_2149_ == 0)
{
v___y_2073_ = v___y_2150_;
v___y_2074_ = v___y_2151_;
v___y_2075_ = v___x_2146_;
goto v___jp_2072_;
}
else
{
v___y_2073_ = v___y_2150_;
v___y_2074_ = v___y_2151_;
v___y_2075_ = v___y_2148_;
goto v___jp_2072_;
}
}
}
v___jp_2153_:
{
if (v___y_2155_ == 0)
{
v___y_2148_ = v___y_2154_;
v___y_2149_ = v___y_2158_;
v___y_2150_ = v___y_2156_;
v___y_2151_ = v___y_2157_;
v___y_2152_ = v___x_2146_;
goto v___jp_2147_;
}
else
{
v___y_2148_ = v___y_2154_;
v___y_2149_ = v___y_2158_;
v___y_2150_ = v___y_2156_;
v___y_2151_ = v___y_2157_;
v___y_2152_ = v___y_2154_;
goto v___jp_2147_;
}
}
v___jp_2159_:
{
uint32_t v___x_2165_; uint8_t v___x_2166_; 
v___x_2165_ = 95;
v___x_2166_ = lean_uint32_dec_eq(v___y_2161_, v___x_2165_);
if (v___x_2166_ == 0)
{
uint8_t v___x_2167_; 
v___x_2167_ = l_Lean_isLetterLike(v___y_2161_);
v___y_2154_ = v___y_2160_;
v___y_2155_ = v___y_2163_;
v___y_2156_ = v___y_2162_;
v___y_2157_ = v___y_2164_;
v___y_2158_ = v___x_2167_;
goto v___jp_2153_;
}
else
{
v___y_2154_ = v___y_2160_;
v___y_2155_ = v___y_2163_;
v___y_2156_ = v___y_2162_;
v___y_2157_ = v___y_2164_;
v___y_2158_ = v___x_2166_;
goto v___jp_2153_;
}
}
v___jp_2168_:
{
uint32_t v___x_2174_; uint8_t v___x_2175_; 
v___x_2174_ = 97;
v___x_2175_ = lean_uint32_dec_le(v___x_2174_, v___y_2170_);
if (v___x_2175_ == 0)
{
v___y_2160_ = v___y_2169_;
v___y_2161_ = v___y_2170_;
v___y_2162_ = v___y_2172_;
v___y_2163_ = v___y_2171_;
v___y_2164_ = v___y_2173_;
goto v___jp_2159_;
}
else
{
uint32_t v___x_2176_; uint8_t v___x_2177_; 
v___x_2176_ = 122;
v___x_2177_ = lean_uint32_dec_le(v___y_2170_, v___x_2176_);
if (v___x_2177_ == 0)
{
v___y_2160_ = v___y_2169_;
v___y_2161_ = v___y_2170_;
v___y_2162_ = v___y_2172_;
v___y_2163_ = v___y_2171_;
v___y_2164_ = v___y_2173_;
goto v___jp_2159_;
}
else
{
v___y_2154_ = v___y_2169_;
v___y_2155_ = v___y_2171_;
v___y_2156_ = v___y_2172_;
v___y_2157_ = v___y_2173_;
v___y_2158_ = v___x_2177_;
goto v___jp_2153_;
}
}
}
}
else
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; uint8_t v___x_2552_; 
v___x_2548_ = lean_unsigned_to_nat(0u);
v___x_2549_ = lean_unsigned_to_nat(2u);
v___x_2550_ = l_Lean_Syntax_getArg(v_x_2047_, v___x_2549_);
v___x_2551_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__10));
lean_inc(v___x_2550_);
v___x_2552_ = l_Lean_Syntax_isOfKind(v___x_2550_, v___x_2551_);
if (v___x_2552_ == 0)
{
lean_object* v___x_2553_; lean_object* v___x_2554_; uint8_t v___x_2555_; 
lean_dec(v___x_2550_);
v___x_2553_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2047_);
v___x_2554_ = l_Lean_Syntax_getKind(v_x_2047_);
v___x_2555_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2553_, v___x_2554_);
if (v___x_2555_ == 0)
{
lean_object* v___x_2556_; uint8_t v___x_2557_; uint8_t v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; uint8_t v___y_2562_; lean_object* v___y_2564_; uint8_t v___y_2565_; lean_object* v___y_2566_; uint8_t v___y_2567_; lean_object* v___y_2569_; uint8_t v___y_2570_; uint32_t v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2577_; uint8_t v___y_2578_; uint32_t v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2586_; lean_object* v___y_2587_; uint8_t v___y_2588_; lean_object* v___y_2602_; uint32_t v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2609_; uint32_t v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2617_; 
v___x_2556_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2557_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2556_, v___x_2554_);
lean_dec(v___x_2554_);
if (v___x_2557_ == 0)
{
lean_object* v___x_2631_; uint8_t v___x_2632_; 
v___x_2631_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2047_);
v___x_2632_ = l_Lean_Syntax_isOfKind(v_x_2047_, v___x_2631_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; size_t v_sz_2634_; size_t v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; uint8_t v___x_2639_; 
v___x_2633_ = l_Lean_Syntax_getArgs(v_x_2047_);
v_sz_2634_ = lean_array_size(v___x_2633_);
v___x_2635_ = ((size_t)0ULL);
v___x_2636_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2046_, v_sz_2634_, v___x_2635_, v___x_2633_);
v___x_2637_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2638_ = lean_array_get_size(v___x_2636_);
v___x_2639_ = lean_nat_dec_lt(v___x_2548_, v___x_2638_);
if (v___x_2639_ == 0)
{
lean_dec_ref(v___x_2636_);
v___y_2617_ = v___x_2637_;
goto v___jp_2616_;
}
else
{
size_t v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = lean_usize_of_nat(v___x_2638_);
v___x_2641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2636_, v___x_2635_, v___x_2640_, v___x_2637_);
lean_dec_ref(v___x_2636_);
v___y_2617_ = v___x_2641_;
goto v___jp_2616_;
}
}
else
{
lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2642_ = l_Lean_Syntax_getArg(v_x_2047_, v___x_2548_);
v___x_2643_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2046_, v___x_2642_);
v___y_2617_ = v___x_2643_;
goto v___jp_2616_;
}
}
else
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; uint8_t v___x_2647_; 
v___x_2644_ = lean_unsigned_to_nat(1u);
v___x_2645_ = l_Lean_Syntax_getArg(v_x_2047_, v___x_2644_);
lean_dec(v_x_2047_);
v___x_2646_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v___x_2645_);
v___x_2647_ = l_Lean_Syntax_isOfKind(v___x_2645_, v___x_2646_);
if (v___x_2647_ == 0)
{
lean_object* v___x_2648_; 
lean_dec(v___x_2645_);
lean_dec_ref(v_text_2046_);
v___x_2648_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2648_;
}
else
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2649_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2649_, 0, v_text_2046_);
v___x_2650_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v___x_2645_, v___x_2649_);
return v___x_2650_;
}
}
v___jp_2558_:
{
if (v___y_2562_ == 0)
{
v___y_2049_ = v___y_2560_;
v___y_2050_ = v___y_2561_;
v___y_2051_ = v___x_2557_;
goto v___jp_2048_;
}
else
{
if (v___y_2559_ == 0)
{
v___y_2049_ = v___y_2560_;
v___y_2050_ = v___y_2561_;
v___y_2051_ = v___x_2144_;
goto v___jp_2048_;
}
else
{
v___y_2049_ = v___y_2560_;
v___y_2050_ = v___y_2561_;
v___y_2051_ = v___x_2557_;
goto v___jp_2048_;
}
}
}
v___jp_2563_:
{
if (v___y_2565_ == 0)
{
v___y_2559_ = v___y_2567_;
v___y_2560_ = v___y_2564_;
v___y_2561_ = v___y_2566_;
v___y_2562_ = v___x_2144_;
goto v___jp_2558_;
}
else
{
v___y_2559_ = v___y_2567_;
v___y_2560_ = v___y_2564_;
v___y_2561_ = v___y_2566_;
v___y_2562_ = v___x_2557_;
goto v___jp_2558_;
}
}
v___jp_2568_:
{
uint32_t v___x_2573_; uint8_t v___x_2574_; 
v___x_2573_ = 95;
v___x_2574_ = lean_uint32_dec_eq(v___y_2571_, v___x_2573_);
if (v___x_2574_ == 0)
{
uint8_t v___x_2575_; 
v___x_2575_ = l_Lean_isLetterLike(v___y_2571_);
v___y_2564_ = v___y_2569_;
v___y_2565_ = v___y_2570_;
v___y_2566_ = v___y_2572_;
v___y_2567_ = v___x_2575_;
goto v___jp_2563_;
}
else
{
v___y_2564_ = v___y_2569_;
v___y_2565_ = v___y_2570_;
v___y_2566_ = v___y_2572_;
v___y_2567_ = v___x_2574_;
goto v___jp_2563_;
}
}
v___jp_2576_:
{
uint32_t v___x_2581_; uint8_t v___x_2582_; 
v___x_2581_ = 97;
v___x_2582_ = lean_uint32_dec_le(v___x_2581_, v___y_2579_);
if (v___x_2582_ == 0)
{
v___y_2569_ = v___y_2577_;
v___y_2570_ = v___y_2578_;
v___y_2571_ = v___y_2579_;
v___y_2572_ = v___y_2580_;
goto v___jp_2568_;
}
else
{
uint32_t v___x_2583_; uint8_t v___x_2584_; 
v___x_2583_ = 122;
v___x_2584_ = lean_uint32_dec_le(v___y_2579_, v___x_2583_);
if (v___x_2584_ == 0)
{
v___y_2569_ = v___y_2577_;
v___y_2570_ = v___y_2578_;
v___y_2571_ = v___y_2579_;
v___y_2572_ = v___y_2580_;
goto v___jp_2568_;
}
else
{
v___y_2564_ = v___y_2577_;
v___y_2565_ = v___y_2578_;
v___y_2566_ = v___y_2580_;
v___y_2567_ = v___x_2584_;
goto v___jp_2563_;
}
}
}
v___jp_2585_:
{
lean_object* v___x_2589_; 
lean_inc_ref(v___y_2587_);
v___x_2589_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2587_);
if (lean_obj_tag(v___x_2589_) == 0)
{
v___y_2564_ = v___y_2586_;
v___y_2565_ = v___y_2588_;
v___y_2566_ = v___y_2587_;
v___y_2567_ = v___x_2557_;
goto v___jp_2563_;
}
else
{
lean_object* v_val_2590_; lean_object* v___x_2591_; 
v_val_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_val_2590_);
lean_dec_ref_known(v___x_2589_, 1);
v___x_2591_ = l_String_Slice_Pos_get_x3f(v_val_2590_, v___x_2548_);
lean_dec(v_val_2590_);
if (lean_obj_tag(v___x_2591_) == 0)
{
v___y_2564_ = v___y_2586_;
v___y_2565_ = v___y_2588_;
v___y_2566_ = v___y_2587_;
v___y_2567_ = v___x_2557_;
goto v___jp_2563_;
}
else
{
lean_object* v_val_2592_; uint32_t v___x_2593_; uint32_t v___x_2594_; uint8_t v___x_2595_; 
v_val_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_val_2592_);
lean_dec_ref_known(v___x_2591_, 1);
v___x_2593_ = 65;
v___x_2594_ = lean_unbox_uint32(v_val_2592_);
v___x_2595_ = lean_uint32_dec_le(v___x_2593_, v___x_2594_);
if (v___x_2595_ == 0)
{
uint32_t v___x_2596_; 
v___x_2596_ = lean_unbox_uint32(v_val_2592_);
lean_dec(v_val_2592_);
v___y_2577_ = v___y_2586_;
v___y_2578_ = v___y_2588_;
v___y_2579_ = v___x_2596_;
v___y_2580_ = v___y_2587_;
goto v___jp_2576_;
}
else
{
uint32_t v___x_2597_; uint32_t v___x_2598_; uint8_t v___x_2599_; 
v___x_2597_ = 90;
v___x_2598_ = lean_unbox_uint32(v_val_2592_);
v___x_2599_ = lean_uint32_dec_le(v___x_2598_, v___x_2597_);
if (v___x_2599_ == 0)
{
uint32_t v___x_2600_; 
v___x_2600_ = lean_unbox_uint32(v_val_2592_);
lean_dec(v_val_2592_);
v___y_2577_ = v___y_2586_;
v___y_2578_ = v___y_2588_;
v___y_2579_ = v___x_2600_;
v___y_2580_ = v___y_2587_;
goto v___jp_2576_;
}
else
{
lean_dec(v_val_2592_);
v___y_2564_ = v___y_2586_;
v___y_2565_ = v___y_2588_;
v___y_2566_ = v___y_2587_;
v___y_2567_ = v___x_2599_;
goto v___jp_2563_;
}
}
}
}
}
v___jp_2601_:
{
uint32_t v___x_2605_; uint8_t v___x_2606_; 
v___x_2605_ = 95;
v___x_2606_ = lean_uint32_dec_eq(v___y_2603_, v___x_2605_);
if (v___x_2606_ == 0)
{
uint8_t v___x_2607_; 
v___x_2607_ = l_Lean_isLetterLike(v___y_2603_);
v___y_2586_ = v___y_2602_;
v___y_2587_ = v___y_2604_;
v___y_2588_ = v___x_2607_;
goto v___jp_2585_;
}
else
{
v___y_2586_ = v___y_2602_;
v___y_2587_ = v___y_2604_;
v___y_2588_ = v___x_2606_;
goto v___jp_2585_;
}
}
v___jp_2608_:
{
uint32_t v___x_2612_; uint8_t v___x_2613_; 
v___x_2612_ = 97;
v___x_2613_ = lean_uint32_dec_le(v___x_2612_, v___y_2610_);
if (v___x_2613_ == 0)
{
v___y_2602_ = v___y_2609_;
v___y_2603_ = v___y_2610_;
v___y_2604_ = v___y_2611_;
goto v___jp_2601_;
}
else
{
uint32_t v___x_2614_; uint8_t v___x_2615_; 
v___x_2614_ = 122;
v___x_2615_ = lean_uint32_dec_le(v___y_2610_, v___x_2614_);
if (v___x_2615_ == 0)
{
v___y_2602_ = v___y_2609_;
v___y_2603_ = v___y_2610_;
v___y_2604_ = v___y_2611_;
goto v___jp_2601_;
}
else
{
v___y_2586_ = v___y_2609_;
v___y_2587_ = v___y_2611_;
v___y_2588_ = v___x_2615_;
goto v___jp_2585_;
}
}
}
v___jp_2616_:
{
if (lean_obj_tag(v_x_2047_) == 2)
{
lean_object* v_val_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v_val_2618_ = lean_ctor_get(v_x_2047_, 1);
v___x_2619_ = lean_string_utf8_byte_size(v_val_2618_);
lean_inc_ref(v_val_2618_);
v___x_2620_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2620_, 0, v_val_2618_);
lean_ctor_set(v___x_2620_, 1, v___x_2548_);
lean_ctor_set(v___x_2620_, 2, v___x_2619_);
v___x_2621_ = l_String_Slice_Pos_get_x3f(v___x_2620_, v___x_2548_);
lean_dec_ref_known(v___x_2620_, 3);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_inc_ref(v_val_2618_);
v___y_2586_ = v___y_2617_;
v___y_2587_ = v_val_2618_;
v___y_2588_ = v___x_2557_;
goto v___jp_2585_;
}
else
{
lean_object* v_val_2622_; uint32_t v___x_2623_; uint32_t v___x_2624_; uint8_t v___x_2625_; 
v_val_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_val_2622_);
lean_dec_ref_known(v___x_2621_, 1);
v___x_2623_ = 65;
v___x_2624_ = lean_unbox_uint32(v_val_2622_);
v___x_2625_ = lean_uint32_dec_le(v___x_2623_, v___x_2624_);
if (v___x_2625_ == 0)
{
uint32_t v___x_2626_; 
v___x_2626_ = lean_unbox_uint32(v_val_2622_);
lean_dec(v_val_2622_);
lean_inc_ref(v_val_2618_);
v___y_2609_ = v___y_2617_;
v___y_2610_ = v___x_2626_;
v___y_2611_ = v_val_2618_;
goto v___jp_2608_;
}
else
{
uint32_t v___x_2627_; uint32_t v___x_2628_; uint8_t v___x_2629_; 
v___x_2627_ = 90;
v___x_2628_ = lean_unbox_uint32(v_val_2622_);
v___x_2629_ = lean_uint32_dec_le(v___x_2628_, v___x_2627_);
if (v___x_2629_ == 0)
{
uint32_t v___x_2630_; 
v___x_2630_ = lean_unbox_uint32(v_val_2622_);
lean_dec(v_val_2622_);
lean_inc_ref(v_val_2618_);
v___y_2609_ = v___y_2617_;
v___y_2610_ = v___x_2630_;
v___y_2611_ = v_val_2618_;
goto v___jp_2608_;
}
else
{
lean_dec(v_val_2622_);
lean_inc_ref(v_val_2618_);
v___y_2586_ = v___y_2617_;
v___y_2587_ = v_val_2618_;
v___y_2588_ = v___x_2629_;
goto v___jp_2585_;
}
}
}
}
else
{
lean_dec(v_x_2047_);
return v___y_2617_;
}
}
}
else
{
lean_object* v___x_2651_; 
lean_dec(v___x_2554_);
lean_dec(v_x_2047_);
lean_dec_ref(v_text_2046_);
v___x_2651_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2651_;
}
}
else
{
lean_object* v___x_2652_; lean_object* v_tokens_2653_; uint8_t v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2652_ = l_Lean_Syntax_getArg(v_x_2047_, v___x_2548_);
lean_dec(v_x_2047_);
v_tokens_2653_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2046_, v___x_2652_);
v___x_2654_ = 2;
v___x_2655_ = lean_unsigned_to_nat(5u);
v___x_2656_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2656_, 0, v___x_2550_);
lean_ctor_set(v___x_2656_, 1, v___x_2655_);
lean_ctor_set_uint8(v___x_2656_, sizeof(void*)*2, v___x_2654_);
v___x_2657_ = lean_array_push(v_tokens_2653_, v___x_2656_);
return v___x_2657_;
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
v___x_2055_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2052_, v___y_2050_, v___x_2054_);
lean_dec(v___x_2054_);
lean_dec_ref(v___y_2050_);
v___x_2056_ = lean_unsigned_to_nat(5u);
v___x_2057_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2057_, 0, v_x_2047_);
lean_ctor_set(v___x_2057_, 1, v___x_2056_);
v___x_2058_ = lean_unbox(v___x_2055_);
lean_dec(v___x_2055_);
lean_ctor_set_uint8(v___x_2057_, sizeof(void*)*2, v___x_2058_);
v___x_2059_ = lean_array_push(v___y_2049_, v___x_2057_);
return v___x_2059_;
}
else
{
lean_dec_ref(v___y_2050_);
lean_dec(v_x_2047_);
return v___y_2049_;
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
v___x_2091_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2088_, v___y_2085_, v___x_2090_);
lean_dec(v___x_2090_);
lean_dec_ref(v___y_2085_);
v___x_2092_ = lean_unsigned_to_nat(5u);
v___x_2093_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2093_, 0, v_x_2047_);
lean_ctor_set(v___x_2093_, 1, v___x_2092_);
v___x_2094_ = lean_unbox(v___x_2091_);
lean_dec(v___x_2091_);
lean_ctor_set_uint8(v___x_2093_, sizeof(void*)*2, v___x_2094_);
v___x_2095_ = lean_array_push(v___y_2086_, v___x_2093_);
return v___x_2095_;
}
else
{
lean_dec_ref(v___y_2085_);
lean_dec(v_x_2047_);
return v___y_2086_;
}
}
v___jp_2096_:
{
if (v___y_2102_ == 0)
{
v___y_2085_ = v___y_2098_;
v___y_2086_ = v___y_2101_;
v___y_2087_ = v___y_2100_;
goto v___jp_2084_;
}
else
{
if (v___y_2097_ == 0)
{
v___y_2085_ = v___y_2098_;
v___y_2086_ = v___y_2101_;
v___y_2087_ = v___y_2099_;
goto v___jp_2084_;
}
else
{
v___y_2085_ = v___y_2098_;
v___y_2086_ = v___y_2101_;
v___y_2087_ = v___y_2100_;
goto v___jp_2084_;
}
}
}
v___jp_2103_:
{
if (v___y_2105_ == 0)
{
v___y_2097_ = v___y_2109_;
v___y_2098_ = v___y_2104_;
v___y_2099_ = v___y_2107_;
v___y_2100_ = v___y_2106_;
v___y_2101_ = v___y_2108_;
v___y_2102_ = v___y_2107_;
goto v___jp_2096_;
}
else
{
v___y_2097_ = v___y_2109_;
v___y_2098_ = v___y_2104_;
v___y_2099_ = v___y_2107_;
v___y_2100_ = v___y_2106_;
v___y_2101_ = v___y_2108_;
v___y_2102_ = v___y_2106_;
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
v___y_2105_ = v___y_2112_;
v___y_2106_ = v___y_2114_;
v___y_2107_ = v___y_2113_;
v___y_2108_ = v___y_2115_;
v___y_2109_ = v___x_2119_;
goto v___jp_2103_;
}
else
{
v___y_2104_ = v___y_2111_;
v___y_2105_ = v___y_2112_;
v___y_2106_ = v___y_2114_;
v___y_2107_ = v___y_2113_;
v___y_2108_ = v___y_2115_;
v___y_2109_ = v___x_2118_;
goto v___jp_2103_;
}
}
v___jp_2120_:
{
uint32_t v___x_2127_; uint8_t v___x_2128_; 
v___x_2127_ = 97;
v___x_2128_ = lean_uint32_dec_le(v___x_2127_, v___y_2126_);
if (v___x_2128_ == 0)
{
v___y_2111_ = v___y_2121_;
v___y_2112_ = v___y_2122_;
v___y_2113_ = v___y_2124_;
v___y_2114_ = v___y_2123_;
v___y_2115_ = v___y_2125_;
v___y_2116_ = v___y_2126_;
goto v___jp_2110_;
}
else
{
uint32_t v___x_2129_; uint8_t v___x_2130_; 
v___x_2129_ = 122;
v___x_2130_ = lean_uint32_dec_le(v___y_2126_, v___x_2129_);
if (v___x_2130_ == 0)
{
v___y_2111_ = v___y_2121_;
v___y_2112_ = v___y_2122_;
v___y_2113_ = v___y_2124_;
v___y_2114_ = v___y_2123_;
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
v___y_2109_ = v___x_2130_;
goto v___jp_2103_;
}
}
}
v___jp_2131_:
{
if (v___y_2134_ == 0)
{
lean_object* v___x_2135_; uint8_t v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; uint8_t v___x_2141_; lean_object* v___x_2142_; 
v___x_2135_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2136_ = 0;
v___x_2137_ = lean_box(v___x_2136_);
v___x_2138_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2135_, v___y_2132_, v___x_2137_);
lean_dec(v___x_2137_);
lean_dec_ref(v___y_2132_);
v___x_2139_ = lean_unsigned_to_nat(5u);
v___x_2140_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2140_, 0, v_x_2047_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
v___x_2141_ = lean_unbox(v___x_2138_);
lean_dec(v___x_2138_);
lean_ctor_set_uint8(v___x_2140_, sizeof(void*)*2, v___x_2141_);
v___x_2142_ = lean_array_push(v___y_2133_, v___x_2140_);
return v___x_2142_;
}
else
{
lean_dec_ref(v___y_2132_);
lean_dec(v_x_2047_);
return v___y_2133_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(lean_object* v_text_2658_, size_t v_sz_2659_, size_t v_i_2660_, lean_object* v_bs_2661_){
_start:
{
uint8_t v___x_2662_; 
v___x_2662_ = lean_usize_dec_lt(v_i_2660_, v_sz_2659_);
if (v___x_2662_ == 0)
{
lean_dec_ref(v_text_2658_);
return v_bs_2661_;
}
else
{
lean_object* v_v_2663_; lean_object* v___x_2664_; lean_object* v_bs_x27_2665_; lean_object* v___x_2666_; size_t v___x_2667_; size_t v___x_2668_; lean_object* v___x_2669_; 
v_v_2663_ = lean_array_uget(v_bs_2661_, v_i_2660_);
v___x_2664_ = lean_unsigned_to_nat(0u);
v_bs_x27_2665_ = lean_array_uset(v_bs_2661_, v_i_2660_, v___x_2664_);
lean_inc_ref(v_text_2658_);
v___x_2666_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2658_, v_v_2663_);
v___x_2667_ = ((size_t)1ULL);
v___x_2668_ = lean_usize_add(v_i_2660_, v___x_2667_);
v___x_2669_ = lean_array_uset(v_bs_x27_2665_, v_i_2660_, v___x_2666_);
v_i_2660_ = v___x_2668_;
v_bs_2661_ = v___x_2669_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3___boxed(lean_object* v_text_2671_, lean_object* v_sz_2672_, lean_object* v_i_2673_, lean_object* v_bs_2674_){
_start:
{
size_t v_sz_boxed_2675_; size_t v_i_boxed_2676_; lean_object* v_res_2677_; 
v_sz_boxed_2675_ = lean_unbox_usize(v_sz_2672_);
lean_dec(v_sz_2672_);
v_i_boxed_2676_ = lean_unbox_usize(v_i_2673_);
lean_dec(v_i_2673_);
v_res_2677_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2671_, v_sz_boxed_2675_, v_i_boxed_2676_, v_bs_2674_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(lean_object* v_00_u03b4_2678_, lean_object* v_t_2679_, lean_object* v_k_2680_, lean_object* v_fallback_2681_){
_start:
{
lean_object* v___x_2682_; 
v___x_2682_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v_t_2679_, v_k_2680_, v_fallback_2681_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___boxed(lean_object* v_00_u03b4_2683_, lean_object* v_t_2684_, lean_object* v_k_2685_, lean_object* v_fallback_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(v_00_u03b4_2683_, v_t_2684_, v_k_2685_, v_fallback_2686_);
lean_dec(v_fallback_2686_);
lean_dec_ref(v_k_2685_);
lean_dec(v_t_2684_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(lean_object* v_x_2688_, lean_object* v_info_2689_, lean_object* v_x_2690_){
_start:
{
if (lean_obj_tag(v_info_2689_) == 1)
{
lean_object* v_i_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2735_; 
v_i_2691_ = lean_ctor_get(v_info_2689_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v_info_2689_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2693_ = v_info_2689_;
v_isShared_2694_ = v_isSharedCheck_2735_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_i_2691_);
lean_dec(v_info_2689_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2735_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v_toElabInfo_2695_; lean_object* v_lctx_2696_; lean_object* v_expr_2697_; uint8_t v_isBinder_2698_; lean_object* v_stx_2699_; lean_object* v___x_2716_; 
v_toElabInfo_2695_ = lean_ctor_get(v_i_2691_, 0);
lean_inc_ref(v_toElabInfo_2695_);
v_lctx_2696_ = lean_ctor_get(v_i_2691_, 1);
lean_inc_ref(v_lctx_2696_);
v_expr_2697_ = lean_ctor_get(v_i_2691_, 3);
lean_inc_ref(v_expr_2697_);
v_isBinder_2698_ = lean_ctor_get_uint8(v_i_2691_, sizeof(void*)*4);
lean_dec_ref(v_i_2691_);
v_stx_2699_ = lean_ctor_get(v_toElabInfo_2695_, 1);
lean_inc(v_stx_2699_);
lean_dec_ref(v_toElabInfo_2695_);
v___x_2716_ = l_Lean_Syntax_getHeadInfo(v_stx_2699_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v___x_2717_; uint8_t v___x_2718_; 
lean_dec_ref_known(v___x_2716_, 4);
v___x_2717_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__10));
lean_inc(v_stx_2699_);
v___x_2718_ = l_Lean_Syntax_isOfKind(v_stx_2699_, v___x_2717_);
if (v___x_2718_ == 0)
{
lean_dec_ref(v_expr_2697_);
lean_dec_ref(v_lctx_2696_);
lean_del_object(v___x_2693_);
goto v___jp_2707_;
}
else
{
if (lean_obj_tag(v_expr_2697_) == 1)
{
lean_object* v_fvarId_2719_; lean_object* v___x_2720_; 
v_fvarId_2719_ = lean_ctor_get(v_expr_2697_, 0);
lean_inc(v_fvarId_2719_);
lean_dec_ref_known(v_expr_2697_, 1);
v___x_2720_ = lean_local_ctx_find(v_lctx_2696_, v_fvarId_2719_);
if (lean_obj_tag(v___x_2720_) == 1)
{
lean_object* v_val_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2733_; 
v_val_2721_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2723_ = v___x_2720_;
v_isShared_2724_ = v_isSharedCheck_2733_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_val_2721_);
lean_dec(v___x_2720_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2733_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
uint8_t v___x_2725_; 
v___x_2725_ = l_Lean_LocalDecl_isAuxDecl(v_val_2721_);
if (v___x_2725_ == 0)
{
uint8_t v___x_2726_; 
lean_del_object(v___x_2723_);
v___x_2726_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2721_);
lean_dec(v_val_2721_);
if (v___x_2726_ == 0)
{
goto v___jp_2700_;
}
else
{
if (v___x_2725_ == 0)
{
lean_del_object(v___x_2693_);
goto v___jp_2707_;
}
else
{
goto v___jp_2700_;
}
}
}
else
{
lean_dec(v_val_2721_);
lean_del_object(v___x_2693_);
if (v_isBinder_2698_ == 0)
{
lean_del_object(v___x_2723_);
goto v___jp_2707_;
}
else
{
uint8_t v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2731_; 
v___x_2727_ = 3;
v___x_2728_ = lean_unsigned_to_nat(5u);
v___x_2729_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2729_, 0, v_stx_2699_);
lean_ctor_set(v___x_2729_, 1, v___x_2728_);
lean_ctor_set_uint8(v___x_2729_, sizeof(void*)*2, v___x_2727_);
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 0, v___x_2729_);
v___x_2731_ = v___x_2723_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v___x_2729_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
}
}
else
{
lean_dec(v___x_2720_);
lean_del_object(v___x_2693_);
goto v___jp_2707_;
}
}
else
{
lean_dec_ref(v_expr_2697_);
lean_dec_ref(v_lctx_2696_);
lean_del_object(v___x_2693_);
goto v___jp_2707_;
}
}
}
else
{
lean_object* v___x_2734_; 
lean_dec(v___x_2716_);
lean_dec(v_stx_2699_);
lean_dec_ref(v_expr_2697_);
lean_dec_ref(v_lctx_2696_);
lean_del_object(v___x_2693_);
v___x_2734_ = lean_box(0);
return v___x_2734_;
}
v___jp_2700_:
{
uint8_t v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2705_; 
v___x_2701_ = 1;
v___x_2702_ = lean_unsigned_to_nat(5u);
v___x_2703_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2703_, 0, v_stx_2699_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
lean_ctor_set_uint8(v___x_2703_, sizeof(void*)*2, v___x_2701_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 0, v___x_2703_);
v___x_2705_ = v___x_2693_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2703_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
v___jp_2707_:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; uint8_t v___x_2710_; 
lean_inc(v_stx_2699_);
v___x_2708_ = l_Lean_Syntax_getKind(v_stx_2699_);
v___x_2709_ = l_Lean_Parser_Term_identProjKind;
v___x_2710_ = lean_name_eq(v___x_2708_, v___x_2709_);
lean_dec(v___x_2708_);
if (v___x_2710_ == 0)
{
lean_object* v___x_2711_; 
lean_dec(v_stx_2699_);
v___x_2711_ = lean_box(0);
return v___x_2711_;
}
else
{
uint8_t v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2712_ = 2;
v___x_2713_ = lean_unsigned_to_nat(5u);
v___x_2714_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2714_, 0, v_stx_2699_);
lean_ctor_set(v___x_2714_, 1, v___x_2713_);
lean_ctor_set_uint8(v___x_2714_, sizeof(void*)*2, v___x_2712_);
v___x_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2714_);
return v___x_2715_;
}
}
}
}
else
{
lean_object* v___x_2736_; 
lean_dec_ref(v_info_2689_);
v___x_2736_ = lean_box(0);
return v___x_2736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0___boxed(lean_object* v_x_2737_, lean_object* v_info_2738_, lean_object* v_x_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(v_x_2737_, v_info_2738_, v_x_2739_);
lean_dec_ref(v_x_2739_);
lean_dec_ref(v_x_2737_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(lean_object* v_i_2742_){
_start:
{
lean_object* v___f_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___f_2743_ = ((lean_object*)(l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___closed__0));
v___x_2744_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_2743_, v_i_2742_);
v___x_2745_ = lean_array_mk(v___x_2744_);
return v___x_2745_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_dbgShowTokens___lam__0(lean_object* v_x_2746_, lean_object* v_y_2747_){
_start:
{
lean_object* v_fst_2748_; lean_object* v_fst_2749_; uint8_t v___x_2750_; 
v_fst_2748_ = lean_ctor_get(v_x_2746_, 0);
v_fst_2749_ = lean_ctor_get(v_y_2747_, 0);
v___x_2750_ = lean_nat_dec_le(v_fst_2748_, v_fst_2749_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___lam__0___boxed(lean_object* v_x_2751_, lean_object* v_y_2752_){
_start:
{
uint8_t v_res_2753_; lean_object* v_r_2754_; 
v_res_2753_ = l_Lean_Server_FileWorker_dbgShowTokens___lam__0(v_x_2751_, v_y_2752_);
lean_dec_ref(v_y_2752_);
lean_dec_ref(v_x_2751_);
v_r_2754_ = lean_box(v_res_2753_);
return v_r_2754_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(lean_object* v_x_2755_, lean_object* v_x_2756_){
_start:
{
if (lean_obj_tag(v_x_2756_) == 0)
{
lean_inc(v_x_2755_);
return v_x_2755_;
}
else
{
lean_object* v_key_2757_; lean_object* v_value_2758_; lean_object* v_tail_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v_key_2757_ = lean_ctor_get(v_x_2756_, 0);
v_value_2758_ = lean_ctor_get(v_x_2756_, 1);
v_tail_2759_ = lean_ctor_get(v_x_2756_, 2);
v___x_2760_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_2755_, v_tail_2759_);
lean_inc(v_value_2758_);
lean_inc(v_key_2757_);
v___x_2761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2761_, 0, v_key_2757_);
lean_ctor_set(v___x_2761_, 1, v_value_2758_);
v___x_2762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2761_);
lean_ctor_set(v___x_2762_, 1, v___x_2760_);
return v___x_2762_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5___boxed(lean_object* v_x_2763_, lean_object* v_x_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_2763_, v_x_2764_);
lean_dec(v_x_2764_);
lean_dec(v_x_2763_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(lean_object* v_as_2766_, size_t v_i_2767_, size_t v_stop_2768_, lean_object* v_b_2769_){
_start:
{
uint8_t v___x_2770_; 
v___x_2770_ = lean_usize_dec_eq(v_i_2767_, v_stop_2768_);
if (v___x_2770_ == 0)
{
size_t v___x_2771_; size_t v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2771_ = ((size_t)1ULL);
v___x_2772_ = lean_usize_sub(v_i_2767_, v___x_2771_);
v___x_2773_ = lean_array_uget_borrowed(v_as_2766_, v___x_2772_);
v___x_2774_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_b_2769_, v___x_2773_);
lean_dec(v_b_2769_);
v_i_2767_ = v___x_2772_;
v_b_2769_ = v___x_2774_;
goto _start;
}
else
{
return v_b_2769_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6___boxed(lean_object* v_as_2776_, lean_object* v_i_2777_, lean_object* v_stop_2778_, lean_object* v_b_2779_){
_start:
{
size_t v_i_boxed_2780_; size_t v_stop_boxed_2781_; lean_object* v_res_2782_; 
v_i_boxed_2780_ = lean_unbox_usize(v_i_2777_);
lean_dec(v_i_2777_);
v_stop_boxed_2781_ = lean_unbox_usize(v_stop_2778_);
lean_dec(v_stop_2778_);
v_res_2782_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_as_2776_, v_i_boxed_2780_, v_stop_boxed_2781_, v_b_2779_);
lean_dec_ref(v_as_2776_);
return v_res_2782_;
}
}
LEAN_EXPORT uint8_t l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(lean_object* v_x_2783_, lean_object* v_y_2784_){
_start:
{
lean_object* v_fst_2785_; lean_object* v_fst_2786_; uint8_t v___x_2787_; 
v_fst_2785_ = lean_ctor_get(v_x_2783_, 0);
v_fst_2786_ = lean_ctor_get(v_y_2784_, 0);
v___x_2787_ = lean_nat_dec_le(v_fst_2785_, v_fst_2786_);
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0___boxed(lean_object* v_x_2788_, lean_object* v_y_2789_){
_start:
{
uint8_t v_res_2790_; lean_object* v_r_2791_; 
v_res_2790_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(v_x_2788_, v_y_2789_);
lean_dec_ref(v_y_2789_);
lean_dec_ref(v_x_2788_);
v_r_2791_ = lean_box(v_res_2790_);
return v_r_2791_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(lean_object* v_x_2795_, lean_object* v_x_2796_){
_start:
{
if (lean_obj_tag(v_x_2796_) == 0)
{
return v_x_2795_;
}
else
{
lean_object* v_head_2797_; lean_object* v_snd_2798_; lean_object* v_snd_2799_; lean_object* v_tail_2800_; lean_object* v_fst_2801_; lean_object* v_fst_2802_; lean_object* v_fst_2803_; lean_object* v_snd_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; uint8_t v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v_fst_2814_; lean_object* v_snd_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v_head_2797_ = lean_ctor_get(v_x_2796_, 0);
lean_inc(v_head_2797_);
v_snd_2798_ = lean_ctor_get(v_head_2797_, 1);
lean_inc(v_snd_2798_);
v_snd_2799_ = lean_ctor_get(v_snd_2798_, 1);
lean_inc(v_snd_2799_);
v_tail_2800_ = lean_ctor_get(v_x_2796_, 1);
lean_inc(v_tail_2800_);
lean_dec_ref_known(v_x_2796_, 2);
v_fst_2801_ = lean_ctor_get(v_head_2797_, 0);
lean_inc(v_fst_2801_);
lean_dec(v_head_2797_);
v_fst_2802_ = lean_ctor_get(v_snd_2798_, 0);
lean_inc(v_fst_2802_);
lean_dec(v_snd_2798_);
v_fst_2803_ = lean_ctor_get(v_snd_2799_, 0);
lean_inc(v_fst_2803_);
v_snd_2804_ = lean_ctor_get(v_snd_2799_, 1);
lean_inc(v_snd_2804_);
lean_dec(v_snd_2799_);
v___x_2805_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_2806_ = l_Nat_reprFast(v_fst_2801_);
v___x_2807_ = lean_string_append(v___x_2805_, v___x_2806_);
lean_dec_ref(v___x_2806_);
v___x_2808_ = lean_box(0);
v___x_2809_ = 0;
v___x_2810_ = l_Lean_Syntax_formatStx(v_fst_2803_, v___x_2808_, v___x_2809_);
v___x_2811_ = l_Std_Format_defWidth;
v___x_2812_ = lean_unsigned_to_nat(0u);
v___x_2813_ = l_Std_Format_pretty(v___x_2810_, v___x_2811_, v___x_2812_, v___x_2812_);
v_fst_2814_ = lean_ctor_get(v_snd_2804_, 0);
lean_inc(v_fst_2814_);
v_snd_2815_ = lean_ctor_get(v_snd_2804_, 1);
lean_inc(v_snd_2815_);
lean_dec(v_snd_2804_);
v___x_2816_ = l_Nat_reprFast(v_fst_2802_);
v___x_2817_ = lean_string_append(v___x_2805_, v___x_2816_);
lean_dec_ref(v___x_2816_);
v___x_2818_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_2819_ = lean_string_append(v_x_2795_, v___x_2818_);
v___x_2820_ = lean_string_append(v___x_2807_, v___x_2818_);
v___x_2821_ = lean_string_append(v___x_2817_, v___x_2818_);
v___x_2822_ = lean_string_append(v___x_2805_, v___x_2813_);
lean_dec_ref(v___x_2813_);
v___x_2823_ = lean_string_append(v___x_2822_, v___x_2818_);
v___x_2824_ = lean_unsigned_to_nat(80u);
v___x_2825_ = l_Lean_Json_pretty(v_fst_2814_, v___x_2824_);
v___x_2826_ = lean_string_append(v___x_2805_, v___x_2825_);
lean_dec_ref(v___x_2825_);
v___x_2827_ = lean_string_append(v___x_2826_, v___x_2818_);
v___x_2828_ = l_Nat_reprFast(v_snd_2815_);
v___x_2829_ = lean_string_append(v___x_2827_, v___x_2828_);
lean_dec_ref(v___x_2828_);
v___x_2830_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_2831_ = lean_string_append(v___x_2829_, v___x_2830_);
v___x_2832_ = lean_string_append(v___x_2823_, v___x_2831_);
lean_dec_ref(v___x_2831_);
v___x_2833_ = lean_string_append(v___x_2832_, v___x_2830_);
v___x_2834_ = lean_string_append(v___x_2821_, v___x_2833_);
lean_dec_ref(v___x_2833_);
v___x_2835_ = lean_string_append(v___x_2834_, v___x_2830_);
v___x_2836_ = lean_string_append(v___x_2820_, v___x_2835_);
lean_dec_ref(v___x_2835_);
v___x_2837_ = lean_string_append(v___x_2836_, v___x_2830_);
v___x_2838_ = lean_string_append(v___x_2819_, v___x_2837_);
lean_dec_ref(v___x_2837_);
v_x_2795_ = v___x_2838_;
v_x_2796_ = v_tail_2800_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(lean_object* v_x_2843_){
_start:
{
if (lean_obj_tag(v_x_2843_) == 0)
{
lean_object* v___x_2844_; 
v___x_2844_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__0));
return v___x_2844_;
}
else
{
lean_object* v_tail_2845_; 
v_tail_2845_ = lean_ctor_get(v_x_2843_, 1);
if (lean_obj_tag(v_tail_2845_) == 0)
{
lean_object* v_head_2846_; lean_object* v_snd_2847_; lean_object* v_snd_2848_; lean_object* v_fst_2849_; lean_object* v_fst_2850_; lean_object* v_fst_2851_; lean_object* v_snd_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; uint8_t v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v_fst_2862_; lean_object* v_snd_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
v_head_2846_ = lean_ctor_get(v_x_2843_, 0);
lean_inc(v_head_2846_);
lean_dec_ref_known(v_x_2843_, 2);
v_snd_2847_ = lean_ctor_get(v_head_2846_, 1);
lean_inc(v_snd_2847_);
v_snd_2848_ = lean_ctor_get(v_snd_2847_, 1);
lean_inc(v_snd_2848_);
v_fst_2849_ = lean_ctor_get(v_head_2846_, 0);
lean_inc(v_fst_2849_);
lean_dec(v_head_2846_);
v_fst_2850_ = lean_ctor_get(v_snd_2847_, 0);
lean_inc(v_fst_2850_);
lean_dec(v_snd_2847_);
v_fst_2851_ = lean_ctor_get(v_snd_2848_, 0);
lean_inc(v_fst_2851_);
v_snd_2852_ = lean_ctor_get(v_snd_2848_, 1);
lean_inc(v_snd_2852_);
lean_dec(v_snd_2848_);
v___x_2853_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_2854_ = l_Nat_reprFast(v_fst_2849_);
v___x_2855_ = lean_string_append(v___x_2853_, v___x_2854_);
lean_dec_ref(v___x_2854_);
v___x_2856_ = lean_box(0);
v___x_2857_ = 0;
v___x_2858_ = l_Lean_Syntax_formatStx(v_fst_2851_, v___x_2856_, v___x_2857_);
v___x_2859_ = l_Std_Format_defWidth;
v___x_2860_ = lean_unsigned_to_nat(0u);
v___x_2861_ = l_Std_Format_pretty(v___x_2858_, v___x_2859_, v___x_2860_, v___x_2860_);
v_fst_2862_ = lean_ctor_get(v_snd_2852_, 0);
lean_inc(v_fst_2862_);
v_snd_2863_ = lean_ctor_get(v_snd_2852_, 1);
lean_inc(v_snd_2863_);
lean_dec(v_snd_2852_);
v___x_2864_ = l_Nat_reprFast(v_fst_2850_);
v___x_2865_ = lean_string_append(v___x_2853_, v___x_2864_);
lean_dec_ref(v___x_2864_);
v___x_2866_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_2867_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_2868_ = lean_string_append(v___x_2855_, v___x_2867_);
v___x_2869_ = lean_string_append(v___x_2865_, v___x_2867_);
v___x_2870_ = lean_string_append(v___x_2853_, v___x_2861_);
lean_dec_ref(v___x_2861_);
v___x_2871_ = lean_string_append(v___x_2870_, v___x_2867_);
v___x_2872_ = lean_unsigned_to_nat(80u);
v___x_2873_ = l_Lean_Json_pretty(v_fst_2862_, v___x_2872_);
v___x_2874_ = lean_string_append(v___x_2853_, v___x_2873_);
lean_dec_ref(v___x_2873_);
v___x_2875_ = lean_string_append(v___x_2874_, v___x_2867_);
v___x_2876_ = l_Nat_reprFast(v_snd_2863_);
v___x_2877_ = lean_string_append(v___x_2875_, v___x_2876_);
lean_dec_ref(v___x_2876_);
v___x_2878_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_2879_ = lean_string_append(v___x_2877_, v___x_2878_);
v___x_2880_ = lean_string_append(v___x_2871_, v___x_2879_);
lean_dec_ref(v___x_2879_);
v___x_2881_ = lean_string_append(v___x_2880_, v___x_2878_);
v___x_2882_ = lean_string_append(v___x_2869_, v___x_2881_);
lean_dec_ref(v___x_2881_);
v___x_2883_ = lean_string_append(v___x_2882_, v___x_2878_);
v___x_2884_ = lean_string_append(v___x_2868_, v___x_2883_);
lean_dec_ref(v___x_2883_);
v___x_2885_ = lean_string_append(v___x_2884_, v___x_2878_);
v___x_2886_ = lean_string_append(v___x_2866_, v___x_2885_);
lean_dec_ref(v___x_2885_);
v___x_2887_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__2));
v___x_2888_ = lean_string_append(v___x_2886_, v___x_2887_);
return v___x_2888_;
}
else
{
lean_object* v_head_2889_; lean_object* v_snd_2890_; lean_object* v_snd_2891_; lean_object* v_fst_2892_; lean_object* v_fst_2893_; lean_object* v_fst_2894_; lean_object* v_snd_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; uint8_t v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v_fst_2905_; lean_object* v_snd_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; uint32_t v___x_2931_; lean_object* v___x_2932_; 
lean_inc(v_tail_2845_);
v_head_2889_ = lean_ctor_get(v_x_2843_, 0);
lean_inc(v_head_2889_);
lean_dec_ref_known(v_x_2843_, 2);
v_snd_2890_ = lean_ctor_get(v_head_2889_, 1);
lean_inc(v_snd_2890_);
v_snd_2891_ = lean_ctor_get(v_snd_2890_, 1);
lean_inc(v_snd_2891_);
v_fst_2892_ = lean_ctor_get(v_head_2889_, 0);
lean_inc(v_fst_2892_);
lean_dec(v_head_2889_);
v_fst_2893_ = lean_ctor_get(v_snd_2890_, 0);
lean_inc(v_fst_2893_);
lean_dec(v_snd_2890_);
v_fst_2894_ = lean_ctor_get(v_snd_2891_, 0);
lean_inc(v_fst_2894_);
v_snd_2895_ = lean_ctor_get(v_snd_2891_, 1);
lean_inc(v_snd_2895_);
lean_dec(v_snd_2891_);
v___x_2896_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_2897_ = l_Nat_reprFast(v_fst_2892_);
v___x_2898_ = lean_string_append(v___x_2896_, v___x_2897_);
lean_dec_ref(v___x_2897_);
v___x_2899_ = lean_box(0);
v___x_2900_ = 0;
v___x_2901_ = l_Lean_Syntax_formatStx(v_fst_2894_, v___x_2899_, v___x_2900_);
v___x_2902_ = l_Std_Format_defWidth;
v___x_2903_ = lean_unsigned_to_nat(0u);
v___x_2904_ = l_Std_Format_pretty(v___x_2901_, v___x_2902_, v___x_2903_, v___x_2903_);
v_fst_2905_ = lean_ctor_get(v_snd_2895_, 0);
lean_inc(v_fst_2905_);
v_snd_2906_ = lean_ctor_get(v_snd_2895_, 1);
lean_inc(v_snd_2906_);
lean_dec(v_snd_2895_);
v___x_2907_ = l_Nat_reprFast(v_fst_2893_);
v___x_2908_ = lean_string_append(v___x_2896_, v___x_2907_);
lean_dec_ref(v___x_2907_);
v___x_2909_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_2910_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_2911_ = lean_string_append(v___x_2898_, v___x_2910_);
v___x_2912_ = lean_string_append(v___x_2908_, v___x_2910_);
v___x_2913_ = lean_string_append(v___x_2896_, v___x_2904_);
lean_dec_ref(v___x_2904_);
v___x_2914_ = lean_string_append(v___x_2913_, v___x_2910_);
v___x_2915_ = lean_unsigned_to_nat(80u);
v___x_2916_ = l_Lean_Json_pretty(v_fst_2905_, v___x_2915_);
v___x_2917_ = lean_string_append(v___x_2896_, v___x_2916_);
lean_dec_ref(v___x_2916_);
v___x_2918_ = lean_string_append(v___x_2917_, v___x_2910_);
v___x_2919_ = l_Nat_reprFast(v_snd_2906_);
v___x_2920_ = lean_string_append(v___x_2918_, v___x_2919_);
lean_dec_ref(v___x_2919_);
v___x_2921_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_2922_ = lean_string_append(v___x_2920_, v___x_2921_);
v___x_2923_ = lean_string_append(v___x_2914_, v___x_2922_);
lean_dec_ref(v___x_2922_);
v___x_2924_ = lean_string_append(v___x_2923_, v___x_2921_);
v___x_2925_ = lean_string_append(v___x_2912_, v___x_2924_);
lean_dec_ref(v___x_2924_);
v___x_2926_ = lean_string_append(v___x_2925_, v___x_2921_);
v___x_2927_ = lean_string_append(v___x_2911_, v___x_2926_);
lean_dec_ref(v___x_2926_);
v___x_2928_ = lean_string_append(v___x_2927_, v___x_2921_);
v___x_2929_ = lean_string_append(v___x_2909_, v___x_2928_);
lean_dec_ref(v___x_2928_);
v___x_2930_ = l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(v___x_2929_, v_tail_2845_);
v___x_2931_ = 93;
v___x_2932_ = lean_string_push(v___x_2930_, v___x_2931_);
return v___x_2932_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(lean_object* v_a_2933_, lean_object* v_a_2934_){
_start:
{
if (lean_obj_tag(v_a_2933_) == 0)
{
lean_object* v___x_2935_; 
v___x_2935_ = l_List_reverse___redArg(v_a_2934_);
return v___x_2935_;
}
else
{
lean_object* v_head_2936_; lean_object* v_snd_2937_; lean_object* v_snd_2938_; lean_object* v_tail_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2971_; 
v_head_2936_ = lean_ctor_get(v_a_2933_, 0);
lean_inc(v_head_2936_);
v_snd_2937_ = lean_ctor_get(v_head_2936_, 1);
lean_inc(v_snd_2937_);
v_snd_2938_ = lean_ctor_get(v_snd_2937_, 1);
lean_inc(v_snd_2938_);
v_tail_2939_ = lean_ctor_get(v_a_2933_, 1);
v_isSharedCheck_2971_ = !lean_is_exclusive(v_a_2933_);
if (v_isSharedCheck_2971_ == 0)
{
lean_object* v_unused_2972_; 
v_unused_2972_ = lean_ctor_get(v_a_2933_, 0);
lean_dec(v_unused_2972_);
v___x_2941_ = v_a_2933_;
v_isShared_2942_ = v_isSharedCheck_2971_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_tail_2939_);
lean_dec(v_a_2933_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2971_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v_fst_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2969_; 
v_fst_2943_ = lean_ctor_get(v_head_2936_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v_head_2936_);
if (v_isSharedCheck_2969_ == 0)
{
lean_object* v_unused_2970_; 
v_unused_2970_ = lean_ctor_get(v_head_2936_, 1);
lean_dec(v_unused_2970_);
v___x_2945_ = v_head_2936_;
v_isShared_2946_ = v_isSharedCheck_2969_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_fst_2943_);
lean_dec(v_head_2936_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2969_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v_fst_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2967_; 
v_fst_2947_ = lean_ctor_get(v_snd_2937_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v_snd_2937_);
if (v_isSharedCheck_2967_ == 0)
{
lean_object* v_unused_2968_; 
v_unused_2968_ = lean_ctor_get(v_snd_2937_, 1);
lean_dec(v_unused_2968_);
v___x_2949_ = v_snd_2937_;
v_isShared_2950_ = v_isSharedCheck_2967_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_fst_2947_);
lean_dec(v_snd_2937_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2967_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v_stx_2951_; uint8_t v_type_2952_; lean_object* v_priority_2953_; lean_object* v___x_2954_; lean_object* v___x_2956_; 
v_stx_2951_ = lean_ctor_get(v_snd_2938_, 0);
lean_inc(v_stx_2951_);
v_type_2952_ = lean_ctor_get_uint8(v_snd_2938_, sizeof(void*)*2);
v_priority_2953_ = lean_ctor_get(v_snd_2938_, 1);
lean_inc(v_priority_2953_);
lean_dec(v_snd_2938_);
v___x_2954_ = l_Lean_Lsp_instToJsonSemanticTokenType_toJson(v_type_2952_);
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 1, v_priority_2953_);
lean_ctor_set(v___x_2949_, 0, v___x_2954_);
v___x_2956_ = v___x_2949_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2954_);
lean_ctor_set(v_reuseFailAlloc_2966_, 1, v_priority_2953_);
v___x_2956_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
lean_object* v___x_2958_; 
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 1, v___x_2956_);
lean_ctor_set(v___x_2945_, 0, v_stx_2951_);
v___x_2958_ = v___x_2945_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_stx_2951_);
lean_ctor_set(v_reuseFailAlloc_2965_, 1, v___x_2956_);
v___x_2958_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2962_; 
v___x_2959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2959_, 0, v_fst_2947_);
lean_ctor_set(v___x_2959_, 1, v___x_2958_);
v___x_2960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2960_, 0, v_fst_2943_);
lean_ctor_set(v___x_2960_, 1, v___x_2959_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 1, v_a_2934_);
lean_ctor_set(v___x_2941_, 0, v___x_2960_);
v___x_2962_ = v___x_2941_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2960_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v_a_2934_);
v___x_2962_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
v_a_2933_ = v_tail_2939_;
v_a_2934_ = v___x_2962_;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(lean_object* v_as_x27_2975_, lean_object* v_b_2976_){
_start:
{
if (lean_obj_tag(v_as_x27_2975_) == 0)
{
return v_b_2976_;
}
else
{
lean_object* v_head_2977_; lean_object* v_tail_2978_; lean_object* v_fst_2979_; lean_object* v_snd_2980_; lean_object* v___f_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v_head_2977_ = lean_ctor_get(v_as_x27_2975_, 0);
v_tail_2978_ = lean_ctor_get(v_as_x27_2975_, 1);
v_fst_2979_ = lean_ctor_get(v_head_2977_, 0);
v_snd_2980_ = lean_ctor_get(v_head_2977_, 1);
v___f_2981_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__0));
lean_inc(v_snd_2980_);
v___x_2982_ = lean_array_to_list(v_snd_2980_);
v___x_2983_ = l_List_mergeSort___redArg(v___x_2982_, v___f_2981_);
lean_inc(v_fst_2979_);
v___x_2984_ = l_Nat_reprFast(v_fst_2979_);
v___x_2985_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__1));
v___x_2986_ = lean_string_append(v___x_2984_, v___x_2985_);
v___x_2987_ = lean_box(0);
v___x_2988_ = l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(v___x_2983_, v___x_2987_);
v___x_2989_ = l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(v___x_2988_);
v___x_2990_ = lean_string_append(v___x_2986_, v___x_2989_);
lean_dec_ref(v___x_2989_);
v___x_2991_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0));
v___x_2992_ = lean_string_append(v___x_2990_, v___x_2991_);
v___x_2993_ = lean_string_append(v_b_2976_, v___x_2992_);
lean_dec_ref(v___x_2992_);
v_as_x27_2975_ = v_tail_2978_;
v_b_2976_ = v___x_2993_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___boxed(lean_object* v_as_x27_2995_, lean_object* v_b_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v_as_x27_2995_, v_b_2996_);
lean_dec(v_as_x27_2995_);
return v_res_2997_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(lean_object* v_a_2998_, lean_object* v_x_2999_){
_start:
{
if (lean_obj_tag(v_x_2999_) == 0)
{
uint8_t v___x_3000_; 
v___x_3000_ = 0;
return v___x_3000_;
}
else
{
lean_object* v_key_3001_; lean_object* v_tail_3002_; uint8_t v___x_3003_; 
v_key_3001_ = lean_ctor_get(v_x_2999_, 0);
v_tail_3002_ = lean_ctor_get(v_x_2999_, 2);
v___x_3003_ = lean_nat_dec_eq(v_key_3001_, v_a_2998_);
if (v___x_3003_ == 0)
{
v_x_2999_ = v_tail_3002_;
goto _start;
}
else
{
return v___x_3003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg___boxed(lean_object* v_a_3005_, lean_object* v_x_3006_){
_start:
{
uint8_t v_res_3007_; lean_object* v_r_3008_; 
v_res_3007_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3005_, v_x_3006_);
lean_dec(v_x_3006_);
lean_dec(v_a_3005_);
v_r_3008_ = lean_box(v_res_3007_);
return v_r_3008_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(lean_object* v_x_3009_, lean_object* v_x_3010_){
_start:
{
if (lean_obj_tag(v_x_3010_) == 0)
{
return v_x_3009_;
}
else
{
lean_object* v_key_3011_; lean_object* v_value_3012_; lean_object* v_tail_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3036_; 
v_key_3011_ = lean_ctor_get(v_x_3010_, 0);
v_value_3012_ = lean_ctor_get(v_x_3010_, 1);
v_tail_3013_ = lean_ctor_get(v_x_3010_, 2);
v_isSharedCheck_3036_ = !lean_is_exclusive(v_x_3010_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3015_ = v_x_3010_;
v_isShared_3016_ = v_isSharedCheck_3036_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_tail_3013_);
lean_inc(v_value_3012_);
lean_inc(v_key_3011_);
lean_dec(v_x_3010_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3036_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3017_; uint64_t v___x_3018_; uint64_t v___x_3019_; uint64_t v___x_3020_; uint64_t v_fold_3021_; uint64_t v___x_3022_; uint64_t v___x_3023_; uint64_t v___x_3024_; size_t v___x_3025_; size_t v___x_3026_; size_t v___x_3027_; size_t v___x_3028_; size_t v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3032_; 
v___x_3017_ = lean_array_get_size(v_x_3009_);
v___x_3018_ = lean_uint64_of_nat(v_key_3011_);
v___x_3019_ = 32ULL;
v___x_3020_ = lean_uint64_shift_right(v___x_3018_, v___x_3019_);
v_fold_3021_ = lean_uint64_xor(v___x_3018_, v___x_3020_);
v___x_3022_ = 16ULL;
v___x_3023_ = lean_uint64_shift_right(v_fold_3021_, v___x_3022_);
v___x_3024_ = lean_uint64_xor(v_fold_3021_, v___x_3023_);
v___x_3025_ = lean_uint64_to_usize(v___x_3024_);
v___x_3026_ = lean_usize_of_nat(v___x_3017_);
v___x_3027_ = ((size_t)1ULL);
v___x_3028_ = lean_usize_sub(v___x_3026_, v___x_3027_);
v___x_3029_ = lean_usize_land(v___x_3025_, v___x_3028_);
v___x_3030_ = lean_array_uget_borrowed(v_x_3009_, v___x_3029_);
lean_inc(v___x_3030_);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 2, v___x_3030_);
v___x_3032_ = v___x_3015_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_key_3011_);
lean_ctor_set(v_reuseFailAlloc_3035_, 1, v_value_3012_);
lean_ctor_set(v_reuseFailAlloc_3035_, 2, v___x_3030_);
v___x_3032_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
lean_object* v___x_3033_; 
v___x_3033_ = lean_array_uset(v_x_3009_, v___x_3029_, v___x_3032_);
v_x_3009_ = v___x_3033_;
v_x_3010_ = v_tail_3013_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(lean_object* v_i_3037_, lean_object* v_source_3038_, lean_object* v_target_3039_){
_start:
{
lean_object* v___x_3040_; uint8_t v___x_3041_; 
v___x_3040_ = lean_array_get_size(v_source_3038_);
v___x_3041_ = lean_nat_dec_lt(v_i_3037_, v___x_3040_);
if (v___x_3041_ == 0)
{
lean_dec_ref(v_source_3038_);
lean_dec(v_i_3037_);
return v_target_3039_;
}
else
{
lean_object* v_es_3042_; lean_object* v___x_3043_; lean_object* v_source_3044_; lean_object* v_target_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v_es_3042_ = lean_array_fget(v_source_3038_, v_i_3037_);
v___x_3043_ = lean_box(0);
v_source_3044_ = lean_array_fset(v_source_3038_, v_i_3037_, v___x_3043_);
v_target_3045_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_target_3039_, v_es_3042_);
v___x_3046_ = lean_unsigned_to_nat(1u);
v___x_3047_ = lean_nat_add(v_i_3037_, v___x_3046_);
lean_dec(v_i_3037_);
v_i_3037_ = v___x_3047_;
v_source_3038_ = v_source_3044_;
v_target_3039_ = v_target_3045_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(lean_object* v_data_3049_){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v_nbuckets_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3050_ = lean_array_get_size(v_data_3049_);
v___x_3051_ = lean_unsigned_to_nat(2u);
v_nbuckets_3052_ = lean_nat_mul(v___x_3050_, v___x_3051_);
v___x_3053_ = lean_unsigned_to_nat(0u);
v___x_3054_ = lean_box(0);
v___x_3055_ = lean_mk_array(v_nbuckets_3052_, v___x_3054_);
v___x_3056_ = lean_array_propagate_mark(v_data_3049_, v___x_3055_);
v___x_3057_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v___x_3053_, v_data_3049_, v___x_3056_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(lean_object* v_character_3060_, lean_object* v_a_3061_, lean_object* v_character_3062_, lean_object* v_x_x3f_3063_){
_start:
{
lean_object* v___y_3065_; 
if (lean_obj_tag(v_x_x3f_3063_) == 0)
{
lean_object* v___x_3070_; 
v___x_3070_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___y_3065_ = v___x_3070_;
goto v___jp_3064_;
}
else
{
lean_object* v_val_3071_; 
v_val_3071_ = lean_ctor_get(v_x_x3f_3063_, 0);
lean_inc(v_val_3071_);
lean_dec_ref_known(v_x_x3f_3063_, 1);
v___y_3065_ = v_val_3071_;
goto v___jp_3064_;
}
v___jp_3064_:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3066_, 0, v_character_3060_);
lean_ctor_set(v___x_3066_, 1, v_a_3061_);
v___x_3067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3067_, 0, v_character_3062_);
lean_ctor_set(v___x_3067_, 1, v___x_3066_);
v___x_3068_ = lean_array_push(v___y_3065_, v___x_3067_);
v___x_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3068_);
return v___x_3069_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(lean_object* v_character_3072_, lean_object* v_a_3073_, lean_object* v_character_3074_, lean_object* v_a_3075_, lean_object* v_x_3076_){
_start:
{
if (lean_obj_tag(v_x_3076_) == 0)
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v_val_3079_; lean_object* v___x_3080_; 
v___x_3077_ = lean_box(0);
v___x_3078_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_3072_, v_a_3073_, v_character_3074_, v___x_3077_);
v_val_3079_ = lean_ctor_get(v___x_3078_, 0);
lean_inc(v_val_3079_);
lean_dec(v___x_3078_);
v___x_3080_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3080_, 0, v_a_3075_);
lean_ctor_set(v___x_3080_, 1, v_val_3079_);
lean_ctor_set(v___x_3080_, 2, v_x_3076_);
return v___x_3080_;
}
else
{
lean_object* v_key_3081_; lean_object* v_value_3082_; lean_object* v_tail_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3098_; 
v_key_3081_ = lean_ctor_get(v_x_3076_, 0);
v_value_3082_ = lean_ctor_get(v_x_3076_, 1);
v_tail_3083_ = lean_ctor_get(v_x_3076_, 2);
v_isSharedCheck_3098_ = !lean_is_exclusive(v_x_3076_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3085_ = v_x_3076_;
v_isShared_3086_ = v_isSharedCheck_3098_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_tail_3083_);
lean_inc(v_value_3082_);
lean_inc(v_key_3081_);
lean_dec(v_x_3076_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3098_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
uint8_t v___x_3087_; 
v___x_3087_ = lean_nat_dec_eq(v_key_3081_, v_a_3075_);
if (v___x_3087_ == 0)
{
lean_object* v_tail_3088_; lean_object* v___x_3090_; 
v_tail_3088_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_3072_, v_a_3073_, v_character_3074_, v_a_3075_, v_tail_3083_);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 2, v_tail_3088_);
v___x_3090_ = v___x_3085_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_key_3081_);
lean_ctor_set(v_reuseFailAlloc_3091_, 1, v_value_3082_);
lean_ctor_set(v_reuseFailAlloc_3091_, 2, v_tail_3088_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
else
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v_val_3094_; lean_object* v___x_3096_; 
lean_dec(v_key_3081_);
v___x_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3092_, 0, v_value_3082_);
v___x_3093_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_3072_, v_a_3073_, v_character_3074_, v___x_3092_);
v_val_3094_ = lean_ctor_get(v___x_3093_, 0);
lean_inc(v_val_3094_);
lean_dec(v___x_3093_);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 1, v_val_3094_);
lean_ctor_set(v___x_3085_, 0, v_a_3075_);
v___x_3096_ = v___x_3085_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3075_);
lean_ctor_set(v_reuseFailAlloc_3097_, 1, v_val_3094_);
lean_ctor_set(v_reuseFailAlloc_3097_, 2, v_tail_3083_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(lean_object* v_character_3099_, lean_object* v_a_3100_, lean_object* v_character_3101_, lean_object* v_m_3102_, lean_object* v_a_3103_){
_start:
{
lean_object* v_size_3104_; lean_object* v_buckets_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3157_; 
v_size_3104_ = lean_ctor_get(v_m_3102_, 0);
v_buckets_3105_ = lean_ctor_get(v_m_3102_, 1);
v_isSharedCheck_3157_ = !lean_is_exclusive(v_m_3102_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3107_ = v_m_3102_;
v_isShared_3108_ = v_isSharedCheck_3157_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_buckets_3105_);
lean_inc(v_size_3104_);
lean_dec(v_m_3102_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3157_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3109_; uint64_t v___x_3110_; uint64_t v___x_3111_; uint64_t v___x_3112_; uint64_t v_fold_3113_; uint64_t v___x_3114_; uint64_t v___x_3115_; uint64_t v___x_3116_; size_t v___x_3117_; size_t v___x_3118_; size_t v___x_3119_; size_t v___x_3120_; size_t v___x_3121_; lean_object* v_bkt_3122_; uint8_t v___x_3123_; 
v___x_3109_ = lean_array_get_size(v_buckets_3105_);
v___x_3110_ = lean_uint64_of_nat(v_a_3103_);
v___x_3111_ = 32ULL;
v___x_3112_ = lean_uint64_shift_right(v___x_3110_, v___x_3111_);
v_fold_3113_ = lean_uint64_xor(v___x_3110_, v___x_3112_);
v___x_3114_ = 16ULL;
v___x_3115_ = lean_uint64_shift_right(v_fold_3113_, v___x_3114_);
v___x_3116_ = lean_uint64_xor(v_fold_3113_, v___x_3115_);
v___x_3117_ = lean_uint64_to_usize(v___x_3116_);
v___x_3118_ = lean_usize_of_nat(v___x_3109_);
v___x_3119_ = ((size_t)1ULL);
v___x_3120_ = lean_usize_sub(v___x_3118_, v___x_3119_);
v___x_3121_ = lean_usize_land(v___x_3117_, v___x_3120_);
v_bkt_3122_ = lean_array_uget_borrowed(v_buckets_3105_, v___x_3121_);
v___x_3123_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3103_, v_bkt_3122_);
if (v___x_3123_ == 0)
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v_size_x27_3129_; lean_object* v___x_3130_; lean_object* v_buckets_x27_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; uint8_t v___x_3137_; 
v___x_3124_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___x_3125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3125_, 0, v_character_3099_);
lean_ctor_set(v___x_3125_, 1, v_a_3100_);
v___x_3126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3126_, 0, v_character_3101_);
lean_ctor_set(v___x_3126_, 1, v___x_3125_);
v___x_3127_ = lean_array_push(v___x_3124_, v___x_3126_);
v___x_3128_ = lean_unsigned_to_nat(1u);
v_size_x27_3129_ = lean_nat_add(v_size_3104_, v___x_3128_);
lean_dec(v_size_3104_);
lean_inc(v_bkt_3122_);
v___x_3130_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3130_, 0, v_a_3103_);
lean_ctor_set(v___x_3130_, 1, v___x_3127_);
lean_ctor_set(v___x_3130_, 2, v_bkt_3122_);
v_buckets_x27_3131_ = lean_array_uset(v_buckets_3105_, v___x_3121_, v___x_3130_);
v___x_3132_ = lean_unsigned_to_nat(4u);
v___x_3133_ = lean_nat_mul(v_size_x27_3129_, v___x_3132_);
v___x_3134_ = lean_unsigned_to_nat(3u);
v___x_3135_ = lean_nat_div(v___x_3133_, v___x_3134_);
lean_dec(v___x_3133_);
v___x_3136_ = lean_array_get_size(v_buckets_x27_3131_);
v___x_3137_ = lean_nat_dec_le(v___x_3135_, v___x_3136_);
lean_dec(v___x_3135_);
if (v___x_3137_ == 0)
{
lean_object* v_val_3138_; lean_object* v___x_3140_; 
v_val_3138_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_buckets_x27_3131_);
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 1, v_val_3138_);
lean_ctor_set(v___x_3107_, 0, v_size_x27_3129_);
v___x_3140_ = v___x_3107_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_size_x27_3129_);
lean_ctor_set(v_reuseFailAlloc_3141_, 1, v_val_3138_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
else
{
lean_object* v___x_3143_; 
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 1, v_buckets_x27_3131_);
lean_ctor_set(v___x_3107_, 0, v_size_x27_3129_);
v___x_3143_ = v___x_3107_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_size_x27_3129_);
lean_ctor_set(v_reuseFailAlloc_3144_, 1, v_buckets_x27_3131_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
else
{
lean_object* v___x_3145_; lean_object* v_buckets_x27_3146_; lean_object* v_bkt_x27_3147_; lean_object* v___y_3149_; uint8_t v___x_3154_; 
lean_inc(v_bkt_3122_);
v___x_3145_ = lean_box(0);
v_buckets_x27_3146_ = lean_array_uset(v_buckets_3105_, v___x_3121_, v___x_3145_);
lean_inc(v_a_3103_);
v_bkt_x27_3147_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_3099_, v_a_3100_, v_character_3101_, v_a_3103_, v_bkt_3122_);
v___x_3154_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3103_, v_bkt_x27_3147_);
lean_dec(v_a_3103_);
if (v___x_3154_ == 0)
{
lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3155_ = lean_unsigned_to_nat(1u);
v___x_3156_ = lean_nat_sub(v_size_3104_, v___x_3155_);
lean_dec(v_size_3104_);
v___y_3149_ = v___x_3156_;
goto v___jp_3148_;
}
else
{
v___y_3149_ = v_size_3104_;
goto v___jp_3148_;
}
v___jp_3148_:
{
lean_object* v___x_3150_; lean_object* v___x_3152_; 
v___x_3150_ = lean_array_uset(v_buckets_x27_3146_, v___x_3121_, v_bkt_x27_3147_);
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 1, v___x_3150_);
lean_ctor_set(v___x_3107_, 0, v___y_3149_);
v___x_3152_ = v___x_3107_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___y_3149_);
lean_ctor_set(v_reuseFailAlloc_3153_, 1, v___x_3150_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(lean_object* v_text_3158_, lean_object* v_as_3159_, size_t v_sz_3160_, size_t v_i_3161_, lean_object* v_b_3162_){
_start:
{
lean_object* v_a_3164_; uint8_t v___x_3168_; 
v___x_3168_ = lean_usize_dec_lt(v_i_3161_, v_sz_3160_);
if (v___x_3168_ == 0)
{
lean_dec_ref(v_text_3158_);
return v_b_3162_;
}
else
{
lean_object* v_a_3169_; lean_object* v_stx_3170_; uint8_t v___x_3171_; lean_object* v___x_3172_; 
v_a_3169_ = lean_array_uget_borrowed(v_as_3159_, v_i_3161_);
v_stx_3170_ = lean_ctor_get(v_a_3169_, 0);
v___x_3171_ = 0;
lean_inc_ref(v_text_3158_);
v___x_3172_ = l_Lean_FileMap_lspRangeOfStx_x3f(v_text_3158_, v_stx_3170_, v___x_3171_);
if (lean_obj_tag(v___x_3172_) == 1)
{
lean_object* v_val_3173_; lean_object* v_start_3174_; lean_object* v_end_3175_; lean_object* v_line_3176_; lean_object* v_character_3177_; lean_object* v_character_3178_; lean_object* v___x_3179_; 
v_val_3173_ = lean_ctor_get(v___x_3172_, 0);
lean_inc(v_val_3173_);
lean_dec_ref_known(v___x_3172_, 1);
v_start_3174_ = lean_ctor_get(v_val_3173_, 0);
lean_inc_ref(v_start_3174_);
v_end_3175_ = lean_ctor_get(v_val_3173_, 1);
lean_inc_ref(v_end_3175_);
lean_dec(v_val_3173_);
v_line_3176_ = lean_ctor_get(v_start_3174_, 0);
lean_inc(v_line_3176_);
v_character_3177_ = lean_ctor_get(v_start_3174_, 1);
lean_inc(v_character_3177_);
lean_dec_ref(v_start_3174_);
v_character_3178_ = lean_ctor_get(v_end_3175_, 1);
lean_inc(v_character_3178_);
lean_dec_ref(v_end_3175_);
lean_inc(v_a_3169_);
v___x_3179_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(v_character_3178_, v_a_3169_, v_character_3177_, v_b_3162_, v_line_3176_);
v_a_3164_ = v___x_3179_;
goto v___jp_3163_;
}
else
{
lean_dec(v___x_3172_);
v_a_3164_ = v_b_3162_;
goto v___jp_3163_;
}
}
v___jp_3163_:
{
size_t v___x_3165_; size_t v___x_3166_; 
v___x_3165_ = ((size_t)1ULL);
v___x_3166_ = lean_usize_add(v_i_3161_, v___x_3165_);
v_i_3161_ = v___x_3166_;
v_b_3162_ = v_a_3164_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3___boxed(lean_object* v_text_3180_, lean_object* v_as_3181_, lean_object* v_sz_3182_, lean_object* v_i_3183_, lean_object* v_b_3184_){
_start:
{
size_t v_sz_boxed_3185_; size_t v_i_boxed_3186_; lean_object* v_res_3187_; 
v_sz_boxed_3185_ = lean_unbox_usize(v_sz_3182_);
lean_dec(v_sz_3182_);
v_i_boxed_3186_ = lean_unbox_usize(v_i_3183_);
lean_dec(v_i_3183_);
v_res_3187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3180_, v_as_3181_, v_sz_boxed_3185_, v_i_boxed_3186_, v_b_3184_);
lean_dec_ref(v_as_3181_);
return v_res_3187_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0(void){
_start:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3188_ = lean_box(0);
v___x_3189_ = lean_unsigned_to_nat(16u);
v___x_3190_ = lean_mk_array(v___x_3189_, v___x_3188_);
return v___x_3190_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1(void){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v_byLine_3193_; 
v___x_3191_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__0, &l_Lean_Server_FileWorker_dbgShowTokens___closed__0_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0);
v___x_3192_ = lean_unsigned_to_nat(0u);
v_byLine_3193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byLine_3193_, 0, v___x_3192_);
lean_ctor_set(v_byLine_3193_, 1, v___x_3191_);
return v_byLine_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens(lean_object* v_text_3196_, lean_object* v_toks_3197_){
_start:
{
lean_object* v___x_3198_; lean_object* v_byLine_3199_; size_t v_sz_3200_; size_t v___x_3201_; lean_object* v___x_3202_; lean_object* v_buckets_3203_; lean_object* v___f_3204_; lean_object* v___x_3205_; lean_object* v___y_3207_; lean_object* v___x_3210_; lean_object* v___x_3211_; uint8_t v___x_3212_; 
v___x_3198_ = lean_unsigned_to_nat(0u);
v_byLine_3199_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__1, &l_Lean_Server_FileWorker_dbgShowTokens___closed__1_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1);
v_sz_3200_ = lean_array_size(v_toks_3197_);
v___x_3201_ = ((size_t)0ULL);
v___x_3202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3196_, v_toks_3197_, v_sz_3200_, v___x_3201_, v_byLine_3199_);
v_buckets_3203_ = lean_ctor_get(v___x_3202_, 1);
lean_inc_ref(v_buckets_3203_);
lean_dec_ref(v___x_3202_);
v___f_3204_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__2));
v___x_3205_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__3));
v___x_3210_ = lean_box(0);
v___x_3211_ = lean_array_get_size(v_buckets_3203_);
v___x_3212_ = lean_nat_dec_lt(v___x_3198_, v___x_3211_);
if (v___x_3212_ == 0)
{
lean_dec_ref(v_buckets_3203_);
v___y_3207_ = v___x_3210_;
goto v___jp_3206_;
}
else
{
size_t v___x_3213_; lean_object* v___x_3214_; 
v___x_3213_ = lean_usize_of_nat(v___x_3211_);
v___x_3214_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_buckets_3203_, v___x_3213_, v___x_3201_, v___x_3210_);
lean_dec_ref(v_buckets_3203_);
v___y_3207_ = v___x_3214_;
goto v___jp_3206_;
}
v___jp_3206_:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3208_ = l_List_mergeSort___redArg(v___y_3207_, v___f_3204_);
v___x_3209_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v___x_3208_, v___x_3205_);
lean_dec(v___x_3208_);
return v___x_3209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___boxed(lean_object* v_text_3215_, lean_object* v_toks_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l_Lean_Server_FileWorker_dbgShowTokens(v_text_3215_, v_toks_3216_);
lean_dec_ref(v_toks_3216_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(lean_object* v_as_3218_, lean_object* v_as_x27_3219_, lean_object* v_b_3220_, lean_object* v_a_3221_){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v_as_x27_3219_, v_b_3220_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___boxed(lean_object* v_as_3223_, lean_object* v_as_x27_3224_, lean_object* v_b_3225_, lean_object* v_a_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(v_as_3223_, v_as_x27_3224_, v_b_3225_, v_a_3226_);
lean_dec(v_as_x27_3224_);
lean_dec(v_as_3223_);
return v_res_3227_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(lean_object* v_00_u03b2_3228_, lean_object* v_a_3229_, lean_object* v_x_3230_){
_start:
{
uint8_t v___x_3231_; 
v___x_3231_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3229_, v_x_3230_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3232_, lean_object* v_a_3233_, lean_object* v_x_3234_){
_start:
{
uint8_t v_res_3235_; lean_object* v_r_3236_; 
v_res_3235_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(v_00_u03b2_3232_, v_a_3233_, v_x_3234_);
lean_dec(v_x_3234_);
lean_dec(v_a_3233_);
v_r_3236_ = lean_box(v_res_3235_);
return v_r_3236_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4(lean_object* v_00_u03b2_3237_, lean_object* v_data_3238_){
_start:
{
lean_object* v___x_3239_; 
v___x_3239_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_data_3238_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3240_, lean_object* v_i_3241_, lean_object* v_source_3242_, lean_object* v_target_3243_){
_start:
{
lean_object* v___x_3244_; 
v___x_3244_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v_i_3241_, v_source_3242_, v_target_3243_);
return v___x_3244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10(lean_object* v_00_u03b2_3245_, lean_object* v_x_3246_, lean_object* v_x_3247_){
_start:
{
lean_object* v___x_3248_; 
v___x_3248_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_x_3246_, v_x_3247_);
return v___x_3248_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(lean_object* v_beginPos_3249_, lean_object* v_doc_3250_, lean_object* v_as_x27_3251_, lean_object* v_b_3252_, lean_object* v___y_3253_){
_start:
{
if (lean_obj_tag(v_as_x27_3251_) == 0)
{
lean_object* v___x_3255_; 
lean_dec_ref(v_doc_3250_);
v___x_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3255_, 0, v_b_3252_);
return v___x_3255_;
}
else
{
lean_object* v_head_3256_; lean_object* v_tail_3257_; lean_object* v___x_3258_; uint8_t v___x_3259_; 
v_head_3256_ = lean_ctor_get(v_as_x27_3251_, 0);
v_tail_3257_ = lean_ctor_get(v_as_x27_3251_, 1);
v___x_3258_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_head_3256_);
v___x_3259_ = lean_nat_dec_le(v___x_3258_, v_beginPos_3249_);
lean_dec(v___x_3258_);
if (v___x_3259_ == 0)
{
lean_object* v_toEditableDocumentCore_3260_; lean_object* v_meta_3261_; lean_object* v_text_3262_; lean_object* v_stx_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v_toEditableDocumentCore_3260_ = lean_ctor_get(v_doc_3250_, 0);
v_meta_3261_ = lean_ctor_get(v_toEditableDocumentCore_3260_, 0);
v_text_3262_ = lean_ctor_get(v_meta_3261_, 3);
v_stx_3263_ = lean_ctor_get(v_head_3256_, 0);
lean_inc(v_stx_3263_);
lean_inc_ref(v_text_3262_);
v___x_3264_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_3262_, v_stx_3263_);
lean_inc(v_head_3256_);
v___x_3265_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_head_3256_);
v___x_3266_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(v___x_3265_);
v___x_3267_ = l_Array_append___redArg(v_b_3252_, v___x_3264_);
lean_dec_ref(v___x_3264_);
v___x_3268_ = l_Array_append___redArg(v___x_3267_, v___x_3266_);
lean_dec_ref(v___x_3266_);
v___x_3269_ = l_Lean_Server_RequestM_checkCancelled(v___y_3253_);
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_dec_ref_known(v___x_3269_, 1);
v_as_x27_3251_ = v_tail_3257_;
v_b_3252_ = v___x_3268_;
goto _start;
}
else
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3278_; 
lean_dec_ref(v___x_3268_);
lean_dec_ref(v_doc_3250_);
v_a_3271_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3273_ = v___x_3269_;
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3269_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3276_; 
if (v_isShared_3274_ == 0)
{
v___x_3276_ = v___x_3273_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_a_3271_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
else
{
v_as_x27_3251_ = v_tail_3257_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg___boxed(lean_object* v_beginPos_3280_, lean_object* v_doc_3281_, lean_object* v_as_x27_3282_, lean_object* v_b_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3280_, v_doc_3281_, v_as_x27_3282_, v_b_3283_, v___y_3284_);
lean_dec_ref(v___y_3284_);
lean_dec(v_as_x27_3282_);
lean_dec(v_beginPos_3280_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens(lean_object* v_doc_3287_, lean_object* v_beginPos_3288_, lean_object* v_endPos_x3f_3289_, lean_object* v_snaps_3290_, lean_object* v_a_3291_){
_start:
{
lean_object* v_leanSemanticTokens_3293_; lean_object* v___x_3294_; 
v_leanSemanticTokens_3293_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
lean_inc_ref(v_doc_3287_);
v___x_3294_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3288_, v_doc_3287_, v_snaps_3290_, v_leanSemanticTokens_3293_, v_a_3291_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_toEditableDocumentCore_3295_; lean_object* v_meta_3296_; lean_object* v_a_3297_; lean_object* v_text_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v_toEditableDocumentCore_3295_ = lean_ctor_get(v_doc_3287_, 0);
lean_inc_ref(v_toEditableDocumentCore_3295_);
lean_dec_ref(v_doc_3287_);
v_meta_3296_ = lean_ctor_get(v_toEditableDocumentCore_3295_, 0);
lean_inc_ref(v_meta_3296_);
lean_dec_ref(v_toEditableDocumentCore_3295_);
v_a_3297_ = lean_ctor_get(v___x_3294_, 0);
lean_inc(v_a_3297_);
lean_dec_ref_known(v___x_3294_, 1);
v_text_3298_ = lean_ctor_get(v_meta_3296_, 3);
lean_inc_ref(v_text_3298_);
lean_dec_ref(v_meta_3296_);
v___x_3299_ = l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(v_text_3298_, v_beginPos_3288_, v_endPos_x3f_3289_, v_a_3297_);
lean_dec(v_a_3297_);
v___x_3300_ = l_Lean_Server_RequestM_checkCancelled(v_a_3291_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
lean_dec_ref_known(v___x_3300_, 1);
v___x_3301_ = l_Lean_Server_FileWorker_handleOverlappingSemanticTokens(v___x_3299_);
v___x_3302_ = l_Lean_Server_RequestM_checkCancelled(v_a_3291_);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3310_; 
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3310_ == 0)
{
lean_object* v_unused_3311_; 
v_unused_3311_ = lean_ctor_get(v___x_3302_, 0);
lean_dec(v_unused_3311_);
v___x_3304_ = v___x_3302_;
v_isShared_3305_ = v_isSharedCheck_3310_;
goto v_resetjp_3303_;
}
else
{
lean_dec(v___x_3302_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3310_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3306_; lean_object* v___x_3308_; 
v___x_3306_ = l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(v___x_3301_);
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 0, v___x_3306_);
v___x_3308_ = v___x_3304_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v___x_3306_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
else
{
lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3319_; 
lean_dec_ref(v___x_3301_);
v_a_3312_ = lean_ctor_get(v___x_3302_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3314_ = v___x_3302_;
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v___x_3302_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3317_; 
if (v_isShared_3315_ == 0)
{
v___x_3317_ = v___x_3314_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_a_3312_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
}
else
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3327_; 
lean_dec_ref(v___x_3299_);
v_a_3320_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3322_ = v___x_3300_;
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3300_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3325_; 
if (v_isShared_3323_ == 0)
{
v___x_3325_ = v___x_3322_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3320_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
}
else
{
lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3335_; 
lean_dec_ref(v_doc_3287_);
v_a_3328_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3330_ = v___x_3294_;
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3294_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3333_; 
if (v_isShared_3331_ == 0)
{
v___x_3333_ = v___x_3330_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_a_3328_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens___boxed(lean_object* v_doc_3336_, lean_object* v_beginPos_3337_, lean_object* v_endPos_x3f_3338_, lean_object* v_snaps_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_doc_3336_, v_beginPos_3337_, v_endPos_x3f_3338_, v_snaps_3339_, v_a_3340_);
lean_dec_ref(v_a_3340_);
lean_dec(v_snaps_3339_);
lean_dec(v_endPos_x3f_3338_);
lean_dec(v_beginPos_3337_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(lean_object* v_beginPos_3343_, lean_object* v_doc_3344_, lean_object* v_as_3345_, lean_object* v_as_x27_3346_, lean_object* v_b_3347_, lean_object* v_a_3348_, lean_object* v___y_3349_){
_start:
{
lean_object* v___x_3351_; 
v___x_3351_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3343_, v_doc_3344_, v_as_x27_3346_, v_b_3347_, v___y_3349_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___boxed(lean_object* v_beginPos_3352_, lean_object* v_doc_3353_, lean_object* v_as_3354_, lean_object* v_as_x27_3355_, lean_object* v_b_3356_, lean_object* v_a_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(v_beginPos_3352_, v_doc_3353_, v_as_3354_, v_as_x27_3355_, v_b_3356_, v_a_3357_, v___y_3358_);
lean_dec_ref(v___y_3358_);
lean_dec(v_as_x27_3355_);
lean_dec(v_as_3354_);
lean_dec(v_beginPos_3352_);
return v_res_3360_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState_default(void){
_start:
{
lean_object* v___x_3369_; 
v___x_3369_ = lean_box(0);
return v___x_3369_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState(void){
_start:
{
lean_object* v___x_3370_; 
v___x_3370_ = lean_box(0);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(lean_object* v___y_3371_){
_start:
{
lean_object* v_doc_3373_; lean_object* v___x_3374_; 
v_doc_3373_ = lean_ctor_get(v___y_3371_, 1);
lean_inc_ref(v_doc_3373_);
v___x_3374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3374_, 0, v_doc_3373_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0___boxed(lean_object* v___y_3375_, lean_object* v___y_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v___y_3375_);
lean_dec_ref(v___y_3375_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(lean_object* v_a_3378_){
_start:
{
lean_object* v___x_3380_; lean_object* v_a_3381_; lean_object* v_toEditableDocumentCore_3382_; lean_object* v_cmdSnaps_3383_; lean_object* v_cancelTk_3384_; uint32_t v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v_snd_3388_; lean_object* v_fst_3389_; lean_object* v_snd_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3419_; 
v___x_3380_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_3378_);
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
lean_inc(v_a_3381_);
lean_dec_ref(v___x_3380_);
v_toEditableDocumentCore_3382_ = lean_ctor_get(v_a_3381_, 0);
v_cmdSnaps_3383_ = lean_ctor_get(v_toEditableDocumentCore_3382_, 2);
v_cancelTk_3384_ = lean_ctor_get(v_a_3378_, 4);
v___x_3385_ = 3000;
v___x_3386_ = l_Lean_Server_RequestCancellationToken_cancellationTasks(v_cancelTk_3384_);
lean_inc(v_cmdSnaps_3383_);
v___x_3387_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(v_cmdSnaps_3383_, v___x_3385_, v___x_3386_);
v_snd_3388_ = lean_ctor_get(v___x_3387_, 1);
lean_inc(v_snd_3388_);
v_fst_3389_ = lean_ctor_get(v___x_3387_, 0);
lean_inc(v_fst_3389_);
lean_dec_ref(v___x_3387_);
v_snd_3390_ = lean_ctor_get(v_snd_3388_, 1);
v_isSharedCheck_3419_ = !lean_is_exclusive(v_snd_3388_);
if (v_isSharedCheck_3419_ == 0)
{
lean_object* v_unused_3420_; 
v_unused_3420_ = lean_ctor_get(v_snd_3388_, 0);
lean_dec(v_unused_3420_);
v___x_3392_ = v_snd_3388_;
v_isShared_3393_ = v_isSharedCheck_3419_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_snd_3390_);
lean_dec(v_snd_3388_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3419_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3394_ = lean_unsigned_to_nat(0u);
v___x_3395_ = lean_box(0);
v___x_3396_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_3381_, v___x_3394_, v___x_3395_, v_fst_3389_, v_a_3378_);
lean_dec(v_fst_3389_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v_a_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3410_; 
v_a_3397_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3399_ = v___x_3396_;
v_isShared_3400_ = v_isSharedCheck_3410_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_a_3397_);
lean_dec(v___x_3396_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3410_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
lean_object* v___x_3401_; uint8_t v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3405_; 
v___x_3401_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3401_, 0, v_a_3397_);
v___x_3402_ = lean_unbox(v_snd_3390_);
lean_dec(v_snd_3390_);
lean_ctor_set_uint8(v___x_3401_, sizeof(void*)*1, v___x_3402_);
v___x_3403_ = lean_box(0);
if (v_isShared_3393_ == 0)
{
lean_ctor_set(v___x_3392_, 1, v___x_3403_);
lean_ctor_set(v___x_3392_, 0, v___x_3401_);
v___x_3405_ = v___x_3392_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v___x_3401_);
lean_ctor_set(v_reuseFailAlloc_3409_, 1, v___x_3403_);
v___x_3405_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
lean_object* v___x_3407_; 
if (v_isShared_3400_ == 0)
{
lean_ctor_set(v___x_3399_, 0, v___x_3405_);
v___x_3407_ = v___x_3399_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v___x_3405_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
else
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_del_object(v___x_3392_);
lean_dec(v_snd_3390_);
v_a_3411_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3396_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3396_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg___boxed(lean_object* v_a_3421_, lean_object* v_a_3422_){
_start:
{
lean_object* v_res_3423_; 
v_res_3423_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_3421_);
lean_dec_ref(v_a_3421_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull(lean_object* v_x_3424_, lean_object* v_x_3425_, lean_object* v_a_3426_){
_start:
{
lean_object* v___x_3428_; 
v___x_3428_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_3426_);
return v___x_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___boxed(lean_object* v_x_3429_, lean_object* v_x_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_Lean_Server_FileWorker_handleSemanticTokensFull(v_x_3429_, v_x_3430_, v_a_3431_);
lean_dec_ref(v_a_3431_);
lean_dec_ref(v_x_3429_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(lean_object* v_a_3434_){
_start:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3436_ = lean_box(0);
v___x_3437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3436_);
lean_ctor_set(v___x_3437_, 1, v_a_3434_);
v___x_3438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3437_);
return v___x_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg___boxed(lean_object* v_a_3439_, lean_object* v_a_3440_){
_start:
{
lean_object* v_res_3441_; 
v_res_3441_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_3439_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange(lean_object* v_x_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_){
_start:
{
lean_object* v___x_3446_; 
v___x_3446_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_3443_);
return v___x_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___boxed(lean_object* v_x_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_){
_start:
{
lean_object* v_res_3451_; 
v_res_3451_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange(v_x_3447_, v_a_3448_, v_a_3449_);
lean_dec_ref(v_a_3449_);
lean_dec_ref(v_x_3447_);
return v_res_3451_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(lean_object* v___x_3452_, lean_object* v_x_3453_){
_start:
{
lean_object* v___x_3454_; uint8_t v___x_3455_; 
v___x_3454_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_x_3453_);
v___x_3455_ = lean_nat_dec_le(v___x_3452_, v___x_3454_);
lean_dec(v___x_3454_);
return v___x_3455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed(lean_object* v___x_3456_, lean_object* v_x_3457_){
_start:
{
uint8_t v_res_3458_; lean_object* v_r_3459_; 
v_res_3458_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(v___x_3456_, v_x_3457_);
lean_dec_ref(v_x_3457_);
lean_dec(v___x_3456_);
v_r_3459_ = lean_box(v_res_3458_);
return v_r_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(lean_object* v___x_3460_, lean_object* v_a_3461_, lean_object* v___x_3462_, lean_object* v_x_3463_, lean_object* v___y_3464_){
_start:
{
lean_object* v_fst_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; 
v_fst_3466_ = lean_ctor_get(v_x_3463_, 0);
v___x_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3460_);
v___x_3468_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_3461_, v___x_3462_, v___x_3467_, v_fst_3466_, v___y_3464_);
lean_dec_ref_known(v___x_3467_, 1);
return v___x_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed(lean_object* v___x_3469_, lean_object* v_a_3470_, lean_object* v___x_3471_, lean_object* v_x_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_){
_start:
{
lean_object* v_res_3475_; 
v_res_3475_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(v___x_3469_, v_a_3470_, v___x_3471_, v_x_3472_, v___y_3473_);
lean_dec_ref(v___y_3473_);
lean_dec_ref(v_x_3472_);
lean_dec(v___x_3471_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange(lean_object* v_p_3476_, lean_object* v_a_3477_){
_start:
{
lean_object* v___x_3479_; lean_object* v_a_3480_; lean_object* v_toEditableDocumentCore_3481_; lean_object* v_meta_3482_; lean_object* v_range_3483_; lean_object* v_cmdSnaps_3484_; lean_object* v_text_3485_; lean_object* v_start_3486_; lean_object* v_end_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___f_3490_; lean_object* v___f_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3479_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_3477_);
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_a_3480_);
lean_dec_ref(v___x_3479_);
v_toEditableDocumentCore_3481_ = lean_ctor_get(v_a_3480_, 0);
v_meta_3482_ = lean_ctor_get(v_toEditableDocumentCore_3481_, 0);
v_range_3483_ = lean_ctor_get(v_p_3476_, 1);
lean_inc_ref(v_range_3483_);
lean_dec_ref(v_p_3476_);
v_cmdSnaps_3484_ = lean_ctor_get(v_toEditableDocumentCore_3481_, 2);
lean_inc(v_cmdSnaps_3484_);
v_text_3485_ = lean_ctor_get(v_meta_3482_, 3);
v_start_3486_ = lean_ctor_get(v_range_3483_, 0);
lean_inc_ref(v_start_3486_);
v_end_3487_ = lean_ctor_get(v_range_3483_, 1);
lean_inc_ref(v_end_3487_);
lean_dec_ref(v_range_3483_);
v___x_3488_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_3485_, v_start_3486_);
v___x_3489_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_3485_, v_end_3487_);
lean_inc(v___x_3489_);
v___f_3490_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3490_, 0, v___x_3489_);
v___f_3491_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3491_, 0, v___x_3489_);
lean_closure_set(v___f_3491_, 1, v_a_3480_);
lean_closure_set(v___f_3491_, 2, v___x_3488_);
v___x_3492_ = l_Lean_AsyncList_waitUntil___redArg(v___f_3490_, v_cmdSnaps_3484_);
v___x_3493_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_3492_, v___f_3491_, v_a_3477_);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___boxed(lean_object* v_p_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l_Lean_Server_FileWorker_handleSemanticTokensRange(v_p_3494_, v_a_3495_);
lean_dec_ref(v_a_3495_);
return v_res_3497_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_keys_3498_, lean_object* v_i_3499_, lean_object* v_k_3500_){
_start:
{
lean_object* v___x_3501_; uint8_t v___x_3502_; 
v___x_3501_ = lean_array_get_size(v_keys_3498_);
v___x_3502_ = lean_nat_dec_lt(v_i_3499_, v___x_3501_);
if (v___x_3502_ == 0)
{
lean_dec(v_i_3499_);
return v___x_3502_;
}
else
{
lean_object* v_k_x27_3503_; uint8_t v___x_3504_; 
v_k_x27_3503_ = lean_array_fget_borrowed(v_keys_3498_, v_i_3499_);
v___x_3504_ = lean_string_dec_eq(v_k_3500_, v_k_x27_3503_);
if (v___x_3504_ == 0)
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3505_ = lean_unsigned_to_nat(1u);
v___x_3506_ = lean_nat_add(v_i_3499_, v___x_3505_);
lean_dec(v_i_3499_);
v_i_3499_ = v___x_3506_;
goto _start;
}
else
{
lean_dec(v_i_3499_);
return v___x_3502_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_keys_3508_, lean_object* v_i_3509_, lean_object* v_k_3510_){
_start:
{
uint8_t v_res_3511_; lean_object* v_r_3512_; 
v_res_3511_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_3508_, v_i_3509_, v_k_3510_);
lean_dec_ref(v_k_3510_);
lean_dec_ref(v_keys_3508_);
v_r_3512_ = lean_box(v_res_3511_);
return v_r_3512_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(lean_object* v_x_3513_, size_t v_x_3514_, lean_object* v_x_3515_){
_start:
{
if (lean_obj_tag(v_x_3513_) == 0)
{
lean_object* v_es_3516_; lean_object* v___x_3517_; size_t v___x_3518_; size_t v___x_3519_; lean_object* v_j_3520_; lean_object* v___x_3521_; 
v_es_3516_ = lean_ctor_get(v_x_3513_, 0);
v___x_3517_ = lean_box(2);
v___x_3518_ = ((size_t)31ULL);
v___x_3519_ = lean_usize_land(v_x_3514_, v___x_3518_);
v_j_3520_ = lean_usize_to_nat(v___x_3519_);
v___x_3521_ = lean_array_get_borrowed(v___x_3517_, v_es_3516_, v_j_3520_);
lean_dec(v_j_3520_);
switch(lean_obj_tag(v___x_3521_))
{
case 0:
{
lean_object* v_key_3522_; uint8_t v___x_3523_; 
v_key_3522_ = lean_ctor_get(v___x_3521_, 0);
v___x_3523_ = lean_string_dec_eq(v_x_3515_, v_key_3522_);
return v___x_3523_;
}
case 1:
{
lean_object* v_node_3524_; size_t v___x_3525_; size_t v___x_3526_; 
v_node_3524_ = lean_ctor_get(v___x_3521_, 0);
v___x_3525_ = ((size_t)5ULL);
v___x_3526_ = lean_usize_shift_right(v_x_3514_, v___x_3525_);
v_x_3513_ = v_node_3524_;
v_x_3514_ = v___x_3526_;
goto _start;
}
default: 
{
uint8_t v___x_3528_; 
v___x_3528_ = 0;
return v___x_3528_;
}
}
}
else
{
lean_object* v_ks_3529_; lean_object* v___x_3530_; uint8_t v___x_3531_; 
v_ks_3529_ = lean_ctor_get(v_x_3513_, 0);
v___x_3530_ = lean_unsigned_to_nat(0u);
v___x_3531_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_ks_3529_, v___x_3530_, v_x_3515_);
return v___x_3531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_x_3532_, lean_object* v_x_3533_, lean_object* v_x_3534_){
_start:
{
size_t v_x_2475__boxed_3535_; uint8_t v_res_3536_; lean_object* v_r_3537_; 
v_x_2475__boxed_3535_ = lean_unbox_usize(v_x_3533_);
lean_dec(v_x_3533_);
v_res_3536_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_3532_, v_x_2475__boxed_3535_, v_x_3534_);
lean_dec_ref(v_x_3534_);
lean_dec_ref(v_x_3532_);
v_r_3537_ = lean_box(v_res_3536_);
return v_r_3537_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_x_3538_, lean_object* v_x_3539_){
_start:
{
uint64_t v___x_3540_; size_t v___x_3541_; uint8_t v___x_3542_; 
v___x_3540_ = lean_string_hash(v_x_3539_);
v___x_3541_ = lean_uint64_to_usize(v___x_3540_);
v___x_3542_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_3538_, v___x_3541_, v_x_3539_);
return v___x_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object* v_x_3543_, lean_object* v_x_3544_){
_start:
{
uint8_t v_res_3545_; lean_object* v_r_3546_; 
v_res_3545_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_3543_, v_x_3544_);
lean_dec_ref(v_x_3544_);
lean_dec_ref(v_x_3543_);
v_r_3546_ = lean_box(v_res_3545_);
return v_r_3546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(lean_object* v___x_3547_, lean_object* v_x_3548_){
_start:
{
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4___boxed(lean_object* v___x_3549_, lean_object* v_x_3550_){
_start:
{
lean_object* v_res_3551_; 
v_res_3551_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(v___x_3549_, v_x_3550_);
lean_dec_ref(v_x_3550_);
return v_res_3551_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(lean_object* v_x_3552_, lean_object* v_x_3553_, lean_object* v_x_3554_, lean_object* v_x_3555_){
_start:
{
lean_object* v_ks_3556_; lean_object* v_vs_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3581_; 
v_ks_3556_ = lean_ctor_get(v_x_3552_, 0);
v_vs_3557_ = lean_ctor_get(v_x_3552_, 1);
v_isSharedCheck_3581_ = !lean_is_exclusive(v_x_3552_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3559_ = v_x_3552_;
v_isShared_3560_ = v_isSharedCheck_3581_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_vs_3557_);
lean_inc(v_ks_3556_);
lean_dec(v_x_3552_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3581_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3561_; uint8_t v___x_3562_; 
v___x_3561_ = lean_array_get_size(v_ks_3556_);
v___x_3562_ = lean_nat_dec_lt(v_x_3553_, v___x_3561_);
if (v___x_3562_ == 0)
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3566_; 
lean_dec(v_x_3553_);
v___x_3563_ = lean_array_push(v_ks_3556_, v_x_3554_);
v___x_3564_ = lean_array_push(v_vs_3557_, v_x_3555_);
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 1, v___x_3564_);
lean_ctor_set(v___x_3559_, 0, v___x_3563_);
v___x_3566_ = v___x_3559_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v___x_3563_);
lean_ctor_set(v_reuseFailAlloc_3567_, 1, v___x_3564_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
else
{
lean_object* v_k_x27_3568_; uint8_t v___x_3569_; 
v_k_x27_3568_ = lean_array_fget_borrowed(v_ks_3556_, v_x_3553_);
v___x_3569_ = lean_string_dec_eq(v_x_3554_, v_k_x27_3568_);
if (v___x_3569_ == 0)
{
lean_object* v___x_3571_; 
if (v_isShared_3560_ == 0)
{
v___x_3571_ = v___x_3559_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_ks_3556_);
lean_ctor_set(v_reuseFailAlloc_3575_, 1, v_vs_3557_);
v___x_3571_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3572_ = lean_unsigned_to_nat(1u);
v___x_3573_ = lean_nat_add(v_x_3553_, v___x_3572_);
lean_dec(v_x_3553_);
v_x_3552_ = v___x_3571_;
v_x_3553_ = v___x_3573_;
goto _start;
}
}
else
{
lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3579_; 
v___x_3576_ = lean_array_fset(v_ks_3556_, v_x_3553_, v_x_3554_);
v___x_3577_ = lean_array_fset(v_vs_3557_, v_x_3553_, v_x_3555_);
lean_dec(v_x_3553_);
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 1, v___x_3577_);
lean_ctor_set(v___x_3559_, 0, v___x_3576_);
v___x_3579_ = v___x_3559_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3576_);
lean_ctor_set(v_reuseFailAlloc_3580_, 1, v___x_3577_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(lean_object* v_n_3582_, lean_object* v_k_3583_, lean_object* v_v_3584_){
_start:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; 
v___x_3585_ = lean_unsigned_to_nat(0u);
v___x_3586_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_n_3582_, v___x_3585_, v_k_3583_, v_v_3584_);
return v___x_3586_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_3587_; 
v___x_3587_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(lean_object* v_x_3588_, size_t v_x_3589_, size_t v_x_3590_, lean_object* v_x_3591_, lean_object* v_x_3592_){
_start:
{
if (lean_obj_tag(v_x_3588_) == 0)
{
lean_object* v_es_3593_; size_t v___x_3594_; size_t v___x_3595_; lean_object* v_j_3596_; lean_object* v___x_3597_; uint8_t v___x_3598_; 
v_es_3593_ = lean_ctor_get(v_x_3588_, 0);
v___x_3594_ = ((size_t)31ULL);
v___x_3595_ = lean_usize_land(v_x_3589_, v___x_3594_);
v_j_3596_ = lean_usize_to_nat(v___x_3595_);
v___x_3597_ = lean_array_get_size(v_es_3593_);
v___x_3598_ = lean_nat_dec_lt(v_j_3596_, v___x_3597_);
if (v___x_3598_ == 0)
{
lean_dec(v_j_3596_);
lean_dec(v_x_3592_);
lean_dec_ref(v_x_3591_);
return v_x_3588_;
}
else
{
lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3637_; 
lean_inc_ref(v_es_3593_);
v_isSharedCheck_3637_ = !lean_is_exclusive(v_x_3588_);
if (v_isSharedCheck_3637_ == 0)
{
lean_object* v_unused_3638_; 
v_unused_3638_ = lean_ctor_get(v_x_3588_, 0);
lean_dec(v_unused_3638_);
v___x_3600_ = v_x_3588_;
v_isShared_3601_ = v_isSharedCheck_3637_;
goto v_resetjp_3599_;
}
else
{
lean_dec(v_x_3588_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3637_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v_v_3602_; lean_object* v___x_3603_; lean_object* v_xs_x27_3604_; lean_object* v___y_3606_; 
v_v_3602_ = lean_array_fget(v_es_3593_, v_j_3596_);
v___x_3603_ = lean_box(0);
v_xs_x27_3604_ = lean_array_fset(v_es_3593_, v_j_3596_, v___x_3603_);
switch(lean_obj_tag(v_v_3602_))
{
case 0:
{
lean_object* v_key_3611_; lean_object* v_val_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3622_; 
v_key_3611_ = lean_ctor_get(v_v_3602_, 0);
v_val_3612_ = lean_ctor_get(v_v_3602_, 1);
v_isSharedCheck_3622_ = !lean_is_exclusive(v_v_3602_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3614_ = v_v_3602_;
v_isShared_3615_ = v_isSharedCheck_3622_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_val_3612_);
lean_inc(v_key_3611_);
lean_dec(v_v_3602_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3622_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
uint8_t v___x_3616_; 
v___x_3616_ = lean_string_dec_eq(v_x_3591_, v_key_3611_);
if (v___x_3616_ == 0)
{
lean_object* v___x_3617_; lean_object* v___x_3618_; 
lean_del_object(v___x_3614_);
v___x_3617_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3611_, v_val_3612_, v_x_3591_, v_x_3592_);
v___x_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3617_);
v___y_3606_ = v___x_3618_;
goto v___jp_3605_;
}
else
{
lean_object* v___x_3620_; 
lean_dec(v_val_3612_);
lean_dec(v_key_3611_);
if (v_isShared_3615_ == 0)
{
lean_ctor_set(v___x_3614_, 1, v_x_3592_);
lean_ctor_set(v___x_3614_, 0, v_x_3591_);
v___x_3620_ = v___x_3614_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_x_3591_);
lean_ctor_set(v_reuseFailAlloc_3621_, 1, v_x_3592_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
v___y_3606_ = v___x_3620_;
goto v___jp_3605_;
}
}
}
}
case 1:
{
lean_object* v_node_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3635_; 
v_node_3623_ = lean_ctor_get(v_v_3602_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v_v_3602_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3625_ = v_v_3602_;
v_isShared_3626_ = v_isSharedCheck_3635_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_node_3623_);
lean_dec(v_v_3602_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3635_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
size_t v___x_3627_; size_t v___x_3628_; size_t v___x_3629_; size_t v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3633_; 
v___x_3627_ = ((size_t)5ULL);
v___x_3628_ = lean_usize_shift_right(v_x_3589_, v___x_3627_);
v___x_3629_ = ((size_t)1ULL);
v___x_3630_ = lean_usize_add(v_x_3590_, v___x_3629_);
v___x_3631_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_node_3623_, v___x_3628_, v___x_3630_, v_x_3591_, v_x_3592_);
if (v_isShared_3626_ == 0)
{
lean_ctor_set(v___x_3625_, 0, v___x_3631_);
v___x_3633_ = v___x_3625_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v___x_3631_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
v___y_3606_ = v___x_3633_;
goto v___jp_3605_;
}
}
}
default: 
{
lean_object* v___x_3636_; 
v___x_3636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3636_, 0, v_x_3591_);
lean_ctor_set(v___x_3636_, 1, v_x_3592_);
v___y_3606_ = v___x_3636_;
goto v___jp_3605_;
}
}
v___jp_3605_:
{
lean_object* v___x_3607_; lean_object* v___x_3609_; 
v___x_3607_ = lean_array_fset(v_xs_x27_3604_, v_j_3596_, v___y_3606_);
lean_dec(v_j_3596_);
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 0, v___x_3607_);
v___x_3609_ = v___x_3600_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3607_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
}
}
else
{
lean_object* v_ks_3639_; lean_object* v_vs_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3658_; 
v_ks_3639_ = lean_ctor_get(v_x_3588_, 0);
v_vs_3640_ = lean_ctor_get(v_x_3588_, 1);
v_isSharedCheck_3658_ = !lean_is_exclusive(v_x_3588_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3642_ = v_x_3588_;
v_isShared_3643_ = v_isSharedCheck_3658_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_vs_3640_);
lean_inc(v_ks_3639_);
lean_dec(v_x_3588_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3658_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3645_; 
if (v_isShared_3643_ == 0)
{
v___x_3645_ = v___x_3642_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_ks_3639_);
lean_ctor_set(v_reuseFailAlloc_3657_, 1, v_vs_3640_);
v___x_3645_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
lean_object* v_newNode_3646_; size_t v___x_3647_; uint8_t v___x_3648_; 
v_newNode_3646_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v___x_3645_, v_x_3591_, v_x_3592_);
v___x_3647_ = ((size_t)7ULL);
v___x_3648_ = lean_usize_dec_le(v___x_3647_, v_x_3590_);
if (v___x_3648_ == 0)
{
lean_object* v___x_3649_; lean_object* v___x_3650_; uint8_t v___x_3651_; 
v___x_3649_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3646_);
v___x_3650_ = lean_unsigned_to_nat(4u);
v___x_3651_ = lean_nat_dec_lt(v___x_3649_, v___x_3650_);
lean_dec(v___x_3649_);
if (v___x_3651_ == 0)
{
lean_object* v_ks_3652_; lean_object* v_vs_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
v_ks_3652_ = lean_ctor_get(v_newNode_3646_, 0);
lean_inc_ref(v_ks_3652_);
v_vs_3653_ = lean_ctor_get(v_newNode_3646_, 1);
lean_inc_ref(v_vs_3653_);
lean_dec_ref(v_newNode_3646_);
v___x_3654_ = lean_unsigned_to_nat(0u);
v___x_3655_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0);
v___x_3656_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_x_3590_, v_ks_3652_, v_vs_3653_, v___x_3654_, v___x_3655_);
lean_dec_ref(v_vs_3653_);
lean_dec_ref(v_ks_3652_);
return v___x_3656_;
}
else
{
return v_newNode_3646_;
}
}
else
{
return v_newNode_3646_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(size_t v_depth_3659_, lean_object* v_keys_3660_, lean_object* v_vals_3661_, lean_object* v_i_3662_, lean_object* v_entries_3663_){
_start:
{
lean_object* v___x_3664_; uint8_t v___x_3665_; 
v___x_3664_ = lean_array_get_size(v_keys_3660_);
v___x_3665_ = lean_nat_dec_lt(v_i_3662_, v___x_3664_);
if (v___x_3665_ == 0)
{
lean_dec(v_i_3662_);
return v_entries_3663_;
}
else
{
lean_object* v_k_3666_; lean_object* v_v_3667_; uint64_t v___x_3668_; size_t v_h_3669_; size_t v___x_3670_; lean_object* v___x_3671_; size_t v___x_3672_; size_t v___x_3673_; size_t v___x_3674_; size_t v_h_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
v_k_3666_ = lean_array_fget_borrowed(v_keys_3660_, v_i_3662_);
v_v_3667_ = lean_array_fget_borrowed(v_vals_3661_, v_i_3662_);
v___x_3668_ = lean_string_hash(v_k_3666_);
v_h_3669_ = lean_uint64_to_usize(v___x_3668_);
v___x_3670_ = ((size_t)5ULL);
v___x_3671_ = lean_unsigned_to_nat(1u);
v___x_3672_ = ((size_t)1ULL);
v___x_3673_ = lean_usize_sub(v_depth_3659_, v___x_3672_);
v___x_3674_ = lean_usize_mul(v___x_3670_, v___x_3673_);
v_h_3675_ = lean_usize_shift_right(v_h_3669_, v___x_3674_);
v___x_3676_ = lean_nat_add(v_i_3662_, v___x_3671_);
lean_dec(v_i_3662_);
lean_inc(v_v_3667_);
lean_inc(v_k_3666_);
v___x_3677_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_entries_3663_, v_h_3675_, v_depth_3659_, v_k_3666_, v_v_3667_);
v_i_3662_ = v___x_3676_;
v_entries_3663_ = v___x_3677_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_depth_3679_, lean_object* v_keys_3680_, lean_object* v_vals_3681_, lean_object* v_i_3682_, lean_object* v_entries_3683_){
_start:
{
size_t v_depth_boxed_3684_; lean_object* v_res_3685_; 
v_depth_boxed_3684_ = lean_unbox_usize(v_depth_3679_);
lean_dec(v_depth_3679_);
v_res_3685_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_boxed_3684_, v_keys_3680_, v_vals_3681_, v_i_3682_, v_entries_3683_);
lean_dec_ref(v_vals_3681_);
lean_dec_ref(v_keys_3680_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(lean_object* v_x_3686_, lean_object* v_x_3687_, lean_object* v_x_3688_, lean_object* v_x_3689_, lean_object* v_x_3690_){
_start:
{
size_t v_x_2610__boxed_3691_; size_t v_x_2611__boxed_3692_; lean_object* v_res_3693_; 
v_x_2610__boxed_3691_ = lean_unbox_usize(v_x_3687_);
lean_dec(v_x_3687_);
v_x_2611__boxed_3692_ = lean_unbox_usize(v_x_3688_);
lean_dec(v_x_3688_);
v_res_3693_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_3686_, v_x_2610__boxed_3691_, v_x_2611__boxed_3692_, v_x_3689_, v_x_3690_);
return v_res_3693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(lean_object* v_x_3694_, lean_object* v_x_3695_, lean_object* v_x_3696_){
_start:
{
uint64_t v___x_3697_; size_t v___x_3698_; size_t v___x_3699_; lean_object* v___x_3700_; 
v___x_3697_ = lean_string_hash(v_x_3695_);
v___x_3698_ = lean_uint64_to_usize(v___x_3697_);
v___x_3699_ = ((size_t)1ULL);
v___x_3700_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_3694_, v___x_3698_, v___x_3699_, v_x_3695_, v_x_3696_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(lean_object* v_params_3702_){
_start:
{
lean_object* v___x_3703_; 
lean_inc(v_params_3702_);
v___x_3703_ = l_Lean_Lsp_instFromJsonSemanticTokensParams_fromJson(v_params_3702_);
if (lean_obj_tag(v___x_3703_) == 0)
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3719_; 
v_a_3704_ = lean_ctor_get(v___x_3703_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3703_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3706_ = v___x_3703_;
v_isShared_3707_ = v_isSharedCheck_3719_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3703_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3719_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
uint8_t v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3717_; 
v___x_3708_ = 3;
v___x_3709_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_3710_ = l_Lean_Json_compress(v_params_3702_);
v___x_3711_ = lean_string_append(v___x_3709_, v___x_3710_);
lean_dec_ref(v___x_3710_);
v___x_3712_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0));
v___x_3713_ = lean_string_append(v___x_3711_, v___x_3712_);
v___x_3714_ = lean_string_append(v___x_3713_, v_a_3704_);
lean_dec(v_a_3704_);
v___x_3715_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3715_, 0, v___x_3714_);
lean_ctor_set_uint8(v___x_3715_, sizeof(void*)*1, v___x_3708_);
if (v_isShared_3707_ == 0)
{
lean_ctor_set(v___x_3706_, 0, v___x_3715_);
v___x_3717_ = v___x_3706_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3715_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
else
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3727_; 
lean_dec(v_params_3702_);
v_a_3720_ = lean_ctor_get(v___x_3703_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3703_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3722_ = v___x_3703_;
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3703_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3720_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(lean_object* v_params_3728_){
_start:
{
lean_object* v___x_3730_; 
v___x_3730_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_params_3728_);
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3730_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3730_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
lean_ctor_set_tag(v___x_3733_, 1);
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
else
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
v_a_3739_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3741_ = v___x_3730_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3730_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
lean_ctor_set_tag(v___x_3741_, 0);
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3739_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg___boxed(lean_object* v_params_3747_, lean_object* v_a_3748_){
_start:
{
lean_object* v_res_3749_; 
v_res_3749_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_3747_);
return v_res_3749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(lean_object* v_method_3750_, lean_object* v_inst_3751_, lean_object* v_handler_3752_, lean_object* v_param_3753_, lean_object* v_state_3754_, lean_object* v___y_3755_){
_start:
{
lean_object* v___x_3757_; 
v___x_3757_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_param_3753_);
if (lean_obj_tag(v___x_3757_) == 0)
{
lean_object* v_a_3758_; lean_object* v___x_3759_; 
v_a_3758_ = lean_ctor_get(v___x_3757_, 0);
lean_inc(v_a_3758_);
lean_dec_ref_known(v___x_3757_, 1);
v___x_3759_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_3750_, v_state_3754_, lean_box(0), v_inst_3751_, v___y_3755_);
if (lean_obj_tag(v___x_3759_) == 0)
{
lean_object* v_a_3760_; lean_object* v___x_3761_; 
v_a_3760_ = lean_ctor_get(v___x_3759_, 0);
lean_inc(v_a_3760_);
lean_dec_ref_known(v___x_3759_, 1);
lean_inc_ref(v___y_3755_);
v___x_3761_ = lean_apply_4(v_handler_3752_, v_a_3758_, v_a_3760_, v___y_3755_, lean_box(0));
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_object* v_a_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3785_; 
v_a_3762_ = lean_ctor_get(v___x_3761_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3764_ = v___x_3761_;
v_isShared_3765_ = v_isSharedCheck_3785_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_a_3762_);
lean_dec(v___x_3761_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3785_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v_fst_3766_; lean_object* v_snd_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3784_; 
v_fst_3766_ = lean_ctor_get(v_a_3762_, 0);
v_snd_3767_ = lean_ctor_get(v_a_3762_, 1);
v_isSharedCheck_3784_ = !lean_is_exclusive(v_a_3762_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3769_ = v_a_3762_;
v_isShared_3770_ = v_isSharedCheck_3784_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_snd_3767_);
lean_inc(v_fst_3766_);
lean_dec(v_a_3762_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3784_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v_response_3771_; uint8_t v_isComplete_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3778_; 
v_response_3771_ = lean_ctor_get(v_fst_3766_, 0);
lean_inc(v_response_3771_);
v_isComplete_3772_ = lean_ctor_get_uint8(v_fst_3766_, sizeof(void*)*1);
lean_dec(v_fst_3766_);
v___x_3773_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_response_3771_);
lean_inc(v___x_3773_);
v___x_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3773_);
v___x_3775_ = l_Lean_Json_compress(v___x_3773_);
v___x_3776_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3776_, 0, v___x_3774_);
lean_ctor_set(v___x_3776_, 1, v___x_3775_);
lean_ctor_set_uint8(v___x_3776_, sizeof(void*)*2, v_isComplete_3772_);
if (v_isShared_3770_ == 0)
{
lean_ctor_set(v___x_3769_, 0, v_inst_3751_);
v___x_3778_ = v___x_3769_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_inst_3751_);
lean_ctor_set(v_reuseFailAlloc_3783_, 1, v_snd_3767_);
v___x_3778_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
lean_object* v___x_3779_; lean_object* v___x_3781_; 
v___x_3779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3776_);
lean_ctor_set(v___x_3779_, 1, v___x_3778_);
if (v_isShared_3765_ == 0)
{
lean_ctor_set(v___x_3764_, 0, v___x_3779_);
v___x_3781_ = v___x_3764_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v___x_3779_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
}
}
}
else
{
lean_object* v_a_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
lean_dec(v_inst_3751_);
v_a_3786_ = lean_ctor_get(v___x_3761_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3788_ = v___x_3761_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_a_3786_);
lean_dec(v___x_3761_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3786_);
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
else
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3801_; 
lean_dec(v_a_3758_);
lean_dec_ref(v_handler_3752_);
lean_dec(v_inst_3751_);
v_a_3794_ = lean_ctor_get(v___x_3759_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3759_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3796_ = v___x_3759_;
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3759_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3799_; 
if (v_isShared_3797_ == 0)
{
v___x_3799_ = v___x_3796_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_a_3794_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
else
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3809_; 
lean_dec_ref(v_handler_3752_);
lean_dec(v_inst_3751_);
v_a_3802_ = lean_ctor_get(v___x_3757_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3757_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3804_ = v___x_3757_;
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3757_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3807_; 
if (v_isShared_3805_ == 0)
{
v___x_3807_ = v___x_3804_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3802_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed(lean_object* v_method_3810_, lean_object* v_inst_3811_, lean_object* v_handler_3812_, lean_object* v_param_3813_, lean_object* v_state_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(v_method_3810_, v_inst_3811_, v_handler_3812_, v_param_3813_, v_state_3814_, v___y_3815_);
lean_dec_ref(v___y_3815_);
lean_dec(v_state_3814_);
lean_dec_ref(v_method_3810_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(lean_object* v_mutex_3818_, lean_object* v_a_x3f_3819_){
_start:
{
lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3821_ = lean_io_basemutex_unlock(v_mutex_3818_);
v___x_3822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3821_);
return v___x_3822_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0___boxed(lean_object* v_mutex_3823_, lean_object* v_a_x3f_3824_, lean_object* v___y_3825_){
_start:
{
lean_object* v_res_3826_; 
v_res_3826_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_3823_, v_a_x3f_3824_);
lean_dec(v_a_x3f_3824_);
lean_dec(v_mutex_3823_);
return v_res_3826_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(lean_object* v_mutex_3827_, lean_object* v_k_3828_, lean_object* v___y_3829_){
_start:
{
lean_object* v_ref_3831_; lean_object* v_mutex_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; 
v_ref_3831_ = lean_ctor_get(v_mutex_3827_, 0);
lean_inc(v_ref_3831_);
v_mutex_3832_ = lean_ctor_get(v_mutex_3827_, 1);
lean_inc(v_mutex_3832_);
lean_dec_ref(v_mutex_3827_);
v___x_3833_ = lean_io_basemutex_lock(v_mutex_3832_);
lean_inc_ref(v___y_3829_);
v___x_3834_ = lean_apply_3(v_k_3828_, v_ref_3831_, v___y_3829_, lean_box(0));
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v_a_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3851_; 
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3837_ = v___x_3834_;
v_isShared_3838_ = v_isSharedCheck_3851_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_a_3835_);
lean_dec(v___x_3834_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3851_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3840_; 
lean_inc(v_a_3835_);
if (v_isShared_3838_ == 0)
{
lean_ctor_set_tag(v___x_3837_, 1);
v___x_3840_ = v___x_3837_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3835_);
v___x_3840_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
lean_object* v___x_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3848_; 
v___x_3841_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_3832_, v___x_3840_);
lean_dec_ref(v___x_3840_);
lean_dec(v_mutex_3832_);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3841_);
if (v_isSharedCheck_3848_ == 0)
{
lean_object* v_unused_3849_; 
v_unused_3849_ = lean_ctor_get(v___x_3841_, 0);
lean_dec(v_unused_3849_);
v___x_3843_ = v___x_3841_;
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
else
{
lean_dec(v___x_3841_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
if (v_isShared_3844_ == 0)
{
lean_ctor_set(v___x_3843_, 0, v_a_3835_);
v___x_3846_ = v___x_3843_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_a_3835_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
}
}
else
{
lean_object* v_a_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3861_; 
v_a_3852_ = lean_ctor_get(v___x_3834_, 0);
lean_inc(v_a_3852_);
lean_dec_ref_known(v___x_3834_, 1);
v___x_3853_ = lean_box(0);
v___x_3854_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_3832_, v___x_3853_);
lean_dec(v_mutex_3832_);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3861_ == 0)
{
lean_object* v_unused_3862_; 
v_unused_3862_ = lean_ctor_get(v___x_3854_, 0);
lean_dec(v_unused_3862_);
v___x_3856_ = v___x_3854_;
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
else
{
lean_dec(v___x_3854_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___x_3859_; 
if (v_isShared_3857_ == 0)
{
lean_ctor_set_tag(v___x_3856_, 1);
lean_ctor_set(v___x_3856_, 0, v_a_3852_);
v___x_3859_ = v___x_3856_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_a_3852_);
v___x_3859_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
return v___x_3859_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_mutex_3863_, lean_object* v_k_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_){
_start:
{
lean_object* v_res_3867_; 
v_res_3867_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_3863_, v_k_3864_, v___y_3865_);
lean_dec_ref(v___y_3865_);
return v_res_3867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(lean_object* v_val_3868_, lean_object* v___f_3869_, lean_object* v_param_3870_, lean_object* v___x_3871_, lean_object* v_x_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3875_ = lean_st_ref_get(v_val_3868_);
lean_inc_ref(v___y_3873_);
v___x_3876_ = lean_apply_4(v___f_3869_, v_param_3870_, v___x_3875_, v___y_3873_, lean_box(0));
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3886_; 
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3879_ = v___x_3876_;
v_isShared_3880_ = v_isSharedCheck_3886_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3876_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3886_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v_snd_3881_; lean_object* v___x_3882_; lean_object* v___x_3884_; 
v_snd_3881_ = lean_ctor_get(v_a_3877_, 1);
lean_inc(v_snd_3881_);
lean_dec(v_a_3877_);
v___x_3882_ = lean_st_ref_swap(v_val_3868_, v_snd_3881_);
lean_dec(v___x_3882_);
if (v_isShared_3880_ == 0)
{
lean_ctor_set(v___x_3879_, 0, v___x_3871_);
v___x_3884_ = v___x_3879_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v___x_3871_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
else
{
lean_object* v_a_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3894_; 
v_a_3887_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3894_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3889_ = v___x_3876_;
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_a_3887_);
lean_dec(v___x_3876_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3892_; 
if (v_isShared_3890_ == 0)
{
v___x_3892_ = v___x_3889_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v_a_3887_);
v___x_3892_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
return v___x_3892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed(lean_object* v_val_3895_, lean_object* v___f_3896_, lean_object* v_param_3897_, lean_object* v___x_3898_, lean_object* v_x_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_){
_start:
{
lean_object* v_res_3902_; 
v_res_3902_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(v_val_3895_, v___f_3896_, v_param_3897_, v___x_3898_, v_x_3899_, v___y_3900_);
lean_dec_ref(v___y_3900_);
lean_dec(v_val_3895_);
return v_res_3902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(lean_object* v___f_3903_, lean_object* v___f_3904_, lean_object* v___x_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_){
_start:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3909_ = lean_st_ref_get(v___y_3906_);
v___x_3910_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_3909_, v___f_3903_, v___y_3907_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3920_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3913_ = v___x_3910_;
v_isShared_3914_ = v_isSharedCheck_3920_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v___x_3910_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3920_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3918_; 
v___x_3915_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_3904_, v_a_3911_);
v___x_3916_ = lean_st_ref_swap(v___y_3906_, v___x_3915_);
lean_dec(v___x_3916_);
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 0, v___x_3905_);
v___x_3918_ = v___x_3913_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3905_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
else
{
lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3928_; 
lean_dec_ref(v___f_3904_);
v_a_3921_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3923_ = v___x_3910_;
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v___x_3910_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3926_; 
if (v_isShared_3924_ == 0)
{
v___x_3926_ = v___x_3923_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_a_3921_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed(lean_object* v___f_3929_, lean_object* v___f_3930_, lean_object* v___x_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_){
_start:
{
lean_object* v_res_3935_; 
v_res_3935_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(v___f_3929_, v___f_3930_, v___x_3931_, v___y_3932_, v___y_3933_);
lean_dec_ref(v___y_3933_);
lean_dec(v___y_3932_);
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(lean_object* v_val_3936_, lean_object* v___f_3937_, lean_object* v___x_3938_, lean_object* v___f_3939_, lean_object* v_val_3940_, lean_object* v_param_3941_, lean_object* v___y_3942_){
_start:
{
lean_object* v___f_3944_; lean_object* v___f_3945_; lean_object* v___x_3946_; 
v___f_3944_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed), 7, 4);
lean_closure_set(v___f_3944_, 0, v_val_3936_);
lean_closure_set(v___f_3944_, 1, v___f_3937_);
lean_closure_set(v___f_3944_, 2, v_param_3941_);
lean_closure_set(v___f_3944_, 3, v___x_3938_);
v___f_3945_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed), 6, 3);
lean_closure_set(v___f_3945_, 0, v___f_3944_);
lean_closure_set(v___f_3945_, 1, v___f_3939_);
lean_closure_set(v___f_3945_, 2, v___x_3938_);
v___x_3946_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_3940_, v___f_3945_, v___y_3942_);
return v___x_3946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed(lean_object* v_val_3947_, lean_object* v___f_3948_, lean_object* v___x_3949_, lean_object* v___f_3950_, lean_object* v_val_3951_, lean_object* v_param_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(v_val_3947_, v___f_3948_, v___x_3949_, v___f_3950_, v_val_3951_, v_param_3952_, v___y_3953_);
lean_dec_ref(v___y_3953_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(lean_object* v___x_3956_, lean_object* v_x_3957_){
_start:
{
return v___x_3956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3___boxed(lean_object* v___x_3958_, lean_object* v_x_3959_){
_start:
{
lean_object* v_res_3960_; 
v_res_3960_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(v___x_3958_, v_x_3959_);
lean_dec_ref(v_x_3959_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__0(lean_object* v_j_3961_){
_start:
{
lean_object* v___x_3962_; 
v___x_3962_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_j_3961_);
if (lean_obj_tag(v___x_3962_) == 0)
{
lean_object* v_a_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3970_; 
v_a_3963_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3965_ = v___x_3962_;
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_a_3963_);
lean_dec(v___x_3962_);
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
v_reuseFailAlloc_3969_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3978_; 
v_a_3971_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3973_ = v___x_3962_;
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3962_);
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
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(lean_object* v_val_3979_, lean_object* v___f_3980_, lean_object* v_param_3981_, lean_object* v_x_3982_, lean_object* v___y_3983_){
_start:
{
lean_object* v___x_3985_; lean_object* v___x_3986_; 
v___x_3985_ = lean_st_ref_get(v_val_3979_);
lean_inc_ref(v___y_3983_);
v___x_3986_ = lean_apply_4(v___f_3980_, v_param_3981_, v___x_3985_, v___y_3983_, lean_box(0));
if (lean_obj_tag(v___x_3986_) == 0)
{
lean_object* v_a_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3997_; 
v_a_3987_ = lean_ctor_get(v___x_3986_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3986_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3989_ = v___x_3986_;
v_isShared_3990_ = v_isSharedCheck_3997_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_a_3987_);
lean_dec(v___x_3986_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3997_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v_fst_3991_; lean_object* v_snd_3992_; lean_object* v___x_3993_; lean_object* v___x_3995_; 
v_fst_3991_ = lean_ctor_get(v_a_3987_, 0);
lean_inc(v_fst_3991_);
v_snd_3992_ = lean_ctor_get(v_a_3987_, 1);
lean_inc(v_snd_3992_);
lean_dec(v_a_3987_);
v___x_3993_ = lean_st_ref_swap(v_val_3979_, v_snd_3992_);
lean_dec(v___x_3993_);
if (v_isShared_3990_ == 0)
{
lean_ctor_set(v___x_3989_, 0, v_fst_3991_);
v___x_3995_ = v___x_3989_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_fst_3991_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
else
{
lean_object* v_a_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4005_; 
v_a_3998_ = lean_ctor_get(v___x_3986_, 0);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3986_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_4000_ = v___x_3986_;
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_a_3998_);
lean_dec(v___x_3986_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4003_; 
if (v_isShared_4001_ == 0)
{
v___x_4003_ = v___x_4000_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_a_3998_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed(lean_object* v_val_4006_, lean_object* v___f_4007_, lean_object* v_param_4008_, lean_object* v_x_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_){
_start:
{
lean_object* v_res_4012_; 
v_res_4012_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(v_val_4006_, v___f_4007_, v_param_4008_, v_x_4009_, v___y_4010_);
lean_dec_ref(v___y_4010_);
lean_dec(v_val_4006_);
return v_res_4012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(lean_object* v___f_4013_, lean_object* v___f_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_){
_start:
{
lean_object* v___x_4018_; lean_object* v___x_4019_; 
v___x_4018_ = lean_st_ref_get(v___y_4015_);
v___x_4019_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4018_, v___f_4013_, v___y_4016_);
if (lean_obj_tag(v___x_4019_) == 0)
{
lean_object* v_a_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4029_; 
v_a_4020_ = lean_ctor_get(v___x_4019_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v___x_4019_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_4022_ = v___x_4019_;
v_isShared_4023_ = v_isSharedCheck_4029_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_a_4020_);
lean_dec(v___x_4019_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4029_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4027_; 
lean_inc(v_a_4020_);
v___x_4024_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4014_, v_a_4020_);
v___x_4025_ = lean_st_ref_swap(v___y_4015_, v___x_4024_);
lean_dec(v___x_4025_);
if (v_isShared_4023_ == 0)
{
v___x_4027_ = v___x_4022_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_a_4020_);
v___x_4027_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
return v___x_4027_;
}
}
}
else
{
lean_dec_ref(v___f_4014_);
return v___x_4019_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed(lean_object* v___f_4030_, lean_object* v___f_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_){
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(v___f_4030_, v___f_4031_, v___y_4032_, v___y_4033_);
lean_dec_ref(v___y_4033_);
lean_dec(v___y_4032_);
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(lean_object* v_val_4036_, lean_object* v___f_4037_, lean_object* v___f_4038_, lean_object* v_val_4039_, lean_object* v_param_4040_, lean_object* v___y_4041_){
_start:
{
lean_object* v___f_4043_; lean_object* v___f_4044_; lean_object* v___x_4045_; 
v___f_4043_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_4043_, 0, v_val_4036_);
lean_closure_set(v___f_4043_, 1, v___f_4037_);
lean_closure_set(v___f_4043_, 2, v_param_4040_);
v___f_4044_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed), 5, 2);
lean_closure_set(v___f_4044_, 0, v___f_4043_);
lean_closure_set(v___f_4044_, 1, v___f_4038_);
v___x_4045_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_4039_, v___f_4044_, v___y_4041_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed(lean_object* v_val_4046_, lean_object* v___f_4047_, lean_object* v___f_4048_, lean_object* v_val_4049_, lean_object* v_param_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
lean_object* v_res_4053_; 
v_res_4053_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(v_val_4046_, v___f_4047_, v___f_4048_, v_val_4049_, v_param_4050_, v___y_4051_);
lean_dec_ref(v___y_4051_);
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(lean_object* v_method_4054_, lean_object* v_inst_4055_, lean_object* v_onDidChange_4056_, lean_object* v_param_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_){
_start:
{
lean_object* v___x_4061_; 
v___x_4061_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_4054_, v___y_4058_, lean_box(0), v_inst_4055_, v___y_4059_);
if (lean_obj_tag(v___x_4061_) == 0)
{
lean_object* v_a_4062_; lean_object* v___x_4063_; 
v_a_4062_ = lean_ctor_get(v___x_4061_, 0);
lean_inc(v_a_4062_);
lean_dec_ref_known(v___x_4061_, 1);
lean_inc_ref(v___y_4059_);
v___x_4063_ = lean_apply_4(v_onDidChange_4056_, v_param_4057_, v_a_4062_, v___y_4059_, lean_box(0));
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4082_; 
v_a_4064_ = lean_ctor_get(v___x_4063_, 0);
v_isSharedCheck_4082_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4082_ == 0)
{
v___x_4066_ = v___x_4063_;
v_isShared_4067_ = v_isSharedCheck_4082_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4063_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4082_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v_snd_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4080_; 
v_snd_4068_ = lean_ctor_get(v_a_4064_, 1);
v_isSharedCheck_4080_ = !lean_is_exclusive(v_a_4064_);
if (v_isSharedCheck_4080_ == 0)
{
lean_object* v_unused_4081_; 
v_unused_4081_ = lean_ctor_get(v_a_4064_, 0);
lean_dec(v_unused_4081_);
v___x_4070_ = v_a_4064_;
v_isShared_4071_ = v_isSharedCheck_4080_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_snd_4068_);
lean_dec(v_a_4064_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4080_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v___x_4073_; 
if (v_isShared_4071_ == 0)
{
lean_ctor_set(v___x_4070_, 0, v_inst_4055_);
v___x_4073_ = v___x_4070_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_inst_4055_);
lean_ctor_set(v_reuseFailAlloc_4079_, 1, v_snd_4068_);
v___x_4073_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4077_; 
v___x_4074_ = lean_box(0);
v___x_4075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4075_, 0, v___x_4074_);
lean_ctor_set(v___x_4075_, 1, v___x_4073_);
if (v_isShared_4067_ == 0)
{
lean_ctor_set(v___x_4066_, 0, v___x_4075_);
v___x_4077_ = v___x_4066_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v___x_4075_);
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
else
{
lean_object* v_a_4083_; lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4090_; 
lean_dec(v_inst_4055_);
v_a_4083_ = lean_ctor_get(v___x_4063_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4090_ == 0)
{
v___x_4085_ = v___x_4063_;
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
else
{
lean_inc(v_a_4083_);
lean_dec(v___x_4063_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___x_4088_; 
if (v_isShared_4086_ == 0)
{
v___x_4088_ = v___x_4085_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_a_4083_);
v___x_4088_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
return v___x_4088_;
}
}
}
}
else
{
lean_object* v_a_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4098_; 
lean_dec_ref(v_param_4057_);
lean_dec_ref(v_onDidChange_4056_);
lean_dec(v_inst_4055_);
v_a_4091_ = lean_ctor_get(v___x_4061_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v___x_4061_);
if (v_isSharedCheck_4098_ == 0)
{
v___x_4093_ = v___x_4061_;
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_a_4091_);
lean_dec(v___x_4061_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
lean_object* v___x_4096_; 
if (v_isShared_4094_ == 0)
{
v___x_4096_ = v___x_4093_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_a_4091_);
v___x_4096_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
return v___x_4096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed(lean_object* v_method_4099_, lean_object* v_inst_4100_, lean_object* v_onDidChange_4101_, lean_object* v_param_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_){
_start:
{
lean_object* v_res_4106_; 
v_res_4106_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(v_method_4099_, v_inst_4100_, v_onDidChange_4101_, v_param_4102_, v___y_4103_, v___y_4104_);
lean_dec_ref(v___y_4104_);
lean_dec(v___y_4103_);
lean_dec_ref(v_method_4099_);
return v_res_4106_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_4114_; lean_object* v___x_4115_; 
v___x_4114_ = lean_box(0);
v___x_4115_ = lean_task_pure(v___x_4114_);
return v___x_4115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(lean_object* v_method_4116_, lean_object* v_completeness_4117_, lean_object* v_inst_4118_, lean_object* v_initState_4119_, lean_object* v_handler_4120_, lean_object* v_onDidChange_4121_){
_start:
{
lean_object* v___f_4123_; lean_object* v___f_4124_; lean_object* v___f_4125_; uint8_t v___x_4126_; 
v___f_4123_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0));
lean_inc_n(v_inst_4118_, 2);
lean_inc_ref_n(v_method_4116_, 2);
v___f_4124_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4124_, 0, v_method_4116_);
lean_closure_set(v___f_4124_, 1, v_inst_4118_);
lean_closure_set(v___f_4124_, 2, v_handler_4120_);
v___f_4125_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4125_, 0, v_method_4116_);
lean_closure_set(v___f_4125_, 1, v_inst_4118_);
lean_closure_set(v___f_4125_, 2, v_onDidChange_4121_);
v___x_4126_ = l_Lean_initializing();
if (v___x_4126_ == 0)
{
lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
lean_dec_ref(v___f_4125_);
lean_dec_ref(v___f_4124_);
lean_dec(v_initState_4119_);
lean_dec(v_inst_4118_);
lean_dec(v_completeness_4117_);
v___x_4127_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1));
v___x_4128_ = lean_string_append(v___x_4127_, v_method_4116_);
lean_dec_ref(v_method_4116_);
v___x_4129_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2));
v___x_4130_ = lean_string_append(v___x_4128_, v___x_4129_);
v___x_4131_ = lean_mk_io_user_error(v___x_4130_);
v___x_4132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4131_);
return v___x_4132_;
}
else
{
lean_object* v___x_4133_; lean_object* v___f_4134_; lean_object* v___f_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___f_4140_; lean_object* v___f_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4133_ = lean_box(0);
v___f_4134_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__3));
v___f_4135_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__4));
v___x_4136_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5);
v___x_4137_ = l_Std_Mutex_new___redArg(v___x_4136_);
v___x_4138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4138_, 0, v_inst_4118_);
lean_ctor_set(v___x_4138_, 1, v_initState_4119_);
lean_inc_ref(v___x_4138_);
v___x_4139_ = lean_st_mk_ref(v___x_4138_);
lean_inc_ref_n(v___x_4137_, 2);
lean_inc_ref(v___f_4124_);
lean_inc_n(v___x_4139_, 2);
v___f_4140_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_4140_, 0, v___x_4139_);
lean_closure_set(v___f_4140_, 1, v___f_4124_);
lean_closure_set(v___f_4140_, 2, v___f_4134_);
lean_closure_set(v___f_4140_, 3, v___x_4137_);
lean_inc_ref(v___f_4125_);
v___f_4141_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed), 8, 5);
lean_closure_set(v___f_4141_, 0, v___x_4139_);
lean_closure_set(v___f_4141_, 1, v___f_4125_);
lean_closure_set(v___f_4141_, 2, v___x_4133_);
lean_closure_set(v___f_4141_, 3, v___f_4135_);
lean_closure_set(v___f_4141_, 4, v___x_4137_);
v___x_4142_ = l_Lean_Server_statefulRequestHandlers;
v___x_4143_ = lean_st_ref_take(v___x_4142_);
v___x_4144_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4144_, 0, v___f_4123_);
lean_ctor_set(v___x_4144_, 1, v___f_4124_);
lean_ctor_set(v___x_4144_, 2, v___f_4140_);
lean_ctor_set(v___x_4144_, 3, v___f_4125_);
lean_ctor_set(v___x_4144_, 4, v___f_4141_);
lean_ctor_set(v___x_4144_, 5, v___x_4137_);
lean_ctor_set(v___x_4144_, 6, v___x_4138_);
lean_ctor_set(v___x_4144_, 7, v___x_4139_);
lean_ctor_set(v___x_4144_, 8, v_completeness_4117_);
v___x_4145_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_4143_, v_method_4116_, v___x_4144_);
v___x_4146_ = lean_st_ref_put(v___x_4142_, v___x_4145_);
v___x_4147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4147_, 0, v___x_4146_);
return v___x_4147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___boxed(lean_object* v_method_4148_, lean_object* v_completeness_4149_, lean_object* v_inst_4150_, lean_object* v_initState_4151_, lean_object* v_handler_4152_, lean_object* v_onDidChange_4153_, lean_object* v_a_4154_){
_start:
{
lean_object* v_res_4155_; 
v_res_4155_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4148_, v_completeness_4149_, v_inst_4150_, v_initState_4151_, v_handler_4152_, v_onDidChange_4153_);
return v_res_4155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(lean_object* v_method_4157_, lean_object* v_completeness_4158_, lean_object* v_inst_4159_, lean_object* v_initState_4160_, lean_object* v_handler_4161_, lean_object* v_onDidChange_4162_){
_start:
{
lean_object* v___x_4164_; lean_object* v___x_4165_; uint8_t v___x_4166_; 
v___x_4164_ = l_Lean_Server_requestHandlers;
v___x_4165_ = lean_st_ref_get(v___x_4164_);
v___x_4166_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_4165_, v_method_4157_);
lean_dec(v___x_4165_);
if (v___x_4166_ == 0)
{
lean_object* v___x_4167_; 
v___x_4167_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4157_, v_completeness_4158_, v_inst_4159_, v_initState_4160_, v_handler_4161_, v_onDidChange_4162_);
return v___x_4167_;
}
else
{
lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; 
lean_dec_ref(v_onDidChange_4162_);
lean_dec_ref(v_handler_4161_);
lean_dec(v_initState_4160_);
lean_dec(v_inst_4159_);
lean_dec(v_completeness_4158_);
v___x_4168_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1));
v___x_4169_ = lean_string_append(v___x_4168_, v_method_4157_);
lean_dec_ref(v_method_4157_);
v___x_4170_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_4171_ = lean_string_append(v___x_4169_, v___x_4170_);
v___x_4172_ = lean_mk_io_user_error(v___x_4171_);
v___x_4173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4173_, 0, v___x_4172_);
return v___x_4173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___boxed(lean_object* v_method_4174_, lean_object* v_completeness_4175_, lean_object* v_inst_4176_, lean_object* v_initState_4177_, lean_object* v_handler_4178_, lean_object* v_onDidChange_4179_, lean_object* v_a_4180_){
_start:
{
lean_object* v_res_4181_; 
v_res_4181_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4174_, v_completeness_4175_, v_inst_4176_, v_initState_4177_, v_handler_4178_, v_onDidChange_4179_);
return v_res_4181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(lean_object* v_method_4182_, lean_object* v_refreshMethod_4183_, lean_object* v_refreshIntervalMs_4184_, lean_object* v_inst_4185_, lean_object* v_initState_4186_, lean_object* v_handler_4187_, lean_object* v_onDidChange_4188_){
_start:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4190_, 0, v_refreshMethod_4183_);
lean_ctor_set(v___x_4190_, 1, v_refreshIntervalMs_4184_);
v___x_4191_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4182_, v___x_4190_, v_inst_4185_, v_initState_4186_, v_handler_4187_, v_onDidChange_4188_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_method_4192_, lean_object* v_refreshMethod_4193_, lean_object* v_refreshIntervalMs_4194_, lean_object* v_inst_4195_, lean_object* v_initState_4196_, lean_object* v_handler_4197_, lean_object* v_onDidChange_4198_, lean_object* v_a_4199_){
_start:
{
lean_object* v_res_4200_; 
v_res_4200_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_4192_, v_refreshMethod_4193_, v_refreshIntervalMs_4194_, v_inst_4195_, v_initState_4196_, v_handler_4197_, v_onDidChange_4198_);
return v_res_4200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_params_4201_){
_start:
{
lean_object* v___x_4202_; 
lean_inc(v_params_4201_);
v___x_4202_ = l_Lean_Lsp_instFromJsonSemanticTokensRangeParams_fromJson(v_params_4201_);
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_object* v_a_4203_; lean_object* v___x_4205_; uint8_t v_isShared_4206_; uint8_t v_isSharedCheck_4218_; 
v_a_4203_ = lean_ctor_get(v___x_4202_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4202_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4205_ = v___x_4202_;
v_isShared_4206_ = v_isSharedCheck_4218_;
goto v_resetjp_4204_;
}
else
{
lean_inc(v_a_4203_);
lean_dec(v___x_4202_);
v___x_4205_ = lean_box(0);
v_isShared_4206_ = v_isSharedCheck_4218_;
goto v_resetjp_4204_;
}
v_resetjp_4204_:
{
uint8_t v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4216_; 
v___x_4207_ = 3;
v___x_4208_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_4209_ = l_Lean_Json_compress(v_params_4201_);
v___x_4210_ = lean_string_append(v___x_4208_, v___x_4209_);
lean_dec_ref(v___x_4209_);
v___x_4211_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0));
v___x_4212_ = lean_string_append(v___x_4210_, v___x_4211_);
v___x_4213_ = lean_string_append(v___x_4212_, v_a_4203_);
lean_dec(v_a_4203_);
v___x_4214_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4214_, 0, v___x_4213_);
lean_ctor_set_uint8(v___x_4214_, sizeof(void*)*1, v___x_4207_);
if (v_isShared_4206_ == 0)
{
lean_ctor_set(v___x_4205_, 0, v___x_4214_);
v___x_4216_ = v___x_4205_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v___x_4214_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
}
else
{
lean_object* v_a_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4226_; 
lean_dec(v_params_4201_);
v_a_4219_ = lean_ctor_get(v___x_4202_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4202_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4221_ = v___x_4202_;
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_a_4219_);
lean_dec(v___x_4202_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___x_4224_; 
if (v_isShared_4222_ == 0)
{
v___x_4224_ = v___x_4221_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_a_4219_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__0(lean_object* v_j_4227_){
_start:
{
lean_object* v___x_4228_; 
v___x_4228_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_j_4227_);
if (lean_obj_tag(v___x_4228_) == 0)
{
lean_object* v_a_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4236_; 
v_a_4229_ = lean_ctor_get(v___x_4228_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4228_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4231_ = v___x_4228_;
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_a_4229_);
lean_dec(v___x_4228_);
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
v_reuseFailAlloc_4235_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4245_; 
v_a_4237_ = lean_ctor_get(v___x_4228_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4228_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4239_ = v___x_4228_;
v_isShared_4240_ = v_isSharedCheck_4245_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_dec(v___x_4228_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4245_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v_textDocument_4241_; lean_object* v___x_4243_; 
v_textDocument_4241_ = lean_ctor_get(v_a_4237_, 0);
lean_inc_ref(v_textDocument_4241_);
lean_dec(v_a_4237_);
if (v_isShared_4240_ == 0)
{
lean_ctor_set(v___x_4239_, 0, v_textDocument_4241_);
v___x_4243_ = v___x_4239_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_textDocument_4241_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(lean_object* v_serialize_x3f_4246_, uint8_t v_val_4247_, lean_object* v___y_4248_){
_start:
{
if (lean_obj_tag(v___y_4248_) == 0)
{
lean_object* v_a_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4256_; 
lean_dec(v_serialize_x3f_4246_);
v_a_4249_ = lean_ctor_get(v___y_4248_, 0);
v_isSharedCheck_4256_ = !lean_is_exclusive(v___y_4248_);
if (v_isSharedCheck_4256_ == 0)
{
v___x_4251_ = v___y_4248_;
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_a_4249_);
lean_dec(v___y_4248_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v___x_4254_; 
if (v_isShared_4252_ == 0)
{
v___x_4254_ = v___x_4251_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v_a_4249_);
v___x_4254_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
return v___x_4254_;
}
}
}
else
{
if (lean_obj_tag(v_serialize_x3f_4246_) == 1)
{
lean_object* v_a_4257_; lean_object* v___x_4259_; uint8_t v_isShared_4260_; uint8_t v_isSharedCheck_4268_; 
v_a_4257_ = lean_ctor_get(v___y_4248_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___y_4248_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4259_ = v___y_4248_;
v_isShared_4260_ = v_isSharedCheck_4268_;
goto v_resetjp_4258_;
}
else
{
lean_inc(v_a_4257_);
lean_dec(v___y_4248_);
v___x_4259_ = lean_box(0);
v_isShared_4260_ = v_isSharedCheck_4268_;
goto v_resetjp_4258_;
}
v_resetjp_4258_:
{
lean_object* v_val_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4266_; 
v_val_4261_ = lean_ctor_get(v_serialize_x3f_4246_, 0);
lean_inc(v_val_4261_);
lean_dec_ref_known(v_serialize_x3f_4246_, 1);
v___x_4262_ = lean_box(0);
v___x_4263_ = lean_apply_1(v_val_4261_, v_a_4257_);
v___x_4264_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4264_, 0, v___x_4262_);
lean_ctor_set(v___x_4264_, 1, v___x_4263_);
lean_ctor_set_uint8(v___x_4264_, sizeof(void*)*2, v_val_4247_);
if (v_isShared_4260_ == 0)
{
lean_ctor_set(v___x_4259_, 0, v___x_4264_);
v___x_4266_ = v___x_4259_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v___x_4264_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
return v___x_4266_;
}
}
}
else
{
lean_object* v_a_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4280_; 
lean_dec(v_serialize_x3f_4246_);
v_a_4269_ = lean_ctor_get(v___y_4248_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___y_4248_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4271_ = v___y_4248_;
v_isShared_4272_ = v_isSharedCheck_4280_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_a_4269_);
lean_dec(v___y_4248_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4280_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4278_; 
v___x_4273_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_a_4269_);
lean_inc(v___x_4273_);
v___x_4274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4274_, 0, v___x_4273_);
v___x_4275_ = l_Lean_Json_compress(v___x_4273_);
v___x_4276_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4276_, 0, v___x_4274_);
lean_ctor_set(v___x_4276_, 1, v___x_4275_);
lean_ctor_set_uint8(v___x_4276_, sizeof(void*)*2, v_val_4247_);
if (v_isShared_4272_ == 0)
{
lean_ctor_set(v___x_4271_, 0, v___x_4276_);
v___x_4278_ = v___x_4271_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v___x_4276_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object* v_serialize_x3f_4281_, lean_object* v_val_4282_, lean_object* v___y_4283_){
_start:
{
uint8_t v_val_3657__boxed_4284_; lean_object* v_res_4285_; 
v_val_3657__boxed_4284_ = lean_unbox(v_val_4282_);
v_res_4285_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(v_serialize_x3f_4281_, v_val_3657__boxed_4284_, v___y_4283_);
return v_res_4285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_params_4286_){
_start:
{
lean_object* v___x_4288_; 
v___x_4288_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_params_4286_);
if (lean_obj_tag(v___x_4288_) == 0)
{
lean_object* v_a_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4296_; 
v_a_4289_ = lean_ctor_get(v___x_4288_, 0);
v_isSharedCheck_4296_ = !lean_is_exclusive(v___x_4288_);
if (v_isSharedCheck_4296_ == 0)
{
v___x_4291_ = v___x_4288_;
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_a_4289_);
lean_dec(v___x_4288_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v___x_4294_; 
if (v_isShared_4292_ == 0)
{
lean_ctor_set_tag(v___x_4291_, 1);
v___x_4294_ = v___x_4291_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_a_4289_);
v___x_4294_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
return v___x_4294_;
}
}
}
else
{
lean_object* v_a_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4304_; 
v_a_4297_ = lean_ctor_get(v___x_4288_, 0);
v_isSharedCheck_4304_ = !lean_is_exclusive(v___x_4288_);
if (v_isSharedCheck_4304_ == 0)
{
v___x_4299_ = v___x_4288_;
v_isShared_4300_ = v_isSharedCheck_4304_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_a_4297_);
lean_dec(v___x_4288_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4304_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v___x_4302_; 
if (v_isShared_4300_ == 0)
{
lean_ctor_set_tag(v___x_4299_, 0);
v___x_4302_ = v___x_4299_;
goto v_reusejp_4301_;
}
else
{
lean_object* v_reuseFailAlloc_4303_; 
v_reuseFailAlloc_4303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4303_, 0, v_a_4297_);
v___x_4302_ = v_reuseFailAlloc_4303_;
goto v_reusejp_4301_;
}
v_reusejp_4301_:
{
return v___x_4302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_params_4305_, lean_object* v_a_4306_){
_start:
{
lean_object* v_res_4307_; 
v_res_4307_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_4305_);
return v_res_4307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(lean_object* v_handler_4308_, lean_object* v___f_4309_, lean_object* v_j_4310_, lean_object* v___y_4311_){
_start:
{
lean_object* v___x_4313_; 
v___x_4313_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_j_4310_);
if (lean_obj_tag(v___x_4313_) == 0)
{
lean_object* v_a_4314_; lean_object* v___x_4315_; 
v_a_4314_ = lean_ctor_get(v___x_4313_, 0);
lean_inc(v_a_4314_);
lean_dec_ref_known(v___x_4313_, 1);
lean_inc_ref(v___y_4311_);
v___x_4315_ = lean_apply_3(v_handler_4308_, v_a_4314_, v___y_4311_, lean_box(0));
if (lean_obj_tag(v___x_4315_) == 0)
{
lean_object* v_a_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4324_; 
v_a_4316_ = lean_ctor_get(v___x_4315_, 0);
v_isSharedCheck_4324_ = !lean_is_exclusive(v___x_4315_);
if (v_isSharedCheck_4324_ == 0)
{
v___x_4318_ = v___x_4315_;
v_isShared_4319_ = v_isSharedCheck_4324_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_a_4316_);
lean_dec(v___x_4315_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4324_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v___x_4320_; lean_object* v___x_4322_; 
v___x_4320_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4309_, v_a_4316_);
if (v_isShared_4319_ == 0)
{
lean_ctor_set(v___x_4318_, 0, v___x_4320_);
v___x_4322_ = v___x_4318_;
goto v_reusejp_4321_;
}
else
{
lean_object* v_reuseFailAlloc_4323_; 
v_reuseFailAlloc_4323_ = lean_alloc_ctor(0, 1, 0);
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
lean_object* v_a_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4332_; 
lean_dec_ref(v___f_4309_);
v_a_4325_ = lean_ctor_get(v___x_4315_, 0);
v_isSharedCheck_4332_ = !lean_is_exclusive(v___x_4315_);
if (v_isSharedCheck_4332_ == 0)
{
v___x_4327_ = v___x_4315_;
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_a_4325_);
lean_dec(v___x_4315_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4330_; 
if (v_isShared_4328_ == 0)
{
v___x_4330_ = v___x_4327_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v_a_4325_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
}
}
else
{
lean_object* v_a_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4340_; 
lean_dec_ref(v___f_4309_);
lean_dec_ref(v_handler_4308_);
v_a_4333_ = lean_ctor_get(v___x_4313_, 0);
v_isSharedCheck_4340_ = !lean_is_exclusive(v___x_4313_);
if (v_isSharedCheck_4340_ == 0)
{
v___x_4335_ = v___x_4313_;
v_isShared_4336_ = v_isSharedCheck_4340_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_a_4333_);
lean_dec(v___x_4313_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4340_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
lean_object* v___x_4338_; 
if (v_isShared_4336_ == 0)
{
v___x_4338_ = v___x_4335_;
goto v_reusejp_4337_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4339_, 0, v_a_4333_);
v___x_4338_ = v_reuseFailAlloc_4339_;
goto v_reusejp_4337_;
}
v_reusejp_4337_:
{
return v___x_4338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object* v_handler_4341_, lean_object* v___f_4342_, lean_object* v_j_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(v_handler_4341_, v___f_4342_, v_j_4343_, v___y_4344_);
lean_dec_ref(v___y_4344_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(lean_object* v_method_4349_, lean_object* v_handler_4350_, lean_object* v_serialize_x3f_4351_){
_start:
{
lean_object* v___f_4353_; uint8_t v___x_4354_; 
v___f_4353_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0));
v___x_4354_ = l_Lean_initializing();
if (v___x_4354_ == 0)
{
lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
lean_dec(v_serialize_x3f_4351_);
lean_dec_ref(v_handler_4350_);
v___x_4355_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1));
v___x_4356_ = lean_string_append(v___x_4355_, v_method_4349_);
lean_dec_ref(v_method_4349_);
v___x_4357_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2));
v___x_4358_ = lean_string_append(v___x_4356_, v___x_4357_);
v___x_4359_ = lean_mk_io_user_error(v___x_4358_);
v___x_4360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4360_, 0, v___x_4359_);
return v___x_4360_;
}
else
{
lean_object* v___x_4361_; lean_object* v___f_4362_; lean_object* v___f_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; uint8_t v___x_4366_; 
v___x_4361_ = lean_box(v___x_4354_);
v___f_4362_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed), 3, 2);
lean_closure_set(v___f_4362_, 0, v_serialize_x3f_4351_);
lean_closure_set(v___f_4362_, 1, v___x_4361_);
v___f_4363_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_4363_, 0, v_handler_4350_);
lean_closure_set(v___f_4363_, 1, v___f_4362_);
v___x_4364_ = l_Lean_Server_requestHandlers;
v___x_4365_ = lean_st_ref_get(v___x_4364_);
v___x_4366_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_4365_, v_method_4349_);
lean_dec(v___x_4365_);
if (v___x_4366_ == 0)
{
lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; 
v___x_4367_ = lean_st_ref_take(v___x_4364_);
v___x_4368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4368_, 0, v___f_4353_);
lean_ctor_set(v___x_4368_, 1, v___f_4363_);
v___x_4369_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_4367_, v_method_4349_, v___x_4368_);
v___x_4370_ = lean_st_ref_put(v___x_4364_, v___x_4369_);
v___x_4371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4371_, 0, v___x_4370_);
return v___x_4371_;
}
else
{
lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; 
lean_dec_ref(v___f_4363_);
v___x_4372_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1));
v___x_4373_ = lean_string_append(v___x_4372_, v_method_4349_);
lean_dec_ref(v_method_4349_);
v___x_4374_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_4375_ = lean_string_append(v___x_4373_, v___x_4374_);
v___x_4376_ = lean_mk_io_user_error(v___x_4375_);
v___x_4377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4377_, 0, v___x_4376_);
return v___x_4377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_4378_, lean_object* v_handler_4379_, lean_object* v_serialize_x3f_4380_, lean_object* v_a_4381_){
_start:
{
lean_object* v_res_4382_; 
v_res_4382_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v_method_4378_, v_handler_4379_, v_serialize_x3f_4380_);
return v_res_4382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; 
v___x_4390_ = ((lean_object*)(l_Lean_Server_FileWorker_instImpl_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7_));
v___x_4391_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4392_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4393_ = lean_box(0);
v___x_4394_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v___x_4391_, v___x_4392_, v___x_4393_);
if (lean_obj_tag(v___x_4394_) == 0)
{
lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; 
lean_dec_ref_known(v___x_4394_, 1);
v___x_4395_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4396_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4397_ = lean_unsigned_to_nat(2000u);
v___x_4398_ = lean_box(0);
v___x_4399_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__4_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4400_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__5_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4401_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v___x_4395_, v___x_4396_, v___x_4397_, v___x_4390_, v___x_4398_, v___x_4399_, v___x_4400_);
return v___x_4401_;
}
else
{
return v___x_4394_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2____boxed(lean_object* v_a_4402_){
_start:
{
lean_object* v_res_4403_; 
v_res_4403_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_();
return v_res_4403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(lean_object* v_method_4404_, lean_object* v_refreshMethod_4405_, lean_object* v_refreshIntervalMs_4406_, lean_object* v_stateType_4407_, lean_object* v_inst_4408_, lean_object* v_initState_4409_, lean_object* v_handler_4410_, lean_object* v_onDidChange_4411_){
_start:
{
lean_object* v___x_4413_; 
v___x_4413_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_4404_, v_refreshMethod_4405_, v_refreshIntervalMs_4406_, v_inst_4408_, v_initState_4409_, v_handler_4410_, v_onDidChange_4411_);
return v___x_4413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___boxed(lean_object* v_method_4414_, lean_object* v_refreshMethod_4415_, lean_object* v_refreshIntervalMs_4416_, lean_object* v_stateType_4417_, lean_object* v_inst_4418_, lean_object* v_initState_4419_, lean_object* v_handler_4420_, lean_object* v_onDidChange_4421_, lean_object* v_a_4422_){
_start:
{
lean_object* v_res_4423_; 
v_res_4423_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(v_method_4414_, v_refreshMethod_4415_, v_refreshIntervalMs_4416_, v_stateType_4417_, v_inst_4418_, v_initState_4419_, v_handler_4420_, v_onDidChange_4421_);
return v_res_4423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_params_4424_, lean_object* v_a_4425_){
_start:
{
lean_object* v___x_4427_; 
v___x_4427_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_4424_);
return v___x_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_params_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_){
_start:
{
lean_object* v_res_4431_; 
v_res_4431_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(v_params_4428_, v_a_4429_);
lean_dec_ref(v_a_4429_);
return v_res_4431_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_4432_, lean_object* v_x_4433_, lean_object* v_x_4434_){
_start:
{
uint8_t v___x_4435_; 
v___x_4435_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_4433_, v_x_4434_);
return v___x_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object* v_00_u03b2_4436_, lean_object* v_x_4437_, lean_object* v_x_4438_){
_start:
{
uint8_t v_res_4439_; lean_object* v_r_4440_; 
v_res_4439_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(v_00_u03b2_4436_, v_x_4437_, v_x_4438_);
lean_dec_ref(v_x_4438_);
lean_dec_ref(v_x_4437_);
v_r_4440_ = lean_box(v_res_4439_);
return v_r_4440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3(lean_object* v_00_u03b2_4441_, lean_object* v_x_4442_, lean_object* v_x_4443_, lean_object* v_x_4444_){
_start:
{
lean_object* v___x_4445_; 
v___x_4445_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v_x_4442_, v_x_4443_, v_x_4444_);
return v___x_4445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(lean_object* v_method_4446_, lean_object* v_completeness_4447_, lean_object* v_stateType_4448_, lean_object* v_inst_4449_, lean_object* v_initState_4450_, lean_object* v_handler_4451_, lean_object* v_onDidChange_4452_){
_start:
{
lean_object* v___x_4454_; 
v___x_4454_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4446_, v_completeness_4447_, v_inst_4449_, v_initState_4450_, v_handler_4451_, v_onDidChange_4452_);
return v___x_4454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object* v_method_4455_, lean_object* v_completeness_4456_, lean_object* v_stateType_4457_, lean_object* v_inst_4458_, lean_object* v_initState_4459_, lean_object* v_handler_4460_, lean_object* v_onDidChange_4461_, lean_object* v_a_4462_){
_start:
{
lean_object* v_res_4463_; 
v_res_4463_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(v_method_4455_, v_completeness_4456_, v_stateType_4457_, v_inst_4458_, v_initState_4459_, v_handler_4460_, v_onDidChange_4461_);
return v_res_4463_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(lean_object* v_00_u03b2_4464_, lean_object* v_x_4465_, size_t v_x_4466_, lean_object* v_x_4467_){
_start:
{
uint8_t v___x_4468_; 
v___x_4468_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_4465_, v_x_4466_, v_x_4467_);
return v___x_4468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4469_, lean_object* v_x_4470_, lean_object* v_x_4471_, lean_object* v_x_4472_){
_start:
{
size_t v_x_3976__boxed_4473_; uint8_t v_res_4474_; lean_object* v_r_4475_; 
v_x_3976__boxed_4473_ = lean_unbox_usize(v_x_4471_);
lean_dec(v_x_4471_);
v_res_4474_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(v_00_u03b2_4469_, v_x_4470_, v_x_3976__boxed_4473_, v_x_4472_);
lean_dec_ref(v_x_4472_);
lean_dec_ref(v_x_4470_);
v_r_4475_ = lean_box(v_res_4474_);
return v_r_4475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_object* v_00_u03b2_4476_, lean_object* v_x_4477_, size_t v_x_4478_, size_t v_x_4479_, lean_object* v_x_4480_, lean_object* v_x_4481_){
_start:
{
lean_object* v___x_4482_; 
v___x_4482_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_4477_, v_x_4478_, v_x_4479_, v_x_4480_, v_x_4481_);
return v___x_4482_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4483_, lean_object* v_x_4484_, lean_object* v_x_4485_, lean_object* v_x_4486_, lean_object* v_x_4487_, lean_object* v_x_4488_){
_start:
{
size_t v_x_3987__boxed_4489_; size_t v_x_3988__boxed_4490_; lean_object* v_res_4491_; 
v_x_3987__boxed_4489_ = lean_unbox_usize(v_x_4485_);
lean_dec(v_x_4485_);
v_x_3988__boxed_4490_ = lean_unbox_usize(v_x_4486_);
lean_dec(v_x_4486_);
v_res_4491_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(v_00_u03b2_4483_, v_x_4484_, v_x_3987__boxed_4489_, v_x_3988__boxed_4490_, v_x_4487_, v_x_4488_);
return v_res_4491_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(lean_object* v_00_u03b1_4492_, lean_object* v_00_u03b2_4493_, lean_object* v_mutex_4494_, lean_object* v_k_4495_, lean_object* v___y_4496_){
_start:
{
lean_object* v___x_4498_; 
v___x_4498_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_4494_, v_k_4495_, v___y_4496_);
return v___x_4498_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b1_4499_, lean_object* v_00_u03b2_4500_, lean_object* v_mutex_4501_, lean_object* v_k_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_){
_start:
{
lean_object* v_res_4505_; 
v_res_4505_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(v_00_u03b1_4499_, v_00_u03b2_4500_, v_mutex_4501_, v_k_4502_, v___y_4503_);
lean_dec_ref(v___y_4503_);
return v_res_4505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(lean_object* v_method_4506_, lean_object* v_completeness_4507_, lean_object* v_stateType_4508_, lean_object* v_inst_4509_, lean_object* v_initState_4510_, lean_object* v_handler_4511_, lean_object* v_onDidChange_4512_){
_start:
{
lean_object* v___x_4514_; 
v___x_4514_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4506_, v_completeness_4507_, v_inst_4509_, v_initState_4510_, v_handler_4511_, v_onDidChange_4512_);
return v___x_4514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___boxed(lean_object* v_method_4515_, lean_object* v_completeness_4516_, lean_object* v_stateType_4517_, lean_object* v_inst_4518_, lean_object* v_initState_4519_, lean_object* v_handler_4520_, lean_object* v_onDidChange_4521_, lean_object* v_a_4522_){
_start:
{
lean_object* v_res_4523_; 
v_res_4523_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(v_method_4515_, v_completeness_4516_, v_stateType_4517_, v_inst_4518_, v_initState_4519_, v_handler_4520_, v_onDidChange_4521_);
return v_res_4523_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_4524_, lean_object* v_keys_4525_, lean_object* v_vals_4526_, lean_object* v_heq_4527_, lean_object* v_i_4528_, lean_object* v_k_4529_){
_start:
{
uint8_t v___x_4530_; 
v___x_4530_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_4525_, v_i_4528_, v_k_4529_);
return v___x_4530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4531_, lean_object* v_keys_4532_, lean_object* v_vals_4533_, lean_object* v_heq_4534_, lean_object* v_i_4535_, lean_object* v_k_4536_){
_start:
{
uint8_t v_res_4537_; lean_object* v_r_4538_; 
v_res_4537_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(v_00_u03b2_4531_, v_keys_4532_, v_vals_4533_, v_heq_4534_, v_i_4535_, v_k_4536_);
lean_dec_ref(v_k_4536_);
lean_dec_ref(v_vals_4533_);
lean_dec_ref(v_keys_4532_);
v_r_4538_ = lean_box(v_res_4537_);
return v_r_4538_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_4539_, lean_object* v_n_4540_, lean_object* v_k_4541_, lean_object* v_v_4542_){
_start:
{
lean_object* v___x_4543_; 
v___x_4543_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_n_4540_, v_k_4541_, v_v_4542_);
return v___x_4543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_4544_, size_t v_depth_4545_, lean_object* v_keys_4546_, lean_object* v_vals_4547_, lean_object* v_heq_4548_, lean_object* v_i_4549_, lean_object* v_entries_4550_){
_start:
{
lean_object* v___x_4551_; 
v___x_4551_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_4545_, v_keys_4546_, v_vals_4547_, v_i_4549_, v_entries_4550_);
return v___x_4551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_4552_, lean_object* v_depth_4553_, lean_object* v_keys_4554_, lean_object* v_vals_4555_, lean_object* v_heq_4556_, lean_object* v_i_4557_, lean_object* v_entries_4558_){
_start:
{
size_t v_depth_boxed_4559_; lean_object* v_res_4560_; 
v_depth_boxed_4559_ = lean_unbox_usize(v_depth_4553_);
lean_dec(v_depth_4553_);
v_res_4560_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(v_00_u03b2_4552_, v_depth_boxed_4559_, v_keys_4554_, v_vals_4555_, v_heq_4556_, v_i_4557_, v_entries_4558_);
lean_dec_ref(v_vals_4555_);
lean_dec_ref(v_keys_4554_);
return v_res_4560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(lean_object* v_params_4561_, lean_object* v_a_4562_){
_start:
{
lean_object* v___x_4564_; 
v___x_4564_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_4561_);
return v___x_4564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___boxed(lean_object* v_params_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_){
_start:
{
lean_object* v_res_4568_; 
v_res_4568_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(v_params_4565_, v_a_4566_);
lean_dec_ref(v_a_4566_);
return v_res_4568_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_4569_, lean_object* v_x_4570_, lean_object* v_x_4571_, lean_object* v_x_4572_, lean_object* v_x_4573_){
_start:
{
lean_object* v___x_4574_; 
v___x_4574_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_x_4570_, v_x_4571_, v_x_4572_, v_x_4573_);
return v___x_4574_;
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
