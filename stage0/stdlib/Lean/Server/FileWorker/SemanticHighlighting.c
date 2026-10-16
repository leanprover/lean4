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
uint8_t l_Lean_Lsp_instOrdPosition_ord(lean_object*, lean_object*);
uint8_t l_Lean_Lsp_instBEqPosition_beq(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
v___x_113_ = lean_nat_add(v___y_110_, v___y_112_);
lean_dec(v___y_112_);
lean_dec(v___y_110_);
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
lean_ctor_set(v___x_93_, 3, v___y_111_);
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
lean_ctor_set(v_reuseFailAlloc_118_, 3, v___y_111_);
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
v___y_110_ = v___x_126_;
v___y_111_ = v___x_125_;
v___y_112_ = v_size_127_;
goto v___jp_109_;
}
else
{
lean_object* v___x_128_; 
v___x_128_ = lean_unsigned_to_nat(0u);
v___y_110_ = v___x_126_;
v___y_111_ = v___x_125_;
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
lean_object* v_a_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v_a_520_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_520_);
lean_dec_ref_known(v___x_509_, 1);
v___x_521_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__13));
lean_inc(v_json_507_);
v___x_522_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__0(v_json_507_, v___x_521_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_532_; 
lean_dec(v_a_520_);
lean_dec(v_json_507_);
v_a_523_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_532_ == 0)
{
v___x_525_ = v___x_522_;
v_isShared_526_ = v_isSharedCheck_532_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_522_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_532_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_527_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__17, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__17_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__17);
v___x_528_ = lean_string_append(v___x_527_, v_a_523_);
lean_dec(v_a_523_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_528_);
v___x_530_ = v___x_525_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
else
{
lean_object* v_a_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v_a_533_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_533_);
lean_dec_ref_known(v___x_522_, 1);
v___x_534_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds___closed__5));
lean_inc(v_json_507_);
v___x_535_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__1(v_json_507_, v___x_534_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_545_; 
lean_dec(v_a_533_);
lean_dec(v_a_520_);
lean_dec(v_json_507_);
v_a_536_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_545_ == 0)
{
v___x_538_ = v___x_535_;
v_isShared_539_ = v_isSharedCheck_545_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_535_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_545_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_540_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__21, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__21_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__21);
v___x_541_ = lean_string_append(v___x_540_, v_a_536_);
lean_dec(v_a_536_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 0, v___x_541_);
v___x_543_ = v___x_538_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
else
{
lean_object* v_a_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v_a_546_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_a_546_);
lean_dec_ref_known(v___x_535_, 1);
v___x_547_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__22));
v___x_548_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__2(v_json_507_, v___x_547_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_558_; 
lean_dec(v_a_546_);
lean_dec(v_a_533_);
lean_dec(v_a_520_);
v_a_549_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_558_ == 0)
{
v___x_551_ = v___x_548_;
v_isShared_552_ = v_isSharedCheck_558_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_548_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_558_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_553_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__26, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__26_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__26);
v___x_554_ = lean_string_append(v___x_553_, v_a_549_);
lean_dec(v_a_549_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_554_);
v___x_556_ = v___x_551_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
else
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_568_; 
v_a_559_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_568_ == 0)
{
v___x_561_ = v___x_548_;
v_isShared_562_ = v_isSharedCheck_568_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_548_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_568_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; uint8_t v___x_564_; lean_object* v___x_566_; 
v___x_563_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_563_, 0, v_a_520_);
lean_ctor_set(v___x_563_, 1, v_a_533_);
lean_ctor_set(v___x_563_, 2, v_a_559_);
v___x_564_ = lean_unbox(v_a_546_);
lean_dec(v_a_546_);
lean_ctor_set_uint8(v___x_563_, sizeof(void*)*3, v___x_564_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_563_);
v___x_566_ = v___x_561_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_563_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson_spec__0(lean_object* v_a_571_, lean_object* v_a_572_){
_start:
{
if (lean_obj_tag(v_a_571_) == 0)
{
lean_object* v___x_573_; 
v___x_573_ = lean_array_to_list(v_a_572_);
return v___x_573_;
}
else
{
lean_object* v_head_574_; lean_object* v_tail_575_; lean_object* v___x_576_; 
v_head_574_ = lean_ctor_get(v_a_571_, 0);
lean_inc(v_head_574_);
v_tail_575_ = lean_ctor_get(v_a_571_, 1);
lean_inc(v_tail_575_);
lean_dec_ref_known(v_a_571_, 2);
v___x_576_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_572_, v_head_574_);
v_a_571_ = v_tail_575_;
v_a_572_ = v___x_576_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson(lean_object* v_x_580_){
_start:
{
lean_object* v_pos_581_; lean_object* v_tailPos_582_; uint8_t v_type_583_; lean_object* v_priority_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_pos_581_ = lean_ctor_get(v_x_580_, 0);
lean_inc_ref(v_pos_581_);
v_tailPos_582_ = lean_ctor_get(v_x_580_, 1);
lean_inc_ref(v_tailPos_582_);
v_type_583_ = lean_ctor_get_uint8(v_x_580_, sizeof(void*)*3);
v_priority_584_ = lean_ctor_get(v_x_580_, 2);
lean_inc(v_priority_584_);
lean_dec_ref(v_x_580_);
v___x_585_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__0));
v___x_586_ = l_Lean_Lsp_instToJsonPosition_toJson(v_pos_581_);
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_585_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = lean_box(0);
v___x_589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_587_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
v___x_590_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__13));
v___x_591_ = l_Lean_Lsp_instToJsonPosition_toJson(v_tailPos_582_);
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_590_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set(v___x_593_, 1, v___x_588_);
v___x_594_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds___closed__5));
v___x_595_ = l_Lean_Lsp_instToJsonSemanticTokenType_toJson(v_type_583_);
v___x_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_594_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
lean_ctor_set(v___x_597_, 1, v___x_588_);
v___x_598_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__22));
v___x_599_ = l_Lean_JsonNumber_fromNat(v_priority_584_);
v___x_600_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_598_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v___x_588_);
v___x_603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
lean_ctor_set(v___x_603_, 1, v___x_588_);
v___x_604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_597_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_593_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_589_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = ((lean_object*)(l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson___closed__0));
v___x_608_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson_spec__0(v___x_606_, v___x_607_);
v___x_609_ = l_Lean_Json_mkObj(v___x_608_);
lean_dec(v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(lean_object* v_text_612_, lean_object* v_beginPos_613_, lean_object* v_endPos_x3f_614_, lean_object* v_as_615_, size_t v_i_616_, size_t v_stop_617_, lean_object* v_b_618_){
_start:
{
lean_object* v___y_620_; uint8_t v___x_624_; 
v___x_624_ = lean_usize_dec_eq(v_i_616_, v_stop_617_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v_stx_626_; uint8_t v_type_627_; lean_object* v_priority_628_; lean_object* v___x_629_; 
v___x_625_ = lean_array_uget_borrowed(v_as_615_, v_i_616_);
v_stx_626_ = lean_ctor_get(v___x_625_, 0);
v_type_627_ = lean_ctor_get_uint8(v___x_625_, sizeof(void*)*2);
v_priority_628_ = lean_ctor_get(v___x_625_, 1);
v___x_629_ = l_Lean_Syntax_getPos_x3f(v_stx_626_, v___x_624_);
if (lean_obj_tag(v___x_629_) == 0)
{
v___y_620_ = v_b_618_;
goto v___jp_619_;
}
else
{
lean_object* v_val_630_; lean_object* v___x_631_; 
v_val_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_val_630_);
lean_dec_ref_known(v___x_629_, 1);
v___x_631_ = l_Lean_Syntax_getTailPos_x3f(v_stx_626_, v___x_624_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_dec(v_val_630_);
v___y_620_ = v_b_618_;
goto v___jp_619_;
}
else
{
lean_object* v_val_632_; uint8_t v___x_641_; 
v_val_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_val_632_);
lean_dec_ref_known(v___x_631_, 1);
v___x_641_ = lean_nat_dec_le(v_beginPos_613_, v_val_630_);
if (v___x_641_ == 0)
{
lean_dec(v_val_632_);
lean_dec(v_val_630_);
v___y_620_ = v_b_618_;
goto v___jp_619_;
}
else
{
if (lean_obj_tag(v_endPos_x3f_614_) == 0)
{
goto v___jp_633_;
}
else
{
lean_object* v_val_642_; lean_object* v___x_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v_val_642_ = lean_ctor_get(v_endPos_x3f_614_, 0);
v___x_643_ = lean_unsigned_to_nat(1u);
v___x_644_ = lean_nat_add(v_val_630_, v___x_643_);
v___x_645_ = lean_nat_dec_le(v___x_644_, v_val_642_);
lean_dec(v___x_644_);
if (v___x_645_ == 0)
{
lean_dec(v_val_632_);
lean_dec(v_val_630_);
v___y_620_ = v_b_618_;
goto v___jp_619_;
}
else
{
goto v___jp_633_;
}
}
}
v___jp_633_:
{
lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_634_ = lean_unsigned_to_nat(1u);
v___x_635_ = lean_nat_add(v_val_630_, v___x_634_);
v___x_636_ = lean_nat_dec_le(v___x_635_, v_val_632_);
lean_dec(v___x_635_);
if (v___x_636_ == 0)
{
lean_dec(v_val_632_);
lean_dec(v_val_630_);
v___y_620_ = v_b_618_;
goto v___jp_619_;
}
else
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
lean_inc_ref_n(v_text_612_, 2);
v___x_637_ = l_Lean_FileMap_utf8PosToLspPos(v_text_612_, v_val_630_);
lean_dec(v_val_630_);
v___x_638_ = l_Lean_FileMap_utf8PosToLspPos(v_text_612_, v_val_632_);
lean_dec(v_val_632_);
lean_inc(v_priority_628_);
v___x_639_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_639_, 0, v___x_637_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
lean_ctor_set(v___x_639_, 2, v_priority_628_);
lean_ctor_set_uint8(v___x_639_, sizeof(void*)*3, v_type_627_);
v___x_640_ = lean_array_push(v_b_618_, v___x_639_);
v___y_620_ = v___x_640_;
goto v___jp_619_;
}
}
}
}
}
else
{
lean_dec_ref(v_text_612_);
return v_b_618_;
}
v___jp_619_:
{
size_t v___x_621_; size_t v___x_622_; 
v___x_621_ = ((size_t)1ULL);
v___x_622_ = lean_usize_add(v_i_616_, v___x_621_);
v_i_616_ = v___x_622_;
v_b_618_ = v___y_620_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0___boxed(lean_object* v_text_646_, lean_object* v_beginPos_647_, lean_object* v_endPos_x3f_648_, lean_object* v_as_649_, lean_object* v_i_650_, lean_object* v_stop_651_, lean_object* v_b_652_){
_start:
{
size_t v_i_boxed_653_; size_t v_stop_boxed_654_; lean_object* v_res_655_; 
v_i_boxed_653_ = lean_unbox_usize(v_i_650_);
lean_dec(v_i_650_);
v_stop_boxed_654_ = lean_unbox_usize(v_stop_651_);
lean_dec(v_stop_651_);
v_res_655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(v_text_646_, v_beginPos_647_, v_endPos_x3f_648_, v_as_649_, v_i_boxed_653_, v_stop_boxed_654_, v_b_652_);
lean_dec_ref(v_as_649_);
lean_dec(v_endPos_x3f_648_);
lean_dec(v_beginPos_647_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0(lean_object* v_text_658_, lean_object* v_beginPos_659_, lean_object* v_endPos_x3f_660_, lean_object* v_as_661_, lean_object* v_start_662_, lean_object* v_stop_663_){
_start:
{
lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_664_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0___closed__0));
v___x_665_ = lean_nat_dec_lt(v_start_662_, v_stop_663_);
if (v___x_665_ == 0)
{
lean_dec_ref(v_text_658_);
return v___x_664_;
}
else
{
lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_666_ = lean_array_get_size(v_as_661_);
v___x_667_ = lean_nat_dec_le(v_stop_663_, v___x_666_);
if (v___x_667_ == 0)
{
uint8_t v___x_668_; 
v___x_668_ = lean_nat_dec_lt(v_start_662_, v___x_666_);
if (v___x_668_ == 0)
{
lean_dec_ref(v_text_658_);
return v___x_664_;
}
else
{
size_t v___x_669_; size_t v___x_670_; lean_object* v___x_671_; 
v___x_669_ = lean_usize_of_nat(v_start_662_);
v___x_670_ = lean_usize_of_nat(v___x_666_);
v___x_671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(v_text_658_, v_beginPos_659_, v_endPos_x3f_660_, v_as_661_, v___x_669_, v___x_670_, v___x_664_);
return v___x_671_;
}
}
else
{
size_t v___x_672_; size_t v___x_673_; lean_object* v___x_674_; 
v___x_672_ = lean_usize_of_nat(v_start_662_);
v___x_673_ = lean_usize_of_nat(v_stop_663_);
v___x_674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(v_text_658_, v_beginPos_659_, v_endPos_x3f_660_, v_as_661_, v___x_672_, v___x_673_, v___x_664_);
return v___x_674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0___boxed(lean_object* v_text_675_, lean_object* v_beginPos_676_, lean_object* v_endPos_x3f_677_, lean_object* v_as_678_, lean_object* v_start_679_, lean_object* v_stop_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0(v_text_675_, v_beginPos_676_, v_endPos_x3f_677_, v_as_678_, v_start_679_, v_stop_680_);
lean_dec(v_stop_680_);
lean_dec(v_start_679_);
lean_dec_ref(v_as_678_);
lean_dec(v_endPos_x3f_677_);
lean_dec(v_beginPos_676_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(lean_object* v_text_682_, lean_object* v_beginPos_683_, lean_object* v_endPos_x3f_684_, lean_object* v_tokens_685_){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_686_ = lean_unsigned_to_nat(0u);
v___x_687_ = lean_array_get_size(v_tokens_685_);
v___x_688_ = l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0(v_text_682_, v_beginPos_683_, v_endPos_x3f_684_, v_tokens_685_, v___x_686_, v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens___boxed(lean_object* v_text_689_, lean_object* v_beginPos_690_, lean_object* v_endPos_x3f_691_, lean_object* v_tokens_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(v_text_689_, v_beginPos_690_, v_endPos_x3f_691_, v_tokens_692_);
lean_dec_ref(v_tokens_692_);
lean_dec(v_endPos_x3f_691_);
lean_dec(v_beginPos_690_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding_go(lean_object* v_s_702_, lean_object* v_x_703_){
_start:
{
if (lean_obj_tag(v_x_703_) == 0)
{
lean_object* v___x_704_; 
v___x_704_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_704_, 0, v_s_702_);
lean_ctor_set(v___x_704_, 1, v_x_703_);
return v___x_704_;
}
else
{
lean_object* v_head_705_; lean_object* v_tail_706_; lean_object* v_tailPos_707_; lean_object* v_tailPos_708_; uint8_t v___x_709_; 
v_head_705_ = lean_ctor_get(v_x_703_, 0);
v_tail_706_ = lean_ctor_get(v_x_703_, 1);
v_tailPos_707_ = lean_ctor_get(v_s_702_, 1);
v_tailPos_708_ = lean_ctor_get(v_head_705_, 1);
v___x_709_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_707_, v_tailPos_708_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; 
v___x_710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_710_, 0, v_s_702_);
lean_ctor_set(v___x_710_, 1, v_x_703_);
return v___x_710_;
}
else
{
lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_718_; 
lean_inc(v_tail_706_);
lean_inc(v_head_705_);
v_isSharedCheck_718_ = !lean_is_exclusive(v_x_703_);
if (v_isSharedCheck_718_ == 0)
{
lean_object* v_unused_719_; lean_object* v_unused_720_; 
v_unused_719_ = lean_ctor_get(v_x_703_, 1);
lean_dec(v_unused_719_);
v_unused_720_ = lean_ctor_get(v_x_703_, 0);
lean_dec(v_unused_720_);
v___x_712_ = v_x_703_;
v_isShared_713_ = v_isSharedCheck_718_;
goto v_resetjp_711_;
}
else
{
lean_dec(v_x_703_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_718_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_714_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding_go(v_s_702_, v_tail_706_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 1, v___x_714_);
v___x_716_ = v___x_712_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_head_705_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(lean_object* v_st_721_, lean_object* v_s_722_){
_start:
{
lean_object* v_nonOverlapping_723_; lean_object* v_current_x3f_724_; lean_object* v_surrounding_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_733_; 
v_nonOverlapping_723_ = lean_ctor_get(v_st_721_, 0);
v_current_x3f_724_ = lean_ctor_get(v_st_721_, 1);
v_surrounding_725_ = lean_ctor_get(v_st_721_, 2);
v_isSharedCheck_733_ = !lean_is_exclusive(v_st_721_);
if (v_isSharedCheck_733_ == 0)
{
v___x_727_ = v_st_721_;
v_isShared_728_ = v_isSharedCheck_733_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_surrounding_725_);
lean_inc(v_current_x3f_724_);
lean_inc(v_nonOverlapping_723_);
lean_dec(v_st_721_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_733_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_729_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding_go(v_s_722_, v_surrounding_725_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 2, v___x_729_);
v___x_731_ = v___x_727_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_nonOverlapping_723_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_current_x3f_724_);
lean_ctor_set(v_reuseFailAlloc_732_, 2, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better(lean_object* v_t_734_, lean_object* v_soFar_735_){
_start:
{
lean_object* v_tailPos_736_; lean_object* v_priority_737_; lean_object* v_tailPos_738_; lean_object* v_priority_739_; uint8_t v___x_740_; 
v_tailPos_736_ = lean_ctor_get(v_soFar_735_, 1);
v_priority_737_ = lean_ctor_get(v_soFar_735_, 2);
v_tailPos_738_ = lean_ctor_get(v_t_734_, 1);
v_priority_739_ = lean_ctor_get(v_t_734_, 2);
v___x_740_ = lean_nat_dec_lt(v_priority_737_, v_priority_739_);
if (v___x_740_ == 0)
{
uint8_t v___x_741_; 
v___x_741_ = lean_nat_dec_eq(v_priority_739_, v_priority_737_);
if (v___x_741_ == 0)
{
return v___x_741_;
}
else
{
uint8_t v___x_742_; 
v___x_742_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_738_, v_tailPos_736_);
if (v___x_742_ == 0)
{
return v___x_741_;
}
else
{
return v___x_740_;
}
}
}
else
{
return v___x_740_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better___boxed(lean_object* v_t_743_, lean_object* v_soFar_744_){
_start:
{
uint8_t v_res_745_; lean_object* v_r_746_; 
v_res_745_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better(v_t_743_, v_soFar_744_);
lean_dec_ref(v_soFar_744_);
lean_dec_ref(v_t_743_);
v_r_746_ = lean_box(v_res_745_);
return v_r_746_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0(lean_object* v_x_747_, lean_object* v_x_748_){
_start:
{
if (lean_obj_tag(v_x_748_) == 0)
{
return v_x_747_;
}
else
{
if (lean_obj_tag(v_x_747_) == 0)
{
lean_object* v_head_749_; lean_object* v_tail_750_; lean_object* v___x_751_; 
v_head_749_ = lean_ctor_get(v_x_748_, 0);
v_tail_750_ = lean_ctor_get(v_x_748_, 1);
lean_inc(v_head_749_);
v___x_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_751_, 0, v_head_749_);
v_x_747_ = v___x_751_;
v_x_748_ = v_tail_750_;
goto _start;
}
else
{
lean_object* v_head_753_; lean_object* v_tail_754_; lean_object* v_val_755_; uint8_t v___x_756_; 
v_head_753_ = lean_ctor_get(v_x_748_, 0);
v_tail_754_ = lean_ctor_get(v_x_748_, 1);
v_val_755_ = lean_ctor_get(v_x_747_, 0);
v___x_756_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better(v_head_753_, v_val_755_);
if (v___x_756_ == 0)
{
v_x_748_ = v_tail_754_;
goto _start;
}
else
{
lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_765_; 
v_isSharedCheck_765_ = !lean_is_exclusive(v_x_747_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; 
v_unused_766_ = lean_ctor_get(v_x_747_, 0);
lean_dec(v_unused_766_);
v___x_759_ = v_x_747_;
v_isShared_760_ = v_isSharedCheck_765_;
goto v_resetjp_758_;
}
else
{
lean_dec(v_x_747_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_765_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
lean_inc(v_head_753_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v_head_753_);
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_head_753_);
v___x_762_ = v_reuseFailAlloc_764_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
v_x_747_ = v___x_762_;
v_x_748_ = v_tail_754_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0___boxed(lean_object* v_x_767_, lean_object* v_x_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0(v_x_767_, v_x_768_);
lean_dec(v_x_768_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(lean_object* v_toks_770_){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = lean_box(0);
v___x_772_ = l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0(v___x_771_, v_toks_770_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest___boxed(lean_object* v_toks_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(v_toks_773_);
lean_dec(v_toks_773_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(lean_object* v_val_775_, lean_object* v_x_776_){
_start:
{
if (lean_obj_tag(v_x_776_) == 0)
{
return v_x_776_;
}
else
{
lean_object* v_head_777_; lean_object* v_tail_778_; lean_object* v_tailPos_779_; lean_object* v_tailPos_780_; uint8_t v___x_781_; 
v_head_777_ = lean_ctor_get(v_x_776_, 0);
v_tail_778_ = lean_ctor_get(v_x_776_, 1);
v_tailPos_779_ = lean_ctor_get(v_head_777_, 1);
v_tailPos_780_ = lean_ctor_get(v_val_775_, 1);
v___x_781_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_779_, v_tailPos_780_);
if (v___x_781_ == 2)
{
lean_inc_ref(v_x_776_);
return v_x_776_;
}
else
{
v_x_776_ = v_tail_778_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0___boxed(lean_object* v_val_783_, lean_object* v_x_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(v_val_783_, v_x_784_);
lean_dec(v_x_784_);
lean_dec_ref(v_val_783_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(lean_object* v_nextToken_x3f_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_current_x3f_788_; 
v_current_x3f_788_ = lean_ctor_get(v_a_787_, 1);
if (lean_obj_tag(v_current_x3f_788_) == 1)
{
lean_object* v_nonOverlapping_789_; lean_object* v_surrounding_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_831_; 
lean_inc_ref(v_current_x3f_788_);
v_nonOverlapping_789_ = lean_ctor_get(v_a_787_, 0);
v_surrounding_790_ = lean_ctor_get(v_a_787_, 2);
v_isSharedCheck_831_ = !lean_is_exclusive(v_a_787_);
if (v_isSharedCheck_831_ == 0)
{
lean_object* v_unused_832_; 
v_unused_832_ = lean_ctor_get(v_a_787_, 1);
lean_dec(v_unused_832_);
v___x_792_ = v_a_787_;
v_isShared_793_ = v_isSharedCheck_831_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_surrounding_790_);
lean_inc(v_nonOverlapping_789_);
lean_dec(v_a_787_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_831_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v_val_794_; lean_object* v___x_795_; lean_object* v___y_797_; lean_object* v___y_798_; 
v_val_794_ = lean_ctor_get(v_current_x3f_788_, 0);
v___x_795_ = l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(v_val_794_, v_surrounding_790_);
lean_dec(v_surrounding_790_);
if (lean_obj_tag(v_nextToken_x3f_786_) == 1)
{
lean_object* v_val_826_; lean_object* v_tailPos_827_; lean_object* v_pos_828_; uint8_t v___x_829_; 
v_val_826_ = lean_ctor_get(v_nextToken_x3f_786_, 0);
v_tailPos_827_ = lean_ctor_get(v_val_794_, 1);
v_pos_828_ = lean_ctor_get(v_val_826_, 0);
v___x_829_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_827_, v_pos_828_);
if (v___x_829_ == 2)
{
lean_object* v___x_830_; 
lean_del_object(v___x_792_);
v___x_830_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_830_, 0, v_nonOverlapping_789_);
lean_ctor_set(v___x_830_, 1, v_current_x3f_788_);
lean_ctor_set(v___x_830_, 2, v___x_795_);
return v___x_830_;
}
else
{
lean_inc(v_val_794_);
lean_dec_ref_known(v_current_x3f_788_, 1);
goto v___jp_803_;
}
}
else
{
lean_inc(v_val_794_);
lean_dec_ref_known(v_current_x3f_788_, 1);
goto v___jp_803_;
}
v___jp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 2, v___x_795_);
lean_ctor_set(v___x_792_, 1, v___y_798_);
lean_ctor_set(v___x_792_, 0, v___y_797_);
v___x_800_ = v___x_792_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___y_797_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v___y_798_);
lean_ctor_set(v_reuseFailAlloc_802_, 2, v___x_795_);
v___x_800_ = v_reuseFailAlloc_802_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
v_a_787_ = v___x_800_;
goto _start;
}
}
v___jp_803_:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
lean_inc(v_val_794_);
v___x_804_ = lean_array_push(v_nonOverlapping_789_, v_val_794_);
v___x_805_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(v___x_795_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_dec(v_val_794_);
v___y_797_ = v___x_804_;
v___y_798_ = v___x_805_;
goto v___jp_796_;
}
else
{
lean_object* v_val_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_825_; 
v_val_806_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_825_ == 0)
{
v___x_808_ = v___x_805_;
v_isShared_809_ = v_isSharedCheck_825_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_val_806_);
lean_dec(v___x_805_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_825_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v_tailPos_810_; lean_object* v_tailPos_811_; uint8_t v_type_812_; lean_object* v_priority_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_823_; 
v_tailPos_810_ = lean_ctor_get(v_val_794_, 1);
lean_inc_ref(v_tailPos_810_);
lean_dec(v_val_794_);
v_tailPos_811_ = lean_ctor_get(v_val_806_, 1);
v_type_812_ = lean_ctor_get_uint8(v_val_806_, sizeof(void*)*3);
v_priority_813_ = lean_ctor_get(v_val_806_, 2);
v_isSharedCheck_823_ = !lean_is_exclusive(v_val_806_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; 
v_unused_824_ = lean_ctor_get(v_val_806_, 0);
lean_dec(v_unused_824_);
v___x_815_ = v_val_806_;
v_isShared_816_ = v_isSharedCheck_823_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_priority_813_);
lean_inc(v_tailPos_811_);
lean_dec(v_val_806_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_823_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v_tailPos_810_);
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_tailPos_810_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_tailPos_811_);
lean_ctor_set(v_reuseFailAlloc_822_, 2, v_priority_813_);
lean_ctor_set_uint8(v_reuseFailAlloc_822_, sizeof(void*)*3, v_type_812_);
v___x_818_ = v_reuseFailAlloc_822_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_820_; 
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_818_);
v___x_820_ = v___x_808_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
v___y_797_ = v___x_804_;
v___y_798_ = v___x_820_;
goto v___jp_796_;
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
lean_object* v_nonOverlapping_833_; lean_object* v_surrounding_834_; lean_object* v___x_835_; 
v_nonOverlapping_833_ = lean_ctor_get(v_a_787_, 0);
v_surrounding_834_ = lean_ctor_get(v_a_787_, 2);
v___x_835_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(v_surrounding_834_);
if (lean_obj_tag(v___x_835_) == 1)
{
lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_843_; 
lean_inc(v_surrounding_834_);
lean_inc_ref(v_nonOverlapping_833_);
v_isSharedCheck_843_ = !lean_is_exclusive(v_a_787_);
if (v_isSharedCheck_843_ == 0)
{
lean_object* v_unused_844_; lean_object* v_unused_845_; lean_object* v_unused_846_; 
v_unused_844_ = lean_ctor_get(v_a_787_, 2);
lean_dec(v_unused_844_);
v_unused_845_ = lean_ctor_get(v_a_787_, 1);
lean_dec(v_unused_845_);
v_unused_846_ = lean_ctor_get(v_a_787_, 0);
lean_dec(v_unused_846_);
v___x_837_ = v_a_787_;
v_isShared_838_ = v_isSharedCheck_843_;
goto v_resetjp_836_;
}
else
{
lean_dec(v_a_787_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_843_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 1, v___x_835_);
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_nonOverlapping_833_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v___x_835_);
lean_ctor_set(v_reuseFailAlloc_842_, 2, v_surrounding_834_);
v___x_840_ = v_reuseFailAlloc_842_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
v_a_787_ = v___x_840_;
goto _start;
}
}
}
else
{
lean_dec(v___x_835_);
return v_a_787_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg___boxed(lean_object* v_nextToken_x3f_847_, lean_object* v_a_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v_nextToken_x3f_847_, v_a_848_);
lean_dec(v_nextToken_x3f_847_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken(lean_object* v_st_850_, lean_object* v_nextToken_x3f_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v_nextToken_x3f_851_, v_st_850_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken___boxed(lean_object* v_st_853_, lean_object* v_nextToken_x3f_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken(v_st_853_, v_nextToken_x3f_854_);
lean_dec(v_nextToken_x3f_854_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1(lean_object* v_nextToken_x3f_856_, lean_object* v_inst_857_, lean_object* v_a_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v_nextToken_x3f_856_, v_a_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___boxed(lean_object* v_nextToken_x3f_860_, lean_object* v_inst_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1(v_nextToken_x3f_860_, v_inst_861_, v_a_862_);
lean_dec(v_nextToken_x3f_860_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_token(lean_object* v_st_864_, lean_object* v_t_865_){
_start:
{
lean_object* v___x_866_; lean_object* v_st_867_; lean_object* v_current_x3f_868_; 
lean_inc_ref(v_t_865_);
v___x_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_866_, 0, v_t_865_);
v_st_867_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v___x_866_, v_st_864_);
v_current_x3f_868_ = lean_ctor_get(v_st_867_, 1);
if (lean_obj_tag(v_current_x3f_868_) == 1)
{
lean_object* v_val_869_; lean_object* v_nonOverlapping_870_; lean_object* v_surrounding_871_; lean_object* v_pos_872_; lean_object* v_tailPos_873_; lean_object* v_priority_874_; lean_object* v_pos_875_; lean_object* v_tailPos_876_; uint8_t v_type_877_; lean_object* v_priority_878_; lean_object* v___y_880_; uint8_t v___x_888_; 
v_val_869_ = lean_ctor_get(v_current_x3f_868_, 0);
v_nonOverlapping_870_ = lean_ctor_get(v_st_867_, 0);
v_surrounding_871_ = lean_ctor_get(v_st_867_, 2);
v_pos_872_ = lean_ctor_get(v_t_865_, 0);
v_tailPos_873_ = lean_ctor_get(v_t_865_, 1);
v_priority_874_ = lean_ctor_get(v_t_865_, 2);
v_pos_875_ = lean_ctor_get(v_val_869_, 0);
v_tailPos_876_ = lean_ctor_get(v_val_869_, 1);
v_type_877_ = lean_ctor_get_uint8(v_val_869_, sizeof(void*)*3);
v_priority_878_ = lean_ctor_get(v_val_869_, 2);
v___x_888_ = lean_nat_dec_lt(v_priority_874_, v_priority_878_);
if (v___x_888_ == 0)
{
uint8_t v___x_889_; 
v___x_889_ = lean_nat_dec_eq(v_priority_878_, v_priority_874_);
if (v___x_889_ == 0)
{
lean_inc_ref(v_tailPos_873_);
lean_inc_ref(v_pos_872_);
lean_inc(v_surrounding_871_);
lean_inc_ref(v_nonOverlapping_870_);
lean_inc(v_val_869_);
lean_dec_ref(v_st_867_);
lean_dec_ref(v_t_865_);
goto v___jp_884_;
}
else
{
uint8_t v___x_890_; 
v___x_890_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_875_, v_pos_872_);
if (v___x_890_ == 0)
{
lean_inc_ref(v_tailPos_873_);
lean_inc_ref(v_pos_872_);
lean_inc(v_surrounding_871_);
lean_inc_ref(v_nonOverlapping_870_);
lean_inc(v_val_869_);
lean_dec_ref(v_st_867_);
lean_dec_ref(v_t_865_);
goto v___jp_884_;
}
else
{
uint8_t v___x_891_; 
v___x_891_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_876_, v_tailPos_873_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; 
lean_dec_ref_known(v___x_866_, 1);
v___x_892_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_867_, v_t_865_);
return v___x_892_;
}
else
{
lean_inc_ref(v_tailPos_873_);
lean_inc_ref(v_pos_872_);
lean_inc(v_surrounding_871_);
lean_inc_ref(v_nonOverlapping_870_);
lean_inc(v_val_869_);
lean_dec_ref(v_st_867_);
lean_dec_ref(v_t_865_);
goto v___jp_884_;
}
}
}
}
else
{
lean_object* v___x_893_; 
lean_dec_ref_known(v___x_866_, 1);
v___x_893_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_867_, v_t_865_);
return v___x_893_;
}
v___jp_879_:
{
lean_object* v_st_881_; uint8_t v___x_882_; 
v_st_881_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_st_881_, 0, v___y_880_);
lean_ctor_set(v_st_881_, 1, v___x_866_);
lean_ctor_set(v_st_881_, 2, v_surrounding_871_);
v___x_882_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_873_, v_tailPos_876_);
lean_dec_ref(v_tailPos_873_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; 
v___x_883_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_881_, v_val_869_);
return v___x_883_;
}
else
{
lean_dec(v_val_869_);
return v_st_881_;
}
}
v___jp_884_:
{
uint8_t v___x_885_; 
v___x_885_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_875_, v_pos_872_);
if (v___x_885_ == 0)
{
lean_object* v_curr_886_; lean_object* v___x_887_; 
lean_inc(v_priority_878_);
lean_inc_ref(v_pos_875_);
v_curr_886_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_curr_886_, 0, v_pos_875_);
lean_ctor_set(v_curr_886_, 1, v_pos_872_);
lean_ctor_set(v_curr_886_, 2, v_priority_878_);
lean_ctor_set_uint8(v_curr_886_, sizeof(void*)*3, v_type_877_);
v___x_887_ = lean_array_push(v_nonOverlapping_870_, v_curr_886_);
v___y_880_ = v___x_887_;
goto v___jp_879_;
}
else
{
lean_dec_ref(v_pos_872_);
v___y_880_ = v_nonOverlapping_870_;
goto v___jp_879_;
}
}
}
else
{
lean_object* v_nonOverlapping_894_; lean_object* v_surrounding_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec_ref(v_t_865_);
v_nonOverlapping_894_ = lean_ctor_get(v_st_867_, 0);
v_surrounding_895_ = lean_ctor_get(v_st_867_, 2);
v_isSharedCheck_902_ = !lean_is_exclusive(v_st_867_);
if (v_isSharedCheck_902_ == 0)
{
lean_object* v_unused_903_; 
v_unused_903_ = lean_ctor_get(v_st_867_, 1);
lean_dec(v_unused_903_);
v___x_897_ = v_st_867_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_surrounding_895_);
lean_inc(v_nonOverlapping_894_);
lean_dec(v_st_867_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 1, v___x_866_);
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_nonOverlapping_894_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_901_, 2, v_surrounding_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0(lean_object* v_x_904_, lean_object* v_x_905_){
_start:
{
lean_object* v_pos_906_; lean_object* v_tailPos_907_; lean_object* v_pos_908_; lean_object* v_tailPos_909_; uint8_t v___x_910_; 
v_pos_906_ = lean_ctor_get(v_x_904_, 0);
v_tailPos_907_ = lean_ctor_get(v_x_904_, 1);
v_pos_908_ = lean_ctor_get(v_x_905_, 0);
v_tailPos_909_ = lean_ctor_get(v_x_905_, 1);
v___x_910_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_906_, v_pos_908_);
if (v___x_910_ == 0)
{
uint8_t v___x_911_; 
v___x_911_ = 1;
return v___x_911_;
}
else
{
uint8_t v___x_912_; 
v___x_912_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_906_, v_pos_908_);
if (v___x_912_ == 0)
{
return v___x_912_;
}
else
{
uint8_t v___x_913_; 
v___x_913_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_907_, v_tailPos_909_);
if (v___x_913_ == 2)
{
uint8_t v___x_914_; 
v___x_914_ = 0;
return v___x_914_;
}
else
{
return v___x_912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0___boxed(lean_object* v_x_915_, lean_object* v_x_916_){
_start:
{
uint8_t v_res_917_; lean_object* v_r_918_; 
v_res_917_ = l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0(v_x_915_, v_x_916_);
lean_dec_ref(v_x_916_);
lean_dec_ref(v_x_915_);
v_r_918_ = lean_box(v_res_917_);
return v_r_918_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(lean_object* v_as_x27_919_, lean_object* v_b_920_){
_start:
{
if (lean_obj_tag(v_as_x27_919_) == 0)
{
return v_b_920_;
}
else
{
lean_object* v_head_921_; lean_object* v_tail_922_; lean_object* v___x_923_; 
v_head_921_ = lean_ctor_get(v_as_x27_919_, 0);
v_tail_922_ = lean_ctor_get(v_as_x27_919_, 1);
lean_inc(v_head_921_);
v___x_923_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_token(v_b_920_, v_head_921_);
v_as_x27_919_ = v_tail_922_;
v_b_920_ = v___x_923_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg___boxed(lean_object* v_as_x27_925_, lean_object* v_b_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(v_as_x27_925_, v_b_926_);
lean_dec(v_as_x27_925_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleOverlappingSemanticTokens(lean_object* v_tokens_929_){
_start:
{
lean_object* v___f_930_; lean_object* v_count_931_; lean_object* v___x_932_; lean_object* v_tokens_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v_st_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v_nonOverlapping_944_; 
v___f_930_ = ((lean_object*)(l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___closed__0));
v_count_931_ = lean_array_get_size(v_tokens_929_);
v___x_932_ = lean_array_to_list(v_tokens_929_);
v_tokens_933_ = l_List_mergeSort___redArg(v___x_932_, v___f_930_);
v___x_934_ = lean_unsigned_to_nat(11u);
v___x_935_ = lean_nat_mul(v_count_931_, v___x_934_);
v___x_936_ = lean_unsigned_to_nat(10u);
v___x_937_ = lean_nat_div(v___x_935_, v___x_936_);
lean_dec(v___x_935_);
v___x_938_ = lean_mk_empty_array_with_capacity(v___x_937_);
lean_dec(v___x_937_);
v___x_939_ = lean_box(0);
v___x_940_ = lean_box(0);
v_st_941_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_st_941_, 0, v___x_938_);
lean_ctor_set(v_st_941_, 1, v___x_939_);
lean_ctor_set(v_st_941_, 2, v___x_940_);
v___x_942_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(v_tokens_933_, v_st_941_);
lean_dec(v_tokens_933_);
v___x_943_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v___x_939_, v___x_942_);
v_nonOverlapping_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc_ref(v_nonOverlapping_944_);
lean_dec_ref(v___x_943_);
return v_nonOverlapping_944_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0(lean_object* v_as_945_, lean_object* v_as_x27_946_, lean_object* v_b_947_, lean_object* v_a_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(v_as_x27_946_, v_b_947_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___boxed(lean_object* v_as_950_, lean_object* v_as_x27_951_, lean_object* v_b_952_, lean_object* v_a_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0(v_as_950_, v_as_x27_951_, v_b_952_, v_a_953_);
lean_dec(v_as_x27_951_);
lean_dec(v_as_950_);
return v_res_954_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(uint8_t v___x_955_, lean_object* v_x_956_, lean_object* v_x_957_){
_start:
{
lean_object* v_pos_958_; lean_object* v_tailPos_959_; lean_object* v_pos_960_; lean_object* v_tailPos_961_; uint8_t v___x_962_; 
v_pos_958_ = lean_ctor_get(v_x_956_, 0);
v_tailPos_959_ = lean_ctor_get(v_x_956_, 1);
v_pos_960_ = lean_ctor_get(v_x_957_, 0);
v_tailPos_961_ = lean_ctor_get(v_x_957_, 1);
v___x_962_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_958_, v_pos_960_);
if (v___x_962_ == 0)
{
return v___x_955_;
}
else
{
uint8_t v___x_963_; 
v___x_963_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_958_, v_pos_960_);
if (v___x_963_ == 0)
{
return v___x_963_;
}
else
{
uint8_t v___x_964_; 
v___x_964_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_959_, v_tailPos_961_);
if (v___x_964_ == 2)
{
uint8_t v___x_965_; 
v___x_965_ = 0;
return v___x_965_;
}
else
{
return v___x_963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0___boxed(lean_object* v___x_966_, lean_object* v_x_967_, lean_object* v_x_968_){
_start:
{
uint8_t v___x_1153__boxed_969_; uint8_t v_res_970_; lean_object* v_r_971_; 
v___x_1153__boxed_969_ = lean_unbox(v___x_966_);
v_res_970_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1153__boxed_969_, v_x_967_, v_x_968_);
lean_dec_ref(v_x_968_);
lean_dec_ref(v_x_967_);
v_r_971_ = lean_box(v_res_970_);
return v_r_971_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(lean_object* v_hi_972_, lean_object* v_pivot_973_, lean_object* v_as_974_, lean_object* v_i_975_, lean_object* v_k_976_){
_start:
{
uint8_t v___x_987_; 
v___x_987_ = lean_nat_dec_lt(v_k_976_, v_hi_972_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; lean_object* v___x_989_; 
lean_dec(v_k_976_);
v___x_988_ = lean_array_fswap(v_as_974_, v_i_975_, v_hi_972_);
v___x_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_989_, 0, v_i_975_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
return v___x_989_;
}
else
{
lean_object* v___x_990_; lean_object* v_pos_991_; lean_object* v_tailPos_992_; lean_object* v_pos_993_; lean_object* v_tailPos_994_; uint8_t v___x_995_; 
v___x_990_ = lean_array_fget_borrowed(v_as_974_, v_k_976_);
v_pos_991_ = lean_ctor_get(v___x_990_, 0);
v_tailPos_992_ = lean_ctor_get(v___x_990_, 1);
v_pos_993_ = lean_ctor_get(v_pivot_973_, 0);
v_tailPos_994_ = lean_ctor_get(v_pivot_973_, 1);
v___x_995_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_991_, v_pos_993_);
if (v___x_995_ == 0)
{
goto v___jp_977_;
}
else
{
uint8_t v___x_996_; 
v___x_996_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_991_, v_pos_993_);
if (v___x_996_ == 0)
{
goto v___jp_983_;
}
else
{
uint8_t v___x_997_; 
v___x_997_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_992_, v_tailPos_994_);
if (v___x_997_ == 2)
{
goto v___jp_983_;
}
else
{
goto v___jp_977_;
}
}
}
}
v___jp_977_:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_978_ = lean_array_fswap(v_as_974_, v_i_975_, v_k_976_);
v___x_979_ = lean_unsigned_to_nat(1u);
v___x_980_ = lean_nat_add(v_i_975_, v___x_979_);
lean_dec(v_i_975_);
v___x_981_ = lean_nat_add(v_k_976_, v___x_979_);
lean_dec(v_k_976_);
v_as_974_ = v___x_978_;
v_i_975_ = v___x_980_;
v_k_976_ = v___x_981_;
goto _start;
}
v___jp_983_:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = lean_unsigned_to_nat(1u);
v___x_985_ = lean_nat_add(v_k_976_, v___x_984_);
lean_dec(v_k_976_);
v_k_976_ = v___x_985_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg___boxed(lean_object* v_hi_998_, lean_object* v_pivot_999_, lean_object* v_as_1000_, lean_object* v_i_1001_, lean_object* v_k_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(v_hi_998_, v_pivot_999_, v_as_1000_, v_i_1001_, v_k_1002_);
lean_dec_ref(v_pivot_999_);
lean_dec(v_hi_998_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(lean_object* v_n_1004_, lean_object* v_as_1005_, lean_object* v_lo_1006_, lean_object* v_hi_1007_){
_start:
{
lean_object* v___y_1009_; uint8_t v___x_1019_; 
v___x_1019_ = lean_nat_dec_lt(v_lo_1006_, v_hi_1007_);
if (v___x_1019_ == 0)
{
lean_dec(v_lo_1006_);
return v_as_1005_;
}
else
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v_mid_1022_; lean_object* v___y_1024_; lean_object* v___y_1030_; lean_object* v___x_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; 
v___x_1020_ = lean_nat_add(v_lo_1006_, v_hi_1007_);
v___x_1021_ = lean_unsigned_to_nat(1u);
v_mid_1022_ = lean_nat_shiftr(v___x_1020_, v___x_1021_);
lean_dec(v___x_1020_);
v___x_1035_ = lean_array_fget_borrowed(v_as_1005_, v_mid_1022_);
v___x_1036_ = lean_array_fget_borrowed(v_as_1005_, v_lo_1006_);
v___x_1037_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1019_, v___x_1035_, v___x_1036_);
if (v___x_1037_ == 0)
{
v___y_1030_ = v_as_1005_;
goto v___jp_1029_;
}
else
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_array_fswap(v_as_1005_, v_lo_1006_, v_mid_1022_);
v___y_1030_ = v___x_1038_;
goto v___jp_1029_;
}
v___jp_1023_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; 
v___x_1025_ = lean_array_fget_borrowed(v___y_1024_, v_mid_1022_);
v___x_1026_ = lean_array_fget_borrowed(v___y_1024_, v_hi_1007_);
v___x_1027_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1019_, v___x_1025_, v___x_1026_);
if (v___x_1027_ == 0)
{
lean_dec(v_mid_1022_);
v___y_1009_ = v___y_1024_;
goto v___jp_1008_;
}
else
{
lean_object* v___x_1028_; 
v___x_1028_ = lean_array_fswap(v___y_1024_, v_mid_1022_, v_hi_1007_);
lean_dec(v_mid_1022_);
v___y_1009_ = v___x_1028_;
goto v___jp_1008_;
}
}
v___jp_1029_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
v___x_1031_ = lean_array_fget_borrowed(v___y_1030_, v_hi_1007_);
v___x_1032_ = lean_array_fget_borrowed(v___y_1030_, v_lo_1006_);
v___x_1033_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1019_, v___x_1031_, v___x_1032_);
if (v___x_1033_ == 0)
{
v___y_1024_ = v___y_1030_;
goto v___jp_1023_;
}
else
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_array_fswap(v___y_1030_, v_lo_1006_, v_hi_1007_);
v___y_1024_ = v___x_1034_;
goto v___jp_1023_;
}
}
}
v___jp_1008_:
{
lean_object* v_pivot_1010_; lean_object* v___x_1011_; lean_object* v_fst_1012_; lean_object* v_snd_1013_; uint8_t v___x_1014_; 
v_pivot_1010_ = lean_array_fget(v___y_1009_, v_hi_1007_);
lean_inc_n(v_lo_1006_, 2);
v___x_1011_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(v_hi_1007_, v_pivot_1010_, v___y_1009_, v_lo_1006_, v_lo_1006_);
lean_dec(v_pivot_1010_);
v_fst_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_fst_1012_);
v_snd_1013_ = lean_ctor_get(v___x_1011_, 1);
lean_inc(v_snd_1013_);
lean_dec_ref(v___x_1011_);
v___x_1014_ = lean_nat_dec_le(v_hi_1007_, v_fst_1012_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1015_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_n_1004_, v_snd_1013_, v_lo_1006_, v_fst_1012_);
v___x_1016_ = lean_unsigned_to_nat(1u);
v___x_1017_ = lean_nat_add(v_fst_1012_, v___x_1016_);
lean_dec(v_fst_1012_);
v_as_1005_ = v___x_1015_;
v_lo_1006_ = v___x_1017_;
goto _start;
}
else
{
lean_dec(v_fst_1012_);
lean_dec(v_lo_1006_);
return v_snd_1013_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___boxed(lean_object* v_n_1039_, lean_object* v_as_1040_, lean_object* v_lo_1041_, lean_object* v_hi_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_n_1039_, v_as_1040_, v_lo_1041_, v_hi_1042_);
lean_dec(v_hi_1042_);
lean_dec(v_n_1039_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(lean_object* v_as_1044_, size_t v_sz_1045_, size_t v_i_1046_, lean_object* v_b_1047_){
_start:
{
uint8_t v___x_1048_; 
v___x_1048_ = lean_usize_dec_lt(v_i_1046_, v_sz_1045_);
if (v___x_1048_ == 0)
{
return v_b_1047_;
}
else
{
lean_object* v_a_1049_; lean_object* v_pos_1050_; lean_object* v_snd_1051_; lean_object* v_tailPos_1052_; uint8_t v_type_1053_; lean_object* v_fst_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1085_; 
v_a_1049_ = lean_array_uget_borrowed(v_as_1044_, v_i_1046_);
v_pos_1050_ = lean_ctor_get(v_a_1049_, 0);
v_snd_1051_ = lean_ctor_get(v_b_1047_, 1);
lean_inc(v_snd_1051_);
v_tailPos_1052_ = lean_ctor_get(v_a_1049_, 1);
v_type_1053_ = lean_ctor_get_uint8(v_a_1049_, sizeof(void*)*3);
v_fst_1054_ = lean_ctor_get(v_b_1047_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_b_1047_);
if (v_isSharedCheck_1085_ == 0)
{
lean_object* v_unused_1086_; 
v_unused_1086_ = lean_ctor_get(v_b_1047_, 1);
lean_dec(v_unused_1086_);
v___x_1056_ = v_b_1047_;
v_isShared_1057_ = v_isSharedCheck_1085_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_fst_1054_);
lean_dec(v_b_1047_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1085_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v_line_1058_; lean_object* v_character_1059_; lean_object* v_line_1060_; lean_object* v_character_1061_; lean_object* v_tokenModifiers_1062_; lean_object* v___x_1063_; lean_object* v___y_1065_; uint8_t v___x_1084_; 
v_line_1058_ = lean_ctor_get(v_pos_1050_, 0);
v_character_1059_ = lean_ctor_get(v_pos_1050_, 1);
v_line_1060_ = lean_ctor_get(v_snd_1051_, 0);
lean_inc(v_line_1060_);
v_character_1061_ = lean_ctor_get(v_snd_1051_, 1);
lean_inc(v_character_1061_);
lean_dec(v_snd_1051_);
v_tokenModifiers_1062_ = lean_unsigned_to_nat(0u);
v___x_1063_ = lean_nat_sub(v_line_1058_, v_line_1060_);
v___x_1084_ = lean_nat_dec_eq(v_line_1058_, v_line_1060_);
lean_dec(v_line_1060_);
if (v___x_1084_ == 0)
{
lean_dec(v_character_1061_);
v___y_1065_ = v_tokenModifiers_1062_;
goto v___jp_1064_;
}
else
{
v___y_1065_ = v_character_1061_;
goto v___jp_1064_;
}
v___jp_1064_:
{
lean_object* v_character_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1079_; 
v_character_1066_ = lean_ctor_get(v_tailPos_1052_, 1);
v___x_1067_ = lean_nat_sub(v_character_1059_, v___y_1065_);
lean_dec(v___y_1065_);
v___x_1068_ = lean_nat_sub(v_character_1066_, v_character_1059_);
v___x_1069_ = l_Lean_Lsp_SemanticTokenType_toNat(v_type_1053_);
v___x_1070_ = lean_unsigned_to_nat(5u);
v___x_1071_ = lean_mk_empty_array_with_capacity(v___x_1070_);
v___x_1072_ = lean_array_push(v___x_1071_, v___x_1063_);
v___x_1073_ = lean_array_push(v___x_1072_, v___x_1067_);
v___x_1074_ = lean_array_push(v___x_1073_, v___x_1068_);
v___x_1075_ = lean_array_push(v___x_1074_, v___x_1069_);
v___x_1076_ = lean_array_push(v___x_1075_, v_tokenModifiers_1062_);
v___x_1077_ = l_Array_append___redArg(v_fst_1054_, v___x_1076_);
lean_dec_ref(v___x_1076_);
lean_inc_ref(v_pos_1050_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 1, v_pos_1050_);
lean_ctor_set(v___x_1056_, 0, v___x_1077_);
v___x_1079_ = v___x_1056_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1077_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_pos_1050_);
v___x_1079_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
size_t v___x_1080_; size_t v___x_1081_; 
v___x_1080_ = ((size_t)1ULL);
v___x_1081_ = lean_usize_add(v_i_1046_, v___x_1080_);
v_i_1046_ = v___x_1081_;
v_b_1047_ = v___x_1079_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0___boxed(lean_object* v_as_1087_, lean_object* v_sz_1088_, lean_object* v_i_1089_, lean_object* v_b_1090_){
_start:
{
size_t v_sz_boxed_1091_; size_t v_i_boxed_1092_; lean_object* v_res_1093_; 
v_sz_boxed_1091_ = lean_unbox_usize(v_sz_1088_);
lean_dec(v_sz_1088_);
v_i_boxed_1092_ = lean_unbox_usize(v_i_1089_);
lean_dec(v_i_1089_);
v_res_1093_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(v_as_1087_, v_sz_boxed_1091_, v_i_boxed_1092_, v_b_1090_);
lean_dec_ref(v_as_1087_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(lean_object* v_tokens_1096_){
_start:
{
lean_object* v_tokenModifiers_1097_; lean_object* v___y_1099_; lean_object* v___x_1119_; lean_object* v___y_1121_; lean_object* v___y_1122_; uint8_t v___x_1124_; 
v_tokenModifiers_1097_ = lean_unsigned_to_nat(0u);
v___x_1119_ = lean_array_get_size(v_tokens_1096_);
v___x_1124_ = lean_nat_dec_eq(v___x_1119_, v_tokenModifiers_1097_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___y_1128_; uint8_t v___x_1130_; 
v___x_1125_ = lean_unsigned_to_nat(1u);
v___x_1126_ = lean_nat_sub(v___x_1119_, v___x_1125_);
v___x_1130_ = lean_nat_dec_le(v_tokenModifiers_1097_, v___x_1126_);
if (v___x_1130_ == 0)
{
lean_inc(v___x_1126_);
v___y_1128_ = v___x_1126_;
goto v___jp_1127_;
}
else
{
v___y_1128_ = v_tokenModifiers_1097_;
goto v___jp_1127_;
}
v___jp_1127_:
{
uint8_t v___x_1129_; 
v___x_1129_ = lean_nat_dec_le(v___y_1128_, v___x_1126_);
if (v___x_1129_ == 0)
{
lean_dec(v___x_1126_);
lean_inc(v___y_1128_);
v___y_1121_ = v___y_1128_;
v___y_1122_ = v___y_1128_;
goto v___jp_1120_;
}
else
{
v___y_1121_ = v___y_1128_;
v___y_1122_ = v___x_1126_;
goto v___jp_1120_;
}
}
}
else
{
v___y_1099_ = v_tokens_1096_;
goto v___jp_1098_;
}
v___jp_1098_:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v_data_1103_; lean_object* v_lastPos_1104_; lean_object* v___x_1105_; size_t v_sz_1106_; size_t v___x_1107_; lean_object* v___x_1108_; lean_object* v_fst_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1117_; 
v___x_1100_ = lean_unsigned_to_nat(5u);
v___x_1101_ = lean_array_get_size(v___y_1099_);
v___x_1102_ = lean_nat_mul(v___x_1100_, v___x_1101_);
v_data_1103_ = lean_mk_empty_array_with_capacity(v___x_1102_);
lean_dec(v___x_1102_);
v_lastPos_1104_ = ((lean_object*)(l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens___closed__0));
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v_data_1103_);
lean_ctor_set(v___x_1105_, 1, v_lastPos_1104_);
v_sz_1106_ = lean_array_size(v___y_1099_);
v___x_1107_ = ((size_t)0ULL);
v___x_1108_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(v___y_1099_, v_sz_1106_, v___x_1107_, v___x_1105_);
lean_dec_ref(v___y_1099_);
v_fst_1109_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1117_ == 0)
{
lean_object* v_unused_1118_; 
v_unused_1118_ = lean_ctor_get(v___x_1108_, 1);
lean_dec(v_unused_1118_);
v___x_1111_ = v___x_1108_;
v_isShared_1112_ = v_isSharedCheck_1117_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_fst_1109_);
lean_dec(v___x_1108_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1117_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; lean_object* v___x_1115_; 
v___x_1113_ = lean_box(0);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 1, v_fst_1109_);
lean_ctor_set(v___x_1111_, 0, v___x_1113_);
v___x_1115_ = v___x_1111_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1113_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_fst_1109_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
v___jp_1120_:
{
lean_object* v___x_1123_; 
v___x_1123_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v___x_1119_, v_tokens_1096_, v___y_1121_, v___y_1122_);
lean_dec(v___y_1122_);
v___y_1099_ = v___x_1123_;
goto v___jp_1098_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1(lean_object* v_n_1131_, lean_object* v_as_1132_, lean_object* v_lo_1133_, lean_object* v_hi_1134_, lean_object* v_w_1135_, lean_object* v_hlo_1136_, lean_object* v_hhi_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_n_1131_, v_as_1132_, v_lo_1133_, v_hi_1134_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___boxed(lean_object* v_n_1139_, lean_object* v_as_1140_, lean_object* v_lo_1141_, lean_object* v_hi_1142_, lean_object* v_w_1143_, lean_object* v_hlo_1144_, lean_object* v_hhi_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1(v_n_1139_, v_as_1140_, v_lo_1141_, v_hi_1142_, v_w_1143_, v_hlo_1144_, v_hhi_1145_);
lean_dec(v_hi_1142_);
lean_dec(v_n_1139_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1(lean_object* v_n_1147_, lean_object* v_lo_1148_, lean_object* v_hi_1149_, lean_object* v_hhi_1150_, lean_object* v_pivot_1151_, lean_object* v_as_1152_, lean_object* v_i_1153_, lean_object* v_k_1154_, lean_object* v_ilo_1155_, lean_object* v_ik_1156_, lean_object* v_w_1157_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(v_hi_1149_, v_pivot_1151_, v_as_1152_, v_i_1153_, v_k_1154_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___boxed(lean_object* v_n_1159_, lean_object* v_lo_1160_, lean_object* v_hi_1161_, lean_object* v_hhi_1162_, lean_object* v_pivot_1163_, lean_object* v_as_1164_, lean_object* v_i_1165_, lean_object* v_k_1166_, lean_object* v_ilo_1167_, lean_object* v_ik_1168_, lean_object* v_w_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1(v_n_1159_, v_lo_1160_, v_hi_1161_, v_hhi_1162_, v_pivot_1163_, v_as_1164_, v_i_1165_, v_k_1166_, v_ilo_1167_, v_ik_1168_, v_w_1169_);
lean_dec_ref(v_pivot_1163_);
lean_dec(v_hi_1161_);
lean_dec(v_lo_1160_);
lean_dec(v_n_1159_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(lean_object* v_tk_1171_, uint8_t v_k_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v___y_1175_; 
if (v_k_1172_ == 18)
{
lean_object* v___x_1180_; 
v___x_1180_ = lean_unsigned_to_nat(3u);
v___y_1175_ = v___x_1180_;
goto v___jp_1174_;
}
else
{
lean_object* v___x_1181_; 
v___x_1181_ = lean_unsigned_to_nat(5u);
v___y_1175_ = v___x_1181_;
goto v___jp_1174_;
}
v___jp_1174_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1176_ = lean_box(0);
v___x_1177_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1177_, 0, v_tk_1171_);
lean_ctor_set(v___x_1177_, 1, v___y_1175_);
lean_ctor_set_uint8(v___x_1177_, sizeof(void*)*2, v_k_1172_);
v___x_1178_ = lean_array_push(v_a_1173_, v___x_1177_);
v___x_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1176_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
return v___x_1179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok___boxed(lean_object* v_tk_1182_, lean_object* v_k_1183_, lean_object* v_a_1184_){
_start:
{
uint8_t v_k_boxed_1185_; lean_object* v_res_1186_; 
v_k_boxed_1185_ = lean_unbox(v_k_1183_);
v_res_1186_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_1182_, v_k_boxed_1185_, v_a_1184_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine(lean_object* v_line_1188_, lean_object* v_value_1189_){
_start:
{
uint8_t v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = 0;
v___x_1191_ = l_Lean_Syntax_getRange_x3f(v_line_1188_, v___x_1190_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v___x_1192_; 
v___x_1192_ = lean_box(0);
return v___x_1192_;
}
else
{
lean_object* v_val_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1223_; 
v_val_1193_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1195_ = v___x_1191_;
v_isShared_1196_ = v_isSharedCheck_1223_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_val_1193_);
lean_dec(v___x_1191_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1223_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v_start_1197_; lean_object* v_stop_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1222_; 
v_start_1197_ = lean_ctor_get(v_val_1193_, 0);
v_stop_1198_ = lean_ctor_get(v_val_1193_, 1);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_val_1193_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1200_ = v_val_1193_;
v_isShared_1201_ = v_isSharedCheck_1222_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_stop_1198_);
lean_inc(v_start_1197_);
lean_dec(v_val_1193_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1222_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
uint8_t v___y_1203_; lean_object* v___y_1204_; lean_object* v___x_1214_; lean_object* v___x_1215_; uint8_t v___x_1216_; 
v___x_1214_ = lean_string_utf8_byte_size(v_value_1189_);
v___x_1215_ = lean_unsigned_to_nat(1u);
v___x_1216_ = lean_nat_dec_le(v___x_1215_, v___x_1214_);
if (v___x_1216_ == 0)
{
goto v___jp_1212_;
}
else
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; 
v___x_1217_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0));
v___x_1218_ = lean_unsigned_to_nat(0u);
v___x_1219_ = lean_nat_sub(v___x_1214_, v___x_1215_);
v___x_1220_ = lean_string_memcmp(v_value_1189_, v___x_1217_, v___x_1219_, v___x_1218_, v___x_1215_);
lean_dec(v___x_1219_);
if (v___x_1220_ == 0)
{
goto v___jp_1212_;
}
else
{
lean_object* v___x_1221_; 
v___x_1221_ = lean_nat_sub(v_stop_1198_, v___x_1215_);
lean_dec(v_stop_1198_);
v___y_1203_ = v___x_1216_;
v___y_1204_ = v___x_1221_;
goto v___jp_1202_;
}
}
v___jp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 1, v___y_1204_);
v___x_1206_ = v___x_1200_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_start_1197_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v___y_1204_);
v___x_1206_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1207_ = l_Lean_Syntax_ofRange(v___x_1206_, v___y_1203_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1207_);
v___x_1209_ = v___x_1195_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
v___jp_1212_:
{
uint8_t v___x_1213_; 
v___x_1213_ = 1;
v___y_1203_ = v___x_1213_;
v___y_1204_ = v_stop_1198_;
goto v___jp_1202_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___boxed(lean_object* v_line_1224_, lean_object* v_value_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine(v_line_1224_, v_value_1225_);
lean_dec_ref(v_value_1225_);
lean_dec(v_line_1224_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goArg(lean_object* v_arg_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_Doc_ArgView_of(v_arg_1227_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = lean_box(0);
v___x_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
lean_ctor_set(v___x_1231_, 1, v_a_1228_);
return v___x_1231_;
}
else
{
lean_object* v_val_1232_; 
v_val_1232_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_val_1232_);
lean_dec_ref_known(v___x_1229_, 1);
switch(lean_obj_tag(v_val_1232_))
{
case 0:
{
lean_object* v_val_1233_; uint8_t v___x_1234_; lean_object* v___x_1235_; 
v_val_1233_ = lean_ctor_get(v_val_1232_, 1);
lean_inc(v_val_1233_);
lean_dec_ref_known(v_val_1232_, 2);
v___x_1234_ = 11;
v___x_1235_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_val_1233_, v___x_1234_, v_a_1228_);
return v___x_1235_;
}
case 1:
{
lean_object* v_parens_1236_; lean_object* v_name_1237_; lean_object* v_assign_1238_; lean_object* v_val_1239_; lean_object* v___y_1241_; 
v_parens_1236_ = lean_ctor_get(v_val_1232_, 1);
lean_inc(v_parens_1236_);
v_name_1237_ = lean_ctor_get(v_val_1232_, 2);
lean_inc(v_name_1237_);
v_assign_1238_ = lean_ctor_get(v_val_1232_, 3);
lean_inc(v_assign_1238_);
v_val_1239_ = lean_ctor_get(v_val_1232_, 4);
lean_inc(v_val_1239_);
lean_dec_ref_known(v_val_1232_, 5);
if (lean_obj_tag(v_parens_1236_) == 1)
{
lean_object* v_val_1264_; lean_object* v_fst_1265_; uint8_t v___x_1266_; lean_object* v___x_1267_; lean_object* v_snd_1268_; 
v_val_1264_ = lean_ctor_get(v_parens_1236_, 0);
v_fst_1265_ = lean_ctor_get(v_val_1264_, 0);
v___x_1266_ = 0;
lean_inc(v_fst_1265_);
v___x_1267_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_fst_1265_, v___x_1266_, v_a_1228_);
v_snd_1268_ = lean_ctor_get(v___x_1267_, 1);
lean_inc(v_snd_1268_);
lean_dec_ref(v___x_1267_);
v___y_1241_ = v_snd_1268_;
goto v___jp_1240_;
}
else
{
v___y_1241_ = v_a_1228_;
goto v___jp_1240_;
}
v___jp_1240_:
{
uint8_t v___x_1242_; lean_object* v___x_1243_; lean_object* v_snd_1244_; uint8_t v___x_1245_; lean_object* v___x_1246_; lean_object* v_snd_1247_; uint8_t v___x_1248_; lean_object* v___x_1249_; 
v___x_1242_ = 2;
v___x_1243_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1237_, v___x_1242_, v___y_1241_);
v_snd_1244_ = lean_ctor_get(v___x_1243_, 1);
lean_inc(v_snd_1244_);
lean_dec_ref(v___x_1243_);
v___x_1245_ = 0;
v___x_1246_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_assign_1238_, v___x_1245_, v_snd_1244_);
v_snd_1247_ = lean_ctor_get(v___x_1246_, 1);
lean_inc(v_snd_1247_);
lean_dec_ref(v___x_1246_);
v___x_1248_ = 11;
v___x_1249_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_val_1239_, v___x_1248_, v_snd_1247_);
if (lean_obj_tag(v_parens_1236_) == 1)
{
lean_object* v_val_1250_; lean_object* v_snd_1251_; lean_object* v_snd_1252_; lean_object* v___x_1253_; 
v_val_1250_ = lean_ctor_get(v_parens_1236_, 0);
lean_inc(v_val_1250_);
lean_dec_ref_known(v_parens_1236_, 1);
v_snd_1251_ = lean_ctor_get(v___x_1249_, 1);
lean_inc(v_snd_1251_);
lean_dec_ref(v___x_1249_);
v_snd_1252_ = lean_ctor_get(v_val_1250_, 1);
lean_inc(v_snd_1252_);
lean_dec(v_val_1250_);
v___x_1253_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_snd_1252_, v___x_1245_, v_snd_1251_);
return v___x_1253_;
}
else
{
lean_object* v_snd_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1262_; 
lean_dec(v_parens_1236_);
v_snd_1254_ = lean_ctor_get(v___x_1249_, 1);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1262_ == 0)
{
lean_object* v_unused_1263_; 
v_unused_1263_ = lean_ctor_get(v___x_1249_, 0);
lean_dec(v_unused_1263_);
v___x_1256_ = v___x_1249_;
v_isShared_1257_ = v_isSharedCheck_1262_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_snd_1254_);
lean_dec(v___x_1249_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1262_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1258_; lean_object* v___x_1260_; 
v___x_1258_ = lean_box(0);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v___x_1258_);
v___x_1260_ = v___x_1256_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_snd_1254_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
}
default: 
{
lean_object* v_sign_1269_; lean_object* v_name_1270_; uint8_t v___x_1271_; lean_object* v___x_1272_; lean_object* v_snd_1273_; uint8_t v___x_1274_; lean_object* v___x_1275_; 
v_sign_1269_ = lean_ctor_get(v_val_1232_, 1);
lean_inc(v_sign_1269_);
v_name_1270_ = lean_ctor_get(v_val_1232_, 2);
lean_inc(v_name_1270_);
lean_dec_ref_known(v_val_1232_, 3);
v___x_1271_ = 0;
v___x_1272_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_sign_1269_, v___x_1271_, v_a_1228_);
v_snd_1273_ = lean_ctor_get(v___x_1272_, 1);
lean_inc(v_snd_1273_);
lean_dec_ref(v___x_1272_);
v___x_1274_ = 2;
v___x_1275_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1270_, v___x_1274_, v_snd_1273_);
return v___x_1275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goTarget(lean_object* v_tgt_1276_, lean_object* v_a_1277_){
_start:
{
if (lean_obj_tag(v_tgt_1276_) == 0)
{
lean_object* v_opener_1278_; lean_object* v_url_1279_; lean_object* v_closer_1280_; uint8_t v___x_1281_; lean_object* v___x_1282_; lean_object* v_snd_1283_; uint8_t v___x_1284_; lean_object* v___x_1285_; lean_object* v_snd_1286_; lean_object* v___x_1287_; 
v_opener_1278_ = lean_ctor_get(v_tgt_1276_, 1);
lean_inc(v_opener_1278_);
v_url_1279_ = lean_ctor_get(v_tgt_1276_, 2);
lean_inc(v_url_1279_);
v_closer_1280_ = lean_ctor_get(v_tgt_1276_, 3);
lean_inc(v_closer_1280_);
lean_dec_ref_known(v_tgt_1276_, 4);
v___x_1281_ = 0;
v___x_1282_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1278_, v___x_1281_, v_a_1277_);
v_snd_1283_ = lean_ctor_get(v___x_1282_, 1);
lean_inc(v_snd_1283_);
lean_dec_ref(v___x_1282_);
v___x_1284_ = 18;
v___x_1285_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_url_1279_, v___x_1284_, v_snd_1283_);
v_snd_1286_ = lean_ctor_get(v___x_1285_, 1);
lean_inc(v_snd_1286_);
lean_dec_ref(v___x_1285_);
v___x_1287_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1280_, v___x_1281_, v_snd_1286_);
return v___x_1287_;
}
else
{
lean_object* v_opener_1288_; lean_object* v_name_1289_; lean_object* v_closer_1290_; uint8_t v___x_1291_; lean_object* v___x_1292_; lean_object* v_snd_1293_; uint8_t v___x_1294_; lean_object* v___x_1295_; lean_object* v_snd_1296_; lean_object* v___x_1297_; 
v_opener_1288_ = lean_ctor_get(v_tgt_1276_, 1);
lean_inc(v_opener_1288_);
v_name_1289_ = lean_ctor_get(v_tgt_1276_, 2);
lean_inc(v_name_1289_);
v_closer_1290_ = lean_ctor_get(v_tgt_1276_, 3);
lean_inc(v_closer_1290_);
lean_dec_ref_known(v_tgt_1276_, 4);
v___x_1291_ = 0;
v___x_1292_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1288_, v___x_1291_, v_a_1277_);
v_snd_1293_ = lean_ctor_get(v___x_1292_, 1);
lean_inc(v_snd_1293_);
lean_dec_ref(v___x_1292_);
v___x_1294_ = 2;
v___x_1295_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1289_, v___x_1294_, v_snd_1293_);
v_snd_1296_ = lean_ctor_get(v___x_1295_, 1);
lean_inc(v_snd_1296_);
lean_dec_ref(v___x_1295_);
v___x_1297_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1290_, v___x_1291_, v_snd_1296_);
return v___x_1297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode_spec__0(lean_object* v_as_1298_, size_t v_sz_1299_, size_t v_i_1300_, lean_object* v_b_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v_a_1304_; lean_object* v_snd_1305_; uint8_t v___x_1309_; 
v___x_1309_ = lean_usize_dec_lt(v_i_1300_, v_sz_1299_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1310_; 
v___x_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1310_, 0, v_b_1301_);
lean_ctor_set(v___x_1310_, 1, v___y_1302_);
return v___x_1310_;
}
else
{
lean_object* v___x_1311_; lean_object* v_a_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1311_ = lean_box(0);
v_a_1312_ = lean_array_uget_borrowed(v_as_1298_, v_i_1300_);
v___x_1313_ = l_Lean_TSyntax_getVersoCodeLine(v_a_1312_);
v___x_1314_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine(v_a_1312_, v___x_1313_);
lean_dec_ref(v___x_1313_);
if (lean_obj_tag(v___x_1314_) == 1)
{
lean_object* v_val_1315_; uint8_t v___x_1316_; lean_object* v___x_1317_; lean_object* v_snd_1318_; 
v_val_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_val_1315_);
lean_dec_ref_known(v___x_1314_, 1);
v___x_1316_ = 18;
v___x_1317_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_val_1315_, v___x_1316_, v___y_1302_);
v_snd_1318_ = lean_ctor_get(v___x_1317_, 1);
lean_inc(v_snd_1318_);
lean_dec_ref(v___x_1317_);
v_a_1304_ = v___x_1311_;
v_snd_1305_ = v_snd_1318_;
goto v___jp_1303_;
}
else
{
lean_dec(v___x_1314_);
v_a_1304_ = v___x_1311_;
v_snd_1305_ = v___y_1302_;
goto v___jp_1303_;
}
}
v___jp_1303_:
{
size_t v___x_1306_; size_t v___x_1307_; 
v___x_1306_ = ((size_t)1ULL);
v___x_1307_ = lean_usize_add(v_i_1300_, v___x_1306_);
v_i_1300_ = v___x_1307_;
v_b_1301_ = v_a_1304_;
v___y_1302_ = v_snd_1305_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode_spec__0___boxed(lean_object* v_as_1319_, lean_object* v_sz_1320_, lean_object* v_i_1321_, lean_object* v_b_1322_, lean_object* v___y_1323_){
_start:
{
size_t v_sz_boxed_1324_; size_t v_i_boxed_1325_; lean_object* v_res_1326_; 
v_sz_boxed_1324_ = lean_unbox_usize(v_sz_1320_);
lean_dec(v_sz_1320_);
v_i_boxed_1325_ = lean_unbox_usize(v_i_1321_);
lean_dec(v_i_1321_);
v_res_1326_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode_spec__0(v_as_1319_, v_sz_boxed_1324_, v_i_boxed_1325_, v_b_1322_, v___y_1323_);
lean_dec_ref(v_as_1319_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode(lean_object* v_code_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_opener_1329_; lean_object* v_content_1330_; lean_object* v_closer_1331_; uint8_t v___x_1332_; lean_object* v___x_1333_; lean_object* v_snd_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; size_t v_sz_1337_; size_t v___x_1338_; lean_object* v___x_1339_; lean_object* v_snd_1340_; lean_object* v___x_1341_; 
v_opener_1329_ = lean_ctor_get(v_code_1327_, 1);
lean_inc(v_opener_1329_);
v_content_1330_ = lean_ctor_get(v_code_1327_, 2);
lean_inc(v_content_1330_);
v_closer_1331_ = lean_ctor_get(v_code_1327_, 3);
lean_inc(v_closer_1331_);
lean_dec_ref(v_code_1327_);
v___x_1332_ = 0;
v___x_1333_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1329_, v___x_1332_, v_a_1328_);
v_snd_1334_ = lean_ctor_get(v___x_1333_, 1);
lean_inc(v_snd_1334_);
lean_dec_ref(v___x_1333_);
v___x_1335_ = l_Lean_TSyntax_getVersoCodeLines(v_content_1330_);
lean_dec(v_content_1330_);
v___x_1336_ = lean_box(0);
v_sz_1337_ = lean_array_size(v___x_1335_);
v___x_1338_ = ((size_t)0ULL);
v___x_1339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode_spec__0(v___x_1335_, v_sz_1337_, v___x_1338_, v___x_1336_, v_snd_1334_);
lean_dec_ref(v___x_1335_);
v_snd_1340_ = lean_ctor_get(v___x_1339_, 1);
lean_inc(v_snd_1340_);
lean_dec_ref(v___x_1339_);
v___x_1341_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1331_, v___x_1332_, v_snd_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(lean_object* v_as_1342_, size_t v_sz_1343_, size_t v_i_1344_, lean_object* v_b_1345_, lean_object* v___y_1346_){
_start:
{
uint8_t v___x_1347_; 
v___x_1347_ = lean_usize_dec_lt(v_i_1344_, v_sz_1343_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; 
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v_b_1345_);
lean_ctor_set(v___x_1348_, 1, v___y_1346_);
return v___x_1348_;
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1350_; lean_object* v_snd_1351_; lean_object* v___x_1352_; size_t v___x_1353_; size_t v___x_1354_; 
v_a_1349_ = lean_array_uget_borrowed(v_as_1342_, v_i_1344_);
lean_inc(v_a_1349_);
v___x_1350_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goArg(v_a_1349_, v___y_1346_);
v_snd_1351_ = lean_ctor_get(v___x_1350_, 1);
lean_inc(v_snd_1351_);
lean_dec_ref(v___x_1350_);
v___x_1352_ = lean_box(0);
v___x_1353_ = ((size_t)1ULL);
v___x_1354_ = lean_usize_add(v_i_1344_, v___x_1353_);
v_i_1344_ = v___x_1354_;
v_b_1345_ = v___x_1352_;
v___y_1346_ = v_snd_1351_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2___boxed(lean_object* v_as_1356_, lean_object* v_sz_1357_, lean_object* v_i_1358_, lean_object* v_b_1359_, lean_object* v___y_1360_){
_start:
{
size_t v_sz_boxed_1361_; size_t v_i_boxed_1362_; lean_object* v_res_1363_; 
v_sz_boxed_1361_ = lean_unbox_usize(v_sz_1357_);
lean_dec(v_sz_1357_);
v_i_boxed_1362_ = lean_unbox_usize(v_i_1358_);
lean_dec(v_i_1358_);
v_res_1363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(v_as_1356_, v_sz_boxed_1361_, v_i_boxed_1362_, v_b_1359_, v___y_1360_);
lean_dec_ref(v_as_1356_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem(lean_object* v_getTokens_1364_, lean_object* v_marker_1365_, lean_object* v_contents_1366_, lean_object* v_a_1367_){
_start:
{
uint8_t v___x_1368_; lean_object* v___x_1369_; lean_object* v_snd_1370_; lean_object* v___x_1371_; size_t v_sz_1372_; size_t v___x_1373_; lean_object* v___x_1374_; lean_object* v_snd_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
v___x_1368_ = 0;
v___x_1369_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_marker_1365_, v___x_1368_, v_a_1367_);
v_snd_1370_ = lean_ctor_get(v___x_1369_, 1);
lean_inc(v_snd_1370_);
lean_dec_ref(v___x_1369_);
v___x_1371_ = lean_box(0);
v_sz_1372_ = lean_array_size(v_contents_1366_);
v___x_1373_ = ((size_t)0ULL);
v___x_1374_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1364_, v_contents_1366_, v_sz_1372_, v___x_1373_, v___x_1371_, v_snd_1370_);
v_snd_1375_ = lean_ctor_get(v___x_1374_, 1);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1382_ == 0)
{
lean_object* v_unused_1383_; 
v_unused_1383_ = lean_ctor_get(v___x_1374_, 0);
lean_dec(v_unused_1383_);
v___x_1377_ = v___x_1374_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_snd_1375_);
lean_dec(v___x_1374_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 0, v___x_1371_);
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1371_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_snd_1375_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3(lean_object* v_getTokens_1384_, lean_object* v_as_1385_, size_t v_sz_1386_, size_t v_i_1387_, lean_object* v_b_1388_, lean_object* v___y_1389_){
_start:
{
uint8_t v___x_1390_; 
v___x_1390_ = lean_usize_dec_lt(v_i_1387_, v_sz_1386_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1391_; 
lean_dec_ref(v_getTokens_1384_);
v___x_1391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1391_, 0, v_b_1388_);
lean_ctor_set(v___x_1391_, 1, v___y_1389_);
return v___x_1391_;
}
else
{
lean_object* v_a_1392_; lean_object* v_marker_1393_; lean_object* v_contents_1394_; lean_object* v___x_1395_; lean_object* v_snd_1396_; lean_object* v___x_1397_; size_t v___x_1398_; size_t v___x_1399_; 
v_a_1392_ = lean_array_uget_borrowed(v_as_1385_, v_i_1387_);
v_marker_1393_ = lean_ctor_get(v_a_1392_, 1);
v_contents_1394_ = lean_ctor_get(v_a_1392_, 2);
lean_inc(v_marker_1393_);
lean_inc_ref(v_getTokens_1384_);
v___x_1395_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem(v_getTokens_1384_, v_marker_1393_, v_contents_1394_, v___y_1389_);
v_snd_1396_ = lean_ctor_get(v___x_1395_, 1);
lean_inc(v_snd_1396_);
lean_dec_ref(v___x_1395_);
v___x_1397_ = lean_box(0);
v___x_1398_ = ((size_t)1ULL);
v___x_1399_ = lean_usize_add(v_i_1387_, v___x_1398_);
v_i_1387_ = v___x_1399_;
v_b_1388_ = v___x_1397_;
v___y_1389_ = v_snd_1396_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__4(lean_object* v_getTokens_1401_, lean_object* v_as_1402_, size_t v_sz_1403_, size_t v_i_1404_, lean_object* v_b_1405_, lean_object* v___y_1406_){
_start:
{
uint8_t v___x_1407_; 
v___x_1407_ = lean_usize_dec_lt(v_i_1404_, v_sz_1403_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; 
lean_dec_ref(v_getTokens_1401_);
v___x_1408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1408_, 0, v_b_1405_);
lean_ctor_set(v___x_1408_, 1, v___y_1406_);
return v___x_1408_;
}
else
{
lean_object* v_a_1409_; lean_object* v_marker_1410_; lean_object* v_contents_1411_; lean_object* v___x_1412_; lean_object* v_snd_1413_; lean_object* v___x_1414_; size_t v___x_1415_; size_t v___x_1416_; 
v_a_1409_ = lean_array_uget_borrowed(v_as_1402_, v_i_1404_);
v_marker_1410_ = lean_ctor_get(v_a_1409_, 1);
v_contents_1411_ = lean_ctor_get(v_a_1409_, 2);
lean_inc(v_marker_1410_);
lean_inc_ref(v_getTokens_1401_);
v___x_1412_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem(v_getTokens_1401_, v_marker_1410_, v_contents_1411_, v___y_1406_);
v_snd_1413_ = lean_ctor_get(v___x_1412_, 1);
lean_inc(v_snd_1413_);
lean_dec_ref(v___x_1412_);
v___x_1414_ = lean_box(0);
v___x_1415_ = ((size_t)1ULL);
v___x_1416_ = lean_usize_add(v_i_1404_, v___x_1415_);
v_i_1404_ = v___x_1416_;
v_b_1405_ = v___x_1414_;
v___y_1406_ = v_snd_1413_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDesc(lean_object* v_getTokens_1418_, lean_object* v_item_1419_, lean_object* v_a_1420_){
_start:
{
lean_object* v_marker_1421_; lean_object* v_term_1422_; lean_object* v_desc_1423_; uint8_t v___x_1424_; lean_object* v___x_1425_; lean_object* v_snd_1426_; lean_object* v___x_1427_; size_t v_sz_1428_; size_t v___x_1429_; lean_object* v___x_1430_; lean_object* v_snd_1431_; size_t v_sz_1432_; lean_object* v___x_1433_; lean_object* v_snd_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
v_marker_1421_ = lean_ctor_get(v_item_1419_, 1);
lean_inc(v_marker_1421_);
v_term_1422_ = lean_ctor_get(v_item_1419_, 2);
lean_inc_ref(v_term_1422_);
v_desc_1423_ = lean_ctor_get(v_item_1419_, 3);
lean_inc_ref(v_desc_1423_);
lean_dec_ref(v_item_1419_);
v___x_1424_ = 0;
v___x_1425_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_marker_1421_, v___x_1424_, v_a_1420_);
v_snd_1426_ = lean_ctor_get(v___x_1425_, 1);
lean_inc(v_snd_1426_);
lean_dec_ref(v___x_1425_);
v___x_1427_ = lean_box(0);
v_sz_1428_ = lean_array_size(v_term_1422_);
v___x_1429_ = ((size_t)0ULL);
lean_inc_ref(v_getTokens_1418_);
v___x_1430_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1418_, v_term_1422_, v_sz_1428_, v___x_1429_, v___x_1427_, v_snd_1426_);
lean_dec_ref(v_term_1422_);
v_snd_1431_ = lean_ctor_get(v___x_1430_, 1);
lean_inc(v_snd_1431_);
lean_dec_ref(v___x_1430_);
v_sz_1432_ = lean_array_size(v_desc_1423_);
v___x_1433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1418_, v_desc_1423_, v_sz_1432_, v___x_1429_, v___x_1427_, v_snd_1431_);
lean_dec_ref(v_desc_1423_);
v_snd_1434_ = lean_ctor_get(v___x_1433_, 1);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1441_ == 0)
{
lean_object* v_unused_1442_; 
v_unused_1442_ = lean_ctor_get(v___x_1433_, 0);
lean_dec(v_unused_1442_);
v___x_1436_ = v___x_1433_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_snd_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v___x_1427_);
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_snd_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__5(lean_object* v_getTokens_1443_, lean_object* v_as_1444_, size_t v_sz_1445_, size_t v_i_1446_, lean_object* v_b_1447_, lean_object* v___y_1448_){
_start:
{
uint8_t v___x_1449_; 
v___x_1449_ = lean_usize_dec_lt(v_i_1446_, v_sz_1445_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; 
lean_dec_ref(v_getTokens_1443_);
v___x_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1450_, 0, v_b_1447_);
lean_ctor_set(v___x_1450_, 1, v___y_1448_);
return v___x_1450_;
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1452_; lean_object* v_snd_1453_; lean_object* v___x_1454_; size_t v___x_1455_; size_t v___x_1456_; 
v_a_1451_ = lean_array_uget_borrowed(v_as_1444_, v_i_1446_);
lean_inc(v_a_1451_);
lean_inc_ref(v_getTokens_1443_);
v___x_1452_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDesc(v_getTokens_1443_, v_a_1451_, v___y_1448_);
v_snd_1453_ = lean_ctor_get(v___x_1452_, 1);
lean_inc(v_snd_1453_);
lean_dec_ref(v___x_1452_);
v___x_1454_ = lean_box(0);
v___x_1455_ = ((size_t)1ULL);
v___x_1456_ = lean_usize_add(v_i_1446_, v___x_1455_);
v_i_1446_ = v___x_1456_;
v_b_1447_ = v___x_1454_;
v___y_1448_ = v_snd_1453_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6(lean_object* v_getTokens_1458_, lean_object* v_as_1459_, size_t v_i_1460_, size_t v_stop_1461_, lean_object* v_b_1462_, lean_object* v___y_1463_){
_start:
{
uint8_t v___x_1464_; 
v___x_1464_ = lean_usize_dec_eq(v_i_1460_, v_stop_1461_);
if (v___x_1464_ == 0)
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v_fst_1467_; lean_object* v_snd_1468_; size_t v___x_1469_; size_t v___x_1470_; 
v___x_1465_ = lean_array_uget_borrowed(v_as_1459_, v_i_1460_);
lean_inc(v___x_1465_);
lean_inc_ref(v_getTokens_1458_);
v___x_1466_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_getTokens_1458_, v___x_1465_, v___y_1463_);
v_fst_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_fst_1467_);
v_snd_1468_ = lean_ctor_get(v___x_1466_, 1);
lean_inc(v_snd_1468_);
lean_dec_ref(v___x_1466_);
v___x_1469_ = ((size_t)1ULL);
v___x_1470_ = lean_usize_add(v_i_1460_, v___x_1469_);
v_i_1460_ = v___x_1470_;
v_b_1462_ = v_fst_1467_;
v___y_1463_ = v_snd_1468_;
goto _start;
}
else
{
lean_object* v___x_1472_; 
lean_dec_ref(v_getTokens_1458_);
v___x_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1472_, 0, v_b_1462_);
lean_ctor_set(v___x_1472_, 1, v___y_1463_);
return v___x_1472_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(lean_object* v_getTokens_1473_, lean_object* v_stx_1474_, lean_object* v_a_1475_){
_start:
{
lean_object* v___x_1476_; 
lean_inc(v_stx_1474_);
v___x_1476_ = l_Lean_Doc_InlineView_of(v_stx_1474_);
if (lean_obj_tag(v___x_1476_) == 1)
{
lean_object* v_val_1477_; 
lean_dec(v_stx_1474_);
v_val_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_val_1477_);
lean_dec_ref_known(v___x_1476_, 1);
switch(lean_obj_tag(v_val_1477_))
{
case 1:
{
lean_object* v_view_1478_; lean_object* v_opener_1479_; lean_object* v_content_1480_; lean_object* v_closer_1481_; lean_object* v___x_1482_; 
v_view_1478_ = lean_ctor_get(v_val_1477_, 0);
lean_inc_ref(v_view_1478_);
lean_dec_ref_known(v_val_1477_, 1);
v_opener_1479_ = lean_ctor_get(v_view_1478_, 1);
lean_inc(v_opener_1479_);
v_content_1480_ = lean_ctor_get(v_view_1478_, 2);
lean_inc_ref(v_content_1480_);
v_closer_1481_ = lean_ctor_get(v_view_1478_, 3);
lean_inc(v_closer_1481_);
lean_dec_ref(v_view_1478_);
v___x_1482_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDelimited(v_getTokens_1473_, v_opener_1479_, v_closer_1481_, v_content_1480_, v_a_1475_);
lean_dec_ref(v_content_1480_);
return v___x_1482_;
}
case 2:
{
lean_object* v_view_1483_; lean_object* v_opener_1484_; lean_object* v_content_1485_; lean_object* v_closer_1486_; lean_object* v___x_1487_; 
v_view_1483_ = lean_ctor_get(v_val_1477_, 0);
lean_inc_ref(v_view_1483_);
lean_dec_ref_known(v_val_1477_, 1);
v_opener_1484_ = lean_ctor_get(v_view_1483_, 1);
lean_inc(v_opener_1484_);
v_content_1485_ = lean_ctor_get(v_view_1483_, 2);
lean_inc_ref(v_content_1485_);
v_closer_1486_ = lean_ctor_get(v_view_1483_, 3);
lean_inc(v_closer_1486_);
lean_dec_ref(v_view_1483_);
v___x_1487_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDelimited(v_getTokens_1473_, v_opener_1484_, v_closer_1486_, v_content_1485_, v_a_1475_);
lean_dec_ref(v_content_1485_);
return v___x_1487_;
}
case 3:
{
lean_object* v_view_1488_; lean_object* v___x_1489_; 
lean_dec_ref(v_getTokens_1473_);
v_view_1488_ = lean_ctor_get(v_val_1477_, 0);
lean_inc_ref(v_view_1488_);
lean_dec_ref_known(v_val_1477_, 1);
v___x_1489_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode(v_view_1488_, v_a_1475_);
return v___x_1489_;
}
case 4:
{
lean_object* v_view_1490_; lean_object* v_marker_1491_; lean_object* v_code_1492_; uint8_t v___x_1493_; lean_object* v___x_1494_; lean_object* v_snd_1495_; lean_object* v___x_1496_; 
lean_dec_ref(v_getTokens_1473_);
v_view_1490_ = lean_ctor_get(v_val_1477_, 0);
lean_inc_ref(v_view_1490_);
lean_dec_ref_known(v_val_1477_, 1);
v_marker_1491_ = lean_ctor_get(v_view_1490_, 1);
lean_inc(v_marker_1491_);
v_code_1492_ = lean_ctor_get(v_view_1490_, 2);
lean_inc_ref(v_code_1492_);
lean_dec_ref(v_view_1490_);
v___x_1493_ = 0;
v___x_1494_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_marker_1491_, v___x_1493_, v_a_1475_);
v_snd_1495_ = lean_ctor_get(v___x_1494_, 1);
lean_inc(v_snd_1495_);
lean_dec_ref(v___x_1494_);
v___x_1496_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode(v_code_1492_, v_snd_1495_);
return v___x_1496_;
}
case 5:
{
lean_object* v_view_1497_; lean_object* v_opener_1498_; lean_object* v_content_1499_; lean_object* v_closer_1500_; lean_object* v_target_1501_; lean_object* v___x_1502_; lean_object* v_snd_1503_; lean_object* v___x_1504_; 
v_view_1497_ = lean_ctor_get(v_val_1477_, 0);
lean_inc_ref(v_view_1497_);
lean_dec_ref_known(v_val_1477_, 1);
v_opener_1498_ = lean_ctor_get(v_view_1497_, 1);
lean_inc(v_opener_1498_);
v_content_1499_ = lean_ctor_get(v_view_1497_, 2);
lean_inc_ref(v_content_1499_);
v_closer_1500_ = lean_ctor_get(v_view_1497_, 3);
lean_inc(v_closer_1500_);
v_target_1501_ = lean_ctor_get(v_view_1497_, 4);
lean_inc_ref(v_target_1501_);
lean_dec_ref(v_view_1497_);
v___x_1502_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDelimited(v_getTokens_1473_, v_opener_1498_, v_closer_1500_, v_content_1499_, v_a_1475_);
lean_dec_ref(v_content_1499_);
v_snd_1503_ = lean_ctor_get(v___x_1502_, 1);
lean_inc(v_snd_1503_);
lean_dec_ref(v___x_1502_);
v___x_1504_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goTarget(v_target_1501_, v_snd_1503_);
return v___x_1504_;
}
case 6:
{
lean_object* v_view_1505_; lean_object* v_opener_1506_; lean_object* v_alt_1507_; lean_object* v_closer_1508_; lean_object* v_target_1509_; uint8_t v___x_1510_; lean_object* v___x_1511_; lean_object* v_snd_1512_; uint8_t v___x_1513_; lean_object* v___x_1514_; lean_object* v_snd_1515_; lean_object* v___x_1516_; lean_object* v_snd_1517_; lean_object* v___x_1518_; 
lean_dec_ref(v_getTokens_1473_);
v_view_1505_ = lean_ctor_get(v_val_1477_, 0);
lean_inc_ref(v_view_1505_);
lean_dec_ref_known(v_val_1477_, 1);
v_opener_1506_ = lean_ctor_get(v_view_1505_, 1);
lean_inc(v_opener_1506_);
v_alt_1507_ = lean_ctor_get(v_view_1505_, 2);
lean_inc(v_alt_1507_);
v_closer_1508_ = lean_ctor_get(v_view_1505_, 3);
lean_inc(v_closer_1508_);
v_target_1509_ = lean_ctor_get(v_view_1505_, 4);
lean_inc_ref(v_target_1509_);
lean_dec_ref(v_view_1505_);
v___x_1510_ = 0;
v___x_1511_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1506_, v___x_1510_, v_a_1475_);
v_snd_1512_ = lean_ctor_get(v___x_1511_, 1);
lean_inc(v_snd_1512_);
lean_dec_ref(v___x_1511_);
v___x_1513_ = 18;
v___x_1514_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_alt_1507_, v___x_1513_, v_snd_1512_);
v_snd_1515_ = lean_ctor_get(v___x_1514_, 1);
lean_inc(v_snd_1515_);
lean_dec_ref(v___x_1514_);
v___x_1516_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1508_, v___x_1510_, v_snd_1515_);
v_snd_1517_ = lean_ctor_get(v___x_1516_, 1);
lean_inc(v_snd_1517_);
lean_dec_ref(v___x_1516_);
v___x_1518_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goTarget(v_target_1509_, v_snd_1517_);
return v___x_1518_;
}
case 7:
{
lean_object* v_view_1519_; lean_object* v_opener_1520_; lean_object* v_name_1521_; lean_object* v_closer_1522_; uint8_t v___x_1523_; lean_object* v___x_1524_; lean_object* v_snd_1525_; uint8_t v___x_1526_; lean_object* v___x_1527_; lean_object* v_snd_1528_; lean_object* v___x_1529_; 
lean_dec_ref(v_getTokens_1473_);
v_view_1519_ = lean_ctor_get(v_val_1477_, 0);
lean_inc_ref(v_view_1519_);
lean_dec_ref_known(v_val_1477_, 1);
v_opener_1520_ = lean_ctor_get(v_view_1519_, 1);
lean_inc(v_opener_1520_);
v_name_1521_ = lean_ctor_get(v_view_1519_, 2);
lean_inc(v_name_1521_);
v_closer_1522_ = lean_ctor_get(v_view_1519_, 3);
lean_inc(v_closer_1522_);
lean_dec_ref(v_view_1519_);
v___x_1523_ = 0;
v___x_1524_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1520_, v___x_1523_, v_a_1475_);
v_snd_1525_ = lean_ctor_get(v___x_1524_, 1);
lean_inc(v_snd_1525_);
lean_dec_ref(v___x_1524_);
v___x_1526_ = 2;
v___x_1527_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1521_, v___x_1526_, v_snd_1525_);
v_snd_1528_ = lean_ctor_get(v___x_1527_, 1);
lean_inc(v_snd_1528_);
lean_dec_ref(v___x_1527_);
v___x_1529_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1522_, v___x_1523_, v_snd_1528_);
return v___x_1529_;
}
case 9:
{
lean_object* v_view_1530_; lean_object* v_braceOpen_1531_; lean_object* v_name_1532_; lean_object* v_args_1533_; lean_object* v_braceClose_1534_; lean_object* v_brackets_1535_; lean_object* v_content_1536_; uint8_t v___x_1537_; lean_object* v___x_1538_; lean_object* v_snd_1539_; uint8_t v___x_1540_; lean_object* v___x_1541_; lean_object* v_snd_1542_; lean_object* v___x_1543_; lean_object* v___y_1545_; size_t v_sz_1562_; size_t v___x_1563_; lean_object* v___x_1564_; lean_object* v_snd_1565_; lean_object* v___x_1566_; 
v_view_1530_ = lean_ctor_get(v_val_1477_, 0);
lean_inc_ref(v_view_1530_);
lean_dec_ref_known(v_val_1477_, 1);
v_braceOpen_1531_ = lean_ctor_get(v_view_1530_, 1);
lean_inc(v_braceOpen_1531_);
v_name_1532_ = lean_ctor_get(v_view_1530_, 2);
lean_inc(v_name_1532_);
v_args_1533_ = lean_ctor_get(v_view_1530_, 3);
lean_inc_ref(v_args_1533_);
v_braceClose_1534_ = lean_ctor_get(v_view_1530_, 4);
lean_inc(v_braceClose_1534_);
v_brackets_1535_ = lean_ctor_get(v_view_1530_, 5);
lean_inc(v_brackets_1535_);
v_content_1536_ = lean_ctor_get(v_view_1530_, 6);
lean_inc_ref(v_content_1536_);
lean_dec_ref(v_view_1530_);
v___x_1537_ = 0;
v___x_1538_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_braceOpen_1531_, v___x_1537_, v_a_1475_);
v_snd_1539_ = lean_ctor_get(v___x_1538_, 1);
lean_inc(v_snd_1539_);
lean_dec_ref(v___x_1538_);
v___x_1540_ = 3;
v___x_1541_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1532_, v___x_1540_, v_snd_1539_);
v_snd_1542_ = lean_ctor_get(v___x_1541_, 1);
lean_inc(v_snd_1542_);
lean_dec_ref(v___x_1541_);
v___x_1543_ = lean_box(0);
v_sz_1562_ = lean_array_size(v_args_1533_);
v___x_1563_ = ((size_t)0ULL);
v___x_1564_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(v_args_1533_, v_sz_1562_, v___x_1563_, v___x_1543_, v_snd_1542_);
lean_dec_ref(v_args_1533_);
v_snd_1565_ = lean_ctor_get(v___x_1564_, 1);
lean_inc(v_snd_1565_);
lean_dec_ref(v___x_1564_);
v___x_1566_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_braceClose_1534_, v___x_1537_, v_snd_1565_);
if (lean_obj_tag(v_brackets_1535_) == 1)
{
lean_object* v_val_1567_; lean_object* v_snd_1568_; lean_object* v_fst_1569_; lean_object* v___x_1570_; lean_object* v_snd_1571_; 
v_val_1567_ = lean_ctor_get(v_brackets_1535_, 0);
v_snd_1568_ = lean_ctor_get(v___x_1566_, 1);
lean_inc(v_snd_1568_);
lean_dec_ref(v___x_1566_);
v_fst_1569_ = lean_ctor_get(v_val_1567_, 0);
lean_inc(v_fst_1569_);
v___x_1570_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_fst_1569_, v___x_1537_, v_snd_1568_);
v_snd_1571_ = lean_ctor_get(v___x_1570_, 1);
lean_inc(v_snd_1571_);
lean_dec_ref(v___x_1570_);
v___y_1545_ = v_snd_1571_;
goto v___jp_1544_;
}
else
{
lean_object* v_snd_1572_; 
v_snd_1572_ = lean_ctor_get(v___x_1566_, 1);
lean_inc(v_snd_1572_);
lean_dec_ref(v___x_1566_);
v___y_1545_ = v_snd_1572_;
goto v___jp_1544_;
}
v___jp_1544_:
{
size_t v_sz_1546_; size_t v___x_1547_; lean_object* v___x_1548_; 
v_sz_1546_ = lean_array_size(v_content_1536_);
v___x_1547_ = ((size_t)0ULL);
v___x_1548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1473_, v_content_1536_, v_sz_1546_, v___x_1547_, v___x_1543_, v___y_1545_);
lean_dec_ref(v_content_1536_);
if (lean_obj_tag(v_brackets_1535_) == 1)
{
lean_object* v_val_1549_; lean_object* v_snd_1550_; lean_object* v_snd_1551_; lean_object* v___x_1552_; 
v_val_1549_ = lean_ctor_get(v_brackets_1535_, 0);
lean_inc(v_val_1549_);
lean_dec_ref_known(v_brackets_1535_, 1);
v_snd_1550_ = lean_ctor_get(v___x_1548_, 1);
lean_inc(v_snd_1550_);
lean_dec_ref(v___x_1548_);
v_snd_1551_ = lean_ctor_get(v_val_1549_, 1);
lean_inc(v_snd_1551_);
lean_dec(v_val_1549_);
v___x_1552_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_snd_1551_, v___x_1537_, v_snd_1550_);
return v___x_1552_;
}
else
{
lean_object* v_snd_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec(v_brackets_1535_);
v_snd_1553_ = lean_ctor_get(v___x_1548_, 1);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; 
v_unused_1561_ = lean_ctor_get(v___x_1548_, 0);
lean_dec(v_unused_1561_);
v___x_1555_ = v___x_1548_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_snd_1553_);
lean_dec(v___x_1548_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1543_);
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1543_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_snd_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
}
default: 
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
lean_dec(v_val_1477_);
lean_dec_ref(v_getTokens_1473_);
v___x_1573_ = lean_box(0);
v___x_1574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
lean_ctor_set(v___x_1574_, 1, v_a_1475_);
return v___x_1574_;
}
}
}
else
{
lean_object* v___x_1575_; 
lean_dec(v___x_1476_);
lean_inc(v_stx_1474_);
v___x_1575_ = l_Lean_Doc_BlockView_of(v_stx_1474_);
if (lean_obj_tag(v___x_1575_) == 1)
{
lean_object* v_val_1576_; 
lean_dec(v_stx_1474_);
v_val_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_val_1576_);
lean_dec_ref_known(v___x_1575_, 1);
switch(lean_obj_tag(v_val_1576_))
{
case 0:
{
lean_object* v_view_1577_; lean_object* v_content_1578_; lean_object* v___x_1579_; size_t v_sz_1580_; size_t v___x_1581_; lean_object* v___x_1582_; lean_object* v_snd_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
v_view_1577_ = lean_ctor_get(v_val_1576_, 0);
lean_inc_ref(v_view_1577_);
lean_dec_ref_known(v_val_1576_, 1);
v_content_1578_ = lean_ctor_get(v_view_1577_, 1);
lean_inc_ref(v_content_1578_);
lean_dec_ref(v_view_1577_);
v___x_1579_ = lean_box(0);
v_sz_1580_ = lean_array_size(v_content_1578_);
v___x_1581_ = ((size_t)0ULL);
v___x_1582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1473_, v_content_1578_, v_sz_1580_, v___x_1581_, v___x_1579_, v_a_1475_);
lean_dec_ref(v_content_1578_);
v_snd_1583_ = lean_ctor_get(v___x_1582_, 1);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1590_ == 0)
{
lean_object* v_unused_1591_; 
v_unused_1591_ = lean_ctor_get(v___x_1582_, 0);
lean_dec(v_unused_1591_);
v___x_1585_ = v___x_1582_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_snd_1583_);
lean_dec(v___x_1582_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 0, v___x_1579_);
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1579_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_snd_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
case 1:
{
lean_object* v_view_1592_; lean_object* v_items_1593_; lean_object* v___x_1594_; size_t v_sz_1595_; size_t v___x_1596_; lean_object* v___x_1597_; lean_object* v_snd_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
v_view_1592_ = lean_ctor_get(v_val_1576_, 0);
lean_inc_ref(v_view_1592_);
lean_dec_ref_known(v_val_1576_, 1);
v_items_1593_ = lean_ctor_get(v_view_1592_, 1);
lean_inc_ref(v_items_1593_);
lean_dec_ref(v_view_1592_);
v___x_1594_ = lean_box(0);
v_sz_1595_ = lean_array_size(v_items_1593_);
v___x_1596_ = ((size_t)0ULL);
v___x_1597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3(v_getTokens_1473_, v_items_1593_, v_sz_1595_, v___x_1596_, v___x_1594_, v_a_1475_);
lean_dec_ref(v_items_1593_);
v_snd_1598_ = lean_ctor_get(v___x_1597_, 1);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1605_ == 0)
{
lean_object* v_unused_1606_; 
v_unused_1606_ = lean_ctor_get(v___x_1597_, 0);
lean_dec(v_unused_1606_);
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_snd_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v___x_1594_);
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1594_);
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
case 2:
{
lean_object* v_view_1607_; lean_object* v_items_1608_; lean_object* v___x_1609_; size_t v_sz_1610_; size_t v___x_1611_; lean_object* v___x_1612_; lean_object* v_snd_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
v_view_1607_ = lean_ctor_get(v_val_1576_, 0);
lean_inc_ref(v_view_1607_);
lean_dec_ref_known(v_val_1576_, 1);
v_items_1608_ = lean_ctor_get(v_view_1607_, 2);
lean_inc_ref(v_items_1608_);
lean_dec_ref(v_view_1607_);
v___x_1609_ = lean_box(0);
v_sz_1610_ = lean_array_size(v_items_1608_);
v___x_1611_ = ((size_t)0ULL);
v___x_1612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__4(v_getTokens_1473_, v_items_1608_, v_sz_1610_, v___x_1611_, v___x_1609_, v_a_1475_);
lean_dec_ref(v_items_1608_);
v_snd_1613_ = lean_ctor_get(v___x_1612_, 1);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1620_ == 0)
{
lean_object* v_unused_1621_; 
v_unused_1621_ = lean_ctor_get(v___x_1612_, 0);
lean_dec(v_unused_1621_);
v___x_1615_ = v___x_1612_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_snd_1613_);
lean_dec(v___x_1612_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 0, v___x_1609_);
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_snd_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
case 3:
{
lean_object* v_view_1622_; lean_object* v_items_1623_; lean_object* v___x_1624_; size_t v_sz_1625_; size_t v___x_1626_; lean_object* v___x_1627_; lean_object* v_snd_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
v_view_1622_ = lean_ctor_get(v_val_1576_, 0);
lean_inc_ref(v_view_1622_);
lean_dec_ref_known(v_val_1576_, 1);
v_items_1623_ = lean_ctor_get(v_view_1622_, 1);
lean_inc_ref(v_items_1623_);
lean_dec_ref(v_view_1622_);
v___x_1624_ = lean_box(0);
v_sz_1625_ = lean_array_size(v_items_1623_);
v___x_1626_ = ((size_t)0ULL);
v___x_1627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__5(v_getTokens_1473_, v_items_1623_, v_sz_1625_, v___x_1626_, v___x_1624_, v_a_1475_);
lean_dec_ref(v_items_1623_);
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
case 4:
{
lean_object* v_view_1637_; lean_object* v_marker_1638_; lean_object* v_content_1639_; uint8_t v___x_1640_; lean_object* v___x_1641_; lean_object* v_snd_1642_; lean_object* v___x_1643_; size_t v_sz_1644_; size_t v___x_1645_; lean_object* v___x_1646_; lean_object* v_snd_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
v_view_1637_ = lean_ctor_get(v_val_1576_, 0);
lean_inc_ref(v_view_1637_);
lean_dec_ref_known(v_val_1576_, 1);
v_marker_1638_ = lean_ctor_get(v_view_1637_, 1);
lean_inc(v_marker_1638_);
v_content_1639_ = lean_ctor_get(v_view_1637_, 2);
lean_inc_ref(v_content_1639_);
lean_dec_ref(v_view_1637_);
v___x_1640_ = 0;
v___x_1641_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_marker_1638_, v___x_1640_, v_a_1475_);
v_snd_1642_ = lean_ctor_get(v___x_1641_, 1);
lean_inc(v_snd_1642_);
lean_dec_ref(v___x_1641_);
v___x_1643_ = lean_box(0);
v_sz_1644_ = lean_array_size(v_content_1639_);
v___x_1645_ = ((size_t)0ULL);
v___x_1646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1473_, v_content_1639_, v_sz_1644_, v___x_1645_, v___x_1643_, v_snd_1642_);
lean_dec_ref(v_content_1639_);
v_snd_1647_ = lean_ctor_get(v___x_1646_, 1);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1654_ == 0)
{
lean_object* v_unused_1655_; 
v_unused_1655_ = lean_ctor_get(v___x_1646_, 0);
lean_dec(v_unused_1655_);
v___x_1649_ = v___x_1646_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_snd_1647_);
lean_dec(v___x_1646_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v___x_1643_);
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1643_);
lean_ctor_set(v_reuseFailAlloc_1653_, 1, v_snd_1647_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
case 5:
{
lean_object* v_view_1656_; lean_object* v_openFence_1657_; lean_object* v_name_x3f_1658_; lean_object* v_args_1659_; lean_object* v_content_1660_; lean_object* v_closeFence_1661_; uint8_t v___x_1662_; lean_object* v___y_1664_; lean_object* v___x_1672_; 
lean_dec_ref(v_getTokens_1473_);
v_view_1656_ = lean_ctor_get(v_val_1576_, 0);
lean_inc_ref(v_view_1656_);
lean_dec_ref_known(v_val_1576_, 1);
v_openFence_1657_ = lean_ctor_get(v_view_1656_, 1);
lean_inc(v_openFence_1657_);
v_name_x3f_1658_ = lean_ctor_get(v_view_1656_, 2);
lean_inc(v_name_x3f_1658_);
v_args_1659_ = lean_ctor_get(v_view_1656_, 3);
lean_inc_ref(v_args_1659_);
v_content_1660_ = lean_ctor_get(v_view_1656_, 4);
lean_inc(v_content_1660_);
v_closeFence_1661_ = lean_ctor_get(v_view_1656_, 5);
lean_inc(v_closeFence_1661_);
lean_dec_ref(v_view_1656_);
v___x_1662_ = 0;
v___x_1672_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_openFence_1657_, v___x_1662_, v_a_1475_);
if (lean_obj_tag(v_name_x3f_1658_) == 1)
{
lean_object* v_snd_1673_; lean_object* v_val_1674_; uint8_t v___x_1675_; lean_object* v___x_1676_; lean_object* v_snd_1677_; lean_object* v___x_1678_; size_t v_sz_1679_; size_t v___x_1680_; lean_object* v___x_1681_; lean_object* v_snd_1682_; 
v_snd_1673_ = lean_ctor_get(v___x_1672_, 1);
lean_inc(v_snd_1673_);
lean_dec_ref(v___x_1672_);
v_val_1674_ = lean_ctor_get(v_name_x3f_1658_, 0);
lean_inc(v_val_1674_);
lean_dec_ref_known(v_name_x3f_1658_, 1);
v___x_1675_ = 3;
v___x_1676_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_val_1674_, v___x_1675_, v_snd_1673_);
v_snd_1677_ = lean_ctor_get(v___x_1676_, 1);
lean_inc(v_snd_1677_);
lean_dec_ref(v___x_1676_);
v___x_1678_ = lean_box(0);
v_sz_1679_ = lean_array_size(v_args_1659_);
v___x_1680_ = ((size_t)0ULL);
v___x_1681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(v_args_1659_, v_sz_1679_, v___x_1680_, v___x_1678_, v_snd_1677_);
lean_dec_ref(v_args_1659_);
v_snd_1682_ = lean_ctor_get(v___x_1681_, 1);
lean_inc(v_snd_1682_);
lean_dec_ref(v___x_1681_);
v___y_1664_ = v_snd_1682_;
goto v___jp_1663_;
}
else
{
lean_object* v_snd_1683_; 
lean_dec_ref(v_args_1659_);
lean_dec(v_name_x3f_1658_);
v_snd_1683_ = lean_ctor_get(v___x_1672_, 1);
lean_inc(v_snd_1683_);
lean_dec_ref(v___x_1672_);
v___y_1664_ = v_snd_1683_;
goto v___jp_1663_;
}
v___jp_1663_:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; size_t v_sz_1667_; size_t v___x_1668_; lean_object* v___x_1669_; lean_object* v_snd_1670_; lean_object* v___x_1671_; 
v___x_1665_ = l_Lean_TSyntax_getVersoCodeBlockLines(v_content_1660_);
lean_dec(v_content_1660_);
v___x_1666_ = lean_box(0);
v_sz_1667_ = lean_array_size(v___x_1665_);
v___x_1668_ = ((size_t)0ULL);
v___x_1669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode_spec__0(v___x_1665_, v_sz_1667_, v___x_1668_, v___x_1666_, v___y_1664_);
lean_dec_ref(v___x_1665_);
v_snd_1670_ = lean_ctor_get(v___x_1669_, 1);
lean_inc(v_snd_1670_);
lean_dec_ref(v___x_1669_);
v___x_1671_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closeFence_1661_, v___x_1662_, v_snd_1670_);
return v___x_1671_;
}
}
case 6:
{
lean_object* v_view_1684_; lean_object* v_opener_1685_; lean_object* v_name_1686_; lean_object* v_args_1687_; lean_object* v_content_1688_; lean_object* v_closer_1689_; uint8_t v___x_1690_; lean_object* v___x_1691_; lean_object* v_snd_1692_; uint8_t v___x_1693_; lean_object* v___x_1694_; lean_object* v_snd_1695_; lean_object* v___x_1696_; size_t v_sz_1697_; size_t v___x_1698_; lean_object* v___x_1699_; lean_object* v_snd_1700_; size_t v_sz_1701_; lean_object* v___x_1702_; lean_object* v_snd_1703_; lean_object* v___x_1704_; 
v_view_1684_ = lean_ctor_get(v_val_1576_, 0);
lean_inc_ref(v_view_1684_);
lean_dec_ref_known(v_val_1576_, 1);
v_opener_1685_ = lean_ctor_get(v_view_1684_, 1);
lean_inc(v_opener_1685_);
v_name_1686_ = lean_ctor_get(v_view_1684_, 2);
lean_inc(v_name_1686_);
v_args_1687_ = lean_ctor_get(v_view_1684_, 3);
lean_inc_ref(v_args_1687_);
v_content_1688_ = lean_ctor_get(v_view_1684_, 4);
lean_inc_ref(v_content_1688_);
v_closer_1689_ = lean_ctor_get(v_view_1684_, 5);
lean_inc(v_closer_1689_);
lean_dec_ref(v_view_1684_);
v___x_1690_ = 0;
v___x_1691_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1685_, v___x_1690_, v_a_1475_);
v_snd_1692_ = lean_ctor_get(v___x_1691_, 1);
lean_inc(v_snd_1692_);
lean_dec_ref(v___x_1691_);
v___x_1693_ = 3;
v___x_1694_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1686_, v___x_1693_, v_snd_1692_);
v_snd_1695_ = lean_ctor_get(v___x_1694_, 1);
lean_inc(v_snd_1695_);
lean_dec_ref(v___x_1694_);
v___x_1696_ = lean_box(0);
v_sz_1697_ = lean_array_size(v_args_1687_);
v___x_1698_ = ((size_t)0ULL);
v___x_1699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(v_args_1687_, v_sz_1697_, v___x_1698_, v___x_1696_, v_snd_1695_);
lean_dec_ref(v_args_1687_);
v_snd_1700_ = lean_ctor_get(v___x_1699_, 1);
lean_inc(v_snd_1700_);
lean_dec_ref(v___x_1699_);
v_sz_1701_ = lean_array_size(v_content_1688_);
v___x_1702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1473_, v_content_1688_, v_sz_1701_, v___x_1698_, v___x_1696_, v_snd_1700_);
lean_dec_ref(v_content_1688_);
v_snd_1703_ = lean_ctor_get(v___x_1702_, 1);
lean_inc(v_snd_1703_);
lean_dec_ref(v___x_1702_);
v___x_1704_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1689_, v___x_1690_, v_snd_1703_);
return v___x_1704_;
}
case 7:
{
lean_object* v_view_1705_; lean_object* v_braceOpen_1706_; lean_object* v_name_1707_; lean_object* v_args_1708_; lean_object* v_braceClose_1709_; uint8_t v___x_1710_; lean_object* v___x_1711_; lean_object* v_snd_1712_; uint8_t v___x_1713_; lean_object* v___x_1714_; lean_object* v_snd_1715_; lean_object* v___x_1716_; size_t v_sz_1717_; size_t v___x_1718_; lean_object* v___x_1719_; lean_object* v_snd_1720_; lean_object* v___x_1721_; 
lean_dec_ref(v_getTokens_1473_);
v_view_1705_ = lean_ctor_get(v_val_1576_, 0);
lean_inc_ref(v_view_1705_);
lean_dec_ref_known(v_val_1576_, 1);
v_braceOpen_1706_ = lean_ctor_get(v_view_1705_, 1);
lean_inc(v_braceOpen_1706_);
v_name_1707_ = lean_ctor_get(v_view_1705_, 2);
lean_inc(v_name_1707_);
v_args_1708_ = lean_ctor_get(v_view_1705_, 3);
lean_inc_ref(v_args_1708_);
v_braceClose_1709_ = lean_ctor_get(v_view_1705_, 4);
lean_inc(v_braceClose_1709_);
lean_dec_ref(v_view_1705_);
v___x_1710_ = 0;
v___x_1711_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_braceOpen_1706_, v___x_1710_, v_a_1475_);
v_snd_1712_ = lean_ctor_get(v___x_1711_, 1);
lean_inc(v_snd_1712_);
lean_dec_ref(v___x_1711_);
v___x_1713_ = 3;
v___x_1714_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1707_, v___x_1713_, v_snd_1712_);
v_snd_1715_ = lean_ctor_get(v___x_1714_, 1);
lean_inc(v_snd_1715_);
lean_dec_ref(v___x_1714_);
v___x_1716_ = lean_box(0);
v_sz_1717_ = lean_array_size(v_args_1708_);
v___x_1718_ = ((size_t)0ULL);
v___x_1719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(v_args_1708_, v_sz_1717_, v___x_1718_, v___x_1716_, v_snd_1715_);
lean_dec_ref(v_args_1708_);
v_snd_1720_ = lean_ctor_get(v___x_1719_, 1);
lean_inc(v_snd_1720_);
lean_dec_ref(v___x_1719_);
v___x_1721_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_braceClose_1709_, v___x_1710_, v_snd_1720_);
return v___x_1721_;
}
case 8:
{
lean_object* v_view_1722_; lean_object* v_marker_1723_; lean_object* v_content_1724_; uint8_t v___x_1725_; lean_object* v___x_1726_; lean_object* v_snd_1727_; lean_object* v___x_1728_; size_t v_sz_1729_; size_t v___x_1730_; lean_object* v___x_1731_; lean_object* v_snd_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
v_view_1722_ = lean_ctor_get(v_val_1576_, 0);
lean_inc_ref(v_view_1722_);
lean_dec_ref_known(v_val_1576_, 1);
v_marker_1723_ = lean_ctor_get(v_view_1722_, 1);
lean_inc(v_marker_1723_);
v_content_1724_ = lean_ctor_get(v_view_1722_, 3);
lean_inc_ref(v_content_1724_);
lean_dec_ref(v_view_1722_);
v___x_1725_ = 0;
v___x_1726_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_marker_1723_, v___x_1725_, v_a_1475_);
v_snd_1727_ = lean_ctor_get(v___x_1726_, 1);
lean_inc(v_snd_1727_);
lean_dec_ref(v___x_1726_);
v___x_1728_ = lean_box(0);
v_sz_1729_ = lean_array_size(v_content_1724_);
v___x_1730_ = ((size_t)0ULL);
v___x_1731_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1473_, v_content_1724_, v_sz_1729_, v___x_1730_, v___x_1728_, v_snd_1727_);
lean_dec_ref(v_content_1724_);
v_snd_1732_ = lean_ctor_get(v___x_1731_, 1);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1739_ == 0)
{
lean_object* v_unused_1740_; 
v_unused_1740_ = lean_ctor_get(v___x_1731_, 0);
lean_dec(v_unused_1740_);
v___x_1734_ = v___x_1731_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_snd_1732_);
lean_dec(v___x_1731_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 0, v___x_1728_);
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1728_);
lean_ctor_set(v_reuseFailAlloc_1738_, 1, v_snd_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
case 9:
{
lean_object* v_view_1741_; lean_object* v_opener_1742_; lean_object* v_name_1743_; lean_object* v_closer_1744_; lean_object* v_url_1745_; uint8_t v___x_1746_; lean_object* v___x_1747_; lean_object* v_snd_1748_; uint8_t v___x_1749_; lean_object* v___x_1750_; lean_object* v_snd_1751_; lean_object* v___x_1752_; lean_object* v_snd_1753_; uint8_t v___x_1754_; lean_object* v___x_1755_; 
lean_dec_ref(v_getTokens_1473_);
v_view_1741_ = lean_ctor_get(v_val_1576_, 0);
lean_inc_ref(v_view_1741_);
lean_dec_ref_known(v_val_1576_, 1);
v_opener_1742_ = lean_ctor_get(v_view_1741_, 1);
lean_inc(v_opener_1742_);
v_name_1743_ = lean_ctor_get(v_view_1741_, 2);
lean_inc(v_name_1743_);
v_closer_1744_ = lean_ctor_get(v_view_1741_, 3);
lean_inc(v_closer_1744_);
v_url_1745_ = lean_ctor_get(v_view_1741_, 4);
lean_inc(v_url_1745_);
lean_dec_ref(v_view_1741_);
v___x_1746_ = 0;
v___x_1747_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1742_, v___x_1746_, v_a_1475_);
v_snd_1748_ = lean_ctor_get(v___x_1747_, 1);
lean_inc(v_snd_1748_);
lean_dec_ref(v___x_1747_);
v___x_1749_ = 2;
v___x_1750_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1743_, v___x_1749_, v_snd_1748_);
v_snd_1751_ = lean_ctor_get(v___x_1750_, 1);
lean_inc(v_snd_1751_);
lean_dec_ref(v___x_1750_);
v___x_1752_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1744_, v___x_1746_, v_snd_1751_);
v_snd_1753_ = lean_ctor_get(v___x_1752_, 1);
lean_inc(v_snd_1753_);
lean_dec_ref(v___x_1752_);
v___x_1754_ = 18;
v___x_1755_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_url_1745_, v___x_1754_, v_snd_1753_);
return v___x_1755_;
}
case 10:
{
lean_object* v_view_1756_; lean_object* v_opener_1757_; lean_object* v_name_1758_; lean_object* v_closer_1759_; lean_object* v_content_1760_; uint8_t v___x_1761_; lean_object* v___x_1762_; lean_object* v_snd_1763_; uint8_t v___x_1764_; lean_object* v___x_1765_; lean_object* v_snd_1766_; lean_object* v___x_1767_; lean_object* v_snd_1768_; lean_object* v___x_1769_; size_t v_sz_1770_; size_t v___x_1771_; lean_object* v___x_1772_; lean_object* v_snd_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
v_view_1756_ = lean_ctor_get(v_val_1576_, 0);
lean_inc_ref(v_view_1756_);
lean_dec_ref_known(v_val_1576_, 1);
v_opener_1757_ = lean_ctor_get(v_view_1756_, 1);
lean_inc(v_opener_1757_);
v_name_1758_ = lean_ctor_get(v_view_1756_, 2);
lean_inc(v_name_1758_);
v_closer_1759_ = lean_ctor_get(v_view_1756_, 3);
lean_inc(v_closer_1759_);
v_content_1760_ = lean_ctor_get(v_view_1756_, 4);
lean_inc_ref(v_content_1760_);
lean_dec_ref(v_view_1756_);
v___x_1761_ = 0;
v___x_1762_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1757_, v___x_1761_, v_a_1475_);
v_snd_1763_ = lean_ctor_get(v___x_1762_, 1);
lean_inc(v_snd_1763_);
lean_dec_ref(v___x_1762_);
v___x_1764_ = 2;
v___x_1765_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1758_, v___x_1764_, v_snd_1763_);
v_snd_1766_ = lean_ctor_get(v___x_1765_, 1);
lean_inc(v_snd_1766_);
lean_dec_ref(v___x_1765_);
v___x_1767_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1759_, v___x_1761_, v_snd_1766_);
v_snd_1768_ = lean_ctor_get(v___x_1767_, 1);
lean_inc(v_snd_1768_);
lean_dec_ref(v___x_1767_);
v___x_1769_ = lean_box(0);
v_sz_1770_ = lean_array_size(v_content_1760_);
v___x_1771_ = ((size_t)0ULL);
v___x_1772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1473_, v_content_1760_, v_sz_1770_, v___x_1771_, v___x_1769_, v_snd_1768_);
lean_dec_ref(v_content_1760_);
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
default: 
{
lean_object* v_view_1782_; lean_object* v_opener_1783_; lean_object* v_contents_1784_; lean_object* v_closer_1785_; uint8_t v___x_1786_; lean_object* v___x_1787_; lean_object* v_snd_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v_view_1782_ = lean_ctor_get(v_val_1576_, 0);
lean_inc_ref(v_view_1782_);
lean_dec_ref_known(v_val_1576_, 1);
v_opener_1783_ = lean_ctor_get(v_view_1782_, 1);
lean_inc(v_opener_1783_);
v_contents_1784_ = lean_ctor_get(v_view_1782_, 2);
lean_inc(v_contents_1784_);
v_closer_1785_ = lean_ctor_get(v_view_1782_, 3);
lean_inc(v_closer_1785_);
lean_dec_ref(v_view_1782_);
v___x_1786_ = 0;
v___x_1787_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1783_, v___x_1786_, v_a_1475_);
v_snd_1788_ = lean_ctor_get(v___x_1787_, 1);
lean_inc(v_snd_1788_);
lean_dec_ref(v___x_1787_);
v___x_1789_ = lean_apply_1(v_getTokens_1473_, v_contents_1784_);
v___x_1790_ = l_Array_append___redArg(v_snd_1788_, v___x_1789_);
lean_dec_ref(v___x_1789_);
v___x_1791_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1785_, v___x_1786_, v___x_1790_);
return v___x_1791_;
}
}
}
else
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
lean_dec(v___x_1575_);
v___x_1792_ = l_Lean_Syntax_getArgs(v_stx_1474_);
lean_dec(v_stx_1474_);
v___x_1793_ = lean_unsigned_to_nat(0u);
v___x_1794_ = lean_array_get_size(v___x_1792_);
v___x_1795_ = lean_box(0);
v___x_1796_ = lean_nat_dec_lt(v___x_1793_, v___x_1794_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; 
lean_dec_ref(v___x_1792_);
lean_dec_ref(v_getTokens_1473_);
v___x_1797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1795_);
lean_ctor_set(v___x_1797_, 1, v_a_1475_);
return v___x_1797_;
}
else
{
size_t v___x_1798_; size_t v___x_1799_; lean_object* v___x_1800_; 
v___x_1798_ = ((size_t)0ULL);
v___x_1799_ = lean_usize_of_nat(v___x_1794_);
v___x_1800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6(v_getTokens_1473_, v___x_1792_, v___x_1798_, v___x_1799_, v___x_1795_, v_a_1475_);
lean_dec_ref(v___x_1792_);
return v___x_1800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(lean_object* v_getTokens_1801_, lean_object* v_as_1802_, size_t v_sz_1803_, size_t v_i_1804_, lean_object* v_b_1805_, lean_object* v___y_1806_){
_start:
{
uint8_t v___x_1807_; 
v___x_1807_ = lean_usize_dec_lt(v_i_1804_, v_sz_1803_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1808_; 
lean_dec_ref(v_getTokens_1801_);
v___x_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1808_, 0, v_b_1805_);
lean_ctor_set(v___x_1808_, 1, v___y_1806_);
return v___x_1808_;
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1810_; lean_object* v_snd_1811_; lean_object* v___x_1812_; size_t v___x_1813_; size_t v___x_1814_; 
v_a_1809_ = lean_array_uget_borrowed(v_as_1802_, v_i_1804_);
lean_inc(v_a_1809_);
lean_inc_ref(v_getTokens_1801_);
v___x_1810_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_getTokens_1801_, v_a_1809_, v___y_1806_);
v_snd_1811_ = lean_ctor_get(v___x_1810_, 1);
lean_inc(v_snd_1811_);
lean_dec_ref(v___x_1810_);
v___x_1812_ = lean_box(0);
v___x_1813_ = ((size_t)1ULL);
v___x_1814_ = lean_usize_add(v_i_1804_, v___x_1813_);
v_i_1804_ = v___x_1814_;
v_b_1805_ = v___x_1812_;
v___y_1806_ = v_snd_1811_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDelimited(lean_object* v_getTokens_1816_, lean_object* v_opener_1817_, lean_object* v_closer_1818_, lean_object* v_content_1819_, lean_object* v_a_1820_){
_start:
{
uint8_t v___x_1821_; lean_object* v___x_1822_; lean_object* v_snd_1823_; lean_object* v___x_1824_; size_t v_sz_1825_; size_t v___x_1826_; lean_object* v___x_1827_; lean_object* v_snd_1828_; lean_object* v___x_1829_; 
v___x_1821_ = 0;
v___x_1822_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1817_, v___x_1821_, v_a_1820_);
v_snd_1823_ = lean_ctor_get(v___x_1822_, 1);
lean_inc(v_snd_1823_);
lean_dec_ref(v___x_1822_);
v___x_1824_ = lean_box(0);
v_sz_1825_ = lean_array_size(v_content_1819_);
v___x_1826_ = ((size_t)0ULL);
v___x_1827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1816_, v_content_1819_, v_sz_1825_, v___x_1826_, v___x_1824_, v_snd_1823_);
v_snd_1828_ = lean_ctor_get(v___x_1827_, 1);
lean_inc(v_snd_1828_);
lean_dec_ref(v___x_1827_);
v___x_1829_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1818_, v___x_1821_, v_snd_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDelimited___boxed(lean_object* v_getTokens_1830_, lean_object* v_opener_1831_, lean_object* v_closer_1832_, lean_object* v_content_1833_, lean_object* v_a_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDelimited(v_getTokens_1830_, v_opener_1831_, v_closer_1832_, v_content_1833_, v_a_1834_);
lean_dec_ref(v_content_1833_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem___boxed(lean_object* v_getTokens_1836_, lean_object* v_marker_1837_, lean_object* v_contents_1838_, lean_object* v_a_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem(v_getTokens_1836_, v_marker_1837_, v_contents_1838_, v_a_1839_);
lean_dec_ref(v_contents_1838_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6___boxed(lean_object* v_getTokens_1841_, lean_object* v_as_1842_, lean_object* v_i_1843_, lean_object* v_stop_1844_, lean_object* v_b_1845_, lean_object* v___y_1846_){
_start:
{
size_t v_i_boxed_1847_; size_t v_stop_boxed_1848_; lean_object* v_res_1849_; 
v_i_boxed_1847_ = lean_unbox_usize(v_i_1843_);
lean_dec(v_i_1843_);
v_stop_boxed_1848_ = lean_unbox_usize(v_stop_1844_);
lean_dec(v_stop_1844_);
v_res_1849_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6(v_getTokens_1841_, v_as_1842_, v_i_boxed_1847_, v_stop_boxed_1848_, v_b_1845_, v___y_1846_);
lean_dec_ref(v_as_1842_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__5___boxed(lean_object* v_getTokens_1850_, lean_object* v_as_1851_, lean_object* v_sz_1852_, lean_object* v_i_1853_, lean_object* v_b_1854_, lean_object* v___y_1855_){
_start:
{
size_t v_sz_boxed_1856_; size_t v_i_boxed_1857_; lean_object* v_res_1858_; 
v_sz_boxed_1856_ = lean_unbox_usize(v_sz_1852_);
lean_dec(v_sz_1852_);
v_i_boxed_1857_ = lean_unbox_usize(v_i_1853_);
lean_dec(v_i_1853_);
v_res_1858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__5(v_getTokens_1850_, v_as_1851_, v_sz_boxed_1856_, v_i_boxed_1857_, v_b_1854_, v___y_1855_);
lean_dec_ref(v_as_1851_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0___boxed(lean_object* v_getTokens_1859_, lean_object* v_as_1860_, lean_object* v_sz_1861_, lean_object* v_i_1862_, lean_object* v_b_1863_, lean_object* v___y_1864_){
_start:
{
size_t v_sz_boxed_1865_; size_t v_i_boxed_1866_; lean_object* v_res_1867_; 
v_sz_boxed_1865_ = lean_unbox_usize(v_sz_1861_);
lean_dec(v_sz_1861_);
v_i_boxed_1866_ = lean_unbox_usize(v_i_1862_);
lean_dec(v_i_1862_);
v_res_1867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1859_, v_as_1860_, v_sz_boxed_1865_, v_i_boxed_1866_, v_b_1863_, v___y_1864_);
lean_dec_ref(v_as_1860_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3___boxed(lean_object* v_getTokens_1868_, lean_object* v_as_1869_, lean_object* v_sz_1870_, lean_object* v_i_1871_, lean_object* v_b_1872_, lean_object* v___y_1873_){
_start:
{
size_t v_sz_boxed_1874_; size_t v_i_boxed_1875_; lean_object* v_res_1876_; 
v_sz_boxed_1874_ = lean_unbox_usize(v_sz_1870_);
lean_dec(v_sz_1870_);
v_i_boxed_1875_ = lean_unbox_usize(v_i_1871_);
lean_dec(v_i_1871_);
v_res_1876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3(v_getTokens_1868_, v_as_1869_, v_sz_boxed_1874_, v_i_boxed_1875_, v_b_1872_, v___y_1873_);
lean_dec_ref(v_as_1869_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__4___boxed(lean_object* v_getTokens_1877_, lean_object* v_as_1878_, lean_object* v_sz_1879_, lean_object* v_i_1880_, lean_object* v_b_1881_, lean_object* v___y_1882_){
_start:
{
size_t v_sz_boxed_1883_; size_t v_i_boxed_1884_; lean_object* v_res_1885_; 
v_sz_boxed_1883_ = lean_unbox_usize(v_sz_1879_);
lean_dec(v_sz_1879_);
v_i_boxed_1884_ = lean_unbox_usize(v_i_1880_);
lean_dec(v_i_1880_);
v_res_1885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__4(v_getTokens_1877_, v_as_1878_, v_sz_boxed_1883_, v_i_boxed_1884_, v_b_1881_, v___y_1882_);
lean_dec_ref(v_as_1878_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(lean_object* v_stx_1888_, lean_object* v_getTokens_1889_){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v_snd_1892_; 
v___x_1890_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
v___x_1891_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_getTokens_1889_, v_stx_1888_, v___x_1890_);
v_snd_1892_ = lean_ctor_get(v___x_1891_, 1);
lean_inc(v_snd_1892_);
lean_dec_ref(v___x_1891_);
return v_snd_1892_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(lean_object* v_s_1893_){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; uint8_t v_decide_1896_; 
v___x_1894_ = lean_unsigned_to_nat(0u);
v___x_1895_ = lean_string_utf8_byte_size(v_s_1893_);
v_decide_1896_ = lean_nat_dec_eq(v___x_1894_, v___x_1895_);
if (v_decide_1896_ == 0)
{
uint32_t v___x_1897_; uint32_t v___x_1898_; uint8_t v___x_1899_; 
v___x_1897_ = 35;
v___x_1898_ = lean_string_utf8_get_fast(v_s_1893_, v___x_1894_);
v___x_1899_ = lean_uint32_dec_eq(v___x_1898_, v___x_1897_);
if (v___x_1899_ == 0)
{
lean_object* v___x_1900_; 
lean_dec_ref(v_s_1893_);
v___x_1900_ = lean_box(0);
return v___x_1900_;
}
else
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1901_ = lean_string_utf8_next_fast(v_s_1893_, v___x_1894_);
v___x_1902_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1902_, 0, v_s_1893_);
lean_ctor_set(v___x_1902_, 1, v___x_1901_);
lean_ctor_set(v___x_1902_, 2, v___x_1895_);
v___x_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
return v___x_1903_;
}
}
else
{
lean_object* v___x_1904_; 
lean_dec_ref(v_s_1893_);
v___x_1904_ = lean_box(0);
return v___x_1904_;
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(lean_object* v_s_1905_, uint32_t v_pat_1906_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v_s_1905_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___boxed(lean_object* v_s_1908_, lean_object* v_pat_1909_){
_start:
{
uint32_t v_pat_boxed_1910_; lean_object* v_res_1911_; 
v_pat_boxed_1910_ = lean_unbox_uint32(v_pat_1909_);
lean_dec(v_pat_1909_);
v_res_1911_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_s_1908_, v_pat_boxed_1910_);
return v_res_1911_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(lean_object* v_a_1912_, lean_object* v_as_1913_, size_t v_i_1914_, size_t v_stop_1915_){
_start:
{
uint8_t v___x_1916_; 
v___x_1916_ = lean_usize_dec_eq(v_i_1914_, v_stop_1915_);
if (v___x_1916_ == 0)
{
lean_object* v___x_1917_; uint8_t v___x_1918_; 
v___x_1917_ = lean_array_uget_borrowed(v_as_1913_, v_i_1914_);
v___x_1918_ = lean_name_eq(v_a_1912_, v___x_1917_);
if (v___x_1918_ == 0)
{
size_t v___x_1919_; size_t v___x_1920_; 
v___x_1919_ = ((size_t)1ULL);
v___x_1920_ = lean_usize_add(v_i_1914_, v___x_1919_);
v_i_1914_ = v___x_1920_;
goto _start;
}
else
{
return v___x_1918_;
}
}
else
{
uint8_t v___x_1922_; 
v___x_1922_ = 0;
return v___x_1922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0___boxed(lean_object* v_a_1923_, lean_object* v_as_1924_, lean_object* v_i_1925_, lean_object* v_stop_1926_){
_start:
{
size_t v_i_boxed_1927_; size_t v_stop_boxed_1928_; uint8_t v_res_1929_; lean_object* v_r_1930_; 
v_i_boxed_1927_ = lean_unbox_usize(v_i_1925_);
lean_dec(v_i_1925_);
v_stop_boxed_1928_ = lean_unbox_usize(v_stop_1926_);
lean_dec(v_stop_1926_);
v_res_1929_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(v_a_1923_, v_as_1924_, v_i_boxed_1927_, v_stop_boxed_1928_);
lean_dec_ref(v_as_1924_);
lean_dec(v_a_1923_);
v_r_1930_ = lean_box(v_res_1929_);
return v_r_1930_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(lean_object* v_as_1931_, lean_object* v_a_1932_){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; uint8_t v___x_1935_; 
v___x_1933_ = lean_unsigned_to_nat(0u);
v___x_1934_ = lean_array_get_size(v_as_1931_);
v___x_1935_ = lean_nat_dec_lt(v___x_1933_, v___x_1934_);
if (v___x_1935_ == 0)
{
return v___x_1935_;
}
else
{
size_t v___x_1936_; size_t v___x_1937_; uint8_t v___x_1938_; 
v___x_1936_ = ((size_t)0ULL);
v___x_1937_ = lean_usize_of_nat(v___x_1934_);
v___x_1938_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(v_a_1932_, v_as_1931_, v___x_1936_, v___x_1937_);
return v___x_1938_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0___boxed(lean_object* v_as_1939_, lean_object* v_a_1940_){
_start:
{
uint8_t v_res_1941_; lean_object* v_r_1942_; 
v_res_1941_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v_as_1939_, v_a_1940_);
lean_dec(v_a_1940_);
lean_dec_ref(v_as_1939_);
v_r_1942_ = lean_box(v_res_1941_);
return v_r_1942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(lean_object* v_as_1943_, size_t v_i_1944_, size_t v_stop_1945_, lean_object* v_b_1946_){
_start:
{
uint8_t v___x_1947_; 
v___x_1947_ = lean_usize_dec_eq(v_i_1944_, v_stop_1945_);
if (v___x_1947_ == 0)
{
lean_object* v___x_1948_; lean_object* v___x_1949_; size_t v___x_1950_; size_t v___x_1951_; 
v___x_1948_ = lean_array_uget_borrowed(v_as_1943_, v_i_1944_);
v___x_1949_ = l_Array_append___redArg(v_b_1946_, v___x_1948_);
v___x_1950_ = ((size_t)1ULL);
v___x_1951_ = lean_usize_add(v_i_1944_, v___x_1950_);
v_i_1944_ = v___x_1951_;
v_b_1946_ = v___x_1949_;
goto _start;
}
else
{
return v_b_1946_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4___boxed(lean_object* v_as_1953_, lean_object* v_i_1954_, lean_object* v_stop_1955_, lean_object* v_b_1956_){
_start:
{
size_t v_i_boxed_1957_; size_t v_stop_boxed_1958_; lean_object* v_res_1959_; 
v_i_boxed_1957_ = lean_unbox_usize(v_i_1954_);
lean_dec(v_i_1954_);
v_stop_boxed_1958_ = lean_unbox_usize(v_stop_1955_);
lean_dec(v_stop_1955_);
v_res_1959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v_as_1953_, v_i_boxed_1957_, v_stop_boxed_1958_, v_b_1956_);
lean_dec_ref(v_as_1953_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(lean_object* v_t_1960_, lean_object* v_k_1961_, lean_object* v_fallback_1962_){
_start:
{
if (lean_obj_tag(v_t_1960_) == 0)
{
lean_object* v_k_1963_; lean_object* v_v_1964_; lean_object* v_l_1965_; lean_object* v_r_1966_; uint8_t v___x_1967_; 
v_k_1963_ = lean_ctor_get(v_t_1960_, 1);
v_v_1964_ = lean_ctor_get(v_t_1960_, 2);
v_l_1965_ = lean_ctor_get(v_t_1960_, 3);
v_r_1966_ = lean_ctor_get(v_t_1960_, 4);
v___x_1967_ = lean_string_compare(v_k_1961_, v_k_1963_);
switch(v___x_1967_)
{
case 0:
{
v_t_1960_ = v_l_1965_;
goto _start;
}
case 1:
{
lean_inc(v_v_1964_);
return v_v_1964_;
}
default: 
{
v_t_1960_ = v_r_1966_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_1962_);
return v_fallback_1962_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg___boxed(lean_object* v_t_1970_, lean_object* v_k_1971_, lean_object* v_fallback_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v_t_1970_, v_k_1971_, v_fallback_1972_);
lean_dec(v_fallback_1972_);
lean_dec_ref(v_k_1971_);
lean_dec(v_t_1970_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(lean_object* v_text_2000_, lean_object* v_x_2001_){
_start:
{
lean_object* v___y_2003_; lean_object* v___y_2004_; uint8_t v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; uint8_t v___y_2017_; uint8_t v___y_2019_; uint32_t v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; uint8_t v___y_2027_; uint32_t v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2047_; lean_object* v___y_2048_; uint8_t v___y_2049_; uint8_t v___y_2050_; lean_object* v___y_2052_; uint32_t v___y_2053_; lean_object* v___y_2054_; uint8_t v___y_2055_; lean_object* v___y_2060_; uint32_t v___y_2061_; lean_object* v___y_2062_; uint8_t v___y_2063_; lean_object* v___y_2069_; lean_object* v___y_2070_; uint8_t v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; uint8_t v___y_2083_; uint32_t v___y_2085_; uint8_t v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; uint32_t v___y_2093_; uint8_t v___y_2094_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2113_; lean_object* v___y_2114_; uint8_t v___y_2115_; uint8_t v___y_2116_; lean_object* v___y_2118_; lean_object* v___y_2119_; uint32_t v___y_2120_; uint8_t v___y_2121_; lean_object* v___y_2126_; lean_object* v___y_2127_; uint32_t v___y_2128_; uint8_t v___y_2129_; lean_object* v___y_2135_; lean_object* v___y_2136_; uint8_t v___y_2146_; lean_object* v___y_2147_; lean_object* v___y_2148_; uint8_t v___y_2149_; uint8_t v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; uint32_t v___y_2154_; uint8_t v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; uint32_t v___y_2162_; lean_object* v___x_2167_; uint8_t v___x_2168_; 
v___x_2167_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1));
lean_inc(v_x_2001_);
v___x_2168_ = l_Lean_Syntax_isOfKind(v_x_2001_, v___x_2167_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; uint8_t v___x_2170_; 
v___x_2169_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3));
lean_inc(v_x_2001_);
v___x_2170_ = l_Lean_Syntax_isOfKind(v_x_2001_, v___x_2169_);
if (v___x_2170_ == 0)
{
lean_object* v___x_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2171_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2001_);
v___x_2172_ = l_Lean_Syntax_getKind(v_x_2001_);
v___x_2173_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2171_, v___x_2172_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; uint8_t v___x_2175_; lean_object* v___y_2177_; lean_object* v___y_2178_; uint8_t v___y_2179_; lean_object* v___y_2194_; uint32_t v___y_2195_; lean_object* v___y_2196_; lean_object* v___y_2201_; uint32_t v___y_2202_; lean_object* v___y_2203_; lean_object* v___y_2209_; 
v___x_2174_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2175_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2174_, v___x_2172_);
lean_dec(v___x_2172_);
if (v___x_2175_ == 0)
{
lean_object* v___x_2224_; uint8_t v___x_2225_; 
v___x_2224_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2001_);
v___x_2225_ = l_Lean_Syntax_isOfKind(v_x_2001_, v___x_2224_);
if (v___x_2225_ == 0)
{
lean_object* v___x_2226_; size_t v_sz_2227_; size_t v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; uint8_t v___x_2233_; 
v___x_2226_ = l_Lean_Syntax_getArgs(v_x_2001_);
v_sz_2227_ = lean_array_size(v___x_2226_);
v___x_2228_ = ((size_t)0ULL);
v___x_2229_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2000_, v_sz_2227_, v___x_2228_, v___x_2226_);
v___x_2230_ = lean_unsigned_to_nat(0u);
v___x_2231_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2232_ = lean_array_get_size(v___x_2229_);
v___x_2233_ = lean_nat_dec_lt(v___x_2230_, v___x_2232_);
if (v___x_2233_ == 0)
{
lean_dec_ref(v___x_2229_);
v___y_2209_ = v___x_2231_;
goto v___jp_2208_;
}
else
{
size_t v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = lean_usize_of_nat(v___x_2232_);
v___x_2235_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2229_, v___x_2228_, v___x_2234_, v___x_2231_);
lean_dec_ref(v___x_2229_);
v___y_2209_ = v___x_2235_;
goto v___jp_2208_;
}
}
else
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2236_ = lean_unsigned_to_nat(0u);
v___x_2237_ = l_Lean_Syntax_getArg(v_x_2001_, v___x_2236_);
v___x_2238_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2000_, v___x_2237_);
v___y_2209_ = v___x_2238_;
goto v___jp_2208_;
}
}
else
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; uint8_t v___x_2242_; 
v___x_2239_ = lean_unsigned_to_nat(1u);
v___x_2240_ = l_Lean_Syntax_getArg(v_x_2001_, v___x_2239_);
lean_dec(v_x_2001_);
v___x_2241_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v___x_2240_);
v___x_2242_ = l_Lean_Syntax_isOfKind(v___x_2240_, v___x_2241_);
if (v___x_2242_ == 0)
{
lean_object* v___x_2243_; 
lean_dec(v___x_2240_);
lean_dec_ref(v_text_2000_);
v___x_2243_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2243_;
}
else
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2244_, 0, v_text_2000_);
v___x_2245_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v___x_2240_, v___x_2244_);
return v___x_2245_;
}
}
v___jp_2176_:
{
lean_object* v___x_2180_; 
lean_inc_ref(v___y_2178_);
v___x_2180_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2178_);
if (lean_obj_tag(v___x_2180_) == 0)
{
v___y_2014_ = v___y_2179_;
v___y_2015_ = v___y_2177_;
v___y_2016_ = v___y_2178_;
v___y_2017_ = v___x_2175_;
goto v___jp_2013_;
}
else
{
lean_object* v_val_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v_val_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_val_2181_);
lean_dec_ref_known(v___x_2180_, 1);
v___x_2182_ = lean_unsigned_to_nat(0u);
v___x_2183_ = l_String_Slice_Pos_get_x3f(v_val_2181_, v___x_2182_);
lean_dec(v_val_2181_);
if (lean_obj_tag(v___x_2183_) == 0)
{
v___y_2014_ = v___y_2179_;
v___y_2015_ = v___y_2177_;
v___y_2016_ = v___y_2178_;
v___y_2017_ = v___x_2175_;
goto v___jp_2013_;
}
else
{
lean_object* v_val_2184_; uint32_t v___x_2185_; uint32_t v___x_2186_; uint8_t v___x_2187_; 
v_val_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_val_2184_);
lean_dec_ref_known(v___x_2183_, 1);
v___x_2185_ = 65;
v___x_2186_ = lean_unbox_uint32(v_val_2184_);
v___x_2187_ = lean_uint32_dec_le(v___x_2185_, v___x_2186_);
if (v___x_2187_ == 0)
{
uint32_t v___x_2188_; 
v___x_2188_ = lean_unbox_uint32(v_val_2184_);
lean_dec(v_val_2184_);
v___y_2027_ = v___y_2179_;
v___y_2028_ = v___x_2188_;
v___y_2029_ = v___y_2177_;
v___y_2030_ = v___y_2178_;
goto v___jp_2026_;
}
else
{
uint32_t v___x_2189_; uint32_t v___x_2190_; uint8_t v___x_2191_; 
v___x_2189_ = 90;
v___x_2190_ = lean_unbox_uint32(v_val_2184_);
v___x_2191_ = lean_uint32_dec_le(v___x_2190_, v___x_2189_);
if (v___x_2191_ == 0)
{
uint32_t v___x_2192_; 
v___x_2192_ = lean_unbox_uint32(v_val_2184_);
lean_dec(v_val_2184_);
v___y_2027_ = v___y_2179_;
v___y_2028_ = v___x_2192_;
v___y_2029_ = v___y_2177_;
v___y_2030_ = v___y_2178_;
goto v___jp_2026_;
}
else
{
lean_dec(v_val_2184_);
v___y_2014_ = v___y_2179_;
v___y_2015_ = v___y_2177_;
v___y_2016_ = v___y_2178_;
v___y_2017_ = v___x_2191_;
goto v___jp_2013_;
}
}
}
}
}
v___jp_2193_:
{
uint32_t v___x_2197_; uint8_t v___x_2198_; 
v___x_2197_ = 95;
v___x_2198_ = lean_uint32_dec_eq(v___y_2195_, v___x_2197_);
if (v___x_2198_ == 0)
{
uint8_t v___x_2199_; 
v___x_2199_ = l_Lean_isLetterLike(v___y_2195_);
v___y_2177_ = v___y_2194_;
v___y_2178_ = v___y_2196_;
v___y_2179_ = v___x_2199_;
goto v___jp_2176_;
}
else
{
v___y_2177_ = v___y_2194_;
v___y_2178_ = v___y_2196_;
v___y_2179_ = v___x_2198_;
goto v___jp_2176_;
}
}
v___jp_2200_:
{
uint32_t v___x_2204_; uint8_t v___x_2205_; 
v___x_2204_ = 97;
v___x_2205_ = lean_uint32_dec_le(v___x_2204_, v___y_2202_);
if (v___x_2205_ == 0)
{
v___y_2194_ = v___y_2201_;
v___y_2195_ = v___y_2202_;
v___y_2196_ = v___y_2203_;
goto v___jp_2193_;
}
else
{
uint32_t v___x_2206_; uint8_t v___x_2207_; 
v___x_2206_ = 122;
v___x_2207_ = lean_uint32_dec_le(v___y_2202_, v___x_2206_);
if (v___x_2207_ == 0)
{
v___y_2194_ = v___y_2201_;
v___y_2195_ = v___y_2202_;
v___y_2196_ = v___y_2203_;
goto v___jp_2193_;
}
else
{
v___y_2177_ = v___y_2201_;
v___y_2178_ = v___y_2203_;
v___y_2179_ = v___x_2207_;
goto v___jp_2176_;
}
}
}
v___jp_2208_:
{
if (lean_obj_tag(v_x_2001_) == 2)
{
lean_object* v_val_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v_val_2210_ = lean_ctor_get(v_x_2001_, 1);
v___x_2211_ = lean_unsigned_to_nat(0u);
v___x_2212_ = lean_string_utf8_byte_size(v_val_2210_);
lean_inc_ref(v_val_2210_);
v___x_2213_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2213_, 0, v_val_2210_);
lean_ctor_set(v___x_2213_, 1, v___x_2211_);
lean_ctor_set(v___x_2213_, 2, v___x_2212_);
v___x_2214_ = l_String_Slice_Pos_get_x3f(v___x_2213_, v___x_2211_);
lean_dec_ref_known(v___x_2213_, 3);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_inc_ref(v_val_2210_);
v___y_2177_ = v___y_2209_;
v___y_2178_ = v_val_2210_;
v___y_2179_ = v___x_2175_;
goto v___jp_2176_;
}
else
{
lean_object* v_val_2215_; uint32_t v___x_2216_; uint32_t v___x_2217_; uint8_t v___x_2218_; 
v_val_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_val_2215_);
lean_dec_ref_known(v___x_2214_, 1);
v___x_2216_ = 65;
v___x_2217_ = lean_unbox_uint32(v_val_2215_);
v___x_2218_ = lean_uint32_dec_le(v___x_2216_, v___x_2217_);
if (v___x_2218_ == 0)
{
uint32_t v___x_2219_; 
v___x_2219_ = lean_unbox_uint32(v_val_2215_);
lean_dec(v_val_2215_);
lean_inc_ref(v_val_2210_);
v___y_2201_ = v___y_2209_;
v___y_2202_ = v___x_2219_;
v___y_2203_ = v_val_2210_;
goto v___jp_2200_;
}
else
{
uint32_t v___x_2220_; uint32_t v___x_2221_; uint8_t v___x_2222_; 
v___x_2220_ = 90;
v___x_2221_ = lean_unbox_uint32(v_val_2215_);
v___x_2222_ = lean_uint32_dec_le(v___x_2221_, v___x_2220_);
if (v___x_2222_ == 0)
{
uint32_t v___x_2223_; 
v___x_2223_ = lean_unbox_uint32(v_val_2215_);
lean_dec(v_val_2215_);
lean_inc_ref(v_val_2210_);
v___y_2201_ = v___y_2209_;
v___y_2202_ = v___x_2223_;
v___y_2203_ = v_val_2210_;
goto v___jp_2200_;
}
else
{
lean_dec(v_val_2215_);
lean_inc_ref(v_val_2210_);
v___y_2177_ = v___y_2209_;
v___y_2178_ = v_val_2210_;
v___y_2179_ = v___x_2222_;
goto v___jp_2176_;
}
}
}
}
else
{
lean_dec(v_x_2001_);
return v___y_2209_;
}
}
}
else
{
lean_object* v___x_2246_; 
lean_dec(v___x_2172_);
lean_dec(v_x_2001_);
lean_dec_ref(v_text_2000_);
v___x_2246_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2246_;
}
}
else
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; uint8_t v___x_2252_; 
v___x_2247_ = lean_unsigned_to_nat(0u);
v___x_2248_ = lean_unsigned_to_nat(1u);
v___x_2249_ = lean_unsigned_to_nat(2u);
v___x_2250_ = l_Lean_Syntax_getArg(v_x_2001_, v___x_2249_);
v___x_2251_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__10));
lean_inc(v___x_2250_);
v___x_2252_ = l_Lean_Syntax_isOfKind(v___x_2250_, v___x_2251_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2253_; lean_object* v___x_2254_; uint8_t v___x_2255_; 
lean_dec(v___x_2250_);
v___x_2253_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2001_);
v___x_2254_ = l_Lean_Syntax_getKind(v_x_2001_);
v___x_2255_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2253_, v___x_2254_);
if (v___x_2255_ == 0)
{
lean_object* v___x_2256_; uint8_t v___x_2257_; lean_object* v___y_2259_; lean_object* v___y_2260_; uint8_t v___y_2261_; lean_object* v___y_2275_; lean_object* v___y_2276_; uint32_t v___y_2277_; lean_object* v___y_2282_; lean_object* v___y_2283_; uint32_t v___y_2284_; lean_object* v___y_2290_; 
v___x_2256_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2257_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2256_, v___x_2254_);
lean_dec(v___x_2254_);
if (v___x_2257_ == 0)
{
lean_object* v___x_2304_; uint8_t v___x_2305_; 
v___x_2304_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2001_);
v___x_2305_ = l_Lean_Syntax_isOfKind(v_x_2001_, v___x_2304_);
if (v___x_2305_ == 0)
{
lean_object* v___x_2306_; size_t v_sz_2307_; size_t v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; uint8_t v___x_2312_; 
v___x_2306_ = l_Lean_Syntax_getArgs(v_x_2001_);
v_sz_2307_ = lean_array_size(v___x_2306_);
v___x_2308_ = ((size_t)0ULL);
v___x_2309_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2000_, v_sz_2307_, v___x_2308_, v___x_2306_);
v___x_2310_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2311_ = lean_array_get_size(v___x_2309_);
v___x_2312_ = lean_nat_dec_lt(v___x_2247_, v___x_2311_);
if (v___x_2312_ == 0)
{
lean_dec_ref(v___x_2309_);
v___y_2290_ = v___x_2310_;
goto v___jp_2289_;
}
else
{
size_t v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = lean_usize_of_nat(v___x_2311_);
v___x_2314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2309_, v___x_2308_, v___x_2313_, v___x_2310_);
lean_dec_ref(v___x_2309_);
v___y_2290_ = v___x_2314_;
goto v___jp_2289_;
}
}
else
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = l_Lean_Syntax_getArg(v_x_2001_, v___x_2247_);
v___x_2316_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2000_, v___x_2315_);
v___y_2290_ = v___x_2316_;
goto v___jp_2289_;
}
}
else
{
lean_object* v___x_2317_; lean_object* v___x_2318_; uint8_t v___x_2319_; 
v___x_2317_ = l_Lean_Syntax_getArg(v_x_2001_, v___x_2248_);
lean_dec(v_x_2001_);
v___x_2318_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v___x_2317_);
v___x_2319_ = l_Lean_Syntax_isOfKind(v___x_2317_, v___x_2318_);
if (v___x_2319_ == 0)
{
lean_object* v___x_2320_; 
lean_dec(v___x_2317_);
lean_dec_ref(v_text_2000_);
v___x_2320_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2320_;
}
else
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2321_, 0, v_text_2000_);
v___x_2322_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v___x_2317_, v___x_2321_);
return v___x_2322_;
}
}
v___jp_2258_:
{
lean_object* v___x_2262_; 
lean_inc_ref(v___y_2260_);
v___x_2262_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2260_);
if (lean_obj_tag(v___x_2262_) == 0)
{
v___y_2047_ = v___y_2259_;
v___y_2048_ = v___y_2260_;
v___y_2049_ = v___y_2261_;
v___y_2050_ = v___x_2257_;
goto v___jp_2046_;
}
else
{
lean_object* v_val_2263_; lean_object* v___x_2264_; 
v_val_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc(v_val_2263_);
lean_dec_ref_known(v___x_2262_, 1);
v___x_2264_ = l_String_Slice_Pos_get_x3f(v_val_2263_, v___x_2247_);
lean_dec(v_val_2263_);
if (lean_obj_tag(v___x_2264_) == 0)
{
v___y_2047_ = v___y_2259_;
v___y_2048_ = v___y_2260_;
v___y_2049_ = v___y_2261_;
v___y_2050_ = v___x_2257_;
goto v___jp_2046_;
}
else
{
lean_object* v_val_2265_; uint32_t v___x_2266_; uint32_t v___x_2267_; uint8_t v___x_2268_; 
v_val_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_val_2265_);
lean_dec_ref_known(v___x_2264_, 1);
v___x_2266_ = 65;
v___x_2267_ = lean_unbox_uint32(v_val_2265_);
v___x_2268_ = lean_uint32_dec_le(v___x_2266_, v___x_2267_);
if (v___x_2268_ == 0)
{
uint32_t v___x_2269_; 
v___x_2269_ = lean_unbox_uint32(v_val_2265_);
lean_dec(v_val_2265_);
v___y_2060_ = v___y_2259_;
v___y_2061_ = v___x_2269_;
v___y_2062_ = v___y_2260_;
v___y_2063_ = v___y_2261_;
goto v___jp_2059_;
}
else
{
uint32_t v___x_2270_; uint32_t v___x_2271_; uint8_t v___x_2272_; 
v___x_2270_ = 90;
v___x_2271_ = lean_unbox_uint32(v_val_2265_);
v___x_2272_ = lean_uint32_dec_le(v___x_2271_, v___x_2270_);
if (v___x_2272_ == 0)
{
uint32_t v___x_2273_; 
v___x_2273_ = lean_unbox_uint32(v_val_2265_);
lean_dec(v_val_2265_);
v___y_2060_ = v___y_2259_;
v___y_2061_ = v___x_2273_;
v___y_2062_ = v___y_2260_;
v___y_2063_ = v___y_2261_;
goto v___jp_2059_;
}
else
{
lean_dec(v_val_2265_);
v___y_2047_ = v___y_2259_;
v___y_2048_ = v___y_2260_;
v___y_2049_ = v___y_2261_;
v___y_2050_ = v___x_2272_;
goto v___jp_2046_;
}
}
}
}
}
v___jp_2274_:
{
uint32_t v___x_2278_; uint8_t v___x_2279_; 
v___x_2278_ = 95;
v___x_2279_ = lean_uint32_dec_eq(v___y_2277_, v___x_2278_);
if (v___x_2279_ == 0)
{
uint8_t v___x_2280_; 
v___x_2280_ = l_Lean_isLetterLike(v___y_2277_);
v___y_2259_ = v___y_2275_;
v___y_2260_ = v___y_2276_;
v___y_2261_ = v___x_2280_;
goto v___jp_2258_;
}
else
{
v___y_2259_ = v___y_2275_;
v___y_2260_ = v___y_2276_;
v___y_2261_ = v___x_2279_;
goto v___jp_2258_;
}
}
v___jp_2281_:
{
uint32_t v___x_2285_; uint8_t v___x_2286_; 
v___x_2285_ = 97;
v___x_2286_ = lean_uint32_dec_le(v___x_2285_, v___y_2284_);
if (v___x_2286_ == 0)
{
v___y_2275_ = v___y_2282_;
v___y_2276_ = v___y_2283_;
v___y_2277_ = v___y_2284_;
goto v___jp_2274_;
}
else
{
uint32_t v___x_2287_; uint8_t v___x_2288_; 
v___x_2287_ = 122;
v___x_2288_ = lean_uint32_dec_le(v___y_2284_, v___x_2287_);
if (v___x_2288_ == 0)
{
v___y_2275_ = v___y_2282_;
v___y_2276_ = v___y_2283_;
v___y_2277_ = v___y_2284_;
goto v___jp_2274_;
}
else
{
v___y_2259_ = v___y_2282_;
v___y_2260_ = v___y_2283_;
v___y_2261_ = v___x_2288_;
goto v___jp_2258_;
}
}
}
v___jp_2289_:
{
if (lean_obj_tag(v_x_2001_) == 2)
{
lean_object* v_val_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v_val_2291_ = lean_ctor_get(v_x_2001_, 1);
v___x_2292_ = lean_string_utf8_byte_size(v_val_2291_);
lean_inc_ref(v_val_2291_);
v___x_2293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2293_, 0, v_val_2291_);
lean_ctor_set(v___x_2293_, 1, v___x_2247_);
lean_ctor_set(v___x_2293_, 2, v___x_2292_);
v___x_2294_ = l_String_Slice_Pos_get_x3f(v___x_2293_, v___x_2247_);
lean_dec_ref_known(v___x_2293_, 3);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_inc_ref(v_val_2291_);
v___y_2259_ = v___y_2290_;
v___y_2260_ = v_val_2291_;
v___y_2261_ = v___x_2257_;
goto v___jp_2258_;
}
else
{
lean_object* v_val_2295_; uint32_t v___x_2296_; uint32_t v___x_2297_; uint8_t v___x_2298_; 
v_val_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_val_2295_);
lean_dec_ref_known(v___x_2294_, 1);
v___x_2296_ = 65;
v___x_2297_ = lean_unbox_uint32(v_val_2295_);
v___x_2298_ = lean_uint32_dec_le(v___x_2296_, v___x_2297_);
if (v___x_2298_ == 0)
{
uint32_t v___x_2299_; 
v___x_2299_ = lean_unbox_uint32(v_val_2295_);
lean_dec(v_val_2295_);
lean_inc_ref(v_val_2291_);
v___y_2282_ = v___y_2290_;
v___y_2283_ = v_val_2291_;
v___y_2284_ = v___x_2299_;
goto v___jp_2281_;
}
else
{
uint32_t v___x_2300_; uint32_t v___x_2301_; uint8_t v___x_2302_; 
v___x_2300_ = 90;
v___x_2301_ = lean_unbox_uint32(v_val_2295_);
v___x_2302_ = lean_uint32_dec_le(v___x_2301_, v___x_2300_);
if (v___x_2302_ == 0)
{
uint32_t v___x_2303_; 
v___x_2303_ = lean_unbox_uint32(v_val_2295_);
lean_dec(v_val_2295_);
lean_inc_ref(v_val_2291_);
v___y_2282_ = v___y_2290_;
v___y_2283_ = v_val_2291_;
v___y_2284_ = v___x_2303_;
goto v___jp_2281_;
}
else
{
lean_dec(v_val_2295_);
lean_inc_ref(v_val_2291_);
v___y_2259_ = v___y_2290_;
v___y_2260_ = v_val_2291_;
v___y_2261_ = v___x_2302_;
goto v___jp_2258_;
}
}
}
}
else
{
lean_dec(v_x_2001_);
return v___y_2290_;
}
}
}
else
{
lean_object* v___x_2323_; 
lean_dec(v___x_2254_);
lean_dec(v_x_2001_);
lean_dec_ref(v_text_2000_);
v___x_2323_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2323_;
}
}
else
{
lean_object* v___x_2324_; lean_object* v___x_2325_; uint8_t v___x_2326_; 
v___x_2324_ = lean_unsigned_to_nat(3u);
v___x_2325_ = l_Lean_Syntax_getArg(v_x_2001_, v___x_2324_);
v___x_2326_ = l_Lean_Syntax_matchesNull(v___x_2325_, v___x_2247_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; lean_object* v___x_2328_; uint8_t v___x_2329_; 
lean_dec(v___x_2250_);
v___x_2327_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2001_);
v___x_2328_ = l_Lean_Syntax_getKind(v_x_2001_);
v___x_2329_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2327_, v___x_2328_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; uint8_t v___x_2331_; lean_object* v___y_2333_; lean_object* v___y_2334_; uint8_t v___y_2335_; uint32_t v___y_2349_; lean_object* v___y_2350_; lean_object* v___y_2351_; uint32_t v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2364_; 
v___x_2330_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2331_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2330_, v___x_2328_);
lean_dec(v___x_2328_);
if (v___x_2331_ == 0)
{
lean_object* v___x_2378_; uint8_t v___x_2379_; 
v___x_2378_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2001_);
v___x_2379_ = l_Lean_Syntax_isOfKind(v_x_2001_, v___x_2378_);
if (v___x_2379_ == 0)
{
lean_object* v___x_2380_; size_t v_sz_2381_; size_t v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; uint8_t v___x_2386_; 
v___x_2380_ = l_Lean_Syntax_getArgs(v_x_2001_);
v_sz_2381_ = lean_array_size(v___x_2380_);
v___x_2382_ = ((size_t)0ULL);
v___x_2383_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2000_, v_sz_2381_, v___x_2382_, v___x_2380_);
v___x_2384_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2385_ = lean_array_get_size(v___x_2383_);
v___x_2386_ = lean_nat_dec_lt(v___x_2247_, v___x_2385_);
if (v___x_2386_ == 0)
{
lean_dec_ref(v___x_2383_);
v___y_2364_ = v___x_2384_;
goto v___jp_2363_;
}
else
{
size_t v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = lean_usize_of_nat(v___x_2385_);
v___x_2388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2383_, v___x_2382_, v___x_2387_, v___x_2384_);
lean_dec_ref(v___x_2383_);
v___y_2364_ = v___x_2388_;
goto v___jp_2363_;
}
}
else
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = l_Lean_Syntax_getArg(v_x_2001_, v___x_2247_);
v___x_2390_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2000_, v___x_2389_);
v___y_2364_ = v___x_2390_;
goto v___jp_2363_;
}
}
else
{
lean_object* v___x_2391_; lean_object* v___x_2392_; uint8_t v___x_2393_; 
v___x_2391_ = l_Lean_Syntax_getArg(v_x_2001_, v___x_2248_);
lean_dec(v_x_2001_);
v___x_2392_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v___x_2391_);
v___x_2393_ = l_Lean_Syntax_isOfKind(v___x_2391_, v___x_2392_);
if (v___x_2393_ == 0)
{
lean_object* v___x_2394_; 
lean_dec(v___x_2391_);
lean_dec_ref(v_text_2000_);
v___x_2394_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2394_;
}
else
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2395_, 0, v_text_2000_);
v___x_2396_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v___x_2391_, v___x_2395_);
return v___x_2396_;
}
}
v___jp_2332_:
{
lean_object* v___x_2336_; 
lean_inc_ref(v___y_2334_);
v___x_2336_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2334_);
if (lean_obj_tag(v___x_2336_) == 0)
{
v___y_2080_ = v___y_2335_;
v___y_2081_ = v___y_2333_;
v___y_2082_ = v___y_2334_;
v___y_2083_ = v___x_2331_;
goto v___jp_2079_;
}
else
{
lean_object* v_val_2337_; lean_object* v___x_2338_; 
v_val_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_val_2337_);
lean_dec_ref_known(v___x_2336_, 1);
v___x_2338_ = l_String_Slice_Pos_get_x3f(v_val_2337_, v___x_2247_);
lean_dec(v_val_2337_);
if (lean_obj_tag(v___x_2338_) == 0)
{
v___y_2080_ = v___y_2335_;
v___y_2081_ = v___y_2333_;
v___y_2082_ = v___y_2334_;
v___y_2083_ = v___x_2331_;
goto v___jp_2079_;
}
else
{
lean_object* v_val_2339_; uint32_t v___x_2340_; uint32_t v___x_2341_; uint8_t v___x_2342_; 
v_val_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_val_2339_);
lean_dec_ref_known(v___x_2338_, 1);
v___x_2340_ = 65;
v___x_2341_ = lean_unbox_uint32(v_val_2339_);
v___x_2342_ = lean_uint32_dec_le(v___x_2340_, v___x_2341_);
if (v___x_2342_ == 0)
{
uint32_t v___x_2343_; 
v___x_2343_ = lean_unbox_uint32(v_val_2339_);
lean_dec(v_val_2339_);
v___y_2093_ = v___x_2343_;
v___y_2094_ = v___y_2335_;
v___y_2095_ = v___y_2333_;
v___y_2096_ = v___y_2334_;
goto v___jp_2092_;
}
else
{
uint32_t v___x_2344_; uint32_t v___x_2345_; uint8_t v___x_2346_; 
v___x_2344_ = 90;
v___x_2345_ = lean_unbox_uint32(v_val_2339_);
v___x_2346_ = lean_uint32_dec_le(v___x_2345_, v___x_2344_);
if (v___x_2346_ == 0)
{
uint32_t v___x_2347_; 
v___x_2347_ = lean_unbox_uint32(v_val_2339_);
lean_dec(v_val_2339_);
v___y_2093_ = v___x_2347_;
v___y_2094_ = v___y_2335_;
v___y_2095_ = v___y_2333_;
v___y_2096_ = v___y_2334_;
goto v___jp_2092_;
}
else
{
lean_dec(v_val_2339_);
v___y_2080_ = v___y_2335_;
v___y_2081_ = v___y_2333_;
v___y_2082_ = v___y_2334_;
v___y_2083_ = v___x_2346_;
goto v___jp_2079_;
}
}
}
}
}
v___jp_2348_:
{
uint32_t v___x_2352_; uint8_t v___x_2353_; 
v___x_2352_ = 95;
v___x_2353_ = lean_uint32_dec_eq(v___y_2349_, v___x_2352_);
if (v___x_2353_ == 0)
{
uint8_t v___x_2354_; 
v___x_2354_ = l_Lean_isLetterLike(v___y_2349_);
v___y_2333_ = v___y_2350_;
v___y_2334_ = v___y_2351_;
v___y_2335_ = v___x_2354_;
goto v___jp_2332_;
}
else
{
v___y_2333_ = v___y_2350_;
v___y_2334_ = v___y_2351_;
v___y_2335_ = v___x_2353_;
goto v___jp_2332_;
}
}
v___jp_2355_:
{
uint32_t v___x_2359_; uint8_t v___x_2360_; 
v___x_2359_ = 97;
v___x_2360_ = lean_uint32_dec_le(v___x_2359_, v___y_2356_);
if (v___x_2360_ == 0)
{
v___y_2349_ = v___y_2356_;
v___y_2350_ = v___y_2357_;
v___y_2351_ = v___y_2358_;
goto v___jp_2348_;
}
else
{
uint32_t v___x_2361_; uint8_t v___x_2362_; 
v___x_2361_ = 122;
v___x_2362_ = lean_uint32_dec_le(v___y_2356_, v___x_2361_);
if (v___x_2362_ == 0)
{
v___y_2349_ = v___y_2356_;
v___y_2350_ = v___y_2357_;
v___y_2351_ = v___y_2358_;
goto v___jp_2348_;
}
else
{
v___y_2333_ = v___y_2357_;
v___y_2334_ = v___y_2358_;
v___y_2335_ = v___x_2362_;
goto v___jp_2332_;
}
}
}
v___jp_2363_:
{
if (lean_obj_tag(v_x_2001_) == 2)
{
lean_object* v_val_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v_val_2365_ = lean_ctor_get(v_x_2001_, 1);
v___x_2366_ = lean_string_utf8_byte_size(v_val_2365_);
lean_inc_ref(v_val_2365_);
v___x_2367_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2367_, 0, v_val_2365_);
lean_ctor_set(v___x_2367_, 1, v___x_2247_);
lean_ctor_set(v___x_2367_, 2, v___x_2366_);
v___x_2368_ = l_String_Slice_Pos_get_x3f(v___x_2367_, v___x_2247_);
lean_dec_ref_known(v___x_2367_, 3);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_inc_ref(v_val_2365_);
v___y_2333_ = v___y_2364_;
v___y_2334_ = v_val_2365_;
v___y_2335_ = v___x_2331_;
goto v___jp_2332_;
}
else
{
lean_object* v_val_2369_; uint32_t v___x_2370_; uint32_t v___x_2371_; uint8_t v___x_2372_; 
v_val_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_val_2369_);
lean_dec_ref_known(v___x_2368_, 1);
v___x_2370_ = 65;
v___x_2371_ = lean_unbox_uint32(v_val_2369_);
v___x_2372_ = lean_uint32_dec_le(v___x_2370_, v___x_2371_);
if (v___x_2372_ == 0)
{
uint32_t v___x_2373_; 
v___x_2373_ = lean_unbox_uint32(v_val_2369_);
lean_dec(v_val_2369_);
lean_inc_ref(v_val_2365_);
v___y_2356_ = v___x_2373_;
v___y_2357_ = v___y_2364_;
v___y_2358_ = v_val_2365_;
goto v___jp_2355_;
}
else
{
uint32_t v___x_2374_; uint32_t v___x_2375_; uint8_t v___x_2376_; 
v___x_2374_ = 90;
v___x_2375_ = lean_unbox_uint32(v_val_2369_);
v___x_2376_ = lean_uint32_dec_le(v___x_2375_, v___x_2374_);
if (v___x_2376_ == 0)
{
uint32_t v___x_2377_; 
v___x_2377_ = lean_unbox_uint32(v_val_2369_);
lean_dec(v_val_2369_);
lean_inc_ref(v_val_2365_);
v___y_2356_ = v___x_2377_;
v___y_2357_ = v___y_2364_;
v___y_2358_ = v_val_2365_;
goto v___jp_2355_;
}
else
{
lean_dec(v_val_2369_);
lean_inc_ref(v_val_2365_);
v___y_2333_ = v___y_2364_;
v___y_2334_ = v_val_2365_;
v___y_2335_ = v___x_2376_;
goto v___jp_2332_;
}
}
}
}
else
{
lean_dec(v_x_2001_);
return v___y_2364_;
}
}
}
else
{
lean_object* v___x_2397_; 
lean_dec(v___x_2328_);
lean_dec(v_x_2001_);
lean_dec_ref(v_text_2000_);
v___x_2397_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2397_;
}
}
else
{
lean_object* v___x_2398_; lean_object* v___x_2399_; uint8_t v___x_2400_; 
v___x_2398_ = lean_unsigned_to_nat(4u);
v___x_2399_ = l_Lean_Syntax_getArg(v_x_2001_, v___x_2398_);
v___x_2400_ = l_Lean_Syntax_matchesNull(v___x_2399_, v___x_2247_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; lean_object* v___x_2402_; uint8_t v___x_2403_; 
lean_dec(v___x_2250_);
v___x_2401_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2001_);
v___x_2402_ = l_Lean_Syntax_getKind(v_x_2001_);
v___x_2403_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2401_, v___x_2402_);
if (v___x_2403_ == 0)
{
lean_object* v___x_2404_; uint8_t v___x_2405_; lean_object* v___y_2407_; lean_object* v___y_2408_; uint8_t v___y_2409_; lean_object* v___y_2423_; lean_object* v___y_2424_; uint32_t v___y_2425_; lean_object* v___y_2430_; lean_object* v___y_2431_; uint32_t v___y_2432_; lean_object* v___y_2438_; 
v___x_2404_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2405_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2404_, v___x_2402_);
lean_dec(v___x_2402_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2452_; uint8_t v___x_2453_; 
v___x_2452_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2001_);
v___x_2453_ = l_Lean_Syntax_isOfKind(v_x_2001_, v___x_2452_);
if (v___x_2453_ == 0)
{
lean_object* v___x_2454_; size_t v_sz_2455_; size_t v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; uint8_t v___x_2460_; 
v___x_2454_ = l_Lean_Syntax_getArgs(v_x_2001_);
v_sz_2455_ = lean_array_size(v___x_2454_);
v___x_2456_ = ((size_t)0ULL);
v___x_2457_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2000_, v_sz_2455_, v___x_2456_, v___x_2454_);
v___x_2458_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2459_ = lean_array_get_size(v___x_2457_);
v___x_2460_ = lean_nat_dec_lt(v___x_2247_, v___x_2459_);
if (v___x_2460_ == 0)
{
lean_dec_ref(v___x_2457_);
v___y_2438_ = v___x_2458_;
goto v___jp_2437_;
}
else
{
size_t v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = lean_usize_of_nat(v___x_2459_);
v___x_2462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2457_, v___x_2456_, v___x_2461_, v___x_2458_);
lean_dec_ref(v___x_2457_);
v___y_2438_ = v___x_2462_;
goto v___jp_2437_;
}
}
else
{
lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2463_ = l_Lean_Syntax_getArg(v_x_2001_, v___x_2247_);
v___x_2464_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2000_, v___x_2463_);
v___y_2438_ = v___x_2464_;
goto v___jp_2437_;
}
}
else
{
lean_object* v___x_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2465_ = l_Lean_Syntax_getArg(v_x_2001_, v___x_2248_);
lean_dec(v_x_2001_);
v___x_2466_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v___x_2465_);
v___x_2467_ = l_Lean_Syntax_isOfKind(v___x_2465_, v___x_2466_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; 
lean_dec(v___x_2465_);
lean_dec_ref(v_text_2000_);
v___x_2468_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2468_;
}
else
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2469_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2469_, 0, v_text_2000_);
v___x_2470_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v___x_2465_, v___x_2469_);
return v___x_2470_;
}
}
v___jp_2406_:
{
lean_object* v___x_2410_; 
lean_inc_ref(v___y_2408_);
v___x_2410_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2408_);
if (lean_obj_tag(v___x_2410_) == 0)
{
v___y_2113_ = v___y_2407_;
v___y_2114_ = v___y_2408_;
v___y_2115_ = v___y_2409_;
v___y_2116_ = v___x_2405_;
goto v___jp_2112_;
}
else
{
lean_object* v_val_2411_; lean_object* v___x_2412_; 
v_val_2411_ = lean_ctor_get(v___x_2410_, 0);
lean_inc(v_val_2411_);
lean_dec_ref_known(v___x_2410_, 1);
v___x_2412_ = l_String_Slice_Pos_get_x3f(v_val_2411_, v___x_2247_);
lean_dec(v_val_2411_);
if (lean_obj_tag(v___x_2412_) == 0)
{
v___y_2113_ = v___y_2407_;
v___y_2114_ = v___y_2408_;
v___y_2115_ = v___y_2409_;
v___y_2116_ = v___x_2405_;
goto v___jp_2112_;
}
else
{
lean_object* v_val_2413_; uint32_t v___x_2414_; uint32_t v___x_2415_; uint8_t v___x_2416_; 
v_val_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_val_2413_);
lean_dec_ref_known(v___x_2412_, 1);
v___x_2414_ = 65;
v___x_2415_ = lean_unbox_uint32(v_val_2413_);
v___x_2416_ = lean_uint32_dec_le(v___x_2414_, v___x_2415_);
if (v___x_2416_ == 0)
{
uint32_t v___x_2417_; 
v___x_2417_ = lean_unbox_uint32(v_val_2413_);
lean_dec(v_val_2413_);
v___y_2126_ = v___y_2407_;
v___y_2127_ = v___y_2408_;
v___y_2128_ = v___x_2417_;
v___y_2129_ = v___y_2409_;
goto v___jp_2125_;
}
else
{
uint32_t v___x_2418_; uint32_t v___x_2419_; uint8_t v___x_2420_; 
v___x_2418_ = 90;
v___x_2419_ = lean_unbox_uint32(v_val_2413_);
v___x_2420_ = lean_uint32_dec_le(v___x_2419_, v___x_2418_);
if (v___x_2420_ == 0)
{
uint32_t v___x_2421_; 
v___x_2421_ = lean_unbox_uint32(v_val_2413_);
lean_dec(v_val_2413_);
v___y_2126_ = v___y_2407_;
v___y_2127_ = v___y_2408_;
v___y_2128_ = v___x_2421_;
v___y_2129_ = v___y_2409_;
goto v___jp_2125_;
}
else
{
lean_dec(v_val_2413_);
v___y_2113_ = v___y_2407_;
v___y_2114_ = v___y_2408_;
v___y_2115_ = v___y_2409_;
v___y_2116_ = v___x_2420_;
goto v___jp_2112_;
}
}
}
}
}
v___jp_2422_:
{
uint32_t v___x_2426_; uint8_t v___x_2427_; 
v___x_2426_ = 95;
v___x_2427_ = lean_uint32_dec_eq(v___y_2425_, v___x_2426_);
if (v___x_2427_ == 0)
{
uint8_t v___x_2428_; 
v___x_2428_ = l_Lean_isLetterLike(v___y_2425_);
v___y_2407_ = v___y_2423_;
v___y_2408_ = v___y_2424_;
v___y_2409_ = v___x_2428_;
goto v___jp_2406_;
}
else
{
v___y_2407_ = v___y_2423_;
v___y_2408_ = v___y_2424_;
v___y_2409_ = v___x_2427_;
goto v___jp_2406_;
}
}
v___jp_2429_:
{
uint32_t v___x_2433_; uint8_t v___x_2434_; 
v___x_2433_ = 97;
v___x_2434_ = lean_uint32_dec_le(v___x_2433_, v___y_2432_);
if (v___x_2434_ == 0)
{
v___y_2423_ = v___y_2430_;
v___y_2424_ = v___y_2431_;
v___y_2425_ = v___y_2432_;
goto v___jp_2422_;
}
else
{
uint32_t v___x_2435_; uint8_t v___x_2436_; 
v___x_2435_ = 122;
v___x_2436_ = lean_uint32_dec_le(v___y_2432_, v___x_2435_);
if (v___x_2436_ == 0)
{
v___y_2423_ = v___y_2430_;
v___y_2424_ = v___y_2431_;
v___y_2425_ = v___y_2432_;
goto v___jp_2422_;
}
else
{
v___y_2407_ = v___y_2430_;
v___y_2408_ = v___y_2431_;
v___y_2409_ = v___x_2436_;
goto v___jp_2406_;
}
}
}
v___jp_2437_:
{
if (lean_obj_tag(v_x_2001_) == 2)
{
lean_object* v_val_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v_val_2439_ = lean_ctor_get(v_x_2001_, 1);
v___x_2440_ = lean_string_utf8_byte_size(v_val_2439_);
lean_inc_ref(v_val_2439_);
v___x_2441_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2441_, 0, v_val_2439_);
lean_ctor_set(v___x_2441_, 1, v___x_2247_);
lean_ctor_set(v___x_2441_, 2, v___x_2440_);
v___x_2442_ = l_String_Slice_Pos_get_x3f(v___x_2441_, v___x_2247_);
lean_dec_ref_known(v___x_2441_, 3);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_inc_ref(v_val_2439_);
v___y_2407_ = v___y_2438_;
v___y_2408_ = v_val_2439_;
v___y_2409_ = v___x_2405_;
goto v___jp_2406_;
}
else
{
lean_object* v_val_2443_; uint32_t v___x_2444_; uint32_t v___x_2445_; uint8_t v___x_2446_; 
v_val_2443_ = lean_ctor_get(v___x_2442_, 0);
lean_inc(v_val_2443_);
lean_dec_ref_known(v___x_2442_, 1);
v___x_2444_ = 65;
v___x_2445_ = lean_unbox_uint32(v_val_2443_);
v___x_2446_ = lean_uint32_dec_le(v___x_2444_, v___x_2445_);
if (v___x_2446_ == 0)
{
uint32_t v___x_2447_; 
v___x_2447_ = lean_unbox_uint32(v_val_2443_);
lean_dec(v_val_2443_);
lean_inc_ref(v_val_2439_);
v___y_2430_ = v___y_2438_;
v___y_2431_ = v_val_2439_;
v___y_2432_ = v___x_2447_;
goto v___jp_2429_;
}
else
{
uint32_t v___x_2448_; uint32_t v___x_2449_; uint8_t v___x_2450_; 
v___x_2448_ = 90;
v___x_2449_ = lean_unbox_uint32(v_val_2443_);
v___x_2450_ = lean_uint32_dec_le(v___x_2449_, v___x_2448_);
if (v___x_2450_ == 0)
{
uint32_t v___x_2451_; 
v___x_2451_ = lean_unbox_uint32(v_val_2443_);
lean_dec(v_val_2443_);
lean_inc_ref(v_val_2439_);
v___y_2430_ = v___y_2438_;
v___y_2431_ = v_val_2439_;
v___y_2432_ = v___x_2451_;
goto v___jp_2429_;
}
else
{
lean_dec(v_val_2443_);
lean_inc_ref(v_val_2439_);
v___y_2407_ = v___y_2438_;
v___y_2408_ = v_val_2439_;
v___y_2409_ = v___x_2450_;
goto v___jp_2406_;
}
}
}
}
else
{
lean_dec(v_x_2001_);
return v___y_2438_;
}
}
}
else
{
lean_object* v___x_2471_; 
lean_dec(v___x_2402_);
lean_dec(v_x_2001_);
lean_dec_ref(v_text_2000_);
v___x_2471_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2471_;
}
}
else
{
lean_object* v___x_2472_; lean_object* v_tokens_2473_; uint8_t v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2472_ = l_Lean_Syntax_getArg(v_x_2001_, v___x_2247_);
lean_dec(v_x_2001_);
v_tokens_2473_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2000_, v___x_2472_);
v___x_2474_ = 2;
v___x_2475_ = lean_unsigned_to_nat(5u);
v___x_2476_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2476_, 0, v___x_2250_);
lean_ctor_set(v___x_2476_, 1, v___x_2475_);
lean_ctor_set_uint8(v___x_2476_, sizeof(void*)*2, v___x_2474_);
v___x_2477_ = lean_array_push(v_tokens_2473_, v___x_2476_);
return v___x_2477_;
}
}
}
}
}
else
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; uint8_t v___x_2482_; 
v___x_2478_ = lean_unsigned_to_nat(0u);
v___x_2479_ = lean_unsigned_to_nat(2u);
v___x_2480_ = l_Lean_Syntax_getArg(v_x_2001_, v___x_2479_);
v___x_2481_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__10));
lean_inc(v___x_2480_);
v___x_2482_ = l_Lean_Syntax_isOfKind(v___x_2480_, v___x_2481_);
if (v___x_2482_ == 0)
{
lean_object* v___x_2483_; lean_object* v___x_2484_; uint8_t v___x_2485_; 
lean_dec(v___x_2480_);
v___x_2483_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2001_);
v___x_2484_ = l_Lean_Syntax_getKind(v_x_2001_);
v___x_2485_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2483_, v___x_2484_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2486_; uint8_t v___x_2487_; lean_object* v___y_2489_; lean_object* v___y_2490_; uint8_t v___y_2491_; uint32_t v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; uint32_t v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2520_; 
v___x_2486_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2487_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2486_, v___x_2484_);
lean_dec(v___x_2484_);
if (v___x_2487_ == 0)
{
lean_object* v___x_2534_; uint8_t v___x_2535_; 
v___x_2534_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2001_);
v___x_2535_ = l_Lean_Syntax_isOfKind(v_x_2001_, v___x_2534_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2536_; size_t v_sz_2537_; size_t v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; uint8_t v___x_2542_; 
v___x_2536_ = l_Lean_Syntax_getArgs(v_x_2001_);
v_sz_2537_ = lean_array_size(v___x_2536_);
v___x_2538_ = ((size_t)0ULL);
v___x_2539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2000_, v_sz_2537_, v___x_2538_, v___x_2536_);
v___x_2540_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2541_ = lean_array_get_size(v___x_2539_);
v___x_2542_ = lean_nat_dec_lt(v___x_2478_, v___x_2541_);
if (v___x_2542_ == 0)
{
lean_dec_ref(v___x_2539_);
v___y_2520_ = v___x_2540_;
goto v___jp_2519_;
}
else
{
size_t v___x_2543_; lean_object* v___x_2544_; 
v___x_2543_ = lean_usize_of_nat(v___x_2541_);
v___x_2544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2539_, v___x_2538_, v___x_2543_, v___x_2540_);
lean_dec_ref(v___x_2539_);
v___y_2520_ = v___x_2544_;
goto v___jp_2519_;
}
}
else
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = l_Lean_Syntax_getArg(v_x_2001_, v___x_2478_);
v___x_2546_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2000_, v___x_2545_);
v___y_2520_ = v___x_2546_;
goto v___jp_2519_;
}
}
else
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; uint8_t v___x_2550_; 
v___x_2547_ = lean_unsigned_to_nat(1u);
v___x_2548_ = l_Lean_Syntax_getArg(v_x_2001_, v___x_2547_);
lean_dec(v_x_2001_);
v___x_2549_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v___x_2548_);
v___x_2550_ = l_Lean_Syntax_isOfKind(v___x_2548_, v___x_2549_);
if (v___x_2550_ == 0)
{
lean_object* v___x_2551_; 
lean_dec(v___x_2548_);
lean_dec_ref(v_text_2000_);
v___x_2551_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2551_;
}
else
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2552_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2552_, 0, v_text_2000_);
v___x_2553_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v___x_2548_, v___x_2552_);
return v___x_2553_;
}
}
v___jp_2488_:
{
lean_object* v___x_2492_; 
lean_inc_ref(v___y_2490_);
v___x_2492_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2490_);
if (lean_obj_tag(v___x_2492_) == 0)
{
v___y_2146_ = v___y_2491_;
v___y_2147_ = v___y_2489_;
v___y_2148_ = v___y_2490_;
v___y_2149_ = v___x_2487_;
goto v___jp_2145_;
}
else
{
lean_object* v_val_2493_; lean_object* v___x_2494_; 
v_val_2493_ = lean_ctor_get(v___x_2492_, 0);
lean_inc(v_val_2493_);
lean_dec_ref_known(v___x_2492_, 1);
v___x_2494_ = l_String_Slice_Pos_get_x3f(v_val_2493_, v___x_2478_);
lean_dec(v_val_2493_);
if (lean_obj_tag(v___x_2494_) == 0)
{
v___y_2146_ = v___y_2491_;
v___y_2147_ = v___y_2489_;
v___y_2148_ = v___y_2490_;
v___y_2149_ = v___x_2487_;
goto v___jp_2145_;
}
else
{
lean_object* v_val_2495_; uint32_t v___x_2496_; uint32_t v___x_2497_; uint8_t v___x_2498_; 
v_val_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_val_2495_);
lean_dec_ref_known(v___x_2494_, 1);
v___x_2496_ = 65;
v___x_2497_ = lean_unbox_uint32(v_val_2495_);
v___x_2498_ = lean_uint32_dec_le(v___x_2496_, v___x_2497_);
if (v___x_2498_ == 0)
{
uint32_t v___x_2499_; 
v___x_2499_ = lean_unbox_uint32(v_val_2495_);
lean_dec(v_val_2495_);
v___y_2159_ = v___y_2491_;
v___y_2160_ = v___y_2489_;
v___y_2161_ = v___y_2490_;
v___y_2162_ = v___x_2499_;
goto v___jp_2158_;
}
else
{
uint32_t v___x_2500_; uint32_t v___x_2501_; uint8_t v___x_2502_; 
v___x_2500_ = 90;
v___x_2501_ = lean_unbox_uint32(v_val_2495_);
v___x_2502_ = lean_uint32_dec_le(v___x_2501_, v___x_2500_);
if (v___x_2502_ == 0)
{
uint32_t v___x_2503_; 
v___x_2503_ = lean_unbox_uint32(v_val_2495_);
lean_dec(v_val_2495_);
v___y_2159_ = v___y_2491_;
v___y_2160_ = v___y_2489_;
v___y_2161_ = v___y_2490_;
v___y_2162_ = v___x_2503_;
goto v___jp_2158_;
}
else
{
lean_dec(v_val_2495_);
v___y_2146_ = v___y_2491_;
v___y_2147_ = v___y_2489_;
v___y_2148_ = v___y_2490_;
v___y_2149_ = v___x_2502_;
goto v___jp_2145_;
}
}
}
}
}
v___jp_2504_:
{
uint32_t v___x_2508_; uint8_t v___x_2509_; 
v___x_2508_ = 95;
v___x_2509_ = lean_uint32_dec_eq(v___y_2505_, v___x_2508_);
if (v___x_2509_ == 0)
{
uint8_t v___x_2510_; 
v___x_2510_ = l_Lean_isLetterLike(v___y_2505_);
v___y_2489_ = v___y_2506_;
v___y_2490_ = v___y_2507_;
v___y_2491_ = v___x_2510_;
goto v___jp_2488_;
}
else
{
v___y_2489_ = v___y_2506_;
v___y_2490_ = v___y_2507_;
v___y_2491_ = v___x_2509_;
goto v___jp_2488_;
}
}
v___jp_2511_:
{
uint32_t v___x_2515_; uint8_t v___x_2516_; 
v___x_2515_ = 97;
v___x_2516_ = lean_uint32_dec_le(v___x_2515_, v___y_2512_);
if (v___x_2516_ == 0)
{
v___y_2505_ = v___y_2512_;
v___y_2506_ = v___y_2513_;
v___y_2507_ = v___y_2514_;
goto v___jp_2504_;
}
else
{
uint32_t v___x_2517_; uint8_t v___x_2518_; 
v___x_2517_ = 122;
v___x_2518_ = lean_uint32_dec_le(v___y_2512_, v___x_2517_);
if (v___x_2518_ == 0)
{
v___y_2505_ = v___y_2512_;
v___y_2506_ = v___y_2513_;
v___y_2507_ = v___y_2514_;
goto v___jp_2504_;
}
else
{
v___y_2489_ = v___y_2513_;
v___y_2490_ = v___y_2514_;
v___y_2491_ = v___x_2518_;
goto v___jp_2488_;
}
}
}
v___jp_2519_:
{
if (lean_obj_tag(v_x_2001_) == 2)
{
lean_object* v_val_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v_val_2521_ = lean_ctor_get(v_x_2001_, 1);
v___x_2522_ = lean_string_utf8_byte_size(v_val_2521_);
lean_inc_ref(v_val_2521_);
v___x_2523_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2523_, 0, v_val_2521_);
lean_ctor_set(v___x_2523_, 1, v___x_2478_);
lean_ctor_set(v___x_2523_, 2, v___x_2522_);
v___x_2524_ = l_String_Slice_Pos_get_x3f(v___x_2523_, v___x_2478_);
lean_dec_ref_known(v___x_2523_, 3);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_inc_ref(v_val_2521_);
v___y_2489_ = v___y_2520_;
v___y_2490_ = v_val_2521_;
v___y_2491_ = v___x_2487_;
goto v___jp_2488_;
}
else
{
lean_object* v_val_2525_; uint32_t v___x_2526_; uint32_t v___x_2527_; uint8_t v___x_2528_; 
v_val_2525_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_val_2525_);
lean_dec_ref_known(v___x_2524_, 1);
v___x_2526_ = 65;
v___x_2527_ = lean_unbox_uint32(v_val_2525_);
v___x_2528_ = lean_uint32_dec_le(v___x_2526_, v___x_2527_);
if (v___x_2528_ == 0)
{
uint32_t v___x_2529_; 
v___x_2529_ = lean_unbox_uint32(v_val_2525_);
lean_dec(v_val_2525_);
lean_inc_ref(v_val_2521_);
v___y_2512_ = v___x_2529_;
v___y_2513_ = v___y_2520_;
v___y_2514_ = v_val_2521_;
goto v___jp_2511_;
}
else
{
uint32_t v___x_2530_; uint32_t v___x_2531_; uint8_t v___x_2532_; 
v___x_2530_ = 90;
v___x_2531_ = lean_unbox_uint32(v_val_2525_);
v___x_2532_ = lean_uint32_dec_le(v___x_2531_, v___x_2530_);
if (v___x_2532_ == 0)
{
uint32_t v___x_2533_; 
v___x_2533_ = lean_unbox_uint32(v_val_2525_);
lean_dec(v_val_2525_);
lean_inc_ref(v_val_2521_);
v___y_2512_ = v___x_2533_;
v___y_2513_ = v___y_2520_;
v___y_2514_ = v_val_2521_;
goto v___jp_2511_;
}
else
{
lean_dec(v_val_2525_);
lean_inc_ref(v_val_2521_);
v___y_2489_ = v___y_2520_;
v___y_2490_ = v_val_2521_;
v___y_2491_ = v___x_2532_;
goto v___jp_2488_;
}
}
}
}
else
{
lean_dec(v_x_2001_);
return v___y_2520_;
}
}
}
else
{
lean_object* v___x_2554_; 
lean_dec(v___x_2484_);
lean_dec(v_x_2001_);
lean_dec_ref(v_text_2000_);
v___x_2554_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2554_;
}
}
else
{
lean_object* v___x_2555_; lean_object* v_tokens_2556_; uint8_t v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2555_ = l_Lean_Syntax_getArg(v_x_2001_, v___x_2478_);
lean_dec(v_x_2001_);
v_tokens_2556_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2000_, v___x_2555_);
v___x_2557_ = 2;
v___x_2558_ = lean_unsigned_to_nat(5u);
v___x_2559_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2559_, 0, v___x_2480_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
lean_ctor_set_uint8(v___x_2559_, sizeof(void*)*2, v___x_2557_);
v___x_2560_ = lean_array_push(v_tokens_2556_, v___x_2559_);
return v___x_2560_;
}
}
v___jp_2002_:
{
lean_object* v___x_2005_; uint8_t v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; uint8_t v___x_2011_; lean_object* v___x_2012_; 
v___x_2005_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2006_ = 0;
v___x_2007_ = lean_box(v___x_2006_);
v___x_2008_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2005_, v___y_2004_, v___x_2007_);
lean_dec(v___x_2007_);
lean_dec_ref(v___y_2004_);
v___x_2009_ = lean_unsigned_to_nat(5u);
v___x_2010_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2010_, 0, v_x_2001_);
lean_ctor_set(v___x_2010_, 1, v___x_2009_);
v___x_2011_ = lean_unbox(v___x_2008_);
lean_dec(v___x_2008_);
lean_ctor_set_uint8(v___x_2010_, sizeof(void*)*2, v___x_2011_);
v___x_2012_ = lean_array_push(v___y_2003_, v___x_2010_);
return v___x_2012_;
}
v___jp_2013_:
{
if (v___y_2014_ == 0)
{
if (v___y_2017_ == 0)
{
lean_dec_ref(v___y_2016_);
lean_dec(v_x_2001_);
return v___y_2015_;
}
else
{
v___y_2003_ = v___y_2015_;
v___y_2004_ = v___y_2016_;
goto v___jp_2002_;
}
}
else
{
v___y_2003_ = v___y_2015_;
v___y_2004_ = v___y_2016_;
goto v___jp_2002_;
}
}
v___jp_2018_:
{
uint32_t v___x_2023_; uint8_t v___x_2024_; 
v___x_2023_ = 95;
v___x_2024_ = lean_uint32_dec_eq(v___y_2020_, v___x_2023_);
if (v___x_2024_ == 0)
{
uint8_t v___x_2025_; 
v___x_2025_ = l_Lean_isLetterLike(v___y_2020_);
v___y_2014_ = v___y_2019_;
v___y_2015_ = v___y_2021_;
v___y_2016_ = v___y_2022_;
v___y_2017_ = v___x_2025_;
goto v___jp_2013_;
}
else
{
v___y_2014_ = v___y_2019_;
v___y_2015_ = v___y_2021_;
v___y_2016_ = v___y_2022_;
v___y_2017_ = v___x_2024_;
goto v___jp_2013_;
}
}
v___jp_2026_:
{
uint32_t v___x_2031_; uint8_t v___x_2032_; 
v___x_2031_ = 97;
v___x_2032_ = lean_uint32_dec_le(v___x_2031_, v___y_2028_);
if (v___x_2032_ == 0)
{
v___y_2019_ = v___y_2027_;
v___y_2020_ = v___y_2028_;
v___y_2021_ = v___y_2029_;
v___y_2022_ = v___y_2030_;
goto v___jp_2018_;
}
else
{
uint32_t v___x_2033_; uint8_t v___x_2034_; 
v___x_2033_ = 122;
v___x_2034_ = lean_uint32_dec_le(v___y_2028_, v___x_2033_);
if (v___x_2034_ == 0)
{
v___y_2019_ = v___y_2027_;
v___y_2020_ = v___y_2028_;
v___y_2021_ = v___y_2029_;
v___y_2022_ = v___y_2030_;
goto v___jp_2018_;
}
else
{
v___y_2014_ = v___y_2027_;
v___y_2015_ = v___y_2029_;
v___y_2016_ = v___y_2030_;
v___y_2017_ = v___x_2034_;
goto v___jp_2013_;
}
}
}
v___jp_2035_:
{
lean_object* v___x_2038_; uint8_t v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; uint8_t v___x_2044_; lean_object* v___x_2045_; 
v___x_2038_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2039_ = 0;
v___x_2040_ = lean_box(v___x_2039_);
v___x_2041_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2038_, v___y_2037_, v___x_2040_);
lean_dec(v___x_2040_);
lean_dec_ref(v___y_2037_);
v___x_2042_ = lean_unsigned_to_nat(5u);
v___x_2043_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2043_, 0, v_x_2001_);
lean_ctor_set(v___x_2043_, 1, v___x_2042_);
v___x_2044_ = lean_unbox(v___x_2041_);
lean_dec(v___x_2041_);
lean_ctor_set_uint8(v___x_2043_, sizeof(void*)*2, v___x_2044_);
v___x_2045_ = lean_array_push(v___y_2036_, v___x_2043_);
return v___x_2045_;
}
v___jp_2046_:
{
if (v___y_2049_ == 0)
{
if (v___y_2050_ == 0)
{
lean_dec_ref(v___y_2048_);
lean_dec(v_x_2001_);
return v___y_2047_;
}
else
{
v___y_2036_ = v___y_2047_;
v___y_2037_ = v___y_2048_;
goto v___jp_2035_;
}
}
else
{
v___y_2036_ = v___y_2047_;
v___y_2037_ = v___y_2048_;
goto v___jp_2035_;
}
}
v___jp_2051_:
{
uint32_t v___x_2056_; uint8_t v___x_2057_; 
v___x_2056_ = 95;
v___x_2057_ = lean_uint32_dec_eq(v___y_2053_, v___x_2056_);
if (v___x_2057_ == 0)
{
uint8_t v___x_2058_; 
v___x_2058_ = l_Lean_isLetterLike(v___y_2053_);
v___y_2047_ = v___y_2052_;
v___y_2048_ = v___y_2054_;
v___y_2049_ = v___y_2055_;
v___y_2050_ = v___x_2058_;
goto v___jp_2046_;
}
else
{
v___y_2047_ = v___y_2052_;
v___y_2048_ = v___y_2054_;
v___y_2049_ = v___y_2055_;
v___y_2050_ = v___x_2057_;
goto v___jp_2046_;
}
}
v___jp_2059_:
{
uint32_t v___x_2064_; uint8_t v___x_2065_; 
v___x_2064_ = 97;
v___x_2065_ = lean_uint32_dec_le(v___x_2064_, v___y_2061_);
if (v___x_2065_ == 0)
{
v___y_2052_ = v___y_2060_;
v___y_2053_ = v___y_2061_;
v___y_2054_ = v___y_2062_;
v___y_2055_ = v___y_2063_;
goto v___jp_2051_;
}
else
{
uint32_t v___x_2066_; uint8_t v___x_2067_; 
v___x_2066_ = 122;
v___x_2067_ = lean_uint32_dec_le(v___y_2061_, v___x_2066_);
if (v___x_2067_ == 0)
{
v___y_2052_ = v___y_2060_;
v___y_2053_ = v___y_2061_;
v___y_2054_ = v___y_2062_;
v___y_2055_ = v___y_2063_;
goto v___jp_2051_;
}
else
{
v___y_2047_ = v___y_2060_;
v___y_2048_ = v___y_2062_;
v___y_2049_ = v___y_2063_;
v___y_2050_ = v___x_2067_;
goto v___jp_2046_;
}
}
}
v___jp_2068_:
{
lean_object* v___x_2071_; uint8_t v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; lean_object* v___x_2078_; 
v___x_2071_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2072_ = 0;
v___x_2073_ = lean_box(v___x_2072_);
v___x_2074_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2071_, v___y_2070_, v___x_2073_);
lean_dec(v___x_2073_);
lean_dec_ref(v___y_2070_);
v___x_2075_ = lean_unsigned_to_nat(5u);
v___x_2076_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2076_, 0, v_x_2001_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
v___x_2077_ = lean_unbox(v___x_2074_);
lean_dec(v___x_2074_);
lean_ctor_set_uint8(v___x_2076_, sizeof(void*)*2, v___x_2077_);
v___x_2078_ = lean_array_push(v___y_2069_, v___x_2076_);
return v___x_2078_;
}
v___jp_2079_:
{
if (v___y_2080_ == 0)
{
if (v___y_2083_ == 0)
{
lean_dec_ref(v___y_2082_);
lean_dec(v_x_2001_);
return v___y_2081_;
}
else
{
v___y_2069_ = v___y_2081_;
v___y_2070_ = v___y_2082_;
goto v___jp_2068_;
}
}
else
{
v___y_2069_ = v___y_2081_;
v___y_2070_ = v___y_2082_;
goto v___jp_2068_;
}
}
v___jp_2084_:
{
uint32_t v___x_2089_; uint8_t v___x_2090_; 
v___x_2089_ = 95;
v___x_2090_ = lean_uint32_dec_eq(v___y_2085_, v___x_2089_);
if (v___x_2090_ == 0)
{
uint8_t v___x_2091_; 
v___x_2091_ = l_Lean_isLetterLike(v___y_2085_);
v___y_2080_ = v___y_2086_;
v___y_2081_ = v___y_2087_;
v___y_2082_ = v___y_2088_;
v___y_2083_ = v___x_2091_;
goto v___jp_2079_;
}
else
{
v___y_2080_ = v___y_2086_;
v___y_2081_ = v___y_2087_;
v___y_2082_ = v___y_2088_;
v___y_2083_ = v___x_2090_;
goto v___jp_2079_;
}
}
v___jp_2092_:
{
uint32_t v___x_2097_; uint8_t v___x_2098_; 
v___x_2097_ = 97;
v___x_2098_ = lean_uint32_dec_le(v___x_2097_, v___y_2093_);
if (v___x_2098_ == 0)
{
v___y_2085_ = v___y_2093_;
v___y_2086_ = v___y_2094_;
v___y_2087_ = v___y_2095_;
v___y_2088_ = v___y_2096_;
goto v___jp_2084_;
}
else
{
uint32_t v___x_2099_; uint8_t v___x_2100_; 
v___x_2099_ = 122;
v___x_2100_ = lean_uint32_dec_le(v___y_2093_, v___x_2099_);
if (v___x_2100_ == 0)
{
v___y_2085_ = v___y_2093_;
v___y_2086_ = v___y_2094_;
v___y_2087_ = v___y_2095_;
v___y_2088_ = v___y_2096_;
goto v___jp_2084_;
}
else
{
v___y_2080_ = v___y_2094_;
v___y_2081_ = v___y_2095_;
v___y_2082_ = v___y_2096_;
v___y_2083_ = v___x_2100_;
goto v___jp_2079_;
}
}
}
v___jp_2101_:
{
lean_object* v___x_2104_; uint8_t v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; uint8_t v___x_2110_; lean_object* v___x_2111_; 
v___x_2104_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2105_ = 0;
v___x_2106_ = lean_box(v___x_2105_);
v___x_2107_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2104_, v___y_2103_, v___x_2106_);
lean_dec(v___x_2106_);
lean_dec_ref(v___y_2103_);
v___x_2108_ = lean_unsigned_to_nat(5u);
v___x_2109_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2109_, 0, v_x_2001_);
lean_ctor_set(v___x_2109_, 1, v___x_2108_);
v___x_2110_ = lean_unbox(v___x_2107_);
lean_dec(v___x_2107_);
lean_ctor_set_uint8(v___x_2109_, sizeof(void*)*2, v___x_2110_);
v___x_2111_ = lean_array_push(v___y_2102_, v___x_2109_);
return v___x_2111_;
}
v___jp_2112_:
{
if (v___y_2115_ == 0)
{
if (v___y_2116_ == 0)
{
lean_dec_ref(v___y_2114_);
lean_dec(v_x_2001_);
return v___y_2113_;
}
else
{
v___y_2102_ = v___y_2113_;
v___y_2103_ = v___y_2114_;
goto v___jp_2101_;
}
}
else
{
v___y_2102_ = v___y_2113_;
v___y_2103_ = v___y_2114_;
goto v___jp_2101_;
}
}
v___jp_2117_:
{
uint32_t v___x_2122_; uint8_t v___x_2123_; 
v___x_2122_ = 95;
v___x_2123_ = lean_uint32_dec_eq(v___y_2120_, v___x_2122_);
if (v___x_2123_ == 0)
{
uint8_t v___x_2124_; 
v___x_2124_ = l_Lean_isLetterLike(v___y_2120_);
v___y_2113_ = v___y_2118_;
v___y_2114_ = v___y_2119_;
v___y_2115_ = v___y_2121_;
v___y_2116_ = v___x_2124_;
goto v___jp_2112_;
}
else
{
v___y_2113_ = v___y_2118_;
v___y_2114_ = v___y_2119_;
v___y_2115_ = v___y_2121_;
v___y_2116_ = v___x_2123_;
goto v___jp_2112_;
}
}
v___jp_2125_:
{
uint32_t v___x_2130_; uint8_t v___x_2131_; 
v___x_2130_ = 97;
v___x_2131_ = lean_uint32_dec_le(v___x_2130_, v___y_2128_);
if (v___x_2131_ == 0)
{
v___y_2118_ = v___y_2126_;
v___y_2119_ = v___y_2127_;
v___y_2120_ = v___y_2128_;
v___y_2121_ = v___y_2129_;
goto v___jp_2117_;
}
else
{
uint32_t v___x_2132_; uint8_t v___x_2133_; 
v___x_2132_ = 122;
v___x_2133_ = lean_uint32_dec_le(v___y_2128_, v___x_2132_);
if (v___x_2133_ == 0)
{
v___y_2118_ = v___y_2126_;
v___y_2119_ = v___y_2127_;
v___y_2120_ = v___y_2128_;
v___y_2121_ = v___y_2129_;
goto v___jp_2117_;
}
else
{
v___y_2113_ = v___y_2126_;
v___y_2114_ = v___y_2127_;
v___y_2115_ = v___y_2129_;
v___y_2116_ = v___x_2133_;
goto v___jp_2112_;
}
}
}
v___jp_2134_:
{
lean_object* v___x_2137_; uint8_t v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; uint8_t v___x_2143_; lean_object* v___x_2144_; 
v___x_2137_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2138_ = 0;
v___x_2139_ = lean_box(v___x_2138_);
v___x_2140_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2137_, v___y_2136_, v___x_2139_);
lean_dec(v___x_2139_);
lean_dec_ref(v___y_2136_);
v___x_2141_ = lean_unsigned_to_nat(5u);
v___x_2142_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2142_, 0, v_x_2001_);
lean_ctor_set(v___x_2142_, 1, v___x_2141_);
v___x_2143_ = lean_unbox(v___x_2140_);
lean_dec(v___x_2140_);
lean_ctor_set_uint8(v___x_2142_, sizeof(void*)*2, v___x_2143_);
v___x_2144_ = lean_array_push(v___y_2135_, v___x_2142_);
return v___x_2144_;
}
v___jp_2145_:
{
if (v___y_2146_ == 0)
{
if (v___y_2149_ == 0)
{
lean_dec_ref(v___y_2148_);
lean_dec(v_x_2001_);
return v___y_2147_;
}
else
{
v___y_2135_ = v___y_2147_;
v___y_2136_ = v___y_2148_;
goto v___jp_2134_;
}
}
else
{
v___y_2135_ = v___y_2147_;
v___y_2136_ = v___y_2148_;
goto v___jp_2134_;
}
}
v___jp_2150_:
{
uint32_t v___x_2155_; uint8_t v___x_2156_; 
v___x_2155_ = 95;
v___x_2156_ = lean_uint32_dec_eq(v___y_2154_, v___x_2155_);
if (v___x_2156_ == 0)
{
uint8_t v___x_2157_; 
v___x_2157_ = l_Lean_isLetterLike(v___y_2154_);
v___y_2146_ = v___y_2151_;
v___y_2147_ = v___y_2152_;
v___y_2148_ = v___y_2153_;
v___y_2149_ = v___x_2157_;
goto v___jp_2145_;
}
else
{
v___y_2146_ = v___y_2151_;
v___y_2147_ = v___y_2152_;
v___y_2148_ = v___y_2153_;
v___y_2149_ = v___x_2156_;
goto v___jp_2145_;
}
}
v___jp_2158_:
{
uint32_t v___x_2163_; uint8_t v___x_2164_; 
v___x_2163_ = 97;
v___x_2164_ = lean_uint32_dec_le(v___x_2163_, v___y_2162_);
if (v___x_2164_ == 0)
{
v___y_2151_ = v___y_2159_;
v___y_2152_ = v___y_2160_;
v___y_2153_ = v___y_2161_;
v___y_2154_ = v___y_2162_;
goto v___jp_2150_;
}
else
{
uint32_t v___x_2165_; uint8_t v___x_2166_; 
v___x_2165_ = 122;
v___x_2166_ = lean_uint32_dec_le(v___y_2162_, v___x_2165_);
if (v___x_2166_ == 0)
{
v___y_2151_ = v___y_2159_;
v___y_2152_ = v___y_2160_;
v___y_2153_ = v___y_2161_;
v___y_2154_ = v___y_2162_;
goto v___jp_2150_;
}
else
{
v___y_2146_ = v___y_2159_;
v___y_2147_ = v___y_2160_;
v___y_2148_ = v___y_2161_;
v___y_2149_ = v___x_2166_;
goto v___jp_2145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(lean_object* v_text_2561_, size_t v_sz_2562_, size_t v_i_2563_, lean_object* v_bs_2564_){
_start:
{
uint8_t v___x_2565_; 
v___x_2565_ = lean_usize_dec_lt(v_i_2563_, v_sz_2562_);
if (v___x_2565_ == 0)
{
lean_dec_ref(v_text_2561_);
return v_bs_2564_;
}
else
{
lean_object* v_v_2566_; lean_object* v___x_2567_; lean_object* v_bs_x27_2568_; lean_object* v___x_2569_; size_t v___x_2570_; size_t v___x_2571_; lean_object* v___x_2572_; 
v_v_2566_ = lean_array_uget(v_bs_2564_, v_i_2563_);
v___x_2567_ = lean_unsigned_to_nat(0u);
v_bs_x27_2568_ = lean_array_uset(v_bs_2564_, v_i_2563_, v___x_2567_);
lean_inc_ref(v_text_2561_);
v___x_2569_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2561_, v_v_2566_);
v___x_2570_ = ((size_t)1ULL);
v___x_2571_ = lean_usize_add(v_i_2563_, v___x_2570_);
v___x_2572_ = lean_array_uset(v_bs_x27_2568_, v_i_2563_, v___x_2569_);
v_i_2563_ = v___x_2571_;
v_bs_2564_ = v___x_2572_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3___boxed(lean_object* v_text_2574_, lean_object* v_sz_2575_, lean_object* v_i_2576_, lean_object* v_bs_2577_){
_start:
{
size_t v_sz_boxed_2578_; size_t v_i_boxed_2579_; lean_object* v_res_2580_; 
v_sz_boxed_2578_ = lean_unbox_usize(v_sz_2575_);
lean_dec(v_sz_2575_);
v_i_boxed_2579_ = lean_unbox_usize(v_i_2576_);
lean_dec(v_i_2576_);
v_res_2580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2574_, v_sz_boxed_2578_, v_i_boxed_2579_, v_bs_2577_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(lean_object* v_00_u03b4_2581_, lean_object* v_t_2582_, lean_object* v_k_2583_, lean_object* v_fallback_2584_){
_start:
{
lean_object* v___x_2585_; 
v___x_2585_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v_t_2582_, v_k_2583_, v_fallback_2584_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___boxed(lean_object* v_00_u03b4_2586_, lean_object* v_t_2587_, lean_object* v_k_2588_, lean_object* v_fallback_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(v_00_u03b4_2586_, v_t_2587_, v_k_2588_, v_fallback_2589_);
lean_dec(v_fallback_2589_);
lean_dec_ref(v_k_2588_);
lean_dec(v_t_2587_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(lean_object* v_x_2591_, lean_object* v_info_2592_, lean_object* v_x_2593_){
_start:
{
if (lean_obj_tag(v_info_2592_) == 1)
{
lean_object* v_i_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2639_; 
v_i_2594_ = lean_ctor_get(v_info_2592_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v_info_2592_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2596_ = v_info_2592_;
v_isShared_2597_ = v_isSharedCheck_2639_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_i_2594_);
lean_dec(v_info_2592_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2639_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v_toElabInfo_2598_; lean_object* v_lctx_2599_; lean_object* v_expr_2600_; uint8_t v_isBinder_2601_; lean_object* v_stx_2602_; lean_object* v___x_2614_; 
v_toElabInfo_2598_ = lean_ctor_get(v_i_2594_, 0);
lean_inc_ref(v_toElabInfo_2598_);
v_lctx_2599_ = lean_ctor_get(v_i_2594_, 1);
lean_inc_ref(v_lctx_2599_);
v_expr_2600_ = lean_ctor_get(v_i_2594_, 3);
lean_inc_ref(v_expr_2600_);
v_isBinder_2601_ = lean_ctor_get_uint8(v_i_2594_, sizeof(void*)*4);
lean_dec_ref(v_i_2594_);
v_stx_2602_ = lean_ctor_get(v_toElabInfo_2598_, 1);
lean_inc(v_stx_2602_);
lean_dec_ref(v_toElabInfo_2598_);
v___x_2614_ = l_Lean_Syntax_getHeadInfo(v_stx_2602_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v___x_2615_; uint8_t v___x_2616_; 
lean_dec_ref_known(v___x_2614_, 4);
v___x_2615_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__10));
lean_inc(v_stx_2602_);
v___x_2616_ = l_Lean_Syntax_isOfKind(v_stx_2602_, v___x_2615_);
if (v___x_2616_ == 0)
{
lean_dec_ref(v_expr_2600_);
lean_dec_ref(v_lctx_2599_);
goto v___jp_2603_;
}
else
{
if (lean_obj_tag(v_expr_2600_) == 1)
{
lean_object* v_fvarId_2617_; lean_object* v___x_2618_; 
v_fvarId_2617_ = lean_ctor_get(v_expr_2600_, 0);
lean_inc(v_fvarId_2617_);
lean_dec_ref_known(v_expr_2600_, 1);
v___x_2618_ = lean_local_ctx_find(v_lctx_2599_, v_fvarId_2617_);
if (lean_obj_tag(v___x_2618_) == 1)
{
lean_object* v_val_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2637_; 
v_val_2619_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2621_ = v___x_2618_;
v_isShared_2622_ = v_isSharedCheck_2637_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_val_2619_);
lean_dec(v___x_2618_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2637_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
uint8_t v___x_2623_; 
v___x_2623_ = l_Lean_LocalDecl_isAuxDecl(v_val_2619_);
if (v___x_2623_ == 0)
{
uint8_t v___x_2624_; 
v___x_2624_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2619_);
lean_dec(v_val_2619_);
if (v___x_2624_ == 0)
{
uint8_t v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2629_; 
lean_del_object(v___x_2596_);
v___x_2625_ = 1;
v___x_2626_ = lean_unsigned_to_nat(5u);
v___x_2627_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2627_, 0, v_stx_2602_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
lean_ctor_set_uint8(v___x_2627_, sizeof(void*)*2, v___x_2625_);
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 0, v___x_2627_);
v___x_2629_ = v___x_2621_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2627_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
else
{
lean_del_object(v___x_2621_);
goto v___jp_2603_;
}
}
else
{
lean_dec(v_val_2619_);
if (v_isBinder_2601_ == 0)
{
lean_del_object(v___x_2621_);
goto v___jp_2603_;
}
else
{
uint8_t v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2635_; 
lean_del_object(v___x_2596_);
v___x_2631_ = 3;
v___x_2632_ = lean_unsigned_to_nat(5u);
v___x_2633_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2633_, 0, v_stx_2602_);
lean_ctor_set(v___x_2633_, 1, v___x_2632_);
lean_ctor_set_uint8(v___x_2633_, sizeof(void*)*2, v___x_2631_);
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 0, v___x_2633_);
v___x_2635_ = v___x_2621_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2633_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
}
else
{
lean_dec(v___x_2618_);
goto v___jp_2603_;
}
}
else
{
lean_dec_ref(v_expr_2600_);
lean_dec_ref(v_lctx_2599_);
goto v___jp_2603_;
}
}
}
else
{
lean_object* v___x_2638_; 
lean_dec(v___x_2614_);
lean_dec(v_stx_2602_);
lean_dec_ref(v_expr_2600_);
lean_dec_ref(v_lctx_2599_);
lean_del_object(v___x_2596_);
v___x_2638_ = lean_box(0);
return v___x_2638_;
}
v___jp_2603_:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; uint8_t v___x_2606_; 
lean_inc(v_stx_2602_);
v___x_2604_ = l_Lean_Syntax_getKind(v_stx_2602_);
v___x_2605_ = l_Lean_Parser_Term_identProjKind;
v___x_2606_ = lean_name_eq(v___x_2604_, v___x_2605_);
lean_dec(v___x_2604_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2607_; 
lean_dec(v_stx_2602_);
lean_del_object(v___x_2596_);
v___x_2607_ = lean_box(0);
return v___x_2607_;
}
else
{
uint8_t v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2612_; 
v___x_2608_ = 2;
v___x_2609_ = lean_unsigned_to_nat(5u);
v___x_2610_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2610_, 0, v_stx_2602_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*2, v___x_2608_);
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 0, v___x_2610_);
v___x_2612_ = v___x_2596_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2610_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
}
else
{
lean_object* v___x_2640_; 
lean_dec_ref(v_info_2592_);
v___x_2640_ = lean_box(0);
return v___x_2640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0___boxed(lean_object* v_x_2641_, lean_object* v_info_2642_, lean_object* v_x_2643_){
_start:
{
lean_object* v_res_2644_; 
v_res_2644_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(v_x_2641_, v_info_2642_, v_x_2643_);
lean_dec_ref(v_x_2643_);
lean_dec_ref(v_x_2641_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(lean_object* v_i_2646_){
_start:
{
lean_object* v___f_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___f_2647_ = ((lean_object*)(l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___closed__0));
v___x_2648_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_2647_, v_i_2646_);
v___x_2649_ = lean_array_mk(v___x_2648_);
return v___x_2649_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_dbgShowTokens___lam__0(lean_object* v_x_2650_, lean_object* v_y_2651_){
_start:
{
lean_object* v_fst_2652_; lean_object* v_fst_2653_; uint8_t v___x_2654_; 
v_fst_2652_ = lean_ctor_get(v_x_2650_, 0);
v_fst_2653_ = lean_ctor_get(v_y_2651_, 0);
v___x_2654_ = lean_nat_dec_le(v_fst_2652_, v_fst_2653_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___lam__0___boxed(lean_object* v_x_2655_, lean_object* v_y_2656_){
_start:
{
uint8_t v_res_2657_; lean_object* v_r_2658_; 
v_res_2657_ = l_Lean_Server_FileWorker_dbgShowTokens___lam__0(v_x_2655_, v_y_2656_);
lean_dec_ref(v_y_2656_);
lean_dec_ref(v_x_2655_);
v_r_2658_ = lean_box(v_res_2657_);
return v_r_2658_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(lean_object* v_x_2659_, lean_object* v_x_2660_){
_start:
{
if (lean_obj_tag(v_x_2660_) == 0)
{
lean_inc(v_x_2659_);
return v_x_2659_;
}
else
{
lean_object* v_key_2661_; lean_object* v_value_2662_; lean_object* v_tail_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v_key_2661_ = lean_ctor_get(v_x_2660_, 0);
v_value_2662_ = lean_ctor_get(v_x_2660_, 1);
v_tail_2663_ = lean_ctor_get(v_x_2660_, 2);
v___x_2664_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_2659_, v_tail_2663_);
lean_inc(v_value_2662_);
lean_inc(v_key_2661_);
v___x_2665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2665_, 0, v_key_2661_);
lean_ctor_set(v___x_2665_, 1, v_value_2662_);
v___x_2666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2665_);
lean_ctor_set(v___x_2666_, 1, v___x_2664_);
return v___x_2666_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5___boxed(lean_object* v_x_2667_, lean_object* v_x_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_2667_, v_x_2668_);
lean_dec(v_x_2668_);
lean_dec(v_x_2667_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(lean_object* v_as_2670_, size_t v_i_2671_, size_t v_stop_2672_, lean_object* v_b_2673_){
_start:
{
uint8_t v___x_2674_; 
v___x_2674_ = lean_usize_dec_eq(v_i_2671_, v_stop_2672_);
if (v___x_2674_ == 0)
{
size_t v___x_2675_; size_t v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2675_ = ((size_t)1ULL);
v___x_2676_ = lean_usize_sub(v_i_2671_, v___x_2675_);
v___x_2677_ = lean_array_uget_borrowed(v_as_2670_, v___x_2676_);
v___x_2678_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_b_2673_, v___x_2677_);
lean_dec(v_b_2673_);
v_i_2671_ = v___x_2676_;
v_b_2673_ = v___x_2678_;
goto _start;
}
else
{
return v_b_2673_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6___boxed(lean_object* v_as_2680_, lean_object* v_i_2681_, lean_object* v_stop_2682_, lean_object* v_b_2683_){
_start:
{
size_t v_i_boxed_2684_; size_t v_stop_boxed_2685_; lean_object* v_res_2686_; 
v_i_boxed_2684_ = lean_unbox_usize(v_i_2681_);
lean_dec(v_i_2681_);
v_stop_boxed_2685_ = lean_unbox_usize(v_stop_2682_);
lean_dec(v_stop_2682_);
v_res_2686_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_as_2680_, v_i_boxed_2684_, v_stop_boxed_2685_, v_b_2683_);
lean_dec_ref(v_as_2680_);
return v_res_2686_;
}
}
LEAN_EXPORT uint8_t l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(lean_object* v_x_2687_, lean_object* v_y_2688_){
_start:
{
lean_object* v_fst_2689_; lean_object* v_fst_2690_; uint8_t v___x_2691_; 
v_fst_2689_ = lean_ctor_get(v_x_2687_, 0);
v_fst_2690_ = lean_ctor_get(v_y_2688_, 0);
v___x_2691_ = lean_nat_dec_le(v_fst_2689_, v_fst_2690_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0___boxed(lean_object* v_x_2692_, lean_object* v_y_2693_){
_start:
{
uint8_t v_res_2694_; lean_object* v_r_2695_; 
v_res_2694_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(v_x_2692_, v_y_2693_);
lean_dec_ref(v_y_2693_);
lean_dec_ref(v_x_2692_);
v_r_2695_ = lean_box(v_res_2694_);
return v_r_2695_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(lean_object* v_x_2699_, lean_object* v_x_2700_){
_start:
{
if (lean_obj_tag(v_x_2700_) == 0)
{
return v_x_2699_;
}
else
{
lean_object* v_head_2701_; lean_object* v_snd_2702_; lean_object* v_snd_2703_; lean_object* v_tail_2704_; lean_object* v_fst_2705_; lean_object* v_fst_2706_; lean_object* v_fst_2707_; lean_object* v_snd_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; uint8_t v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v_fst_2718_; lean_object* v_snd_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v_head_2701_ = lean_ctor_get(v_x_2700_, 0);
lean_inc(v_head_2701_);
v_snd_2702_ = lean_ctor_get(v_head_2701_, 1);
lean_inc(v_snd_2702_);
v_snd_2703_ = lean_ctor_get(v_snd_2702_, 1);
lean_inc(v_snd_2703_);
v_tail_2704_ = lean_ctor_get(v_x_2700_, 1);
lean_inc(v_tail_2704_);
lean_dec_ref_known(v_x_2700_, 2);
v_fst_2705_ = lean_ctor_get(v_head_2701_, 0);
lean_inc(v_fst_2705_);
lean_dec(v_head_2701_);
v_fst_2706_ = lean_ctor_get(v_snd_2702_, 0);
lean_inc(v_fst_2706_);
lean_dec(v_snd_2702_);
v_fst_2707_ = lean_ctor_get(v_snd_2703_, 0);
lean_inc(v_fst_2707_);
v_snd_2708_ = lean_ctor_get(v_snd_2703_, 1);
lean_inc(v_snd_2708_);
lean_dec(v_snd_2703_);
v___x_2709_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_2710_ = l_Nat_reprFast(v_fst_2705_);
v___x_2711_ = lean_string_append(v___x_2709_, v___x_2710_);
lean_dec_ref(v___x_2710_);
v___x_2712_ = lean_box(0);
v___x_2713_ = 0;
v___x_2714_ = l_Lean_Syntax_formatStx(v_fst_2707_, v___x_2712_, v___x_2713_);
v___x_2715_ = l_Std_Format_defWidth;
v___x_2716_ = lean_unsigned_to_nat(0u);
v___x_2717_ = l_Std_Format_pretty(v___x_2714_, v___x_2715_, v___x_2716_, v___x_2716_);
v_fst_2718_ = lean_ctor_get(v_snd_2708_, 0);
lean_inc(v_fst_2718_);
v_snd_2719_ = lean_ctor_get(v_snd_2708_, 1);
lean_inc(v_snd_2719_);
lean_dec(v_snd_2708_);
v___x_2720_ = l_Nat_reprFast(v_fst_2706_);
v___x_2721_ = lean_string_append(v___x_2709_, v___x_2720_);
lean_dec_ref(v___x_2720_);
v___x_2722_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_2723_ = lean_string_append(v_x_2699_, v___x_2722_);
v___x_2724_ = lean_string_append(v___x_2711_, v___x_2722_);
v___x_2725_ = lean_string_append(v___x_2721_, v___x_2722_);
v___x_2726_ = lean_string_append(v___x_2709_, v___x_2717_);
lean_dec_ref(v___x_2717_);
v___x_2727_ = lean_string_append(v___x_2726_, v___x_2722_);
v___x_2728_ = lean_unsigned_to_nat(80u);
v___x_2729_ = l_Lean_Json_pretty(v_fst_2718_, v___x_2728_);
v___x_2730_ = lean_string_append(v___x_2709_, v___x_2729_);
lean_dec_ref(v___x_2729_);
v___x_2731_ = lean_string_append(v___x_2730_, v___x_2722_);
v___x_2732_ = l_Nat_reprFast(v_snd_2719_);
v___x_2733_ = lean_string_append(v___x_2731_, v___x_2732_);
lean_dec_ref(v___x_2732_);
v___x_2734_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_2735_ = lean_string_append(v___x_2733_, v___x_2734_);
v___x_2736_ = lean_string_append(v___x_2727_, v___x_2735_);
lean_dec_ref(v___x_2735_);
v___x_2737_ = lean_string_append(v___x_2736_, v___x_2734_);
v___x_2738_ = lean_string_append(v___x_2725_, v___x_2737_);
lean_dec_ref(v___x_2737_);
v___x_2739_ = lean_string_append(v___x_2738_, v___x_2734_);
v___x_2740_ = lean_string_append(v___x_2724_, v___x_2739_);
lean_dec_ref(v___x_2739_);
v___x_2741_ = lean_string_append(v___x_2740_, v___x_2734_);
v___x_2742_ = lean_string_append(v___x_2723_, v___x_2741_);
lean_dec_ref(v___x_2741_);
v_x_2699_ = v___x_2742_;
v_x_2700_ = v_tail_2704_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(lean_object* v_x_2747_){
_start:
{
if (lean_obj_tag(v_x_2747_) == 0)
{
lean_object* v___x_2748_; 
v___x_2748_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__0));
return v___x_2748_;
}
else
{
lean_object* v_tail_2749_; 
v_tail_2749_ = lean_ctor_get(v_x_2747_, 1);
if (lean_obj_tag(v_tail_2749_) == 0)
{
lean_object* v_head_2750_; lean_object* v_snd_2751_; lean_object* v_snd_2752_; lean_object* v_fst_2753_; lean_object* v_fst_2754_; lean_object* v_fst_2755_; lean_object* v_snd_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; uint8_t v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v_fst_2766_; lean_object* v_snd_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v_head_2750_ = lean_ctor_get(v_x_2747_, 0);
lean_inc(v_head_2750_);
lean_dec_ref_known(v_x_2747_, 2);
v_snd_2751_ = lean_ctor_get(v_head_2750_, 1);
lean_inc(v_snd_2751_);
v_snd_2752_ = lean_ctor_get(v_snd_2751_, 1);
lean_inc(v_snd_2752_);
v_fst_2753_ = lean_ctor_get(v_head_2750_, 0);
lean_inc(v_fst_2753_);
lean_dec(v_head_2750_);
v_fst_2754_ = lean_ctor_get(v_snd_2751_, 0);
lean_inc(v_fst_2754_);
lean_dec(v_snd_2751_);
v_fst_2755_ = lean_ctor_get(v_snd_2752_, 0);
lean_inc(v_fst_2755_);
v_snd_2756_ = lean_ctor_get(v_snd_2752_, 1);
lean_inc(v_snd_2756_);
lean_dec(v_snd_2752_);
v___x_2757_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_2758_ = l_Nat_reprFast(v_fst_2753_);
v___x_2759_ = lean_string_append(v___x_2757_, v___x_2758_);
lean_dec_ref(v___x_2758_);
v___x_2760_ = lean_box(0);
v___x_2761_ = 0;
v___x_2762_ = l_Lean_Syntax_formatStx(v_fst_2755_, v___x_2760_, v___x_2761_);
v___x_2763_ = l_Std_Format_defWidth;
v___x_2764_ = lean_unsigned_to_nat(0u);
v___x_2765_ = l_Std_Format_pretty(v___x_2762_, v___x_2763_, v___x_2764_, v___x_2764_);
v_fst_2766_ = lean_ctor_get(v_snd_2756_, 0);
lean_inc(v_fst_2766_);
v_snd_2767_ = lean_ctor_get(v_snd_2756_, 1);
lean_inc(v_snd_2767_);
lean_dec(v_snd_2756_);
v___x_2768_ = l_Nat_reprFast(v_fst_2754_);
v___x_2769_ = lean_string_append(v___x_2757_, v___x_2768_);
lean_dec_ref(v___x_2768_);
v___x_2770_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_2771_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_2772_ = lean_string_append(v___x_2759_, v___x_2771_);
v___x_2773_ = lean_string_append(v___x_2769_, v___x_2771_);
v___x_2774_ = lean_string_append(v___x_2757_, v___x_2765_);
lean_dec_ref(v___x_2765_);
v___x_2775_ = lean_string_append(v___x_2774_, v___x_2771_);
v___x_2776_ = lean_unsigned_to_nat(80u);
v___x_2777_ = l_Lean_Json_pretty(v_fst_2766_, v___x_2776_);
v___x_2778_ = lean_string_append(v___x_2757_, v___x_2777_);
lean_dec_ref(v___x_2777_);
v___x_2779_ = lean_string_append(v___x_2778_, v___x_2771_);
v___x_2780_ = l_Nat_reprFast(v_snd_2767_);
v___x_2781_ = lean_string_append(v___x_2779_, v___x_2780_);
lean_dec_ref(v___x_2780_);
v___x_2782_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_2783_ = lean_string_append(v___x_2781_, v___x_2782_);
v___x_2784_ = lean_string_append(v___x_2775_, v___x_2783_);
lean_dec_ref(v___x_2783_);
v___x_2785_ = lean_string_append(v___x_2784_, v___x_2782_);
v___x_2786_ = lean_string_append(v___x_2773_, v___x_2785_);
lean_dec_ref(v___x_2785_);
v___x_2787_ = lean_string_append(v___x_2786_, v___x_2782_);
v___x_2788_ = lean_string_append(v___x_2772_, v___x_2787_);
lean_dec_ref(v___x_2787_);
v___x_2789_ = lean_string_append(v___x_2788_, v___x_2782_);
v___x_2790_ = lean_string_append(v___x_2770_, v___x_2789_);
lean_dec_ref(v___x_2789_);
v___x_2791_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__2));
v___x_2792_ = lean_string_append(v___x_2790_, v___x_2791_);
return v___x_2792_;
}
else
{
lean_object* v_head_2793_; lean_object* v_snd_2794_; lean_object* v_snd_2795_; lean_object* v_fst_2796_; lean_object* v_fst_2797_; lean_object* v_fst_2798_; lean_object* v_snd_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; uint8_t v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v_fst_2809_; lean_object* v_snd_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; uint32_t v___x_2835_; lean_object* v___x_2836_; 
lean_inc(v_tail_2749_);
v_head_2793_ = lean_ctor_get(v_x_2747_, 0);
lean_inc(v_head_2793_);
lean_dec_ref_known(v_x_2747_, 2);
v_snd_2794_ = lean_ctor_get(v_head_2793_, 1);
lean_inc(v_snd_2794_);
v_snd_2795_ = lean_ctor_get(v_snd_2794_, 1);
lean_inc(v_snd_2795_);
v_fst_2796_ = lean_ctor_get(v_head_2793_, 0);
lean_inc(v_fst_2796_);
lean_dec(v_head_2793_);
v_fst_2797_ = lean_ctor_get(v_snd_2794_, 0);
lean_inc(v_fst_2797_);
lean_dec(v_snd_2794_);
v_fst_2798_ = lean_ctor_get(v_snd_2795_, 0);
lean_inc(v_fst_2798_);
v_snd_2799_ = lean_ctor_get(v_snd_2795_, 1);
lean_inc(v_snd_2799_);
lean_dec(v_snd_2795_);
v___x_2800_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_2801_ = l_Nat_reprFast(v_fst_2796_);
v___x_2802_ = lean_string_append(v___x_2800_, v___x_2801_);
lean_dec_ref(v___x_2801_);
v___x_2803_ = lean_box(0);
v___x_2804_ = 0;
v___x_2805_ = l_Lean_Syntax_formatStx(v_fst_2798_, v___x_2803_, v___x_2804_);
v___x_2806_ = l_Std_Format_defWidth;
v___x_2807_ = lean_unsigned_to_nat(0u);
v___x_2808_ = l_Std_Format_pretty(v___x_2805_, v___x_2806_, v___x_2807_, v___x_2807_);
v_fst_2809_ = lean_ctor_get(v_snd_2799_, 0);
lean_inc(v_fst_2809_);
v_snd_2810_ = lean_ctor_get(v_snd_2799_, 1);
lean_inc(v_snd_2810_);
lean_dec(v_snd_2799_);
v___x_2811_ = l_Nat_reprFast(v_fst_2797_);
v___x_2812_ = lean_string_append(v___x_2800_, v___x_2811_);
lean_dec_ref(v___x_2811_);
v___x_2813_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_2814_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_2815_ = lean_string_append(v___x_2802_, v___x_2814_);
v___x_2816_ = lean_string_append(v___x_2812_, v___x_2814_);
v___x_2817_ = lean_string_append(v___x_2800_, v___x_2808_);
lean_dec_ref(v___x_2808_);
v___x_2818_ = lean_string_append(v___x_2817_, v___x_2814_);
v___x_2819_ = lean_unsigned_to_nat(80u);
v___x_2820_ = l_Lean_Json_pretty(v_fst_2809_, v___x_2819_);
v___x_2821_ = lean_string_append(v___x_2800_, v___x_2820_);
lean_dec_ref(v___x_2820_);
v___x_2822_ = lean_string_append(v___x_2821_, v___x_2814_);
v___x_2823_ = l_Nat_reprFast(v_snd_2810_);
v___x_2824_ = lean_string_append(v___x_2822_, v___x_2823_);
lean_dec_ref(v___x_2823_);
v___x_2825_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_2826_ = lean_string_append(v___x_2824_, v___x_2825_);
v___x_2827_ = lean_string_append(v___x_2818_, v___x_2826_);
lean_dec_ref(v___x_2826_);
v___x_2828_ = lean_string_append(v___x_2827_, v___x_2825_);
v___x_2829_ = lean_string_append(v___x_2816_, v___x_2828_);
lean_dec_ref(v___x_2828_);
v___x_2830_ = lean_string_append(v___x_2829_, v___x_2825_);
v___x_2831_ = lean_string_append(v___x_2815_, v___x_2830_);
lean_dec_ref(v___x_2830_);
v___x_2832_ = lean_string_append(v___x_2831_, v___x_2825_);
v___x_2833_ = lean_string_append(v___x_2813_, v___x_2832_);
lean_dec_ref(v___x_2832_);
v___x_2834_ = l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(v___x_2833_, v_tail_2749_);
v___x_2835_ = 93;
v___x_2836_ = lean_string_push(v___x_2834_, v___x_2835_);
return v___x_2836_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(lean_object* v_a_2837_, lean_object* v_a_2838_){
_start:
{
if (lean_obj_tag(v_a_2837_) == 0)
{
lean_object* v___x_2839_; 
v___x_2839_ = l_List_reverse___redArg(v_a_2838_);
return v___x_2839_;
}
else
{
lean_object* v_head_2840_; lean_object* v_snd_2841_; lean_object* v_snd_2842_; lean_object* v_tail_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2875_; 
v_head_2840_ = lean_ctor_get(v_a_2837_, 0);
lean_inc(v_head_2840_);
v_snd_2841_ = lean_ctor_get(v_head_2840_, 1);
lean_inc(v_snd_2841_);
v_snd_2842_ = lean_ctor_get(v_snd_2841_, 1);
lean_inc(v_snd_2842_);
v_tail_2843_ = lean_ctor_get(v_a_2837_, 1);
v_isSharedCheck_2875_ = !lean_is_exclusive(v_a_2837_);
if (v_isSharedCheck_2875_ == 0)
{
lean_object* v_unused_2876_; 
v_unused_2876_ = lean_ctor_get(v_a_2837_, 0);
lean_dec(v_unused_2876_);
v___x_2845_ = v_a_2837_;
v_isShared_2846_ = v_isSharedCheck_2875_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_tail_2843_);
lean_dec(v_a_2837_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2875_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v_fst_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2873_; 
v_fst_2847_ = lean_ctor_get(v_head_2840_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v_head_2840_);
if (v_isSharedCheck_2873_ == 0)
{
lean_object* v_unused_2874_; 
v_unused_2874_ = lean_ctor_get(v_head_2840_, 1);
lean_dec(v_unused_2874_);
v___x_2849_ = v_head_2840_;
v_isShared_2850_ = v_isSharedCheck_2873_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_fst_2847_);
lean_dec(v_head_2840_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2873_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v_fst_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2871_; 
v_fst_2851_ = lean_ctor_get(v_snd_2841_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v_snd_2841_);
if (v_isSharedCheck_2871_ == 0)
{
lean_object* v_unused_2872_; 
v_unused_2872_ = lean_ctor_get(v_snd_2841_, 1);
lean_dec(v_unused_2872_);
v___x_2853_ = v_snd_2841_;
v_isShared_2854_ = v_isSharedCheck_2871_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_fst_2851_);
lean_dec(v_snd_2841_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2871_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v_stx_2855_; uint8_t v_type_2856_; lean_object* v_priority_2857_; lean_object* v___x_2858_; lean_object* v___x_2860_; 
v_stx_2855_ = lean_ctor_get(v_snd_2842_, 0);
lean_inc(v_stx_2855_);
v_type_2856_ = lean_ctor_get_uint8(v_snd_2842_, sizeof(void*)*2);
v_priority_2857_ = lean_ctor_get(v_snd_2842_, 1);
lean_inc(v_priority_2857_);
lean_dec(v_snd_2842_);
v___x_2858_ = l_Lean_Lsp_instToJsonSemanticTokenType_toJson(v_type_2856_);
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 1, v_priority_2857_);
lean_ctor_set(v___x_2853_, 0, v___x_2858_);
v___x_2860_ = v___x_2853_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2858_);
lean_ctor_set(v_reuseFailAlloc_2870_, 1, v_priority_2857_);
v___x_2860_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
lean_object* v___x_2862_; 
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 1, v___x_2860_);
lean_ctor_set(v___x_2849_, 0, v_stx_2855_);
v___x_2862_ = v___x_2849_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_stx_2855_);
lean_ctor_set(v_reuseFailAlloc_2869_, 1, v___x_2860_);
v___x_2862_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2866_; 
v___x_2863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2863_, 0, v_fst_2851_);
lean_ctor_set(v___x_2863_, 1, v___x_2862_);
v___x_2864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2864_, 0, v_fst_2847_);
lean_ctor_set(v___x_2864_, 1, v___x_2863_);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 1, v_a_2838_);
lean_ctor_set(v___x_2845_, 0, v___x_2864_);
v___x_2866_ = v___x_2845_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2864_);
lean_ctor_set(v_reuseFailAlloc_2868_, 1, v_a_2838_);
v___x_2866_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
v_a_2837_ = v_tail_2843_;
v_a_2838_ = v___x_2866_;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(lean_object* v_as_x27_2879_, lean_object* v_b_2880_){
_start:
{
if (lean_obj_tag(v_as_x27_2879_) == 0)
{
return v_b_2880_;
}
else
{
lean_object* v_head_2881_; lean_object* v_tail_2882_; lean_object* v_fst_2883_; lean_object* v_snd_2884_; lean_object* v___f_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v_head_2881_ = lean_ctor_get(v_as_x27_2879_, 0);
v_tail_2882_ = lean_ctor_get(v_as_x27_2879_, 1);
v_fst_2883_ = lean_ctor_get(v_head_2881_, 0);
v_snd_2884_ = lean_ctor_get(v_head_2881_, 1);
v___f_2885_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__0));
lean_inc(v_snd_2884_);
v___x_2886_ = lean_array_to_list(v_snd_2884_);
v___x_2887_ = l_List_mergeSort___redArg(v___x_2886_, v___f_2885_);
lean_inc(v_fst_2883_);
v___x_2888_ = l_Nat_reprFast(v_fst_2883_);
v___x_2889_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__1));
v___x_2890_ = lean_string_append(v___x_2888_, v___x_2889_);
v___x_2891_ = lean_box(0);
v___x_2892_ = l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(v___x_2887_, v___x_2891_);
v___x_2893_ = l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(v___x_2892_);
v___x_2894_ = lean_string_append(v___x_2890_, v___x_2893_);
lean_dec_ref(v___x_2893_);
v___x_2895_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0));
v___x_2896_ = lean_string_append(v___x_2894_, v___x_2895_);
v___x_2897_ = lean_string_append(v_b_2880_, v___x_2896_);
lean_dec_ref(v___x_2896_);
v_as_x27_2879_ = v_tail_2882_;
v_b_2880_ = v___x_2897_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___boxed(lean_object* v_as_x27_2899_, lean_object* v_b_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v_as_x27_2899_, v_b_2900_);
lean_dec(v_as_x27_2899_);
return v_res_2901_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(lean_object* v_a_2902_, lean_object* v_x_2903_){
_start:
{
if (lean_obj_tag(v_x_2903_) == 0)
{
uint8_t v___x_2904_; 
v___x_2904_ = 0;
return v___x_2904_;
}
else
{
lean_object* v_key_2905_; lean_object* v_tail_2906_; uint8_t v___x_2907_; 
v_key_2905_ = lean_ctor_get(v_x_2903_, 0);
v_tail_2906_ = lean_ctor_get(v_x_2903_, 2);
v___x_2907_ = lean_nat_dec_eq(v_key_2905_, v_a_2902_);
if (v___x_2907_ == 0)
{
v_x_2903_ = v_tail_2906_;
goto _start;
}
else
{
return v___x_2907_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg___boxed(lean_object* v_a_2909_, lean_object* v_x_2910_){
_start:
{
uint8_t v_res_2911_; lean_object* v_r_2912_; 
v_res_2911_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_2909_, v_x_2910_);
lean_dec(v_x_2910_);
lean_dec(v_a_2909_);
v_r_2912_ = lean_box(v_res_2911_);
return v_r_2912_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(lean_object* v_x_2913_, lean_object* v_x_2914_){
_start:
{
if (lean_obj_tag(v_x_2914_) == 0)
{
return v_x_2913_;
}
else
{
lean_object* v_key_2915_; lean_object* v_value_2916_; lean_object* v_tail_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2940_; 
v_key_2915_ = lean_ctor_get(v_x_2914_, 0);
v_value_2916_ = lean_ctor_get(v_x_2914_, 1);
v_tail_2917_ = lean_ctor_get(v_x_2914_, 2);
v_isSharedCheck_2940_ = !lean_is_exclusive(v_x_2914_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2919_ = v_x_2914_;
v_isShared_2920_ = v_isSharedCheck_2940_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_tail_2917_);
lean_inc(v_value_2916_);
lean_inc(v_key_2915_);
lean_dec(v_x_2914_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2940_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2921_; uint64_t v___x_2922_; uint64_t v___x_2923_; uint64_t v___x_2924_; uint64_t v_fold_2925_; uint64_t v___x_2926_; uint64_t v___x_2927_; uint64_t v___x_2928_; size_t v___x_2929_; size_t v___x_2930_; size_t v___x_2931_; size_t v___x_2932_; size_t v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2936_; 
v___x_2921_ = lean_array_get_size(v_x_2913_);
v___x_2922_ = lean_uint64_of_nat(v_key_2915_);
v___x_2923_ = 32ULL;
v___x_2924_ = lean_uint64_shift_right(v___x_2922_, v___x_2923_);
v_fold_2925_ = lean_uint64_xor(v___x_2922_, v___x_2924_);
v___x_2926_ = 16ULL;
v___x_2927_ = lean_uint64_shift_right(v_fold_2925_, v___x_2926_);
v___x_2928_ = lean_uint64_xor(v_fold_2925_, v___x_2927_);
v___x_2929_ = lean_uint64_to_usize(v___x_2928_);
v___x_2930_ = lean_usize_of_nat(v___x_2921_);
v___x_2931_ = ((size_t)1ULL);
v___x_2932_ = lean_usize_sub(v___x_2930_, v___x_2931_);
v___x_2933_ = lean_usize_land(v___x_2929_, v___x_2932_);
v___x_2934_ = lean_array_uget_borrowed(v_x_2913_, v___x_2933_);
lean_inc(v___x_2934_);
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 2, v___x_2934_);
v___x_2936_ = v___x_2919_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_key_2915_);
lean_ctor_set(v_reuseFailAlloc_2939_, 1, v_value_2916_);
lean_ctor_set(v_reuseFailAlloc_2939_, 2, v___x_2934_);
v___x_2936_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
lean_object* v___x_2937_; 
v___x_2937_ = lean_array_uset(v_x_2913_, v___x_2933_, v___x_2936_);
v_x_2913_ = v___x_2937_;
v_x_2914_ = v_tail_2917_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(lean_object* v_i_2941_, lean_object* v_source_2942_, lean_object* v_target_2943_){
_start:
{
lean_object* v___x_2944_; uint8_t v___x_2945_; 
v___x_2944_ = lean_array_get_size(v_source_2942_);
v___x_2945_ = lean_nat_dec_lt(v_i_2941_, v___x_2944_);
if (v___x_2945_ == 0)
{
lean_dec_ref(v_source_2942_);
lean_dec(v_i_2941_);
return v_target_2943_;
}
else
{
lean_object* v_es_2946_; lean_object* v___x_2947_; lean_object* v_source_2948_; lean_object* v_target_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v_es_2946_ = lean_array_fget(v_source_2942_, v_i_2941_);
v___x_2947_ = lean_box(0);
v_source_2948_ = lean_array_fset(v_source_2942_, v_i_2941_, v___x_2947_);
v_target_2949_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_target_2943_, v_es_2946_);
v___x_2950_ = lean_unsigned_to_nat(1u);
v___x_2951_ = lean_nat_add(v_i_2941_, v___x_2950_);
lean_dec(v_i_2941_);
v_i_2941_ = v___x_2951_;
v_source_2942_ = v_source_2948_;
v_target_2943_ = v_target_2949_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(lean_object* v_data_2953_){
_start:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v_nbuckets_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2954_ = lean_array_get_size(v_data_2953_);
v___x_2955_ = lean_unsigned_to_nat(2u);
v_nbuckets_2956_ = lean_nat_mul(v___x_2954_, v___x_2955_);
v___x_2957_ = lean_unsigned_to_nat(0u);
v___x_2958_ = lean_box(0);
v___x_2959_ = lean_mk_array(v_nbuckets_2956_, v___x_2958_);
v___x_2960_ = lean_array_propagate_mark(v_data_2953_, v___x_2959_);
v___x_2961_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v___x_2957_, v_data_2953_, v___x_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(lean_object* v_character_2964_, lean_object* v_a_2965_, lean_object* v_character_2966_, lean_object* v_x_x3f_2967_){
_start:
{
lean_object* v___y_2969_; 
if (lean_obj_tag(v_x_x3f_2967_) == 0)
{
lean_object* v___x_2974_; 
v___x_2974_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___y_2969_ = v___x_2974_;
goto v___jp_2968_;
}
else
{
lean_object* v_val_2975_; 
v_val_2975_ = lean_ctor_get(v_x_x3f_2967_, 0);
lean_inc(v_val_2975_);
lean_dec_ref_known(v_x_x3f_2967_, 1);
v___y_2969_ = v_val_2975_;
goto v___jp_2968_;
}
v___jp_2968_:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2970_, 0, v_character_2964_);
lean_ctor_set(v___x_2970_, 1, v_a_2965_);
v___x_2971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2971_, 0, v_character_2966_);
lean_ctor_set(v___x_2971_, 1, v___x_2970_);
v___x_2972_ = lean_array_push(v___y_2969_, v___x_2971_);
v___x_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2972_);
return v___x_2973_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(lean_object* v_character_2976_, lean_object* v_a_2977_, lean_object* v_character_2978_, lean_object* v_a_2979_, lean_object* v_x_2980_){
_start:
{
if (lean_obj_tag(v_x_2980_) == 0)
{
lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v_val_2983_; lean_object* v___x_2984_; 
v___x_2981_ = lean_box(0);
v___x_2982_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_2976_, v_a_2977_, v_character_2978_, v___x_2981_);
v_val_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_val_2983_);
lean_dec(v___x_2982_);
v___x_2984_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2984_, 0, v_a_2979_);
lean_ctor_set(v___x_2984_, 1, v_val_2983_);
lean_ctor_set(v___x_2984_, 2, v_x_2980_);
return v___x_2984_;
}
else
{
lean_object* v_key_2985_; lean_object* v_value_2986_; lean_object* v_tail_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_3002_; 
v_key_2985_ = lean_ctor_get(v_x_2980_, 0);
v_value_2986_ = lean_ctor_get(v_x_2980_, 1);
v_tail_2987_ = lean_ctor_get(v_x_2980_, 2);
v_isSharedCheck_3002_ = !lean_is_exclusive(v_x_2980_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2989_ = v_x_2980_;
v_isShared_2990_ = v_isSharedCheck_3002_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_tail_2987_);
lean_inc(v_value_2986_);
lean_inc(v_key_2985_);
lean_dec(v_x_2980_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_3002_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
uint8_t v___x_2991_; 
v___x_2991_ = lean_nat_dec_eq(v_key_2985_, v_a_2979_);
if (v___x_2991_ == 0)
{
lean_object* v_tail_2992_; lean_object* v___x_2994_; 
v_tail_2992_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_2976_, v_a_2977_, v_character_2978_, v_a_2979_, v_tail_2987_);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 2, v_tail_2992_);
v___x_2994_ = v___x_2989_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_key_2985_);
lean_ctor_set(v_reuseFailAlloc_2995_, 1, v_value_2986_);
lean_ctor_set(v_reuseFailAlloc_2995_, 2, v_tail_2992_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
else
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v_val_2998_; lean_object* v___x_3000_; 
lean_dec(v_key_2985_);
v___x_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2996_, 0, v_value_2986_);
v___x_2997_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_2976_, v_a_2977_, v_character_2978_, v___x_2996_);
v_val_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_val_2998_);
lean_dec(v___x_2997_);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 1, v_val_2998_);
lean_ctor_set(v___x_2989_, 0, v_a_2979_);
v___x_3000_ = v___x_2989_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2979_);
lean_ctor_set(v_reuseFailAlloc_3001_, 1, v_val_2998_);
lean_ctor_set(v_reuseFailAlloc_3001_, 2, v_tail_2987_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(lean_object* v_character_3003_, lean_object* v_a_3004_, lean_object* v_character_3005_, lean_object* v_m_3006_, lean_object* v_a_3007_){
_start:
{
lean_object* v_size_3008_; lean_object* v_buckets_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3061_; 
v_size_3008_ = lean_ctor_get(v_m_3006_, 0);
v_buckets_3009_ = lean_ctor_get(v_m_3006_, 1);
v_isSharedCheck_3061_ = !lean_is_exclusive(v_m_3006_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3011_ = v_m_3006_;
v_isShared_3012_ = v_isSharedCheck_3061_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_buckets_3009_);
lean_inc(v_size_3008_);
lean_dec(v_m_3006_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3061_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3013_; uint64_t v___x_3014_; uint64_t v___x_3015_; uint64_t v___x_3016_; uint64_t v_fold_3017_; uint64_t v___x_3018_; uint64_t v___x_3019_; uint64_t v___x_3020_; size_t v___x_3021_; size_t v___x_3022_; size_t v___x_3023_; size_t v___x_3024_; size_t v___x_3025_; lean_object* v_bkt_3026_; uint8_t v___x_3027_; 
v___x_3013_ = lean_array_get_size(v_buckets_3009_);
v___x_3014_ = lean_uint64_of_nat(v_a_3007_);
v___x_3015_ = 32ULL;
v___x_3016_ = lean_uint64_shift_right(v___x_3014_, v___x_3015_);
v_fold_3017_ = lean_uint64_xor(v___x_3014_, v___x_3016_);
v___x_3018_ = 16ULL;
v___x_3019_ = lean_uint64_shift_right(v_fold_3017_, v___x_3018_);
v___x_3020_ = lean_uint64_xor(v_fold_3017_, v___x_3019_);
v___x_3021_ = lean_uint64_to_usize(v___x_3020_);
v___x_3022_ = lean_usize_of_nat(v___x_3013_);
v___x_3023_ = ((size_t)1ULL);
v___x_3024_ = lean_usize_sub(v___x_3022_, v___x_3023_);
v___x_3025_ = lean_usize_land(v___x_3021_, v___x_3024_);
v_bkt_3026_ = lean_array_uget_borrowed(v_buckets_3009_, v___x_3025_);
v___x_3027_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3007_, v_bkt_3026_);
if (v___x_3027_ == 0)
{
lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v_size_x27_3033_; lean_object* v___x_3034_; lean_object* v_buckets_x27_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; uint8_t v___x_3041_; 
v___x_3028_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___x_3029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3029_, 0, v_character_3003_);
lean_ctor_set(v___x_3029_, 1, v_a_3004_);
v___x_3030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3030_, 0, v_character_3005_);
lean_ctor_set(v___x_3030_, 1, v___x_3029_);
v___x_3031_ = lean_array_push(v___x_3028_, v___x_3030_);
v___x_3032_ = lean_unsigned_to_nat(1u);
v_size_x27_3033_ = lean_nat_add(v_size_3008_, v___x_3032_);
lean_dec(v_size_3008_);
lean_inc(v_bkt_3026_);
v___x_3034_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3034_, 0, v_a_3007_);
lean_ctor_set(v___x_3034_, 1, v___x_3031_);
lean_ctor_set(v___x_3034_, 2, v_bkt_3026_);
v_buckets_x27_3035_ = lean_array_uset(v_buckets_3009_, v___x_3025_, v___x_3034_);
v___x_3036_ = lean_unsigned_to_nat(4u);
v___x_3037_ = lean_nat_mul(v_size_x27_3033_, v___x_3036_);
v___x_3038_ = lean_unsigned_to_nat(3u);
v___x_3039_ = lean_nat_div(v___x_3037_, v___x_3038_);
lean_dec(v___x_3037_);
v___x_3040_ = lean_array_get_size(v_buckets_x27_3035_);
v___x_3041_ = lean_nat_dec_le(v___x_3039_, v___x_3040_);
lean_dec(v___x_3039_);
if (v___x_3041_ == 0)
{
lean_object* v_val_3042_; lean_object* v___x_3044_; 
v_val_3042_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_buckets_x27_3035_);
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 1, v_val_3042_);
lean_ctor_set(v___x_3011_, 0, v_size_x27_3033_);
v___x_3044_ = v___x_3011_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_size_x27_3033_);
lean_ctor_set(v_reuseFailAlloc_3045_, 1, v_val_3042_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
else
{
lean_object* v___x_3047_; 
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 1, v_buckets_x27_3035_);
lean_ctor_set(v___x_3011_, 0, v_size_x27_3033_);
v___x_3047_ = v___x_3011_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_size_x27_3033_);
lean_ctor_set(v_reuseFailAlloc_3048_, 1, v_buckets_x27_3035_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
else
{
lean_object* v___x_3049_; lean_object* v_buckets_x27_3050_; lean_object* v_bkt_x27_3051_; lean_object* v___y_3053_; uint8_t v___x_3058_; 
lean_inc(v_bkt_3026_);
v___x_3049_ = lean_box(0);
v_buckets_x27_3050_ = lean_array_uset(v_buckets_3009_, v___x_3025_, v___x_3049_);
lean_inc(v_a_3007_);
v_bkt_x27_3051_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_3003_, v_a_3004_, v_character_3005_, v_a_3007_, v_bkt_3026_);
v___x_3058_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3007_, v_bkt_x27_3051_);
lean_dec(v_a_3007_);
if (v___x_3058_ == 0)
{
lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3059_ = lean_unsigned_to_nat(1u);
v___x_3060_ = lean_nat_sub(v_size_3008_, v___x_3059_);
lean_dec(v_size_3008_);
v___y_3053_ = v___x_3060_;
goto v___jp_3052_;
}
else
{
v___y_3053_ = v_size_3008_;
goto v___jp_3052_;
}
v___jp_3052_:
{
lean_object* v___x_3054_; lean_object* v___x_3056_; 
v___x_3054_ = lean_array_uset(v_buckets_x27_3050_, v___x_3025_, v_bkt_x27_3051_);
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 1, v___x_3054_);
lean_ctor_set(v___x_3011_, 0, v___y_3053_);
v___x_3056_ = v___x_3011_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v___y_3053_);
lean_ctor_set(v_reuseFailAlloc_3057_, 1, v___x_3054_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(lean_object* v_text_3062_, lean_object* v_as_3063_, size_t v_sz_3064_, size_t v_i_3065_, lean_object* v_b_3066_){
_start:
{
lean_object* v_a_3068_; uint8_t v___x_3072_; 
v___x_3072_ = lean_usize_dec_lt(v_i_3065_, v_sz_3064_);
if (v___x_3072_ == 0)
{
lean_dec_ref(v_text_3062_);
return v_b_3066_;
}
else
{
lean_object* v_a_3073_; lean_object* v_stx_3074_; uint8_t v___x_3075_; lean_object* v___x_3076_; 
v_a_3073_ = lean_array_uget_borrowed(v_as_3063_, v_i_3065_);
v_stx_3074_ = lean_ctor_get(v_a_3073_, 0);
v___x_3075_ = 0;
lean_inc_ref(v_text_3062_);
v___x_3076_ = l_Lean_FileMap_lspRangeOfStx_x3f(v_text_3062_, v_stx_3074_, v___x_3075_);
if (lean_obj_tag(v___x_3076_) == 1)
{
lean_object* v_val_3077_; lean_object* v_start_3078_; lean_object* v_end_3079_; lean_object* v_line_3080_; lean_object* v_character_3081_; lean_object* v_character_3082_; lean_object* v___x_3083_; 
v_val_3077_ = lean_ctor_get(v___x_3076_, 0);
lean_inc(v_val_3077_);
lean_dec_ref_known(v___x_3076_, 1);
v_start_3078_ = lean_ctor_get(v_val_3077_, 0);
lean_inc_ref(v_start_3078_);
v_end_3079_ = lean_ctor_get(v_val_3077_, 1);
lean_inc_ref(v_end_3079_);
lean_dec(v_val_3077_);
v_line_3080_ = lean_ctor_get(v_start_3078_, 0);
lean_inc(v_line_3080_);
v_character_3081_ = lean_ctor_get(v_start_3078_, 1);
lean_inc(v_character_3081_);
lean_dec_ref(v_start_3078_);
v_character_3082_ = lean_ctor_get(v_end_3079_, 1);
lean_inc(v_character_3082_);
lean_dec_ref(v_end_3079_);
lean_inc(v_a_3073_);
v___x_3083_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(v_character_3082_, v_a_3073_, v_character_3081_, v_b_3066_, v_line_3080_);
v_a_3068_ = v___x_3083_;
goto v___jp_3067_;
}
else
{
lean_dec(v___x_3076_);
v_a_3068_ = v_b_3066_;
goto v___jp_3067_;
}
}
v___jp_3067_:
{
size_t v___x_3069_; size_t v___x_3070_; 
v___x_3069_ = ((size_t)1ULL);
v___x_3070_ = lean_usize_add(v_i_3065_, v___x_3069_);
v_i_3065_ = v___x_3070_;
v_b_3066_ = v_a_3068_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3___boxed(lean_object* v_text_3084_, lean_object* v_as_3085_, lean_object* v_sz_3086_, lean_object* v_i_3087_, lean_object* v_b_3088_){
_start:
{
size_t v_sz_boxed_3089_; size_t v_i_boxed_3090_; lean_object* v_res_3091_; 
v_sz_boxed_3089_ = lean_unbox_usize(v_sz_3086_);
lean_dec(v_sz_3086_);
v_i_boxed_3090_ = lean_unbox_usize(v_i_3087_);
lean_dec(v_i_3087_);
v_res_3091_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3084_, v_as_3085_, v_sz_boxed_3089_, v_i_boxed_3090_, v_b_3088_);
lean_dec_ref(v_as_3085_);
return v_res_3091_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0(void){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3092_ = lean_box(0);
v___x_3093_ = lean_unsigned_to_nat(16u);
v___x_3094_ = lean_mk_array(v___x_3093_, v___x_3092_);
return v___x_3094_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1(void){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v_byLine_3097_; 
v___x_3095_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__0, &l_Lean_Server_FileWorker_dbgShowTokens___closed__0_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0);
v___x_3096_ = lean_unsigned_to_nat(0u);
v_byLine_3097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byLine_3097_, 0, v___x_3096_);
lean_ctor_set(v_byLine_3097_, 1, v___x_3095_);
return v_byLine_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens(lean_object* v_text_3100_, lean_object* v_toks_3101_){
_start:
{
lean_object* v___x_3102_; lean_object* v_byLine_3103_; size_t v_sz_3104_; size_t v___x_3105_; lean_object* v___x_3106_; lean_object* v_buckets_3107_; lean_object* v___f_3108_; lean_object* v___x_3109_; lean_object* v___y_3111_; lean_object* v___x_3114_; lean_object* v___x_3115_; uint8_t v___x_3116_; 
v___x_3102_ = lean_unsigned_to_nat(0u);
v_byLine_3103_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__1, &l_Lean_Server_FileWorker_dbgShowTokens___closed__1_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1);
v_sz_3104_ = lean_array_size(v_toks_3101_);
v___x_3105_ = ((size_t)0ULL);
v___x_3106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3100_, v_toks_3101_, v_sz_3104_, v___x_3105_, v_byLine_3103_);
v_buckets_3107_ = lean_ctor_get(v___x_3106_, 1);
lean_inc_ref(v_buckets_3107_);
lean_dec_ref(v___x_3106_);
v___f_3108_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__2));
v___x_3109_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__3));
v___x_3114_ = lean_box(0);
v___x_3115_ = lean_array_get_size(v_buckets_3107_);
v___x_3116_ = lean_nat_dec_lt(v___x_3102_, v___x_3115_);
if (v___x_3116_ == 0)
{
lean_dec_ref(v_buckets_3107_);
v___y_3111_ = v___x_3114_;
goto v___jp_3110_;
}
else
{
size_t v___x_3117_; lean_object* v___x_3118_; 
v___x_3117_ = lean_usize_of_nat(v___x_3115_);
v___x_3118_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_buckets_3107_, v___x_3117_, v___x_3105_, v___x_3114_);
lean_dec_ref(v_buckets_3107_);
v___y_3111_ = v___x_3118_;
goto v___jp_3110_;
}
v___jp_3110_:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3112_ = l_List_mergeSort___redArg(v___y_3111_, v___f_3108_);
v___x_3113_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v___x_3112_, v___x_3109_);
lean_dec(v___x_3112_);
return v___x_3113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___boxed(lean_object* v_text_3119_, lean_object* v_toks_3120_){
_start:
{
lean_object* v_res_3121_; 
v_res_3121_ = l_Lean_Server_FileWorker_dbgShowTokens(v_text_3119_, v_toks_3120_);
lean_dec_ref(v_toks_3120_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(lean_object* v_as_3122_, lean_object* v_as_x27_3123_, lean_object* v_b_3124_, lean_object* v_a_3125_){
_start:
{
lean_object* v___x_3126_; 
v___x_3126_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v_as_x27_3123_, v_b_3124_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___boxed(lean_object* v_as_3127_, lean_object* v_as_x27_3128_, lean_object* v_b_3129_, lean_object* v_a_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(v_as_3127_, v_as_x27_3128_, v_b_3129_, v_a_3130_);
lean_dec(v_as_x27_3128_);
lean_dec(v_as_3127_);
return v_res_3131_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(lean_object* v_00_u03b2_3132_, lean_object* v_a_3133_, lean_object* v_x_3134_){
_start:
{
uint8_t v___x_3135_; 
v___x_3135_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3133_, v_x_3134_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3136_, lean_object* v_a_3137_, lean_object* v_x_3138_){
_start:
{
uint8_t v_res_3139_; lean_object* v_r_3140_; 
v_res_3139_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(v_00_u03b2_3136_, v_a_3137_, v_x_3138_);
lean_dec(v_x_3138_);
lean_dec(v_a_3137_);
v_r_3140_ = lean_box(v_res_3139_);
return v_r_3140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4(lean_object* v_00_u03b2_3141_, lean_object* v_data_3142_){
_start:
{
lean_object* v___x_3143_; 
v___x_3143_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_data_3142_);
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3144_, lean_object* v_i_3145_, lean_object* v_source_3146_, lean_object* v_target_3147_){
_start:
{
lean_object* v___x_3148_; 
v___x_3148_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v_i_3145_, v_source_3146_, v_target_3147_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10(lean_object* v_00_u03b2_3149_, lean_object* v_x_3150_, lean_object* v_x_3151_){
_start:
{
lean_object* v___x_3152_; 
v___x_3152_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_x_3150_, v_x_3151_);
return v___x_3152_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(lean_object* v_beginPos_3153_, lean_object* v_doc_3154_, lean_object* v_as_x27_3155_, lean_object* v_b_3156_, lean_object* v___y_3157_){
_start:
{
if (lean_obj_tag(v_as_x27_3155_) == 0)
{
lean_object* v___x_3159_; 
lean_dec_ref(v_doc_3154_);
v___x_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3159_, 0, v_b_3156_);
return v___x_3159_;
}
else
{
lean_object* v_head_3160_; lean_object* v_tail_3161_; lean_object* v___x_3162_; uint8_t v___x_3163_; 
v_head_3160_ = lean_ctor_get(v_as_x27_3155_, 0);
v_tail_3161_ = lean_ctor_get(v_as_x27_3155_, 1);
v___x_3162_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_head_3160_);
v___x_3163_ = lean_nat_dec_le(v___x_3162_, v_beginPos_3153_);
lean_dec(v___x_3162_);
if (v___x_3163_ == 0)
{
lean_object* v_toEditableDocumentCore_3164_; lean_object* v_meta_3165_; lean_object* v_text_3166_; lean_object* v_stx_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v_toEditableDocumentCore_3164_ = lean_ctor_get(v_doc_3154_, 0);
v_meta_3165_ = lean_ctor_get(v_toEditableDocumentCore_3164_, 0);
v_text_3166_ = lean_ctor_get(v_meta_3165_, 3);
v_stx_3167_ = lean_ctor_get(v_head_3160_, 0);
lean_inc(v_stx_3167_);
lean_inc_ref(v_text_3166_);
v___x_3168_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_3166_, v_stx_3167_);
lean_inc(v_head_3160_);
v___x_3169_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_head_3160_);
v___x_3170_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(v___x_3169_);
v___x_3171_ = l_Array_append___redArg(v_b_3156_, v___x_3168_);
lean_dec_ref(v___x_3168_);
v___x_3172_ = l_Array_append___redArg(v___x_3171_, v___x_3170_);
lean_dec_ref(v___x_3170_);
v___x_3173_ = l_Lean_Server_RequestM_checkCancelled(v___y_3157_);
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_dec_ref_known(v___x_3173_, 1);
v_as_x27_3155_ = v_tail_3161_;
v_b_3156_ = v___x_3172_;
goto _start;
}
else
{
lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3182_; 
lean_dec_ref(v___x_3172_);
lean_dec_ref(v_doc_3154_);
v_a_3175_ = lean_ctor_get(v___x_3173_, 0);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3177_ = v___x_3173_;
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_dec(v___x_3173_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3180_; 
if (v_isShared_3178_ == 0)
{
v___x_3180_ = v___x_3177_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_a_3175_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
}
}
else
{
v_as_x27_3155_ = v_tail_3161_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg___boxed(lean_object* v_beginPos_3184_, lean_object* v_doc_3185_, lean_object* v_as_x27_3186_, lean_object* v_b_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3184_, v_doc_3185_, v_as_x27_3186_, v_b_3187_, v___y_3188_);
lean_dec_ref(v___y_3188_);
lean_dec(v_as_x27_3186_);
lean_dec(v_beginPos_3184_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens(lean_object* v_doc_3191_, lean_object* v_beginPos_3192_, lean_object* v_endPos_x3f_3193_, lean_object* v_snaps_3194_, lean_object* v_a_3195_){
_start:
{
lean_object* v_leanSemanticTokens_3197_; lean_object* v___x_3198_; 
v_leanSemanticTokens_3197_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
lean_inc_ref(v_doc_3191_);
v___x_3198_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3192_, v_doc_3191_, v_snaps_3194_, v_leanSemanticTokens_3197_, v_a_3195_);
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_object* v_toEditableDocumentCore_3199_; lean_object* v_meta_3200_; lean_object* v_a_3201_; lean_object* v_text_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v_toEditableDocumentCore_3199_ = lean_ctor_get(v_doc_3191_, 0);
lean_inc_ref(v_toEditableDocumentCore_3199_);
lean_dec_ref(v_doc_3191_);
v_meta_3200_ = lean_ctor_get(v_toEditableDocumentCore_3199_, 0);
lean_inc_ref(v_meta_3200_);
lean_dec_ref(v_toEditableDocumentCore_3199_);
v_a_3201_ = lean_ctor_get(v___x_3198_, 0);
lean_inc(v_a_3201_);
lean_dec_ref_known(v___x_3198_, 1);
v_text_3202_ = lean_ctor_get(v_meta_3200_, 3);
lean_inc_ref(v_text_3202_);
lean_dec_ref(v_meta_3200_);
v___x_3203_ = l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(v_text_3202_, v_beginPos_3192_, v_endPos_x3f_3193_, v_a_3201_);
lean_dec(v_a_3201_);
v___x_3204_ = l_Lean_Server_RequestM_checkCancelled(v_a_3195_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v___x_3205_; lean_object* v___x_3206_; 
lean_dec_ref_known(v___x_3204_, 1);
v___x_3205_ = l_Lean_Server_FileWorker_handleOverlappingSemanticTokens(v___x_3203_);
v___x_3206_ = l_Lean_Server_RequestM_checkCancelled(v_a_3195_);
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3214_; 
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3214_ == 0)
{
lean_object* v_unused_3215_; 
v_unused_3215_ = lean_ctor_get(v___x_3206_, 0);
lean_dec(v_unused_3215_);
v___x_3208_ = v___x_3206_;
v_isShared_3209_ = v_isSharedCheck_3214_;
goto v_resetjp_3207_;
}
else
{
lean_dec(v___x_3206_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3214_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3210_; lean_object* v___x_3212_; 
v___x_3210_ = l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(v___x_3205_);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 0, v___x_3210_);
v___x_3212_ = v___x_3208_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3210_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_dec_ref(v___x_3205_);
v_a_3216_ = lean_ctor_get(v___x_3206_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3206_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3206_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
else
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3231_; 
lean_dec_ref(v___x_3203_);
v_a_3224_ = lean_ctor_get(v___x_3204_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3226_ = v___x_3204_;
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3204_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
if (v_isShared_3227_ == 0)
{
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3224_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
}
else
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3239_; 
lean_dec_ref(v_doc_3191_);
v_a_3232_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3234_ = v___x_3198_;
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3198_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3237_; 
if (v_isShared_3235_ == 0)
{
v___x_3237_ = v___x_3234_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_a_3232_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens___boxed(lean_object* v_doc_3240_, lean_object* v_beginPos_3241_, lean_object* v_endPos_x3f_3242_, lean_object* v_snaps_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_doc_3240_, v_beginPos_3241_, v_endPos_x3f_3242_, v_snaps_3243_, v_a_3244_);
lean_dec_ref(v_a_3244_);
lean_dec(v_snaps_3243_);
lean_dec(v_endPos_x3f_3242_);
lean_dec(v_beginPos_3241_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(lean_object* v_beginPos_3247_, lean_object* v_doc_3248_, lean_object* v_as_3249_, lean_object* v_as_x27_3250_, lean_object* v_b_3251_, lean_object* v_a_3252_, lean_object* v___y_3253_){
_start:
{
lean_object* v___x_3255_; 
v___x_3255_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3247_, v_doc_3248_, v_as_x27_3250_, v_b_3251_, v___y_3253_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___boxed(lean_object* v_beginPos_3256_, lean_object* v_doc_3257_, lean_object* v_as_3258_, lean_object* v_as_x27_3259_, lean_object* v_b_3260_, lean_object* v_a_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_){
_start:
{
lean_object* v_res_3264_; 
v_res_3264_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(v_beginPos_3256_, v_doc_3257_, v_as_3258_, v_as_x27_3259_, v_b_3260_, v_a_3261_, v___y_3262_);
lean_dec_ref(v___y_3262_);
lean_dec(v_as_x27_3259_);
lean_dec(v_as_3258_);
lean_dec(v_beginPos_3256_);
return v_res_3264_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState_default(void){
_start:
{
lean_object* v___x_3273_; 
v___x_3273_ = lean_box(0);
return v___x_3273_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState(void){
_start:
{
lean_object* v___x_3274_; 
v___x_3274_ = lean_box(0);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(lean_object* v___y_3275_){
_start:
{
lean_object* v_doc_3277_; lean_object* v___x_3278_; 
v_doc_3277_ = lean_ctor_get(v___y_3275_, 1);
lean_inc_ref(v_doc_3277_);
v___x_3278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3278_, 0, v_doc_3277_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0___boxed(lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
lean_object* v_res_3281_; 
v_res_3281_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v___y_3279_);
lean_dec_ref(v___y_3279_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(lean_object* v_a_3282_){
_start:
{
lean_object* v___x_3284_; lean_object* v_a_3285_; lean_object* v_toEditableDocumentCore_3286_; lean_object* v_cmdSnaps_3287_; lean_object* v_cancelTk_3288_; uint32_t v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v_snd_3292_; lean_object* v_fst_3293_; lean_object* v_snd_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3323_; 
v___x_3284_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_3282_);
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_a_3285_);
lean_dec_ref(v___x_3284_);
v_toEditableDocumentCore_3286_ = lean_ctor_get(v_a_3285_, 0);
v_cmdSnaps_3287_ = lean_ctor_get(v_toEditableDocumentCore_3286_, 2);
v_cancelTk_3288_ = lean_ctor_get(v_a_3282_, 4);
v___x_3289_ = 3000;
v___x_3290_ = l_Lean_Server_RequestCancellationToken_cancellationTasks(v_cancelTk_3288_);
lean_inc(v_cmdSnaps_3287_);
v___x_3291_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(v_cmdSnaps_3287_, v___x_3289_, v___x_3290_);
v_snd_3292_ = lean_ctor_get(v___x_3291_, 1);
lean_inc(v_snd_3292_);
v_fst_3293_ = lean_ctor_get(v___x_3291_, 0);
lean_inc(v_fst_3293_);
lean_dec_ref(v___x_3291_);
v_snd_3294_ = lean_ctor_get(v_snd_3292_, 1);
v_isSharedCheck_3323_ = !lean_is_exclusive(v_snd_3292_);
if (v_isSharedCheck_3323_ == 0)
{
lean_object* v_unused_3324_; 
v_unused_3324_ = lean_ctor_get(v_snd_3292_, 0);
lean_dec(v_unused_3324_);
v___x_3296_ = v_snd_3292_;
v_isShared_3297_ = v_isSharedCheck_3323_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_snd_3294_);
lean_dec(v_snd_3292_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3323_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3298_ = lean_unsigned_to_nat(0u);
v___x_3299_ = lean_box(0);
v___x_3300_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_3285_, v___x_3298_, v___x_3299_, v_fst_3293_, v_a_3282_);
lean_dec(v_fst_3293_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3314_; 
v_a_3301_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3303_ = v___x_3300_;
v_isShared_3304_ = v_isSharedCheck_3314_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3300_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3314_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3305_; uint8_t v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3309_; 
v___x_3305_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3305_, 0, v_a_3301_);
v___x_3306_ = lean_unbox(v_snd_3294_);
lean_dec(v_snd_3294_);
lean_ctor_set_uint8(v___x_3305_, sizeof(void*)*1, v___x_3306_);
v___x_3307_ = lean_box(0);
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 1, v___x_3307_);
lean_ctor_set(v___x_3296_, 0, v___x_3305_);
v___x_3309_ = v___x_3296_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3305_);
lean_ctor_set(v_reuseFailAlloc_3313_, 1, v___x_3307_);
v___x_3309_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
lean_object* v___x_3311_; 
if (v_isShared_3304_ == 0)
{
lean_ctor_set(v___x_3303_, 0, v___x_3309_);
v___x_3311_ = v___x_3303_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3309_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
}
else
{
lean_object* v_a_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3322_; 
lean_del_object(v___x_3296_);
lean_dec(v_snd_3294_);
v_a_3315_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3317_ = v___x_3300_;
v_isShared_3318_ = v_isSharedCheck_3322_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_a_3315_);
lean_dec(v___x_3300_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3322_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
lean_object* v___x_3320_; 
if (v_isShared_3318_ == 0)
{
v___x_3320_ = v___x_3317_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v_a_3315_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
return v___x_3320_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg___boxed(lean_object* v_a_3325_, lean_object* v_a_3326_){
_start:
{
lean_object* v_res_3327_; 
v_res_3327_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_3325_);
lean_dec_ref(v_a_3325_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull(lean_object* v_x_3328_, lean_object* v_x_3329_, lean_object* v_a_3330_){
_start:
{
lean_object* v___x_3332_; 
v___x_3332_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_3330_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___boxed(lean_object* v_x_3333_, lean_object* v_x_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_){
_start:
{
lean_object* v_res_3337_; 
v_res_3337_ = l_Lean_Server_FileWorker_handleSemanticTokensFull(v_x_3333_, v_x_3334_, v_a_3335_);
lean_dec_ref(v_a_3335_);
lean_dec_ref(v_x_3333_);
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(lean_object* v_a_3338_){
_start:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3340_ = lean_box(0);
v___x_3341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3340_);
lean_ctor_set(v___x_3341_, 1, v_a_3338_);
v___x_3342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3341_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg___boxed(lean_object* v_a_3343_, lean_object* v_a_3344_){
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_3343_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange(lean_object* v_x_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_){
_start:
{
lean_object* v___x_3350_; 
v___x_3350_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_3347_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___boxed(lean_object* v_x_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_){
_start:
{
lean_object* v_res_3355_; 
v_res_3355_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange(v_x_3351_, v_a_3352_, v_a_3353_);
lean_dec_ref(v_a_3353_);
lean_dec_ref(v_x_3351_);
return v_res_3355_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(lean_object* v___x_3356_, lean_object* v_x_3357_){
_start:
{
lean_object* v___x_3358_; uint8_t v___x_3359_; 
v___x_3358_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_x_3357_);
v___x_3359_ = lean_nat_dec_le(v___x_3356_, v___x_3358_);
lean_dec(v___x_3358_);
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed(lean_object* v___x_3360_, lean_object* v_x_3361_){
_start:
{
uint8_t v_res_3362_; lean_object* v_r_3363_; 
v_res_3362_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(v___x_3360_, v_x_3361_);
lean_dec_ref(v_x_3361_);
lean_dec(v___x_3360_);
v_r_3363_ = lean_box(v_res_3362_);
return v_r_3363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(lean_object* v___x_3364_, lean_object* v_a_3365_, lean_object* v___x_3366_, lean_object* v_x_3367_, lean_object* v___y_3368_){
_start:
{
lean_object* v_fst_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; 
v_fst_3370_ = lean_ctor_get(v_x_3367_, 0);
v___x_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3364_);
v___x_3372_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_3365_, v___x_3366_, v___x_3371_, v_fst_3370_, v___y_3368_);
lean_dec_ref_known(v___x_3371_, 1);
return v___x_3372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed(lean_object* v___x_3373_, lean_object* v_a_3374_, lean_object* v___x_3375_, lean_object* v_x_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
lean_object* v_res_3379_; 
v_res_3379_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(v___x_3373_, v_a_3374_, v___x_3375_, v_x_3376_, v___y_3377_);
lean_dec_ref(v___y_3377_);
lean_dec_ref(v_x_3376_);
lean_dec(v___x_3375_);
return v_res_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange(lean_object* v_p_3380_, lean_object* v_a_3381_){
_start:
{
lean_object* v___x_3383_; lean_object* v_a_3384_; lean_object* v_toEditableDocumentCore_3385_; lean_object* v_meta_3386_; lean_object* v_range_3387_; lean_object* v_cmdSnaps_3388_; lean_object* v_text_3389_; lean_object* v_start_3390_; lean_object* v_end_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___f_3394_; lean_object* v___f_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3383_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_3381_);
v_a_3384_ = lean_ctor_get(v___x_3383_, 0);
lean_inc(v_a_3384_);
lean_dec_ref(v___x_3383_);
v_toEditableDocumentCore_3385_ = lean_ctor_get(v_a_3384_, 0);
v_meta_3386_ = lean_ctor_get(v_toEditableDocumentCore_3385_, 0);
v_range_3387_ = lean_ctor_get(v_p_3380_, 1);
lean_inc_ref(v_range_3387_);
lean_dec_ref(v_p_3380_);
v_cmdSnaps_3388_ = lean_ctor_get(v_toEditableDocumentCore_3385_, 2);
lean_inc(v_cmdSnaps_3388_);
v_text_3389_ = lean_ctor_get(v_meta_3386_, 3);
v_start_3390_ = lean_ctor_get(v_range_3387_, 0);
lean_inc_ref(v_start_3390_);
v_end_3391_ = lean_ctor_get(v_range_3387_, 1);
lean_inc_ref(v_end_3391_);
lean_dec_ref(v_range_3387_);
v___x_3392_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_3389_, v_start_3390_);
v___x_3393_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_3389_, v_end_3391_);
lean_inc(v___x_3393_);
v___f_3394_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3394_, 0, v___x_3393_);
v___f_3395_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3395_, 0, v___x_3393_);
lean_closure_set(v___f_3395_, 1, v_a_3384_);
lean_closure_set(v___f_3395_, 2, v___x_3392_);
v___x_3396_ = l_Lean_AsyncList_waitUntil___redArg(v___f_3394_, v_cmdSnaps_3388_);
v___x_3397_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_3396_, v___f_3395_, v_a_3381_);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___boxed(lean_object* v_p_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l_Lean_Server_FileWorker_handleSemanticTokensRange(v_p_3398_, v_a_3399_);
lean_dec_ref(v_a_3399_);
return v_res_3401_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_keys_3402_, lean_object* v_i_3403_, lean_object* v_k_3404_){
_start:
{
lean_object* v___x_3405_; uint8_t v___x_3406_; 
v___x_3405_ = lean_array_get_size(v_keys_3402_);
v___x_3406_ = lean_nat_dec_lt(v_i_3403_, v___x_3405_);
if (v___x_3406_ == 0)
{
lean_dec(v_i_3403_);
return v___x_3406_;
}
else
{
lean_object* v_k_x27_3407_; uint8_t v___x_3408_; 
v_k_x27_3407_ = lean_array_fget_borrowed(v_keys_3402_, v_i_3403_);
v___x_3408_ = lean_string_dec_eq(v_k_3404_, v_k_x27_3407_);
if (v___x_3408_ == 0)
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3409_ = lean_unsigned_to_nat(1u);
v___x_3410_ = lean_nat_add(v_i_3403_, v___x_3409_);
lean_dec(v_i_3403_);
v_i_3403_ = v___x_3410_;
goto _start;
}
else
{
lean_dec(v_i_3403_);
return v___x_3406_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_keys_3412_, lean_object* v_i_3413_, lean_object* v_k_3414_){
_start:
{
uint8_t v_res_3415_; lean_object* v_r_3416_; 
v_res_3415_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_3412_, v_i_3413_, v_k_3414_);
lean_dec_ref(v_k_3414_);
lean_dec_ref(v_keys_3412_);
v_r_3416_ = lean_box(v_res_3415_);
return v_r_3416_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(lean_object* v_x_3417_, size_t v_x_3418_, lean_object* v_x_3419_){
_start:
{
if (lean_obj_tag(v_x_3417_) == 0)
{
lean_object* v_es_3420_; lean_object* v___x_3421_; size_t v___x_3422_; size_t v___x_3423_; lean_object* v_j_3424_; lean_object* v___x_3425_; 
v_es_3420_ = lean_ctor_get(v_x_3417_, 0);
v___x_3421_ = lean_box(2);
v___x_3422_ = ((size_t)31ULL);
v___x_3423_ = lean_usize_land(v_x_3418_, v___x_3422_);
v_j_3424_ = lean_usize_to_nat(v___x_3423_);
v___x_3425_ = lean_array_get_borrowed(v___x_3421_, v_es_3420_, v_j_3424_);
lean_dec(v_j_3424_);
switch(lean_obj_tag(v___x_3425_))
{
case 0:
{
lean_object* v_key_3426_; uint8_t v___x_3427_; 
v_key_3426_ = lean_ctor_get(v___x_3425_, 0);
v___x_3427_ = lean_string_dec_eq(v_x_3419_, v_key_3426_);
return v___x_3427_;
}
case 1:
{
lean_object* v_node_3428_; size_t v___x_3429_; size_t v___x_3430_; 
v_node_3428_ = lean_ctor_get(v___x_3425_, 0);
v___x_3429_ = ((size_t)5ULL);
v___x_3430_ = lean_usize_shift_right(v_x_3418_, v___x_3429_);
v_x_3417_ = v_node_3428_;
v_x_3418_ = v___x_3430_;
goto _start;
}
default: 
{
uint8_t v___x_3432_; 
v___x_3432_ = 0;
return v___x_3432_;
}
}
}
else
{
lean_object* v_ks_3433_; lean_object* v___x_3434_; uint8_t v___x_3435_; 
v_ks_3433_ = lean_ctor_get(v_x_3417_, 0);
v___x_3434_ = lean_unsigned_to_nat(0u);
v___x_3435_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_ks_3433_, v___x_3434_, v_x_3419_);
return v___x_3435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_x_3436_, lean_object* v_x_3437_, lean_object* v_x_3438_){
_start:
{
size_t v_x_2586__boxed_3439_; uint8_t v_res_3440_; lean_object* v_r_3441_; 
v_x_2586__boxed_3439_ = lean_unbox_usize(v_x_3437_);
lean_dec(v_x_3437_);
v_res_3440_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_3436_, v_x_2586__boxed_3439_, v_x_3438_);
lean_dec_ref(v_x_3438_);
lean_dec_ref(v_x_3436_);
v_r_3441_ = lean_box(v_res_3440_);
return v_r_3441_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_x_3442_, lean_object* v_x_3443_){
_start:
{
uint64_t v___x_3444_; size_t v___x_3445_; uint8_t v___x_3446_; 
v___x_3444_ = lean_string_hash(v_x_3443_);
v___x_3445_ = lean_uint64_to_usize(v___x_3444_);
v___x_3446_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_3442_, v___x_3445_, v_x_3443_);
return v___x_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object* v_x_3447_, lean_object* v_x_3448_){
_start:
{
uint8_t v_res_3449_; lean_object* v_r_3450_; 
v_res_3449_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_3447_, v_x_3448_);
lean_dec_ref(v_x_3448_);
lean_dec_ref(v_x_3447_);
v_r_3450_ = lean_box(v_res_3449_);
return v_r_3450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(lean_object* v___x_3451_, lean_object* v_x_3452_){
_start:
{
return v___x_3451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4___boxed(lean_object* v___x_3453_, lean_object* v_x_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(v___x_3453_, v_x_3454_);
lean_dec_ref(v_x_3454_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(lean_object* v_x_3456_, lean_object* v_x_3457_, lean_object* v_x_3458_, lean_object* v_x_3459_){
_start:
{
lean_object* v_ks_3460_; lean_object* v_vs_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3485_; 
v_ks_3460_ = lean_ctor_get(v_x_3456_, 0);
v_vs_3461_ = lean_ctor_get(v_x_3456_, 1);
v_isSharedCheck_3485_ = !lean_is_exclusive(v_x_3456_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3463_ = v_x_3456_;
v_isShared_3464_ = v_isSharedCheck_3485_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_vs_3461_);
lean_inc(v_ks_3460_);
lean_dec(v_x_3456_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3485_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3465_; uint8_t v___x_3466_; 
v___x_3465_ = lean_array_get_size(v_ks_3460_);
v___x_3466_ = lean_nat_dec_lt(v_x_3457_, v___x_3465_);
if (v___x_3466_ == 0)
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3470_; 
lean_dec(v_x_3457_);
v___x_3467_ = lean_array_push(v_ks_3460_, v_x_3458_);
v___x_3468_ = lean_array_push(v_vs_3461_, v_x_3459_);
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 1, v___x_3468_);
lean_ctor_set(v___x_3463_, 0, v___x_3467_);
v___x_3470_ = v___x_3463_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v___x_3467_);
lean_ctor_set(v_reuseFailAlloc_3471_, 1, v___x_3468_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
else
{
lean_object* v_k_x27_3472_; uint8_t v___x_3473_; 
v_k_x27_3472_ = lean_array_fget_borrowed(v_ks_3460_, v_x_3457_);
v___x_3473_ = lean_string_dec_eq(v_x_3458_, v_k_x27_3472_);
if (v___x_3473_ == 0)
{
lean_object* v___x_3475_; 
if (v_isShared_3464_ == 0)
{
v___x_3475_ = v___x_3463_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_ks_3460_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v_vs_3461_);
v___x_3475_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___x_3476_ = lean_unsigned_to_nat(1u);
v___x_3477_ = lean_nat_add(v_x_3457_, v___x_3476_);
lean_dec(v_x_3457_);
v_x_3456_ = v___x_3475_;
v_x_3457_ = v___x_3477_;
goto _start;
}
}
else
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3483_; 
v___x_3480_ = lean_array_fset(v_ks_3460_, v_x_3457_, v_x_3458_);
v___x_3481_ = lean_array_fset(v_vs_3461_, v_x_3457_, v_x_3459_);
lean_dec(v_x_3457_);
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 1, v___x_3481_);
lean_ctor_set(v___x_3463_, 0, v___x_3480_);
v___x_3483_ = v___x_3463_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v___x_3480_);
lean_ctor_set(v_reuseFailAlloc_3484_, 1, v___x_3481_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(lean_object* v_n_3486_, lean_object* v_k_3487_, lean_object* v_v_3488_){
_start:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3489_ = lean_unsigned_to_nat(0u);
v___x_3490_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_n_3486_, v___x_3489_, v_k_3487_, v_v_3488_);
return v___x_3490_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_3491_; 
v___x_3491_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(lean_object* v_x_3492_, size_t v_x_3493_, size_t v_x_3494_, lean_object* v_x_3495_, lean_object* v_x_3496_){
_start:
{
if (lean_obj_tag(v_x_3492_) == 0)
{
lean_object* v_es_3497_; size_t v___x_3498_; size_t v___x_3499_; lean_object* v_j_3500_; lean_object* v___x_3501_; uint8_t v___x_3502_; 
v_es_3497_ = lean_ctor_get(v_x_3492_, 0);
v___x_3498_ = ((size_t)31ULL);
v___x_3499_ = lean_usize_land(v_x_3493_, v___x_3498_);
v_j_3500_ = lean_usize_to_nat(v___x_3499_);
v___x_3501_ = lean_array_get_size(v_es_3497_);
v___x_3502_ = lean_nat_dec_lt(v_j_3500_, v___x_3501_);
if (v___x_3502_ == 0)
{
lean_dec(v_j_3500_);
lean_dec(v_x_3496_);
lean_dec_ref(v_x_3495_);
return v_x_3492_;
}
else
{
lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3541_; 
lean_inc_ref(v_es_3497_);
v_isSharedCheck_3541_ = !lean_is_exclusive(v_x_3492_);
if (v_isSharedCheck_3541_ == 0)
{
lean_object* v_unused_3542_; 
v_unused_3542_ = lean_ctor_get(v_x_3492_, 0);
lean_dec(v_unused_3542_);
v___x_3504_ = v_x_3492_;
v_isShared_3505_ = v_isSharedCheck_3541_;
goto v_resetjp_3503_;
}
else
{
lean_dec(v_x_3492_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3541_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v_v_3506_; lean_object* v___x_3507_; lean_object* v_xs_x27_3508_; lean_object* v___y_3510_; 
v_v_3506_ = lean_array_fget(v_es_3497_, v_j_3500_);
v___x_3507_ = lean_box(0);
v_xs_x27_3508_ = lean_array_fset(v_es_3497_, v_j_3500_, v___x_3507_);
switch(lean_obj_tag(v_v_3506_))
{
case 0:
{
lean_object* v_key_3515_; lean_object* v_val_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3526_; 
v_key_3515_ = lean_ctor_get(v_v_3506_, 0);
v_val_3516_ = lean_ctor_get(v_v_3506_, 1);
v_isSharedCheck_3526_ = !lean_is_exclusive(v_v_3506_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3518_ = v_v_3506_;
v_isShared_3519_ = v_isSharedCheck_3526_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_val_3516_);
lean_inc(v_key_3515_);
lean_dec(v_v_3506_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3526_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
uint8_t v___x_3520_; 
v___x_3520_ = lean_string_dec_eq(v_x_3495_, v_key_3515_);
if (v___x_3520_ == 0)
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
lean_del_object(v___x_3518_);
v___x_3521_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3515_, v_val_3516_, v_x_3495_, v_x_3496_);
v___x_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3521_);
v___y_3510_ = v___x_3522_;
goto v___jp_3509_;
}
else
{
lean_object* v___x_3524_; 
lean_dec(v_val_3516_);
lean_dec(v_key_3515_);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 1, v_x_3496_);
lean_ctor_set(v___x_3518_, 0, v_x_3495_);
v___x_3524_ = v___x_3518_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_x_3495_);
lean_ctor_set(v_reuseFailAlloc_3525_, 1, v_x_3496_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
v___y_3510_ = v___x_3524_;
goto v___jp_3509_;
}
}
}
}
case 1:
{
lean_object* v_node_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3539_; 
v_node_3527_ = lean_ctor_get(v_v_3506_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v_v_3506_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3529_ = v_v_3506_;
v_isShared_3530_ = v_isSharedCheck_3539_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_node_3527_);
lean_dec(v_v_3506_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3539_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
size_t v___x_3531_; size_t v___x_3532_; size_t v___x_3533_; size_t v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3537_; 
v___x_3531_ = ((size_t)5ULL);
v___x_3532_ = lean_usize_shift_right(v_x_3493_, v___x_3531_);
v___x_3533_ = ((size_t)1ULL);
v___x_3534_ = lean_usize_add(v_x_3494_, v___x_3533_);
v___x_3535_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_node_3527_, v___x_3532_, v___x_3534_, v_x_3495_, v_x_3496_);
if (v_isShared_3530_ == 0)
{
lean_ctor_set(v___x_3529_, 0, v___x_3535_);
v___x_3537_ = v___x_3529_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3535_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
v___y_3510_ = v___x_3537_;
goto v___jp_3509_;
}
}
}
default: 
{
lean_object* v___x_3540_; 
v___x_3540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3540_, 0, v_x_3495_);
lean_ctor_set(v___x_3540_, 1, v_x_3496_);
v___y_3510_ = v___x_3540_;
goto v___jp_3509_;
}
}
v___jp_3509_:
{
lean_object* v___x_3511_; lean_object* v___x_3513_; 
v___x_3511_ = lean_array_fset(v_xs_x27_3508_, v_j_3500_, v___y_3510_);
lean_dec(v_j_3500_);
if (v_isShared_3505_ == 0)
{
lean_ctor_set(v___x_3504_, 0, v___x_3511_);
v___x_3513_ = v___x_3504_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___x_3511_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
}
else
{
lean_object* v_ks_3543_; lean_object* v_vs_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3562_; 
v_ks_3543_ = lean_ctor_get(v_x_3492_, 0);
v_vs_3544_ = lean_ctor_get(v_x_3492_, 1);
v_isSharedCheck_3562_ = !lean_is_exclusive(v_x_3492_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3546_ = v_x_3492_;
v_isShared_3547_ = v_isSharedCheck_3562_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_vs_3544_);
lean_inc(v_ks_3543_);
lean_dec(v_x_3492_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3562_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3549_; 
if (v_isShared_3547_ == 0)
{
v___x_3549_ = v___x_3546_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_ks_3543_);
lean_ctor_set(v_reuseFailAlloc_3561_, 1, v_vs_3544_);
v___x_3549_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
lean_object* v_newNode_3550_; size_t v___x_3551_; uint8_t v___x_3552_; 
v_newNode_3550_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v___x_3549_, v_x_3495_, v_x_3496_);
v___x_3551_ = ((size_t)7ULL);
v___x_3552_ = lean_usize_dec_le(v___x_3551_, v_x_3494_);
if (v___x_3552_ == 0)
{
lean_object* v___x_3553_; lean_object* v___x_3554_; uint8_t v___x_3555_; 
v___x_3553_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3550_);
v___x_3554_ = lean_unsigned_to_nat(4u);
v___x_3555_ = lean_nat_dec_lt(v___x_3553_, v___x_3554_);
lean_dec(v___x_3553_);
if (v___x_3555_ == 0)
{
lean_object* v_ks_3556_; lean_object* v_vs_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v_ks_3556_ = lean_ctor_get(v_newNode_3550_, 0);
lean_inc_ref(v_ks_3556_);
v_vs_3557_ = lean_ctor_get(v_newNode_3550_, 1);
lean_inc_ref(v_vs_3557_);
lean_dec_ref(v_newNode_3550_);
v___x_3558_ = lean_unsigned_to_nat(0u);
v___x_3559_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0);
v___x_3560_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_x_3494_, v_ks_3556_, v_vs_3557_, v___x_3558_, v___x_3559_);
lean_dec_ref(v_vs_3557_);
lean_dec_ref(v_ks_3556_);
return v___x_3560_;
}
else
{
return v_newNode_3550_;
}
}
else
{
return v_newNode_3550_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(size_t v_depth_3563_, lean_object* v_keys_3564_, lean_object* v_vals_3565_, lean_object* v_i_3566_, lean_object* v_entries_3567_){
_start:
{
lean_object* v___x_3568_; uint8_t v___x_3569_; 
v___x_3568_ = lean_array_get_size(v_keys_3564_);
v___x_3569_ = lean_nat_dec_lt(v_i_3566_, v___x_3568_);
if (v___x_3569_ == 0)
{
lean_dec(v_i_3566_);
return v_entries_3567_;
}
else
{
lean_object* v_k_3570_; lean_object* v_v_3571_; uint64_t v___x_3572_; size_t v_h_3573_; size_t v___x_3574_; lean_object* v___x_3575_; size_t v___x_3576_; size_t v___x_3577_; size_t v___x_3578_; size_t v_h_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v_k_3570_ = lean_array_fget_borrowed(v_keys_3564_, v_i_3566_);
v_v_3571_ = lean_array_fget_borrowed(v_vals_3565_, v_i_3566_);
v___x_3572_ = lean_string_hash(v_k_3570_);
v_h_3573_ = lean_uint64_to_usize(v___x_3572_);
v___x_3574_ = ((size_t)5ULL);
v___x_3575_ = lean_unsigned_to_nat(1u);
v___x_3576_ = ((size_t)1ULL);
v___x_3577_ = lean_usize_sub(v_depth_3563_, v___x_3576_);
v___x_3578_ = lean_usize_mul(v___x_3574_, v___x_3577_);
v_h_3579_ = lean_usize_shift_right(v_h_3573_, v___x_3578_);
v___x_3580_ = lean_nat_add(v_i_3566_, v___x_3575_);
lean_dec(v_i_3566_);
lean_inc(v_v_3571_);
lean_inc(v_k_3570_);
v___x_3581_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_entries_3567_, v_h_3579_, v_depth_3563_, v_k_3570_, v_v_3571_);
v_i_3566_ = v___x_3580_;
v_entries_3567_ = v___x_3581_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_depth_3583_, lean_object* v_keys_3584_, lean_object* v_vals_3585_, lean_object* v_i_3586_, lean_object* v_entries_3587_){
_start:
{
size_t v_depth_boxed_3588_; lean_object* v_res_3589_; 
v_depth_boxed_3588_ = lean_unbox_usize(v_depth_3583_);
lean_dec(v_depth_3583_);
v_res_3589_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_boxed_3588_, v_keys_3584_, v_vals_3585_, v_i_3586_, v_entries_3587_);
lean_dec_ref(v_vals_3585_);
lean_dec_ref(v_keys_3584_);
return v_res_3589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(lean_object* v_x_3590_, lean_object* v_x_3591_, lean_object* v_x_3592_, lean_object* v_x_3593_, lean_object* v_x_3594_){
_start:
{
size_t v_x_2721__boxed_3595_; size_t v_x_2722__boxed_3596_; lean_object* v_res_3597_; 
v_x_2721__boxed_3595_ = lean_unbox_usize(v_x_3591_);
lean_dec(v_x_3591_);
v_x_2722__boxed_3596_ = lean_unbox_usize(v_x_3592_);
lean_dec(v_x_3592_);
v_res_3597_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_3590_, v_x_2721__boxed_3595_, v_x_2722__boxed_3596_, v_x_3593_, v_x_3594_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(lean_object* v_x_3598_, lean_object* v_x_3599_, lean_object* v_x_3600_){
_start:
{
uint64_t v___x_3601_; size_t v___x_3602_; size_t v___x_3603_; lean_object* v___x_3604_; 
v___x_3601_ = lean_string_hash(v_x_3599_);
v___x_3602_ = lean_uint64_to_usize(v___x_3601_);
v___x_3603_ = ((size_t)1ULL);
v___x_3604_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_3598_, v___x_3602_, v___x_3603_, v_x_3599_, v_x_3600_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(lean_object* v_params_3606_){
_start:
{
lean_object* v___x_3607_; 
lean_inc(v_params_3606_);
v___x_3607_ = l_Lean_Lsp_instFromJsonSemanticTokensParams_fromJson(v_params_3606_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3623_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3610_ = v___x_3607_;
v_isShared_3611_ = v_isSharedCheck_3623_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3607_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3623_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
uint8_t v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3621_; 
v___x_3612_ = 3;
v___x_3613_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_3614_ = l_Lean_Json_compress(v_params_3606_);
v___x_3615_ = lean_string_append(v___x_3613_, v___x_3614_);
lean_dec_ref(v___x_3614_);
v___x_3616_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0));
v___x_3617_ = lean_string_append(v___x_3615_, v___x_3616_);
v___x_3618_ = lean_string_append(v___x_3617_, v_a_3608_);
lean_dec(v_a_3608_);
v___x_3619_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3619_, 0, v___x_3618_);
lean_ctor_set_uint8(v___x_3619_, sizeof(void*)*1, v___x_3612_);
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 0, v___x_3619_);
v___x_3621_ = v___x_3610_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v___x_3619_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
else
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
lean_dec(v_params_3606_);
v_a_3624_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3607_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3607_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3624_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(lean_object* v_params_3632_){
_start:
{
lean_object* v___x_3634_; 
v___x_3634_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_params_3632_);
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
v_a_3635_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3637_ = v___x_3634_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3634_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
lean_ctor_set_tag(v___x_3637_, 1);
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_a_3635_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
else
{
lean_object* v_a_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3650_; 
v_a_3643_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3650_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3645_ = v___x_3634_;
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_a_3643_);
lean_dec(v___x_3634_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3648_; 
if (v_isShared_3646_ == 0)
{
lean_ctor_set_tag(v___x_3645_, 0);
v___x_3648_ = v___x_3645_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_a_3643_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg___boxed(lean_object* v_params_3651_, lean_object* v_a_3652_){
_start:
{
lean_object* v_res_3653_; 
v_res_3653_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_3651_);
return v_res_3653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(lean_object* v_method_3654_, lean_object* v_inst_3655_, lean_object* v_handler_3656_, lean_object* v_param_3657_, lean_object* v_state_3658_, lean_object* v___y_3659_){
_start:
{
lean_object* v___x_3661_; 
v___x_3661_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_param_3657_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_a_3662_; lean_object* v___x_3663_; 
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
lean_inc(v_a_3662_);
lean_dec_ref_known(v___x_3661_, 1);
v___x_3663_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_3654_, v_state_3658_, lean_box(0), v_inst_3655_, v___y_3659_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v_a_3664_; lean_object* v___x_3665_; 
v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
lean_inc(v_a_3664_);
lean_dec_ref_known(v___x_3663_, 1);
lean_inc_ref(v___y_3659_);
v___x_3665_ = lean_apply_4(v_handler_3656_, v_a_3662_, v_a_3664_, v___y_3659_, lean_box(0));
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3689_; 
v_a_3666_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3668_ = v___x_3665_;
v_isShared_3669_ = v_isSharedCheck_3689_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_dec(v___x_3665_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3689_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v_fst_3670_; lean_object* v_snd_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3688_; 
v_fst_3670_ = lean_ctor_get(v_a_3666_, 0);
v_snd_3671_ = lean_ctor_get(v_a_3666_, 1);
v_isSharedCheck_3688_ = !lean_is_exclusive(v_a_3666_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3673_ = v_a_3666_;
v_isShared_3674_ = v_isSharedCheck_3688_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_snd_3671_);
lean_inc(v_fst_3670_);
lean_dec(v_a_3666_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3688_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v_response_3675_; uint8_t v_isComplete_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3682_; 
v_response_3675_ = lean_ctor_get(v_fst_3670_, 0);
lean_inc(v_response_3675_);
v_isComplete_3676_ = lean_ctor_get_uint8(v_fst_3670_, sizeof(void*)*1);
lean_dec(v_fst_3670_);
v___x_3677_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_response_3675_);
lean_inc(v___x_3677_);
v___x_3678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3678_, 0, v___x_3677_);
v___x_3679_ = l_Lean_Json_compress(v___x_3677_);
v___x_3680_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3680_, 0, v___x_3678_);
lean_ctor_set(v___x_3680_, 1, v___x_3679_);
lean_ctor_set_uint8(v___x_3680_, sizeof(void*)*2, v_isComplete_3676_);
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 0, v_inst_3655_);
v___x_3682_ = v___x_3673_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_inst_3655_);
lean_ctor_set(v_reuseFailAlloc_3687_, 1, v_snd_3671_);
v___x_3682_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
lean_object* v___x_3683_; lean_object* v___x_3685_; 
v___x_3683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3680_);
lean_ctor_set(v___x_3683_, 1, v___x_3682_);
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 0, v___x_3683_);
v___x_3685_ = v___x_3668_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v___x_3683_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
}
}
else
{
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3697_; 
lean_dec(v_inst_3655_);
v_a_3690_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3692_ = v___x_3665_;
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v___x_3665_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3695_; 
if (v_isShared_3693_ == 0)
{
v___x_3695_ = v___x_3692_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_a_3690_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
}
else
{
lean_object* v_a_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3705_; 
lean_dec(v_a_3662_);
lean_dec_ref(v_handler_3656_);
lean_dec(v_inst_3655_);
v_a_3698_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3700_ = v___x_3663_;
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_a_3698_);
lean_dec(v___x_3663_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3703_; 
if (v_isShared_3701_ == 0)
{
v___x_3703_ = v___x_3700_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_a_3698_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
}
}
else
{
lean_object* v_a_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3713_; 
lean_dec_ref(v_handler_3656_);
lean_dec(v_inst_3655_);
v_a_3706_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3708_ = v___x_3661_;
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_a_3706_);
lean_dec(v___x_3661_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3711_; 
if (v_isShared_3709_ == 0)
{
v___x_3711_ = v___x_3708_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_a_3706_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed(lean_object* v_method_3714_, lean_object* v_inst_3715_, lean_object* v_handler_3716_, lean_object* v_param_3717_, lean_object* v_state_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_){
_start:
{
lean_object* v_res_3721_; 
v_res_3721_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(v_method_3714_, v_inst_3715_, v_handler_3716_, v_param_3717_, v_state_3718_, v___y_3719_);
lean_dec_ref(v___y_3719_);
lean_dec(v_state_3718_);
lean_dec_ref(v_method_3714_);
return v_res_3721_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(lean_object* v_mutex_3722_, lean_object* v_a_x3f_3723_){
_start:
{
lean_object* v___x_3725_; lean_object* v___x_3726_; 
v___x_3725_ = lean_io_basemutex_unlock(v_mutex_3722_);
v___x_3726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3725_);
return v___x_3726_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0___boxed(lean_object* v_mutex_3727_, lean_object* v_a_x3f_3728_, lean_object* v___y_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_3727_, v_a_x3f_3728_);
lean_dec(v_a_x3f_3728_);
lean_dec(v_mutex_3727_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(lean_object* v_mutex_3731_, lean_object* v_k_3732_, lean_object* v___y_3733_){
_start:
{
lean_object* v_ref_3735_; lean_object* v_mutex_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; 
v_ref_3735_ = lean_ctor_get(v_mutex_3731_, 0);
lean_inc(v_ref_3735_);
v_mutex_3736_ = lean_ctor_get(v_mutex_3731_, 1);
lean_inc(v_mutex_3736_);
lean_dec_ref(v_mutex_3731_);
v___x_3737_ = lean_io_basemutex_lock(v_mutex_3736_);
lean_inc_ref(v___y_3733_);
v___x_3738_ = lean_apply_3(v_k_3732_, v_ref_3735_, v___y_3733_, lean_box(0));
if (lean_obj_tag(v___x_3738_) == 0)
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3755_; 
v_a_3739_ = lean_ctor_get(v___x_3738_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3741_ = v___x_3738_;
v_isShared_3742_ = v_isSharedCheck_3755_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3738_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3755_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
lean_inc(v_a_3739_);
if (v_isShared_3742_ == 0)
{
lean_ctor_set_tag(v___x_3741_, 1);
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3739_);
v___x_3744_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
lean_object* v___x_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3752_; 
v___x_3745_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_3736_, v___x_3744_);
lean_dec_ref(v___x_3744_);
lean_dec(v_mutex_3736_);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3752_ == 0)
{
lean_object* v_unused_3753_; 
v_unused_3753_ = lean_ctor_get(v___x_3745_, 0);
lean_dec(v_unused_3753_);
v___x_3747_ = v___x_3745_;
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
else
{
lean_dec(v___x_3745_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3750_; 
if (v_isShared_3748_ == 0)
{
lean_ctor_set(v___x_3747_, 0, v_a_3739_);
v___x_3750_ = v___x_3747_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3739_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
}
}
else
{
lean_object* v_a_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3765_; 
v_a_3756_ = lean_ctor_get(v___x_3738_, 0);
lean_inc(v_a_3756_);
lean_dec_ref_known(v___x_3738_, 1);
v___x_3757_ = lean_box(0);
v___x_3758_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_3736_, v___x_3757_);
lean_dec(v_mutex_3736_);
v_isSharedCheck_3765_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3765_ == 0)
{
lean_object* v_unused_3766_; 
v_unused_3766_ = lean_ctor_get(v___x_3758_, 0);
lean_dec(v_unused_3766_);
v___x_3760_ = v___x_3758_;
v_isShared_3761_ = v_isSharedCheck_3765_;
goto v_resetjp_3759_;
}
else
{
lean_dec(v___x_3758_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3765_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
lean_object* v___x_3763_; 
if (v_isShared_3761_ == 0)
{
lean_ctor_set_tag(v___x_3760_, 1);
lean_ctor_set(v___x_3760_, 0, v_a_3756_);
v___x_3763_ = v___x_3760_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_a_3756_);
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
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_mutex_3767_, lean_object* v_k_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_3767_, v_k_3768_, v___y_3769_);
lean_dec_ref(v___y_3769_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(lean_object* v_val_3772_, lean_object* v___f_3773_, lean_object* v_param_3774_, lean_object* v___x_3775_, lean_object* v_x_3776_, lean_object* v___y_3777_){
_start:
{
lean_object* v___x_3779_; lean_object* v___x_3780_; 
v___x_3779_ = lean_st_ref_get(v_val_3772_);
lean_inc_ref(v___y_3777_);
v___x_3780_ = lean_apply_4(v___f_3773_, v_param_3774_, v___x_3779_, v___y_3777_, lean_box(0));
if (lean_obj_tag(v___x_3780_) == 0)
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3790_; 
v_a_3781_ = lean_ctor_get(v___x_3780_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3783_ = v___x_3780_;
v_isShared_3784_ = v_isSharedCheck_3790_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3780_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3790_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v_snd_3785_; lean_object* v___x_3786_; lean_object* v___x_3788_; 
v_snd_3785_ = lean_ctor_get(v_a_3781_, 1);
lean_inc(v_snd_3785_);
lean_dec(v_a_3781_);
v___x_3786_ = lean_st_ref_swap(v_val_3772_, v_snd_3785_);
lean_dec(v___x_3786_);
if (v_isShared_3784_ == 0)
{
lean_ctor_set(v___x_3783_, 0, v___x_3775_);
v___x_3788_ = v___x_3783_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v___x_3775_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
else
{
lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3798_; 
v_a_3791_ = lean_ctor_get(v___x_3780_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3793_ = v___x_3780_;
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v___x_3780_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3796_; 
if (v_isShared_3794_ == 0)
{
v___x_3796_ = v___x_3793_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_a_3791_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed(lean_object* v_val_3799_, lean_object* v___f_3800_, lean_object* v_param_3801_, lean_object* v___x_3802_, lean_object* v_x_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
lean_object* v_res_3806_; 
v_res_3806_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(v_val_3799_, v___f_3800_, v_param_3801_, v___x_3802_, v_x_3803_, v___y_3804_);
lean_dec_ref(v___y_3804_);
lean_dec(v_val_3799_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(lean_object* v___f_3807_, lean_object* v___f_3808_, lean_object* v___x_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_){
_start:
{
lean_object* v___x_3813_; lean_object* v___x_3814_; 
v___x_3813_ = lean_st_ref_get(v___y_3810_);
v___x_3814_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_3813_, v___f_3807_, v___y_3811_);
if (lean_obj_tag(v___x_3814_) == 0)
{
lean_object* v_a_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3824_; 
v_a_3815_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3817_ = v___x_3814_;
v_isShared_3818_ = v_isSharedCheck_3824_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_a_3815_);
lean_dec(v___x_3814_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3824_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3822_; 
v___x_3819_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_3808_, v_a_3815_);
v___x_3820_ = lean_st_ref_swap(v___y_3810_, v___x_3819_);
lean_dec(v___x_3820_);
if (v_isShared_3818_ == 0)
{
lean_ctor_set(v___x_3817_, 0, v___x_3809_);
v___x_3822_ = v___x_3817_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v___x_3809_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
lean_dec_ref(v___f_3808_);
v_a_3825_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v___x_3814_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3814_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3825_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed(lean_object* v___f_3833_, lean_object* v___f_3834_, lean_object* v___x_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v_res_3839_; 
v_res_3839_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(v___f_3833_, v___f_3834_, v___x_3835_, v___y_3836_, v___y_3837_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
return v_res_3839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(lean_object* v_val_3840_, lean_object* v___f_3841_, lean_object* v___x_3842_, lean_object* v___f_3843_, lean_object* v_val_3844_, lean_object* v_param_3845_, lean_object* v___y_3846_){
_start:
{
lean_object* v___f_3848_; lean_object* v___f_3849_; lean_object* v___x_3850_; 
v___f_3848_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed), 7, 4);
lean_closure_set(v___f_3848_, 0, v_val_3840_);
lean_closure_set(v___f_3848_, 1, v___f_3841_);
lean_closure_set(v___f_3848_, 2, v_param_3845_);
lean_closure_set(v___f_3848_, 3, v___x_3842_);
v___f_3849_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed), 6, 3);
lean_closure_set(v___f_3849_, 0, v___f_3848_);
lean_closure_set(v___f_3849_, 1, v___f_3843_);
lean_closure_set(v___f_3849_, 2, v___x_3842_);
v___x_3850_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_3844_, v___f_3849_, v___y_3846_);
return v___x_3850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed(lean_object* v_val_3851_, lean_object* v___f_3852_, lean_object* v___x_3853_, lean_object* v___f_3854_, lean_object* v_val_3855_, lean_object* v_param_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(v_val_3851_, v___f_3852_, v___x_3853_, v___f_3854_, v_val_3855_, v_param_3856_, v___y_3857_);
lean_dec_ref(v___y_3857_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(lean_object* v___x_3860_, lean_object* v_x_3861_){
_start:
{
return v___x_3860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3___boxed(lean_object* v___x_3862_, lean_object* v_x_3863_){
_start:
{
lean_object* v_res_3864_; 
v_res_3864_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(v___x_3862_, v_x_3863_);
lean_dec_ref(v_x_3863_);
return v_res_3864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__0(lean_object* v_j_3865_){
_start:
{
lean_object* v___x_3866_; 
v___x_3866_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_j_3865_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3874_; 
v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3869_ = v___x_3866_;
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v___x_3866_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v___x_3872_; 
if (v_isShared_3870_ == 0)
{
v___x_3872_ = v___x_3869_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_a_3867_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
else
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3882_; 
v_a_3875_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3882_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3882_ == 0)
{
v___x_3877_ = v___x_3866_;
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v___x_3866_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___x_3880_; 
if (v_isShared_3878_ == 0)
{
v___x_3880_ = v___x_3877_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_a_3875_);
v___x_3880_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
return v___x_3880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(lean_object* v_val_3883_, lean_object* v___f_3884_, lean_object* v_param_3885_, lean_object* v_x_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3889_ = lean_st_ref_get(v_val_3883_);
lean_inc_ref(v___y_3887_);
v___x_3890_ = lean_apply_4(v___f_3884_, v_param_3885_, v___x_3889_, v___y_3887_, lean_box(0));
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3901_; 
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3901_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3901_ == 0)
{
v___x_3893_ = v___x_3890_;
v_isShared_3894_ = v_isSharedCheck_3901_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3890_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3901_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v_fst_3895_; lean_object* v_snd_3896_; lean_object* v___x_3897_; lean_object* v___x_3899_; 
v_fst_3895_ = lean_ctor_get(v_a_3891_, 0);
lean_inc(v_fst_3895_);
v_snd_3896_ = lean_ctor_get(v_a_3891_, 1);
lean_inc(v_snd_3896_);
lean_dec(v_a_3891_);
v___x_3897_ = lean_st_ref_swap(v_val_3883_, v_snd_3896_);
lean_dec(v___x_3897_);
if (v_isShared_3894_ == 0)
{
lean_ctor_set(v___x_3893_, 0, v_fst_3895_);
v___x_3899_ = v___x_3893_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v_fst_3895_);
v___x_3899_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
return v___x_3899_;
}
}
}
else
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3909_; 
v_a_3902_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3904_ = v___x_3890_;
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3890_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v___x_3907_; 
if (v_isShared_3905_ == 0)
{
v___x_3907_ = v___x_3904_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_a_3902_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed(lean_object* v_val_3910_, lean_object* v___f_3911_, lean_object* v_param_3912_, lean_object* v_x_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_){
_start:
{
lean_object* v_res_3916_; 
v_res_3916_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(v_val_3910_, v___f_3911_, v_param_3912_, v_x_3913_, v___y_3914_);
lean_dec_ref(v___y_3914_);
lean_dec(v_val_3910_);
return v_res_3916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(lean_object* v___f_3917_, lean_object* v___f_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_){
_start:
{
lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3922_ = lean_st_ref_get(v___y_3919_);
v___x_3923_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_3922_, v___f_3917_, v___y_3920_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3933_; 
v_a_3924_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3926_ = v___x_3923_;
v_isShared_3927_ = v_isSharedCheck_3933_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3923_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3933_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3931_; 
lean_inc(v_a_3924_);
v___x_3928_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_3918_, v_a_3924_);
v___x_3929_ = lean_st_ref_swap(v___y_3919_, v___x_3928_);
lean_dec(v___x_3929_);
if (v_isShared_3927_ == 0)
{
v___x_3931_ = v___x_3926_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_a_3924_);
v___x_3931_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
return v___x_3931_;
}
}
}
else
{
lean_dec_ref(v___f_3918_);
return v___x_3923_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed(lean_object* v___f_3934_, lean_object* v___f_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_){
_start:
{
lean_object* v_res_3939_; 
v_res_3939_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(v___f_3934_, v___f_3935_, v___y_3936_, v___y_3937_);
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3936_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(lean_object* v_val_3940_, lean_object* v___f_3941_, lean_object* v___f_3942_, lean_object* v_val_3943_, lean_object* v_param_3944_, lean_object* v___y_3945_){
_start:
{
lean_object* v___f_3947_; lean_object* v___f_3948_; lean_object* v___x_3949_; 
v___f_3947_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_3947_, 0, v_val_3940_);
lean_closure_set(v___f_3947_, 1, v___f_3941_);
lean_closure_set(v___f_3947_, 2, v_param_3944_);
v___f_3948_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed), 5, 2);
lean_closure_set(v___f_3948_, 0, v___f_3947_);
lean_closure_set(v___f_3948_, 1, v___f_3942_);
v___x_3949_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_3943_, v___f_3948_, v___y_3945_);
return v___x_3949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed(lean_object* v_val_3950_, lean_object* v___f_3951_, lean_object* v___f_3952_, lean_object* v_val_3953_, lean_object* v_param_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_){
_start:
{
lean_object* v_res_3957_; 
v_res_3957_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(v_val_3950_, v___f_3951_, v___f_3952_, v_val_3953_, v_param_3954_, v___y_3955_);
lean_dec_ref(v___y_3955_);
return v_res_3957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(lean_object* v_method_3958_, lean_object* v_inst_3959_, lean_object* v_onDidChange_3960_, lean_object* v_param_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_){
_start:
{
lean_object* v___x_3965_; 
v___x_3965_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_3958_, v___y_3962_, lean_box(0), v_inst_3959_, v___y_3963_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v_a_3966_; lean_object* v___x_3967_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
lean_inc(v_a_3966_);
lean_dec_ref_known(v___x_3965_, 1);
lean_inc_ref(v___y_3963_);
v___x_3967_ = lean_apply_4(v_onDidChange_3960_, v_param_3961_, v_a_3966_, v___y_3963_, lean_box(0));
if (lean_obj_tag(v___x_3967_) == 0)
{
lean_object* v_a_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_3986_; 
v_a_3968_ = lean_ctor_get(v___x_3967_, 0);
v_isSharedCheck_3986_ = !lean_is_exclusive(v___x_3967_);
if (v_isSharedCheck_3986_ == 0)
{
v___x_3970_ = v___x_3967_;
v_isShared_3971_ = v_isSharedCheck_3986_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_a_3968_);
lean_dec(v___x_3967_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_3986_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v_snd_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3984_; 
v_snd_3972_ = lean_ctor_get(v_a_3968_, 1);
v_isSharedCheck_3984_ = !lean_is_exclusive(v_a_3968_);
if (v_isSharedCheck_3984_ == 0)
{
lean_object* v_unused_3985_; 
v_unused_3985_ = lean_ctor_get(v_a_3968_, 0);
lean_dec(v_unused_3985_);
v___x_3974_ = v_a_3968_;
v_isShared_3975_ = v_isSharedCheck_3984_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_snd_3972_);
lean_dec(v_a_3968_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3984_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3977_; 
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 0, v_inst_3959_);
v___x_3977_ = v___x_3974_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_inst_3959_);
lean_ctor_set(v_reuseFailAlloc_3983_, 1, v_snd_3972_);
v___x_3977_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3981_; 
v___x_3978_ = lean_box(0);
v___x_3979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3978_);
lean_ctor_set(v___x_3979_, 1, v___x_3977_);
if (v_isShared_3971_ == 0)
{
lean_ctor_set(v___x_3970_, 0, v___x_3979_);
v___x_3981_ = v___x_3970_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v___x_3979_);
v___x_3981_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
return v___x_3981_;
}
}
}
}
}
else
{
lean_object* v_a_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3994_; 
lean_dec(v_inst_3959_);
v_a_3987_ = lean_ctor_get(v___x_3967_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3967_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3989_ = v___x_3967_;
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_a_3987_);
lean_dec(v___x_3967_);
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
lean_dec_ref(v_param_3961_);
lean_dec_ref(v_onDidChange_3960_);
lean_dec(v_inst_3959_);
v_a_3995_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3997_ = v___x_3965_;
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_a_3995_);
lean_dec(v___x_3965_);
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
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed(lean_object* v_method_4003_, lean_object* v_inst_4004_, lean_object* v_onDidChange_4005_, lean_object* v_param_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_){
_start:
{
lean_object* v_res_4010_; 
v_res_4010_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(v_method_4003_, v_inst_4004_, v_onDidChange_4005_, v_param_4006_, v___y_4007_, v___y_4008_);
lean_dec_ref(v___y_4008_);
lean_dec(v___y_4007_);
lean_dec_ref(v_method_4003_);
return v_res_4010_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_4018_; lean_object* v___x_4019_; 
v___x_4018_ = lean_box(0);
v___x_4019_ = lean_task_pure(v___x_4018_);
return v___x_4019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(lean_object* v_method_4020_, lean_object* v_completeness_4021_, lean_object* v_inst_4022_, lean_object* v_initState_4023_, lean_object* v_handler_4024_, lean_object* v_onDidChange_4025_){
_start:
{
lean_object* v___f_4027_; lean_object* v___f_4028_; lean_object* v___f_4029_; uint8_t v___x_4030_; 
v___f_4027_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0));
lean_inc_n(v_inst_4022_, 2);
lean_inc_ref_n(v_method_4020_, 2);
v___f_4028_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4028_, 0, v_method_4020_);
lean_closure_set(v___f_4028_, 1, v_inst_4022_);
lean_closure_set(v___f_4028_, 2, v_handler_4024_);
v___f_4029_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4029_, 0, v_method_4020_);
lean_closure_set(v___f_4029_, 1, v_inst_4022_);
lean_closure_set(v___f_4029_, 2, v_onDidChange_4025_);
v___x_4030_ = l_Lean_initializing();
if (v___x_4030_ == 0)
{
lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
lean_dec_ref(v___f_4029_);
lean_dec_ref(v___f_4028_);
lean_dec(v_initState_4023_);
lean_dec(v_inst_4022_);
lean_dec(v_completeness_4021_);
v___x_4031_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1));
v___x_4032_ = lean_string_append(v___x_4031_, v_method_4020_);
lean_dec_ref(v_method_4020_);
v___x_4033_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2));
v___x_4034_ = lean_string_append(v___x_4032_, v___x_4033_);
v___x_4035_ = lean_mk_io_user_error(v___x_4034_);
v___x_4036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4036_, 0, v___x_4035_);
return v___x_4036_;
}
else
{
lean_object* v___x_4037_; lean_object* v___f_4038_; lean_object* v___f_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___f_4044_; lean_object* v___f_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; 
v___x_4037_ = lean_box(0);
v___f_4038_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__3));
v___f_4039_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__4));
v___x_4040_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5);
v___x_4041_ = l_Std_Mutex_new___redArg(v___x_4040_);
v___x_4042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4042_, 0, v_inst_4022_);
lean_ctor_set(v___x_4042_, 1, v_initState_4023_);
lean_inc_ref(v___x_4042_);
v___x_4043_ = lean_st_mk_ref(v___x_4042_);
lean_inc_ref_n(v___x_4041_, 2);
lean_inc_ref(v___f_4028_);
lean_inc_n(v___x_4043_, 2);
v___f_4044_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_4044_, 0, v___x_4043_);
lean_closure_set(v___f_4044_, 1, v___f_4028_);
lean_closure_set(v___f_4044_, 2, v___f_4038_);
lean_closure_set(v___f_4044_, 3, v___x_4041_);
lean_inc_ref(v___f_4029_);
v___f_4045_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed), 8, 5);
lean_closure_set(v___f_4045_, 0, v___x_4043_);
lean_closure_set(v___f_4045_, 1, v___f_4029_);
lean_closure_set(v___f_4045_, 2, v___x_4037_);
lean_closure_set(v___f_4045_, 3, v___f_4039_);
lean_closure_set(v___f_4045_, 4, v___x_4041_);
v___x_4046_ = l_Lean_Server_statefulRequestHandlers;
v___x_4047_ = lean_st_ref_take(v___x_4046_);
v___x_4048_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4048_, 0, v___f_4027_);
lean_ctor_set(v___x_4048_, 1, v___f_4028_);
lean_ctor_set(v___x_4048_, 2, v___f_4044_);
lean_ctor_set(v___x_4048_, 3, v___f_4029_);
lean_ctor_set(v___x_4048_, 4, v___f_4045_);
lean_ctor_set(v___x_4048_, 5, v___x_4041_);
lean_ctor_set(v___x_4048_, 6, v___x_4042_);
lean_ctor_set(v___x_4048_, 7, v___x_4043_);
lean_ctor_set(v___x_4048_, 8, v_completeness_4021_);
v___x_4049_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_4047_, v_method_4020_, v___x_4048_);
v___x_4050_ = lean_st_ref_put(v___x_4046_, v___x_4049_);
v___x_4051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4050_);
return v___x_4051_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___boxed(lean_object* v_method_4052_, lean_object* v_completeness_4053_, lean_object* v_inst_4054_, lean_object* v_initState_4055_, lean_object* v_handler_4056_, lean_object* v_onDidChange_4057_, lean_object* v_a_4058_){
_start:
{
lean_object* v_res_4059_; 
v_res_4059_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4052_, v_completeness_4053_, v_inst_4054_, v_initState_4055_, v_handler_4056_, v_onDidChange_4057_);
return v_res_4059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(lean_object* v_method_4061_, lean_object* v_completeness_4062_, lean_object* v_inst_4063_, lean_object* v_initState_4064_, lean_object* v_handler_4065_, lean_object* v_onDidChange_4066_){
_start:
{
lean_object* v___x_4068_; lean_object* v___x_4069_; uint8_t v___x_4070_; 
v___x_4068_ = l_Lean_Server_requestHandlers;
v___x_4069_ = lean_st_ref_get(v___x_4068_);
v___x_4070_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_4069_, v_method_4061_);
lean_dec(v___x_4069_);
if (v___x_4070_ == 0)
{
lean_object* v___x_4071_; 
v___x_4071_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4061_, v_completeness_4062_, v_inst_4063_, v_initState_4064_, v_handler_4065_, v_onDidChange_4066_);
return v___x_4071_;
}
else
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
lean_dec_ref(v_onDidChange_4066_);
lean_dec_ref(v_handler_4065_);
lean_dec(v_initState_4064_);
lean_dec(v_inst_4063_);
lean_dec(v_completeness_4062_);
v___x_4072_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1));
v___x_4073_ = lean_string_append(v___x_4072_, v_method_4061_);
lean_dec_ref(v_method_4061_);
v___x_4074_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_4075_ = lean_string_append(v___x_4073_, v___x_4074_);
v___x_4076_ = lean_mk_io_user_error(v___x_4075_);
v___x_4077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4076_);
return v___x_4077_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___boxed(lean_object* v_method_4078_, lean_object* v_completeness_4079_, lean_object* v_inst_4080_, lean_object* v_initState_4081_, lean_object* v_handler_4082_, lean_object* v_onDidChange_4083_, lean_object* v_a_4084_){
_start:
{
lean_object* v_res_4085_; 
v_res_4085_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4078_, v_completeness_4079_, v_inst_4080_, v_initState_4081_, v_handler_4082_, v_onDidChange_4083_);
return v_res_4085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(lean_object* v_method_4086_, lean_object* v_refreshMethod_4087_, lean_object* v_refreshIntervalMs_4088_, lean_object* v_inst_4089_, lean_object* v_initState_4090_, lean_object* v_handler_4091_, lean_object* v_onDidChange_4092_){
_start:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4094_, 0, v_refreshMethod_4087_);
lean_ctor_set(v___x_4094_, 1, v_refreshIntervalMs_4088_);
v___x_4095_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4086_, v___x_4094_, v_inst_4089_, v_initState_4090_, v_handler_4091_, v_onDidChange_4092_);
return v___x_4095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_method_4096_, lean_object* v_refreshMethod_4097_, lean_object* v_refreshIntervalMs_4098_, lean_object* v_inst_4099_, lean_object* v_initState_4100_, lean_object* v_handler_4101_, lean_object* v_onDidChange_4102_, lean_object* v_a_4103_){
_start:
{
lean_object* v_res_4104_; 
v_res_4104_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_4096_, v_refreshMethod_4097_, v_refreshIntervalMs_4098_, v_inst_4099_, v_initState_4100_, v_handler_4101_, v_onDidChange_4102_);
return v_res_4104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_params_4105_){
_start:
{
lean_object* v___x_4106_; 
lean_inc(v_params_4105_);
v___x_4106_ = l_Lean_Lsp_instFromJsonSemanticTokensRangeParams_fromJson(v_params_4105_);
if (lean_obj_tag(v___x_4106_) == 0)
{
lean_object* v_a_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4122_; 
v_a_4107_ = lean_ctor_get(v___x_4106_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4106_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4109_ = v___x_4106_;
v_isShared_4110_ = v_isSharedCheck_4122_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_a_4107_);
lean_dec(v___x_4106_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4122_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
uint8_t v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4120_; 
v___x_4111_ = 3;
v___x_4112_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_4113_ = l_Lean_Json_compress(v_params_4105_);
v___x_4114_ = lean_string_append(v___x_4112_, v___x_4113_);
lean_dec_ref(v___x_4113_);
v___x_4115_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0));
v___x_4116_ = lean_string_append(v___x_4114_, v___x_4115_);
v___x_4117_ = lean_string_append(v___x_4116_, v_a_4107_);
lean_dec(v_a_4107_);
v___x_4118_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4118_, 0, v___x_4117_);
lean_ctor_set_uint8(v___x_4118_, sizeof(void*)*1, v___x_4111_);
if (v_isShared_4110_ == 0)
{
lean_ctor_set(v___x_4109_, 0, v___x_4118_);
v___x_4120_ = v___x_4109_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v___x_4118_);
v___x_4120_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
return v___x_4120_;
}
}
}
else
{
lean_object* v_a_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4130_; 
lean_dec(v_params_4105_);
v_a_4123_ = lean_ctor_get(v___x_4106_, 0);
v_isSharedCheck_4130_ = !lean_is_exclusive(v___x_4106_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_4125_ = v___x_4106_;
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_a_4123_);
lean_dec(v___x_4106_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4128_; 
if (v_isShared_4126_ == 0)
{
v___x_4128_ = v___x_4125_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4129_; 
v_reuseFailAlloc_4129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v_a_4123_);
v___x_4128_ = v_reuseFailAlloc_4129_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
return v___x_4128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__0(lean_object* v_j_4131_){
_start:
{
lean_object* v___x_4132_; 
v___x_4132_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_j_4131_);
if (lean_obj_tag(v___x_4132_) == 0)
{
lean_object* v_a_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4140_; 
v_a_4133_ = lean_ctor_get(v___x_4132_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v___x_4132_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_4135_ = v___x_4132_;
v_isShared_4136_ = v_isSharedCheck_4140_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_a_4133_);
lean_dec(v___x_4132_);
v___x_4135_ = lean_box(0);
v_isShared_4136_ = v_isSharedCheck_4140_;
goto v_resetjp_4134_;
}
v_resetjp_4134_:
{
lean_object* v___x_4138_; 
if (v_isShared_4136_ == 0)
{
v___x_4138_ = v___x_4135_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v_a_4133_);
v___x_4138_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
return v___x_4138_;
}
}
}
else
{
lean_object* v_a_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4149_; 
v_a_4141_ = lean_ctor_get(v___x_4132_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v___x_4132_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4143_ = v___x_4132_;
v_isShared_4144_ = v_isSharedCheck_4149_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_a_4141_);
lean_dec(v___x_4132_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4149_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v_textDocument_4145_; lean_object* v___x_4147_; 
v_textDocument_4145_ = lean_ctor_get(v_a_4141_, 0);
lean_inc_ref(v_textDocument_4145_);
lean_dec(v_a_4141_);
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 0, v_textDocument_4145_);
v___x_4147_ = v___x_4143_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_textDocument_4145_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(lean_object* v_serialize_x3f_4150_, uint8_t v_val_4151_, lean_object* v___y_4152_){
_start:
{
if (lean_obj_tag(v___y_4152_) == 0)
{
lean_object* v_a_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4160_; 
lean_dec(v_serialize_x3f_4150_);
v_a_4153_ = lean_ctor_get(v___y_4152_, 0);
v_isSharedCheck_4160_ = !lean_is_exclusive(v___y_4152_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4155_ = v___y_4152_;
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_a_4153_);
lean_dec(v___y_4152_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v___x_4158_; 
if (v_isShared_4156_ == 0)
{
v___x_4158_ = v___x_4155_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_a_4153_);
v___x_4158_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
return v___x_4158_;
}
}
}
else
{
if (lean_obj_tag(v_serialize_x3f_4150_) == 1)
{
lean_object* v_a_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4172_; 
v_a_4161_ = lean_ctor_get(v___y_4152_, 0);
v_isSharedCheck_4172_ = !lean_is_exclusive(v___y_4152_);
if (v_isSharedCheck_4172_ == 0)
{
v___x_4163_ = v___y_4152_;
v_isShared_4164_ = v_isSharedCheck_4172_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_a_4161_);
lean_dec(v___y_4152_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4172_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v_val_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4170_; 
v_val_4165_ = lean_ctor_get(v_serialize_x3f_4150_, 0);
lean_inc(v_val_4165_);
lean_dec_ref_known(v_serialize_x3f_4150_, 1);
v___x_4166_ = lean_box(0);
v___x_4167_ = lean_apply_1(v_val_4165_, v_a_4161_);
v___x_4168_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4168_, 0, v___x_4166_);
lean_ctor_set(v___x_4168_, 1, v___x_4167_);
lean_ctor_set_uint8(v___x_4168_, sizeof(void*)*2, v_val_4151_);
if (v_isShared_4164_ == 0)
{
lean_ctor_set(v___x_4163_, 0, v___x_4168_);
v___x_4170_ = v___x_4163_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v___x_4168_);
v___x_4170_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
return v___x_4170_;
}
}
}
else
{
lean_object* v_a_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4184_; 
lean_dec(v_serialize_x3f_4150_);
v_a_4173_ = lean_ctor_get(v___y_4152_, 0);
v_isSharedCheck_4184_ = !lean_is_exclusive(v___y_4152_);
if (v_isSharedCheck_4184_ == 0)
{
v___x_4175_ = v___y_4152_;
v_isShared_4176_ = v_isSharedCheck_4184_;
goto v_resetjp_4174_;
}
else
{
lean_inc(v_a_4173_);
lean_dec(v___y_4152_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4184_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4182_; 
v___x_4177_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_a_4173_);
lean_inc(v___x_4177_);
v___x_4178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4178_, 0, v___x_4177_);
v___x_4179_ = l_Lean_Json_compress(v___x_4177_);
v___x_4180_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4180_, 0, v___x_4178_);
lean_ctor_set(v___x_4180_, 1, v___x_4179_);
lean_ctor_set_uint8(v___x_4180_, sizeof(void*)*2, v_val_4151_);
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 0, v___x_4180_);
v___x_4182_ = v___x_4175_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v___x_4180_);
v___x_4182_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
return v___x_4182_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object* v_serialize_x3f_4185_, lean_object* v_val_4186_, lean_object* v___y_4187_){
_start:
{
uint8_t v_val_3768__boxed_4188_; lean_object* v_res_4189_; 
v_val_3768__boxed_4188_ = lean_unbox(v_val_4186_);
v_res_4189_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(v_serialize_x3f_4185_, v_val_3768__boxed_4188_, v___y_4187_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_params_4190_){
_start:
{
lean_object* v___x_4192_; 
v___x_4192_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_params_4190_);
if (lean_obj_tag(v___x_4192_) == 0)
{
lean_object* v_a_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4200_; 
v_a_4193_ = lean_ctor_get(v___x_4192_, 0);
v_isSharedCheck_4200_ = !lean_is_exclusive(v___x_4192_);
if (v_isSharedCheck_4200_ == 0)
{
v___x_4195_ = v___x_4192_;
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_a_4193_);
lean_dec(v___x_4192_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v___x_4198_; 
if (v_isShared_4196_ == 0)
{
lean_ctor_set_tag(v___x_4195_, 1);
v___x_4198_ = v___x_4195_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v_a_4193_);
v___x_4198_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
return v___x_4198_;
}
}
}
else
{
lean_object* v_a_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4208_; 
v_a_4201_ = lean_ctor_get(v___x_4192_, 0);
v_isSharedCheck_4208_ = !lean_is_exclusive(v___x_4192_);
if (v_isSharedCheck_4208_ == 0)
{
v___x_4203_ = v___x_4192_;
v_isShared_4204_ = v_isSharedCheck_4208_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_a_4201_);
lean_dec(v___x_4192_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4208_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v___x_4206_; 
if (v_isShared_4204_ == 0)
{
lean_ctor_set_tag(v___x_4203_, 0);
v___x_4206_ = v___x_4203_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v_a_4201_);
v___x_4206_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
return v___x_4206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_params_4209_, lean_object* v_a_4210_){
_start:
{
lean_object* v_res_4211_; 
v_res_4211_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_4209_);
return v_res_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(lean_object* v_handler_4212_, lean_object* v___f_4213_, lean_object* v_j_4214_, lean_object* v___y_4215_){
_start:
{
lean_object* v___x_4217_; 
v___x_4217_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_j_4214_);
if (lean_obj_tag(v___x_4217_) == 0)
{
lean_object* v_a_4218_; lean_object* v___x_4219_; 
v_a_4218_ = lean_ctor_get(v___x_4217_, 0);
lean_inc(v_a_4218_);
lean_dec_ref_known(v___x_4217_, 1);
lean_inc_ref(v___y_4215_);
v___x_4219_ = lean_apply_3(v_handler_4212_, v_a_4218_, v___y_4215_, lean_box(0));
if (lean_obj_tag(v___x_4219_) == 0)
{
lean_object* v_a_4220_; lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4228_; 
v_a_4220_ = lean_ctor_get(v___x_4219_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4219_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4222_ = v___x_4219_;
v_isShared_4223_ = v_isSharedCheck_4228_;
goto v_resetjp_4221_;
}
else
{
lean_inc(v_a_4220_);
lean_dec(v___x_4219_);
v___x_4222_ = lean_box(0);
v_isShared_4223_ = v_isSharedCheck_4228_;
goto v_resetjp_4221_;
}
v_resetjp_4221_:
{
lean_object* v___x_4224_; lean_object* v___x_4226_; 
v___x_4224_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4213_, v_a_4220_);
if (v_isShared_4223_ == 0)
{
lean_ctor_set(v___x_4222_, 0, v___x_4224_);
v___x_4226_ = v___x_4222_;
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
lean_dec_ref(v___f_4213_);
v_a_4229_ = lean_ctor_get(v___x_4219_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4219_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4231_ = v___x_4219_;
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_a_4229_);
lean_dec(v___x_4219_);
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
else
{
lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4244_; 
lean_dec_ref(v___f_4213_);
lean_dec_ref(v_handler_4212_);
v_a_4237_ = lean_ctor_get(v___x_4217_, 0);
v_isSharedCheck_4244_ = !lean_is_exclusive(v___x_4217_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4239_ = v___x_4217_;
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_dec(v___x_4217_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4242_; 
if (v_isShared_4240_ == 0)
{
v___x_4242_ = v___x_4239_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_a_4237_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object* v_handler_4245_, lean_object* v___f_4246_, lean_object* v_j_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_){
_start:
{
lean_object* v_res_4250_; 
v_res_4250_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(v_handler_4245_, v___f_4246_, v_j_4247_, v___y_4248_);
lean_dec_ref(v___y_4248_);
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(lean_object* v_method_4253_, lean_object* v_handler_4254_, lean_object* v_serialize_x3f_4255_){
_start:
{
lean_object* v___f_4257_; uint8_t v___x_4258_; 
v___f_4257_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0));
v___x_4258_ = l_Lean_initializing();
if (v___x_4258_ == 0)
{
lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
lean_dec(v_serialize_x3f_4255_);
lean_dec_ref(v_handler_4254_);
v___x_4259_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1));
v___x_4260_ = lean_string_append(v___x_4259_, v_method_4253_);
lean_dec_ref(v_method_4253_);
v___x_4261_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2));
v___x_4262_ = lean_string_append(v___x_4260_, v___x_4261_);
v___x_4263_ = lean_mk_io_user_error(v___x_4262_);
v___x_4264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4264_, 0, v___x_4263_);
return v___x_4264_;
}
else
{
lean_object* v___x_4265_; lean_object* v___f_4266_; lean_object* v___f_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; uint8_t v___x_4270_; 
v___x_4265_ = lean_box(v___x_4258_);
v___f_4266_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed), 3, 2);
lean_closure_set(v___f_4266_, 0, v_serialize_x3f_4255_);
lean_closure_set(v___f_4266_, 1, v___x_4265_);
v___f_4267_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_4267_, 0, v_handler_4254_);
lean_closure_set(v___f_4267_, 1, v___f_4266_);
v___x_4268_ = l_Lean_Server_requestHandlers;
v___x_4269_ = lean_st_ref_get(v___x_4268_);
v___x_4270_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_4269_, v_method_4253_);
lean_dec(v___x_4269_);
if (v___x_4270_ == 0)
{
lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
v___x_4271_ = lean_st_ref_take(v___x_4268_);
v___x_4272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4272_, 0, v___f_4257_);
lean_ctor_set(v___x_4272_, 1, v___f_4267_);
v___x_4273_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_4271_, v_method_4253_, v___x_4272_);
v___x_4274_ = lean_st_ref_put(v___x_4268_, v___x_4273_);
v___x_4275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4275_, 0, v___x_4274_);
return v___x_4275_;
}
else
{
lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; 
lean_dec_ref(v___f_4267_);
v___x_4276_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1));
v___x_4277_ = lean_string_append(v___x_4276_, v_method_4253_);
lean_dec_ref(v_method_4253_);
v___x_4278_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_4279_ = lean_string_append(v___x_4277_, v___x_4278_);
v___x_4280_ = lean_mk_io_user_error(v___x_4279_);
v___x_4281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4281_, 0, v___x_4280_);
return v___x_4281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_4282_, lean_object* v_handler_4283_, lean_object* v_serialize_x3f_4284_, lean_object* v_a_4285_){
_start:
{
lean_object* v_res_4286_; 
v_res_4286_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v_method_4282_, v_handler_4283_, v_serialize_x3f_4284_);
return v_res_4286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; 
v___x_4294_ = ((lean_object*)(l_Lean_Server_FileWorker_instImpl_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7_));
v___x_4295_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4296_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4297_ = lean_box(0);
v___x_4298_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v___x_4295_, v___x_4296_, v___x_4297_);
if (lean_obj_tag(v___x_4298_) == 0)
{
lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; 
lean_dec_ref_known(v___x_4298_, 1);
v___x_4299_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4300_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4301_ = lean_unsigned_to_nat(2000u);
v___x_4302_ = lean_box(0);
v___x_4303_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__4_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4304_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__5_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4305_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v___x_4299_, v___x_4300_, v___x_4301_, v___x_4294_, v___x_4302_, v___x_4303_, v___x_4304_);
return v___x_4305_;
}
else
{
return v___x_4298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2____boxed(lean_object* v_a_4306_){
_start:
{
lean_object* v_res_4307_; 
v_res_4307_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_();
return v_res_4307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(lean_object* v_method_4308_, lean_object* v_refreshMethod_4309_, lean_object* v_refreshIntervalMs_4310_, lean_object* v_stateType_4311_, lean_object* v_inst_4312_, lean_object* v_initState_4313_, lean_object* v_handler_4314_, lean_object* v_onDidChange_4315_){
_start:
{
lean_object* v___x_4317_; 
v___x_4317_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_4308_, v_refreshMethod_4309_, v_refreshIntervalMs_4310_, v_inst_4312_, v_initState_4313_, v_handler_4314_, v_onDidChange_4315_);
return v___x_4317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___boxed(lean_object* v_method_4318_, lean_object* v_refreshMethod_4319_, lean_object* v_refreshIntervalMs_4320_, lean_object* v_stateType_4321_, lean_object* v_inst_4322_, lean_object* v_initState_4323_, lean_object* v_handler_4324_, lean_object* v_onDidChange_4325_, lean_object* v_a_4326_){
_start:
{
lean_object* v_res_4327_; 
v_res_4327_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(v_method_4318_, v_refreshMethod_4319_, v_refreshIntervalMs_4320_, v_stateType_4321_, v_inst_4322_, v_initState_4323_, v_handler_4324_, v_onDidChange_4325_);
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_params_4328_, lean_object* v_a_4329_){
_start:
{
lean_object* v___x_4331_; 
v___x_4331_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_4328_);
return v___x_4331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_params_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_){
_start:
{
lean_object* v_res_4335_; 
v_res_4335_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(v_params_4332_, v_a_4333_);
lean_dec_ref(v_a_4333_);
return v_res_4335_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_4336_, lean_object* v_x_4337_, lean_object* v_x_4338_){
_start:
{
uint8_t v___x_4339_; 
v___x_4339_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_4337_, v_x_4338_);
return v___x_4339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object* v_00_u03b2_4340_, lean_object* v_x_4341_, lean_object* v_x_4342_){
_start:
{
uint8_t v_res_4343_; lean_object* v_r_4344_; 
v_res_4343_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(v_00_u03b2_4340_, v_x_4341_, v_x_4342_);
lean_dec_ref(v_x_4342_);
lean_dec_ref(v_x_4341_);
v_r_4344_ = lean_box(v_res_4343_);
return v_r_4344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3(lean_object* v_00_u03b2_4345_, lean_object* v_x_4346_, lean_object* v_x_4347_, lean_object* v_x_4348_){
_start:
{
lean_object* v___x_4349_; 
v___x_4349_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v_x_4346_, v_x_4347_, v_x_4348_);
return v___x_4349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(lean_object* v_method_4350_, lean_object* v_completeness_4351_, lean_object* v_stateType_4352_, lean_object* v_inst_4353_, lean_object* v_initState_4354_, lean_object* v_handler_4355_, lean_object* v_onDidChange_4356_){
_start:
{
lean_object* v___x_4358_; 
v___x_4358_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4350_, v_completeness_4351_, v_inst_4353_, v_initState_4354_, v_handler_4355_, v_onDidChange_4356_);
return v___x_4358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object* v_method_4359_, lean_object* v_completeness_4360_, lean_object* v_stateType_4361_, lean_object* v_inst_4362_, lean_object* v_initState_4363_, lean_object* v_handler_4364_, lean_object* v_onDidChange_4365_, lean_object* v_a_4366_){
_start:
{
lean_object* v_res_4367_; 
v_res_4367_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(v_method_4359_, v_completeness_4360_, v_stateType_4361_, v_inst_4362_, v_initState_4363_, v_handler_4364_, v_onDidChange_4365_);
return v_res_4367_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(lean_object* v_00_u03b2_4368_, lean_object* v_x_4369_, size_t v_x_4370_, lean_object* v_x_4371_){
_start:
{
uint8_t v___x_4372_; 
v___x_4372_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_4369_, v_x_4370_, v_x_4371_);
return v___x_4372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4373_, lean_object* v_x_4374_, lean_object* v_x_4375_, lean_object* v_x_4376_){
_start:
{
size_t v_x_4087__boxed_4377_; uint8_t v_res_4378_; lean_object* v_r_4379_; 
v_x_4087__boxed_4377_ = lean_unbox_usize(v_x_4375_);
lean_dec(v_x_4375_);
v_res_4378_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(v_00_u03b2_4373_, v_x_4374_, v_x_4087__boxed_4377_, v_x_4376_);
lean_dec_ref(v_x_4376_);
lean_dec_ref(v_x_4374_);
v_r_4379_ = lean_box(v_res_4378_);
return v_r_4379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_object* v_00_u03b2_4380_, lean_object* v_x_4381_, size_t v_x_4382_, size_t v_x_4383_, lean_object* v_x_4384_, lean_object* v_x_4385_){
_start:
{
lean_object* v___x_4386_; 
v___x_4386_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_4381_, v_x_4382_, v_x_4383_, v_x_4384_, v_x_4385_);
return v___x_4386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4387_, lean_object* v_x_4388_, lean_object* v_x_4389_, lean_object* v_x_4390_, lean_object* v_x_4391_, lean_object* v_x_4392_){
_start:
{
size_t v_x_4098__boxed_4393_; size_t v_x_4099__boxed_4394_; lean_object* v_res_4395_; 
v_x_4098__boxed_4393_ = lean_unbox_usize(v_x_4389_);
lean_dec(v_x_4389_);
v_x_4099__boxed_4394_ = lean_unbox_usize(v_x_4390_);
lean_dec(v_x_4390_);
v_res_4395_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(v_00_u03b2_4387_, v_x_4388_, v_x_4098__boxed_4393_, v_x_4099__boxed_4394_, v_x_4391_, v_x_4392_);
return v_res_4395_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(lean_object* v_00_u03b1_4396_, lean_object* v_00_u03b2_4397_, lean_object* v_mutex_4398_, lean_object* v_k_4399_, lean_object* v___y_4400_){
_start:
{
lean_object* v___x_4402_; 
v___x_4402_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_4398_, v_k_4399_, v___y_4400_);
return v___x_4402_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b1_4403_, lean_object* v_00_u03b2_4404_, lean_object* v_mutex_4405_, lean_object* v_k_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_){
_start:
{
lean_object* v_res_4409_; 
v_res_4409_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(v_00_u03b1_4403_, v_00_u03b2_4404_, v_mutex_4405_, v_k_4406_, v___y_4407_);
lean_dec_ref(v___y_4407_);
return v_res_4409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(lean_object* v_method_4410_, lean_object* v_completeness_4411_, lean_object* v_stateType_4412_, lean_object* v_inst_4413_, lean_object* v_initState_4414_, lean_object* v_handler_4415_, lean_object* v_onDidChange_4416_){
_start:
{
lean_object* v___x_4418_; 
v___x_4418_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4410_, v_completeness_4411_, v_inst_4413_, v_initState_4414_, v_handler_4415_, v_onDidChange_4416_);
return v___x_4418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___boxed(lean_object* v_method_4419_, lean_object* v_completeness_4420_, lean_object* v_stateType_4421_, lean_object* v_inst_4422_, lean_object* v_initState_4423_, lean_object* v_handler_4424_, lean_object* v_onDidChange_4425_, lean_object* v_a_4426_){
_start:
{
lean_object* v_res_4427_; 
v_res_4427_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(v_method_4419_, v_completeness_4420_, v_stateType_4421_, v_inst_4422_, v_initState_4423_, v_handler_4424_, v_onDidChange_4425_);
return v_res_4427_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_4428_, lean_object* v_keys_4429_, lean_object* v_vals_4430_, lean_object* v_heq_4431_, lean_object* v_i_4432_, lean_object* v_k_4433_){
_start:
{
uint8_t v___x_4434_; 
v___x_4434_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_4429_, v_i_4432_, v_k_4433_);
return v___x_4434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4435_, lean_object* v_keys_4436_, lean_object* v_vals_4437_, lean_object* v_heq_4438_, lean_object* v_i_4439_, lean_object* v_k_4440_){
_start:
{
uint8_t v_res_4441_; lean_object* v_r_4442_; 
v_res_4441_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(v_00_u03b2_4435_, v_keys_4436_, v_vals_4437_, v_heq_4438_, v_i_4439_, v_k_4440_);
lean_dec_ref(v_k_4440_);
lean_dec_ref(v_vals_4437_);
lean_dec_ref(v_keys_4436_);
v_r_4442_ = lean_box(v_res_4441_);
return v_r_4442_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_4443_, lean_object* v_n_4444_, lean_object* v_k_4445_, lean_object* v_v_4446_){
_start:
{
lean_object* v___x_4447_; 
v___x_4447_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_n_4444_, v_k_4445_, v_v_4446_);
return v___x_4447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_4448_, size_t v_depth_4449_, lean_object* v_keys_4450_, lean_object* v_vals_4451_, lean_object* v_heq_4452_, lean_object* v_i_4453_, lean_object* v_entries_4454_){
_start:
{
lean_object* v___x_4455_; 
v___x_4455_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_4449_, v_keys_4450_, v_vals_4451_, v_i_4453_, v_entries_4454_);
return v___x_4455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_4456_, lean_object* v_depth_4457_, lean_object* v_keys_4458_, lean_object* v_vals_4459_, lean_object* v_heq_4460_, lean_object* v_i_4461_, lean_object* v_entries_4462_){
_start:
{
size_t v_depth_boxed_4463_; lean_object* v_res_4464_; 
v_depth_boxed_4463_ = lean_unbox_usize(v_depth_4457_);
lean_dec(v_depth_4457_);
v_res_4464_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(v_00_u03b2_4456_, v_depth_boxed_4463_, v_keys_4458_, v_vals_4459_, v_heq_4460_, v_i_4461_, v_entries_4462_);
lean_dec_ref(v_vals_4459_);
lean_dec_ref(v_keys_4458_);
return v_res_4464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(lean_object* v_params_4465_, lean_object* v_a_4466_){
_start:
{
lean_object* v___x_4468_; 
v___x_4468_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_4465_);
return v___x_4468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___boxed(lean_object* v_params_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_){
_start:
{
lean_object* v_res_4472_; 
v_res_4472_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(v_params_4469_, v_a_4470_);
lean_dec_ref(v_a_4470_);
return v_res_4472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_4473_, lean_object* v_x_4474_, lean_object* v_x_4475_, lean_object* v_x_4476_, lean_object* v_x_4477_){
_start:
{
lean_object* v___x_4478_; 
v___x_4478_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_x_4474_, v_x_4475_, v_x_4476_, v_x_4477_);
return v___x_4478_;
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
