// Lean compiler output
// Module: Lean.Server.CodeActions.Basic
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
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonCodeActionParams_fromJson(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t l_Lean_initializing();
lean_object* lean_mk_io_user_error(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Lsp_instToJsonCodeAction_toJson(lean_object*);
lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Server_requestHandlers;
lean_object* lean_st_ref_get(lean_object*);
uint64_t lean_string_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonCodeAction_fromJson(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Server_RequestError_internalError(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Server_instInhabitedRequestError_default;
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_indentExpr(lean_object*);
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_has_compile_error(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_runCoreM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_checkCancelled(lean_object*);
lean_object* l_Lean_Lsp_instToJsonCodeActionParams_toJson(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_withWaitFindSnap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Server_RequestError_ofIoError(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestError_invalidParams(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_instToJsonCodeActionResolveData_toJson_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "params"};
static const lean_object* l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__0 = (const lean_object*)&l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__0_value;
static const lean_string_object l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "providerName"};
static const lean_object* l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__1 = (const lean_object*)&l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__1_value;
static const lean_string_object l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "providerResultIndex"};
static const lean_object* l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__2 = (const lean_object*)&l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__2_value;
static const lean_array_object l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__3 = (const lean_object*)&l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Server_instToJsonCodeActionResolveData_toJson(lean_object*);
static const lean_closure_object l_Lean_Server_instToJsonCodeActionResolveData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_instToJsonCodeActionResolveData_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instToJsonCodeActionResolveData___closed__0 = (const lean_object*)&l_Lean_Server_instToJsonCodeActionResolveData___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_instToJsonCodeActionResolveData = (const lean_object*)&l_Lean_Server_instToJsonCodeActionResolveData___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__0 = (const lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__0_value;
static const lean_string_object l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Server"};
static const lean_object* l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__1 = (const lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__1_value;
static const lean_string_object l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "CodeActionResolveData"};
static const lean_object* l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__2 = (const lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__2_value;
static const lean_ctor_object l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__3_value_aux_0),((lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__3_value_aux_1),((lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(41, 163, 251, 30, 79, 190, 187, 231)}};
static const lean_object* l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__3 = (const lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__3_value;
static lean_once_cell_t l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__4;
static const lean_string_object l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__5 = (const lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__6;
static const lean_ctor_object l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 17, 68, 35, 208, 145, 117, 163)}};
static const lean_object* l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__7 = (const lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__7_value;
static lean_once_cell_t l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__8;
static lean_once_cell_t l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__9;
static const lean_string_object l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__10 = (const lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__11;
static const lean_ctor_object l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 181, 198, 121, 111, 102, 201, 148)}};
static const lean_object* l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__12 = (const lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__12_value;
static lean_once_cell_t l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__13;
static lean_once_cell_t l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__14;
static lean_once_cell_t l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__15;
static const lean_ctor_object l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(68, 69, 136, 239, 46, 100, 203, 21)}};
static const lean_object* l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__16 = (const lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__16_value;
static lean_once_cell_t l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__17;
static lean_once_cell_t l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__18;
static lean_once_cell_t l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__19;
LEAN_EXPORT lean_object* l_Lean_Server_instFromJsonCodeActionResolveData_fromJson(lean_object*);
static const lean_closure_object l_Lean_Server_instFromJsonCodeActionResolveData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_instFromJsonCodeActionResolveData_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instFromJsonCodeActionResolveData___closed__0 = (const lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_instFromJsonCodeActionResolveData = (const lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData___closed__0_value;
static const lean_string_object l_panic___at___00Lean_Server_CodeAction_getFileSource_x21_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_panic___at___00Lean_Server_CodeAction_getFileSource_x21_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_Server_CodeAction_getFileSource_x21_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_CodeAction_getFileSource_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_Server_CodeAction_getFileSource_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Server.CodeActions.Basic"};
static const lean_object* l_Lean_Server_CodeAction_getFileSource_x21___closed__0 = (const lean_object*)&l_Lean_Server_CodeAction_getFileSource_x21___closed__0_value;
static const lean_string_object l_Lean_Server_CodeAction_getFileSource_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.Server.CodeAction.getFileSource!"};
static const lean_object* l_Lean_Server_CodeAction_getFileSource_x21___closed__1 = (const lean_object*)&l_Lean_Server_CodeAction_getFileSource_x21___closed__1_value;
static const lean_string_object l_Lean_Server_CodeAction_getFileSource_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "no data param on code action "};
static const lean_object* l_Lean_Server_CodeAction_getFileSource_x21___closed__2 = (const lean_object*)&l_Lean_Server_CodeAction_getFileSource_x21___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Server_CodeAction_getFileSource_x21(lean_object*);
static const lean_closure_object l_Lean_Server_instFileSourceCodeAction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_CodeAction_getFileSource_x21, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instFileSourceCodeAction___closed__0 = (const lean_object*)&l_Lean_Server_instFileSourceCodeAction___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_instFileSourceCodeAction = (const lean_object*)&l_Lean_Server_instFileSourceCodeAction___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_instCoeCodeActionLazyCodeAction___lam__0(lean_object*);
static const lean_closure_object l_Lean_Server_instCoeCodeActionLazyCodeAction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_instCoeCodeActionLazyCodeAction___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instCoeCodeActionLazyCodeAction___closed__0 = (const lean_object*)&l_Lean_Server_instCoeCodeActionLazyCodeAction___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_instCoeCodeActionLazyCodeAction = (const lean_object*)&l_Lean_Server_instCoeCodeActionLazyCodeAction___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedCodeActionProvider___aux__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedCodeActionProvider___aux__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedCodeActionProvider___aux__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedCodeActionProvider___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedCodeActionProvider___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedCodeActionProvider___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_instInhabitedCodeActionProvider___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_instInhabitedCodeActionProvider___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instInhabitedCodeActionProvider___closed__0 = (const lean_object*)&l_Lean_Server_instInhabitedCodeActionProvider___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_instInhabitedCodeActionProvider = (const lean_object*)&l_Lean_Server_instInhabitedCodeActionProvider___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_2573400817____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_2573400817____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_builtinCodeActionProviders;
LEAN_EXPORT lean_object* l_Lean_Server_addBuiltinCodeActionProvider(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_addBuiltinCodeActionProvider___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_(lean_object*);
static const lean_closure_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_insert, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "codeActionProviderExt"};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 40, 10, 229, 67, 12, 129, 142)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__5_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 8, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__5_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__5_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_codeActionProviderExt;
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid attribute scope: Attribute `["};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "]` must be global, not `"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__5;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "global"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__6_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__7 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__7_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__8 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Cannot add attribute `["};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "]`: Declaration `"};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` has type"};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__5;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "\nbut `["};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__6_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__7;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "]` can only be added to declarations of type"};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__8 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__8_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__21;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "addBuiltinCodeActionProvider"};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "CodeActionProvider"};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(79, 45, 83, 138, 97, 177, 55, 171)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__4_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "CodeActions"};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__4_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__4_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__5_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__4_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(41, 109, 98, 186, 215, 54, 31, 240)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__5_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__5_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__6_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Basic"};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__6_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__6_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__7_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__5_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__6_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 156, 164, 13, 237, 167, 211, 120)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__7_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__7_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__8_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__7_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(231, 236, 211, 153, 183, 200, 194, 142)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__8_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__8_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__9_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__8_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(218, 170, 13, 173, 36, 216, 196, 218)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__9_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__9_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__10_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__9_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(207, 127, 135, 167, 105, 120, 107, 85)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__10_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__10_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__11_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__11_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__11_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__12_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__10_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__11_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(78, 126, 20, 13, 61, 118, 74, 86)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__12_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__12_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__13_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__13_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__13_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__14_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__12_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__13_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 190, 141, 117, 213, 113, 13, 74)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__14_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__14_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__15_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__14_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(98, 52, 0, 130, 198, 230, 46, 197)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__15_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__15_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__16_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__15_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(71, 157, 19, 223, 35, 0, 13, 34)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__16_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__16_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__17_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__16_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__4_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(209, 137, 0, 217, 239, 233, 195, 40)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__17_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__17_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__18_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__17_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__6_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(54, 243, 113, 54, 127, 25, 120, 16)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__18_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__18_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__19_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__18_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1656927832) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(147, 227, 181, 202, 147, 137, 254, 160)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__19_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__19_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__20_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__20_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__20_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__21_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__19_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__20_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 144, 64, 31, 165, 31, 253, 43)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__21_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__21_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__22_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__22_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__22_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__23_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__21_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__22_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(76, 113, 109, 139, 146, 133, 143, 148)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__23_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__23_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__24_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__23_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(117, 166, 231, 135, 42, 93, 24, 222)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__24_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__24_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__25_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 108, .m_capacity = 108, .m_length = 107, .m_data = "Use to decorate methods for suggesting code actions. This is a low-level interface for making code actions."};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__25_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__25_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__26_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "(builtin) "};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__26_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__26_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "builtin_code_action_provider"};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(165, 9, 40, 2, 206, 24, 214, 24)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "code_action_provider"};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 50, 164, 33, 247, 115, 55, 128)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg___closed__0_value_aux_0),((lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(110, 233, 106, 27, 160, 7, 34, 38)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleCodeAction_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleCodeAction_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_handleCodeAction_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_handleCodeAction_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_handleCodeAction_spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_handleCodeAction_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_handleCodeAction_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeAction___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeAction___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Server_handleCodeAction_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Server_handleCodeAction_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_handleCodeAction_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_handleCodeAction_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Server_handleCodeAction___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_handleCodeAction___lam__1___closed__0 = (const lean_object*)&l_Lean_Server_handleCodeAction___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeAction___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeAction___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_handleCodeAction___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeAction___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeAction___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeAction___lam__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_handleCodeAction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_handleCodeAction___lam__0___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Server_handleCodeAction___closed__0 = (const lean_object*)&l_Lean_Server_handleCodeAction___closed__0_value;
static const lean_array_object l_Lean_Server_handleCodeAction___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_handleCodeAction___closed__1 = (const lean_object*)&l_Lean_Server_handleCodeAction___closed__1_value;
static const lean_closure_object l_Lean_Server_handleCodeAction___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_handleCodeAction___lam__3___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Server_handleCodeAction___closed__1_value)} };
static const lean_object* l_Lean_Server_handleCodeAction___closed__2 = (const lean_object*)&l_Lean_Server_handleCodeAction___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeAction(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeAction___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Server_handleCodeAction_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Server_handleCodeAction_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_handleCodeAction_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Cannot parse request params: "};
static const lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__0_value;
static const lean_string_object l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__0(lean_object*);
static const lean_closure_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__0 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__0_value;
static const lean_string_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Failed to register LSP request handler for '"};
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__1 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__1_value;
static const lean_string_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "': only possible during initialization"};
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__2 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__2_value;
static const lean_string_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "': already registered"};
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__3 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "textDocument/codeAction"};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_handleCodeAction___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_handleCodeActionResolve___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Failed to resolve code action index "};
static const lean_object* l_Lean_Server_handleCodeActionResolve___lam__0___closed__0 = (const lean_object*)&l_Lean_Server_handleCodeActionResolve___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeActionResolve___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeActionResolve___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeActionResolve___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeActionResolve___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_handleCodeActionResolve___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "snapshot not found"};
static const lean_object* l_Lean_Server_handleCodeActionResolve___closed__0 = (const lean_object*)&l_Lean_Server_handleCodeActionResolve___closed__0_value;
static lean_once_cell_t l_Lean_Server_handleCodeActionResolve___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_handleCodeActionResolve___closed__1;
static lean_once_cell_t l_Lean_Server_handleCodeActionResolve___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_handleCodeActionResolve___closed__2;
static const lean_string_object l_Lean_Server_handleCodeActionResolve___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Expected a data field on CodeAction."};
static const lean_object* l_Lean_Server_handleCodeActionResolve___closed__3 = (const lean_object*)&l_Lean_Server_handleCodeActionResolve___closed__3_value;
static lean_once_cell_t l_Lean_Server_handleCodeActionResolve___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_handleCodeActionResolve___closed__4;
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeActionResolve(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeActionResolve___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__0(lean_object*);
static const lean_closure_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___closed__0 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "codeAction/resolve"};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_handleCodeActionResolve___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_instToJsonCodeActionResolveData_toJson_spec__0(lean_object* v_a_1_, lean_object* v_a_2_){
_start:
{
if (lean_obj_tag(v_a_1_) == 0)
{
lean_object* v___x_3_; 
v___x_3_ = lean_array_to_list(v_a_2_);
return v___x_3_;
}
else
{
lean_object* v_head_4_; lean_object* v_tail_5_; lean_object* v___x_6_; 
v_head_4_ = lean_ctor_get(v_a_1_, 0);
lean_inc(v_head_4_);
v_tail_5_ = lean_ctor_get(v_a_1_, 1);
lean_inc(v_tail_5_);
lean_dec_ref_known(v_a_1_, 2);
v___x_6_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2_, v_head_4_);
v_a_1_ = v_tail_5_;
v_a_2_ = v___x_6_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instToJsonCodeActionResolveData_toJson(lean_object* v_x_13_){
_start:
{
lean_object* v_params_14_; lean_object* v_providerName_15_; lean_object* v_providerResultIndex_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; uint8_t v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v_params_14_ = lean_ctor_get(v_x_13_, 0);
lean_inc_ref(v_params_14_);
v_providerName_15_ = lean_ctor_get(v_x_13_, 1);
lean_inc(v_providerName_15_);
v_providerResultIndex_16_ = lean_ctor_get(v_x_13_, 2);
lean_inc(v_providerResultIndex_16_);
lean_dec_ref(v_x_13_);
v___x_17_ = ((lean_object*)(l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__0));
v___x_18_ = l_Lean_Lsp_instToJsonCodeActionParams_toJson(v_params_14_);
v___x_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_19_, 0, v___x_17_);
lean_ctor_set(v___x_19_, 1, v___x_18_);
v___x_20_ = lean_box(0);
v___x_21_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_21_, 0, v___x_19_);
lean_ctor_set(v___x_21_, 1, v___x_20_);
v___x_22_ = ((lean_object*)(l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__1));
v___x_23_ = 1;
v___x_24_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_providerName_15_, v___x_23_);
v___x_25_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
v___x_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_26_, 0, v___x_22_);
lean_ctor_set(v___x_26_, 1, v___x_25_);
v___x_27_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
lean_ctor_set(v___x_27_, 1, v___x_20_);
v___x_28_ = ((lean_object*)(l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__2));
v___x_29_ = l_Lean_JsonNumber_fromNat(v_providerResultIndex_16_);
v___x_30_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
v___x_31_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_31_, 0, v___x_28_);
lean_ctor_set(v___x_31_, 1, v___x_30_);
v___x_32_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
lean_ctor_set(v___x_32_, 1, v___x_20_);
v___x_33_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
lean_ctor_set(v___x_33_, 1, v___x_20_);
v___x_34_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_27_);
lean_ctor_set(v___x_34_, 1, v___x_33_);
v___x_35_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_35_, 0, v___x_21_);
lean_ctor_set(v___x_35_, 1, v___x_34_);
v___x_36_ = ((lean_object*)(l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__3));
v___x_37_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_instToJsonCodeActionResolveData_toJson_spec__0(v___x_35_, v___x_36_);
v___x_38_ = l_Lean_Json_mkObj(v___x_37_);
lean_dec(v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__0(lean_object* v_j_41_, lean_object* v_k_42_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = l_Lean_Json_getObjValD(v_j_41_, v_k_42_);
v___x_44_ = l_Lean_Lsp_instFromJsonCodeActionParams_fromJson(v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__0___boxed(lean_object* v_j_45_, lean_object* v_k_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__0(v_j_45_, v_k_46_);
lean_dec_ref(v_k_46_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__1(lean_object* v_j_48_, lean_object* v_k_49_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = l_Lean_Json_getObjValD(v_j_48_, v_k_49_);
v___x_51_ = l_Lean_Name_fromJson_x3f(v___x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__1___boxed(lean_object* v_j_52_, lean_object* v_k_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__1(v_j_52_, v_k_53_);
lean_dec_ref(v_k_53_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__2(lean_object* v_j_55_, lean_object* v_k_56_){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = l_Lean_Json_getObjValD(v_j_55_, v_k_56_);
v___x_58_ = l_Lean_Json_getNat_x3f(v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__2___boxed(lean_object* v_j_59_, lean_object* v_k_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__2(v_j_59_, v_k_60_);
lean_dec_ref(v_k_60_);
return v_res_61_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__4(void){
_start:
{
uint8_t v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_69_ = 1;
v___x_70_ = ((lean_object*)(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__3));
v___x_71_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_70_, v___x_69_);
return v___x_71_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__6(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = ((lean_object*)(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__5));
v___x_74_ = lean_obj_once(&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__4, &l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__4_once, _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__4);
v___x_75_ = lean_string_append(v___x_74_, v___x_73_);
return v___x_75_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__8(void){
_start:
{
uint8_t v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_78_ = 1;
v___x_79_ = ((lean_object*)(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__7));
v___x_80_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_79_, v___x_78_);
return v___x_80_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__9(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_81_ = lean_obj_once(&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__8, &l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__8_once, _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__8);
v___x_82_ = lean_obj_once(&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__6, &l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__6_once, _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__6);
v___x_83_ = lean_string_append(v___x_82_, v___x_81_);
return v___x_83_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__11(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = ((lean_object*)(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__10));
v___x_86_ = lean_obj_once(&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__9, &l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__9_once, _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__9);
v___x_87_ = lean_string_append(v___x_86_, v___x_85_);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__13(void){
_start:
{
uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = 1;
v___x_91_ = ((lean_object*)(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__12));
v___x_92_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_91_, v___x_90_);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__14(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lean_obj_once(&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__13, &l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__13_once, _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__13);
v___x_94_ = lean_obj_once(&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__6, &l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__6_once, _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__6);
v___x_95_ = lean_string_append(v___x_94_, v___x_93_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__15(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = ((lean_object*)(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__10));
v___x_97_ = lean_obj_once(&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__14, &l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__14_once, _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__14);
v___x_98_ = lean_string_append(v___x_97_, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__17(void){
_start:
{
uint8_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = 1;
v___x_102_ = ((lean_object*)(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__16));
v___x_103_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_102_, v___x_101_);
return v___x_103_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__18(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = lean_obj_once(&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__17, &l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__17_once, _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__17);
v___x_105_ = lean_obj_once(&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__6, &l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__6_once, _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__6);
v___x_106_ = lean_string_append(v___x_105_, v___x_104_);
return v___x_106_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__19(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_107_ = ((lean_object*)(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__10));
v___x_108_ = lean_obj_once(&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__18, &l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__18_once, _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__18);
v___x_109_ = lean_string_append(v___x_108_, v___x_107_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instFromJsonCodeActionResolveData_fromJson(lean_object* v_json_110_){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = ((lean_object*)(l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__0));
lean_inc(v_json_110_);
v___x_112_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__0(v_json_110_, v___x_111_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v_a_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_122_; 
lean_dec(v_json_110_);
v_a_113_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_122_ == 0)
{
v___x_115_ = v___x_112_;
v_isShared_116_ = v_isSharedCheck_122_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_a_113_);
lean_dec(v___x_112_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_122_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_120_; 
v___x_117_ = lean_obj_once(&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__11, &l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__11_once, _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__11);
v___x_118_ = lean_string_append(v___x_117_, v_a_113_);
lean_dec(v_a_113_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 0, v___x_118_);
v___x_120_ = v___x_115_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_118_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
else
{
lean_object* v_a_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v_a_123_ = lean_ctor_get(v___x_112_, 0);
lean_inc(v_a_123_);
lean_dec_ref_known(v___x_112_, 1);
v___x_124_ = ((lean_object*)(l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__1));
lean_inc(v_json_110_);
v___x_125_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__1(v_json_110_, v___x_124_);
if (lean_obj_tag(v___x_125_) == 0)
{
lean_object* v_a_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_135_; 
lean_dec(v_a_123_);
lean_dec(v_json_110_);
v_a_126_ = lean_ctor_get(v___x_125_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_135_ == 0)
{
v___x_128_ = v___x_125_;
v_isShared_129_ = v_isSharedCheck_135_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_a_126_);
lean_dec(v___x_125_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_135_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_130_ = lean_obj_once(&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__15, &l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__15_once, _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__15);
v___x_131_ = lean_string_append(v___x_130_, v_a_126_);
lean_dec(v_a_126_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 0, v___x_131_);
v___x_133_ = v___x_128_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
else
{
lean_object* v_a_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_a_136_ = lean_ctor_get(v___x_125_, 0);
lean_inc(v_a_136_);
lean_dec_ref_known(v___x_125_, 1);
v___x_137_ = ((lean_object*)(l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__2));
v___x_138_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__2(v_json_110_, v___x_137_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_148_; 
lean_dec(v_a_136_);
lean_dec(v_a_123_);
v_a_139_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_148_ == 0)
{
v___x_141_ = v___x_138_;
v_isShared_142_ = v_isSharedCheck_148_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_138_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_148_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_143_ = lean_obj_once(&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__19, &l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__19_once, _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__19);
v___x_144_ = lean_string_append(v___x_143_, v_a_139_);
lean_dec(v_a_139_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v___x_144_);
v___x_146_ = v___x_141_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_144_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
else
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_157_; 
v_a_149_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_157_ == 0)
{
v___x_151_ = v___x_138_;
v_isShared_152_ = v_isSharedCheck_157_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_138_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_157_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_153_; lean_object* v___x_155_; 
v___x_153_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_153_, 0, v_a_123_);
lean_ctor_set(v___x_153_, 1, v_a_136_);
lean_ctor_set(v___x_153_, 2, v_a_149_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 0, v___x_153_);
v___x_155_ = v___x_151_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_153_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_CodeAction_getFileSource_x21_spec__0(lean_object* v_msg_161_){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = ((lean_object*)(l_panic___at___00Lean_Server_CodeAction_getFileSource_x21_spec__0___closed__0));
v___x_163_ = lean_panic_fn_borrowed(v___x_162_, v_msg_161_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CodeAction_getFileSource_x21(lean_object* v_ca_167_){
_start:
{
lean_object* v_a_169_; lean_object* v_data_x3f_176_; 
v_data_x3f_176_ = lean_ctor_get(v_ca_167_, 9);
if (lean_obj_tag(v_data_x3f_176_) == 1)
{
lean_object* v_val_177_; lean_object* v___x_178_; 
lean_inc_ref(v_data_x3f_176_);
lean_dec_ref(v_ca_167_);
v_val_177_ = lean_ctor_get(v_data_x3f_176_, 0);
lean_inc(v_val_177_);
lean_dec_ref_known(v_data_x3f_176_, 1);
v___x_178_ = l_Lean_Server_instFromJsonCodeActionResolveData_fromJson(v_val_177_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
lean_dec_ref_known(v___x_178_, 1);
v_a_169_ = v_a_179_;
goto v___jp_168_;
}
else
{
lean_object* v_a_180_; lean_object* v_params_181_; lean_object* v_textDocument_182_; 
v_a_180_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_180_);
lean_dec_ref_known(v___x_178_, 1);
v_params_181_ = lean_ctor_get(v_a_180_, 0);
lean_inc_ref(v_params_181_);
lean_dec(v_a_180_);
v_textDocument_182_ = lean_ctor_get(v_params_181_, 2);
lean_inc_ref(v_textDocument_182_);
lean_dec_ref(v_params_181_);
return v_textDocument_182_;
}
}
else
{
lean_object* v_title_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_title_183_ = lean_ctor_get(v_ca_167_, 2);
lean_inc_ref(v_title_183_);
lean_dec_ref(v_ca_167_);
v___x_184_ = ((lean_object*)(l_Lean_Server_CodeAction_getFileSource_x21___closed__2));
v___x_185_ = lean_string_append(v___x_184_, v_title_183_);
lean_dec_ref(v_title_183_);
v_a_169_ = v___x_185_;
goto v___jp_168_;
}
v___jp_168_:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_170_ = ((lean_object*)(l_Lean_Server_CodeAction_getFileSource_x21___closed__0));
v___x_171_ = ((lean_object*)(l_Lean_Server_CodeAction_getFileSource_x21___closed__1));
v___x_172_ = lean_unsigned_to_nat(47u);
v___x_173_ = lean_unsigned_to_nat(22u);
v___x_174_ = l_mkPanicMessageWithDecl(v___x_170_, v___x_171_, v___x_172_, v___x_173_, v_a_169_);
lean_dec_ref(v_a_169_);
v___x_175_ = l_panic___at___00Lean_Server_CodeAction_getFileSource_x21_spec__0(v___x_174_);
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instCoeCodeActionLazyCodeAction___lam__0(lean_object* v_c_188_){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = lean_box(0);
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v_c_188_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedCodeActionProvider___aux__1___redArg(){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = l_Lean_Server_instInhabitedRequestError_default;
v___x_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedCodeActionProvider___aux__1___redArg___boxed(lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Server_instInhabitedCodeActionProvider___aux__1___redArg();
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedCodeActionProvider___aux__1(lean_object* v_x_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = l_Lean_Server_instInhabitedRequestError_default;
v___x_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedCodeActionProvider___aux__1___boxed(lean_object* v_x_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_Server_instInhabitedCodeActionProvider___aux__1(v_x_204_, v_a_205_, v_a_206_);
lean_dec_ref(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec_ref(v_x_204_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedCodeActionProvider___lam__0(lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = l_Lean_Server_instInhabitedRequestError_default;
v___x_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedCodeActionProvider___lam__0___boxed(lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Server_instInhabitedCodeActionProvider___lam__0(v___y_215_, v___y_216_, v___y_217_);
lean_dec_ref(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec_ref(v___y_215_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_2573400817____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_223_ = lean_box(1);
v___x_224_ = lean_st_mk_ref(v___x_223_);
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_2573400817____hygCtx___hyg_2____boxed(lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_2573400817____hygCtx___hyg_2_();
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_addBuiltinCodeActionProvider(lean_object* v_decl_228_, lean_object* v_provider_229_){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_231_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_builtinCodeActionProviders;
v___x_232_ = lean_st_ref_take(v___x_231_);
v___x_233_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_decl_228_, v_provider_229_, v___x_232_);
v___x_234_ = lean_st_ref_put(v___x_231_, v___x_233_);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_addBuiltinCodeActionProvider___boxed(lean_object* v_decl_236_, lean_object* v_provider_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_Server_addBuiltinCodeActionProvider(v_decl_236_, v_provider_237_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__0(lean_object* v_as_240_, size_t v_i_241_, size_t v_stop_242_, lean_object* v_b_243_){
_start:
{
uint8_t v___x_244_; 
v___x_244_ = lean_usize_dec_eq(v_i_241_, v_stop_242_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; lean_object* v___x_246_; size_t v___x_247_; size_t v___x_248_; 
v___x_245_ = lean_array_uget_borrowed(v_as_240_, v_i_241_);
lean_inc(v___x_245_);
v___x_246_ = l_Lean_NameSet_insert(v_b_243_, v___x_245_);
v___x_247_ = ((size_t)1ULL);
v___x_248_ = lean_usize_add(v_i_241_, v___x_247_);
v_i_241_ = v___x_248_;
v_b_243_ = v___x_246_;
goto _start;
}
else
{
return v_b_243_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_250_, lean_object* v_i_251_, lean_object* v_stop_252_, lean_object* v_b_253_){
_start:
{
size_t v_i_boxed_254_; size_t v_stop_boxed_255_; lean_object* v_res_256_; 
v_i_boxed_254_ = lean_unbox_usize(v_i_251_);
lean_dec(v_i_251_);
v_stop_boxed_255_ = lean_unbox_usize(v_stop_252_);
lean_dec(v_stop_252_);
v_res_256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__0(v_as_250_, v_i_boxed_254_, v_stop_boxed_255_, v_b_253_);
lean_dec_ref(v_as_250_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__1(lean_object* v_as_257_, size_t v_i_258_, size_t v_stop_259_, lean_object* v_b_260_){
_start:
{
lean_object* v___y_262_; uint8_t v___x_266_; 
v___x_266_ = lean_usize_dec_eq(v_i_258_, v_stop_259_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_267_ = lean_array_uget_borrowed(v_as_257_, v_i_258_);
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = lean_array_get_size(v___x_267_);
v___x_270_ = lean_nat_dec_lt(v___x_268_, v___x_269_);
if (v___x_270_ == 0)
{
v___y_262_ = v_b_260_;
goto v___jp_261_;
}
else
{
size_t v___x_271_; size_t v___x_272_; lean_object* v___x_273_; 
v___x_271_ = ((size_t)0ULL);
v___x_272_ = lean_usize_of_nat(v___x_269_);
v___x_273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__0(v___x_267_, v___x_271_, v___x_272_, v_b_260_);
v___y_262_ = v___x_273_;
goto v___jp_261_;
}
}
else
{
return v_b_260_;
}
v___jp_261_:
{
size_t v___x_263_; size_t v___x_264_; 
v___x_263_ = ((size_t)1ULL);
v___x_264_ = lean_usize_add(v_i_258_, v___x_263_);
v_i_258_ = v___x_264_;
v_b_260_ = v___y_262_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_274_, lean_object* v_i_275_, lean_object* v_stop_276_, lean_object* v_b_277_){
_start:
{
size_t v_i_boxed_278_; size_t v_stop_boxed_279_; lean_object* v_res_280_; 
v_i_boxed_278_ = lean_unbox_usize(v_i_275_);
lean_dec(v_i_275_);
v_stop_boxed_279_ = lean_unbox_usize(v_stop_276_);
lean_dec(v_stop_276_);
v_res_280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__1(v_as_274_, v_i_boxed_278_, v_stop_boxed_279_, v_b_277_);
lean_dec_ref(v_as_274_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_(lean_object* v_nss_281_){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_282_ = l_Lean_NameSet_empty;
v___x_283_ = lean_unsigned_to_nat(0u);
v___x_284_ = lean_array_get_size(v_nss_281_);
v___x_285_ = lean_nat_dec_lt(v___x_283_, v___x_284_);
if (v___x_285_ == 0)
{
return v___x_282_;
}
else
{
size_t v___x_286_; size_t v___x_287_; lean_object* v___x_288_; 
v___x_286_ = ((size_t)0ULL);
v___x_287_ = lean_usize_of_nat(v___x_284_);
v___x_288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__1(v_nss_281_, v___x_286_, v___x_287_, v___x_282_);
return v___x_288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2____boxed(lean_object* v_nss_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_(v_nss_289_);
lean_dec_ref(v_nss_289_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2_spec__2___redArg(lean_object* v_hi_291_, lean_object* v_pivot_292_, lean_object* v_as_293_, lean_object* v_i_294_, lean_object* v_k_295_){
_start:
{
uint8_t v___x_296_; 
v___x_296_ = lean_nat_dec_lt(v_k_295_, v_hi_291_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; 
lean_dec(v_k_295_);
v___x_297_ = lean_array_fswap(v_as_293_, v_i_294_, v_hi_291_);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v_i_294_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
return v___x_298_;
}
else
{
lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_299_ = lean_array_fget_borrowed(v_as_293_, v_k_295_);
v___x_300_ = l_Lean_Name_quickLt(v___x_299_, v_pivot_292_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_unsigned_to_nat(1u);
v___x_302_ = lean_nat_add(v_k_295_, v___x_301_);
lean_dec(v_k_295_);
v_k_295_ = v___x_302_;
goto _start;
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_304_ = lean_array_fswap(v_as_293_, v_i_294_, v_k_295_);
v___x_305_ = lean_unsigned_to_nat(1u);
v___x_306_ = lean_nat_add(v_i_294_, v___x_305_);
lean_dec(v_i_294_);
v___x_307_ = lean_nat_add(v_k_295_, v___x_305_);
lean_dec(v_k_295_);
v_as_293_ = v___x_304_;
v_i_294_ = v___x_306_;
v_k_295_ = v___x_307_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2_spec__2___redArg___boxed(lean_object* v_hi_309_, lean_object* v_pivot_310_, lean_object* v_as_311_, lean_object* v_i_312_, lean_object* v_k_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2_spec__2___redArg(v_hi_309_, v_pivot_310_, v_as_311_, v_i_312_, v_k_313_);
lean_dec(v_pivot_310_);
lean_dec(v_hi_309_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg(lean_object* v_n_315_, lean_object* v_as_316_, lean_object* v_lo_317_, lean_object* v_hi_318_){
_start:
{
lean_object* v___y_320_; uint8_t v___x_330_; 
v___x_330_ = lean_nat_dec_lt(v_lo_317_, v_hi_318_);
if (v___x_330_ == 0)
{
lean_dec(v_lo_317_);
return v_as_316_;
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v_mid_333_; lean_object* v___y_335_; lean_object* v___y_341_; lean_object* v___x_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_331_ = lean_nat_add(v_lo_317_, v_hi_318_);
v___x_332_ = lean_unsigned_to_nat(1u);
v_mid_333_ = lean_nat_shiftr(v___x_331_, v___x_332_);
lean_dec(v___x_331_);
v___x_346_ = lean_array_fget_borrowed(v_as_316_, v_mid_333_);
v___x_347_ = lean_array_fget_borrowed(v_as_316_, v_lo_317_);
v___x_348_ = l_Lean_Name_quickLt(v___x_346_, v___x_347_);
if (v___x_348_ == 0)
{
v___y_341_ = v_as_316_;
goto v___jp_340_;
}
else
{
lean_object* v___x_349_; 
v___x_349_ = lean_array_fswap(v_as_316_, v_lo_317_, v_mid_333_);
v___y_341_ = v___x_349_;
goto v___jp_340_;
}
v___jp_334_:
{
lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_336_ = lean_array_fget_borrowed(v___y_335_, v_mid_333_);
v___x_337_ = lean_array_fget_borrowed(v___y_335_, v_hi_318_);
v___x_338_ = l_Lean_Name_quickLt(v___x_336_, v___x_337_);
if (v___x_338_ == 0)
{
lean_dec(v_mid_333_);
v___y_320_ = v___y_335_;
goto v___jp_319_;
}
else
{
lean_object* v___x_339_; 
v___x_339_ = lean_array_fswap(v___y_335_, v_mid_333_, v_hi_318_);
lean_dec(v_mid_333_);
v___y_320_ = v___x_339_;
goto v___jp_319_;
}
}
v___jp_340_:
{
lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_342_ = lean_array_fget_borrowed(v___y_341_, v_hi_318_);
v___x_343_ = lean_array_fget_borrowed(v___y_341_, v_lo_317_);
v___x_344_ = l_Lean_Name_quickLt(v___x_342_, v___x_343_);
if (v___x_344_ == 0)
{
v___y_335_ = v___y_341_;
goto v___jp_334_;
}
else
{
lean_object* v___x_345_; 
v___x_345_ = lean_array_fswap(v___y_341_, v_lo_317_, v_hi_318_);
v___y_335_ = v___x_345_;
goto v___jp_334_;
}
}
}
v___jp_319_:
{
lean_object* v_pivot_321_; lean_object* v___x_322_; lean_object* v_fst_323_; lean_object* v_snd_324_; uint8_t v___x_325_; 
v_pivot_321_ = lean_array_fget(v___y_320_, v_hi_318_);
lean_inc_n(v_lo_317_, 2);
v___x_322_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2_spec__2___redArg(v_hi_318_, v_pivot_321_, v___y_320_, v_lo_317_, v_lo_317_);
lean_dec(v_pivot_321_);
v_fst_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_fst_323_);
v_snd_324_ = lean_ctor_get(v___x_322_, 1);
lean_inc(v_snd_324_);
lean_dec_ref(v___x_322_);
v___x_325_ = lean_nat_dec_le(v_hi_318_, v_fst_323_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_326_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg(v_n_315_, v_snd_324_, v_lo_317_, v_fst_323_);
v___x_327_ = lean_unsigned_to_nat(1u);
v___x_328_ = lean_nat_add(v_fst_323_, v___x_327_);
lean_dec(v_fst_323_);
v_as_316_ = v___x_326_;
v_lo_317_ = v___x_328_;
goto _start;
}
else
{
lean_dec(v_fst_323_);
lean_dec(v_lo_317_);
return v_snd_324_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_n_350_, lean_object* v_as_351_, lean_object* v_lo_352_, lean_object* v_hi_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg(v_n_350_, v_as_351_, v_lo_352_, v_hi_353_);
lean_dec(v_hi_353_);
lean_dec(v_n_350_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_(lean_object* v_es_355_){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_356_ = lean_array_mk(v_es_355_);
v___x_357_ = lean_array_get_size(v___x_356_);
v___x_358_ = lean_unsigned_to_nat(0u);
v___x_359_ = lean_nat_dec_eq(v___x_357_, v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___y_363_; uint8_t v___x_367_; 
v___x_360_ = lean_unsigned_to_nat(1u);
v___x_361_ = lean_nat_sub(v___x_357_, v___x_360_);
v___x_367_ = lean_nat_dec_le(v___x_358_, v___x_361_);
if (v___x_367_ == 0)
{
lean_inc(v___x_361_);
v___y_363_ = v___x_361_;
goto v___jp_362_;
}
else
{
v___y_363_ = v___x_358_;
goto v___jp_362_;
}
v___jp_362_:
{
uint8_t v___x_364_; 
v___x_364_ = lean_nat_dec_le(v___y_363_, v___x_361_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; 
lean_dec(v___x_361_);
lean_inc(v___y_363_);
v___x_365_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg(v___x_357_, v___x_356_, v___y_363_, v___y_363_);
lean_dec(v___y_363_);
return v___x_365_;
}
else
{
lean_object* v___x_366_; 
v___x_366_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg(v___x_357_, v___x_356_, v___y_363_, v___x_361_);
lean_dec(v___x_361_);
return v___x_366_;
}
}
}
else
{
return v___x_356_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__5_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_));
v___x_386_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2____boxed(lean_object* v_a_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_();
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2(lean_object* v_n_389_, lean_object* v_as_390_, lean_object* v_lo_391_, lean_object* v_hi_392_, lean_object* v_w_393_, lean_object* v_hlo_394_, lean_object* v_hhi_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg(v_n_389_, v_as_390_, v_lo_391_, v_hi_392_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_397_, lean_object* v_as_398_, lean_object* v_lo_399_, lean_object* v_hi_400_, lean_object* v_w_401_, lean_object* v_hlo_402_, lean_object* v_hhi_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2(v_n_397_, v_as_398_, v_lo_399_, v_hi_400_, v_w_401_, v_hlo_402_, v_hhi_403_);
lean_dec(v_hi_400_);
lean_dec(v_n_397_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2_spec__2(lean_object* v_n_405_, lean_object* v_lo_406_, lean_object* v_hi_407_, lean_object* v_hhi_408_, lean_object* v_pivot_409_, lean_object* v_as_410_, lean_object* v_i_411_, lean_object* v_k_412_, lean_object* v_ilo_413_, lean_object* v_ik_414_, lean_object* v_w_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2_spec__2___redArg(v_hi_407_, v_pivot_409_, v_as_410_, v_i_411_, v_k_412_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2_spec__2___boxed(lean_object* v_n_417_, lean_object* v_lo_418_, lean_object* v_hi_419_, lean_object* v_hhi_420_, lean_object* v_pivot_421_, lean_object* v_as_422_, lean_object* v_i_423_, lean_object* v_k_424_, lean_object* v_ilo_425_, lean_object* v_ik_426_, lean_object* v_w_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2_spec__2(v_n_417_, v_lo_418_, v_hi_419_, v_hhi_420_, v_pivot_421_, v_as_422_, v_i_423_, v_k_424_, v_ilo_425_, v_ik_426_, v_w_427_);
lean_dec(v_pivot_421_);
lean_dec(v_hi_419_);
lean_dec(v_lo_418_);
lean_dec(v_n_417_);
return v_res_428_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_429_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__0);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
return v___x_431_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg(lean_object* v_env_434_, lean_object* v___y_435_){
_start:
{
lean_object* v___x_437_; lean_object* v_nextMacroScope_438_; lean_object* v_ngen_439_; lean_object* v_auxDeclNGen_440_; lean_object* v_traceState_441_; lean_object* v_recordedDeps_442_; lean_object* v_messages_443_; lean_object* v_infoState_444_; lean_object* v_snapshotTasks_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_456_; 
v___x_437_ = lean_st_ref_take(v___y_435_);
v_nextMacroScope_438_ = lean_ctor_get(v___x_437_, 1);
v_ngen_439_ = lean_ctor_get(v___x_437_, 2);
v_auxDeclNGen_440_ = lean_ctor_get(v___x_437_, 3);
v_traceState_441_ = lean_ctor_get(v___x_437_, 4);
v_recordedDeps_442_ = lean_ctor_get(v___x_437_, 6);
v_messages_443_ = lean_ctor_get(v___x_437_, 7);
v_infoState_444_ = lean_ctor_get(v___x_437_, 8);
v_snapshotTasks_445_ = lean_ctor_get(v___x_437_, 9);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_456_ == 0)
{
lean_object* v_unused_457_; lean_object* v_unused_458_; 
v_unused_457_ = lean_ctor_get(v___x_437_, 5);
lean_dec(v_unused_457_);
v_unused_458_ = lean_ctor_get(v___x_437_, 0);
lean_dec(v_unused_458_);
v___x_447_ = v___x_437_;
v_isShared_448_ = v_isSharedCheck_456_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_snapshotTasks_445_);
lean_inc(v_infoState_444_);
lean_inc(v_messages_443_);
lean_inc(v_recordedDeps_442_);
lean_inc(v_traceState_441_);
lean_inc(v_auxDeclNGen_440_);
lean_inc(v_ngen_439_);
lean_inc(v_nextMacroScope_438_);
lean_dec(v___x_437_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_456_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_449_ = lean_box(0);
v___x_450_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__2);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 5, v___x_450_);
lean_ctor_set(v___x_447_, 0, v_env_434_);
v___x_452_ = v___x_447_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_env_434_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_nextMacroScope_438_);
lean_ctor_set(v_reuseFailAlloc_455_, 2, v_ngen_439_);
lean_ctor_set(v_reuseFailAlloc_455_, 3, v_auxDeclNGen_440_);
lean_ctor_set(v_reuseFailAlloc_455_, 4, v_traceState_441_);
lean_ctor_set(v_reuseFailAlloc_455_, 5, v___x_450_);
lean_ctor_set(v_reuseFailAlloc_455_, 6, v_recordedDeps_442_);
lean_ctor_set(v_reuseFailAlloc_455_, 7, v_messages_443_);
lean_ctor_set(v_reuseFailAlloc_455_, 8, v_infoState_444_);
lean_ctor_set(v_reuseFailAlloc_455_, 9, v_snapshotTasks_445_);
v___x_452_ = v_reuseFailAlloc_455_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_st_ref_put(v___y_435_, v___x_452_);
v___x_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_449_);
return v___x_454_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_env_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg(v_env_459_, v___y_460_);
lean_dec(v___y_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1(lean_object* v_env_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg(v_env_463_, v___y_465_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1(v_env_468_, v___y_469_, v___y_470_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
return v_res_472_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__0);
v___x_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_475_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
lean_ctor_set(v___x_477_, 2, v___x_476_);
lean_ctor_set(v___x_477_, 3, v___x_476_);
lean_ctor_set(v___x_477_, 4, v___x_475_);
lean_ctor_set(v___x_477_, 5, v___x_475_);
lean_ctor_set(v___x_477_, 6, v___x_475_);
lean_ctor_set(v___x_477_, 7, v___x_475_);
lean_ctor_set(v___x_477_, 8, v___x_475_);
lean_ctor_set(v___x_477_, 9, v___x_475_);
lean_ctor_set(v___x_477_, 10, v___x_475_);
return v___x_477_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = lean_unsigned_to_nat(32u);
v___x_479_ = lean_mk_empty_array_with_capacity(v___x_478_);
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_481_ = ((size_t)5ULL);
v___x_482_ = lean_unsigned_to_nat(0u);
v___x_483_ = lean_unsigned_to_nat(32u);
v___x_484_ = lean_mk_empty_array_with_capacity(v___x_483_);
v___x_485_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_486_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v___x_484_);
lean_ctor_set(v___x_486_, 2, v___x_482_);
lean_ctor_set(v___x_486_, 3, v___x_482_);
lean_ctor_set_usize(v___x_486_, 4, v___x_481_);
return v___x_486_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_487_ = lean_box(1);
v___x_488_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_489_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_490_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v___x_488_);
lean_ctor_set(v___x_490_, 2, v___x_487_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v___x_495_; lean_object* v_toCold_496_; lean_object* v_env_497_; lean_object* v_options_498_; uint8_t v___x_499_; lean_object* v_env_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_495_ = lean_st_ref_get(v___y_493_);
v_toCold_496_ = lean_ctor_get(v___y_492_, 0);
v_env_497_ = lean_ctor_get(v___x_495_, 0);
lean_inc_ref(v_env_497_);
lean_dec(v___x_495_);
v_options_498_ = lean_ctor_get(v_toCold_496_, 2);
v___x_499_ = 0;
v_env_500_ = l_Lean_Environment_setRecordingDeps(v_env_497_, v___x_499_);
v___x_501_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_502_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__4);
lean_inc_ref(v_options_498_);
v___x_503_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_503_, 0, v_env_500_);
lean_ctor_set(v___x_503_, 1, v___x_501_);
lean_ctor_set(v___x_503_, 2, v___x_502_);
lean_ctor_set(v___x_503_, 3, v_options_498_);
v___x_504_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
lean_ctor_set(v___x_504_, 1, v_msgData_491_);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0(v_msgData_506_, v___y_507_, v___y_508_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_ref_515_; lean_object* v___x_516_; lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_525_; 
v_ref_515_ = lean_ctor_get(v___y_512_, 2);
v___x_516_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0(v_msg_511_, v___y_512_, v___y_513_);
v_a_517_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_525_ == 0)
{
v___x_519_ = v___x_516_;
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_516_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_521_; lean_object* v___x_523_; 
lean_inc(v_ref_515_);
v___x_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_521_, 0, v_ref_515_);
lean_ctor_set(v___x_521_, 1, v_a_517_);
if (v_isShared_520_ == 0)
{
lean_ctor_set_tag(v___x_519_, 1);
lean_ctor_set(v___x_519_, 0, v___x_521_);
v___x_523_ = v___x_519_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___redArg(v_msg_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
return v_res_530_;
}
}
static lean_object* _init_l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_));
v___x_533_ = l_Lean_stringToMessageData(v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_));
v___x_536_ = l_Lean_stringToMessageData(v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(lean_object* v_name_537_, lean_object* v_decl_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_542_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_, &l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__once, _init_l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_);
v___x_543_ = l_Lean_MessageData_ofName(v_name_537_);
v___x_544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_542_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
v___x_545_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_, &l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__once, _init_l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_);
v___x_546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_544_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
v___x_547_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___redArg(v___x_546_, v___y_539_, v___y_540_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2____boxed(lean_object* v_name_548_, lean_object* v_decl_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(v_name_548_, v_decl_549_, v___y_550_, v___y_551_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v_decl_549_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(lean_object* v_addEntryFn_554_, lean_object* v_decl_555_, lean_object* v_s_556_){
_start:
{
lean_object* v_importedEntries_557_; lean_object* v_state_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_566_; 
v_importedEntries_557_ = lean_ctor_get(v_s_556_, 0);
v_state_558_ = lean_ctor_get(v_s_556_, 1);
v_isSharedCheck_566_ = !lean_is_exclusive(v_s_556_);
if (v_isSharedCheck_566_ == 0)
{
v___x_560_ = v_s_556_;
v_isShared_561_ = v_isSharedCheck_566_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_state_558_);
lean_inc(v_importedEntries_557_);
lean_dec(v_s_556_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_566_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v_state_562_; lean_object* v___x_564_; 
v_state_562_ = lean_apply_2(v_addEntryFn_554_, v_state_558_, v_decl_555_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 1, v_state_562_);
v___x_564_ = v___x_560_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_importedEntries_557_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_state_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__0));
v___x_569_ = l_Lean_stringToMessageData(v___x_568_);
return v___x_569_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__2));
v___x_572_ = l_Lean_stringToMessageData(v___x_571_);
return v___x_572_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__4));
v___x_575_ = l_Lean_stringToMessageData(v___x_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg(lean_object* v_name_579_, uint8_t v_kind_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___y_590_; 
v___x_584_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__1);
v___x_585_ = l_Lean_MessageData_ofName(v_name_579_);
v___x_586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_584_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__3);
v___x_588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_586_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
switch(v_kind_580_)
{
case 0:
{
lean_object* v___x_597_; 
v___x_597_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__6));
v___y_590_ = v___x_597_;
goto v___jp_589_;
}
case 1:
{
lean_object* v___x_598_; 
v___x_598_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__7));
v___y_590_ = v___x_598_;
goto v___jp_589_;
}
default: 
{
lean_object* v___x_599_; 
v___x_599_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__8));
v___y_590_ = v___x_599_;
goto v___jp_589_;
}
}
v___jp_589_:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
lean_inc_ref(v___y_590_);
v___x_591_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_591_, 0, v___y_590_);
v___x_592_ = l_Lean_MessageData_ofFormat(v___x_591_);
v___x_593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_588_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__5);
v___x_595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_593_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v___x_596_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___redArg(v___x_595_, v___y_581_, v___y_582_);
return v___x_596_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object* v_name_600_, lean_object* v_kind_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
uint8_t v_kind_boxed_605_; lean_object* v_res_606_; 
v_kind_boxed_605_ = lean_unbox(v_kind_601_);
v_res_606_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg(v_name_600_, v_kind_boxed_605_, v___y_602_, v___y_603_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
return v_res_606_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__0));
v___x_609_ = l_Lean_stringToMessageData(v___x_608_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__2));
v___x_612_ = l_Lean_stringToMessageData(v___x_611_);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__4));
v___x_615_ = l_Lean_stringToMessageData(v___x_614_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__6));
v___x_618_ = l_Lean_stringToMessageData(v___x_617_);
return v___x_618_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__9(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__8));
v___x_621_ = l_Lean_stringToMessageData(v___x_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg(lean_object* v_attrName_622_, lean_object* v_declName_623_, lean_object* v_givenType_624_, lean_object* v_expectedType_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_629_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__1);
v___x_630_ = l_Lean_MessageData_ofName(v_attrName_622_);
lean_inc_ref(v___x_630_);
v___x_631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_629_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
v___x_632_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__3);
v___x_633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_631_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___x_634_ = 0;
v___x_635_ = l_Lean_MessageData_ofConstName(v_declName_623_, v___x_634_);
v___x_636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_633_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
v___x_637_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__5);
v___x_638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_636_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = l_Lean_indentExpr(v_givenType_624_);
v___x_640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_638_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__7);
v___x_642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_640_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v___x_630_);
v___x_644_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__9, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__9_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__9);
v___x_645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_643_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
v___x_646_ = l_Lean_indentExpr(v_expectedType_625_);
v___x_647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_645_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___redArg(v___x_647_, v___y_626_, v___y_627_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___boxed(lean_object* v_attrName_649_, lean_object* v_declName_650_, lean_object* v_givenType_651_, lean_object* v_expectedType_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg(v_attrName_649_, v_declName_650_, v_givenType_651_, v_expectedType_652_, v___y_653_, v___y_654_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(lean_object* v_ref_657_, lean_object* v_msg_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v_toCold_662_; lean_object* v_currRecDepth_663_; lean_object* v_ref_664_; uint16_t v_optionFlags_665_; uint8_t v_suppressElabErrors_666_; uint8_t v_checkDeprecated_667_; uint8_t v_isRecordingDeps_668_; lean_object* v_ref_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v_toCold_662_ = lean_ctor_get(v___y_659_, 0);
v_currRecDepth_663_ = lean_ctor_get(v___y_659_, 1);
v_ref_664_ = lean_ctor_get(v___y_659_, 2);
v_optionFlags_665_ = lean_ctor_get_uint16(v___y_659_, sizeof(void*)*3);
v_suppressElabErrors_666_ = lean_ctor_get_uint8(v___y_659_, sizeof(void*)*3 + 2);
v_checkDeprecated_667_ = lean_ctor_get_uint8(v___y_659_, sizeof(void*)*3 + 3);
v_isRecordingDeps_668_ = lean_ctor_get_uint8(v___y_659_, sizeof(void*)*3 + 4);
v_ref_669_ = l_Lean_replaceRef(v_ref_657_, v_ref_664_);
lean_inc(v_currRecDepth_663_);
lean_inc_ref(v_toCold_662_);
v___x_670_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_670_, 0, v_toCold_662_);
lean_ctor_set(v___x_670_, 1, v_currRecDepth_663_);
lean_ctor_set(v___x_670_, 2, v_ref_669_);
lean_ctor_set_uint16(v___x_670_, sizeof(void*)*3, v_optionFlags_665_);
lean_ctor_set_uint8(v___x_670_, sizeof(void*)*3 + 2, v_suppressElabErrors_666_);
lean_ctor_set_uint8(v___x_670_, sizeof(void*)*3 + 3, v_checkDeprecated_667_);
lean_ctor_set_uint8(v___x_670_, sizeof(void*)*3 + 4, v_isRecordingDeps_668_);
v___x_671_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___redArg(v_msg_658_, v___x_670_, v___y_660_);
lean_dec_ref_known(v___x_670_, 3);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg___boxed(lean_object* v_ref_672_, lean_object* v_msg_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_672_, v_msg_673_, v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v_ref_672_);
return v_res_677_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0));
v___x_680_ = l_Lean_stringToMessageData(v___x_679_);
return v___x_680_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2));
v___x_683_ = l_Lean_stringToMessageData(v___x_682_);
return v___x_683_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4));
v___x_686_ = l_Lean_stringToMessageData(v___x_685_);
return v___x_686_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_689_ = l_Lean_stringToMessageData(v___x_688_);
return v___x_689_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_692_ = l_Lean_stringToMessageData(v___x_691_);
return v___x_692_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_695_ = l_Lean_stringToMessageData(v___x_694_);
return v___x_695_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_698_ = l_Lean_stringToMessageData(v___x_697_);
return v___x_698_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_701_ = l_Lean_stringToMessageData(v___x_700_);
return v___x_701_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_704_ = l_Lean_stringToMessageData(v___x_703_);
return v___x_704_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__18));
v___x_707_ = l_Lean_stringToMessageData(v___x_706_);
return v___x_707_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__21(void){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_709_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__20));
v___x_710_ = l_Lean_stringToMessageData(v___x_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_711_, lean_object* v_declHint_712_, lean_object* v___y_713_){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v_env_717_; uint8_t v___x_718_; 
v___x_715_ = lean_box(0);
v___x_716_ = lean_st_ref_get(v___y_713_);
v_env_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc_ref(v_env_717_);
lean_dec(v___x_716_);
v___x_718_ = l_Lean_Name_isAnonymous(v_declHint_712_);
if (v___x_718_ == 0)
{
uint8_t v_isExporting_719_; 
v_isExporting_719_ = lean_ctor_get_uint8(v_env_717_, sizeof(void*)*13);
if (v_isExporting_719_ == 0)
{
lean_object* v___x_720_; 
lean_dec_ref(v_env_717_);
lean_dec(v_declHint_712_);
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v_msg_711_);
return v___x_720_;
}
else
{
lean_object* v___x_721_; uint8_t v___x_722_; 
lean_inc_ref(v_env_717_);
v___x_721_ = l_Lean_Environment_setExporting(v_env_717_, v___x_718_);
lean_inc(v_declHint_712_);
lean_inc_ref(v___x_721_);
v___x_722_ = l_Lean_Environment_contains(v___x_721_, v_declHint_712_, v_isExporting_719_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; 
lean_dec_ref(v___x_721_);
lean_dec_ref(v_env_717_);
lean_dec(v_declHint_712_);
v___x_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_723_, 0, v_msg_711_);
return v___x_723_;
}
else
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v_c_729_; lean_object* v___x_730_; 
v___x_724_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_725_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_726_ = l_Lean_Options_empty;
lean_inc_ref(v___x_721_);
v___x_727_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_727_, 0, v___x_721_);
lean_ctor_set(v___x_727_, 1, v___x_724_);
lean_ctor_set(v___x_727_, 2, v___x_725_);
lean_ctor_set(v___x_727_, 3, v___x_726_);
lean_inc(v_declHint_712_);
v___x_728_ = l_Lean_MessageData_ofConstName(v_declHint_712_, v___x_718_);
v_c_729_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_729_, 0, v___x_727_);
lean_ctor_set(v_c_729_, 1, v___x_728_);
v___x_730_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_721_, v_declHint_712_);
lean_dec_ref(v___x_721_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
lean_dec_ref(v_env_717_);
lean_dec(v_declHint_712_);
v___x_731_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
lean_ctor_set(v___x_732_, 1, v_c_729_);
v___x_733_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_732_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = l_Lean_MessageData_note(v___x_734_);
v___x_736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_736_, 0, v_msg_711_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
return v___x_737_;
}
else
{
lean_object* v_val_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_791_; 
v_val_738_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_791_ == 0)
{
v___x_740_ = v___x_730_;
v_isShared_741_ = v_isSharedCheck_791_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_val_738_);
lean_dec(v___x_730_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_791_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v_modules_743_; lean_object* v_moduleNames_744_; lean_object* v_mod_745_; uint8_t v___x_760_; 
v___x_742_ = l_Lean_Environment_header(v_env_717_);
lean_dec_ref(v_env_717_);
v_modules_743_ = lean_ctor_get(v___x_742_, 3);
lean_inc_ref(v_modules_743_);
v_moduleNames_744_ = lean_ctor_get(v___x_742_, 4);
lean_inc_ref(v_moduleNames_744_);
lean_dec_ref(v___x_742_);
v_mod_745_ = lean_array_get(v___x_715_, v_moduleNames_744_, v_val_738_);
lean_dec_ref(v_moduleNames_744_);
v___x_760_ = l_Lean_isPrivateName(v_declHint_712_);
lean_dec(v_declHint_712_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_761_ = lean_array_get_size(v_modules_743_);
v___x_762_ = lean_nat_dec_lt(v_val_738_, v___x_761_);
if (v___x_762_ == 0)
{
lean_dec_ref(v_modules_743_);
lean_dec(v_val_738_);
goto v___jp_746_;
}
else
{
lean_object* v___x_763_; lean_object* v_toImport_764_; uint8_t v_isExported_765_; 
v___x_763_ = lean_array_fget(v_modules_743_, v_val_738_);
lean_dec(v_val_738_);
lean_dec_ref(v_modules_743_);
v_toImport_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc_ref(v_toImport_764_);
lean_dec(v___x_763_);
v_isExported_765_ = lean_ctor_get_uint8(v_toImport_764_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_764_);
if (v_isExported_765_ == 0)
{
goto v___jp_746_;
}
else
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
lean_del_object(v___x_740_);
v___x_766_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set(v___x_767_, 1, v_c_729_);
v___x_768_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_767_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = l_Lean_MessageData_ofName(v_mod_745_);
lean_inc_ref(v___x_770_);
v___x_771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_769_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_771_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v___x_774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
lean_ctor_set(v___x_774_, 1, v___x_770_);
v___x_775_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_774_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = l_Lean_MessageData_note(v___x_776_);
v___x_778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_778_, 0, v_msg_711_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
return v___x_779_;
}
}
}
else
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
lean_dec_ref(v_modules_743_);
lean_del_object(v___x_740_);
lean_dec(v_val_738_);
v___x_780_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set(v___x_781_, 1, v_c_729_);
v___x_782_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19);
v___x_783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_781_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = l_Lean_MessageData_ofName(v_mod_745_);
v___x_785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_783_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__21);
v___x_787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = l_Lean_MessageData_note(v___x_787_);
v___x_789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_789_, 0, v_msg_711_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
return v___x_790_;
}
v___jp_746_:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_758_; 
v___x_747_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
lean_ctor_set(v___x_748_, 1, v_c_729_);
v___x_749_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_748_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = l_Lean_MessageData_ofName(v_mod_745_);
v___x_752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_750_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_752_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___x_755_ = l_Lean_MessageData_note(v___x_754_);
v___x_756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_756_, 0, v_msg_711_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
if (v_isShared_741_ == 0)
{
lean_ctor_set_tag(v___x_740_, 0);
lean_ctor_set(v___x_740_, 0, v___x_756_);
v___x_758_ = v___x_740_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_792_; 
lean_dec_ref(v_env_717_);
lean_dec(v_declHint_712_);
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v_msg_711_);
return v___x_792_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_793_, lean_object* v_declHint_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_793_, v_declHint_794_, v___y_795_);
lean_dec(v___y_795_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(lean_object* v_msg_798_, lean_object* v_declHint_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v___x_803_; lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_813_; 
v___x_803_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_798_, v_declHint_799_, v___y_801_);
v_a_804_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_813_ == 0)
{
v___x_806_ = v___x_803_;
v_isShared_807_ = v_isSharedCheck_813_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_803_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_813_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_808_ = l_Lean_unknownIdentifierMessageTag;
v___x_809_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
lean_ctor_set(v___x_809_, 1, v_a_804_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v___x_809_);
v___x_811_ = v___x_806_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8___boxed(lean_object* v_msg_814_, lean_object* v_declHint_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(v_msg_814_, v_declHint_815_, v___y_816_, v___y_817_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(lean_object* v_ref_820_, lean_object* v_msg_821_, lean_object* v_declHint_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v___x_826_; lean_object* v_a_827_; lean_object* v___x_828_; 
v___x_826_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(v_msg_821_, v_declHint_822_, v___y_823_, v___y_824_);
v_a_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_a_827_);
lean_dec_ref(v___x_826_);
v___x_828_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_820_, v_a_827_, v___y_823_, v___y_824_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_ref_829_, lean_object* v_msg_830_, lean_object* v_declHint_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(v_ref_829_, v_msg_830_, v_declHint_831_, v___y_832_, v___y_833_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v_ref_829_);
return v_res_835_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__0));
v___x_838_ = l_Lean_stringToMessageData(v___x_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(lean_object* v_ref_839_, lean_object* v_constName_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v___x_844_; uint8_t v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_844_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1);
v___x_845_ = 0;
lean_inc(v_constName_840_);
v___x_846_ = l_Lean_MessageData_ofConstName(v_constName_840_, v___x_845_);
v___x_847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_844_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v___x_848_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__5);
v___x_849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_847_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
v___x_850_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(v_ref_839_, v___x_849_, v_constName_840_, v___y_841_, v___y_842_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_ref_851_, lean_object* v_constName_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(v_ref_851_, v_constName_852_, v___y_853_, v___y_854_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v_ref_851_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_constName_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v_ref_861_; lean_object* v___x_862_; 
v_ref_861_ = lean_ctor_get(v___y_858_, 2);
v___x_862_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(v_ref_861_, v_constName_857_, v___y_858_, v___y_859_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_constName_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2(lean_object* v_constName_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v___x_872_; lean_object* v_env_873_; uint8_t v___x_874_; lean_object* v___x_875_; 
v___x_872_ = lean_st_ref_get(v___y_870_);
v_env_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc_ref(v_env_873_);
lean_dec(v___x_872_);
v___x_874_ = 0;
lean_inc(v_constName_868_);
v___x_875_ = l_Lean_Environment_find_x3f(v_env_873_, v_constName_868_, v___x_874_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_868_, v___y_869_, v___y_870_);
return v___x_876_;
}
else
{
lean_object* v_val_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
lean_dec(v_constName_868_);
v_val_877_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_875_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_val_877_);
lean_dec(v___x_875_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
lean_ctor_set_tag(v___x_879_, 0);
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_val_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2___boxed(lean_object* v_constName_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2(v_constName_885_, v___y_886_, v___y_887_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(uint8_t v_builtin_895_, lean_object* v___x_896_, lean_object* v___x_897_, lean_object* v___x_898_, lean_object* v_name_899_, lean_object* v_decl_900_, lean_object* v_stx_901_, uint8_t v_kind_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_932_; lean_object* v___y_933_; 
if (v_builtin_895_ == 0)
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_));
lean_inc(v_decl_900_);
v___x_957_ = l_Lean_ensureAttrDeclIsMeta(v___x_956_, v_decl_900_, v_kind_902_, v___y_903_, v___y_904_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_dec_ref_known(v___x_957_, 1);
goto v___jp_951_;
}
else
{
lean_dec(v_stx_901_);
lean_dec(v_decl_900_);
lean_dec(v_name_899_);
lean_dec_ref(v___x_898_);
lean_dec_ref(v___x_897_);
lean_dec(v___x_896_);
return v___x_957_;
}
}
else
{
goto v___jp_951_;
}
v___jp_906_:
{
lean_object* v___x_909_; 
v___x_909_ = lean_st_ref_get(v___y_908_);
if (v_builtin_895_ == 0)
{
lean_object* v_env_910_; lean_object* v___x_911_; lean_object* v_toEnvExtension_912_; lean_object* v_addEntryFn_913_; lean_object* v_asyncMode_914_; uint8_t v_logWrites_915_; lean_object* v___f_916_; uint8_t v___x_917_; 
lean_dec_ref(v___x_898_);
lean_dec_ref(v___x_897_);
v_env_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc_ref(v_env_910_);
lean_dec(v___x_909_);
v___x_911_ = l_Lean_Server_codeActionProviderExt;
v_toEnvExtension_912_ = lean_ctor_get(v___x_911_, 0);
v_addEntryFn_913_ = lean_ctor_get(v___x_911_, 3);
v_asyncMode_914_ = lean_ctor_get(v_toEnvExtension_912_, 2);
v_logWrites_915_ = lean_ctor_get_uint8(v_toEnvExtension_912_, sizeof(void*)*6);
lean_inc(v_addEntryFn_913_);
v___f_916_ = lean_alloc_closure((void*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_916_, 0, v_addEntryFn_913_);
lean_closure_set(v___f_916_, 1, v_decl_900_);
v___x_917_ = 1;
if (v_logWrites_915_ == 0)
{
lean_object* v___x_918_; lean_object* v___x_919_; 
lean_inc_ref(v_toEnvExtension_912_);
v___x_918_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_912_, v_env_910_, v___f_916_, v_asyncMode_914_, v___x_896_, v___x_917_);
v___x_919_ = l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg(v___x_918_, v___y_908_);
return v___x_919_;
}
else
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
lean_inc_ref_n(v_toEnvExtension_912_, 2);
v___x_920_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_912_, v_env_910_);
lean_dec_ref(v_env_910_);
v___x_921_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_912_, v___x_920_, v___f_916_, v_asyncMode_914_, v___x_896_, v___x_917_);
v___x_922_ = l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg(v___x_921_, v___y_908_);
return v___x_922_;
}
}
else
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
lean_dec(v___x_909_);
lean_dec(v___x_896_);
v___x_923_ = lean_box(0);
lean_inc_n(v_decl_900_, 2);
v___x_924_ = l_Lean_mkConst(v_decl_900_, v___x_923_);
v___x_925_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_));
v___x_926_ = l_Lean_Name_mkStr3(v___x_897_, v___x_898_, v___x_925_);
v___x_927_ = l_Lean_mkConst(v___x_926_, v___x_923_);
v___x_928_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_decl_900_);
v___x_929_ = l_Lean_mkAppB(v___x_927_, v___x_928_, v___x_924_);
v___x_930_ = l_Lean_declareBuiltin(v_decl_900_, v___x_929_, v___y_907_, v___y_908_);
return v___x_930_;
}
}
v___jp_931_:
{
lean_object* v___x_934_; 
lean_inc(v_decl_900_);
v___x_934_ = l_Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2(v_decl_900_, v___y_932_, v___y_933_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_a_935_);
lean_dec_ref_known(v___x_934_, 1);
v___x_936_ = l_Lean_ConstantInfo_type(v_a_935_);
lean_dec(v_a_935_);
v___x_937_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_));
lean_inc_ref(v___x_898_);
lean_inc_ref(v___x_897_);
v___x_938_ = l_Lean_Name_mkStr3(v___x_897_, v___x_898_, v___x_937_);
v___x_939_ = l_Lean_Expr_isConstOf(v___x_936_, v___x_938_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
lean_dec_ref(v___x_898_);
lean_dec_ref(v___x_897_);
lean_dec(v___x_896_);
v___x_940_ = lean_box(0);
v___x_941_ = l_Lean_mkConst(v___x_938_, v___x_940_);
v___x_942_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg(v_name_899_, v_decl_900_, v___x_936_, v___x_941_, v___y_932_, v___y_933_);
return v___x_942_;
}
else
{
lean_dec(v___x_938_);
lean_dec_ref(v___x_936_);
lean_dec(v_name_899_);
v___y_907_ = v___y_932_;
v___y_908_ = v___y_933_;
goto v___jp_906_;
}
}
else
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
lean_dec(v_decl_900_);
lean_dec(v_name_899_);
lean_dec_ref(v___x_898_);
lean_dec_ref(v___x_897_);
lean_dec(v___x_896_);
v_a_943_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_934_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_934_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_943_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
v___jp_951_:
{
lean_object* v___x_952_; 
v___x_952_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_901_, v___y_903_, v___y_904_);
if (lean_obj_tag(v___x_952_) == 0)
{
uint8_t v___x_953_; uint8_t v___x_954_; 
lean_dec_ref_known(v___x_952_, 1);
v___x_953_ = 0;
v___x_954_ = l_Lean_instBEqAttributeKind_beq(v_kind_902_, v___x_953_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; 
lean_dec(v_decl_900_);
lean_dec_ref(v___x_898_);
lean_dec_ref(v___x_897_);
lean_dec(v___x_896_);
v___x_955_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg(v_name_899_, v_kind_902_, v___y_903_, v___y_904_);
return v___x_955_;
}
else
{
v___y_932_ = v___y_903_;
v___y_933_ = v___y_904_;
goto v___jp_931_;
}
}
else
{
lean_dec(v_decl_900_);
lean_dec(v_name_899_);
lean_dec_ref(v___x_898_);
lean_dec_ref(v___x_897_);
lean_dec(v___x_896_);
return v___x_952_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2____boxed(lean_object* v_builtin_958_, lean_object* v___x_959_, lean_object* v___x_960_, lean_object* v___x_961_, lean_object* v_name_962_, lean_object* v_decl_963_, lean_object* v_stx_964_, lean_object* v_kind_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
uint8_t v_builtin_boxed_969_; uint8_t v_kind_boxed_970_; lean_object* v_res_971_; 
v_builtin_boxed_969_ = lean_unbox(v_builtin_958_);
v_kind_boxed_970_ = lean_unbox(v_kind_965_);
v_res_971_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(v_builtin_boxed_969_, v___x_959_, v___x_960_, v___x_961_, v_name_962_, v_decl_963_, v_stx_964_, v_kind_boxed_970_, v___y_966_, v___y_967_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(uint8_t v_builtin_1035_, lean_object* v_name_1036_){
_start:
{
lean_object* v___f_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___f_1043_; lean_object* v___x_1044_; lean_object* v___y_1046_; 
lean_inc_n(v_name_1036_, 2);
v___f_1038_ = lean_alloc_closure((void*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_1038_, 0, v_name_1036_);
v___x_1039_ = lean_box(0);
v___x_1040_ = ((lean_object*)(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__0));
v___x_1041_ = ((lean_object*)(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__1));
v___x_1042_ = lean_box(v_builtin_1035_);
v___f_1043_ = lean_alloc_closure((void*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2____boxed), 11, 5);
lean_closure_set(v___f_1043_, 0, v___x_1042_);
lean_closure_set(v___f_1043_, 1, v___x_1039_);
lean_closure_set(v___f_1043_, 2, v___x_1040_);
lean_closure_set(v___f_1043_, 3, v___x_1041_);
lean_closure_set(v___f_1043_, 4, v_name_1036_);
v___x_1044_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__24_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_));
if (v_builtin_1035_ == 0)
{
lean_object* v___x_1053_; 
v___x_1053_ = ((lean_object*)(l_panic___at___00Lean_Server_CodeAction_getFileSource_x21_spec__0___closed__0));
v___y_1046_ = v___x_1053_;
goto v___jp_1045_;
}
else
{
lean_object* v___x_1054_; 
v___x_1054_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__26_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_));
v___y_1046_ = v___x_1054_;
goto v___jp_1045_;
}
v___jp_1045_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1047_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3___closed__25_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_));
lean_inc_ref(v___y_1046_);
v___x_1048_ = lean_string_append(v___y_1046_, v___x_1047_);
v___x_1049_ = 1;
v___x_1050_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1050_, 0, v___x_1044_);
lean_ctor_set(v___x_1050_, 1, v_name_1036_);
lean_ctor_set(v___x_1050_, 2, v___x_1048_);
lean_ctor_set_uint8(v___x_1050_, sizeof(void*)*3, v___x_1049_);
v___x_1051_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
lean_ctor_set(v___x_1051_, 1, v___f_1043_);
lean_ctor_set(v___x_1051_, 2, v___f_1038_);
v___x_1052_ = l_Lean_registerBuiltinAttribute(v___x_1051_);
return v___x_1052_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2____boxed(lean_object* v_builtin_1055_, lean_object* v_name_1056_, lean_object* v___y_1057_){
_start:
{
uint8_t v_builtin_boxed_1058_; lean_object* v_res_1059_; 
v_builtin_boxed_1058_ = lean_unbox(v_builtin_1055_);
v_res_1059_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(v_builtin_boxed_1058_, v_name_1056_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(){
_start:
{
uint8_t v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1067_ = 1;
v___x_1068_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_));
v___x_1069_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(v___x_1067_, v___x_1068_);
if (lean_obj_tag(v___x_1069_) == 0)
{
uint8_t v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
lean_dec_ref_known(v___x_1069_, 1);
v___x_1070_ = 0;
v___x_1071_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_));
v___x_1072_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(v___x_1070_, v___x_1071_);
return v___x_1072_;
}
else
{
return v___x_1069_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2____boxed(lean_object* v_a_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_();
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1075_, lean_object* v_msg_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___redArg(v_msg_1076_, v___y_1077_, v___y_1078_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1081_, lean_object* v_msg_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0(v_00_u03b1_1081_, v_msg_1082_, v___y_1083_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b1_1087_, lean_object* v_attrName_1088_, lean_object* v_declName_1089_, lean_object* v_givenType_1090_, lean_object* v_expectedType_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg(v_attrName_1088_, v_declName_1089_, v_givenType_1090_, v_expectedType_1091_, v___y_1092_, v___y_1093_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___boxed(lean_object* v_00_u03b1_1096_, lean_object* v_attrName_1097_, lean_object* v_declName_1098_, lean_object* v_givenType_1099_, lean_object* v_expectedType_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3(v_00_u03b1_1096_, v_attrName_1097_, v_declName_1098_, v_givenType_1099_, v_expectedType_1100_, v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b1_1105_, lean_object* v_name_1106_, uint8_t v_kind_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg(v_name_1106_, v_kind_1107_, v___y_1108_, v___y_1109_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___boxed(lean_object* v_00_u03b1_1112_, lean_object* v_name_1113_, lean_object* v_kind_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
uint8_t v_kind_boxed_1118_; lean_object* v_res_1119_; 
v_kind_boxed_1118_ = lean_unbox(v_kind_1114_);
v_res_1119_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4(v_00_u03b1_1112_, v_name_1113_, v_kind_boxed_1118_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_00_u03b1_1120_, lean_object* v_constName_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_1121_, v___y_1122_, v___y_1123_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_00_u03b1_1126_, lean_object* v_constName_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3(v_00_u03b1_1126_, v_constName_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4(lean_object* v_00_u03b1_1132_, lean_object* v_ref_1133_, lean_object* v_constName_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(v_ref_1133_, v_constName_1134_, v___y_1135_, v___y_1136_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1139_, lean_object* v_ref_1140_, lean_object* v_constName_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4(v_00_u03b1_1139_, v_ref_1140_, v_constName_1141_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v_ref_1140_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7(lean_object* v_00_u03b1_1146_, lean_object* v_ref_1147_, lean_object* v_msg_1148_, lean_object* v_declHint_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(v_ref_1147_, v_msg_1148_, v_declHint_1149_, v___y_1150_, v___y_1151_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b1_1154_, lean_object* v_ref_1155_, lean_object* v_msg_1156_, lean_object* v_declHint_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7(v_00_u03b1_1154_, v_ref_1155_, v_msg_1156_, v_declHint_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v_ref_1155_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(lean_object* v_msg_1162_, lean_object* v_declHint_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_1162_, v_declHint_1163_, v___y_1165_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_1168_, lean_object* v_declHint_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(v_msg_1168_, v_declHint_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9(lean_object* v_00_u03b1_1174_, lean_object* v_ref_1175_, lean_object* v_msg_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_1175_, v_msg_1176_, v___y_1177_, v___y_1178_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1181_, lean_object* v_ref_1182_, lean_object* v_msg_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9(v_00_u03b1_1181_, v_ref_1182_, v_msg_1183_, v___y_1184_, v___y_1185_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v_ref_1182_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg(lean_object* v_inst_1192_, lean_object* v_inst_1193_, lean_object* v_inst_1194_, lean_object* v_inst_1195_, lean_object* v_declName_1196_){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg___closed__0));
v___x_1198_ = l_Lean_evalConstCheck___redArg(v_inst_1195_, v_inst_1192_, v_inst_1194_, v_inst_1193_, v___x_1197_, v_declName_1196_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe(lean_object* v_M_1199_, lean_object* v_inst_1200_, lean_object* v_inst_1201_, lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_declName_1204_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg(v_inst_1200_, v_inst_1201_, v_inst_1202_, v_inst_1203_, v_declName_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleCodeAction_spec__6(lean_object* v___y_1206_){
_start:
{
lean_object* v_doc_1208_; lean_object* v___x_1209_; 
v_doc_1208_ = lean_ctor_get(v___y_1206_, 1);
lean_inc_ref(v_doc_1208_);
v___x_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1209_, 0, v_doc_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleCodeAction_spec__6___boxed(lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleCodeAction_spec__6(v___y_1210_);
lean_dec_ref(v___y_1210_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_handleCodeAction_spec__4(lean_object* v_init_1213_, lean_object* v_x_1214_){
_start:
{
if (lean_obj_tag(v_x_1214_) == 0)
{
lean_object* v_k_1215_; lean_object* v_v_1216_; lean_object* v_l_1217_; lean_object* v_r_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v_k_1215_ = lean_ctor_get(v_x_1214_, 1);
v_v_1216_ = lean_ctor_get(v_x_1214_, 2);
v_l_1217_ = lean_ctor_get(v_x_1214_, 3);
v_r_1218_ = lean_ctor_get(v_x_1214_, 4);
v___x_1219_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_handleCodeAction_spec__4(v_init_1213_, v_r_1218_);
lean_inc(v_v_1216_);
lean_inc(v_k_1215_);
v___x_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1220_, 0, v_k_1215_);
lean_ctor_set(v___x_1220_, 1, v_v_1216_);
v___x_1221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
lean_ctor_set(v___x_1221_, 1, v___x_1219_);
v_init_1213_ = v___x_1221_;
v_x_1214_ = v_l_1217_;
goto _start;
}
else
{
return v_init_1213_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_handleCodeAction_spec__4___boxed(lean_object* v_init_1223_, lean_object* v_x_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_handleCodeAction_spec__4(v_init_1223_, v_x_1224_);
lean_dec(v_x_1224_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg___lam__0(lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v___x_1229_; lean_object* v_env_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1229_ = lean_st_ref_get(v___y_1227_);
v_env_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc_ref(v_env_1230_);
lean_dec(v___x_1229_);
v___x_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1231_, 0, v_env_1230_);
v___x_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg___lam__0(v___y_1233_, v___y_1234_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
return v_res_1236_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1237_ = lean_box(0);
v___x_1238_ = l_Lean_Elab_abortCommandExceptionId;
v___x_1239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1238_);
lean_ctor_set(v___x_1239_, 1, v___x_1237_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg(){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg___closed__0);
v___x_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v___y_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg();
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9___redArg(lean_object* v_msg_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_ref_1249_; lean_object* v___x_1250_; lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1259_; 
v_ref_1249_ = lean_ctor_get(v___y_1246_, 2);
v___x_1250_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0(v_msg_1245_, v___y_1246_, v___y_1247_);
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1253_ = v___x_1250_;
v_isShared_1254_ = v_isSharedCheck_1259_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1250_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1259_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1255_; lean_object* v___x_1257_; 
lean_inc(v_ref_1249_);
v___x_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1255_, 0, v_ref_1249_);
lean_ctor_set(v___x_1255_, 1, v_a_1251_);
if (v_isShared_1254_ == 0)
{
lean_ctor_set_tag(v___x_1253_, 1);
lean_ctor_set(v___x_1253_, 0, v___x_1255_);
v___x_1257_ = v___x_1253_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1255_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_msg_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9___redArg(v_msg_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5___redArg(lean_object* v_x_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
if (lean_obj_tag(v_x_1265_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v_a_1270_ = lean_ctor_get(v_x_1265_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v_x_1265_, 1);
v___x_1271_ = l_Lean_stringToMessageData(v_a_1270_);
v___x_1272_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9___redArg(v___x_1271_, v___y_1267_, v___y_1268_);
return v___x_1272_;
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1281_; 
v_a_1273_ = lean_ctor_get(v_x_1265_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_x_1265_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1275_ = v_x_1265_;
v_isShared_1276_ = v_isSharedCheck_1281_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v_x_1265_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1281_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v___x_1279_; 
v___x_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
return v___x_1279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_x_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5___redArg(v_x_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec_ref(v___y_1283_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg(lean_object* v_typeName_1288_, lean_object* v_constName_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v___x_1294_; lean_object* v_env_1295_; uint8_t v___x_1296_; 
v___x_1294_ = lean_st_ref_get(v___y_1292_);
v_env_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc_ref(v_env_1295_);
lean_dec(v___x_1294_);
lean_inc(v_constName_1289_);
v___x_1296_ = lean_has_compile_error(v_env_1295_, v_constName_1289_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg___lam__0(v___y_1291_, v___y_1292_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1317_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1300_ = v___x_1297_;
v_isShared_1301_ = v_isSharedCheck_1317_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1297_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1317_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
if (lean_obj_tag(v_a_1298_) == 0)
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1312_; 
lean_dec(v_constName_1289_);
lean_dec(v_typeName_1288_);
v_a_1302_ = lean_ctor_get(v_a_1298_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_a_1298_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1304_ = v_a_1298_;
v_isShared_1305_ = v_isSharedCheck_1312_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v_a_1298_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1312_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
lean_object* v___x_1309_; 
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v___x_1307_);
v___x_1309_ = v___x_1300_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1307_);
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
else
{
lean_object* v_a_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
lean_del_object(v___x_1300_);
v_a_1313_ = lean_ctor_get(v_a_1298_, 0);
lean_inc(v_a_1313_);
lean_dec_ref_known(v_a_1298_, 1);
v___x_1314_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1291_);
v___x_1315_ = l_Lean_Environment_evalConstCheck___redArg(v_a_1313_, v___x_1314_, v_typeName_1288_, v_constName_1289_);
lean_dec_ref(v___x_1314_);
v___x_1316_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5___redArg(v___x_1315_, v___y_1290_, v___y_1291_, v___y_1292_);
return v___x_1316_;
}
}
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
lean_dec(v_constName_1289_);
lean_dec(v_typeName_1288_);
v_a_1318_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1297_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1297_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
else
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg();
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1371_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1329_ = v___x_1326_;
v_isShared_1330_ = v_isSharedCheck_1371_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1326_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1371_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
if (lean_obj_tag(v_a_1327_) == 0)
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1341_; 
lean_dec(v_constName_1289_);
lean_dec(v_typeName_1288_);
v_a_1331_ = lean_ctor_get(v_a_1327_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_a_1327_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1333_ = v_a_1327_;
v_isShared_1334_ = v_isSharedCheck_1341_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v_a_1327_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1341_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1331_);
v___x_1336_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1338_; 
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v___x_1336_);
v___x_1338_ = v___x_1329_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
else
{
lean_object* v___x_1342_; 
lean_dec_ref_known(v_a_1327_, 1);
lean_del_object(v___x_1329_);
v___x_1342_ = l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg___lam__0(v___y_1291_, v___y_1292_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1362_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1345_ = v___x_1342_;
v_isShared_1346_ = v_isSharedCheck_1362_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1362_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
if (lean_obj_tag(v_a_1343_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1357_; 
lean_dec(v_constName_1289_);
lean_dec(v_typeName_1288_);
v_a_1347_ = lean_ctor_get(v_a_1343_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v_a_1343_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1349_ = v_a_1343_;
v_isShared_1350_ = v_isSharedCheck_1357_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v_a_1343_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1357_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1347_);
v___x_1352_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1354_; 
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v___x_1352_);
v___x_1354_ = v___x_1345_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
lean_del_object(v___x_1345_);
v_a_1358_ = lean_ctor_get(v_a_1343_, 0);
lean_inc(v_a_1358_);
lean_dec_ref_known(v_a_1343_, 1);
v___x_1359_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1291_);
v___x_1360_ = l_Lean_Environment_evalConstCheck___redArg(v_a_1358_, v___x_1359_, v_typeName_1288_, v_constName_1289_);
lean_dec_ref(v___x_1359_);
v___x_1361_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5___redArg(v___x_1360_, v___y_1290_, v___y_1291_, v___y_1292_);
return v___x_1361_;
}
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_dec(v_constName_1289_);
lean_dec(v_typeName_1288_);
v_a_1363_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1342_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1342_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_dec(v_constName_1289_);
lean_dec(v_typeName_1288_);
v_a_1372_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1326_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1326_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg___boxed(lean_object* v_typeName_1380_, lean_object* v_constName_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg(v_typeName_1380_, v_constName_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec_ref(v___y_1382_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2(lean_object* v_declName_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg___closed__0));
v___x_1393_ = l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg(v___x_1392_, v_declName_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2___boxed(lean_object* v_declName_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2(v_declName_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec_ref(v___y_1395_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_handleCodeAction_spec__3(size_t v_sz_1400_, size_t v_i_1401_, lean_object* v_bs_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
uint8_t v___x_1407_; 
v___x_1407_ = lean_usize_dec_lt(v_i_1401_, v_sz_1400_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1408_, 0, v_bs_1402_);
v___x_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1408_);
return v___x_1409_;
}
else
{
lean_object* v_v_1410_; lean_object* v___x_1411_; lean_object* v_bs_x27_1412_; lean_object* v___x_1413_; 
v_v_1410_ = lean_array_uget(v_bs_1402_, v_i_1401_);
v___x_1411_ = lean_unsigned_to_nat(0u);
v_bs_x27_1412_ = lean_array_uset(v_bs_1402_, v_i_1401_, v___x_1411_);
v___x_1413_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2(v_v_1410_, v___y_1403_, v___y_1404_, v___y_1405_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1434_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1434_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1434_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
if (lean_obj_tag(v_a_1414_) == 0)
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1428_; 
lean_dec_ref(v_bs_x27_1412_);
v_a_1418_ = lean_ctor_get(v_a_1414_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_a_1414_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1420_ = v_a_1414_;
v_isShared_1421_ = v_isSharedCheck_1428_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v_a_1414_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1428_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
lean_object* v___x_1425_; 
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v___x_1423_);
v___x_1425_ = v___x_1416_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1423_);
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
else
{
lean_object* v_a_1429_; size_t v___x_1430_; size_t v___x_1431_; lean_object* v___x_1432_; 
lean_del_object(v___x_1416_);
v_a_1429_ = lean_ctor_get(v_a_1414_, 0);
lean_inc(v_a_1429_);
lean_dec_ref_known(v_a_1414_, 1);
v___x_1430_ = ((size_t)1ULL);
v___x_1431_ = lean_usize_add(v_i_1401_, v___x_1430_);
v___x_1432_ = lean_array_uset(v_bs_x27_1412_, v_i_1401_, v_a_1429_);
v_i_1401_ = v___x_1431_;
v_bs_1402_ = v___x_1432_;
goto _start;
}
}
}
else
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
lean_dec_ref(v_bs_x27_1412_);
v_a_1435_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1413_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1413_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_handleCodeAction_spec__3___boxed(lean_object* v_sz_1443_, lean_object* v_i_1444_, lean_object* v_bs_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
size_t v_sz_boxed_1450_; size_t v_i_boxed_1451_; lean_object* v_res_1452_; 
v_sz_boxed_1450_ = lean_unbox_usize(v_sz_1443_);
lean_dec(v_sz_1443_);
v_i_boxed_1451_ = lean_unbox_usize(v_i_1444_);
lean_dec(v_i_1444_);
v_res_1452_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_handleCodeAction_spec__3(v_sz_boxed_1450_, v_i_boxed_1451_, v_bs_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec_ref(v___y_1446_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_handleCodeAction_spec__1_spec__1(lean_object* v_init_1453_, lean_object* v_x_1454_){
_start:
{
if (lean_obj_tag(v_x_1454_) == 0)
{
lean_object* v_k_1455_; lean_object* v_l_1456_; lean_object* v_r_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v_k_1455_ = lean_ctor_get(v_x_1454_, 1);
lean_inc(v_k_1455_);
v_l_1456_ = lean_ctor_get(v_x_1454_, 3);
lean_inc(v_l_1456_);
v_r_1457_ = lean_ctor_get(v_x_1454_, 4);
lean_inc(v_r_1457_);
lean_dec_ref_known(v_x_1454_, 5);
v___x_1458_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_handleCodeAction_spec__1_spec__1(v_init_1453_, v_l_1456_);
v___x_1459_ = lean_array_push(v___x_1458_, v_k_1455_);
v_init_1453_ = v___x_1459_;
v_x_1454_ = v_r_1457_;
goto _start;
}
else
{
return v_init_1453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeAction___lam__0(lean_object* v___x_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v___x_1466_; lean_object* v_env_1467_; lean_object* v___x_1468_; lean_object* v_toEnvExtension_1469_; lean_object* v_asyncMode_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___y_1474_; 
v___x_1466_ = lean_st_ref_get(v___y_1464_);
v_env_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc_ref(v_env_1467_);
lean_dec(v___x_1466_);
v___x_1468_ = l_Lean_Server_codeActionProviderExt;
v_toEnvExtension_1469_ = lean_ctor_get(v___x_1468_, 0);
v_asyncMode_1470_ = lean_ctor_get(v_toEnvExtension_1469_, 2);
v___x_1471_ = lean_box(0);
v___x_1472_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1461_, v___x_1468_, v_env_1467_, v_asyncMode_1470_, v___x_1471_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_size_1522_; 
v_size_1522_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_size_1522_);
v___y_1474_ = v_size_1522_;
goto v___jp_1473_;
}
else
{
lean_object* v___x_1523_; 
v___x_1523_ = lean_unsigned_to_nat(0u);
v___y_1474_ = v___x_1523_;
goto v___jp_1473_;
}
v___jp_1473_:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; size_t v_sz_1477_; size_t v___x_1478_; lean_object* v___x_1479_; 
v___x_1475_ = lean_mk_empty_array_with_capacity(v___y_1474_);
lean_dec(v___y_1474_);
v___x_1476_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_handleCodeAction_spec__1_spec__1(v___x_1475_, v___x_1472_);
v_sz_1477_ = lean_array_size(v___x_1476_);
v___x_1478_ = ((size_t)0ULL);
lean_inc_ref(v___x_1476_);
v___x_1479_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_handleCodeAction_spec__3(v_sz_1477_, v___x_1478_, v___x_1476_, v___y_1462_, v___y_1463_, v___y_1464_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1513_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1482_ = v___x_1479_;
v_isShared_1483_ = v_isSharedCheck_1513_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1513_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
if (lean_obj_tag(v_a_1480_) == 0)
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1494_; 
lean_dec_ref(v___x_1476_);
v_a_1484_ = lean_ctor_get(v_a_1480_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v_a_1480_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1486_ = v_a_1480_;
v_isShared_1487_ = v_isSharedCheck_1494_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v_a_1480_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1494_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v___x_1491_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 0, v___x_1489_);
v___x_1491_ = v___x_1482_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1489_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1512_; 
v_a_1495_ = lean_ctor_get(v_a_1480_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_a_1480_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1497_ = v_a_1480_;
v_isShared_1498_ = v_isSharedCheck_1512_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v_a_1480_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1512_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1499_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_builtinCodeActionProviders;
v___x_1500_ = lean_st_ref_get(v___x_1499_);
v___x_1501_ = lean_box(0);
v___x_1502_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_handleCodeAction_spec__4(v___x_1501_, v___x_1500_);
lean_dec(v___x_1500_);
v___x_1503_ = lean_array_mk(v___x_1502_);
v___x_1504_ = l_Array_zip___redArg(v___x_1476_, v_a_1495_);
lean_dec(v_a_1495_);
lean_dec_ref(v___x_1476_);
v___x_1505_ = l_Array_append___redArg(v___x_1503_, v___x_1504_);
lean_dec_ref(v___x_1504_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v___x_1505_);
v___x_1507_ = v___x_1497_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1505_);
v___x_1507_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1509_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 0, v___x_1507_);
v___x_1509_ = v___x_1482_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
lean_dec_ref(v___x_1476_);
v_a_1514_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1479_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1479_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeAction___lam__0___boxed(lean_object* v___x_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Lean_Server_handleCodeAction___lam__0(v___x_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec_ref(v___y_1525_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Server_handleCodeAction_spec__0___redArg(lean_object* v_params_1530_, lean_object* v_fst_1531_, size_t v_sz_1532_, size_t v_i_1533_, lean_object* v_bs_1534_){
_start:
{
uint8_t v___x_1536_; 
v___x_1536_ = lean_usize_dec_lt(v_i_1533_, v_sz_1532_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; 
lean_dec(v_fst_1531_);
lean_dec_ref(v_params_1530_);
v___x_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1537_, 0, v_bs_1534_);
return v___x_1537_;
}
else
{
lean_object* v_v_1538_; lean_object* v_eager_1539_; lean_object* v_toWorkDoneProgressParams_1540_; lean_object* v_toPartialResultParams_1541_; lean_object* v_title_1542_; lean_object* v_kind_x3f_1543_; lean_object* v_diagnostics_x3f_1544_; lean_object* v_isPreferred_x3f_1545_; lean_object* v_disabled_x3f_1546_; lean_object* v_edit_x3f_1547_; lean_object* v_command_x3f_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1565_; 
v_v_1538_ = lean_array_uget_borrowed(v_bs_1534_, v_i_1533_);
v_eager_1539_ = lean_ctor_get(v_v_1538_, 0);
lean_inc_ref(v_eager_1539_);
v_toWorkDoneProgressParams_1540_ = lean_ctor_get(v_eager_1539_, 0);
v_toPartialResultParams_1541_ = lean_ctor_get(v_eager_1539_, 1);
v_title_1542_ = lean_ctor_get(v_eager_1539_, 2);
v_kind_x3f_1543_ = lean_ctor_get(v_eager_1539_, 3);
v_diagnostics_x3f_1544_ = lean_ctor_get(v_eager_1539_, 4);
v_isPreferred_x3f_1545_ = lean_ctor_get(v_eager_1539_, 5);
v_disabled_x3f_1546_ = lean_ctor_get(v_eager_1539_, 6);
v_edit_x3f_1547_ = lean_ctor_get(v_eager_1539_, 7);
v_command_x3f_1548_ = lean_ctor_get(v_eager_1539_, 8);
v_isSharedCheck_1565_ = !lean_is_exclusive(v_eager_1539_);
if (v_isSharedCheck_1565_ == 0)
{
lean_object* v_unused_1566_; 
v_unused_1566_ = lean_ctor_get(v_eager_1539_, 9);
lean_dec(v_unused_1566_);
v___x_1550_ = v_eager_1539_;
v_isShared_1551_ = v_isSharedCheck_1565_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_command_x3f_1548_);
lean_inc(v_edit_x3f_1547_);
lean_inc(v_disabled_x3f_1546_);
lean_inc(v_isPreferred_x3f_1545_);
lean_inc(v_diagnostics_x3f_1544_);
lean_inc(v_kind_x3f_1543_);
lean_inc(v_title_1542_);
lean_inc(v_toPartialResultParams_1541_);
lean_inc(v_toWorkDoneProgressParams_1540_);
lean_dec(v_eager_1539_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1565_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1552_; lean_object* v_bs_x27_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1552_ = lean_unsigned_to_nat(0u);
v_bs_x27_1553_ = lean_array_uset(v_bs_1534_, v_i_1533_, v___x_1552_);
v___x_1554_ = lean_usize_to_nat(v_i_1533_);
lean_inc(v_fst_1531_);
lean_inc_ref(v_params_1530_);
v___x_1555_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1555_, 0, v_params_1530_);
lean_ctor_set(v___x_1555_, 1, v_fst_1531_);
lean_ctor_set(v___x_1555_, 2, v___x_1554_);
v___x_1556_ = l_Lean_Server_instToJsonCodeActionResolveData_toJson(v___x_1555_);
v___x_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 9, v___x_1557_);
v___x_1559_ = v___x_1550_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_toWorkDoneProgressParams_1540_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_toPartialResultParams_1541_);
lean_ctor_set(v_reuseFailAlloc_1564_, 2, v_title_1542_);
lean_ctor_set(v_reuseFailAlloc_1564_, 3, v_kind_x3f_1543_);
lean_ctor_set(v_reuseFailAlloc_1564_, 4, v_diagnostics_x3f_1544_);
lean_ctor_set(v_reuseFailAlloc_1564_, 5, v_isPreferred_x3f_1545_);
lean_ctor_set(v_reuseFailAlloc_1564_, 6, v_disabled_x3f_1546_);
lean_ctor_set(v_reuseFailAlloc_1564_, 7, v_edit_x3f_1547_);
lean_ctor_set(v_reuseFailAlloc_1564_, 8, v_command_x3f_1548_);
lean_ctor_set(v_reuseFailAlloc_1564_, 9, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
size_t v___x_1560_; size_t v___x_1561_; lean_object* v___x_1562_; 
v___x_1560_ = ((size_t)1ULL);
v___x_1561_ = lean_usize_add(v_i_1533_, v___x_1560_);
v___x_1562_ = lean_array_uset(v_bs_x27_1553_, v_i_1533_, v___x_1559_);
v_i_1533_ = v___x_1561_;
v_bs_1534_ = v___x_1562_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Server_handleCodeAction_spec__0___redArg___boxed(lean_object* v_params_1567_, lean_object* v_fst_1568_, lean_object* v_sz_1569_, lean_object* v_i_1570_, lean_object* v_bs_1571_, lean_object* v___y_1572_){
_start:
{
size_t v_sz_boxed_1573_; size_t v_i_boxed_1574_; lean_object* v_res_1575_; 
v_sz_boxed_1573_ = lean_unbox_usize(v_sz_1569_);
lean_dec(v_sz_1569_);
v_i_boxed_1574_ = lean_unbox_usize(v_i_1570_);
lean_dec(v_i_1570_);
v_res_1575_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Server_handleCodeAction_spec__0___redArg(v_params_1567_, v_fst_1568_, v_sz_boxed_1573_, v_i_boxed_1574_, v_bs_1571_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_handleCodeAction_spec__5(lean_object* v_params_1576_, lean_object* v_snap_1577_, lean_object* v_as_1578_, size_t v_i_1579_, size_t v_stop_1580_, lean_object* v_b_1581_, lean_object* v___y_1582_){
_start:
{
uint8_t v___x_1584_; 
v___x_1584_ = lean_usize_dec_eq(v_i_1579_, v_stop_1580_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; lean_object* v_fst_1586_; lean_object* v_snd_1587_; lean_object* v___x_1588_; 
v___x_1585_ = lean_array_uget_borrowed(v_as_1578_, v_i_1579_);
v_fst_1586_ = lean_ctor_get(v___x_1585_, 0);
v_snd_1587_ = lean_ctor_get(v___x_1585_, 1);
v___x_1588_ = l_Lean_Server_RequestM_checkCancelled(v___y_1582_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v___x_1589_; 
lean_dec_ref_known(v___x_1588_, 1);
lean_inc(v_snd_1587_);
lean_inc_ref(v___y_1582_);
lean_inc_ref(v_snap_1577_);
lean_inc_ref(v_params_1576_);
v___x_1589_ = lean_apply_4(v_snd_1587_, v_params_1576_, v_snap_1577_, v___y_1582_, lean_box(0));
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; size_t v_sz_1591_; size_t v___x_1592_; lean_object* v___x_1593_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1589_, 1);
v_sz_1591_ = lean_array_size(v_a_1590_);
v___x_1592_ = ((size_t)0ULL);
lean_inc(v_fst_1586_);
lean_inc_ref(v_params_1576_);
v___x_1593_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Server_handleCodeAction_spec__0___redArg(v_params_1576_, v_fst_1586_, v_sz_1591_, v___x_1592_, v_a_1590_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; lean_object* v___x_1595_; size_t v___x_1596_; size_t v___x_1597_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
lean_dec_ref_known(v___x_1593_, 1);
v___x_1595_ = l_Array_append___redArg(v_b_1581_, v_a_1594_);
lean_dec(v_a_1594_);
v___x_1596_ = ((size_t)1ULL);
v___x_1597_ = lean_usize_add(v_i_1579_, v___x_1596_);
v_i_1579_ = v___x_1597_;
v_b_1581_ = v___x_1595_;
goto _start;
}
else
{
lean_dec_ref(v_b_1581_);
lean_dec_ref(v_snap_1577_);
lean_dec_ref(v_params_1576_);
return v___x_1593_;
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_dec_ref(v_b_1581_);
lean_dec_ref(v_snap_1577_);
lean_dec_ref(v_params_1576_);
v_a_1599_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1589_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1589_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_dec_ref(v_b_1581_);
lean_dec_ref(v_snap_1577_);
lean_dec_ref(v_params_1576_);
v_a_1607_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1588_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1588_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
else
{
lean_object* v___x_1615_; 
lean_dec_ref(v_snap_1577_);
lean_dec_ref(v_params_1576_);
v___x_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1615_, 0, v_b_1581_);
return v___x_1615_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_handleCodeAction_spec__5___boxed(lean_object* v_params_1616_, lean_object* v_snap_1617_, lean_object* v_as_1618_, lean_object* v_i_1619_, lean_object* v_stop_1620_, lean_object* v_b_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
size_t v_i_boxed_1624_; size_t v_stop_boxed_1625_; lean_object* v_res_1626_; 
v_i_boxed_1624_ = lean_unbox_usize(v_i_1619_);
lean_dec(v_i_1619_);
v_stop_boxed_1625_ = lean_unbox_usize(v_stop_1620_);
lean_dec(v_stop_1620_);
v_res_1626_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_handleCodeAction_spec__5(v_params_1616_, v_snap_1617_, v_as_1618_, v_i_boxed_1624_, v_stop_boxed_1625_, v_b_1621_, v___y_1622_);
lean_dec_ref(v___y_1622_);
lean_dec_ref(v_as_1618_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeAction___lam__1(lean_object* v___f_1629_, lean_object* v_params_1630_, lean_object* v_snap_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v___x_1634_; 
lean_inc_ref(v_snap_1631_);
v___x_1634_ = l_Lean_Server_RequestM_runCoreM___redArg(v_snap_1631_, v___f_1629_, v___y_1632_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1649_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1649_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1649_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; uint8_t v___x_1642_; 
v___x_1639_ = lean_unsigned_to_nat(0u);
v___x_1640_ = ((lean_object*)(l_Lean_Server_handleCodeAction___lam__1___closed__0));
v___x_1641_ = lean_array_get_size(v_a_1635_);
v___x_1642_ = lean_nat_dec_lt(v___x_1639_, v___x_1641_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1644_; 
lean_dec(v_a_1635_);
lean_dec_ref(v_snap_1631_);
lean_dec_ref(v_params_1630_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1640_);
v___x_1644_ = v___x_1637_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1640_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
else
{
size_t v___x_1646_; size_t v___x_1647_; lean_object* v___x_1648_; 
lean_del_object(v___x_1637_);
v___x_1646_ = ((size_t)0ULL);
v___x_1647_ = lean_usize_of_nat(v___x_1641_);
v___x_1648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_handleCodeAction_spec__5(v_params_1630_, v_snap_1631_, v_a_1635_, v___x_1646_, v___x_1647_, v___x_1640_, v___y_1632_);
lean_dec(v_a_1635_);
return v___x_1648_;
}
}
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
lean_dec_ref(v_snap_1631_);
lean_dec_ref(v_params_1630_);
v_a_1650_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1634_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1634_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeAction___lam__1___boxed(lean_object* v___f_1658_, lean_object* v_params_1659_, lean_object* v_snap_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Lean_Server_handleCodeAction___lam__1(v___f_1658_, v_params_1659_, v_snap_1660_, v___y_1661_);
lean_dec_ref(v___y_1661_);
return v_res_1663_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_handleCodeAction___lam__2(lean_object* v___x_1664_, lean_object* v_s_1665_){
_start:
{
lean_object* v___x_1666_; uint8_t v___x_1667_; 
v___x_1666_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_s_1665_);
v___x_1667_ = lean_nat_dec_le(v___x_1664_, v___x_1666_);
lean_dec(v___x_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeAction___lam__2___boxed(lean_object* v___x_1668_, lean_object* v_s_1669_){
_start:
{
uint8_t v_res_1670_; lean_object* v_r_1671_; 
v_res_1670_ = l_Lean_Server_handleCodeAction___lam__2(v___x_1668_, v_s_1669_);
lean_dec_ref(v_s_1669_);
lean_dec(v___x_1668_);
v_r_1671_ = lean_box(v_res_1670_);
return v_r_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeAction___lam__3(lean_object* v___x_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1672_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeAction___lam__3___boxed(lean_object* v___x_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_Server_handleCodeAction___lam__3(v___x_1676_, v___y_1677_);
lean_dec_ref(v___y_1677_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeAction(lean_object* v_params_1686_, lean_object* v_a_1687_){
_start:
{
lean_object* v___f_1689_; lean_object* v___f_1690_; lean_object* v___x_1691_; lean_object* v_a_1692_; lean_object* v_toEditableDocumentCore_1693_; lean_object* v_meta_1694_; lean_object* v_range_1695_; lean_object* v_text_1696_; lean_object* v_end_1697_; lean_object* v___x_1698_; lean_object* v___f_1699_; lean_object* v___f_1700_; lean_object* v___x_1701_; 
v___f_1689_ = ((lean_object*)(l_Lean_Server_handleCodeAction___closed__0));
lean_inc_ref(v_params_1686_);
v___f_1690_ = lean_alloc_closure((void*)(l_Lean_Server_handleCodeAction___lam__1___boxed), 5, 2);
lean_closure_set(v___f_1690_, 0, v___f_1689_);
lean_closure_set(v___f_1690_, 1, v_params_1686_);
v___x_1691_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleCodeAction_spec__6(v_a_1687_);
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_a_1692_);
lean_dec_ref(v___x_1691_);
v_toEditableDocumentCore_1693_ = lean_ctor_get(v_a_1692_, 0);
v_meta_1694_ = lean_ctor_get(v_toEditableDocumentCore_1693_, 0);
v_range_1695_ = lean_ctor_get(v_params_1686_, 3);
lean_inc_ref(v_range_1695_);
lean_dec_ref(v_params_1686_);
v_text_1696_ = lean_ctor_get(v_meta_1694_, 3);
v_end_1697_ = lean_ctor_get(v_range_1695_, 1);
lean_inc_ref(v_end_1697_);
lean_dec_ref(v_range_1695_);
v___x_1698_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1696_, v_end_1697_);
v___f_1699_ = lean_alloc_closure((void*)(l_Lean_Server_handleCodeAction___lam__2___boxed), 2, 1);
lean_closure_set(v___f_1699_, 0, v___x_1698_);
v___f_1700_ = ((lean_object*)(l_Lean_Server_handleCodeAction___closed__2));
v___x_1701_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_a_1692_, v___f_1699_, v___f_1700_, v___f_1690_, v_a_1687_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeAction___boxed(lean_object* v_params_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Lean_Server_handleCodeAction(v_params_1702_, v_a_1703_);
lean_dec_ref(v_a_1703_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Server_handleCodeAction_spec__0(lean_object* v_params_1706_, lean_object* v_fst_1707_, lean_object* v_as_1708_, size_t v_sz_1709_, size_t v_i_1710_, lean_object* v_bs_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Server_handleCodeAction_spec__0___redArg(v_params_1706_, v_fst_1707_, v_sz_1709_, v_i_1710_, v_bs_1711_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Server_handleCodeAction_spec__0___boxed(lean_object* v_params_1715_, lean_object* v_fst_1716_, lean_object* v_as_1717_, lean_object* v_sz_1718_, lean_object* v_i_1719_, lean_object* v_bs_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
size_t v_sz_boxed_1723_; size_t v_i_boxed_1724_; lean_object* v_res_1725_; 
v_sz_boxed_1723_ = lean_unbox_usize(v_sz_1718_);
lean_dec(v_sz_1718_);
v_i_boxed_1724_ = lean_unbox_usize(v_i_1719_);
lean_dec(v_i_1719_);
v_res_1725_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Server_handleCodeAction_spec__0(v_params_1715_, v_fst_1716_, v_as_1717_, v_sz_boxed_1723_, v_i_boxed_1724_, v_bs_1720_, v___y_1721_);
lean_dec_ref(v___y_1721_);
lean_dec_ref(v_as_1717_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_handleCodeAction_spec__1(lean_object* v_init_1726_, lean_object* v_t_1727_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_handleCodeAction_spec__1_spec__1(v_init_1726_, v_t_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6(lean_object* v_00_u03b1_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg();
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b1_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6(v_00_u03b1_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec_ref(v___y_1736_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3(lean_object* v_00_u03b1_1741_, lean_object* v_typeName_1742_, lean_object* v_constName_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg(v_typeName_1742_, v_constName_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1749_, lean_object* v_typeName_1750_, lean_object* v_constName_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3(v_00_u03b1_1749_, v_typeName_1750_, v_constName_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec_ref(v___y_1752_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1757_, lean_object* v_x_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5___redArg(v_x_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1764_, lean_object* v_x_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5(v_00_u03b1_1764_, v_x_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec_ref(v___y_1766_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9(lean_object* v_00_u03b1_1771_, lean_object* v_msg_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9___redArg(v_msg_1772_, v___y_1774_, v___y_1775_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b1_1778_, lean_object* v_msg_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9(v_00_u03b1_1778_, v_msg_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec_ref(v___y_1780_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__2_spec__3(size_t v_sz_1785_, size_t v_i_1786_, lean_object* v_bs_1787_){
_start:
{
uint8_t v___x_1788_; 
v___x_1788_ = lean_usize_dec_lt(v_i_1786_, v_sz_1785_);
if (v___x_1788_ == 0)
{
return v_bs_1787_;
}
else
{
lean_object* v_v_1789_; lean_object* v___x_1790_; lean_object* v_bs_x27_1791_; lean_object* v___x_1792_; size_t v___x_1793_; size_t v___x_1794_; lean_object* v___x_1795_; 
v_v_1789_ = lean_array_uget(v_bs_1787_, v_i_1786_);
v___x_1790_ = lean_unsigned_to_nat(0u);
v_bs_x27_1791_ = lean_array_uset(v_bs_1787_, v_i_1786_, v___x_1790_);
v___x_1792_ = l_Lean_Lsp_instToJsonCodeAction_toJson(v_v_1789_);
v___x_1793_ = ((size_t)1ULL);
v___x_1794_ = lean_usize_add(v_i_1786_, v___x_1793_);
v___x_1795_ = lean_array_uset(v_bs_x27_1791_, v_i_1786_, v___x_1792_);
v_i_1786_ = v___x_1794_;
v_bs_1787_ = v___x_1795_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object* v_sz_1797_, lean_object* v_i_1798_, lean_object* v_bs_1799_){
_start:
{
size_t v_sz_boxed_1800_; size_t v_i_boxed_1801_; lean_object* v_res_1802_; 
v_sz_boxed_1800_ = lean_unbox_usize(v_sz_1797_);
lean_dec(v_sz_1797_);
v_i_boxed_1801_ = lean_unbox_usize(v_i_1798_);
lean_dec(v_i_1798_);
v_res_1802_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__2_spec__3(v_sz_boxed_1800_, v_i_boxed_1801_, v_bs_1799_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_a_1803_){
_start:
{
size_t v_sz_1804_; size_t v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v_sz_1804_ = lean_array_size(v_a_1803_);
v___x_1805_ = ((size_t)0ULL);
v___x_1806_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__2_spec__3(v_sz_1804_, v___x_1805_, v_a_1803_);
v___x_1807_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__1(lean_object* v_serialize_x3f_1808_, uint8_t v_val_1809_, lean_object* v___y_1810_){
_start:
{
if (lean_obj_tag(v___y_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec(v_serialize_x3f_1808_);
v_a_1811_ = lean_ctor_get(v___y_1810_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___y_1810_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___y_1810_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___y_1810_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
else
{
if (lean_obj_tag(v_serialize_x3f_1808_) == 1)
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1830_; 
v_a_1819_ = lean_ctor_get(v___y_1810_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___y_1810_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1821_ = v___y_1810_;
v_isShared_1822_ = v_isSharedCheck_1830_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___y_1810_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1830_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v_val_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1828_; 
v_val_1823_ = lean_ctor_get(v_serialize_x3f_1808_, 0);
lean_inc(v_val_1823_);
lean_dec_ref_known(v_serialize_x3f_1808_, 1);
v___x_1824_ = lean_box(0);
v___x_1825_ = lean_apply_1(v_val_1823_, v_a_1819_);
v___x_1826_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1826_, 0, v___x_1824_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
lean_ctor_set_uint8(v___x_1826_, sizeof(void*)*2, v_val_1809_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1826_);
v___x_1828_ = v___x_1821_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1826_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1842_; 
lean_dec(v_serialize_x3f_1808_);
v_a_1831_ = lean_ctor_get(v___y_1810_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___y_1810_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1833_ = v___y_1810_;
v_isShared_1834_ = v_isSharedCheck_1842_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___y_1810_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1842_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1840_; 
v___x_1835_ = l_Lean_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__2(v_a_1831_);
lean_inc(v___x_1835_);
v___x_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
v___x_1837_ = l_Lean_Json_compress(v___x_1835_);
v___x_1838_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1838_, 0, v___x_1836_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
lean_ctor_set_uint8(v___x_1838_, sizeof(void*)*2, v_val_1809_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 0, v___x_1838_);
v___x_1840_ = v___x_1833_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object* v_serialize_x3f_1843_, lean_object* v_val_1844_, lean_object* v___y_1845_){
_start:
{
uint8_t v_val_949__boxed_1846_; lean_object* v_res_1847_; 
v_val_949__boxed_1846_ = lean_unbox(v_val_1844_);
v_res_1847_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__1(v_serialize_x3f_1843_, v_val_949__boxed_1846_, v___y_1845_);
return v_res_1847_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6___redArg(lean_object* v_keys_1848_, lean_object* v_i_1849_, lean_object* v_k_1850_){
_start:
{
lean_object* v___x_1851_; uint8_t v___x_1852_; 
v___x_1851_ = lean_array_get_size(v_keys_1848_);
v___x_1852_ = lean_nat_dec_lt(v_i_1849_, v___x_1851_);
if (v___x_1852_ == 0)
{
lean_dec(v_i_1849_);
return v___x_1852_;
}
else
{
lean_object* v_k_x27_1853_; uint8_t v___x_1854_; 
v_k_x27_1853_ = lean_array_fget_borrowed(v_keys_1848_, v_i_1849_);
v___x_1854_ = lean_string_dec_eq(v_k_1850_, v_k_x27_1853_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = lean_unsigned_to_nat(1u);
v___x_1856_ = lean_nat_add(v_i_1849_, v___x_1855_);
lean_dec(v_i_1849_);
v_i_1849_ = v___x_1856_;
goto _start;
}
else
{
lean_dec(v_i_1849_);
return v___x_1852_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_keys_1858_, lean_object* v_i_1859_, lean_object* v_k_1860_){
_start:
{
uint8_t v_res_1861_; lean_object* v_r_1862_; 
v_res_1861_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6___redArg(v_keys_1858_, v_i_1859_, v_k_1860_);
lean_dec_ref(v_k_1860_);
lean_dec_ref(v_keys_1858_);
v_r_1862_ = lean_box(v_res_1861_);
return v_r_1862_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(lean_object* v_x_1863_, size_t v_x_1864_, lean_object* v_x_1865_){
_start:
{
if (lean_obj_tag(v_x_1863_) == 0)
{
lean_object* v_es_1866_; lean_object* v___x_1867_; size_t v___x_1868_; size_t v___x_1869_; lean_object* v_j_1870_; lean_object* v___x_1871_; 
v_es_1866_ = lean_ctor_get(v_x_1863_, 0);
v___x_1867_ = lean_box(2);
v___x_1868_ = ((size_t)31ULL);
v___x_1869_ = lean_usize_land(v_x_1864_, v___x_1868_);
v_j_1870_ = lean_usize_to_nat(v___x_1869_);
v___x_1871_ = lean_array_get_borrowed(v___x_1867_, v_es_1866_, v_j_1870_);
lean_dec(v_j_1870_);
switch(lean_obj_tag(v___x_1871_))
{
case 0:
{
lean_object* v_key_1872_; uint8_t v___x_1873_; 
v_key_1872_ = lean_ctor_get(v___x_1871_, 0);
v___x_1873_ = lean_string_dec_eq(v_x_1865_, v_key_1872_);
return v___x_1873_;
}
case 1:
{
lean_object* v_node_1874_; size_t v___x_1875_; size_t v___x_1876_; 
v_node_1874_ = lean_ctor_get(v___x_1871_, 0);
v___x_1875_ = ((size_t)5ULL);
v___x_1876_ = lean_usize_shift_right(v_x_1864_, v___x_1875_);
v_x_1863_ = v_node_1874_;
v_x_1864_ = v___x_1876_;
goto _start;
}
default: 
{
uint8_t v___x_1878_; 
v___x_1878_ = 0;
return v___x_1878_;
}
}
}
else
{
lean_object* v_ks_1879_; lean_object* v___x_1880_; uint8_t v___x_1881_; 
v_ks_1879_ = lean_ctor_get(v_x_1863_, 0);
v___x_1880_ = lean_unsigned_to_nat(0u);
v___x_1881_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6___redArg(v_ks_1879_, v___x_1880_, v_x_1865_);
return v___x_1881_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(lean_object* v_x_1882_, lean_object* v_x_1883_, lean_object* v_x_1884_){
_start:
{
size_t v_x_1032__boxed_1885_; uint8_t v_res_1886_; lean_object* v_r_1887_; 
v_x_1032__boxed_1885_ = lean_unbox_usize(v_x_1883_);
lean_dec(v_x_1883_);
v_res_1886_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_1882_, v_x_1032__boxed_1885_, v_x_1884_);
lean_dec_ref(v_x_1884_);
lean_dec_ref(v_x_1882_);
v_r_1887_ = lean_box(v_res_1886_);
return v_r_1887_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3___redArg(lean_object* v_x_1888_, lean_object* v_x_1889_){
_start:
{
uint64_t v___x_1890_; size_t v___x_1891_; uint8_t v___x_1892_; 
v___x_1890_ = lean_string_hash(v_x_1889_);
v___x_1891_ = lean_uint64_to_usize(v___x_1890_);
v___x_1892_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_1888_, v___x_1891_, v_x_1889_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3___redArg___boxed(lean_object* v_x_1893_, lean_object* v_x_1894_){
_start:
{
uint8_t v_res_1895_; lean_object* v_r_1896_; 
v_res_1895_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3___redArg(v_x_1893_, v_x_1894_);
lean_dec_ref(v_x_1894_);
lean_dec_ref(v_x_1893_);
v_r_1896_ = lean_box(v_res_1895_);
return v_r_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9_spec__10___redArg(lean_object* v_x_1897_, lean_object* v_x_1898_, lean_object* v_x_1899_, lean_object* v_x_1900_){
_start:
{
lean_object* v_ks_1901_; lean_object* v_vs_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1926_; 
v_ks_1901_ = lean_ctor_get(v_x_1897_, 0);
v_vs_1902_ = lean_ctor_get(v_x_1897_, 1);
v_isSharedCheck_1926_ = !lean_is_exclusive(v_x_1897_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1904_ = v_x_1897_;
v_isShared_1905_ = v_isSharedCheck_1926_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_vs_1902_);
lean_inc(v_ks_1901_);
lean_dec(v_x_1897_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1926_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1906_; uint8_t v___x_1907_; 
v___x_1906_ = lean_array_get_size(v_ks_1901_);
v___x_1907_ = lean_nat_dec_lt(v_x_1898_, v___x_1906_);
if (v___x_1907_ == 0)
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1911_; 
lean_dec(v_x_1898_);
v___x_1908_ = lean_array_push(v_ks_1901_, v_x_1899_);
v___x_1909_ = lean_array_push(v_vs_1902_, v_x_1900_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 1, v___x_1909_);
lean_ctor_set(v___x_1904_, 0, v___x_1908_);
v___x_1911_ = v___x_1904_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1908_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
else
{
lean_object* v_k_x27_1913_; uint8_t v___x_1914_; 
v_k_x27_1913_ = lean_array_fget_borrowed(v_ks_1901_, v_x_1898_);
v___x_1914_ = lean_string_dec_eq(v_x_1899_, v_k_x27_1913_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1916_; 
if (v_isShared_1905_ == 0)
{
v___x_1916_ = v___x_1904_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_ks_1901_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v_vs_1902_);
v___x_1916_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1917_ = lean_unsigned_to_nat(1u);
v___x_1918_ = lean_nat_add(v_x_1898_, v___x_1917_);
lean_dec(v_x_1898_);
v_x_1897_ = v___x_1916_;
v_x_1898_ = v___x_1918_;
goto _start;
}
}
else
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1924_; 
v___x_1921_ = lean_array_fset(v_ks_1901_, v_x_1898_, v_x_1899_);
v___x_1922_ = lean_array_fset(v_vs_1902_, v_x_1898_, v_x_1900_);
lean_dec(v_x_1898_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 1, v___x_1922_);
lean_ctor_set(v___x_1904_, 0, v___x_1921_);
v___x_1924_ = v___x_1904_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1921_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v___x_1922_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9___redArg(lean_object* v_n_1927_, lean_object* v_k_1928_, lean_object* v_v_1929_){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1930_ = lean_unsigned_to_nat(0u);
v___x_1931_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9_spec__10___redArg(v_n_1927_, v___x_1930_, v_k_1928_, v_v_1929_);
return v___x_1931_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1932_; 
v___x_1932_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg(lean_object* v_x_1933_, size_t v_x_1934_, size_t v_x_1935_, lean_object* v_x_1936_, lean_object* v_x_1937_){
_start:
{
if (lean_obj_tag(v_x_1933_) == 0)
{
lean_object* v_es_1938_; size_t v___x_1939_; size_t v___x_1940_; lean_object* v_j_1941_; lean_object* v___x_1942_; uint8_t v___x_1943_; 
v_es_1938_ = lean_ctor_get(v_x_1933_, 0);
v___x_1939_ = ((size_t)31ULL);
v___x_1940_ = lean_usize_land(v_x_1934_, v___x_1939_);
v_j_1941_ = lean_usize_to_nat(v___x_1940_);
v___x_1942_ = lean_array_get_size(v_es_1938_);
v___x_1943_ = lean_nat_dec_lt(v_j_1941_, v___x_1942_);
if (v___x_1943_ == 0)
{
lean_dec(v_j_1941_);
lean_dec(v_x_1937_);
lean_dec_ref(v_x_1936_);
return v_x_1933_;
}
else
{
lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1982_; 
lean_inc_ref(v_es_1938_);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_x_1933_);
if (v_isSharedCheck_1982_ == 0)
{
lean_object* v_unused_1983_; 
v_unused_1983_ = lean_ctor_get(v_x_1933_, 0);
lean_dec(v_unused_1983_);
v___x_1945_ = v_x_1933_;
v_isShared_1946_ = v_isSharedCheck_1982_;
goto v_resetjp_1944_;
}
else
{
lean_dec(v_x_1933_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1982_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v_v_1947_; lean_object* v___x_1948_; lean_object* v_xs_x27_1949_; lean_object* v___y_1951_; 
v_v_1947_ = lean_array_fget(v_es_1938_, v_j_1941_);
v___x_1948_ = lean_box(0);
v_xs_x27_1949_ = lean_array_fset(v_es_1938_, v_j_1941_, v___x_1948_);
switch(lean_obj_tag(v_v_1947_))
{
case 0:
{
lean_object* v_key_1956_; lean_object* v_val_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1967_; 
v_key_1956_ = lean_ctor_get(v_v_1947_, 0);
v_val_1957_ = lean_ctor_get(v_v_1947_, 1);
v_isSharedCheck_1967_ = !lean_is_exclusive(v_v_1947_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1959_ = v_v_1947_;
v_isShared_1960_ = v_isSharedCheck_1967_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_val_1957_);
lean_inc(v_key_1956_);
lean_dec(v_v_1947_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1967_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
uint8_t v___x_1961_; 
v___x_1961_ = lean_string_dec_eq(v_x_1936_, v_key_1956_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
lean_del_object(v___x_1959_);
v___x_1962_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1956_, v_val_1957_, v_x_1936_, v_x_1937_);
v___x_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
v___y_1951_ = v___x_1963_;
goto v___jp_1950_;
}
else
{
lean_object* v___x_1965_; 
lean_dec(v_val_1957_);
lean_dec(v_key_1956_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 1, v_x_1937_);
lean_ctor_set(v___x_1959_, 0, v_x_1936_);
v___x_1965_ = v___x_1959_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_x_1936_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v_x_1937_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
v___y_1951_ = v___x_1965_;
goto v___jp_1950_;
}
}
}
}
case 1:
{
lean_object* v_node_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1980_; 
v_node_1968_ = lean_ctor_get(v_v_1947_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v_v_1947_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1970_ = v_v_1947_;
v_isShared_1971_ = v_isSharedCheck_1980_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_node_1968_);
lean_dec(v_v_1947_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1980_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
size_t v___x_1972_; size_t v___x_1973_; size_t v___x_1974_; size_t v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1978_; 
v___x_1972_ = ((size_t)5ULL);
v___x_1973_ = lean_usize_shift_right(v_x_1934_, v___x_1972_);
v___x_1974_ = ((size_t)1ULL);
v___x_1975_ = lean_usize_add(v_x_1935_, v___x_1974_);
v___x_1976_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg(v_node_1968_, v___x_1973_, v___x_1975_, v_x_1936_, v_x_1937_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v___x_1976_);
v___x_1978_ = v___x_1970_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
v___y_1951_ = v___x_1978_;
goto v___jp_1950_;
}
}
}
default: 
{
lean_object* v___x_1981_; 
v___x_1981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1981_, 0, v_x_1936_);
lean_ctor_set(v___x_1981_, 1, v_x_1937_);
v___y_1951_ = v___x_1981_;
goto v___jp_1950_;
}
}
v___jp_1950_:
{
lean_object* v___x_1952_; lean_object* v___x_1954_; 
v___x_1952_ = lean_array_fset(v_xs_x27_1949_, v_j_1941_, v___y_1951_);
lean_dec(v_j_1941_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 0, v___x_1952_);
v___x_1954_ = v___x_1945_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1952_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
}
else
{
lean_object* v_ks_1984_; lean_object* v_vs_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_2003_; 
v_ks_1984_ = lean_ctor_get(v_x_1933_, 0);
v_vs_1985_ = lean_ctor_get(v_x_1933_, 1);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_x_1933_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1987_ = v_x_1933_;
v_isShared_1988_ = v_isSharedCheck_2003_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_vs_1985_);
lean_inc(v_ks_1984_);
lean_dec(v_x_1933_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_2003_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_ks_1984_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_vs_1985_);
v___x_1990_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v_newNode_1991_; size_t v___x_1992_; uint8_t v___x_1993_; 
v_newNode_1991_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9___redArg(v___x_1990_, v_x_1936_, v_x_1937_);
v___x_1992_ = ((size_t)7ULL);
v___x_1993_ = lean_usize_dec_le(v___x_1992_, v_x_1935_);
if (v___x_1993_ == 0)
{
lean_object* v___x_1994_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1994_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1991_);
v___x_1995_ = lean_unsigned_to_nat(4u);
v___x_1996_ = lean_nat_dec_lt(v___x_1994_, v___x_1995_);
lean_dec(v___x_1994_);
if (v___x_1996_ == 0)
{
lean_object* v_ks_1997_; lean_object* v_vs_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v_ks_1997_ = lean_ctor_get(v_newNode_1991_, 0);
lean_inc_ref(v_ks_1997_);
v_vs_1998_ = lean_ctor_get(v_newNode_1991_, 1);
lean_inc_ref(v_vs_1998_);
lean_dec_ref(v_newNode_1991_);
v___x_1999_ = lean_unsigned_to_nat(0u);
v___x_2000_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg___closed__0);
v___x_2001_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10___redArg(v_x_1935_, v_ks_1997_, v_vs_1998_, v___x_1999_, v___x_2000_);
lean_dec_ref(v_vs_1998_);
lean_dec_ref(v_ks_1997_);
return v___x_2001_;
}
else
{
return v_newNode_1991_;
}
}
else
{
return v_newNode_1991_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10___redArg(size_t v_depth_2004_, lean_object* v_keys_2005_, lean_object* v_vals_2006_, lean_object* v_i_2007_, lean_object* v_entries_2008_){
_start:
{
lean_object* v___x_2009_; uint8_t v___x_2010_; 
v___x_2009_ = lean_array_get_size(v_keys_2005_);
v___x_2010_ = lean_nat_dec_lt(v_i_2007_, v___x_2009_);
if (v___x_2010_ == 0)
{
lean_dec(v_i_2007_);
return v_entries_2008_;
}
else
{
lean_object* v_k_2011_; lean_object* v_v_2012_; uint64_t v___x_2013_; size_t v_h_2014_; size_t v___x_2015_; lean_object* v___x_2016_; size_t v___x_2017_; size_t v___x_2018_; size_t v___x_2019_; size_t v_h_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v_k_2011_ = lean_array_fget_borrowed(v_keys_2005_, v_i_2007_);
v_v_2012_ = lean_array_fget_borrowed(v_vals_2006_, v_i_2007_);
v___x_2013_ = lean_string_hash(v_k_2011_);
v_h_2014_ = lean_uint64_to_usize(v___x_2013_);
v___x_2015_ = ((size_t)5ULL);
v___x_2016_ = lean_unsigned_to_nat(1u);
v___x_2017_ = ((size_t)1ULL);
v___x_2018_ = lean_usize_sub(v_depth_2004_, v___x_2017_);
v___x_2019_ = lean_usize_mul(v___x_2015_, v___x_2018_);
v_h_2020_ = lean_usize_shift_right(v_h_2014_, v___x_2019_);
v___x_2021_ = lean_nat_add(v_i_2007_, v___x_2016_);
lean_dec(v_i_2007_);
lean_inc(v_v_2012_);
lean_inc(v_k_2011_);
v___x_2022_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg(v_entries_2008_, v_h_2020_, v_depth_2004_, v_k_2011_, v_v_2012_);
v_i_2007_ = v___x_2021_;
v_entries_2008_ = v___x_2022_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_depth_2024_, lean_object* v_keys_2025_, lean_object* v_vals_2026_, lean_object* v_i_2027_, lean_object* v_entries_2028_){
_start:
{
size_t v_depth_boxed_2029_; lean_object* v_res_2030_; 
v_depth_boxed_2029_ = lean_unbox_usize(v_depth_2024_);
lean_dec(v_depth_2024_);
v_res_2030_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10___redArg(v_depth_boxed_2029_, v_keys_2025_, v_vals_2026_, v_i_2027_, v_entries_2028_);
lean_dec_ref(v_vals_2026_);
lean_dec_ref(v_keys_2025_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg___boxed(lean_object* v_x_2031_, lean_object* v_x_2032_, lean_object* v_x_2033_, lean_object* v_x_2034_, lean_object* v_x_2035_){
_start:
{
size_t v_x_1161__boxed_2036_; size_t v_x_1162__boxed_2037_; lean_object* v_res_2038_; 
v_x_1161__boxed_2036_ = lean_unbox_usize(v_x_2032_);
lean_dec(v_x_2032_);
v_x_1162__boxed_2037_ = lean_unbox_usize(v_x_2033_);
lean_dec(v_x_2033_);
v_res_2038_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg(v_x_2031_, v_x_1161__boxed_2036_, v_x_1162__boxed_2037_, v_x_2034_, v_x_2035_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4___redArg(lean_object* v_x_2039_, lean_object* v_x_2040_, lean_object* v_x_2041_){
_start:
{
uint64_t v___x_2042_; size_t v___x_2043_; size_t v___x_2044_; lean_object* v___x_2045_; 
v___x_2042_ = lean_string_hash(v_x_2040_);
v___x_2043_ = lean_uint64_to_usize(v___x_2042_);
v___x_2044_ = ((size_t)1ULL);
v___x_2045_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg(v_x_2039_, v___x_2043_, v___x_2044_, v_x_2040_, v_x_2041_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_params_2048_){
_start:
{
lean_object* v___x_2049_; 
lean_inc(v_params_2048_);
v___x_2049_ = l_Lean_Lsp_instFromJsonCodeActionParams_fromJson(v_params_2048_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2065_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2052_ = v___x_2049_;
v_isShared_2053_ = v_isSharedCheck_2065_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2049_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2065_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
uint8_t v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2063_; 
v___x_2054_ = 3;
v___x_2055_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__0));
v___x_2056_ = l_Lean_Json_compress(v_params_2048_);
v___x_2057_ = lean_string_append(v___x_2055_, v___x_2056_);
lean_dec_ref(v___x_2056_);
v___x_2058_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__1));
v___x_2059_ = lean_string_append(v___x_2057_, v___x_2058_);
v___x_2060_ = lean_string_append(v___x_2059_, v_a_2050_);
lean_dec(v_a_2050_);
v___x_2061_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
lean_ctor_set_uint8(v___x_2061_, sizeof(void*)*1, v___x_2054_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 0, v___x_2061_);
v___x_2063_ = v___x_2052_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2061_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec(v_params_2048_);
v_a_2066_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2049_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2049_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_params_2074_){
_start:
{
lean_object* v___x_2076_; 
v___x_2076_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0(v_params_2074_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2076_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2076_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
lean_ctor_set_tag(v___x_2079_, 1);
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
v_a_2085_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2076_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2076_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
lean_ctor_set_tag(v___x_2087_, 0);
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_params_2093_, lean_object* v_a_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_2093_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__2(lean_object* v_handler_2096_, lean_object* v___f_2097_, lean_object* v_j_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v___x_2101_; 
v___x_2101_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1___redArg(v_j_2098_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; lean_object* v___x_2103_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref_known(v___x_2101_, 1);
lean_inc_ref(v___y_2099_);
v___x_2103_ = lean_apply_3(v_handler_2096_, v_a_2102_, v___y_2099_, lean_box(0));
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2112_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2106_ = v___x_2103_;
v_isShared_2107_ = v_isSharedCheck_2112_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2103_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2112_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2108_; lean_object* v___x_2110_; 
v___x_2108_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2097_, v_a_2104_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 0, v___x_2108_);
v___x_2110_ = v___x_2106_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2108_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
else
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
lean_dec_ref(v___f_2097_);
v_a_2113_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___x_2103_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2103_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_dec_ref(v___f_2097_);
lean_dec_ref(v_handler_2096_);
v_a_2121_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2101_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2101_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object* v_handler_2129_, lean_object* v___f_2130_, lean_object* v_j_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__2(v_handler_2129_, v___f_2130_, v_j_2131_, v___y_2132_);
lean_dec_ref(v___y_2132_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__0(lean_object* v_j_2135_){
_start:
{
lean_object* v___x_2136_; 
v___x_2136_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0(v_j_2135_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2136_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2136_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2153_; 
v_a_2145_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2147_ = v___x_2136_;
v_isShared_2148_ = v_isSharedCheck_2153_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2136_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2153_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v_textDocument_2149_; lean_object* v___x_2151_; 
v_textDocument_2149_ = lean_ctor_get(v_a_2145_, 2);
lean_inc_ref(v_textDocument_2149_);
lean_dec(v_a_2145_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 0, v_textDocument_2149_);
v___x_2151_ = v___x_2147_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_textDocument_2149_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0(lean_object* v_method_2158_, lean_object* v_handler_2159_, lean_object* v_serialize_x3f_2160_){
_start:
{
lean_object* v___f_2162_; uint8_t v___x_2163_; 
v___f_2162_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__0));
v___x_2163_ = l_Lean_initializing();
if (v___x_2163_ == 0)
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
lean_dec(v_serialize_x3f_2160_);
lean_dec_ref(v_handler_2159_);
v___x_2164_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__1));
v___x_2165_ = lean_string_append(v___x_2164_, v_method_2158_);
lean_dec_ref(v_method_2158_);
v___x_2166_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__2));
v___x_2167_ = lean_string_append(v___x_2165_, v___x_2166_);
v___x_2168_ = lean_mk_io_user_error(v___x_2167_);
v___x_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2168_);
return v___x_2169_;
}
else
{
lean_object* v___x_2170_; lean_object* v___f_2171_; lean_object* v___f_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2170_ = lean_box(v___x_2163_);
v___f_2171_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2171_, 0, v_serialize_x3f_2160_);
lean_closure_set(v___f_2171_, 1, v___x_2170_);
v___f_2172_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_2172_, 0, v_handler_2159_);
lean_closure_set(v___f_2172_, 1, v___f_2171_);
v___x_2173_ = l_Lean_Server_requestHandlers;
v___x_2174_ = lean_st_ref_get(v___x_2173_);
v___x_2175_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_2174_, v_method_2158_);
lean_dec(v___x_2174_);
if (v___x_2175_ == 0)
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2176_ = lean_st_ref_take(v___x_2173_);
v___x_2177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___f_2162_);
lean_ctor_set(v___x_2177_, 1, v___f_2172_);
v___x_2178_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4___redArg(v___x_2176_, v_method_2158_, v___x_2177_);
v___x_2179_ = lean_st_ref_put(v___x_2173_, v___x_2178_);
v___x_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2179_);
return v___x_2180_;
}
else
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
lean_dec_ref(v___f_2172_);
v___x_2181_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__1));
v___x_2182_ = lean_string_append(v___x_2181_, v_method_2158_);
lean_dec_ref(v_method_2158_);
v___x_2183_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__3));
v___x_2184_ = lean_string_append(v___x_2182_, v___x_2183_);
v___x_2185_ = lean_mk_io_user_error(v___x_2184_);
v___x_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2185_);
return v___x_2186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_2187_, lean_object* v_handler_2188_, lean_object* v_serialize_x3f_2189_, lean_object* v_a_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0(v_method_2187_, v_handler_2188_, v_serialize_x3f_2189_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2195_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2_));
v___x_2196_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2_));
v___x_2197_ = lean_box(0);
v___x_2198_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0(v___x_2195_, v___x_2196_, v___x_2197_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2____boxed(lean_object* v_a_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2_();
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_params_2201_, lean_object* v_a_2202_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_2201_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_params_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1(v_params_2205_, v_a_2206_);
lean_dec_ref(v_a_2206_);
return v_res_2208_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3(lean_object* v_00_u03b2_2209_, lean_object* v_x_2210_, lean_object* v_x_2211_){
_start:
{
uint8_t v___x_2212_; 
v___x_2212_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3___redArg(v_x_2210_, v_x_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3___boxed(lean_object* v_00_u03b2_2213_, lean_object* v_x_2214_, lean_object* v_x_2215_){
_start:
{
uint8_t v_res_2216_; lean_object* v_r_2217_; 
v_res_2216_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3(v_00_u03b2_2213_, v_x_2214_, v_x_2215_);
lean_dec_ref(v_x_2215_);
lean_dec_ref(v_x_2214_);
v_r_2217_ = lean_box(v_res_2216_);
return v_r_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4(lean_object* v_00_u03b2_2218_, lean_object* v_x_2219_, lean_object* v_x_2220_, lean_object* v_x_2221_){
_start:
{
lean_object* v___x_2222_; 
v___x_2222_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4___redArg(v_x_2219_, v_x_2220_, v_x_2221_);
return v___x_2222_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_object* v_00_u03b2_2223_, lean_object* v_x_2224_, size_t v_x_2225_, lean_object* v_x_2226_){
_start:
{
uint8_t v___x_2227_; 
v___x_2227_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_2224_, v_x_2225_, v_x_2226_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(lean_object* v_00_u03b2_2228_, lean_object* v_x_2229_, lean_object* v_x_2230_, lean_object* v_x_2231_){
_start:
{
size_t v_x_1623__boxed_2232_; uint8_t v_res_2233_; lean_object* v_r_2234_; 
v_x_1623__boxed_2232_ = lean_unbox_usize(v_x_2230_);
lean_dec(v_x_2230_);
v_res_2233_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5(v_00_u03b2_2228_, v_x_2229_, v_x_1623__boxed_2232_, v_x_2231_);
lean_dec_ref(v_x_2231_);
lean_dec_ref(v_x_2229_);
v_r_2234_ = lean_box(v_res_2233_);
return v_r_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7(lean_object* v_00_u03b2_2235_, lean_object* v_x_2236_, size_t v_x_2237_, size_t v_x_2238_, lean_object* v_x_2239_, lean_object* v_x_2240_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg(v_x_2236_, v_x_2237_, v_x_2238_, v_x_2239_, v_x_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___boxed(lean_object* v_00_u03b2_2242_, lean_object* v_x_2243_, lean_object* v_x_2244_, lean_object* v_x_2245_, lean_object* v_x_2246_, lean_object* v_x_2247_){
_start:
{
size_t v_x_1634__boxed_2248_; size_t v_x_1635__boxed_2249_; lean_object* v_res_2250_; 
v_x_1634__boxed_2248_ = lean_unbox_usize(v_x_2244_);
lean_dec(v_x_2244_);
v_x_1635__boxed_2249_ = lean_unbox_usize(v_x_2245_);
lean_dec(v_x_2245_);
v_res_2250_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7(v_00_u03b2_2242_, v_x_2243_, v_x_1634__boxed_2248_, v_x_1635__boxed_2249_, v_x_2246_, v_x_2247_);
return v_res_2250_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_2251_, lean_object* v_keys_2252_, lean_object* v_vals_2253_, lean_object* v_heq_2254_, lean_object* v_i_2255_, lean_object* v_k_2256_){
_start:
{
uint8_t v___x_2257_; 
v___x_2257_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6___redArg(v_keys_2252_, v_i_2255_, v_k_2256_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6___boxed(lean_object* v_00_u03b2_2258_, lean_object* v_keys_2259_, lean_object* v_vals_2260_, lean_object* v_heq_2261_, lean_object* v_i_2262_, lean_object* v_k_2263_){
_start:
{
uint8_t v_res_2264_; lean_object* v_r_2265_; 
v_res_2264_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6(v_00_u03b2_2258_, v_keys_2259_, v_vals_2260_, v_heq_2261_, v_i_2262_, v_k_2263_);
lean_dec_ref(v_k_2263_);
lean_dec_ref(v_vals_2260_);
lean_dec_ref(v_keys_2259_);
v_r_2265_ = lean_box(v_res_2264_);
return v_r_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9(lean_object* v_00_u03b2_2266_, lean_object* v_n_2267_, lean_object* v_k_2268_, lean_object* v_v_2269_){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9___redArg(v_n_2267_, v_k_2268_, v_v_2269_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10(lean_object* v_00_u03b2_2271_, size_t v_depth_2272_, lean_object* v_keys_2273_, lean_object* v_vals_2274_, lean_object* v_heq_2275_, lean_object* v_i_2276_, lean_object* v_entries_2277_){
_start:
{
lean_object* v___x_2278_; 
v___x_2278_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10___redArg(v_depth_2272_, v_keys_2273_, v_vals_2274_, v_i_2276_, v_entries_2277_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b2_2279_, lean_object* v_depth_2280_, lean_object* v_keys_2281_, lean_object* v_vals_2282_, lean_object* v_heq_2283_, lean_object* v_i_2284_, lean_object* v_entries_2285_){
_start:
{
size_t v_depth_boxed_2286_; lean_object* v_res_2287_; 
v_depth_boxed_2286_ = lean_unbox_usize(v_depth_2280_);
lean_dec(v_depth_2280_);
v_res_2287_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10(v_00_u03b2_2279_, v_depth_boxed_2286_, v_keys_2281_, v_vals_2282_, v_heq_2283_, v_i_2284_, v_entries_2285_);
lean_dec_ref(v_vals_2282_);
lean_dec_ref(v_keys_2281_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9_spec__10(lean_object* v_00_u03b2_2288_, lean_object* v_x_2289_, lean_object* v_x_2290_, lean_object* v_x_2291_, lean_object* v_x_2292_){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9_spec__10___redArg(v_x_2289_, v_x_2290_, v_x_2291_, v_x_2292_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeActionResolve___lam__0(lean_object* v_params_2295_, lean_object* v_providerResultIndex_2296_, lean_object* v_param_2297_, lean_object* v_providerName_2298_, lean_object* v_snap_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v_cap_2303_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2353_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_builtinCodeActionProviders;
v___x_2354_ = lean_st_ref_get(v___x_2353_);
v___x_2355_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2354_, v_providerName_2298_);
lean_dec(v___x_2354_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2356_ = lean_alloc_closure((void*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2___boxed), 5, 1);
lean_closure_set(v___x_2356_, 0, v_providerName_2298_);
lean_inc_ref(v_snap_2299_);
v___x_2357_ = l_Lean_Server_RequestM_runCoreM___redArg(v_snap_2299_, v___x_2356_, v___y_2300_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v_a_2358_; 
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_a_2358_);
lean_dec_ref_known(v___x_2357_, 1);
v_cap_2303_ = v_a_2358_;
goto v___jp_2302_;
}
else
{
lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2366_; 
lean_dec_ref(v_snap_2299_);
lean_dec_ref(v_param_2297_);
lean_dec(v_providerResultIndex_2296_);
lean_dec_ref(v_params_2295_);
v_a_2359_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2361_ = v___x_2357_;
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2357_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2364_; 
if (v_isShared_2362_ == 0)
{
v___x_2364_ = v___x_2361_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2359_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
else
{
lean_object* v_val_2367_; 
lean_dec(v_providerName_2298_);
v_val_2367_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_val_2367_);
lean_dec_ref_known(v___x_2355_, 1);
v_cap_2303_ = v_val_2367_;
goto v___jp_2302_;
}
v___jp_2302_:
{
lean_object* v___x_2304_; 
lean_inc_ref(v___y_2300_);
v___x_2304_ = lean_apply_4(v_cap_2303_, v_params_2295_, v_snap_2299_, v___y_2300_, lean_box(0));
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2344_; 
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2307_ = v___x_2304_;
v_isShared_2308_ = v_isSharedCheck_2344_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2304_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2344_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2309_; uint8_t v___x_2310_; 
v___x_2309_ = lean_array_get_size(v_a_2305_);
v___x_2310_ = lean_nat_dec_lt(v_providerResultIndex_2296_, v___x_2309_);
if (v___x_2310_ == 0)
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2318_; 
lean_dec(v_a_2305_);
lean_dec_ref(v_param_2297_);
v___x_2311_ = ((lean_object*)(l_Lean_Server_handleCodeActionResolve___lam__0___closed__0));
v___x_2312_ = l_Nat_reprFast(v_providerResultIndex_2296_);
v___x_2313_ = lean_string_append(v___x_2311_, v___x_2312_);
lean_dec_ref(v___x_2312_);
v___x_2314_ = ((lean_object*)(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__5));
v___x_2315_ = lean_string_append(v___x_2313_, v___x_2314_);
v___x_2316_ = l_Lean_Server_RequestError_internalError(v___x_2315_);
if (v_isShared_2308_ == 0)
{
lean_ctor_set_tag(v___x_2307_, 1);
lean_ctor_set(v___x_2307_, 0, v___x_2316_);
v___x_2318_ = v___x_2307_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2316_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
else
{
lean_object* v___x_2320_; lean_object* v_lazy_x3f_2321_; 
v___x_2320_ = lean_array_fget(v_a_2305_, v_providerResultIndex_2296_);
lean_dec(v_providerResultIndex_2296_);
lean_dec(v_a_2305_);
v_lazy_x3f_2321_ = lean_ctor_get(v___x_2320_, 1);
lean_inc(v_lazy_x3f_2321_);
lean_dec(v___x_2320_);
if (lean_obj_tag(v_lazy_x3f_2321_) == 1)
{
lean_object* v_val_2322_; lean_object* v___x_2323_; 
lean_del_object(v___x_2307_);
lean_dec_ref(v_param_2297_);
v_val_2322_ = lean_ctor_get(v_lazy_x3f_2321_, 0);
lean_inc(v_val_2322_);
lean_dec_ref_known(v_lazy_x3f_2321_, 1);
v___x_2323_ = lean_apply_1(v_val_2322_, lean_box(0));
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2323_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2323_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2340_; 
v_a_2332_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2334_ = v___x_2323_;
v_isShared_2335_ = v_isSharedCheck_2340_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2323_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2340_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2336_; lean_object* v___x_2338_; 
v___x_2336_ = l_Lean_Server_RequestError_ofIoError(v_a_2332_);
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 0, v___x_2336_);
v___x_2338_ = v___x_2334_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2336_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
else
{
lean_object* v___x_2342_; 
lean_dec(v_lazy_x3f_2321_);
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 0, v_param_2297_);
v___x_2342_ = v___x_2307_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_param_2297_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_dec_ref(v_param_2297_);
lean_dec(v_providerResultIndex_2296_);
v_a_2345_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2304_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2304_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeActionResolve___lam__0___boxed(lean_object* v_params_2368_, lean_object* v_providerResultIndex_2369_, lean_object* v_param_2370_, lean_object* v_providerName_2371_, lean_object* v_snap_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Lean_Server_handleCodeActionResolve___lam__0(v_params_2368_, v_providerResultIndex_2369_, v_param_2370_, v_providerName_2371_, v_snap_2372_, v___y_2373_);
lean_dec_ref(v___y_2373_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeActionResolve___lam__2(lean_object* v___x_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2376_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeActionResolve___lam__2___boxed(lean_object* v___x_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Lean_Server_handleCodeActionResolve___lam__2(v___x_2380_, v___y_2381_);
lean_dec_ref(v___y_2381_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0_spec__0(lean_object* v_params_2384_){
_start:
{
lean_object* v___x_2385_; 
lean_inc(v_params_2384_);
v___x_2385_ = l_Lean_Server_instFromJsonCodeActionResolveData_fromJson(v_params_2384_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2401_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2388_ = v___x_2385_;
v_isShared_2389_ = v_isSharedCheck_2401_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2385_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2401_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
uint8_t v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2399_; 
v___x_2390_ = 3;
v___x_2391_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__0));
v___x_2392_ = l_Lean_Json_compress(v_params_2384_);
v___x_2393_ = lean_string_append(v___x_2391_, v___x_2392_);
lean_dec_ref(v___x_2392_);
v___x_2394_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__1));
v___x_2395_ = lean_string_append(v___x_2393_, v___x_2394_);
v___x_2396_ = lean_string_append(v___x_2395_, v_a_2386_);
lean_dec(v_a_2386_);
v___x_2397_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2397_, 0, v___x_2396_);
lean_ctor_set_uint8(v___x_2397_, sizeof(void*)*1, v___x_2390_);
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 0, v___x_2397_);
v___x_2399_ = v___x_2388_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v___x_2397_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2409_; 
lean_dec(v_params_2384_);
v_a_2402_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2404_ = v___x_2385_;
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2385_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2407_; 
if (v_isShared_2405_ == 0)
{
v___x_2407_ = v___x_2404_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2402_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0___redArg(lean_object* v_params_2410_){
_start:
{
lean_object* v___x_2412_; 
v___x_2412_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0_spec__0(v_params_2410_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2420_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2415_ = v___x_2412_;
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_dec(v___x_2412_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
lean_ctor_set_tag(v___x_2415_, 1);
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2413_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
else
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2428_; 
v_a_2421_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2423_ = v___x_2412_;
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2412_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2426_; 
if (v_isShared_2424_ == 0)
{
lean_ctor_set_tag(v___x_2423_, 0);
v___x_2426_ = v___x_2423_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2421_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0___redArg___boxed(lean_object* v_params_2429_, lean_object* v_a_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0___redArg(v_params_2429_);
return v_res_2431_;
}
}
static lean_object* _init_l_Lean_Server_handleCodeActionResolve___closed__1(void){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = ((lean_object*)(l_Lean_Server_handleCodeActionResolve___closed__0));
v___x_2434_ = l_Lean_Server_RequestError_internalError(v___x_2433_);
return v___x_2434_;
}
}
static lean_object* _init_l_Lean_Server_handleCodeActionResolve___closed__2(void){
_start:
{
lean_object* v___x_2435_; lean_object* v___f_2436_; 
v___x_2435_ = lean_obj_once(&l_Lean_Server_handleCodeActionResolve___closed__1, &l_Lean_Server_handleCodeActionResolve___closed__1_once, _init_l_Lean_Server_handleCodeActionResolve___closed__1);
v___f_2436_ = lean_alloc_closure((void*)(l_Lean_Server_handleCodeActionResolve___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2436_, 0, v___x_2435_);
return v___f_2436_;
}
}
static lean_object* _init_l_Lean_Server_handleCodeActionResolve___closed__4(void){
_start:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2438_ = ((lean_object*)(l_Lean_Server_handleCodeActionResolve___closed__3));
v___x_2439_ = l_Lean_Server_RequestError_invalidParams(v___x_2438_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeActionResolve(lean_object* v_param_2440_, lean_object* v_a_2441_){
_start:
{
lean_object* v___x_2443_; lean_object* v_data_x3f_2444_; 
v___x_2443_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleCodeAction_spec__6(v_a_2441_);
v_data_x3f_2444_ = lean_ctor_get(v_param_2440_, 9);
if (lean_obj_tag(v_data_x3f_2444_) == 1)
{
lean_object* v_a_2445_; lean_object* v_val_2446_; lean_object* v___x_2447_; 
v_a_2445_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_a_2445_);
lean_dec_ref(v___x_2443_);
v_val_2446_ = lean_ctor_get(v_data_x3f_2444_, 0);
lean_inc(v_val_2446_);
v___x_2447_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0___redArg(v_val_2446_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_toEditableDocumentCore_2448_; lean_object* v_meta_2449_; lean_object* v_a_2450_; lean_object* v_params_2451_; lean_object* v_range_2452_; lean_object* v_text_2453_; lean_object* v_providerName_2454_; lean_object* v_providerResultIndex_2455_; lean_object* v_end_2456_; lean_object* v___f_2457_; lean_object* v___x_2458_; lean_object* v___f_2459_; lean_object* v___f_2460_; lean_object* v___x_2461_; 
v_toEditableDocumentCore_2448_ = lean_ctor_get(v_a_2445_, 0);
v_meta_2449_ = lean_ctor_get(v_toEditableDocumentCore_2448_, 0);
v_a_2450_ = lean_ctor_get(v___x_2447_, 0);
lean_inc(v_a_2450_);
lean_dec_ref_known(v___x_2447_, 1);
v_params_2451_ = lean_ctor_get(v_a_2450_, 0);
lean_inc_ref(v_params_2451_);
v_range_2452_ = lean_ctor_get(v_params_2451_, 3);
v_text_2453_ = lean_ctor_get(v_meta_2449_, 3);
v_providerName_2454_ = lean_ctor_get(v_a_2450_, 1);
lean_inc(v_providerName_2454_);
v_providerResultIndex_2455_ = lean_ctor_get(v_a_2450_, 2);
lean_inc(v_providerResultIndex_2455_);
lean_dec(v_a_2450_);
v_end_2456_ = lean_ctor_get(v_range_2452_, 1);
lean_inc_ref(v_end_2456_);
v___f_2457_ = lean_alloc_closure((void*)(l_Lean_Server_handleCodeActionResolve___lam__0___boxed), 7, 4);
lean_closure_set(v___f_2457_, 0, v_params_2451_);
lean_closure_set(v___f_2457_, 1, v_providerResultIndex_2455_);
lean_closure_set(v___f_2457_, 2, v_param_2440_);
lean_closure_set(v___f_2457_, 3, v_providerName_2454_);
v___x_2458_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_2453_, v_end_2456_);
v___f_2459_ = lean_alloc_closure((void*)(l_Lean_Server_handleCodeAction___lam__2___boxed), 2, 1);
lean_closure_set(v___f_2459_, 0, v___x_2458_);
v___f_2460_ = lean_obj_once(&l_Lean_Server_handleCodeActionResolve___closed__2, &l_Lean_Server_handleCodeActionResolve___closed__2_once, _init_l_Lean_Server_handleCodeActionResolve___closed__2);
v___x_2461_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_a_2445_, v___f_2459_, v___f_2460_, v___f_2457_, v_a_2441_);
return v___x_2461_;
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec(v_a_2445_);
lean_dec_ref(v_param_2440_);
v_a_2462_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2447_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2447_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
else
{
lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2477_; 
lean_dec_ref(v_param_2440_);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2477_ == 0)
{
lean_object* v_unused_2478_; 
v_unused_2478_ = lean_ctor_get(v___x_2443_, 0);
lean_dec(v_unused_2478_);
v___x_2471_ = v___x_2443_;
v_isShared_2472_ = v_isSharedCheck_2477_;
goto v_resetjp_2470_;
}
else
{
lean_dec(v___x_2443_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2477_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2473_; lean_object* v___x_2475_; 
v___x_2473_ = lean_obj_once(&l_Lean_Server_handleCodeActionResolve___closed__4, &l_Lean_Server_handleCodeActionResolve___closed__4_once, _init_l_Lean_Server_handleCodeActionResolve___closed__4);
if (v_isShared_2472_ == 0)
{
lean_ctor_set_tag(v___x_2471_, 1);
lean_ctor_set(v___x_2471_, 0, v___x_2473_);
v___x_2475_ = v___x_2471_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2473_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeActionResolve___boxed(lean_object* v_param_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l_Lean_Server_handleCodeActionResolve(v_param_2479_, v_a_2480_);
lean_dec_ref(v_a_2480_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0(lean_object* v_params_2483_, lean_object* v_a_2484_){
_start:
{
lean_object* v___x_2486_; 
v___x_2486_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0___redArg(v_params_2483_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0___boxed(lean_object* v_params_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0(v_params_2487_, v_a_2488_);
lean_dec_ref(v_a_2488_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__1(lean_object* v_serialize_x3f_2491_, uint8_t v_val_2492_, lean_object* v___y_2493_){
_start:
{
if (lean_obj_tag(v___y_2493_) == 0)
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
lean_dec(v_serialize_x3f_2491_);
v_a_2494_ = lean_ctor_get(v___y_2493_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___y_2493_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___y_2493_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___y_2493_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
v___x_2499_ = v___x_2496_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
else
{
if (lean_obj_tag(v_serialize_x3f_2491_) == 1)
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2513_; 
v_a_2502_ = lean_ctor_get(v___y_2493_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___y_2493_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2504_ = v___y_2493_;
v_isShared_2505_ = v_isSharedCheck_2513_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___y_2493_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2513_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v_val_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2511_; 
v_val_2506_ = lean_ctor_get(v_serialize_x3f_2491_, 0);
lean_inc(v_val_2506_);
lean_dec_ref_known(v_serialize_x3f_2491_, 1);
v___x_2507_ = lean_box(0);
v___x_2508_ = lean_apply_1(v_val_2506_, v_a_2502_);
v___x_2509_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2509_, 0, v___x_2507_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
lean_ctor_set_uint8(v___x_2509_, sizeof(void*)*2, v_val_2492_);
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 0, v___x_2509_);
v___x_2511_ = v___x_2504_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2509_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2525_; 
lean_dec(v_serialize_x3f_2491_);
v_a_2514_ = lean_ctor_get(v___y_2493_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___y_2493_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2516_ = v___y_2493_;
v_isShared_2517_ = v_isSharedCheck_2525_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___y_2493_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2525_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2523_; 
v___x_2518_ = l_Lean_Lsp_instToJsonCodeAction_toJson(v_a_2514_);
lean_inc(v___x_2518_);
v___x_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2518_);
v___x_2520_ = l_Lean_Json_compress(v___x_2518_);
v___x_2521_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2521_, 0, v___x_2519_);
lean_ctor_set(v___x_2521_, 1, v___x_2520_);
lean_ctor_set_uint8(v___x_2521_, sizeof(void*)*2, v_val_2492_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 0, v___x_2521_);
v___x_2523_ = v___x_2516_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2521_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object* v_serialize_x3f_2526_, lean_object* v_val_2527_, lean_object* v___y_2528_){
_start:
{
uint8_t v_val_273__boxed_2529_; lean_object* v_res_2530_; 
v_val_273__boxed_2529_ = lean_unbox(v_val_2527_);
v_res_2530_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__1(v_serialize_x3f_2526_, v_val_273__boxed_2529_, v___y_2528_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_params_2531_){
_start:
{
lean_object* v___x_2532_; 
lean_inc(v_params_2531_);
v___x_2532_ = l_Lean_Lsp_instFromJsonCodeAction_fromJson(v_params_2531_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2548_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2535_ = v___x_2532_;
v_isShared_2536_ = v_isSharedCheck_2548_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2532_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2548_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
uint8_t v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2546_; 
v___x_2537_ = 3;
v___x_2538_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__0));
v___x_2539_ = l_Lean_Json_compress(v_params_2531_);
v___x_2540_ = lean_string_append(v___x_2538_, v___x_2539_);
lean_dec_ref(v___x_2539_);
v___x_2541_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__1));
v___x_2542_ = lean_string_append(v___x_2540_, v___x_2541_);
v___x_2543_ = lean_string_append(v___x_2542_, v_a_2533_);
lean_dec(v_a_2533_);
v___x_2544_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2544_, 0, v___x_2543_);
lean_ctor_set_uint8(v___x_2544_, sizeof(void*)*1, v___x_2537_);
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 0, v___x_2544_);
v___x_2546_ = v___x_2535_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v___x_2544_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
lean_dec(v_params_2531_);
v_a_2549_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2532_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2532_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_params_2557_){
_start:
{
lean_object* v___x_2559_; 
v___x_2559_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__0(v_params_2557_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
lean_ctor_set_tag(v___x_2562_, 1);
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2560_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
v_a_2568_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2559_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2559_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
lean_ctor_set_tag(v___x_2570_, 0);
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_params_2576_, lean_object* v_a_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_2576_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__2(lean_object* v_handler_2579_, lean_object* v___f_2580_, lean_object* v_j_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v___x_2584_; 
v___x_2584_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1___redArg(v_j_2581_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; lean_object* v___x_2586_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_a_2585_);
lean_dec_ref_known(v___x_2584_, 1);
lean_inc_ref(v___y_2582_);
v___x_2586_ = lean_apply_3(v_handler_2579_, v_a_2585_, v___y_2582_, lean_box(0));
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2595_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2589_ = v___x_2586_;
v_isShared_2590_ = v_isSharedCheck_2595_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2595_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2591_; lean_object* v___x_2593_; 
v___x_2591_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2580_, v_a_2587_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v___x_2591_);
v___x_2593_ = v___x_2589_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2591_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
else
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
lean_dec_ref(v___f_2580_);
v_a_2596_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2598_ = v___x_2586_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2586_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_dec_ref(v___f_2580_);
lean_dec_ref(v_handler_2579_);
v_a_2604_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2584_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2584_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object* v_handler_2612_, lean_object* v___f_2613_, lean_object* v_j_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__2(v_handler_2612_, v___f_2613_, v_j_2614_, v___y_2615_);
lean_dec_ref(v___y_2615_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__0(lean_object* v_j_2618_){
_start:
{
lean_object* v___x_2619_; 
v___x_2619_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__0(v_j_2618_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2619_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2619_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2636_; 
v_a_2628_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2630_ = v___x_2619_;
v_isShared_2631_ = v_isSharedCheck_2636_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2619_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2636_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2632_; lean_object* v___x_2634_; 
v___x_2632_ = l_Lean_Server_CodeAction_getFileSource_x21(v_a_2628_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 0, v___x_2632_);
v___x_2634_ = v___x_2630_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2632_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0(lean_object* v_method_2638_, lean_object* v_handler_2639_, lean_object* v_serialize_x3f_2640_){
_start:
{
lean_object* v___f_2642_; uint8_t v___x_2643_; 
v___f_2642_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___closed__0));
v___x_2643_ = l_Lean_initializing();
if (v___x_2643_ == 0)
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
lean_dec(v_serialize_x3f_2640_);
lean_dec_ref(v_handler_2639_);
v___x_2644_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__1));
v___x_2645_ = lean_string_append(v___x_2644_, v_method_2638_);
lean_dec_ref(v_method_2638_);
v___x_2646_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__2));
v___x_2647_ = lean_string_append(v___x_2645_, v___x_2646_);
v___x_2648_ = lean_mk_io_user_error(v___x_2647_);
v___x_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2648_);
return v___x_2649_;
}
else
{
lean_object* v___x_2650_; lean_object* v___f_2651_; lean_object* v___f_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; uint8_t v___x_2655_; 
v___x_2650_ = lean_box(v___x_2643_);
v___f_2651_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2651_, 0, v_serialize_x3f_2640_);
lean_closure_set(v___f_2651_, 1, v___x_2650_);
v___f_2652_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_2652_, 0, v_handler_2639_);
lean_closure_set(v___f_2652_, 1, v___f_2651_);
v___x_2653_ = l_Lean_Server_requestHandlers;
v___x_2654_ = lean_st_ref_get(v___x_2653_);
v___x_2655_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_2654_, v_method_2638_);
lean_dec(v___x_2654_);
if (v___x_2655_ == 0)
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2656_ = lean_st_ref_take(v___x_2653_);
v___x_2657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___f_2642_);
lean_ctor_set(v___x_2657_, 1, v___f_2652_);
v___x_2658_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4___redArg(v___x_2656_, v_method_2638_, v___x_2657_);
v___x_2659_ = lean_st_ref_put(v___x_2653_, v___x_2658_);
v___x_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2659_);
return v___x_2660_;
}
else
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
lean_dec_ref(v___f_2652_);
v___x_2661_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__1));
v___x_2662_ = lean_string_append(v___x_2661_, v_method_2638_);
lean_dec_ref(v_method_2638_);
v___x_2663_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__3));
v___x_2664_ = lean_string_append(v___x_2662_, v___x_2663_);
v___x_2665_ = lean_mk_io_user_error(v___x_2664_);
v___x_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2665_);
return v___x_2666_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_2667_, lean_object* v_handler_2668_, lean_object* v_serialize_x3f_2669_, lean_object* v_a_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0(v_method_2667_, v_handler_2668_, v_serialize_x3f_2669_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2675_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2_));
v___x_2676_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2_));
v___x_2677_ = lean_box(0);
v___x_2678_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0(v___x_2675_, v___x_2676_, v___x_2677_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2____boxed(lean_object* v_a_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2_();
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_params_2681_, lean_object* v_a_2682_){
_start:
{
lean_object* v___x_2684_; 
v___x_2684_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_2681_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_params_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1(v_params_2685_, v_a_2686_);
lean_dec_ref(v_a_2686_);
return v_res_2688_;
}
}
lean_object* runtime_initialize_Lean_Server_Requests(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_CodeActions_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Server_Requests(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_2573400817____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_builtinCodeActionProviders = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_builtinCodeActionProviders);
lean_dec_ref(res);
res = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_codeActionProviderExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_codeActionProviderExt);
lean_dec_ref(res);
res = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_CodeActions_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Server_Requests(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_CodeActions_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_Requests(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_CodeActions_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_CodeActions_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_CodeActions_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
