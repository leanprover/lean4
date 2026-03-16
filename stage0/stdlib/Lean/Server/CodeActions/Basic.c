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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_quickLt___boxed(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_initializing();
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
extern lean_object* l_Lean_Server_requestHandlers;
lean_object* lean_st_ref_get(lean_object*);
uint64_t lean_string_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonCodeActionParams_fromJson(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Lsp_instToJsonCodeAction_toJson(lean_object*);
lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonCodeAction_fromJson(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Server_RequestError_internalError(lean_object*);
lean_object* l_Pi_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_indentExpr(lean_object*);
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_has_compile_error(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_instToExprName___private__1(lean_object*);
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
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Server_RequestError_ofIoError(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestError_invalidParams(lean_object*);
extern lean_object* l_Lean_Server_instInhabitedRequestError_default;
lean_object* l_instInhabitedEST___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Lean_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedCodeActionProvider___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedCodeActionProvider___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedCodeActionProvider___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedCodeActionProvider___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Server_instInhabitedCodeActionProvider___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instInhabitedCodeActionProvider___closed__0;
static lean_once_cell_t l_Lean_Server_instInhabitedCodeActionProvider___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instInhabitedCodeActionProvider___closed__1;
static lean_once_cell_t l_Lean_Server_instInhabitedCodeActionProvider___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instInhabitedCodeActionProvider___closed__2;
static lean_once_cell_t l_Lean_Server_instInhabitedCodeActionProvider___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instInhabitedCodeActionProvider___closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedCodeActionProvider;
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_2573400817____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_2573400817____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_builtinCodeActionProviders;
LEAN_EXPORT lean_object* l_Lean_Server_addBuiltinCodeActionProvider(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_addBuiltinCodeActionProvider___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_quickLt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_initFn___lam__1_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_(lean_object*);
static const lean_closure_object l_Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_insert, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Server_initFn___closed__2_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_initFn___lam__1_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_initFn___closed__2_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Server_initFn___closed__2_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Server_initFn___closed__3_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "codeActionProviderExt"};
static const lean_object* l_Lean_Server_initFn___closed__3_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Server_initFn___closed__3_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Server_initFn___closed__4_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_initFn___closed__4_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_initFn___closed__4_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l_Lean_Server_initFn___closed__4_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_initFn___closed__4_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Server_initFn___closed__3_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 40, 10, 229, 67, 12, 129, 142)}};
static const lean_object* l_Lean_Server_initFn___closed__4_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Server_initFn___closed__4_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Server_initFn___closed__5_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_initFn___closed__4_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Server_initFn___closed__2_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Server_initFn___closed__5_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Server_initFn___closed__5_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__5;
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13;
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
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "addBuiltinCodeActionProvider"};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "CodeActionProvider"};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(79, 45, 83, 138, 97, 177, 55, 171)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__4_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "CodeActions"};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__4_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__4_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__5_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__4_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(41, 109, 98, 186, 215, 54, 31, 240)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__5_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__5_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__6_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Basic"};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__6_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__6_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__7_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__5_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__6_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 156, 164, 13, 237, 167, 211, 120)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__7_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__7_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__8_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__7_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(231, 236, 211, 153, 183, 200, 194, 142)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__8_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__8_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__9_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__8_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(218, 170, 13, 173, 36, 216, 196, 218)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__9_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__9_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__10_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__9_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(207, 127, 135, 167, 105, 120, 107, 85)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__10_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__10_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__11_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__11_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__11_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__12_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__10_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__11_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(78, 126, 20, 13, 61, 118, 74, 86)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__12_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__12_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__13_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__13_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__13_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__14_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__12_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__13_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 190, 141, 117, 213, 113, 13, 74)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__14_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__14_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__15_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__14_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(98, 52, 0, 130, 198, 230, 46, 197)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__15_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__15_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__16_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__15_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(71, 157, 19, 223, 35, 0, 13, 34)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__16_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__16_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__17_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__16_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__4_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(209, 137, 0, 217, 239, 233, 195, 40)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__17_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__17_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__18_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__17_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__6_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(54, 243, 113, 54, 127, 25, 120, 16)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__18_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__18_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__19_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__18_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1656927832) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(147, 227, 181, 202, 147, 137, 254, 160)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__19_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__19_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__20_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__20_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__20_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__21_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__19_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__20_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 144, 64, 31, 165, 31, 253, 43)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__21_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__21_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__22_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__22_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__22_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__23_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__21_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__22_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(76, 113, 109, 139, 146, 133, 143, 148)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__23_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__23_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__24_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__23_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(117, 166, 231, 135, 42, 93, 24, 222)}};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__24_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__24_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__25_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 108, .m_capacity = 108, .m_length = 107, .m_data = "Use to decorate methods for suggesting code actions. This is a low-level interface for making code actions."};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__25_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__25_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__26_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "(builtin) "};
static const lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__26_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__26_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(110, 233, 106, 27, 160, 7, 34, 38)}};
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Server_handleCodeAction_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Server_handleCodeAction_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Server_handleCodeAction_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Server_handleCodeAction_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_handleCodeAction_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__1;
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
static const lean_string_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Failed to register LSP request handler for '"};
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__0 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__0_value;
static const lean_string_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "': only possible during initialization"};
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__1 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__1_value;
static const lean_closure_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
lean_dec_ref(v_a_1_);
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
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
lean_dec(v_json_110_);
v_a_123_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_130_ == 0)
{
v___x_125_ = v___x_112_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_112_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
lean_ctor_set_tag(v___x_125_, 0);
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_123_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
else
{
lean_object* v_a_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v_a_131_ = lean_ctor_get(v___x_112_, 0);
lean_inc(v_a_131_);
lean_dec_ref(v___x_112_);
v___x_132_ = ((lean_object*)(l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__1));
lean_inc(v_json_110_);
v___x_133_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__1(v_json_110_, v___x_132_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_143_; 
lean_dec(v_a_131_);
lean_dec(v_json_110_);
v_a_134_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_143_ == 0)
{
v___x_136_ = v___x_133_;
v_isShared_137_ = v_isSharedCheck_143_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_133_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_143_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_141_; 
v___x_138_ = lean_obj_once(&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__15, &l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__15_once, _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__15);
v___x_139_ = lean_string_append(v___x_138_, v_a_134_);
lean_dec(v_a_134_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 0, v___x_139_);
v___x_141_ = v___x_136_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_139_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
else
{
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
lean_dec(v_a_131_);
lean_dec(v_json_110_);
v_a_144_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v___x_133_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_133_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
lean_ctor_set_tag(v___x_146_, 0);
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_a_144_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
else
{
lean_object* v_a_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_a_152_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_a_152_);
lean_dec_ref(v___x_133_);
v___x_153_ = ((lean_object*)(l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__2));
v___x_154_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__2(v_json_110_, v___x_153_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_164_; 
lean_dec(v_a_152_);
lean_dec(v_a_131_);
v_a_155_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_164_ == 0)
{
v___x_157_ = v___x_154_;
v_isShared_158_ = v_isSharedCheck_164_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_154_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_164_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_159_ = lean_obj_once(&l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__19, &l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__19_once, _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__19);
v___x_160_ = lean_string_append(v___x_159_, v_a_155_);
lean_dec(v_a_155_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v___x_160_);
v___x_162_ = v___x_157_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
else
{
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
lean_dec(v_a_152_);
lean_dec(v_a_131_);
v_a_165_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_172_ == 0)
{
v___x_167_ = v___x_154_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_154_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
lean_ctor_set_tag(v___x_167_, 0);
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_165_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
else
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_181_; 
v_a_173_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_181_ == 0)
{
v___x_175_ = v___x_154_;
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_154_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_177_, 0, v_a_131_);
lean_ctor_set(v___x_177_, 1, v_a_152_);
lean_ctor_set(v___x_177_, 2, v_a_173_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v___x_177_);
v___x_179_ = v___x_175_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_CodeAction_getFileSource_x21_spec__0(lean_object* v_msg_185_){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = ((lean_object*)(l_panic___at___00Lean_Server_CodeAction_getFileSource_x21_spec__0___closed__0));
v___x_187_ = lean_panic_fn(v___x_186_, v_msg_185_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CodeAction_getFileSource_x21(lean_object* v_ca_191_){
_start:
{
lean_object* v_a_193_; lean_object* v_data_x3f_200_; 
v_data_x3f_200_ = lean_ctor_get(v_ca_191_, 9);
if (lean_obj_tag(v_data_x3f_200_) == 1)
{
lean_object* v_val_201_; lean_object* v___x_202_; 
lean_inc_ref(v_data_x3f_200_);
lean_dec_ref(v_ca_191_);
v_val_201_ = lean_ctor_get(v_data_x3f_200_, 0);
lean_inc(v_val_201_);
lean_dec_ref(v_data_x3f_200_);
v___x_202_ = l_Lean_Server_instFromJsonCodeActionResolveData_fromJson(v_val_201_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_a_203_);
lean_dec_ref(v___x_202_);
v_a_193_ = v_a_203_;
goto v___jp_192_;
}
else
{
lean_object* v_a_204_; lean_object* v_params_205_; lean_object* v_textDocument_206_; 
v_a_204_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_a_204_);
lean_dec_ref(v___x_202_);
v_params_205_ = lean_ctor_get(v_a_204_, 0);
lean_inc_ref(v_params_205_);
lean_dec(v_a_204_);
v_textDocument_206_ = lean_ctor_get(v_params_205_, 2);
lean_inc_ref(v_textDocument_206_);
lean_dec_ref(v_params_205_);
return v_textDocument_206_;
}
}
else
{
lean_object* v_title_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v_title_207_ = lean_ctor_get(v_ca_191_, 2);
lean_inc_ref(v_title_207_);
lean_dec_ref(v_ca_191_);
v___x_208_ = ((lean_object*)(l_Lean_Server_CodeAction_getFileSource_x21___closed__2));
v___x_209_ = lean_string_append(v___x_208_, v_title_207_);
lean_dec_ref(v_title_207_);
v_a_193_ = v___x_209_;
goto v___jp_192_;
}
v___jp_192_:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_194_ = ((lean_object*)(l_Lean_Server_CodeAction_getFileSource_x21___closed__0));
v___x_195_ = ((lean_object*)(l_Lean_Server_CodeAction_getFileSource_x21___closed__1));
v___x_196_ = lean_unsigned_to_nat(47u);
v___x_197_ = lean_unsigned_to_nat(22u);
v___x_198_ = l_mkPanicMessageWithDecl(v___x_194_, v___x_195_, v___x_196_, v___x_197_, v_a_193_);
lean_dec_ref(v_a_193_);
v___x_199_ = l_panic___at___00Lean_Server_CodeAction_getFileSource_x21_spec__0(v___x_198_);
return v___x_199_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instCoeCodeActionLazyCodeAction___lam__0(lean_object* v_c_212_){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_box(0);
v___x_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_214_, 0, v_c_212_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedCodeActionProvider___lam__0(lean_object* v___f_217_, lean_object* v_a_218_, lean_object* v___y_219_){
_start:
{
lean_object* v___x_23__overap_221_; lean_object* v___x_222_; 
v___x_23__overap_221_ = l_instInhabitedForall___redArg___lam__0(v___f_217_, v___y_219_);
v___x_222_ = lean_apply_1(v___x_23__overap_221_, lean_box(0));
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedCodeActionProvider___lam__0___boxed(lean_object* v___f_223_, lean_object* v_a_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Server_instInhabitedCodeActionProvider___lam__0(v___f_223_, v_a_224_, v___y_225_);
lean_dec_ref(v___y_225_);
lean_dec_ref(v_a_224_);
lean_dec_ref(v___f_223_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedCodeActionProvider___lam__1(lean_object* v___f_228_, lean_object* v_a_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v___x_28__overap_233_; lean_object* v___x_234_; 
v___x_28__overap_233_ = l_Pi_instInhabited___redArg___lam__0(v___f_228_, v___y_230_);
v___x_234_ = lean_apply_2(v___x_28__overap_233_, v___y_231_, lean_box(0));
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedCodeActionProvider___lam__1___boxed(lean_object* v___f_235_, lean_object* v_a_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Server_instInhabitedCodeActionProvider___lam__1(v___f_235_, v_a_236_, v___y_237_, v___y_238_);
lean_dec_ref(v_a_236_);
return v_res_240_;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedCodeActionProvider___closed__0(void){
_start:
{
lean_object* v___x_241_; lean_object* v___f_242_; 
v___x_241_ = l_Lean_Server_instInhabitedRequestError_default;
v___f_242_ = lean_alloc_closure((void*)(l_instInhabitedEST___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_242_, 0, v___x_241_);
return v___f_242_;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedCodeActionProvider___closed__1(void){
_start:
{
lean_object* v___f_243_; lean_object* v___f_244_; 
v___f_243_ = lean_obj_once(&l_Lean_Server_instInhabitedCodeActionProvider___closed__0, &l_Lean_Server_instInhabitedCodeActionProvider___closed__0_once, _init_l_Lean_Server_instInhabitedCodeActionProvider___closed__0);
v___f_244_ = lean_alloc_closure((void*)(l_Lean_Server_instInhabitedCodeActionProvider___lam__0___boxed), 4, 1);
lean_closure_set(v___f_244_, 0, v___f_243_);
return v___f_244_;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedCodeActionProvider___closed__2(void){
_start:
{
lean_object* v___f_245_; lean_object* v___f_246_; 
v___f_245_ = lean_obj_once(&l_Lean_Server_instInhabitedCodeActionProvider___closed__1, &l_Lean_Server_instInhabitedCodeActionProvider___closed__1_once, _init_l_Lean_Server_instInhabitedCodeActionProvider___closed__1);
v___f_246_ = lean_alloc_closure((void*)(l_Lean_Server_instInhabitedCodeActionProvider___lam__1___boxed), 5, 1);
lean_closure_set(v___f_246_, 0, v___f_245_);
return v___f_246_;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedCodeActionProvider___closed__3(void){
_start:
{
lean_object* v___f_247_; lean_object* v___f_248_; 
v___f_247_ = lean_obj_once(&l_Lean_Server_instInhabitedCodeActionProvider___closed__2, &l_Lean_Server_instInhabitedCodeActionProvider___closed__2_once, _init_l_Lean_Server_instInhabitedCodeActionProvider___closed__2);
v___f_248_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_248_, 0, v___f_247_);
return v___f_248_;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedCodeActionProvider(void){
_start:
{
lean_object* v___f_249_; 
v___f_249_ = lean_obj_once(&l_Lean_Server_instInhabitedCodeActionProvider___closed__3, &l_Lean_Server_instInhabitedCodeActionProvider___closed__3_once, _init_l_Lean_Server_instInhabitedCodeActionProvider___closed__3);
return v___f_249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_2573400817____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = lean_box(1);
v___x_252_ = lean_st_mk_ref(v___x_251_);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_2573400817____hygCtx___hyg_2____boxed(lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_2573400817____hygCtx___hyg_2_();
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_addBuiltinCodeActionProvider(lean_object* v_decl_256_, lean_object* v_provider_257_){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_259_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_builtinCodeActionProviders;
v___x_260_ = lean_st_ref_take(v___x_259_);
v___x_261_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_decl_256_, v_provider_257_, v___x_260_);
v___x_262_ = lean_st_ref_set(v___x_259_, v___x_261_);
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_addBuiltinCodeActionProvider___boxed(lean_object* v_decl_264_, lean_object* v_provider_265_, lean_object* v_a_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_Server_addBuiltinCodeActionProvider(v_decl_264_, v_provider_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__0(lean_object* v_as_268_, size_t v_i_269_, size_t v_stop_270_, lean_object* v_b_271_){
_start:
{
uint8_t v___x_272_; 
v___x_272_ = lean_usize_dec_eq(v_i_269_, v_stop_270_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; size_t v___x_275_; size_t v___x_276_; 
v___x_273_ = lean_array_uget_borrowed(v_as_268_, v_i_269_);
lean_inc(v___x_273_);
v___x_274_ = l_Lean_NameSet_insert(v_b_271_, v___x_273_);
v___x_275_ = ((size_t)1ULL);
v___x_276_ = lean_usize_add(v_i_269_, v___x_275_);
v_i_269_ = v___x_276_;
v_b_271_ = v___x_274_;
goto _start;
}
else
{
return v_b_271_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_278_, lean_object* v_i_279_, lean_object* v_stop_280_, lean_object* v_b_281_){
_start:
{
size_t v_i_boxed_282_; size_t v_stop_boxed_283_; lean_object* v_res_284_; 
v_i_boxed_282_ = lean_unbox_usize(v_i_279_);
lean_dec(v_i_279_);
v_stop_boxed_283_ = lean_unbox_usize(v_stop_280_);
lean_dec(v_stop_280_);
v_res_284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__0(v_as_278_, v_i_boxed_282_, v_stop_boxed_283_, v_b_281_);
lean_dec_ref(v_as_278_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__1(lean_object* v_as_285_, size_t v_i_286_, size_t v_stop_287_, lean_object* v_b_288_){
_start:
{
lean_object* v___y_290_; uint8_t v___x_294_; 
v___x_294_ = lean_usize_dec_eq(v_i_286_, v_stop_287_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_295_ = lean_array_uget_borrowed(v_as_285_, v_i_286_);
v___x_296_ = lean_unsigned_to_nat(0u);
v___x_297_ = lean_array_get_size(v___x_295_);
v___x_298_ = lean_nat_dec_lt(v___x_296_, v___x_297_);
if (v___x_298_ == 0)
{
v___y_290_ = v_b_288_;
goto v___jp_289_;
}
else
{
uint8_t v___x_299_; 
v___x_299_ = lean_nat_dec_le(v___x_297_, v___x_297_);
if (v___x_299_ == 0)
{
if (v___x_298_ == 0)
{
v___y_290_ = v_b_288_;
goto v___jp_289_;
}
else
{
size_t v___x_300_; size_t v___x_301_; lean_object* v___x_302_; 
v___x_300_ = ((size_t)0ULL);
v___x_301_ = lean_usize_of_nat(v___x_297_);
v___x_302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__0(v___x_295_, v___x_300_, v___x_301_, v_b_288_);
v___y_290_ = v___x_302_;
goto v___jp_289_;
}
}
else
{
size_t v___x_303_; size_t v___x_304_; lean_object* v___x_305_; 
v___x_303_ = ((size_t)0ULL);
v___x_304_ = lean_usize_of_nat(v___x_297_);
v___x_305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__0(v___x_295_, v___x_303_, v___x_304_, v_b_288_);
v___y_290_ = v___x_305_;
goto v___jp_289_;
}
}
}
else
{
return v_b_288_;
}
v___jp_289_:
{
size_t v___x_291_; size_t v___x_292_; 
v___x_291_ = ((size_t)1ULL);
v___x_292_ = lean_usize_add(v_i_286_, v___x_291_);
v_i_286_ = v___x_292_;
v_b_288_ = v___y_290_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_306_, lean_object* v_i_307_, lean_object* v_stop_308_, lean_object* v_b_309_){
_start:
{
size_t v_i_boxed_310_; size_t v_stop_boxed_311_; lean_object* v_res_312_; 
v_i_boxed_310_ = lean_unbox_usize(v_i_307_);
lean_dec(v_i_307_);
v_stop_boxed_311_ = lean_unbox_usize(v_stop_308_);
lean_dec(v_stop_308_);
v_res_312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__1(v_as_306_, v_i_boxed_310_, v_stop_boxed_311_, v_b_309_);
lean_dec_ref(v_as_306_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_(lean_object* v_nss_313_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_314_ = l_Lean_NameSet_empty;
v___x_315_ = lean_unsigned_to_nat(0u);
v___x_316_ = lean_array_get_size(v_nss_313_);
v___x_317_ = lean_nat_dec_lt(v___x_315_, v___x_316_);
if (v___x_317_ == 0)
{
return v___x_314_;
}
else
{
uint8_t v___x_318_; 
v___x_318_ = lean_nat_dec_le(v___x_316_, v___x_316_);
if (v___x_318_ == 0)
{
if (v___x_317_ == 0)
{
return v___x_314_;
}
else
{
size_t v___x_319_; size_t v___x_320_; lean_object* v___x_321_; 
v___x_319_ = ((size_t)0ULL);
v___x_320_ = lean_usize_of_nat(v___x_316_);
v___x_321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__1(v_nss_313_, v___x_319_, v___x_320_, v___x_314_);
return v___x_321_;
}
}
else
{
size_t v___x_322_; size_t v___x_323_; lean_object* v___x_324_; 
v___x_322_ = ((size_t)0ULL);
v___x_323_ = lean_usize_of_nat(v___x_316_);
v___x_324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__1(v_nss_313_, v___x_322_, v___x_323_, v___x_314_);
return v___x_324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2____boxed(lean_object* v_nss_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_(v_nss_325_);
lean_dec_ref(v_nss_325_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg(lean_object* v_as_328_, lean_object* v_lo_329_, lean_object* v_hi_330_){
_start:
{
uint8_t v___x_331_; 
v___x_331_ = lean_nat_dec_lt(v_lo_329_, v_hi_330_);
if (v___x_331_ == 0)
{
lean_dec(v_lo_329_);
return v_as_328_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v_fst_334_; lean_object* v_snd_335_; uint8_t v___x_336_; 
v___x_332_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg___closed__0));
lean_inc(v_lo_329_);
v___x_333_ = l_Array_qpartition___redArg(v_as_328_, v___x_332_, v_lo_329_, v_hi_330_);
v_fst_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_fst_334_);
v_snd_335_ = lean_ctor_get(v___x_333_, 1);
lean_inc(v_snd_335_);
lean_dec_ref(v___x_333_);
v___x_336_ = lean_nat_dec_le(v_hi_330_, v_fst_334_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg(v_snd_335_, v_lo_329_, v_fst_334_);
v___x_338_ = lean_unsigned_to_nat(1u);
v___x_339_ = lean_nat_add(v_fst_334_, v___x_338_);
lean_dec(v_fst_334_);
v_as_328_ = v___x_337_;
v_lo_329_ = v___x_339_;
goto _start;
}
else
{
lean_dec(v_fst_334_);
lean_dec(v_lo_329_);
return v_snd_335_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_as_341_, lean_object* v_lo_342_, lean_object* v_hi_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg(v_as_341_, v_lo_342_, v_hi_343_);
lean_dec(v_hi_343_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn___lam__1_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_(lean_object* v_es_345_){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_346_ = lean_array_mk(v_es_345_);
v___x_347_ = lean_array_get_size(v___x_346_);
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = lean_nat_dec_eq(v___x_347_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___y_353_; uint8_t v___x_357_; 
v___x_350_ = lean_unsigned_to_nat(1u);
v___x_351_ = lean_nat_sub(v___x_347_, v___x_350_);
v___x_357_ = lean_nat_dec_le(v___x_348_, v___x_351_);
if (v___x_357_ == 0)
{
lean_inc(v___x_351_);
v___y_353_ = v___x_351_;
goto v___jp_352_;
}
else
{
v___y_353_ = v___x_348_;
goto v___jp_352_;
}
v___jp_352_:
{
uint8_t v___x_354_; 
v___x_354_ = lean_nat_dec_le(v___y_353_, v___x_351_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; 
lean_dec(v___x_351_);
lean_inc(v___y_353_);
v___x_355_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg(v___x_346_, v___y_353_, v___y_353_);
lean_dec(v___y_353_);
return v___x_355_;
}
else
{
lean_object* v___x_356_; 
v___x_356_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg(v___x_346_, v___y_353_, v___x_351_);
lean_dec(v___x_351_);
return v___x_356_;
}
}
}
else
{
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = ((lean_object*)(l_Lean_Server_initFn___closed__5_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_));
v___x_375_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2____boxed(lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_();
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2(lean_object* v_n_378_, lean_object* v_as_379_, lean_object* v_lo_380_, lean_object* v_hi_381_, lean_object* v_w_382_, lean_object* v_hlo_383_, lean_object* v_hhi_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg(v_as_379_, v_lo_380_, v_hi_381_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_386_, lean_object* v_as_387_, lean_object* v_lo_388_, lean_object* v_hi_389_, lean_object* v_w_390_, lean_object* v_hlo_391_, lean_object* v_hhi_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2(v_n_386_, v_as_387_, v_lo_388_, v_hi_389_, v_w_390_, v_hlo_391_, v_hhi_392_);
lean_dec(v_hi_389_);
lean_dec(v_n_386_);
return v_res_393_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_394_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__0);
v___x_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
return v___x_396_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg(lean_object* v_env_399_, lean_object* v___y_400_){
_start:
{
lean_object* v___x_402_; lean_object* v_nextMacroScope_403_; lean_object* v_ngen_404_; lean_object* v_auxDeclNGen_405_; lean_object* v_traceState_406_; lean_object* v_messages_407_; lean_object* v_infoState_408_; lean_object* v_snapshotTasks_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_420_; 
v___x_402_ = lean_st_ref_take(v___y_400_);
v_nextMacroScope_403_ = lean_ctor_get(v___x_402_, 1);
v_ngen_404_ = lean_ctor_get(v___x_402_, 2);
v_auxDeclNGen_405_ = lean_ctor_get(v___x_402_, 3);
v_traceState_406_ = lean_ctor_get(v___x_402_, 4);
v_messages_407_ = lean_ctor_get(v___x_402_, 6);
v_infoState_408_ = lean_ctor_get(v___x_402_, 7);
v_snapshotTasks_409_ = lean_ctor_get(v___x_402_, 8);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_420_ == 0)
{
lean_object* v_unused_421_; lean_object* v_unused_422_; 
v_unused_421_ = lean_ctor_get(v___x_402_, 5);
lean_dec(v_unused_421_);
v_unused_422_ = lean_ctor_get(v___x_402_, 0);
lean_dec(v_unused_422_);
v___x_411_ = v___x_402_;
v_isShared_412_ = v_isSharedCheck_420_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_snapshotTasks_409_);
lean_inc(v_infoState_408_);
lean_inc(v_messages_407_);
lean_inc(v_traceState_406_);
lean_inc(v_auxDeclNGen_405_);
lean_inc(v_ngen_404_);
lean_inc(v_nextMacroScope_403_);
lean_dec(v___x_402_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_420_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_413_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__2);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 5, v___x_413_);
lean_ctor_set(v___x_411_, 0, v_env_399_);
v___x_415_ = v___x_411_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_env_399_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_nextMacroScope_403_);
lean_ctor_set(v_reuseFailAlloc_419_, 2, v_ngen_404_);
lean_ctor_set(v_reuseFailAlloc_419_, 3, v_auxDeclNGen_405_);
lean_ctor_set(v_reuseFailAlloc_419_, 4, v_traceState_406_);
lean_ctor_set(v_reuseFailAlloc_419_, 5, v___x_413_);
lean_ctor_set(v_reuseFailAlloc_419_, 6, v_messages_407_);
lean_ctor_set(v_reuseFailAlloc_419_, 7, v_infoState_408_);
lean_ctor_set(v_reuseFailAlloc_419_, 8, v_snapshotTasks_409_);
v___x_415_ = v_reuseFailAlloc_419_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_416_ = lean_st_ref_set(v___y_400_, v___x_415_);
v___x_417_ = lean_box(0);
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
return v___x_418_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_env_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg(v_env_423_, v___y_424_);
lean_dec(v___y_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1(lean_object* v_env_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg(v_env_427_, v___y_429_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1(v_env_432_, v___y_433_, v___y_434_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
return v_res_436_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_437_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
return v___x_439_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_440_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
lean_ctor_set(v___x_442_, 2, v___x_441_);
lean_ctor_set(v___x_442_, 3, v___x_440_);
lean_ctor_set(v___x_442_, 4, v___x_440_);
lean_ctor_set(v___x_442_, 5, v___x_440_);
lean_ctor_set(v___x_442_, 6, v___x_440_);
lean_ctor_set(v___x_442_, 7, v___x_440_);
lean_ctor_set(v___x_442_, 8, v___x_440_);
return v___x_442_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = lean_unsigned_to_nat(32u);
v___x_444_ = lean_mk_empty_array_with_capacity(v___x_443_);
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
return v___x_445_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_446_ = ((size_t)5ULL);
v___x_447_ = lean_unsigned_to_nat(0u);
v___x_448_ = lean_unsigned_to_nat(32u);
v___x_449_ = lean_mk_empty_array_with_capacity(v___x_448_);
v___x_450_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_451_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_451_, 0, v___x_450_);
lean_ctor_set(v___x_451_, 1, v___x_449_);
lean_ctor_set(v___x_451_, 2, v___x_447_);
lean_ctor_set(v___x_451_, 3, v___x_447_);
lean_ctor_set_usize(v___x_451_, 4, v___x_446_);
return v___x_451_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_452_ = lean_box(1);
v___x_453_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_454_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_455_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
lean_ctor_set(v___x_455_, 1, v___x_453_);
lean_ctor_set(v___x_455_, 2, v___x_452_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v___x_460_; lean_object* v_env_461_; lean_object* v_options_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_460_ = lean_st_ref_get(v___y_458_);
v_env_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc_ref(v_env_461_);
lean_dec(v___x_460_);
v_options_462_ = lean_ctor_get(v___y_457_, 2);
v___x_463_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_464_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_462_);
v___x_465_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_465_, 0, v_env_461_);
lean_ctor_set(v___x_465_, 1, v___x_463_);
lean_ctor_set(v___x_465_, 2, v___x_464_);
lean_ctor_set(v___x_465_, 3, v_options_462_);
v___x_466_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
lean_ctor_set(v___x_466_, 1, v_msgData_456_);
v___x_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0(v_msgData_468_, v___y_469_, v___y_470_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_ref_477_; lean_object* v___x_478_; lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_487_; 
v_ref_477_ = lean_ctor_get(v___y_474_, 5);
v___x_478_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0(v_msg_473_, v___y_474_, v___y_475_);
v_a_479_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_487_ == 0)
{
v___x_481_ = v___x_478_;
v_isShared_482_ = v_isSharedCheck_487_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_478_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_487_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_485_; 
lean_inc(v_ref_477_);
v___x_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_483_, 0, v_ref_477_);
lean_ctor_set(v___x_483_, 1, v_a_479_);
if (v_isShared_482_ == 0)
{
lean_ctor_set_tag(v___x_481_, 1);
lean_ctor_set(v___x_481_, 0, v___x_483_);
v___x_485_ = v___x_481_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___redArg(v_msg_488_, v___y_489_, v___y_490_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
return v_res_492_;
}
}
static lean_object* _init_l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_));
v___x_495_ = l_Lean_stringToMessageData(v___x_494_);
return v___x_495_;
}
}
static lean_object* _init_l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_));
v___x_498_ = l_Lean_stringToMessageData(v___x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(lean_object* v_name_499_, lean_object* v_decl_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_504_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_, &l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__once, _init_l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_);
v___x_505_ = l_Lean_MessageData_ofName(v_name_499_);
v___x_506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_504_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
v___x_507_ = lean_obj_once(&l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_, &l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__once, _init_l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_);
v___x_508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_506_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v___x_509_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___redArg(v___x_508_, v___y_501_, v___y_502_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2____boxed(lean_object* v_name_510_, lean_object* v_decl_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(v_name_510_, v_decl_511_, v___y_512_, v___y_513_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v_decl_511_);
return v_res_515_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__0));
v___x_518_ = l_Lean_stringToMessageData(v___x_517_);
return v___x_518_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__2));
v___x_521_ = l_Lean_stringToMessageData(v___x_520_);
return v___x_521_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__4));
v___x_524_ = l_Lean_stringToMessageData(v___x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg(lean_object* v_name_528_, uint8_t v_kind_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___y_539_; 
v___x_533_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__1);
v___x_534_ = l_Lean_MessageData_ofName(v_name_528_);
v___x_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__3);
v___x_537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
switch(v_kind_529_)
{
case 0:
{
lean_object* v___x_546_; 
v___x_546_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__6));
v___y_539_ = v___x_546_;
goto v___jp_538_;
}
case 1:
{
lean_object* v___x_547_; 
v___x_547_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__7));
v___y_539_ = v___x_547_;
goto v___jp_538_;
}
default: 
{
lean_object* v___x_548_; 
v___x_548_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__8));
v___y_539_ = v___x_548_;
goto v___jp_538_;
}
}
v___jp_538_:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_540_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_540_, 0, v___y_539_);
v___x_541_ = l_Lean_MessageData_ofFormat(v___x_540_);
v___x_542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_537_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
v___x_543_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__5);
v___x_544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_542_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
v___x_545_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___redArg(v___x_544_, v___y_530_, v___y_531_);
return v___x_545_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object* v_name_549_, lean_object* v_kind_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
uint8_t v_kind_boxed_554_; lean_object* v_res_555_; 
v_kind_boxed_554_ = lean_unbox(v_kind_550_);
v_res_555_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg(v_name_549_, v_kind_boxed_554_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
return v_res_555_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__0));
v___x_558_ = l_Lean_stringToMessageData(v___x_557_);
return v___x_558_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__2));
v___x_561_ = l_Lean_stringToMessageData(v___x_560_);
return v___x_561_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__4));
v___x_564_ = l_Lean_stringToMessageData(v___x_563_);
return v___x_564_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__6));
v___x_567_ = l_Lean_stringToMessageData(v___x_566_);
return v___x_567_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__9(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__8));
v___x_570_ = l_Lean_stringToMessageData(v___x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg(lean_object* v_attrName_571_, lean_object* v_declName_572_, lean_object* v_givenType_573_, lean_object* v_expectedType_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_578_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__1);
v___x_579_ = l_Lean_MessageData_ofName(v_attrName_571_);
lean_inc_ref(v___x_579_);
v___x_580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_578_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
v___x_581_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__3);
v___x_582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_580_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = 0;
v___x_584_ = l_Lean_MessageData_ofConstName(v_declName_572_, v___x_583_);
v___x_585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_582_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__5);
v___x_587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_585_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = l_Lean_indentExpr(v_givenType_573_);
v___x_589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_587_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
v___x_590_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__7);
v___x_591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_589_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
lean_ctor_set(v___x_592_, 1, v___x_579_);
v___x_593_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__9, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__9_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__9);
v___x_594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_592_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = l_Lean_indentExpr(v_expectedType_574_);
v___x_596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_594_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___redArg(v___x_596_, v___y_575_, v___y_576_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___boxed(lean_object* v_attrName_598_, lean_object* v_declName_599_, lean_object* v_givenType_600_, lean_object* v_expectedType_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg(v_attrName_598_, v_declName_599_, v_givenType_600_, v_expectedType_601_, v___y_602_, v___y_603_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(lean_object* v_ref_606_, lean_object* v_msg_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v_fileName_611_; lean_object* v_fileMap_612_; lean_object* v_options_613_; lean_object* v_currRecDepth_614_; lean_object* v_maxRecDepth_615_; lean_object* v_ref_616_; lean_object* v_currNamespace_617_; lean_object* v_openDecls_618_; lean_object* v_initHeartbeats_619_; lean_object* v_maxHeartbeats_620_; lean_object* v_quotContext_621_; lean_object* v_currMacroScope_622_; uint8_t v_diag_623_; lean_object* v_cancelTk_x3f_624_; uint8_t v_suppressElabErrors_625_; lean_object* v_inheritedTraceOptions_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_635_; 
v_fileName_611_ = lean_ctor_get(v___y_608_, 0);
v_fileMap_612_ = lean_ctor_get(v___y_608_, 1);
v_options_613_ = lean_ctor_get(v___y_608_, 2);
v_currRecDepth_614_ = lean_ctor_get(v___y_608_, 3);
v_maxRecDepth_615_ = lean_ctor_get(v___y_608_, 4);
v_ref_616_ = lean_ctor_get(v___y_608_, 5);
v_currNamespace_617_ = lean_ctor_get(v___y_608_, 6);
v_openDecls_618_ = lean_ctor_get(v___y_608_, 7);
v_initHeartbeats_619_ = lean_ctor_get(v___y_608_, 8);
v_maxHeartbeats_620_ = lean_ctor_get(v___y_608_, 9);
v_quotContext_621_ = lean_ctor_get(v___y_608_, 10);
v_currMacroScope_622_ = lean_ctor_get(v___y_608_, 11);
v_diag_623_ = lean_ctor_get_uint8(v___y_608_, sizeof(void*)*14);
v_cancelTk_x3f_624_ = lean_ctor_get(v___y_608_, 12);
v_suppressElabErrors_625_ = lean_ctor_get_uint8(v___y_608_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_626_ = lean_ctor_get(v___y_608_, 13);
v_isSharedCheck_635_ = !lean_is_exclusive(v___y_608_);
if (v_isSharedCheck_635_ == 0)
{
v___x_628_ = v___y_608_;
v_isShared_629_ = v_isSharedCheck_635_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_inheritedTraceOptions_626_);
lean_inc(v_cancelTk_x3f_624_);
lean_inc(v_currMacroScope_622_);
lean_inc(v_quotContext_621_);
lean_inc(v_maxHeartbeats_620_);
lean_inc(v_initHeartbeats_619_);
lean_inc(v_openDecls_618_);
lean_inc(v_currNamespace_617_);
lean_inc(v_ref_616_);
lean_inc(v_maxRecDepth_615_);
lean_inc(v_currRecDepth_614_);
lean_inc(v_options_613_);
lean_inc(v_fileMap_612_);
lean_inc(v_fileName_611_);
lean_dec(v___y_608_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_635_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v_ref_630_; lean_object* v___x_632_; 
v_ref_630_ = l_Lean_replaceRef(v_ref_606_, v_ref_616_);
lean_dec(v_ref_616_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 5, v_ref_630_);
v___x_632_ = v___x_628_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_fileName_611_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_fileMap_612_);
lean_ctor_set(v_reuseFailAlloc_634_, 2, v_options_613_);
lean_ctor_set(v_reuseFailAlloc_634_, 3, v_currRecDepth_614_);
lean_ctor_set(v_reuseFailAlloc_634_, 4, v_maxRecDepth_615_);
lean_ctor_set(v_reuseFailAlloc_634_, 5, v_ref_630_);
lean_ctor_set(v_reuseFailAlloc_634_, 6, v_currNamespace_617_);
lean_ctor_set(v_reuseFailAlloc_634_, 7, v_openDecls_618_);
lean_ctor_set(v_reuseFailAlloc_634_, 8, v_initHeartbeats_619_);
lean_ctor_set(v_reuseFailAlloc_634_, 9, v_maxHeartbeats_620_);
lean_ctor_set(v_reuseFailAlloc_634_, 10, v_quotContext_621_);
lean_ctor_set(v_reuseFailAlloc_634_, 11, v_currMacroScope_622_);
lean_ctor_set(v_reuseFailAlloc_634_, 12, v_cancelTk_x3f_624_);
lean_ctor_set(v_reuseFailAlloc_634_, 13, v_inheritedTraceOptions_626_);
lean_ctor_set_uint8(v_reuseFailAlloc_634_, sizeof(void*)*14, v_diag_623_);
lean_ctor_set_uint8(v_reuseFailAlloc_634_, sizeof(void*)*14 + 1, v_suppressElabErrors_625_);
v___x_632_ = v_reuseFailAlloc_634_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_633_; 
v___x_633_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___redArg(v_msg_607_, v___x_632_, v___y_609_);
lean_dec_ref(v___x_632_);
return v___x_633_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg___boxed(lean_object* v_ref_636_, lean_object* v_msg_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_636_, v_msg_637_, v___y_638_, v___y_639_);
lean_dec(v___y_639_);
lean_dec(v_ref_636_);
return v_res_641_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0));
v___x_644_ = l_Lean_stringToMessageData(v___x_643_);
return v___x_644_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2));
v___x_647_ = l_Lean_stringToMessageData(v___x_646_);
return v___x_647_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4));
v___x_650_ = l_Lean_stringToMessageData(v___x_649_);
return v___x_650_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_653_ = l_Lean_stringToMessageData(v___x_652_);
return v___x_653_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_656_ = l_Lean_stringToMessageData(v___x_655_);
return v___x_656_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_659_ = l_Lean_stringToMessageData(v___x_658_);
return v___x_659_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_662_ = l_Lean_stringToMessageData(v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_663_, lean_object* v_declHint_664_, lean_object* v___y_665_){
_start:
{
lean_object* v___x_667_; lean_object* v_env_668_; uint8_t v___x_669_; 
v___x_667_ = lean_st_ref_get(v___y_665_);
v_env_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc_ref(v_env_668_);
lean_dec(v___x_667_);
v___x_669_ = l_Lean_Name_isAnonymous(v_declHint_664_);
if (v___x_669_ == 0)
{
uint8_t v_isExporting_670_; 
v_isExporting_670_ = lean_ctor_get_uint8(v_env_668_, sizeof(void*)*8);
if (v_isExporting_670_ == 0)
{
lean_object* v___x_671_; 
lean_dec_ref(v_env_668_);
lean_dec(v_declHint_664_);
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v_msg_663_);
return v___x_671_;
}
else
{
lean_object* v___x_672_; uint8_t v___x_673_; 
lean_inc_ref(v_env_668_);
v___x_672_ = l_Lean_Environment_setExporting(v_env_668_, v___x_669_);
lean_inc(v_declHint_664_);
lean_inc_ref(v___x_672_);
v___x_673_ = l_Lean_Environment_contains(v___x_672_, v_declHint_664_, v_isExporting_670_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; 
lean_dec_ref(v___x_672_);
lean_dec_ref(v_env_668_);
lean_dec(v_declHint_664_);
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v_msg_663_);
return v___x_674_;
}
else
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v_c_680_; lean_object* v___x_681_; 
v___x_675_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_676_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__5);
v___x_677_ = l_Lean_Options_empty;
v___x_678_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_678_, 0, v___x_672_);
lean_ctor_set(v___x_678_, 1, v___x_675_);
lean_ctor_set(v___x_678_, 2, v___x_676_);
lean_ctor_set(v___x_678_, 3, v___x_677_);
lean_inc(v_declHint_664_);
v___x_679_ = l_Lean_MessageData_ofConstName(v_declHint_664_, v___x_669_);
v_c_680_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_680_, 0, v___x_678_);
lean_ctor_set(v_c_680_, 1, v___x_679_);
v___x_681_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_668_, v_declHint_664_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
lean_dec_ref(v_env_668_);
lean_dec(v_declHint_664_);
v___x_682_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
lean_ctor_set(v___x_683_, 1, v_c_680_);
v___x_684_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_683_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = l_Lean_MessageData_note(v___x_685_);
v___x_687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_687_, 0, v_msg_663_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
return v___x_688_;
}
else
{
lean_object* v_val_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_724_; 
v_val_689_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_724_ == 0)
{
v___x_691_ = v___x_681_;
v_isShared_692_ = v_isSharedCheck_724_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_val_689_);
lean_dec(v___x_681_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_724_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v_mod_696_; uint8_t v___x_697_; 
v___x_693_ = lean_box(0);
v___x_694_ = l_Lean_Environment_header(v_env_668_);
lean_dec_ref(v_env_668_);
v___x_695_ = l_Lean_EnvironmentHeader_moduleNames(v___x_694_);
v_mod_696_ = lean_array_get(v___x_693_, v___x_695_, v_val_689_);
lean_dec(v_val_689_);
lean_dec_ref(v___x_695_);
v___x_697_ = l_Lean_isPrivateName(v_declHint_664_);
lean_dec(v_declHint_664_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_698_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
lean_ctor_set(v___x_699_, 1, v_c_680_);
v___x_700_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_699_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = l_Lean_MessageData_ofName(v_mod_696_);
v___x_703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_701_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_703_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
v___x_706_ = l_Lean_MessageData_note(v___x_705_);
v___x_707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_707_, 0, v_msg_663_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
if (v_isShared_692_ == 0)
{
lean_ctor_set_tag(v___x_691_, 0);
lean_ctor_set(v___x_691_, 0, v___x_707_);
v___x_709_ = v___x_691_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
else
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_711_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
lean_ctor_set(v___x_712_, 1, v_c_680_);
v___x_713_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_712_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v___x_715_ = l_Lean_MessageData_ofName(v_mod_696_);
v___x_716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_714_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_716_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = l_Lean_MessageData_note(v___x_718_);
v___x_720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_720_, 0, v_msg_663_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
if (v_isShared_692_ == 0)
{
lean_ctor_set_tag(v___x_691_, 0);
lean_ctor_set(v___x_691_, 0, v___x_720_);
v___x_722_ = v___x_691_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_725_; 
lean_dec_ref(v_env_668_);
lean_dec(v_declHint_664_);
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v_msg_663_);
return v___x_725_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_726_, lean_object* v_declHint_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_726_, v_declHint_727_, v___y_728_);
lean_dec(v___y_728_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(lean_object* v_msg_731_, lean_object* v_declHint_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v___x_736_; lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_746_; 
v___x_736_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_731_, v_declHint_732_, v___y_734_);
v_a_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_746_ == 0)
{
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_746_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_746_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_741_ = l_Lean_unknownIdentifierMessageTag;
v___x_742_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
lean_ctor_set(v___x_742_, 1, v_a_737_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_742_);
v___x_744_ = v___x_739_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_742_);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8___boxed(lean_object* v_msg_747_, lean_object* v_declHint_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(v_msg_747_, v_declHint_748_, v___y_749_, v___y_750_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(lean_object* v_ref_753_, lean_object* v_msg_754_, lean_object* v_declHint_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v___x_759_; lean_object* v_a_760_; lean_object* v___x_761_; 
v___x_759_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(v_msg_754_, v_declHint_755_, v___y_756_, v___y_757_);
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
lean_dec_ref(v___x_759_);
v___x_761_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_753_, v_a_760_, v___y_756_, v___y_757_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_ref_762_, lean_object* v_msg_763_, lean_object* v_declHint_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(v_ref_762_, v_msg_763_, v_declHint_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec(v_ref_762_);
return v_res_768_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__0));
v___x_771_ = l_Lean_stringToMessageData(v___x_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(lean_object* v_ref_772_, lean_object* v_constName_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v___x_777_; uint8_t v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_777_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1);
v___x_778_ = 0;
lean_inc(v_constName_773_);
v___x_779_ = l_Lean_MessageData_ofConstName(v_constName_773_, v___x_778_);
v___x_780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_777_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__5);
v___x_782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_780_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(v_ref_772_, v___x_782_, v_constName_773_, v___y_774_, v___y_775_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_ref_784_, lean_object* v_constName_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(v_ref_784_, v_constName_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec(v_ref_784_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_constName_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v_ref_794_; lean_object* v___x_795_; 
v_ref_794_ = lean_ctor_get(v___y_791_, 5);
lean_inc(v_ref_794_);
v___x_795_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(v_ref_794_, v_constName_790_, v___y_791_, v___y_792_);
lean_dec(v_ref_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_constName_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_796_, v___y_797_, v___y_798_);
lean_dec(v___y_798_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2(lean_object* v_constName_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v___x_805_; lean_object* v_env_806_; uint8_t v___x_807_; lean_object* v___x_808_; 
v___x_805_ = lean_st_ref_get(v___y_803_);
v_env_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc_ref(v_env_806_);
lean_dec(v___x_805_);
v___x_807_ = 0;
lean_inc(v_constName_801_);
v___x_808_ = l_Lean_Environment_find_x3f(v_env_806_, v_constName_801_, v___x_807_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_801_, v___y_802_, v___y_803_);
return v___x_809_;
}
else
{
lean_object* v_val_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec_ref(v___y_802_);
lean_dec(v_constName_801_);
v_val_810_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_808_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_val_810_);
lean_dec(v___x_808_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
lean_ctor_set_tag(v___x_812_, 0);
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_val_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2___boxed(lean_object* v_constName_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2(v_constName_818_, v___y_819_, v___y_820_);
lean_dec(v___y_820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(uint8_t v_builtin_828_, lean_object* v___x_829_, lean_object* v___x_830_, lean_object* v___x_831_, lean_object* v_name_832_, lean_object* v_decl_833_, lean_object* v_stx_834_, uint8_t v_kind_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_858_; lean_object* v___y_859_; 
if (v_builtin_828_ == 0)
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_));
lean_inc(v___y_837_);
lean_inc_ref(v___y_836_);
lean_inc(v_decl_833_);
v___x_883_ = l_Lean_ensureAttrDeclIsMeta(v___x_882_, v_decl_833_, v_kind_835_, v___y_836_, v___y_837_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_dec_ref(v___x_883_);
goto v___jp_877_;
}
else
{
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v_stx_834_);
lean_dec(v_decl_833_);
lean_dec(v_name_832_);
lean_dec_ref(v___x_831_);
lean_dec_ref(v___x_830_);
lean_dec(v___x_829_);
return v___x_883_;
}
}
else
{
goto v___jp_877_;
}
v___jp_839_:
{
lean_object* v___x_842_; 
v___x_842_ = lean_st_ref_get(v___y_841_);
if (v_builtin_828_ == 0)
{
lean_object* v_env_843_; lean_object* v___x_844_; lean_object* v_toEnvExtension_845_; lean_object* v_asyncMode_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
lean_dec_ref(v___y_840_);
lean_dec_ref(v___x_831_);
lean_dec_ref(v___x_830_);
v_env_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc_ref(v_env_843_);
lean_dec(v___x_842_);
v___x_844_ = l_Lean_Server_codeActionProviderExt;
v_toEnvExtension_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc_ref(v_toEnvExtension_845_);
v_asyncMode_846_ = lean_ctor_get(v_toEnvExtension_845_, 2);
lean_inc(v_asyncMode_846_);
lean_dec_ref(v_toEnvExtension_845_);
v___x_847_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_844_, v_env_843_, v_decl_833_, v_asyncMode_846_, v___x_829_);
lean_dec(v_asyncMode_846_);
v___x_848_ = l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg(v___x_847_, v___y_841_);
lean_dec(v___y_841_);
return v___x_848_;
}
else
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
lean_dec(v___x_842_);
lean_dec(v___x_829_);
v___x_849_ = lean_box(0);
lean_inc(v_decl_833_);
v___x_850_ = l_Lean_mkConst(v_decl_833_, v___x_849_);
v___x_851_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_));
v___x_852_ = l_Lean_Name_mkStr3(v___x_830_, v___x_831_, v___x_851_);
v___x_853_ = l_Lean_mkConst(v___x_852_, v___x_849_);
lean_inc(v_decl_833_);
v___x_854_ = l_Lean_instToExprName___private__1(v_decl_833_);
v___x_855_ = l_Lean_mkAppB(v___x_853_, v___x_854_, v___x_850_);
v___x_856_ = l_Lean_declareBuiltin(v_decl_833_, v___x_855_, v___y_840_, v___y_841_);
return v___x_856_;
}
}
v___jp_857_:
{
lean_object* v___x_860_; 
lean_inc_ref(v___y_858_);
lean_inc(v_decl_833_);
v___x_860_ = l_Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2(v_decl_833_, v___y_858_, v___y_859_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; uint8_t v___x_865_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
lean_dec_ref(v___x_860_);
v___x_862_ = l_Lean_ConstantInfo_type(v_a_861_);
lean_dec(v_a_861_);
v___x_863_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_864_ = l_Lean_Name_mkStr3(v___x_830_, v___x_831_, v___x_863_);
v___x_865_ = l_Lean_Expr_isConstOf(v___x_862_, v___x_864_);
if (v___x_865_ == 0)
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
lean_dec_ref(v___x_831_);
lean_dec_ref(v___x_830_);
lean_dec(v___x_829_);
v___x_866_ = lean_box(0);
v___x_867_ = l_Lean_mkConst(v___x_864_, v___x_866_);
v___x_868_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg(v_name_832_, v_decl_833_, v___x_862_, v___x_867_, v___y_858_, v___y_859_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
return v___x_868_;
}
else
{
lean_dec(v___x_864_);
lean_dec_ref(v___x_862_);
lean_dec(v_name_832_);
v___y_840_ = v___y_858_;
v___y_841_ = v___y_859_;
goto v___jp_839_;
}
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v_decl_833_);
lean_dec(v_name_832_);
lean_dec_ref(v___x_831_);
lean_dec_ref(v___x_830_);
lean_dec(v___x_829_);
v_a_869_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_860_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_860_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
v___jp_877_:
{
lean_object* v___x_878_; 
lean_inc_ref(v___y_836_);
v___x_878_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_834_, v___y_836_, v___y_837_);
if (lean_obj_tag(v___x_878_) == 0)
{
uint8_t v___x_879_; uint8_t v___x_880_; 
lean_dec_ref(v___x_878_);
v___x_879_ = 0;
v___x_880_ = l_Lean_instBEqAttributeKind_beq(v_kind_835_, v___x_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; 
lean_dec(v_decl_833_);
lean_dec_ref(v___x_831_);
lean_dec_ref(v___x_830_);
lean_dec(v___x_829_);
v___x_881_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg(v_name_832_, v_kind_835_, v___y_836_, v___y_837_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
return v___x_881_;
}
else
{
v___y_858_ = v___y_836_;
v___y_859_ = v___y_837_;
goto v___jp_857_;
}
}
else
{
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v_decl_833_);
lean_dec(v_name_832_);
lean_dec_ref(v___x_831_);
lean_dec_ref(v___x_830_);
lean_dec(v___x_829_);
return v___x_878_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2____boxed(lean_object* v_builtin_884_, lean_object* v___x_885_, lean_object* v___x_886_, lean_object* v___x_887_, lean_object* v_name_888_, lean_object* v_decl_889_, lean_object* v_stx_890_, lean_object* v_kind_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
uint8_t v_builtin_boxed_895_; uint8_t v_kind_boxed_896_; lean_object* v_res_897_; 
v_builtin_boxed_895_ = lean_unbox(v_builtin_884_);
v_kind_boxed_896_ = lean_unbox(v_kind_891_);
v_res_897_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(v_builtin_boxed_895_, v___x_885_, v___x_886_, v___x_887_, v_name_888_, v_decl_889_, v_stx_890_, v_kind_boxed_896_, v___y_892_, v___y_893_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(uint8_t v_builtin_961_, lean_object* v_name_962_){
_start:
{
lean_object* v___f_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___f_969_; lean_object* v___x_970_; lean_object* v___y_972_; 
lean_inc(v_name_962_);
v___f_964_ = lean_alloc_closure((void*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_964_, 0, v_name_962_);
v___x_965_ = lean_box(0);
v___x_966_ = ((lean_object*)(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__0));
v___x_967_ = ((lean_object*)(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__1));
v___x_968_ = lean_box(v_builtin_961_);
lean_inc(v_name_962_);
v___f_969_ = lean_alloc_closure((void*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2____boxed), 11, 5);
lean_closure_set(v___f_969_, 0, v___x_968_);
lean_closure_set(v___f_969_, 1, v___x_965_);
lean_closure_set(v___f_969_, 2, v___x_966_);
lean_closure_set(v___f_969_, 3, v___x_967_);
lean_closure_set(v___f_969_, 4, v_name_962_);
v___x_970_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__24_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_));
if (v_builtin_961_ == 0)
{
lean_object* v___x_979_; 
v___x_979_ = ((lean_object*)(l_panic___at___00Lean_Server_CodeAction_getFileSource_x21_spec__0___closed__0));
v___y_972_ = v___x_979_;
goto v___jp_971_;
}
else
{
lean_object* v___x_980_; 
v___x_980_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__26_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_));
v___y_972_ = v___x_980_;
goto v___jp_971_;
}
v___jp_971_:
{
lean_object* v___x_973_; lean_object* v___x_974_; uint8_t v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_973_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__25_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_));
v___x_974_ = lean_string_append(v___y_972_, v___x_973_);
v___x_975_ = 1;
v___x_976_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_976_, 0, v___x_970_);
lean_ctor_set(v___x_976_, 1, v_name_962_);
lean_ctor_set(v___x_976_, 2, v___x_974_);
lean_ctor_set_uint8(v___x_976_, sizeof(void*)*3, v___x_975_);
v___x_977_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
lean_ctor_set(v___x_977_, 1, v___f_969_);
lean_ctor_set(v___x_977_, 2, v___f_964_);
v___x_978_ = l_Lean_registerBuiltinAttribute(v___x_977_);
return v___x_978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2____boxed(lean_object* v_builtin_981_, lean_object* v_name_982_, lean_object* v___y_983_){
_start:
{
uint8_t v_builtin_boxed_984_; lean_object* v_res_985_; 
v_builtin_boxed_984_ = lean_unbox(v_builtin_981_);
v_res_985_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(v_builtin_boxed_984_, v_name_982_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(){
_start:
{
uint8_t v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_993_ = 1;
v___x_994_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_));
v___x_995_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(v___x_993_, v___x_994_);
if (lean_obj_tag(v___x_995_) == 0)
{
uint8_t v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
lean_dec_ref(v___x_995_);
v___x_996_ = 0;
v___x_997_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_));
v___x_998_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(v___x_996_, v___x_997_);
return v___x_998_;
}
else
{
return v___x_995_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2____boxed(lean_object* v_a_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_();
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1001_, lean_object* v_msg_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___redArg(v_msg_1002_, v___y_1003_, v___y_1004_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1007_, lean_object* v_msg_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0(v_00_u03b1_1007_, v_msg_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b1_1013_, lean_object* v_attrName_1014_, lean_object* v_declName_1015_, lean_object* v_givenType_1016_, lean_object* v_expectedType_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg(v_attrName_1014_, v_declName_1015_, v_givenType_1016_, v_expectedType_1017_, v___y_1018_, v___y_1019_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___boxed(lean_object* v_00_u03b1_1022_, lean_object* v_attrName_1023_, lean_object* v_declName_1024_, lean_object* v_givenType_1025_, lean_object* v_expectedType_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3(v_00_u03b1_1022_, v_attrName_1023_, v_declName_1024_, v_givenType_1025_, v_expectedType_1026_, v___y_1027_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b1_1031_, lean_object* v_name_1032_, uint8_t v_kind_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg(v_name_1032_, v_kind_1033_, v___y_1034_, v___y_1035_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___boxed(lean_object* v_00_u03b1_1038_, lean_object* v_name_1039_, lean_object* v_kind_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
uint8_t v_kind_boxed_1044_; lean_object* v_res_1045_; 
v_kind_boxed_1044_ = lean_unbox(v_kind_1040_);
v_res_1045_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4(v_00_u03b1_1038_, v_name_1039_, v_kind_boxed_1044_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_00_u03b1_1046_, lean_object* v_constName_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_1047_, v___y_1048_, v___y_1049_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_00_u03b1_1052_, lean_object* v_constName_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3(v_00_u03b1_1052_, v_constName_1053_, v___y_1054_, v___y_1055_);
lean_dec(v___y_1055_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4(lean_object* v_00_u03b1_1058_, lean_object* v_ref_1059_, lean_object* v_constName_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(v_ref_1059_, v_constName_1060_, v___y_1061_, v___y_1062_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1065_, lean_object* v_ref_1066_, lean_object* v_constName_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4(v_00_u03b1_1065_, v_ref_1066_, v_constName_1067_, v___y_1068_, v___y_1069_);
lean_dec(v___y_1069_);
lean_dec(v_ref_1066_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7(lean_object* v_00_u03b1_1072_, lean_object* v_ref_1073_, lean_object* v_msg_1074_, lean_object* v_declHint_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(v_ref_1073_, v_msg_1074_, v_declHint_1075_, v___y_1076_, v___y_1077_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b1_1080_, lean_object* v_ref_1081_, lean_object* v_msg_1082_, lean_object* v_declHint_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7(v_00_u03b1_1080_, v_ref_1081_, v_msg_1082_, v_declHint_1083_, v___y_1084_, v___y_1085_);
lean_dec(v___y_1085_);
lean_dec(v_ref_1081_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(lean_object* v_msg_1088_, lean_object* v_declHint_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_1088_, v_declHint_1089_, v___y_1091_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_1094_, lean_object* v_declHint_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(v_msg_1094_, v_declHint_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9(lean_object* v_00_u03b1_1100_, lean_object* v_ref_1101_, lean_object* v_msg_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_1101_, v_msg_1102_, v___y_1103_, v___y_1104_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1107_, lean_object* v_ref_1108_, lean_object* v_msg_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9(v_00_u03b1_1107_, v_ref_1108_, v_msg_1109_, v___y_1110_, v___y_1111_);
lean_dec(v___y_1111_);
lean_dec(v_ref_1108_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg(lean_object* v_inst_1118_, lean_object* v_inst_1119_, lean_object* v_inst_1120_, lean_object* v_inst_1121_, lean_object* v_declName_1122_){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg___closed__0));
v___x_1124_ = l_Lean_evalConstCheck___redArg(v_inst_1121_, v_inst_1118_, v_inst_1120_, v_inst_1119_, v___x_1123_, v_declName_1122_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe(lean_object* v_M_1125_, lean_object* v_inst_1126_, lean_object* v_inst_1127_, lean_object* v_inst_1128_, lean_object* v_inst_1129_, lean_object* v_declName_1130_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg(v_inst_1126_, v_inst_1127_, v_inst_1128_, v_inst_1129_, v_declName_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleCodeAction_spec__6(lean_object* v___y_1132_){
_start:
{
lean_object* v_doc_1134_; lean_object* v___x_1135_; 
v_doc_1134_ = lean_ctor_get(v___y_1132_, 1);
lean_inc_ref(v_doc_1134_);
v___x_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1135_, 0, v_doc_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleCodeAction_spec__6___boxed(lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleCodeAction_spec__6(v___y_1136_);
lean_dec_ref(v___y_1136_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_handleCodeAction_spec__4(lean_object* v_init_1139_, lean_object* v_x_1140_){
_start:
{
if (lean_obj_tag(v_x_1140_) == 0)
{
lean_object* v_k_1141_; lean_object* v_v_1142_; lean_object* v_l_1143_; lean_object* v_r_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v_k_1141_ = lean_ctor_get(v_x_1140_, 1);
v_v_1142_ = lean_ctor_get(v_x_1140_, 2);
v_l_1143_ = lean_ctor_get(v_x_1140_, 3);
v_r_1144_ = lean_ctor_get(v_x_1140_, 4);
v___x_1145_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_handleCodeAction_spec__4(v_init_1139_, v_r_1144_);
lean_inc(v_v_1142_);
lean_inc(v_k_1141_);
v___x_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1146_, 0, v_k_1141_);
lean_ctor_set(v___x_1146_, 1, v_v_1142_);
v___x_1147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
lean_ctor_set(v___x_1147_, 1, v___x_1145_);
v_init_1139_ = v___x_1147_;
v_x_1140_ = v_l_1143_;
goto _start;
}
else
{
return v_init_1139_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_handleCodeAction_spec__4___boxed(lean_object* v_init_1149_, lean_object* v_x_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_handleCodeAction_spec__4(v_init_1149_, v_x_1150_);
lean_dec(v_x_1150_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg___lam__0(lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v___x_1155_; lean_object* v_env_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1155_ = lean_st_ref_get(v___y_1153_);
v_env_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc_ref(v_env_1156_);
lean_dec(v___x_1155_);
v___x_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1157_, 0, v_env_1156_);
v___x_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg___lam__0(v___y_1159_, v___y_1160_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
return v_res_1162_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1163_ = lean_box(0);
v___x_1164_ = l_Lean_Elab_abortCommandExceptionId;
v___x_1165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
lean_ctor_set(v___x_1165_, 1, v___x_1163_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg(){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg___closed__0);
v___x_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v___y_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg();
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9___redArg(lean_object* v_msg_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_ref_1175_; lean_object* v___x_1176_; lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1185_; 
v_ref_1175_ = lean_ctor_get(v___y_1172_, 5);
v___x_1176_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0(v_msg_1171_, v___y_1172_, v___y_1173_);
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1179_ = v___x_1176_;
v_isShared_1180_ = v_isSharedCheck_1185_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1176_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1185_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1181_; lean_object* v___x_1183_; 
lean_inc(v_ref_1175_);
v___x_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1181_, 0, v_ref_1175_);
lean_ctor_set(v___x_1181_, 1, v_a_1177_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set_tag(v___x_1179_, 1);
lean_ctor_set(v___x_1179_, 0, v___x_1181_);
v___x_1183_ = v___x_1179_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_msg_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9___redArg(v_msg_1186_, v___y_1187_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5___redArg(lean_object* v_x_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
if (lean_obj_tag(v_x_1191_) == 0)
{
lean_object* v_a_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v_a_1196_ = lean_ctor_get(v_x_1191_, 0);
lean_inc(v_a_1196_);
lean_dec_ref(v_x_1191_);
v___x_1197_ = l_Lean_stringToMessageData(v_a_1196_);
v___x_1198_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9___redArg(v___x_1197_, v___y_1193_, v___y_1194_);
return v___x_1198_;
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1207_; 
v_a_1199_ = lean_ctor_get(v_x_1191_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_x_1191_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1201_ = v_x_1191_;
v_isShared_1202_ = v_isSharedCheck_1207_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v_x_1191_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1207_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
return v___x_1205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_x_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5___redArg(v_x_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec_ref(v___y_1209_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg(lean_object* v_typeName_1214_, lean_object* v_constName_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v___x_1220_; lean_object* v_env_1221_; uint8_t v___x_1222_; 
v___x_1220_ = lean_st_ref_get(v___y_1218_);
v_env_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc_ref(v_env_1221_);
lean_dec(v___x_1220_);
lean_inc(v_constName_1215_);
v___x_1222_ = lean_has_compile_error(v_env_1221_, v_constName_1215_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg___lam__0(v___y_1217_, v___y_1218_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1243_; 
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1226_ = v___x_1223_;
v_isShared_1227_ = v_isSharedCheck_1243_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1223_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1243_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
if (lean_obj_tag(v_a_1224_) == 0)
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1238_; 
lean_dec(v_constName_1215_);
lean_dec(v_typeName_1214_);
v_a_1228_ = lean_ctor_get(v_a_1224_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_a_1224_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1230_ = v_a_1224_;
v_isShared_1231_ = v_isSharedCheck_1238_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v_a_1224_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1238_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
lean_object* v___x_1235_; 
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 0, v___x_1233_);
v___x_1235_ = v___x_1226_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1233_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
else
{
lean_object* v_a_1239_; lean_object* v_options_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
lean_del_object(v___x_1226_);
v_a_1239_ = lean_ctor_get(v_a_1224_, 0);
lean_inc(v_a_1239_);
lean_dec_ref(v_a_1224_);
v_options_1240_ = lean_ctor_get(v___y_1217_, 2);
v___x_1241_ = l_Lean_Environment_evalConstCheck___redArg(v_a_1239_, v_options_1240_, v_typeName_1214_, v_constName_1215_);
v___x_1242_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5___redArg(v___x_1241_, v___y_1216_, v___y_1217_, v___y_1218_);
return v___x_1242_;
}
}
}
else
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
lean_dec(v_constName_1215_);
lean_dec(v_typeName_1214_);
v_a_1244_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___x_1223_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1223_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1244_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
else
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg();
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1297_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1255_ = v___x_1252_;
v_isShared_1256_ = v_isSharedCheck_1297_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1252_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1297_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
if (lean_obj_tag(v_a_1253_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1267_; 
lean_dec(v_constName_1215_);
lean_dec(v_typeName_1214_);
v_a_1257_ = lean_ctor_get(v_a_1253_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v_a_1253_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1259_ = v_a_1253_;
v_isShared_1260_ = v_isSharedCheck_1267_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v_a_1253_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1267_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
lean_object* v___x_1264_; 
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 0, v___x_1262_);
v___x_1264_ = v___x_1255_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1262_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
else
{
lean_object* v___x_1268_; 
lean_dec_ref(v_a_1253_);
lean_del_object(v___x_1255_);
v___x_1268_ = l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg___lam__0(v___y_1217_, v___y_1218_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1288_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1271_ = v___x_1268_;
v_isShared_1272_ = v_isSharedCheck_1288_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1268_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1288_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
if (lean_obj_tag(v_a_1269_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1283_; 
lean_dec(v_constName_1215_);
lean_dec(v_typeName_1214_);
v_a_1273_ = lean_ctor_get(v_a_1269_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_a_1269_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1275_ = v_a_1269_;
v_isShared_1276_ = v_isSharedCheck_1283_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v_a_1269_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1283_;
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
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v___x_1280_; 
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v___x_1278_);
v___x_1280_ = v___x_1271_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v_options_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
lean_del_object(v___x_1271_);
v_a_1284_ = lean_ctor_get(v_a_1269_, 0);
lean_inc(v_a_1284_);
lean_dec_ref(v_a_1269_);
v_options_1285_ = lean_ctor_get(v___y_1217_, 2);
v___x_1286_ = l_Lean_Environment_evalConstCheck___redArg(v_a_1284_, v_options_1285_, v_typeName_1214_, v_constName_1215_);
v___x_1287_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5___redArg(v___x_1286_, v___y_1216_, v___y_1217_, v___y_1218_);
return v___x_1287_;
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_dec(v_constName_1215_);
lean_dec(v_typeName_1214_);
v_a_1289_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1268_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1268_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec(v_constName_1215_);
lean_dec(v_typeName_1214_);
v_a_1298_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1252_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1252_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg___boxed(lean_object* v_typeName_1306_, lean_object* v_constName_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg(v_typeName_1306_, v_constName_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec_ref(v___y_1308_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2(lean_object* v_declName_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg___closed__0));
v___x_1319_ = l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg(v___x_1318_, v_declName_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2___boxed(lean_object* v_declName_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2(v_declName_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec_ref(v___y_1321_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_handleCodeAction_spec__3(size_t v_sz_1326_, size_t v_i_1327_, lean_object* v_bs_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
uint8_t v___x_1333_; 
v___x_1333_ = lean_usize_dec_lt(v_i_1327_, v_sz_1326_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1334_, 0, v_bs_1328_);
v___x_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
return v___x_1335_;
}
else
{
lean_object* v_v_1336_; lean_object* v___x_1337_; 
v_v_1336_ = lean_array_uget_borrowed(v_bs_1328_, v_i_1327_);
lean_inc(v_v_1336_);
v___x_1337_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2(v_v_1336_, v___y_1329_, v___y_1330_, v___y_1331_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1360_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1340_ = v___x_1337_;
v_isShared_1341_ = v_isSharedCheck_1360_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1337_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1360_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
if (lean_obj_tag(v_a_1338_) == 0)
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1352_; 
lean_dec_ref(v_bs_1328_);
v_a_1342_ = lean_ctor_get(v_a_1338_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_a_1338_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1344_ = v_a_1338_;
v_isShared_1345_ = v_isSharedCheck_1352_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v_a_1338_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1352_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
lean_object* v___x_1349_; 
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v___x_1347_);
v___x_1349_ = v___x_1340_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1354_; lean_object* v_bs_x27_1355_; size_t v___x_1356_; size_t v___x_1357_; lean_object* v___x_1358_; 
lean_del_object(v___x_1340_);
v_a_1353_ = lean_ctor_get(v_a_1338_, 0);
lean_inc(v_a_1353_);
lean_dec_ref(v_a_1338_);
v___x_1354_ = lean_unsigned_to_nat(0u);
v_bs_x27_1355_ = lean_array_uset(v_bs_1328_, v_i_1327_, v___x_1354_);
v___x_1356_ = ((size_t)1ULL);
v___x_1357_ = lean_usize_add(v_i_1327_, v___x_1356_);
v___x_1358_ = lean_array_uset(v_bs_x27_1355_, v_i_1327_, v_a_1353_);
v_i_1327_ = v___x_1357_;
v_bs_1328_ = v___x_1358_;
goto _start;
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec_ref(v_bs_1328_);
v_a_1361_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1337_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1337_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_handleCodeAction_spec__3___boxed(lean_object* v_sz_1369_, lean_object* v_i_1370_, lean_object* v_bs_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
size_t v_sz_boxed_1376_; size_t v_i_boxed_1377_; lean_object* v_res_1378_; 
v_sz_boxed_1376_ = lean_unbox_usize(v_sz_1369_);
lean_dec(v_sz_1369_);
v_i_boxed_1377_ = lean_unbox_usize(v_i_1370_);
lean_dec(v_i_1370_);
v_res_1378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_handleCodeAction_spec__3(v_sz_boxed_1376_, v_i_boxed_1377_, v_bs_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec_ref(v___y_1372_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_handleCodeAction_spec__1_spec__1(lean_object* v_init_1379_, lean_object* v_x_1380_){
_start:
{
if (lean_obj_tag(v_x_1380_) == 0)
{
lean_object* v_k_1381_; lean_object* v_l_1382_; lean_object* v_r_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v_k_1381_ = lean_ctor_get(v_x_1380_, 1);
lean_inc(v_k_1381_);
v_l_1382_ = lean_ctor_get(v_x_1380_, 3);
lean_inc(v_l_1382_);
v_r_1383_ = lean_ctor_get(v_x_1380_, 4);
lean_inc(v_r_1383_);
lean_dec_ref(v_x_1380_);
v___x_1384_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_handleCodeAction_spec__1_spec__1(v_init_1379_, v_l_1382_);
v___x_1385_ = lean_array_push(v___x_1384_, v_k_1381_);
v_init_1379_ = v___x_1385_;
v_x_1380_ = v_r_1383_;
goto _start;
}
else
{
return v_init_1379_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeAction___lam__0(lean_object* v___x_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v___x_1392_; lean_object* v_env_1393_; lean_object* v___x_1394_; lean_object* v_toEnvExtension_1395_; lean_object* v_asyncMode_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___y_1400_; 
v___x_1392_ = lean_st_ref_get(v___y_1390_);
v_env_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc_ref(v_env_1393_);
lean_dec(v___x_1392_);
v___x_1394_ = l_Lean_Server_codeActionProviderExt;
v_toEnvExtension_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc_ref(v_toEnvExtension_1395_);
v_asyncMode_1396_ = lean_ctor_get(v_toEnvExtension_1395_, 2);
lean_inc(v_asyncMode_1396_);
lean_dec_ref(v_toEnvExtension_1395_);
v___x_1397_ = lean_box(0);
v___x_1398_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1387_, v___x_1394_, v_env_1393_, v_asyncMode_1396_, v___x_1397_);
lean_dec(v_asyncMode_1396_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_size_1448_; 
v_size_1448_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_size_1448_);
v___y_1400_ = v_size_1448_;
goto v___jp_1399_;
}
else
{
lean_object* v___x_1449_; 
v___x_1449_ = lean_unsigned_to_nat(0u);
v___y_1400_ = v___x_1449_;
goto v___jp_1399_;
}
v___jp_1399_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; size_t v_sz_1403_; size_t v___x_1404_; lean_object* v___x_1405_; 
v___x_1401_ = lean_mk_empty_array_with_capacity(v___y_1400_);
lean_dec(v___y_1400_);
v___x_1402_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_handleCodeAction_spec__1_spec__1(v___x_1401_, v___x_1398_);
v_sz_1403_ = lean_array_size(v___x_1402_);
v___x_1404_ = ((size_t)0ULL);
lean_inc_ref(v___x_1402_);
v___x_1405_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_handleCodeAction_spec__3(v_sz_1403_, v___x_1404_, v___x_1402_, v___y_1388_, v___y_1389_, v___y_1390_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1439_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1439_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1439_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
if (lean_obj_tag(v_a_1406_) == 0)
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1420_; 
lean_dec_ref(v___x_1402_);
v_a_1410_ = lean_ctor_get(v_a_1406_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v_a_1406_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1412_ = v_a_1406_;
v_isShared_1413_ = v_isSharedCheck_1420_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v_a_1406_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1420_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1410_);
v___x_1415_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
lean_object* v___x_1417_; 
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1415_);
v___x_1417_ = v___x_1408_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1438_; 
v_a_1421_ = lean_ctor_get(v_a_1406_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_a_1406_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1423_ = v_a_1406_;
v_isShared_1424_ = v_isSharedCheck_1438_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v_a_1406_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1438_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1433_; 
v___x_1425_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_builtinCodeActionProviders;
v___x_1426_ = lean_st_ref_get(v___x_1425_);
v___x_1427_ = lean_box(0);
v___x_1428_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_handleCodeAction_spec__4(v___x_1427_, v___x_1426_);
lean_dec(v___x_1426_);
v___x_1429_ = lean_array_mk(v___x_1428_);
v___x_1430_ = l_Array_zip___redArg(v___x_1402_, v_a_1421_);
lean_dec(v_a_1421_);
lean_dec_ref(v___x_1402_);
v___x_1431_ = l_Array_append___redArg(v___x_1429_, v___x_1430_);
lean_dec_ref(v___x_1430_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v___x_1431_);
v___x_1433_ = v___x_1423_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1435_; 
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1433_);
v___x_1435_ = v___x_1408_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec_ref(v___x_1402_);
v_a_1440_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1405_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1405_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeAction___lam__0___boxed(lean_object* v___x_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Lean_Server_handleCodeAction___lam__0(v___x_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec_ref(v___y_1451_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Server_handleCodeAction_spec__0___redArg(lean_object* v_params_1456_, lean_object* v_fst_1457_, lean_object* v_as_1458_, lean_object* v_i_1459_, lean_object* v_j_1460_, lean_object* v_bs_1461_){
_start:
{
lean_object* v_zero_1463_; uint8_t v_isZero_1464_; 
v_zero_1463_ = lean_unsigned_to_nat(0u);
v_isZero_1464_ = lean_nat_dec_eq(v_i_1459_, v_zero_1463_);
if (v_isZero_1464_ == 1)
{
lean_object* v___x_1465_; 
lean_dec(v_j_1460_);
lean_dec(v_i_1459_);
lean_dec(v_fst_1457_);
lean_dec_ref(v_params_1456_);
v___x_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1465_, 0, v_bs_1461_);
return v___x_1465_;
}
else
{
lean_object* v___x_1466_; lean_object* v_eager_1467_; lean_object* v_toWorkDoneProgressParams_1468_; lean_object* v_toPartialResultParams_1469_; lean_object* v_title_1470_; lean_object* v_kind_x3f_1471_; lean_object* v_diagnostics_x3f_1472_; lean_object* v_isPreferred_x3f_1473_; lean_object* v_disabled_x3f_1474_; lean_object* v_edit_x3f_1475_; lean_object* v_command_x3f_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1491_; 
v___x_1466_ = lean_array_fget_borrowed(v_as_1458_, v_j_1460_);
v_eager_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc_ref(v_eager_1467_);
v_toWorkDoneProgressParams_1468_ = lean_ctor_get(v_eager_1467_, 0);
v_toPartialResultParams_1469_ = lean_ctor_get(v_eager_1467_, 1);
v_title_1470_ = lean_ctor_get(v_eager_1467_, 2);
v_kind_x3f_1471_ = lean_ctor_get(v_eager_1467_, 3);
v_diagnostics_x3f_1472_ = lean_ctor_get(v_eager_1467_, 4);
v_isPreferred_x3f_1473_ = lean_ctor_get(v_eager_1467_, 5);
v_disabled_x3f_1474_ = lean_ctor_get(v_eager_1467_, 6);
v_edit_x3f_1475_ = lean_ctor_get(v_eager_1467_, 7);
v_command_x3f_1476_ = lean_ctor_get(v_eager_1467_, 8);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_eager_1467_);
if (v_isSharedCheck_1491_ == 0)
{
lean_object* v_unused_1492_; 
v_unused_1492_ = lean_ctor_get(v_eager_1467_, 9);
lean_dec(v_unused_1492_);
v___x_1478_ = v_eager_1467_;
v_isShared_1479_ = v_isSharedCheck_1491_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_command_x3f_1476_);
lean_inc(v_edit_x3f_1475_);
lean_inc(v_disabled_x3f_1474_);
lean_inc(v_isPreferred_x3f_1473_);
lean_inc(v_diagnostics_x3f_1472_);
lean_inc(v_kind_x3f_1471_);
lean_inc(v_title_1470_);
lean_inc(v_toPartialResultParams_1469_);
lean_inc(v_toWorkDoneProgressParams_1468_);
lean_dec(v_eager_1467_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1491_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v_one_1480_; lean_object* v_n_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1486_; 
v_one_1480_ = lean_unsigned_to_nat(1u);
v_n_1481_ = lean_nat_sub(v_i_1459_, v_one_1480_);
lean_dec(v_i_1459_);
lean_inc(v_j_1460_);
lean_inc(v_fst_1457_);
lean_inc_ref(v_params_1456_);
v___x_1482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1482_, 0, v_params_1456_);
lean_ctor_set(v___x_1482_, 1, v_fst_1457_);
lean_ctor_set(v___x_1482_, 2, v_j_1460_);
v___x_1483_ = l_Lean_Server_instToJsonCodeActionResolveData_toJson(v___x_1482_);
v___x_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 9, v___x_1484_);
v___x_1486_ = v___x_1478_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_toWorkDoneProgressParams_1468_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_toPartialResultParams_1469_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_title_1470_);
lean_ctor_set(v_reuseFailAlloc_1490_, 3, v_kind_x3f_1471_);
lean_ctor_set(v_reuseFailAlloc_1490_, 4, v_diagnostics_x3f_1472_);
lean_ctor_set(v_reuseFailAlloc_1490_, 5, v_isPreferred_x3f_1473_);
lean_ctor_set(v_reuseFailAlloc_1490_, 6, v_disabled_x3f_1474_);
lean_ctor_set(v_reuseFailAlloc_1490_, 7, v_edit_x3f_1475_);
lean_ctor_set(v_reuseFailAlloc_1490_, 8, v_command_x3f_1476_);
lean_ctor_set(v_reuseFailAlloc_1490_, 9, v___x_1484_);
v___x_1486_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = lean_nat_add(v_j_1460_, v_one_1480_);
lean_dec(v_j_1460_);
v___x_1488_ = lean_array_push(v_bs_1461_, v___x_1486_);
v_i_1459_ = v_n_1481_;
v_j_1460_ = v___x_1487_;
v_bs_1461_ = v___x_1488_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Server_handleCodeAction_spec__0___redArg___boxed(lean_object* v_params_1493_, lean_object* v_fst_1494_, lean_object* v_as_1495_, lean_object* v_i_1496_, lean_object* v_j_1497_, lean_object* v_bs_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Array_mapFinIdxM_map___at___00Lean_Server_handleCodeAction_spec__0___redArg(v_params_1493_, v_fst_1494_, v_as_1495_, v_i_1496_, v_j_1497_, v_bs_1498_);
lean_dec_ref(v_as_1495_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_handleCodeAction_spec__5(lean_object* v_params_1501_, lean_object* v_snap_1502_, lean_object* v_as_1503_, size_t v_i_1504_, size_t v_stop_1505_, lean_object* v_b_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_a_1510_; uint8_t v___x_1514_; 
v___x_1514_ = lean_usize_dec_eq(v_i_1504_, v_stop_1505_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; lean_object* v_fst_1516_; lean_object* v_snd_1517_; lean_object* v___x_1518_; 
v___x_1515_ = lean_array_uget_borrowed(v_as_1503_, v_i_1504_);
v_fst_1516_ = lean_ctor_get(v___x_1515_, 0);
v_snd_1517_ = lean_ctor_get(v___x_1515_, 1);
v___x_1518_ = l_Lean_Server_RequestM_checkCancelled(v___y_1507_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v___x_1519_; 
lean_dec_ref(v___x_1518_);
lean_inc(v_snd_1517_);
lean_inc_ref(v___y_1507_);
lean_inc_ref(v_snap_1502_);
lean_inc_ref(v_params_1501_);
v___x_1519_ = lean_apply_4(v_snd_1517_, v_params_1501_, v_snap_1502_, v___y_1507_, lean_box(0));
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1520_);
lean_dec_ref(v___x_1519_);
v___x_1521_ = lean_array_get_size(v_a_1520_);
v___x_1522_ = lean_unsigned_to_nat(0u);
v___x_1523_ = lean_mk_empty_array_with_capacity(v___x_1521_);
lean_inc(v_fst_1516_);
lean_inc_ref(v_params_1501_);
v___x_1524_ = l_Array_mapFinIdxM_map___at___00Lean_Server_handleCodeAction_spec__0___redArg(v_params_1501_, v_fst_1516_, v_a_1520_, v___x_1521_, v___x_1522_, v___x_1523_);
lean_dec(v_a_1520_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1526_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref(v___x_1524_);
v___x_1526_ = l_Array_append___redArg(v_b_1506_, v_a_1525_);
lean_dec(v_a_1525_);
v_a_1510_ = v___x_1526_;
goto v___jp_1509_;
}
else
{
lean_dec_ref(v_b_1506_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1527_; 
v_a_1527_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1527_);
lean_dec_ref(v___x_1524_);
v_a_1510_ = v_a_1527_;
goto v___jp_1509_;
}
else
{
lean_dec_ref(v___y_1507_);
lean_dec_ref(v_snap_1502_);
lean_dec_ref(v_params_1501_);
return v___x_1524_;
}
}
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
lean_dec_ref(v___y_1507_);
lean_dec_ref(v_b_1506_);
lean_dec_ref(v_snap_1502_);
lean_dec_ref(v_params_1501_);
v_a_1528_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1519_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1519_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
lean_dec_ref(v___y_1507_);
lean_dec_ref(v_b_1506_);
lean_dec_ref(v_snap_1502_);
lean_dec_ref(v_params_1501_);
v_a_1536_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1518_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1518_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1536_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
else
{
lean_object* v___x_1544_; 
lean_dec_ref(v___y_1507_);
lean_dec_ref(v_snap_1502_);
lean_dec_ref(v_params_1501_);
v___x_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1544_, 0, v_b_1506_);
return v___x_1544_;
}
v___jp_1509_:
{
size_t v___x_1511_; size_t v___x_1512_; 
v___x_1511_ = ((size_t)1ULL);
v___x_1512_ = lean_usize_add(v_i_1504_, v___x_1511_);
v_i_1504_ = v___x_1512_;
v_b_1506_ = v_a_1510_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_handleCodeAction_spec__5___boxed(lean_object* v_params_1545_, lean_object* v_snap_1546_, lean_object* v_as_1547_, lean_object* v_i_1548_, lean_object* v_stop_1549_, lean_object* v_b_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
size_t v_i_boxed_1553_; size_t v_stop_boxed_1554_; lean_object* v_res_1555_; 
v_i_boxed_1553_ = lean_unbox_usize(v_i_1548_);
lean_dec(v_i_1548_);
v_stop_boxed_1554_ = lean_unbox_usize(v_stop_1549_);
lean_dec(v_stop_1549_);
v_res_1555_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_handleCodeAction_spec__5(v_params_1545_, v_snap_1546_, v_as_1547_, v_i_boxed_1553_, v_stop_boxed_1554_, v_b_1550_, v___y_1551_);
lean_dec_ref(v_as_1547_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeAction___lam__1(lean_object* v___f_1558_, lean_object* v_params_1559_, lean_object* v_snap_1560_, lean_object* v___y_1561_){
_start:
{
lean_object* v___x_1563_; 
lean_inc_ref(v___y_1561_);
lean_inc_ref(v_snap_1560_);
v___x_1563_ = l_Lean_Server_RequestM_runCoreM___redArg(v_snap_1560_, v___f_1558_, v___y_1561_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1585_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1566_ = v___x_1563_;
v_isShared_1567_ = v_isSharedCheck_1585_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1563_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1585_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; 
v___x_1568_ = lean_unsigned_to_nat(0u);
v___x_1569_ = ((lean_object*)(l_Lean_Server_handleCodeAction___lam__1___closed__0));
v___x_1570_ = lean_array_get_size(v_a_1564_);
v___x_1571_ = lean_nat_dec_lt(v___x_1568_, v___x_1570_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1573_; 
lean_dec(v_a_1564_);
lean_dec_ref(v___y_1561_);
lean_dec_ref(v_snap_1560_);
lean_dec_ref(v_params_1559_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v___x_1569_);
v___x_1573_ = v___x_1566_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1569_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
else
{
uint8_t v___x_1575_; 
v___x_1575_ = lean_nat_dec_le(v___x_1570_, v___x_1570_);
if (v___x_1575_ == 0)
{
if (v___x_1571_ == 0)
{
lean_object* v___x_1577_; 
lean_dec(v_a_1564_);
lean_dec_ref(v___y_1561_);
lean_dec_ref(v_snap_1560_);
lean_dec_ref(v_params_1559_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v___x_1569_);
v___x_1577_ = v___x_1566_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1569_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
else
{
size_t v___x_1579_; size_t v___x_1580_; lean_object* v___x_1581_; 
lean_del_object(v___x_1566_);
v___x_1579_ = ((size_t)0ULL);
v___x_1580_ = lean_usize_of_nat(v___x_1570_);
v___x_1581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_handleCodeAction_spec__5(v_params_1559_, v_snap_1560_, v_a_1564_, v___x_1579_, v___x_1580_, v___x_1569_, v___y_1561_);
lean_dec(v_a_1564_);
return v___x_1581_;
}
}
else
{
size_t v___x_1582_; size_t v___x_1583_; lean_object* v___x_1584_; 
lean_del_object(v___x_1566_);
v___x_1582_ = ((size_t)0ULL);
v___x_1583_ = lean_usize_of_nat(v___x_1570_);
v___x_1584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_handleCodeAction_spec__5(v_params_1559_, v_snap_1560_, v_a_1564_, v___x_1582_, v___x_1583_, v___x_1569_, v___y_1561_);
lean_dec(v_a_1564_);
return v___x_1584_;
}
}
}
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec_ref(v___y_1561_);
lean_dec_ref(v_snap_1560_);
lean_dec_ref(v_params_1559_);
v_a_1586_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1563_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1563_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeAction___lam__1___boxed(lean_object* v___f_1594_, lean_object* v_params_1595_, lean_object* v_snap_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Lean_Server_handleCodeAction___lam__1(v___f_1594_, v_params_1595_, v_snap_1596_, v___y_1597_);
return v_res_1599_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_handleCodeAction___lam__2(lean_object* v___x_1600_, lean_object* v_s_1601_){
_start:
{
lean_object* v___x_1602_; uint8_t v___x_1603_; 
v___x_1602_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_s_1601_);
v___x_1603_ = lean_nat_dec_le(v___x_1600_, v___x_1602_);
lean_dec(v___x_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeAction___lam__2___boxed(lean_object* v___x_1604_, lean_object* v_s_1605_){
_start:
{
uint8_t v_res_1606_; lean_object* v_r_1607_; 
v_res_1606_ = l_Lean_Server_handleCodeAction___lam__2(v___x_1604_, v_s_1605_);
lean_dec_ref(v_s_1605_);
lean_dec(v___x_1604_);
v_r_1607_ = lean_box(v_res_1606_);
return v_r_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeAction___lam__3(lean_object* v___x_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1608_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeAction___lam__3___boxed(lean_object* v___x_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Lean_Server_handleCodeAction___lam__3(v___x_1612_, v___y_1613_);
lean_dec_ref(v___y_1613_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeAction(lean_object* v_params_1622_, lean_object* v_a_1623_){
_start:
{
lean_object* v___x_1625_; lean_object* v_a_1626_; lean_object* v_toEditableDocumentCore_1627_; lean_object* v_meta_1628_; lean_object* v_range_1629_; lean_object* v_text_1630_; lean_object* v_end_1631_; lean_object* v___f_1632_; lean_object* v___f_1633_; lean_object* v___x_1634_; lean_object* v___f_1635_; lean_object* v___f_1636_; lean_object* v___x_1637_; 
v___x_1625_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleCodeAction_spec__6(v_a_1623_);
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1626_);
lean_dec_ref(v___x_1625_);
v_toEditableDocumentCore_1627_ = lean_ctor_get(v_a_1626_, 0);
v_meta_1628_ = lean_ctor_get(v_toEditableDocumentCore_1627_, 0);
v_range_1629_ = lean_ctor_get(v_params_1622_, 3);
v_text_1630_ = lean_ctor_get(v_meta_1628_, 3);
v_end_1631_ = lean_ctor_get(v_range_1629_, 1);
lean_inc_ref(v_end_1631_);
v___f_1632_ = ((lean_object*)(l_Lean_Server_handleCodeAction___closed__0));
v___f_1633_ = lean_alloc_closure((void*)(l_Lean_Server_handleCodeAction___lam__1___boxed), 5, 2);
lean_closure_set(v___f_1633_, 0, v___f_1632_);
lean_closure_set(v___f_1633_, 1, v_params_1622_);
v___x_1634_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1630_, v_end_1631_);
v___f_1635_ = lean_alloc_closure((void*)(l_Lean_Server_handleCodeAction___lam__2___boxed), 2, 1);
lean_closure_set(v___f_1635_, 0, v___x_1634_);
v___f_1636_ = ((lean_object*)(l_Lean_Server_handleCodeAction___closed__2));
v___x_1637_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_a_1626_, v___f_1635_, v___f_1636_, v___f_1633_, v_a_1623_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeAction___boxed(lean_object* v_params_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_Server_handleCodeAction(v_params_1638_, v_a_1639_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Server_handleCodeAction_spec__0(lean_object* v_params_1642_, lean_object* v_fst_1643_, lean_object* v_as_1644_, lean_object* v_i_1645_, lean_object* v_j_1646_, lean_object* v_inv_1647_, lean_object* v_bs_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Array_mapFinIdxM_map___at___00Lean_Server_handleCodeAction_spec__0___redArg(v_params_1642_, v_fst_1643_, v_as_1644_, v_i_1645_, v_j_1646_, v_bs_1648_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Server_handleCodeAction_spec__0___boxed(lean_object* v_params_1652_, lean_object* v_fst_1653_, lean_object* v_as_1654_, lean_object* v_i_1655_, lean_object* v_j_1656_, lean_object* v_inv_1657_, lean_object* v_bs_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Array_mapFinIdxM_map___at___00Lean_Server_handleCodeAction_spec__0(v_params_1652_, v_fst_1653_, v_as_1654_, v_i_1655_, v_j_1656_, v_inv_1657_, v_bs_1658_, v___y_1659_);
lean_dec_ref(v___y_1659_);
lean_dec_ref(v_as_1654_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_handleCodeAction_spec__1(lean_object* v_init_1662_, lean_object* v_t_1663_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_handleCodeAction_spec__1_spec__1(v_init_1662_, v_t_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6(lean_object* v_00_u03b1_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg();
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b1_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6(v_00_u03b1_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec_ref(v___y_1672_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3(lean_object* v_00_u03b1_1677_, lean_object* v_typeName_1678_, lean_object* v_constName_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg(v_typeName_1678_, v_constName_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1685_, lean_object* v_typeName_1686_, lean_object* v_constName_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3(v_00_u03b1_1685_, v_typeName_1686_, v_constName_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec_ref(v___y_1688_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1693_, lean_object* v_x_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5___redArg(v_x_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1700_, lean_object* v_x_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5(v_00_u03b1_1700_, v_x_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec_ref(v___y_1702_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9(lean_object* v_00_u03b1_1707_, lean_object* v_msg_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9___redArg(v_msg_1708_, v___y_1710_, v___y_1711_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b1_1714_, lean_object* v_msg_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9(v_00_u03b1_1714_, v_msg_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec_ref(v___y_1716_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__2_spec__3(size_t v_sz_1721_, size_t v_i_1722_, lean_object* v_bs_1723_){
_start:
{
uint8_t v___x_1724_; 
v___x_1724_ = lean_usize_dec_lt(v_i_1722_, v_sz_1721_);
if (v___x_1724_ == 0)
{
return v_bs_1723_;
}
else
{
lean_object* v_v_1725_; lean_object* v___x_1726_; lean_object* v_bs_x27_1727_; lean_object* v___x_1728_; size_t v___x_1729_; size_t v___x_1730_; lean_object* v___x_1731_; 
v_v_1725_ = lean_array_uget(v_bs_1723_, v_i_1722_);
v___x_1726_ = lean_unsigned_to_nat(0u);
v_bs_x27_1727_ = lean_array_uset(v_bs_1723_, v_i_1722_, v___x_1726_);
v___x_1728_ = l_Lean_Lsp_instToJsonCodeAction_toJson(v_v_1725_);
v___x_1729_ = ((size_t)1ULL);
v___x_1730_ = lean_usize_add(v_i_1722_, v___x_1729_);
v___x_1731_ = lean_array_uset(v_bs_x27_1727_, v_i_1722_, v___x_1728_);
v_i_1722_ = v___x_1730_;
v_bs_1723_ = v___x_1731_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object* v_sz_1733_, lean_object* v_i_1734_, lean_object* v_bs_1735_){
_start:
{
size_t v_sz_boxed_1736_; size_t v_i_boxed_1737_; lean_object* v_res_1738_; 
v_sz_boxed_1736_ = lean_unbox_usize(v_sz_1733_);
lean_dec(v_sz_1733_);
v_i_boxed_1737_ = lean_unbox_usize(v_i_1734_);
lean_dec(v_i_1734_);
v_res_1738_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__2_spec__3(v_sz_boxed_1736_, v_i_boxed_1737_, v_bs_1735_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_a_1739_){
_start:
{
size_t v_sz_1740_; size_t v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v_sz_1740_ = lean_array_size(v_a_1739_);
v___x_1741_ = ((size_t)0ULL);
v___x_1742_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__2_spec__3(v_sz_1740_, v___x_1741_, v_a_1739_);
v___x_1743_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__1(lean_object* v_serialize_x3f_1744_, uint8_t v_a_1745_, lean_object* v___y_1746_){
_start:
{
if (lean_obj_tag(v___y_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_dec(v_serialize_x3f_1744_);
v_a_1747_ = lean_ctor_get(v___y_1746_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___y_1746_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___y_1746_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___y_1746_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
else
{
if (lean_obj_tag(v_serialize_x3f_1744_) == 1)
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1766_; 
v_a_1755_ = lean_ctor_get(v___y_1746_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___y_1746_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1757_ = v___y_1746_;
v_isShared_1758_ = v_isSharedCheck_1766_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___y_1746_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1766_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v_val_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1764_; 
v_val_1759_ = lean_ctor_get(v_serialize_x3f_1744_, 0);
lean_inc(v_val_1759_);
lean_dec_ref(v_serialize_x3f_1744_);
v___x_1760_ = lean_box(0);
v___x_1761_ = lean_apply_1(v_val_1759_, v_a_1755_);
v___x_1762_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1762_, 0, v___x_1760_);
lean_ctor_set(v___x_1762_, 1, v___x_1761_);
lean_ctor_set_uint8(v___x_1762_, sizeof(void*)*2, v_a_1745_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 0, v___x_1762_);
v___x_1764_ = v___x_1757_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1778_; 
lean_dec(v_serialize_x3f_1744_);
v_a_1767_ = lean_ctor_get(v___y_1746_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___y_1746_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1769_ = v___y_1746_;
v_isShared_1770_ = v_isSharedCheck_1778_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___y_1746_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1778_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1776_; 
v___x_1771_ = l_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__2(v_a_1767_);
lean_inc(v___x_1771_);
v___x_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
v___x_1773_ = l_Lean_Json_compress(v___x_1771_);
v___x_1774_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1774_, 0, v___x_1772_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
lean_ctor_set_uint8(v___x_1774_, sizeof(void*)*2, v_a_1745_);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v___x_1774_);
v___x_1776_ = v___x_1769_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1774_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object* v_serialize_x3f_1779_, lean_object* v_a_1780_, lean_object* v___y_1781_){
_start:
{
uint8_t v_a_831__boxed_1782_; lean_object* v_res_1783_; 
v_a_831__boxed_1782_ = lean_unbox(v_a_1780_);
v_res_1783_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__1(v_serialize_x3f_1779_, v_a_831__boxed_1782_, v___y_1781_);
return v_res_1783_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6___redArg(lean_object* v_keys_1784_, lean_object* v_i_1785_, lean_object* v_k_1786_){
_start:
{
lean_object* v___x_1787_; uint8_t v___x_1788_; 
v___x_1787_ = lean_array_get_size(v_keys_1784_);
v___x_1788_ = lean_nat_dec_lt(v_i_1785_, v___x_1787_);
if (v___x_1788_ == 0)
{
lean_dec(v_i_1785_);
return v___x_1788_;
}
else
{
lean_object* v_k_x27_1789_; uint8_t v___x_1790_; 
v_k_x27_1789_ = lean_array_fget_borrowed(v_keys_1784_, v_i_1785_);
v___x_1790_ = lean_string_dec_eq(v_k_1786_, v_k_x27_1789_);
if (v___x_1790_ == 0)
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = lean_unsigned_to_nat(1u);
v___x_1792_ = lean_nat_add(v_i_1785_, v___x_1791_);
lean_dec(v_i_1785_);
v_i_1785_ = v___x_1792_;
goto _start;
}
else
{
lean_dec(v_i_1785_);
return v___x_1790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_keys_1794_, lean_object* v_i_1795_, lean_object* v_k_1796_){
_start:
{
uint8_t v_res_1797_; lean_object* v_r_1798_; 
v_res_1797_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6___redArg(v_keys_1794_, v_i_1795_, v_k_1796_);
lean_dec_ref(v_k_1796_);
lean_dec_ref(v_keys_1794_);
v_r_1798_ = lean_box(v_res_1797_);
return v_r_1798_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0(void){
_start:
{
size_t v___x_1799_; size_t v___x_1800_; size_t v___x_1801_; 
v___x_1799_ = ((size_t)5ULL);
v___x_1800_ = ((size_t)1ULL);
v___x_1801_ = lean_usize_shift_left(v___x_1800_, v___x_1799_);
return v___x_1801_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_1802_; size_t v___x_1803_; size_t v___x_1804_; 
v___x_1802_ = ((size_t)1ULL);
v___x_1803_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0);
v___x_1804_ = lean_usize_sub(v___x_1803_, v___x_1802_);
return v___x_1804_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(lean_object* v_x_1805_, size_t v_x_1806_, lean_object* v_x_1807_){
_start:
{
if (lean_obj_tag(v_x_1805_) == 0)
{
lean_object* v_es_1808_; lean_object* v___x_1809_; size_t v___x_1810_; size_t v___x_1811_; size_t v___x_1812_; lean_object* v_j_1813_; lean_object* v___x_1814_; 
v_es_1808_ = lean_ctor_get(v_x_1805_, 0);
lean_inc_ref(v_es_1808_);
lean_dec_ref(v_x_1805_);
v___x_1809_ = lean_box(2);
v___x_1810_ = ((size_t)5ULL);
v___x_1811_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__1);
v___x_1812_ = lean_usize_land(v_x_1806_, v___x_1811_);
v_j_1813_ = lean_usize_to_nat(v___x_1812_);
v___x_1814_ = lean_array_get(v___x_1809_, v_es_1808_, v_j_1813_);
lean_dec(v_j_1813_);
lean_dec_ref(v_es_1808_);
switch(lean_obj_tag(v___x_1814_))
{
case 0:
{
lean_object* v_key_1815_; uint8_t v___x_1816_; 
v_key_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_key_1815_);
lean_dec_ref(v___x_1814_);
v___x_1816_ = lean_string_dec_eq(v_x_1807_, v_key_1815_);
lean_dec(v_key_1815_);
return v___x_1816_;
}
case 1:
{
lean_object* v_node_1817_; size_t v___x_1818_; 
v_node_1817_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_node_1817_);
lean_dec_ref(v___x_1814_);
v___x_1818_ = lean_usize_shift_right(v_x_1806_, v___x_1810_);
v_x_1805_ = v_node_1817_;
v_x_1806_ = v___x_1818_;
goto _start;
}
default: 
{
uint8_t v___x_1820_; 
v___x_1820_ = 0;
return v___x_1820_;
}
}
}
else
{
lean_object* v_ks_1821_; lean_object* v___x_1822_; uint8_t v___x_1823_; 
v_ks_1821_ = lean_ctor_get(v_x_1805_, 0);
lean_inc_ref(v_ks_1821_);
lean_dec_ref(v_x_1805_);
v___x_1822_ = lean_unsigned_to_nat(0u);
v___x_1823_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6___redArg(v_ks_1821_, v___x_1822_, v_x_1807_);
lean_dec_ref(v_ks_1821_);
return v___x_1823_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(lean_object* v_x_1824_, lean_object* v_x_1825_, lean_object* v_x_1826_){
_start:
{
size_t v_x_926__boxed_1827_; uint8_t v_res_1828_; lean_object* v_r_1829_; 
v_x_926__boxed_1827_ = lean_unbox_usize(v_x_1825_);
lean_dec(v_x_1825_);
v_res_1828_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_1824_, v_x_926__boxed_1827_, v_x_1826_);
lean_dec_ref(v_x_1826_);
v_r_1829_ = lean_box(v_res_1828_);
return v_r_1829_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3___redArg(lean_object* v_x_1830_, lean_object* v_x_1831_){
_start:
{
uint64_t v___x_1832_; size_t v___x_1833_; uint8_t v___x_1834_; 
v___x_1832_ = lean_string_hash(v_x_1831_);
v___x_1833_ = lean_uint64_to_usize(v___x_1832_);
v___x_1834_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_1830_, v___x_1833_, v_x_1831_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3___redArg___boxed(lean_object* v_x_1835_, lean_object* v_x_1836_){
_start:
{
uint8_t v_res_1837_; lean_object* v_r_1838_; 
v_res_1837_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3___redArg(v_x_1835_, v_x_1836_);
lean_dec_ref(v_x_1836_);
v_r_1838_ = lean_box(v_res_1837_);
return v_r_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9_spec__10___redArg(lean_object* v_x_1839_, lean_object* v_x_1840_, lean_object* v_x_1841_, lean_object* v_x_1842_){
_start:
{
lean_object* v_ks_1843_; lean_object* v_vs_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1868_; 
v_ks_1843_ = lean_ctor_get(v_x_1839_, 0);
v_vs_1844_ = lean_ctor_get(v_x_1839_, 1);
v_isSharedCheck_1868_ = !lean_is_exclusive(v_x_1839_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1846_ = v_x_1839_;
v_isShared_1847_ = v_isSharedCheck_1868_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_vs_1844_);
lean_inc(v_ks_1843_);
lean_dec(v_x_1839_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1868_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1848_; uint8_t v___x_1849_; 
v___x_1848_ = lean_array_get_size(v_ks_1843_);
v___x_1849_ = lean_nat_dec_lt(v_x_1840_, v___x_1848_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1853_; 
lean_dec(v_x_1840_);
v___x_1850_ = lean_array_push(v_ks_1843_, v_x_1841_);
v___x_1851_ = lean_array_push(v_vs_1844_, v_x_1842_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 1, v___x_1851_);
lean_ctor_set(v___x_1846_, 0, v___x_1850_);
v___x_1853_ = v___x_1846_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1850_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
else
{
lean_object* v_k_x27_1855_; uint8_t v___x_1856_; 
v_k_x27_1855_ = lean_array_fget_borrowed(v_ks_1843_, v_x_1840_);
v___x_1856_ = lean_string_dec_eq(v_x_1841_, v_k_x27_1855_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1858_; 
if (v_isShared_1847_ == 0)
{
v___x_1858_ = v___x_1846_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_ks_1843_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v_vs_1844_);
v___x_1858_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = lean_unsigned_to_nat(1u);
v___x_1860_ = lean_nat_add(v_x_1840_, v___x_1859_);
lean_dec(v_x_1840_);
v_x_1839_ = v___x_1858_;
v_x_1840_ = v___x_1860_;
goto _start;
}
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1866_; 
v___x_1863_ = lean_array_fset(v_ks_1843_, v_x_1840_, v_x_1841_);
v___x_1864_ = lean_array_fset(v_vs_1844_, v_x_1840_, v_x_1842_);
lean_dec(v_x_1840_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 1, v___x_1864_);
lean_ctor_set(v___x_1846_, 0, v___x_1863_);
v___x_1866_ = v___x_1846_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1863_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9___redArg(lean_object* v_n_1869_, lean_object* v_k_1870_, lean_object* v_v_1871_){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = lean_unsigned_to_nat(0u);
v___x_1873_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9_spec__10___redArg(v_n_1869_, v___x_1872_, v_k_1870_, v_v_1871_);
return v___x_1873_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg(lean_object* v_x_1875_, size_t v_x_1876_, size_t v_x_1877_, lean_object* v_x_1878_, lean_object* v_x_1879_){
_start:
{
if (lean_obj_tag(v_x_1875_) == 0)
{
lean_object* v_es_1880_; size_t v___x_1881_; size_t v___x_1882_; size_t v___x_1883_; size_t v___x_1884_; lean_object* v_j_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; 
v_es_1880_ = lean_ctor_get(v_x_1875_, 0);
v___x_1881_ = ((size_t)5ULL);
v___x_1882_ = ((size_t)1ULL);
v___x_1883_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__1);
v___x_1884_ = lean_usize_land(v_x_1876_, v___x_1883_);
v_j_1885_ = lean_usize_to_nat(v___x_1884_);
v___x_1886_ = lean_array_get_size(v_es_1880_);
v___x_1887_ = lean_nat_dec_lt(v_j_1885_, v___x_1886_);
if (v___x_1887_ == 0)
{
lean_dec(v_j_1885_);
lean_dec(v_x_1879_);
lean_dec_ref(v_x_1878_);
return v_x_1875_;
}
else
{
lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1924_; 
lean_inc_ref(v_es_1880_);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_x_1875_);
if (v_isSharedCheck_1924_ == 0)
{
lean_object* v_unused_1925_; 
v_unused_1925_ = lean_ctor_get(v_x_1875_, 0);
lean_dec(v_unused_1925_);
v___x_1889_ = v_x_1875_;
v_isShared_1890_ = v_isSharedCheck_1924_;
goto v_resetjp_1888_;
}
else
{
lean_dec(v_x_1875_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1924_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v_v_1891_; lean_object* v___x_1892_; lean_object* v_xs_x27_1893_; lean_object* v___y_1895_; 
v_v_1891_ = lean_array_fget(v_es_1880_, v_j_1885_);
v___x_1892_ = lean_box(0);
v_xs_x27_1893_ = lean_array_fset(v_es_1880_, v_j_1885_, v___x_1892_);
switch(lean_obj_tag(v_v_1891_))
{
case 0:
{
lean_object* v_key_1900_; lean_object* v_val_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1911_; 
v_key_1900_ = lean_ctor_get(v_v_1891_, 0);
v_val_1901_ = lean_ctor_get(v_v_1891_, 1);
v_isSharedCheck_1911_ = !lean_is_exclusive(v_v_1891_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1903_ = v_v_1891_;
v_isShared_1904_ = v_isSharedCheck_1911_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_val_1901_);
lean_inc(v_key_1900_);
lean_dec(v_v_1891_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1911_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
uint8_t v___x_1905_; 
v___x_1905_ = lean_string_dec_eq(v_x_1878_, v_key_1900_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
lean_del_object(v___x_1903_);
v___x_1906_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1900_, v_val_1901_, v_x_1878_, v_x_1879_);
v___x_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
v___y_1895_ = v___x_1907_;
goto v___jp_1894_;
}
else
{
lean_object* v___x_1909_; 
lean_dec(v_val_1901_);
lean_dec(v_key_1900_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 1, v_x_1879_);
lean_ctor_set(v___x_1903_, 0, v_x_1878_);
v___x_1909_ = v___x_1903_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_x_1878_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v_x_1879_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
v___y_1895_ = v___x_1909_;
goto v___jp_1894_;
}
}
}
}
case 1:
{
lean_object* v_node_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1922_; 
v_node_1912_ = lean_ctor_get(v_v_1891_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v_v_1891_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1914_ = v_v_1891_;
v_isShared_1915_ = v_isSharedCheck_1922_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_node_1912_);
lean_dec(v_v_1891_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1922_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
size_t v___x_1916_; size_t v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___x_1916_ = lean_usize_shift_right(v_x_1876_, v___x_1881_);
v___x_1917_ = lean_usize_add(v_x_1877_, v___x_1882_);
v___x_1918_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg(v_node_1912_, v___x_1916_, v___x_1917_, v_x_1878_, v_x_1879_);
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 0, v___x_1918_);
v___x_1920_ = v___x_1914_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1918_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
v___y_1895_ = v___x_1920_;
goto v___jp_1894_;
}
}
}
default: 
{
lean_object* v___x_1923_; 
v___x_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1923_, 0, v_x_1878_);
lean_ctor_set(v___x_1923_, 1, v_x_1879_);
v___y_1895_ = v___x_1923_;
goto v___jp_1894_;
}
}
v___jp_1894_:
{
lean_object* v___x_1896_; lean_object* v___x_1898_; 
v___x_1896_ = lean_array_fset(v_xs_x27_1893_, v_j_1885_, v___y_1895_);
lean_dec(v_j_1885_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v___x_1896_);
v___x_1898_ = v___x_1889_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1896_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
}
else
{
lean_object* v_ks_1926_; lean_object* v_vs_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1947_; 
v_ks_1926_ = lean_ctor_get(v_x_1875_, 0);
v_vs_1927_ = lean_ctor_get(v_x_1875_, 1);
v_isSharedCheck_1947_ = !lean_is_exclusive(v_x_1875_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1929_ = v_x_1875_;
v_isShared_1930_ = v_isSharedCheck_1947_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_vs_1927_);
lean_inc(v_ks_1926_);
lean_dec(v_x_1875_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1947_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_ks_1926_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_vs_1927_);
v___x_1932_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v_newNode_1933_; uint8_t v___y_1935_; size_t v___x_1941_; uint8_t v___x_1942_; 
v_newNode_1933_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9___redArg(v___x_1932_, v_x_1878_, v_x_1879_);
v___x_1941_ = ((size_t)7ULL);
v___x_1942_ = lean_usize_dec_le(v___x_1941_, v_x_1877_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; 
v___x_1943_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1933_);
v___x_1944_ = lean_unsigned_to_nat(4u);
v___x_1945_ = lean_nat_dec_lt(v___x_1943_, v___x_1944_);
lean_dec(v___x_1943_);
v___y_1935_ = v___x_1945_;
goto v___jp_1934_;
}
else
{
v___y_1935_ = v___x_1942_;
goto v___jp_1934_;
}
v___jp_1934_:
{
if (v___y_1935_ == 0)
{
lean_object* v_ks_1936_; lean_object* v_vs_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v_ks_1936_ = lean_ctor_get(v_newNode_1933_, 0);
lean_inc_ref(v_ks_1936_);
v_vs_1937_ = lean_ctor_get(v_newNode_1933_, 1);
lean_inc_ref(v_vs_1937_);
lean_dec_ref(v_newNode_1933_);
v___x_1938_ = lean_unsigned_to_nat(0u);
v___x_1939_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg___closed__0);
v___x_1940_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10___redArg(v_x_1877_, v_ks_1936_, v_vs_1937_, v___x_1938_, v___x_1939_);
lean_dec_ref(v_vs_1937_);
lean_dec_ref(v_ks_1936_);
return v___x_1940_;
}
else
{
return v_newNode_1933_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10___redArg(size_t v_depth_1948_, lean_object* v_keys_1949_, lean_object* v_vals_1950_, lean_object* v_i_1951_, lean_object* v_entries_1952_){
_start:
{
lean_object* v___x_1953_; uint8_t v___x_1954_; 
v___x_1953_ = lean_array_get_size(v_keys_1949_);
v___x_1954_ = lean_nat_dec_lt(v_i_1951_, v___x_1953_);
if (v___x_1954_ == 0)
{
lean_dec(v_i_1951_);
return v_entries_1952_;
}
else
{
lean_object* v_k_1955_; lean_object* v_v_1956_; uint64_t v___x_1957_; size_t v_h_1958_; size_t v___x_1959_; lean_object* v___x_1960_; size_t v___x_1961_; size_t v___x_1962_; size_t v___x_1963_; size_t v_h_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v_k_1955_ = lean_array_fget_borrowed(v_keys_1949_, v_i_1951_);
v_v_1956_ = lean_array_fget_borrowed(v_vals_1950_, v_i_1951_);
v___x_1957_ = lean_string_hash(v_k_1955_);
v_h_1958_ = lean_uint64_to_usize(v___x_1957_);
v___x_1959_ = ((size_t)5ULL);
v___x_1960_ = lean_unsigned_to_nat(1u);
v___x_1961_ = ((size_t)1ULL);
v___x_1962_ = lean_usize_sub(v_depth_1948_, v___x_1961_);
v___x_1963_ = lean_usize_mul(v___x_1959_, v___x_1962_);
v_h_1964_ = lean_usize_shift_right(v_h_1958_, v___x_1963_);
v___x_1965_ = lean_nat_add(v_i_1951_, v___x_1960_);
lean_dec(v_i_1951_);
lean_inc(v_v_1956_);
lean_inc(v_k_1955_);
v___x_1966_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg(v_entries_1952_, v_h_1964_, v_depth_1948_, v_k_1955_, v_v_1956_);
v_i_1951_ = v___x_1965_;
v_entries_1952_ = v___x_1966_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_depth_1968_, lean_object* v_keys_1969_, lean_object* v_vals_1970_, lean_object* v_i_1971_, lean_object* v_entries_1972_){
_start:
{
size_t v_depth_boxed_1973_; lean_object* v_res_1974_; 
v_depth_boxed_1973_ = lean_unbox_usize(v_depth_1968_);
lean_dec(v_depth_1968_);
v_res_1974_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10___redArg(v_depth_boxed_1973_, v_keys_1969_, v_vals_1970_, v_i_1971_, v_entries_1972_);
lean_dec_ref(v_vals_1970_);
lean_dec_ref(v_keys_1969_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg___boxed(lean_object* v_x_1975_, lean_object* v_x_1976_, lean_object* v_x_1977_, lean_object* v_x_1978_, lean_object* v_x_1979_){
_start:
{
size_t v_x_1067__boxed_1980_; size_t v_x_1068__boxed_1981_; lean_object* v_res_1982_; 
v_x_1067__boxed_1980_ = lean_unbox_usize(v_x_1976_);
lean_dec(v_x_1976_);
v_x_1068__boxed_1981_ = lean_unbox_usize(v_x_1977_);
lean_dec(v_x_1977_);
v_res_1982_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg(v_x_1975_, v_x_1067__boxed_1980_, v_x_1068__boxed_1981_, v_x_1978_, v_x_1979_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4___redArg(lean_object* v_x_1983_, lean_object* v_x_1984_, lean_object* v_x_1985_){
_start:
{
uint64_t v___x_1986_; size_t v___x_1987_; size_t v___x_1988_; lean_object* v___x_1989_; 
v___x_1986_ = lean_string_hash(v_x_1984_);
v___x_1987_ = lean_uint64_to_usize(v___x_1986_);
v___x_1988_ = ((size_t)1ULL);
v___x_1989_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg(v_x_1983_, v___x_1987_, v___x_1988_, v_x_1984_, v_x_1985_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_params_1992_){
_start:
{
lean_object* v___x_1993_; 
lean_inc(v_params_1992_);
v___x_1993_ = l_Lean_Lsp_instFromJsonCodeActionParams_fromJson(v_params_1992_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2009_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_1996_ = v___x_1993_;
v_isShared_1997_ = v_isSharedCheck_2009_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1993_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2009_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
uint8_t v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_1998_ = 3;
v___x_1999_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__0));
v___x_2000_ = l_Lean_Json_compress(v_params_1992_);
v___x_2001_ = lean_string_append(v___x_1999_, v___x_2000_);
lean_dec_ref(v___x_2000_);
v___x_2002_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__1));
v___x_2003_ = lean_string_append(v___x_2001_, v___x_2002_);
v___x_2004_ = lean_string_append(v___x_2003_, v_a_1994_);
lean_dec(v_a_1994_);
v___x_2005_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2005_, 0, v___x_2004_);
lean_ctor_set_uint8(v___x_2005_, sizeof(void*)*1, v___x_1998_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 0, v___x_2005_);
v___x_2007_ = v___x_1996_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
else
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
lean_dec(v_params_1992_);
v_a_2010_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2012_ = v___x_1993_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_1993_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_params_2018_){
_start:
{
lean_object* v___x_2020_; 
v___x_2020_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0(v_params_2018_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_2020_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2020_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
lean_ctor_set_tag(v___x_2023_, 1);
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2021_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
v_a_2029_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2020_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2020_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
lean_ctor_set_tag(v___x_2031_, 0);
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_params_2037_, lean_object* v_a_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_2037_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__2(lean_object* v_handler_2040_, lean_object* v___f_2041_, lean_object* v_j_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v___x_2045_; 
v___x_2045_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1___redArg(v_j_2042_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2047_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2046_);
lean_dec_ref(v___x_2045_);
v___x_2047_ = lean_apply_3(v_handler_2040_, v_a_2046_, v___y_2043_, lean_box(0));
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2056_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2050_ = v___x_2047_;
v_isShared_2051_ = v_isSharedCheck_2056_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2047_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2056_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2052_; lean_object* v___x_2054_; 
v___x_2052_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2041_, v_a_2048_);
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 0, v___x_2052_);
v___x_2054_ = v___x_2050_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec_ref(v___f_2041_);
v_a_2057_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2047_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2047_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
lean_dec_ref(v___y_2043_);
lean_dec_ref(v___f_2041_);
lean_dec_ref(v_handler_2040_);
v_a_2065_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2045_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2045_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object* v_handler_2073_, lean_object* v___f_2074_, lean_object* v_j_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__2(v_handler_2073_, v___f_2074_, v_j_2075_, v___y_2076_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__0(lean_object* v_j_2079_){
_start:
{
lean_object* v___x_2080_; 
v___x_2080_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0(v_j_2079_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2080_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2080_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2097_; 
v_a_2089_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2091_ = v___x_2080_;
v_isShared_2092_ = v_isSharedCheck_2097_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2080_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2097_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v_textDocument_2093_; lean_object* v___x_2095_; 
v_textDocument_2093_ = lean_ctor_get(v_a_2089_, 2);
lean_inc_ref(v_textDocument_2093_);
lean_dec(v_a_2089_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 0, v_textDocument_2093_);
v___x_2095_ = v___x_2091_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_textDocument_2093_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0(lean_object* v_method_2102_, lean_object* v_handler_2103_, lean_object* v_serialize_x3f_2104_){
_start:
{
lean_object* v___x_2106_; 
v___x_2106_ = l_Lean_initializing();
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2141_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2109_ = v___x_2106_;
v_isShared_2110_ = v_isSharedCheck_2141_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2106_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2141_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
uint8_t v___x_2111_; 
v___x_2111_ = lean_unbox(v_a_2107_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2118_; 
lean_dec(v_a_2107_);
lean_dec(v_serialize_x3f_2104_);
lean_dec_ref(v_handler_2103_);
v___x_2112_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__0));
v___x_2113_ = lean_string_append(v___x_2112_, v_method_2102_);
lean_dec_ref(v_method_2102_);
v___x_2114_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__1));
v___x_2115_ = lean_string_append(v___x_2113_, v___x_2114_);
v___x_2116_ = lean_mk_io_user_error(v___x_2115_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set_tag(v___x_2109_, 1);
lean_ctor_set(v___x_2109_, 0, v___x_2116_);
v___x_2118_ = v___x_2109_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2116_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
else
{
lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; 
v___x_2120_ = l_Lean_Server_requestHandlers;
v___x_2121_ = lean_st_ref_get(v___x_2120_);
v___x_2122_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_2121_, v_method_2102_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; lean_object* v___f_2124_; lean_object* v___f_2125_; lean_object* v___f_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2131_; 
v___x_2123_ = lean_st_ref_take(v___x_2120_);
v___f_2124_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__2));
v___f_2125_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2125_, 0, v_serialize_x3f_2104_);
lean_closure_set(v___f_2125_, 1, v_a_2107_);
v___f_2126_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_2126_, 0, v_handler_2103_);
lean_closure_set(v___f_2126_, 1, v___f_2125_);
v___x_2127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___f_2124_);
lean_ctor_set(v___x_2127_, 1, v___f_2126_);
v___x_2128_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4___redArg(v___x_2123_, v_method_2102_, v___x_2127_);
v___x_2129_ = lean_st_ref_set(v___x_2120_, v___x_2128_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v___x_2129_);
v___x_2131_ = v___x_2109_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
else
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2139_; 
lean_dec(v_a_2107_);
lean_dec(v_serialize_x3f_2104_);
lean_dec_ref(v_handler_2103_);
v___x_2133_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__0));
v___x_2134_ = lean_string_append(v___x_2133_, v_method_2102_);
lean_dec_ref(v_method_2102_);
v___x_2135_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__3));
v___x_2136_ = lean_string_append(v___x_2134_, v___x_2135_);
v___x_2137_ = lean_mk_io_user_error(v___x_2136_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set_tag(v___x_2109_, 1);
lean_ctor_set(v___x_2109_, 0, v___x_2137_);
v___x_2139_ = v___x_2109_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2137_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_dec(v_serialize_x3f_2104_);
lean_dec_ref(v_handler_2103_);
lean_dec_ref(v_method_2102_);
v_a_2142_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2106_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2106_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_2150_, lean_object* v_handler_2151_, lean_object* v_serialize_x3f_2152_, lean_object* v_a_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0(v_method_2150_, v_handler_2151_, v_serialize_x3f_2152_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2158_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2_));
v___x_2159_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2_));
v___x_2160_ = lean_box(0);
v___x_2161_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0(v___x_2158_, v___x_2159_, v___x_2160_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2____boxed(lean_object* v_a_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2_();
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_params_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v___x_2167_; 
v___x_2167_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_2164_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_params_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1(v_params_2168_, v_a_2169_);
lean_dec_ref(v_a_2169_);
return v_res_2171_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3(lean_object* v_00_u03b2_2172_, lean_object* v_x_2173_, lean_object* v_x_2174_){
_start:
{
uint8_t v___x_2175_; 
v___x_2175_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3___redArg(v_x_2173_, v_x_2174_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3___boxed(lean_object* v_00_u03b2_2176_, lean_object* v_x_2177_, lean_object* v_x_2178_){
_start:
{
uint8_t v_res_2179_; lean_object* v_r_2180_; 
v_res_2179_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3(v_00_u03b2_2176_, v_x_2177_, v_x_2178_);
lean_dec_ref(v_x_2178_);
v_r_2180_ = lean_box(v_res_2179_);
return v_r_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4(lean_object* v_00_u03b2_2181_, lean_object* v_x_2182_, lean_object* v_x_2183_, lean_object* v_x_2184_){
_start:
{
lean_object* v___x_2185_; 
v___x_2185_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4___redArg(v_x_2182_, v_x_2183_, v_x_2184_);
return v___x_2185_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_object* v_00_u03b2_2186_, lean_object* v_x_2187_, size_t v_x_2188_, lean_object* v_x_2189_){
_start:
{
uint8_t v___x_2190_; 
v___x_2190_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_2187_, v_x_2188_, v_x_2189_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(lean_object* v_00_u03b2_2191_, lean_object* v_x_2192_, lean_object* v_x_2193_, lean_object* v_x_2194_){
_start:
{
size_t v_x_1574__boxed_2195_; uint8_t v_res_2196_; lean_object* v_r_2197_; 
v_x_1574__boxed_2195_ = lean_unbox_usize(v_x_2193_);
lean_dec(v_x_2193_);
v_res_2196_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5(v_00_u03b2_2191_, v_x_2192_, v_x_1574__boxed_2195_, v_x_2194_);
lean_dec_ref(v_x_2194_);
v_r_2197_ = lean_box(v_res_2196_);
return v_r_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7(lean_object* v_00_u03b2_2198_, lean_object* v_x_2199_, size_t v_x_2200_, size_t v_x_2201_, lean_object* v_x_2202_, lean_object* v_x_2203_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg(v_x_2199_, v_x_2200_, v_x_2201_, v_x_2202_, v_x_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___boxed(lean_object* v_00_u03b2_2205_, lean_object* v_x_2206_, lean_object* v_x_2207_, lean_object* v_x_2208_, lean_object* v_x_2209_, lean_object* v_x_2210_){
_start:
{
size_t v_x_1585__boxed_2211_; size_t v_x_1586__boxed_2212_; lean_object* v_res_2213_; 
v_x_1585__boxed_2211_ = lean_unbox_usize(v_x_2207_);
lean_dec(v_x_2207_);
v_x_1586__boxed_2212_ = lean_unbox_usize(v_x_2208_);
lean_dec(v_x_2208_);
v_res_2213_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7(v_00_u03b2_2205_, v_x_2206_, v_x_1585__boxed_2211_, v_x_1586__boxed_2212_, v_x_2209_, v_x_2210_);
return v_res_2213_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_2214_, lean_object* v_keys_2215_, lean_object* v_vals_2216_, lean_object* v_heq_2217_, lean_object* v_i_2218_, lean_object* v_k_2219_){
_start:
{
uint8_t v___x_2220_; 
v___x_2220_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6___redArg(v_keys_2215_, v_i_2218_, v_k_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6___boxed(lean_object* v_00_u03b2_2221_, lean_object* v_keys_2222_, lean_object* v_vals_2223_, lean_object* v_heq_2224_, lean_object* v_i_2225_, lean_object* v_k_2226_){
_start:
{
uint8_t v_res_2227_; lean_object* v_r_2228_; 
v_res_2227_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6(v_00_u03b2_2221_, v_keys_2222_, v_vals_2223_, v_heq_2224_, v_i_2225_, v_k_2226_);
lean_dec_ref(v_k_2226_);
lean_dec_ref(v_vals_2223_);
lean_dec_ref(v_keys_2222_);
v_r_2228_ = lean_box(v_res_2227_);
return v_r_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9(lean_object* v_00_u03b2_2229_, lean_object* v_n_2230_, lean_object* v_k_2231_, lean_object* v_v_2232_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9___redArg(v_n_2230_, v_k_2231_, v_v_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10(lean_object* v_00_u03b2_2234_, size_t v_depth_2235_, lean_object* v_keys_2236_, lean_object* v_vals_2237_, lean_object* v_heq_2238_, lean_object* v_i_2239_, lean_object* v_entries_2240_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10___redArg(v_depth_2235_, v_keys_2236_, v_vals_2237_, v_i_2239_, v_entries_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b2_2242_, lean_object* v_depth_2243_, lean_object* v_keys_2244_, lean_object* v_vals_2245_, lean_object* v_heq_2246_, lean_object* v_i_2247_, lean_object* v_entries_2248_){
_start:
{
size_t v_depth_boxed_2249_; lean_object* v_res_2250_; 
v_depth_boxed_2249_ = lean_unbox_usize(v_depth_2243_);
lean_dec(v_depth_2243_);
v_res_2250_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10(v_00_u03b2_2242_, v_depth_boxed_2249_, v_keys_2244_, v_vals_2245_, v_heq_2246_, v_i_2247_, v_entries_2248_);
lean_dec_ref(v_vals_2245_);
lean_dec_ref(v_keys_2244_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9_spec__10(lean_object* v_00_u03b2_2251_, lean_object* v_x_2252_, lean_object* v_x_2253_, lean_object* v_x_2254_, lean_object* v_x_2255_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9_spec__10___redArg(v_x_2252_, v_x_2253_, v_x_2254_, v_x_2255_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeActionResolve___lam__0(lean_object* v_params_2258_, lean_object* v_providerResultIndex_2259_, lean_object* v_param_2260_, lean_object* v_providerName_2261_, lean_object* v_snap_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v_cap_2266_; lean_object* v___y_2267_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2317_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_builtinCodeActionProviders;
v___x_2318_ = lean_st_ref_get(v___x_2317_);
v___x_2319_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2318_, v_providerName_2261_);
lean_dec(v___x_2318_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2320_ = lean_alloc_closure((void*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2___boxed), 5, 1);
lean_closure_set(v___x_2320_, 0, v_providerName_2261_);
lean_inc_ref(v___y_2263_);
lean_inc_ref(v_snap_2262_);
v___x_2321_ = l_Lean_Server_RequestM_runCoreM___redArg(v_snap_2262_, v___x_2320_, v___y_2263_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2322_);
lean_dec_ref(v___x_2321_);
v_cap_2266_ = v_a_2322_;
v___y_2267_ = v___y_2263_;
goto v___jp_2265_;
}
else
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
lean_dec_ref(v___y_2263_);
lean_dec_ref(v_snap_2262_);
lean_dec_ref(v_param_2260_);
lean_dec(v_providerResultIndex_2259_);
lean_dec_ref(v_params_2258_);
v_a_2323_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___x_2321_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2321_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
}
else
{
lean_object* v_val_2331_; 
lean_dec(v_providerName_2261_);
v_val_2331_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_val_2331_);
lean_dec_ref(v___x_2319_);
v_cap_2266_ = v_val_2331_;
v___y_2267_ = v___y_2263_;
goto v___jp_2265_;
}
v___jp_2265_:
{
lean_object* v___x_2268_; 
v___x_2268_ = lean_apply_4(v_cap_2266_, v_params_2258_, v_snap_2262_, v___y_2267_, lean_box(0));
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2308_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2271_ = v___x_2268_;
v_isShared_2272_ = v_isSharedCheck_2308_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2268_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2308_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2273_; uint8_t v___x_2274_; 
v___x_2273_ = lean_array_get_size(v_a_2269_);
v___x_2274_ = lean_nat_dec_lt(v_providerResultIndex_2259_, v___x_2273_);
if (v___x_2274_ == 0)
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2282_; 
lean_dec(v_a_2269_);
lean_dec_ref(v_param_2260_);
v___x_2275_ = ((lean_object*)(l_Lean_Server_handleCodeActionResolve___lam__0___closed__0));
v___x_2276_ = l_Nat_reprFast(v_providerResultIndex_2259_);
v___x_2277_ = lean_string_append(v___x_2275_, v___x_2276_);
lean_dec_ref(v___x_2276_);
v___x_2278_ = ((lean_object*)(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__5));
v___x_2279_ = lean_string_append(v___x_2277_, v___x_2278_);
v___x_2280_ = l_Lean_Server_RequestError_internalError(v___x_2279_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set_tag(v___x_2271_, 1);
lean_ctor_set(v___x_2271_, 0, v___x_2280_);
v___x_2282_ = v___x_2271_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___x_2280_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
else
{
lean_object* v___x_2284_; lean_object* v_lazy_x3f_2285_; 
v___x_2284_ = lean_array_fget(v_a_2269_, v_providerResultIndex_2259_);
lean_dec(v_providerResultIndex_2259_);
lean_dec(v_a_2269_);
v_lazy_x3f_2285_ = lean_ctor_get(v___x_2284_, 1);
lean_inc(v_lazy_x3f_2285_);
lean_dec(v___x_2284_);
if (lean_obj_tag(v_lazy_x3f_2285_) == 1)
{
lean_object* v_val_2286_; lean_object* v___x_2287_; 
lean_del_object(v___x_2271_);
lean_dec_ref(v_param_2260_);
v_val_2286_ = lean_ctor_get(v_lazy_x3f_2285_, 0);
lean_inc(v_val_2286_);
lean_dec_ref(v_lazy_x3f_2285_);
v___x_2287_ = lean_apply_1(v_val_2286_, lean_box(0));
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___x_2287_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2287_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
else
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2304_; 
v_a_2296_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2298_ = v___x_2287_;
v_isShared_2299_ = v_isSharedCheck_2304_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2287_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2304_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2300_; lean_object* v___x_2302_; 
v___x_2300_ = l_Lean_Server_RequestError_ofIoError(v_a_2296_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 0, v___x_2300_);
v___x_2302_ = v___x_2298_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
else
{
lean_object* v___x_2306_; 
lean_dec(v_lazy_x3f_2285_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 0, v_param_2260_);
v___x_2306_ = v___x_2271_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_param_2260_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
lean_dec_ref(v_param_2260_);
lean_dec(v_providerResultIndex_2259_);
v_a_2309_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2268_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2268_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeActionResolve___lam__0___boxed(lean_object* v_params_2332_, lean_object* v_providerResultIndex_2333_, lean_object* v_param_2334_, lean_object* v_providerName_2335_, lean_object* v_snap_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_Server_handleCodeActionResolve___lam__0(v_params_2332_, v_providerResultIndex_2333_, v_param_2334_, v_providerName_2335_, v_snap_2336_, v___y_2337_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeActionResolve___lam__2(lean_object* v___x_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v___x_2343_; 
v___x_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2340_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeActionResolve___lam__2___boxed(lean_object* v___x_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lean_Server_handleCodeActionResolve___lam__2(v___x_2344_, v___y_2345_);
lean_dec_ref(v___y_2345_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0_spec__0(lean_object* v_params_2348_){
_start:
{
lean_object* v___x_2349_; 
lean_inc(v_params_2348_);
v___x_2349_ = l_Lean_Server_instFromJsonCodeActionResolveData_fromJson(v_params_2348_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2365_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2352_ = v___x_2349_;
v_isShared_2353_ = v_isSharedCheck_2365_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2349_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2365_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
uint8_t v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2363_; 
v___x_2354_ = 3;
v___x_2355_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__0));
v___x_2356_ = l_Lean_Json_compress(v_params_2348_);
v___x_2357_ = lean_string_append(v___x_2355_, v___x_2356_);
lean_dec_ref(v___x_2356_);
v___x_2358_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__1));
v___x_2359_ = lean_string_append(v___x_2357_, v___x_2358_);
v___x_2360_ = lean_string_append(v___x_2359_, v_a_2350_);
lean_dec(v_a_2350_);
v___x_2361_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2361_, 0, v___x_2360_);
lean_ctor_set_uint8(v___x_2361_, sizeof(void*)*1, v___x_2354_);
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 0, v___x_2361_);
v___x_2363_ = v___x_2352_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec(v_params_2348_);
v_a_2366_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2349_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2349_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0___redArg(lean_object* v_params_2374_){
_start:
{
lean_object* v___x_2376_; 
v___x_2376_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0_spec__0(v_params_2374_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v___x_2376_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2376_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
lean_ctor_set_tag(v___x_2379_, 1);
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2392_; 
v_a_2385_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2387_ = v___x_2376_;
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2376_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
lean_ctor_set_tag(v___x_2387_, 0);
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2385_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0___redArg___boxed(lean_object* v_params_2393_, lean_object* v_a_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0___redArg(v_params_2393_);
return v_res_2395_;
}
}
static lean_object* _init_l_Lean_Server_handleCodeActionResolve___closed__1(void){
_start:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2397_ = ((lean_object*)(l_Lean_Server_handleCodeActionResolve___closed__0));
v___x_2398_ = l_Lean_Server_RequestError_internalError(v___x_2397_);
return v___x_2398_;
}
}
static lean_object* _init_l_Lean_Server_handleCodeActionResolve___closed__2(void){
_start:
{
lean_object* v___x_2399_; lean_object* v___f_2400_; 
v___x_2399_ = lean_obj_once(&l_Lean_Server_handleCodeActionResolve___closed__1, &l_Lean_Server_handleCodeActionResolve___closed__1_once, _init_l_Lean_Server_handleCodeActionResolve___closed__1);
v___f_2400_ = lean_alloc_closure((void*)(l_Lean_Server_handleCodeActionResolve___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2400_, 0, v___x_2399_);
return v___f_2400_;
}
}
static lean_object* _init_l_Lean_Server_handleCodeActionResolve___closed__4(void){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2402_ = ((lean_object*)(l_Lean_Server_handleCodeActionResolve___closed__3));
v___x_2403_ = l_Lean_Server_RequestError_invalidParams(v___x_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeActionResolve(lean_object* v_param_2404_, lean_object* v_a_2405_){
_start:
{
lean_object* v___x_2407_; lean_object* v_data_x3f_2408_; 
v___x_2407_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleCodeAction_spec__6(v_a_2405_);
v_data_x3f_2408_ = lean_ctor_get(v_param_2404_, 9);
if (lean_obj_tag(v_data_x3f_2408_) == 1)
{
lean_object* v_a_2409_; lean_object* v_val_2410_; lean_object* v___x_2411_; 
v_a_2409_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2409_);
lean_dec_ref(v___x_2407_);
v_val_2410_ = lean_ctor_get(v_data_x3f_2408_, 0);
lean_inc(v_val_2410_);
v___x_2411_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0___redArg(v_val_2410_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_toEditableDocumentCore_2412_; lean_object* v_meta_2413_; lean_object* v_a_2414_; lean_object* v_params_2415_; lean_object* v_range_2416_; lean_object* v_text_2417_; lean_object* v_providerName_2418_; lean_object* v_providerResultIndex_2419_; lean_object* v_end_2420_; lean_object* v___f_2421_; lean_object* v___x_2422_; lean_object* v___f_2423_; lean_object* v___f_2424_; lean_object* v___x_2425_; 
v_toEditableDocumentCore_2412_ = lean_ctor_get(v_a_2409_, 0);
v_meta_2413_ = lean_ctor_get(v_toEditableDocumentCore_2412_, 0);
v_a_2414_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_a_2414_);
lean_dec_ref(v___x_2411_);
v_params_2415_ = lean_ctor_get(v_a_2414_, 0);
lean_inc_ref(v_params_2415_);
v_range_2416_ = lean_ctor_get(v_params_2415_, 3);
v_text_2417_ = lean_ctor_get(v_meta_2413_, 3);
v_providerName_2418_ = lean_ctor_get(v_a_2414_, 1);
lean_inc(v_providerName_2418_);
v_providerResultIndex_2419_ = lean_ctor_get(v_a_2414_, 2);
lean_inc(v_providerResultIndex_2419_);
lean_dec(v_a_2414_);
v_end_2420_ = lean_ctor_get(v_range_2416_, 1);
lean_inc_ref(v_end_2420_);
v___f_2421_ = lean_alloc_closure((void*)(l_Lean_Server_handleCodeActionResolve___lam__0___boxed), 7, 4);
lean_closure_set(v___f_2421_, 0, v_params_2415_);
lean_closure_set(v___f_2421_, 1, v_providerResultIndex_2419_);
lean_closure_set(v___f_2421_, 2, v_param_2404_);
lean_closure_set(v___f_2421_, 3, v_providerName_2418_);
v___x_2422_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_2417_, v_end_2420_);
v___f_2423_ = lean_alloc_closure((void*)(l_Lean_Server_handleCodeAction___lam__2___boxed), 2, 1);
lean_closure_set(v___f_2423_, 0, v___x_2422_);
v___f_2424_ = lean_obj_once(&l_Lean_Server_handleCodeActionResolve___closed__2, &l_Lean_Server_handleCodeActionResolve___closed__2_once, _init_l_Lean_Server_handleCodeActionResolve___closed__2);
v___x_2425_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_a_2409_, v___f_2423_, v___f_2424_, v___f_2421_, v_a_2405_);
return v___x_2425_;
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
lean_dec(v_a_2409_);
lean_dec_ref(v_a_2405_);
lean_dec_ref(v_param_2404_);
v_a_2426_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2411_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2411_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
else
{
lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2441_; 
lean_dec_ref(v_a_2405_);
lean_dec_ref(v_param_2404_);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2441_ == 0)
{
lean_object* v_unused_2442_; 
v_unused_2442_ = lean_ctor_get(v___x_2407_, 0);
lean_dec(v_unused_2442_);
v___x_2435_ = v___x_2407_;
v_isShared_2436_ = v_isSharedCheck_2441_;
goto v_resetjp_2434_;
}
else
{
lean_dec(v___x_2407_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2441_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2437_; lean_object* v___x_2439_; 
v___x_2437_ = lean_obj_once(&l_Lean_Server_handleCodeActionResolve___closed__4, &l_Lean_Server_handleCodeActionResolve___closed__4_once, _init_l_Lean_Server_handleCodeActionResolve___closed__4);
if (v_isShared_2436_ == 0)
{
lean_ctor_set_tag(v___x_2435_, 1);
lean_ctor_set(v___x_2435_, 0, v___x_2437_);
v___x_2439_ = v___x_2435_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2437_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleCodeActionResolve___boxed(lean_object* v_param_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Lean_Server_handleCodeActionResolve(v_param_2443_, v_a_2444_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0(lean_object* v_params_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v___x_2450_; 
v___x_2450_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0___redArg(v_params_2447_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0___boxed(lean_object* v_params_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0(v_params_2451_, v_a_2452_);
lean_dec_ref(v_a_2452_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__1(lean_object* v_serialize_x3f_2455_, uint8_t v_a_2456_, lean_object* v___y_2457_){
_start:
{
if (lean_obj_tag(v___y_2457_) == 0)
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2465_; 
lean_dec(v_serialize_x3f_2455_);
v_a_2458_ = lean_ctor_get(v___y_2457_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___y_2457_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2460_ = v___y_2457_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___y_2457_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2458_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
else
{
if (lean_obj_tag(v_serialize_x3f_2455_) == 1)
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2477_; 
v_a_2466_ = lean_ctor_get(v___y_2457_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___y_2457_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2468_ = v___y_2457_;
v_isShared_2469_ = v_isSharedCheck_2477_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___y_2457_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2477_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v_val_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2475_; 
v_val_2470_ = lean_ctor_get(v_serialize_x3f_2455_, 0);
lean_inc(v_val_2470_);
lean_dec_ref(v_serialize_x3f_2455_);
v___x_2471_ = lean_box(0);
v___x_2472_ = lean_apply_1(v_val_2470_, v_a_2466_);
v___x_2473_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2473_, 0, v___x_2471_);
lean_ctor_set(v___x_2473_, 1, v___x_2472_);
lean_ctor_set_uint8(v___x_2473_, sizeof(void*)*2, v_a_2456_);
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 0, v___x_2473_);
v___x_2475_ = v___x_2468_;
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
else
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2489_; 
lean_dec(v_serialize_x3f_2455_);
v_a_2478_ = lean_ctor_get(v___y_2457_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___y_2457_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2480_ = v___y_2457_;
v_isShared_2481_ = v_isSharedCheck_2489_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___y_2457_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2489_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2487_; 
v___x_2482_ = l_Lean_Lsp_instToJsonCodeAction_toJson(v_a_2478_);
lean_inc(v___x_2482_);
v___x_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
v___x_2484_ = l_Lean_Json_compress(v___x_2482_);
v___x_2485_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2485_, 0, v___x_2483_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
lean_ctor_set_uint8(v___x_2485_, sizeof(void*)*2, v_a_2456_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v___x_2485_);
v___x_2487_ = v___x_2480_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2485_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object* v_serialize_x3f_2490_, lean_object* v_a_2491_, lean_object* v___y_2492_){
_start:
{
uint8_t v_a_275__boxed_2493_; lean_object* v_res_2494_; 
v_a_275__boxed_2493_ = lean_unbox(v_a_2491_);
v_res_2494_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__1(v_serialize_x3f_2490_, v_a_275__boxed_2493_, v___y_2492_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_params_2495_){
_start:
{
lean_object* v___x_2496_; 
lean_inc(v_params_2495_);
v___x_2496_ = l_Lean_Lsp_instFromJsonCodeAction_fromJson(v_params_2495_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2512_; 
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2499_ = v___x_2496_;
v_isShared_2500_ = v_isSharedCheck_2512_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2496_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2512_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
uint8_t v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2510_; 
v___x_2501_ = 3;
v___x_2502_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__0));
v___x_2503_ = l_Lean_Json_compress(v_params_2495_);
v___x_2504_ = lean_string_append(v___x_2502_, v___x_2503_);
lean_dec_ref(v___x_2503_);
v___x_2505_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__1));
v___x_2506_ = lean_string_append(v___x_2504_, v___x_2505_);
v___x_2507_ = lean_string_append(v___x_2506_, v_a_2497_);
lean_dec(v_a_2497_);
v___x_2508_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2508_, 0, v___x_2507_);
lean_ctor_set_uint8(v___x_2508_, sizeof(void*)*1, v___x_2501_);
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 0, v___x_2508_);
v___x_2510_ = v___x_2499_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2508_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
lean_dec(v_params_2495_);
v_a_2513_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2496_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2496_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_params_2521_){
_start:
{
lean_object* v___x_2523_; 
v___x_2523_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__0(v_params_2521_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2523_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2523_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
lean_ctor_set_tag(v___x_2526_, 1);
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
else
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
v_a_2532_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2534_ = v___x_2523_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2523_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
lean_ctor_set_tag(v___x_2534_, 0);
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2532_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_params_2540_, lean_object* v_a_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_2540_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__2(lean_object* v_handler_2543_, lean_object* v___f_2544_, lean_object* v_j_2545_, lean_object* v___y_2546_){
_start:
{
lean_object* v___x_2548_; 
v___x_2548_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1___redArg(v_j_2545_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v___x_2550_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref(v___x_2548_);
v___x_2550_ = lean_apply_3(v_handler_2543_, v_a_2549_, v___y_2546_, lean_box(0));
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2559_; 
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2553_ = v___x_2550_;
v_isShared_2554_ = v_isSharedCheck_2559_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2550_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2559_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2555_; lean_object* v___x_2557_; 
v___x_2555_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2544_, v_a_2551_);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 0, v___x_2555_);
v___x_2557_ = v___x_2553_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2555_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
else
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
lean_dec_ref(v___f_2544_);
v_a_2560_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2550_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2550_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
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
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
lean_dec_ref(v___y_2546_);
lean_dec_ref(v___f_2544_);
lean_dec_ref(v_handler_2543_);
v_a_2568_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2548_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2548_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object* v_handler_2576_, lean_object* v___f_2577_, lean_object* v_j_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__2(v_handler_2576_, v___f_2577_, v_j_2578_, v___y_2579_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__0(lean_object* v_j_2582_){
_start:
{
lean_object* v___x_2583_; 
v___x_2583_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__0(v_j_2582_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2591_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2586_ = v___x_2583_;
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2583_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2589_; 
if (v_isShared_2587_ == 0)
{
v___x_2589_ = v___x_2586_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2584_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2600_; 
v_a_2592_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2594_ = v___x_2583_;
v_isShared_2595_ = v_isSharedCheck_2600_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2583_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2600_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2596_; lean_object* v___x_2598_; 
v___x_2596_ = l_Lean_Server_CodeAction_getFileSource_x21(v_a_2592_);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v___x_2596_);
v___x_2598_ = v___x_2594_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2596_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0(lean_object* v_method_2602_, lean_object* v_handler_2603_, lean_object* v_serialize_x3f_2604_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l_Lean_initializing();
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2641_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2609_ = v___x_2606_;
v_isShared_2610_ = v_isSharedCheck_2641_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2606_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2641_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
uint8_t v___x_2611_; 
v___x_2611_ = lean_unbox(v_a_2607_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2618_; 
lean_dec(v_a_2607_);
lean_dec(v_serialize_x3f_2604_);
lean_dec_ref(v_handler_2603_);
v___x_2612_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__0));
v___x_2613_ = lean_string_append(v___x_2612_, v_method_2602_);
lean_dec_ref(v_method_2602_);
v___x_2614_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__1));
v___x_2615_ = lean_string_append(v___x_2613_, v___x_2614_);
v___x_2616_ = lean_mk_io_user_error(v___x_2615_);
if (v_isShared_2610_ == 0)
{
lean_ctor_set_tag(v___x_2609_, 1);
lean_ctor_set(v___x_2609_, 0, v___x_2616_);
v___x_2618_ = v___x_2609_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2616_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
else
{
lean_object* v___x_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; 
v___x_2620_ = l_Lean_Server_requestHandlers;
v___x_2621_ = lean_st_ref_get(v___x_2620_);
v___x_2622_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_2621_, v_method_2602_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; lean_object* v___f_2624_; lean_object* v___f_2625_; lean_object* v___f_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2631_; 
v___x_2623_ = lean_st_ref_take(v___x_2620_);
v___f_2624_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___closed__0));
v___f_2625_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2625_, 0, v_serialize_x3f_2604_);
lean_closure_set(v___f_2625_, 1, v_a_2607_);
v___f_2626_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_2626_, 0, v_handler_2603_);
lean_closure_set(v___f_2626_, 1, v___f_2625_);
v___x_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___f_2624_);
lean_ctor_set(v___x_2627_, 1, v___f_2626_);
v___x_2628_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4___redArg(v___x_2623_, v_method_2602_, v___x_2627_);
v___x_2629_ = lean_st_ref_set(v___x_2620_, v___x_2628_);
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 0, v___x_2629_);
v___x_2631_ = v___x_2609_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v___x_2629_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
else
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2639_; 
lean_dec(v_a_2607_);
lean_dec(v_serialize_x3f_2604_);
lean_dec_ref(v_handler_2603_);
v___x_2633_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__0));
v___x_2634_ = lean_string_append(v___x_2633_, v_method_2602_);
lean_dec_ref(v_method_2602_);
v___x_2635_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__3));
v___x_2636_ = lean_string_append(v___x_2634_, v___x_2635_);
v___x_2637_ = lean_mk_io_user_error(v___x_2636_);
if (v_isShared_2610_ == 0)
{
lean_ctor_set_tag(v___x_2609_, 1);
lean_ctor_set(v___x_2609_, 0, v___x_2637_);
v___x_2639_ = v___x_2609_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v___x_2637_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
}
else
{
lean_object* v_a_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2649_; 
lean_dec(v_serialize_x3f_2604_);
lean_dec_ref(v_handler_2603_);
lean_dec_ref(v_method_2602_);
v_a_2642_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2644_ = v___x_2606_;
v_isShared_2645_ = v_isSharedCheck_2649_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_a_2642_);
lean_dec(v___x_2606_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2649_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___x_2647_; 
if (v_isShared_2645_ == 0)
{
v___x_2647_ = v___x_2644_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_a_2642_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_2650_, lean_object* v_handler_2651_, lean_object* v_serialize_x3f_2652_, lean_object* v_a_2653_){
_start:
{
lean_object* v_res_2654_; 
v_res_2654_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0(v_method_2650_, v_handler_2651_, v_serialize_x3f_2652_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2658_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2_));
v___x_2659_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2_));
v___x_2660_ = lean_box(0);
v___x_2661_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0(v___x_2658_, v___x_2659_, v___x_2660_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2____boxed(lean_object* v_a_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2_();
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_params_2664_, lean_object* v_a_2665_){
_start:
{
lean_object* v___x_2667_; 
v___x_2667_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_2664_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_params_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1(v_params_2668_, v_a_2669_);
lean_dec_ref(v_a_2669_);
return v_res_2671_;
}
}
lean_object* runtime_initialize_Lean_Server_Requests(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_CodeActions_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Server_Requests(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_instInhabitedCodeActionProvider = _init_l_Lean_Server_instInhabitedCodeActionProvider();
lean_mark_persistent(l_Lean_Server_instInhabitedCodeActionProvider);
res = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_2573400817____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_builtinCodeActionProviders = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_builtinCodeActionProviders);
lean_dec_ref(res);
res = l_Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_();
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
