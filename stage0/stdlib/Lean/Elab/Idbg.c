// Lean compiler output
// Module: Lean.Elab.Idbg
// Imports: public import Lean.Elab.Do.Basic meta import Lean.Parser.Do import Std.Async.TCP
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
extern lean_object* l_Lean_Options_empty;
extern lean_object* l_Lean_KVMap_instValueNat;
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Do_doElemElabAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkMonadApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_exprToSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_inServer;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Std_Async_AsyncTask_block___redArg(lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_uv_tcp_send(lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_outOfBounds___redArg(lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
lean_object* lean_uv_tcp_recv(lean_object*, uint64_t);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_uv_tcp_shutdown(lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_mod(uint64_t, uint64_t);
uint64_t lean_uint64_add(uint64_t, uint64_t);
uint16_t lean_uint64_to_uint16(uint64_t);
lean_object* l_Std_Net_IPv4Addr_ofParts(uint8_t, uint8_t, uint8_t, uint8_t);
lean_object* l_List_range(lean_object*);
lean_object* l_IO_sleep(uint32_t);
lean_object* lean_uv_tcp_new();
lean_object* lean_uv_tcp_bind(lean_object*, lean_object*);
lean_object* lean_uv_tcp_listen(lean_object*, uint32_t);
lean_object* lean_uv_tcp_accept(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_IO_CancelToken_new();
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_defaultReportingRange(lean_object*);
lean_object* l_Lean_Core_logSnapshotTask___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setNondep(lean_object*, uint8_t);
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_ensureUnitAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_doElabToSyntax___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_stderr();
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
extern lean_object* l_Lean_Elab_Do_controlInfoElemAttribute;
extern lean_object* l_Lean_Elab_Do_instInhabitedControlInfo_default;
uint8_t l_Lean_Json_isNull(lean_object*);
lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
lean_object* lean_array_pop(lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Level_mvar___override(lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
lean_object* l_Lean_Level_imax___override(lean_object*, lean_object*);
lean_object* l_Lean_Level_max___override(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* lean_uv_tcp_connect(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameToJson___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameToJson___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameToJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameToJson___closed__1 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameToJson___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameToJson(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f_spec__0___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f_spec__0___closed__0_value;
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f_spec__0___closed__1 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "expected Name, got "};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "num expects 2 elements"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f___closed__1_value)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "str expects 2 elements"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f___closed__3_value)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f___closed__4 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f___closed__5 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f(lean_object*);
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__1 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "implicit"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__2 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__2_value)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__3 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "strictImplicit"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__4 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__4_value)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__5 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "instImplicit"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__6 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__6_value)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__7 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoFromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "expected BinderInfo, got "};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoFromJson_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoFromJson_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoFromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoFromJson_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoFromJson_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoFromJson_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoFromJson_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoFromJson_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoFromJson_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoFromJson_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoFromJson_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoFromJson_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoFromJson_x3f___closed__4 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoFromJson_x3f___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoFromJson_x3f(lean_object*);
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_literalToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "natVal"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_literalToJson___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_literalToJson___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_literalToJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "strVal"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_literalToJson___closed__1 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_literalToJson___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_literalToJson(lean_object*);
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_literalFromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "expected Literal, got "};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_literalFromJson_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_literalFromJson_x3f___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_literalFromJson_x3f(lean_object*);
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__1 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__2 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__3;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__4 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "max"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__5 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "imax"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__6 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "param"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__7 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mvar"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__8 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson(lean_object*);
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expected Level, got "};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "imax expects 2 elements"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f___closed__1_value)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "max expects 2 elements"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f___closed__3_value)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f___closed__4 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f___closed__5 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bvar"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "fvar"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__1 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "sort"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__2 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "const"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__3 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "levels"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__4 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__5 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lam"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__6 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__7 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "type"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__8 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "body"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__9 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bi"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__10 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "forallE"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__11 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "letE"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__12 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "value"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__13 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "nondep"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__14 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lit"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__15 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__15_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__16 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__16_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeName"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__17 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__17_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "idx"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__18 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__18_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "struct"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__19 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__19_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "expected Expr, got "};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "app expects 2 elements"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f___closed__1_value)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f(lean_object*);
LEAN_EXPORT uint16_t l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgPort(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgPort___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "the promise linked to the Async was dropped"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___closed__1_value;
static const lean_closure_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___closed__1_value)} };
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___closed__2_value;
static const lean_closure_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___closed__2_value)} };
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___closed__3 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "idbg: connection closed"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___closed__0_value)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___closed__1_value;
static const lean_closure_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___closed__1_value)} };
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___closed__2_value;
static const lean_closure_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___closed__2_value)} };
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "idbg: invalid header"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "idbg: invalid UTF-8"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___closed__2_value)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___closed__3 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "idbg: invalid length"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___closed__4 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___closed__4_value)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___closed__5 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__2;
static const lean_closure_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___lam__3___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___closed__1_value)} };
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__3 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__3_value;
static const lean_closure_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__3_value)} };
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__4 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgLoadEnv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgLoadEnv___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgLoadEnv___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgLoadEnv(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgLoadEnv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval_unsafe__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval_unsafe__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval_unsafe__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval_unsafe__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_idbg"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(113, 143, 231, 50, 41, 181, 42, 64)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "<idbg>"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__4;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__5;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__6;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__7 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__8 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__8_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__9 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__10 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__11;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__13;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__14;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__15;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__16;
static const lean_array_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__17 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__17_value;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__18;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__19;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__20;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__21;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "idbg evalConst failed: "};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__22 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__22_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "internal exception "};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__23 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__23_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__24 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__24_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " (unknown)"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__25 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__25_value;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__26;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__27;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "connection refused"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(18) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__1_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__2;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__3;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "idbg client: "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__4 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__4_value;
static const lean_closure_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___closed__1_value)} };
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__5 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__5_value;
static const lean_closure_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__2___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__5_value)} };
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__6 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_idbg_client_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___redArg();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doIdbg"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(61, 152, 121, 224, 0, 70, 155, 32)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__6_value),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__7_value),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Idbg"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__9_value),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(222, 127, 37, 145, 246, 253, 221, 130)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(167, 188, 96, 25, 36, 32, 177, 172)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(154, 85, 246, 154, 57, 30, 227, 186)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 120, 240, 118, 26, 169, 87, 68)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__14 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__15 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__14_value),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(72, 181, 66, 123, 98, 246, 242, 167)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__16 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__16_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "controlInfoIdbg"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__17 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__16_value),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(38, 98, 163, 235, 228, 39, 161, 40)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__18 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__18_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__4;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "idbg: "};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Import"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__2_value),LEAN_SCALAR_PTR_LITERAL(29, 47, 116, 218, 39, 28, 172, 37)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__1_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__5_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__7;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__2_value),LEAN_SCALAR_PTR_LITERAL(29, 47, 116, 218, 39, 28, 172, 37)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(233, 207, 36, 16, 41, 121, 79, 89)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__11(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "f"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__1 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(29, 68, 183, 24, 128, 148, 178, 23)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__2 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toArray"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__3 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__1_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__3_value),LEAN_SCALAR_PTR_LITERAL(225, 54, 189, 64, 249, 49, 198, 116)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__4 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__5;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__6 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__1_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__6_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__7 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__8;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__9;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_>>=_"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__10 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__10_value),LEAN_SCALAR_PTR_LITERAL(143, 92, 54, 199, 40, 32, 117, 253)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__11 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__5_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__12 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Idbg.idbgClientLoop"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__13 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__13_value;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__14;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "idbgClientLoop"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__15 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(216, 3, 140, 103, 23, 193, 97, 10)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__15_value),LEAN_SCALAR_PTR_LITERAL(114, 35, 176, 243, 23, 158, 209, 172)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__16 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__17 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__18 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__18_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__19 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__19_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__19_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__20 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__20_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = ">>="};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__21 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__21_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__22 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__22_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__23_value_aux_1),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__23_value_aux_2),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__22_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__23 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__23_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__24 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__24_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__25_value_aux_1),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__25_value_aux_2),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__24_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__25 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__25_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__26 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__26_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__27_value_aux_0),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__27_value_aux_1),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__27_value_aux_2),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__26_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__27 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__27_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__28 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__28_value;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__29;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__30 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__30_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elabIdbgCore"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__31 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__31_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "idbg: abstracted type still has metavariables"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__32 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__32_value;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__33;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "idbg: abstracted value still has metavariables"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__34 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__34_value;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__35;
static const lean_array_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__36 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__36_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "repr"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__37 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__37_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__37_value),LEAN_SCALAR_PTR_LITERAL(248, 109, 138, 163, 21, 170, 71, 243)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__38 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__38_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ToString"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__39 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__39_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toString"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__40 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__40_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__39_value),LEAN_SCALAR_PTR_LITERAL(30, 202, 174, 203, 16, 186, 159, 168)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__41_value_aux_0),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__40_value),LEAN_SCALAR_PTR_LITERAL(206, 210, 39, 124, 69, 192, 37, 107)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__41 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__41_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "idbg"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(158, 127, 98, 129, 230, 27, 154, 50)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__1 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elabIdbgTerm"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__16_value),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 12, 184, 32, 84, 90, 234, 209)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "idbg body"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabDoIdbg"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__16_value),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 80, 1, 78, 180, 59, 65, 71)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameToJson(lean_object* v_x_3_){
_start:
{
switch(lean_obj_tag(v_x_3_))
{
case 0:
{
lean_object* v___x_4_; 
v___x_4_ = lean_box(0);
return v___x_4_;
}
case 1:
{
lean_object* v_pre_5_; lean_object* v_str_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v_pre_5_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_pre_5_);
v_str_6_ = lean_ctor_get(v_x_3_, 1);
lean_inc_ref(v_str_6_);
lean_dec_ref_known(v_x_3_, 2);
v___x_7_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameToJson___closed__0));
v___x_8_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameToJson(v_pre_5_);
v___x_9_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_9_, 0, v_str_6_);
v___x_10_ = lean_unsigned_to_nat(2u);
v___x_11_ = lean_mk_empty_array_with_capacity(v___x_10_);
v___x_12_ = lean_array_push(v___x_11_, v___x_8_);
v___x_13_ = lean_array_push(v___x_12_, v___x_9_);
v___x_14_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v___x_7_);
lean_ctor_set(v___x_15_, 1, v___x_14_);
v___x_16_ = lean_box(0);
v___x_17_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_15_);
lean_ctor_set(v___x_17_, 1, v___x_16_);
v___x_18_ = l_Lean_Json_mkObj(v___x_17_);
lean_dec_ref_known(v___x_17_, 2);
return v___x_18_;
}
default: 
{
lean_object* v_pre_19_; lean_object* v_i_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v_pre_19_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_pre_19_);
v_i_20_ = lean_ctor_get(v_x_3_, 1);
lean_inc(v_i_20_);
lean_dec_ref_known(v_x_3_, 2);
v___x_21_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameToJson___closed__1));
v___x_22_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameToJson(v_pre_19_);
v___x_23_ = l_Lean_JsonNumber_fromNat(v_i_20_);
v___x_24_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_24_, 0, v___x_23_);
v___x_25_ = lean_unsigned_to_nat(2u);
v___x_26_ = lean_mk_empty_array_with_capacity(v___x_25_);
v___x_27_ = lean_array_push(v___x_26_, v___x_22_);
v___x_28_ = lean_array_push(v___x_27_, v___x_24_);
v___x_29_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
v___x_30_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_21_);
lean_ctor_set(v___x_30_, 1, v___x_29_);
v___x_31_ = lean_box(0);
v___x_32_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_30_);
lean_ctor_set(v___x_32_, 1, v___x_31_);
v___x_33_ = l_Lean_Json_mkObj(v___x_32_);
lean_dec_ref_known(v___x_32_, 2);
return v___x_33_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f_spec__0_spec__0(size_t v_sz_34_, size_t v_i_35_, lean_object* v_bs_36_){
_start:
{
uint8_t v___x_37_; 
v___x_37_ = lean_usize_dec_lt(v_i_35_, v_sz_34_);
if (v___x_37_ == 0)
{
lean_object* v___x_38_; 
v___x_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_38_, 0, v_bs_36_);
return v___x_38_;
}
else
{
lean_object* v_v_39_; lean_object* v___x_40_; lean_object* v_bs_x27_41_; size_t v___x_42_; size_t v___x_43_; lean_object* v___x_44_; 
v_v_39_ = lean_array_uget(v_bs_36_, v_i_35_);
v___x_40_ = lean_unsigned_to_nat(0u);
v_bs_x27_41_ = lean_array_uset(v_bs_36_, v_i_35_, v___x_40_);
v___x_42_ = ((size_t)1ULL);
v___x_43_ = lean_usize_add(v_i_35_, v___x_42_);
v___x_44_ = lean_array_uset(v_bs_x27_41_, v_i_35_, v_v_39_);
v_i_35_ = v___x_43_;
v_bs_36_ = v___x_44_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f_spec__0_spec__0___boxed(lean_object* v_sz_46_, lean_object* v_i_47_, lean_object* v_bs_48_){
_start:
{
size_t v_sz_boxed_49_; size_t v_i_boxed_50_; lean_object* v_res_51_; 
v_sz_boxed_49_ = lean_unbox_usize(v_sz_46_);
lean_dec(v_sz_46_);
v_i_boxed_50_ = lean_unbox_usize(v_i_47_);
lean_dec(v_i_47_);
v_res_51_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f_spec__0_spec__0(v_sz_boxed_49_, v_i_boxed_50_, v_bs_48_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f_spec__0(lean_object* v_x_54_){
_start:
{
if (lean_obj_tag(v_x_54_) == 4)
{
lean_object* v_elems_55_; size_t v_sz_56_; size_t v___x_57_; lean_object* v___x_58_; 
v_elems_55_ = lean_ctor_get(v_x_54_, 0);
lean_inc_ref(v_elems_55_);
lean_dec_ref_known(v_x_54_, 1);
v_sz_56_ = lean_array_size(v_elems_55_);
v___x_57_ = ((size_t)0ULL);
v___x_58_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f_spec__0_spec__0(v_sz_56_, v___x_57_, v_elems_55_);
return v___x_58_;
}
else
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_59_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f_spec__0___closed__0));
v___x_60_ = lean_unsigned_to_nat(80u);
v___x_61_ = l_Lean_Json_pretty(v_x_54_, v___x_60_);
v___x_62_ = lean_string_append(v___x_59_, v___x_61_);
lean_dec_ref(v___x_61_);
v___x_63_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f_spec__0___closed__1));
v___x_64_ = lean_string_append(v___x_62_, v___x_63_);
v___x_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f(lean_object* v_j_75_){
_start:
{
uint8_t v___x_76_; 
v___x_76_ = l_Lean_Json_isNull(v_j_75_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameToJson___closed__0));
lean_inc(v_j_75_);
v___x_78_ = l_Lean_Json_getObjVal_x3f(v_j_75_, v___x_77_);
if (lean_obj_tag(v___x_78_) == 0)
{
lean_object* v___x_79_; lean_object* v___x_80_; 
lean_dec_ref_known(v___x_78_, 1);
v___x_79_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameToJson___closed__1));
lean_inc(v_j_75_);
v___x_80_ = l_Lean_Json_getObjVal_x3f(v_j_75_, v___x_79_);
if (lean_obj_tag(v___x_80_) == 0)
{
lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_91_; 
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_91_ == 0)
{
lean_object* v_unused_92_; 
v_unused_92_ = lean_ctor_get(v___x_80_, 0);
lean_dec(v_unused_92_);
v___x_82_ = v___x_80_;
v_isShared_83_ = v_isSharedCheck_91_;
goto v_resetjp_81_;
}
else
{
lean_dec(v___x_80_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_91_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_89_; 
v___x_84_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f___closed__0));
v___x_85_ = lean_unsigned_to_nat(80u);
v___x_86_ = l_Lean_Json_pretty(v_j_75_, v___x_85_);
v___x_87_ = lean_string_append(v___x_84_, v___x_86_);
lean_dec_ref(v___x_86_);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 0, v___x_87_);
v___x_89_ = v___x_82_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_87_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
else
{
lean_object* v_a_93_; lean_object* v___x_94_; 
lean_dec(v_j_75_);
v_a_93_ = lean_ctor_get(v___x_80_, 0);
lean_inc(v_a_93_);
lean_dec_ref_known(v___x_80_, 1);
v___x_94_ = l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f_spec__0(v_a_93_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_102_; 
v_a_95_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_102_ == 0)
{
v___x_97_ = v___x_94_;
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_dec(v___x_94_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_a_95_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
else
{
lean_object* v_a_103_; lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v_a_103_ = lean_ctor_get(v___x_94_, 0);
lean_inc(v_a_103_);
lean_dec_ref_known(v___x_94_, 1);
v___x_104_ = lean_array_get_size(v_a_103_);
v___x_105_ = lean_unsigned_to_nat(2u);
v___x_106_ = lean_nat_dec_eq(v___x_104_, v___x_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
lean_dec(v_a_103_);
v___x_107_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f___closed__2));
return v___x_107_;
}
else
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = lean_unsigned_to_nat(0u);
v___x_109_ = lean_array_fget_borrowed(v_a_103_, v___x_108_);
lean_inc(v___x_109_);
v___x_110_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f(v___x_109_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_dec(v_a_103_);
return v___x_110_;
}
else
{
lean_object* v_a_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v_a_111_ = lean_ctor_get(v___x_110_, 0);
lean_inc(v_a_111_);
lean_dec_ref_known(v___x_110_, 1);
v___x_112_ = lean_unsigned_to_nat(1u);
v___x_113_ = lean_array_fget(v_a_103_, v___x_112_);
lean_dec(v_a_103_);
v___x_114_ = l_Lean_Json_getNat_x3f(v___x_113_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_122_; 
lean_dec(v_a_111_);
v_a_115_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_122_ == 0)
{
v___x_117_ = v___x_114_;
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_a_115_);
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
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_131_; 
v_a_123_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_131_ == 0)
{
v___x_125_ = v___x_114_;
v_isShared_126_ = v_isSharedCheck_131_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_114_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_131_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_127_ = l_Lean_Name_num___override(v_a_111_, v_a_123_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_127_);
v___x_129_ = v___x_125_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
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
lean_object* v_a_132_; lean_object* v___x_133_; 
lean_dec(v_j_75_);
v_a_132_ = lean_ctor_get(v___x_78_, 0);
lean_inc(v_a_132_);
lean_dec_ref_known(v___x_78_, 1);
v___x_133_ = l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f_spec__0(v_a_132_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_141_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_141_ == 0)
{
v___x_136_ = v___x_133_;
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_133_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_139_; 
if (v_isShared_137_ == 0)
{
v___x_139_ = v___x_136_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_a_134_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
else
{
lean_object* v_a_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v_a_142_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_a_142_);
lean_dec_ref_known(v___x_133_, 1);
v___x_143_ = lean_array_get_size(v_a_142_);
v___x_144_ = lean_unsigned_to_nat(2u);
v___x_145_ = lean_nat_dec_eq(v___x_143_, v___x_144_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; 
lean_dec(v_a_142_);
v___x_146_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f___closed__4));
return v___x_146_;
}
else
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = lean_array_fget_borrowed(v_a_142_, v___x_147_);
lean_inc(v___x_148_);
v___x_149_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f(v___x_148_);
if (lean_obj_tag(v___x_149_) == 0)
{
lean_dec(v_a_142_);
return v___x_149_;
}
else
{
lean_object* v_a_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v_a_150_ = lean_ctor_get(v___x_149_, 0);
lean_inc(v_a_150_);
lean_dec_ref_known(v___x_149_, 1);
v___x_151_ = lean_unsigned_to_nat(1u);
v___x_152_ = lean_array_fget(v_a_142_, v___x_151_);
lean_dec(v_a_142_);
v___x_153_ = l_Lean_Json_getStr_x3f(v___x_152_);
if (lean_obj_tag(v___x_153_) == 0)
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
lean_dec(v_a_150_);
v_a_154_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_153_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
else
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_170_; 
v_a_162_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_170_ == 0)
{
v___x_164_ = v___x_153_;
v_isShared_165_ = v_isSharedCheck_170_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_153_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_170_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; lean_object* v___x_168_; 
v___x_166_ = l_Lean_Name_str___override(v_a_150_, v_a_162_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_166_);
v___x_168_ = v___x_164_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_166_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
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
lean_object* v___x_171_; 
lean_dec(v_j_75_);
v___x_171_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f___closed__5));
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson(uint8_t v_x_184_){
_start:
{
switch(v_x_184_)
{
case 0:
{
lean_object* v___x_185_; 
v___x_185_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__1));
return v___x_185_;
}
case 1:
{
lean_object* v___x_186_; 
v___x_186_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__3));
return v___x_186_;
}
case 2:
{
lean_object* v___x_187_; 
v___x_187_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__5));
return v___x_187_;
}
default: 
{
lean_object* v___x_188_; 
v___x_188_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__7));
return v___x_188_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___boxed(lean_object* v_x_189_){
_start:
{
uint8_t v_x_64__boxed_190_; lean_object* v_res_191_; 
v_x_64__boxed_190_ = lean_unbox(v_x_189_);
v_res_191_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson(v_x_64__boxed_190_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoFromJson_x3f(lean_object* v_x_205_){
_start:
{
lean_object* v_j_207_; 
if (lean_obj_tag(v_x_205_) == 3)
{
lean_object* v_s_213_; lean_object* v___x_214_; uint8_t v___x_215_; 
v_s_213_ = lean_ctor_get(v_x_205_, 0);
v___x_214_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__0));
v___x_215_ = lean_string_dec_eq(v_s_213_, v___x_214_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_216_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__2));
v___x_217_ = lean_string_dec_eq(v_s_213_, v___x_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_218_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__4));
v___x_219_ = lean_string_dec_eq(v_s_213_, v___x_218_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_220_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson___closed__6));
v___x_221_ = lean_string_dec_eq(v_s_213_, v___x_220_);
if (v___x_221_ == 0)
{
v_j_207_ = v_x_205_;
goto v___jp_206_;
}
else
{
lean_object* v___x_222_; 
lean_dec_ref_known(v_x_205_, 1);
v___x_222_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoFromJson_x3f___closed__1));
return v___x_222_;
}
}
else
{
lean_object* v___x_223_; 
lean_dec_ref_known(v_x_205_, 1);
v___x_223_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoFromJson_x3f___closed__2));
return v___x_223_;
}
}
else
{
lean_object* v___x_224_; 
lean_dec_ref_known(v_x_205_, 1);
v___x_224_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoFromJson_x3f___closed__3));
return v___x_224_;
}
}
else
{
lean_object* v___x_225_; 
lean_dec_ref_known(v_x_205_, 1);
v___x_225_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoFromJson_x3f___closed__4));
return v___x_225_;
}
}
else
{
v_j_207_ = v_x_205_;
goto v___jp_206_;
}
v___jp_206_:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_208_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoFromJson_x3f___closed__0));
v___x_209_ = lean_unsigned_to_nat(80u);
v___x_210_ = l_Lean_Json_pretty(v_j_207_, v___x_209_);
v___x_211_ = lean_string_append(v___x_208_, v___x_210_);
lean_dec_ref(v___x_210_);
v___x_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
return v___x_212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_literalToJson(lean_object* v_x_228_){
_start:
{
if (lean_obj_tag(v_x_228_) == 0)
{
lean_object* v_val_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_242_; 
v_val_229_ = lean_ctor_get(v_x_228_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v_x_228_);
if (v_isSharedCheck_242_ == 0)
{
v___x_231_ = v_x_228_;
v_isShared_232_ = v_isSharedCheck_242_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_val_229_);
lean_dec(v_x_228_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_242_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_233_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_literalToJson___closed__0));
v___x_234_ = l_Lean_JsonNumber_fromNat(v_val_229_);
if (v_isShared_232_ == 0)
{
lean_ctor_set_tag(v___x_231_, 2);
lean_ctor_set(v___x_231_, 0, v___x_234_);
v___x_236_ = v___x_231_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_234_);
v___x_236_ = v_reuseFailAlloc_241_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_233_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v___x_238_ = lean_box(0);
v___x_239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_237_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
v___x_240_ = l_Lean_Json_mkObj(v___x_239_);
lean_dec_ref_known(v___x_239_, 2);
return v___x_240_;
}
}
}
else
{
lean_object* v_val_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_255_; 
v_val_243_ = lean_ctor_get(v_x_228_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v_x_228_);
if (v_isSharedCheck_255_ == 0)
{
v___x_245_ = v_x_228_;
v_isShared_246_ = v_isSharedCheck_255_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_val_243_);
lean_dec(v_x_228_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_255_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_247_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_literalToJson___closed__1));
if (v_isShared_246_ == 0)
{
lean_ctor_set_tag(v___x_245_, 3);
v___x_249_ = v___x_245_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_val_243_);
v___x_249_ = v_reuseFailAlloc_254_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_247_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
v___x_251_ = lean_box(0);
v___x_252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_250_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
v___x_253_ = l_Lean_Json_mkObj(v___x_252_);
lean_dec_ref_known(v___x_252_, 2);
return v___x_253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_literalFromJson_x3f(lean_object* v_j_257_){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_literalToJson___closed__0));
lean_inc(v_j_257_);
v___x_259_ = l_Lean_Json_getObjVal_x3f(v_j_257_, v___x_258_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_298_; 
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_298_ == 0)
{
lean_object* v_unused_299_; 
v_unused_299_ = lean_ctor_get(v___x_259_, 0);
lean_dec(v_unused_299_);
v___x_261_ = v___x_259_;
v_isShared_262_ = v_isSharedCheck_298_;
goto v_resetjp_260_;
}
else
{
lean_dec(v___x_259_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_298_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_literalToJson___closed__1));
lean_inc(v_j_257_);
v___x_264_ = l_Lean_Json_getObjVal_x3f(v_j_257_, v___x_263_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_275_; 
lean_del_object(v___x_261_);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_275_ == 0)
{
lean_object* v_unused_276_; 
v_unused_276_ = lean_ctor_get(v___x_264_, 0);
lean_dec(v_unused_276_);
v___x_266_ = v___x_264_;
v_isShared_267_ = v_isSharedCheck_275_;
goto v_resetjp_265_;
}
else
{
lean_dec(v___x_264_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_275_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_268_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_literalFromJson_x3f___closed__0));
v___x_269_ = lean_unsigned_to_nat(80u);
v___x_270_ = l_Lean_Json_pretty(v_j_257_, v___x_269_);
v___x_271_ = lean_string_append(v___x_268_, v___x_270_);
lean_dec_ref(v___x_270_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 0, v___x_271_);
v___x_273_ = v___x_266_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_271_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
else
{
lean_object* v_a_277_; lean_object* v___x_278_; 
lean_dec(v_j_257_);
v_a_277_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_a_277_);
lean_dec_ref_known(v___x_264_, 1);
v___x_278_ = l_Lean_Json_getStr_x3f(v_a_277_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
lean_del_object(v___x_261_);
v_a_279_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v___x_278_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_278_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_279_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_297_; 
v_a_287_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_297_ == 0)
{
v___x_289_ = v___x_278_;
v_isShared_290_ = v_isSharedCheck_297_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_278_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_297_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_262_ == 0)
{
lean_ctor_set_tag(v___x_261_, 1);
lean_ctor_set(v___x_261_, 0, v_a_287_);
v___x_292_ = v___x_261_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_287_);
v___x_292_ = v_reuseFailAlloc_296_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
lean_object* v___x_294_; 
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_292_);
v___x_294_ = v___x_289_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_324_; 
lean_dec(v_j_257_);
v_a_300_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_324_ == 0)
{
v___x_302_ = v___x_259_;
v_isShared_303_ = v_isSharedCheck_324_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_259_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_324_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_Json_getNat_x3f(v_a_300_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
lean_del_object(v___x_302_);
v_a_305_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_304_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_304_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_323_; 
v_a_313_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_323_ == 0)
{
v___x_315_ = v___x_304_;
v_isShared_316_ = v_isSharedCheck_323_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_304_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_323_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set_tag(v___x_302_, 0);
lean_ctor_set(v___x_302_, 0, v_a_313_);
v___x_318_ = v___x_302_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_313_);
v___x_318_ = v_reuseFailAlloc_322_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_object* v___x_320_; 
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v___x_318_);
v___x_320_ = v___x_315_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__3(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__2));
v___x_333_ = l_Lean_Json_mkObj(v___x_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson(lean_object* v_x_339_){
_start:
{
switch(lean_obj_tag(v_x_339_))
{
case 0:
{
lean_object* v___x_340_; 
v___x_340_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__3, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__3_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__3);
return v___x_340_;
}
case 1:
{
lean_object* v_a_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_a_341_ = lean_ctor_get(v_x_339_, 0);
lean_inc(v_a_341_);
lean_dec_ref_known(v_x_339_, 1);
v___x_342_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__4));
v___x_343_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson(v_a_341_);
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_342_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = lean_box(0);
v___x_346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_344_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v___x_347_ = l_Lean_Json_mkObj(v___x_346_);
lean_dec_ref_known(v___x_346_, 2);
return v___x_347_;
}
case 2:
{
lean_object* v_a_348_; lean_object* v_a_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_a_348_ = lean_ctor_get(v_x_339_, 0);
lean_inc(v_a_348_);
v_a_349_ = lean_ctor_get(v_x_339_, 1);
lean_inc(v_a_349_);
lean_dec_ref_known(v_x_339_, 2);
v___x_350_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__5));
v___x_351_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson(v_a_348_);
v___x_352_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson(v_a_349_);
v___x_353_ = lean_unsigned_to_nat(2u);
v___x_354_ = lean_mk_empty_array_with_capacity(v___x_353_);
v___x_355_ = lean_array_push(v___x_354_, v___x_351_);
v___x_356_ = lean_array_push(v___x_355_, v___x_352_);
v___x_357_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_350_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
v___x_359_ = lean_box(0);
v___x_360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_358_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = l_Lean_Json_mkObj(v___x_360_);
lean_dec_ref_known(v___x_360_, 2);
return v___x_361_;
}
case 3:
{
lean_object* v_a_362_; lean_object* v_a_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_a_362_ = lean_ctor_get(v_x_339_, 0);
lean_inc(v_a_362_);
v_a_363_ = lean_ctor_get(v_x_339_, 1);
lean_inc(v_a_363_);
lean_dec_ref_known(v_x_339_, 2);
v___x_364_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__6));
v___x_365_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson(v_a_362_);
v___x_366_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson(v_a_363_);
v___x_367_ = lean_unsigned_to_nat(2u);
v___x_368_ = lean_mk_empty_array_with_capacity(v___x_367_);
v___x_369_ = lean_array_push(v___x_368_, v___x_365_);
v___x_370_ = lean_array_push(v___x_369_, v___x_366_);
v___x_371_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_364_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
v___x_373_ = lean_box(0);
v___x_374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_372_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = l_Lean_Json_mkObj(v___x_374_);
lean_dec_ref_known(v___x_374_, 2);
return v___x_375_;
}
case 4:
{
lean_object* v_a_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v_a_376_ = lean_ctor_get(v_x_339_, 0);
lean_inc(v_a_376_);
lean_dec_ref_known(v_x_339_, 1);
v___x_377_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__7));
v___x_378_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameToJson(v_a_376_);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_377_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
v___x_380_ = lean_box(0);
v___x_381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_379_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
v___x_382_ = l_Lean_Json_mkObj(v___x_381_);
lean_dec_ref_known(v___x_381_, 2);
return v___x_382_;
}
default: 
{
lean_object* v_a_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v_a_383_ = lean_ctor_get(v_x_339_, 0);
lean_inc(v_a_383_);
lean_dec_ref_known(v_x_339_, 1);
v___x_384_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__8));
v___x_385_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameToJson(v_a_383_);
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_384_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = lean_box(0);
v___x_388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_386_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = l_Lean_Json_mkObj(v___x_388_);
lean_dec_ref_known(v___x_388_, 2);
return v___x_389_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f(lean_object* v_j_399_){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__0));
lean_inc(v_j_399_);
v___x_401_ = l_Lean_Json_getObjVal_x3f(v_j_399_, v___x_400_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v___x_402_; lean_object* v___x_403_; 
lean_dec_ref_known(v___x_401_, 1);
v___x_402_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__4));
lean_inc(v_j_399_);
v___x_403_ = l_Lean_Json_getObjVal_x3f(v_j_399_, v___x_402_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; 
lean_dec_ref_known(v___x_403_, 1);
v___x_404_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__5));
lean_inc(v_j_399_);
v___x_405_ = l_Lean_Json_getObjVal_x3f(v_j_399_, v___x_404_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; 
lean_dec_ref_known(v___x_405_, 1);
v___x_406_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__6));
lean_inc(v_j_399_);
v___x_407_ = l_Lean_Json_getObjVal_x3f(v_j_399_, v___x_406_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; 
lean_dec_ref_known(v___x_407_, 1);
v___x_408_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__7));
lean_inc(v_j_399_);
v___x_409_ = l_Lean_Json_getObjVal_x3f(v_j_399_, v___x_408_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; 
lean_dec_ref_known(v___x_409_, 1);
v___x_410_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__8));
lean_inc(v_j_399_);
v___x_411_ = l_Lean_Json_getObjVal_x3f(v_j_399_, v___x_410_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_422_; 
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_422_ == 0)
{
lean_object* v_unused_423_; 
v_unused_423_ = lean_ctor_get(v___x_411_, 0);
lean_dec(v_unused_423_);
v___x_413_ = v___x_411_;
v_isShared_414_ = v_isSharedCheck_422_;
goto v_resetjp_412_;
}
else
{
lean_dec(v___x_411_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_422_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_415_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f___closed__0));
v___x_416_ = lean_unsigned_to_nat(80u);
v___x_417_ = l_Lean_Json_pretty(v_j_399_, v___x_416_);
v___x_418_ = lean_string_append(v___x_415_, v___x_417_);
lean_dec_ref(v___x_417_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v___x_418_);
v___x_420_ = v___x_413_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
else
{
lean_object* v_a_424_; lean_object* v___x_425_; 
lean_dec(v_j_399_);
v_a_424_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_424_);
lean_dec_ref_known(v___x_411_, 1);
v___x_425_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f(v_a_424_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_425_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_425_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
else
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_442_; 
v_a_434_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_442_ == 0)
{
v___x_436_ = v___x_425_;
v_isShared_437_ = v_isSharedCheck_442_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_425_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_442_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_438_ = l_Lean_Level_mvar___override(v_a_434_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_438_);
v___x_440_ = v___x_436_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_438_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
}
else
{
lean_object* v_a_443_; lean_object* v___x_444_; 
lean_dec(v_j_399_);
v_a_443_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_a_443_);
lean_dec_ref_known(v___x_409_, 1);
v___x_444_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f(v_a_443_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___x_444_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_444_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_445_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
else
{
lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_461_; 
v_a_453_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_461_ == 0)
{
v___x_455_ = v___x_444_;
v_isShared_456_ = v_isSharedCheck_461_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___x_444_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_461_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; lean_object* v___x_459_; 
v___x_457_ = l_Lean_Level_param___override(v_a_453_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 0, v___x_457_);
v___x_459_ = v___x_455_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
}
else
{
lean_object* v_a_462_; lean_object* v___x_463_; 
lean_dec(v_j_399_);
v_a_462_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_a_462_);
lean_dec_ref_known(v___x_407_, 1);
v___x_463_ = l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f_spec__0(v_a_462_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
v_a_464_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_463_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_463_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v_a_472_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_a_472_);
lean_dec_ref_known(v___x_463_, 1);
v___x_473_ = lean_array_get_size(v_a_472_);
v___x_474_ = lean_unsigned_to_nat(2u);
v___x_475_ = lean_nat_dec_eq(v___x_473_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; 
lean_dec(v_a_472_);
v___x_476_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f___closed__2));
return v___x_476_;
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_477_ = lean_unsigned_to_nat(0u);
v___x_478_ = lean_array_fget_borrowed(v_a_472_, v___x_477_);
lean_inc(v___x_478_);
v___x_479_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f(v___x_478_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_dec(v_a_472_);
return v___x_479_;
}
else
{
lean_object* v_a_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_480_);
lean_dec_ref_known(v___x_479_, 1);
v___x_481_ = lean_unsigned_to_nat(1u);
v___x_482_ = lean_array_fget(v_a_472_, v___x_481_);
lean_dec(v_a_472_);
v___x_483_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f(v___x_482_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_dec(v_a_480_);
return v___x_483_;
}
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_492_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_492_ == 0)
{
v___x_486_ = v___x_483_;
v_isShared_487_ = v_isSharedCheck_492_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_483_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_492_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_488_ = l_Lean_Level_imax___override(v_a_480_, v_a_484_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v___x_488_);
v___x_490_ = v___x_486_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_488_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
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
lean_object* v_a_493_; lean_object* v___x_494_; 
lean_dec(v_j_399_);
v_a_493_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_493_);
lean_dec_ref_known(v___x_405_, 1);
v___x_494_ = l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f_spec__0(v_a_493_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
v_a_495_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_494_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_494_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
else
{
lean_object* v_a_503_; lean_object* v___x_504_; lean_object* v___x_505_; uint8_t v___x_506_; 
v_a_503_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_a_503_);
lean_dec_ref_known(v___x_494_, 1);
v___x_504_ = lean_array_get_size(v_a_503_);
v___x_505_ = lean_unsigned_to_nat(2u);
v___x_506_ = lean_nat_dec_eq(v___x_504_, v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; 
lean_dec(v_a_503_);
v___x_507_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f___closed__4));
return v___x_507_;
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_508_ = lean_unsigned_to_nat(0u);
v___x_509_ = lean_array_fget_borrowed(v_a_503_, v___x_508_);
lean_inc(v___x_509_);
v___x_510_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f(v___x_509_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_dec(v_a_503_);
return v___x_510_;
}
else
{
lean_object* v_a_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_a_511_);
lean_dec_ref_known(v___x_510_, 1);
v___x_512_ = lean_unsigned_to_nat(1u);
v___x_513_ = lean_array_fget(v_a_503_, v___x_512_);
lean_dec(v_a_503_);
v___x_514_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f(v___x_513_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_dec(v_a_511_);
return v___x_514_;
}
else
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_523_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_523_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_519_ = l_Lean_Level_max___override(v_a_511_, v_a_515_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_519_);
v___x_521_ = v___x_517_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
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
lean_object* v_a_524_; lean_object* v___x_525_; 
lean_dec(v_j_399_);
v_a_524_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_a_524_);
lean_dec_ref_known(v___x_403_, 1);
v___x_525_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f(v_a_524_);
if (lean_obj_tag(v___x_525_) == 0)
{
return v___x_525_;
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_534_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_534_ == 0)
{
v___x_528_ = v___x_525_;
v_isShared_529_ = v_isSharedCheck_534_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_534_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_530_ = l_Lean_Level_succ___override(v_a_526_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_530_);
v___x_532_ = v___x_528_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
else
{
lean_object* v___x_535_; 
lean_dec_ref_known(v___x_401_, 1);
lean_dec(v_j_399_);
v___x_535_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f___closed__5));
return v___x_535_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson_spec__0(size_t v_sz_536_, size_t v_i_537_, lean_object* v_bs_538_){
_start:
{
uint8_t v___x_539_; 
v___x_539_ = lean_usize_dec_lt(v_i_537_, v_sz_536_);
if (v___x_539_ == 0)
{
return v_bs_538_;
}
else
{
lean_object* v_v_540_; lean_object* v___x_541_; lean_object* v_bs_x27_542_; lean_object* v___x_543_; size_t v___x_544_; size_t v___x_545_; lean_object* v___x_546_; 
v_v_540_ = lean_array_uget(v_bs_538_, v_i_537_);
v___x_541_ = lean_unsigned_to_nat(0u);
v_bs_x27_542_ = lean_array_uset(v_bs_538_, v_i_537_, v___x_541_);
v___x_543_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson(v_v_540_);
v___x_544_ = ((size_t)1ULL);
v___x_545_ = lean_usize_add(v_i_537_, v___x_544_);
v___x_546_ = lean_array_uset(v_bs_x27_542_, v_i_537_, v___x_543_);
v_i_537_ = v___x_545_;
v_bs_538_ = v___x_546_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson_spec__0___boxed(lean_object* v_sz_548_, lean_object* v_i_549_, lean_object* v_bs_550_){
_start:
{
size_t v_sz_boxed_551_; size_t v_i_boxed_552_; lean_object* v_res_553_; 
v_sz_boxed_551_ = lean_unbox_usize(v_sz_548_);
lean_dec(v_sz_548_);
v_i_boxed_552_ = lean_unbox_usize(v_i_549_);
lean_dec(v_i_549_);
v_res_553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson_spec__0(v_sz_boxed_551_, v_i_boxed_552_, v_bs_550_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson(lean_object* v_x_574_){
_start:
{
switch(lean_obj_tag(v_x_574_))
{
case 0:
{
lean_object* v_deBruijnIndex_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_deBruijnIndex_575_ = lean_ctor_get(v_x_574_, 0);
lean_inc(v_deBruijnIndex_575_);
lean_dec_ref_known(v_x_574_, 1);
v___x_576_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__0));
v___x_577_ = l_Lean_JsonNumber_fromNat(v_deBruijnIndex_575_);
v___x_578_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_576_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = lean_box(0);
v___x_581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_579_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = l_Lean_Json_mkObj(v___x_581_);
lean_dec_ref_known(v___x_581_, 2);
return v___x_582_;
}
case 1:
{
lean_object* v_fvarId_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v_fvarId_583_ = lean_ctor_get(v_x_574_, 0);
lean_inc(v_fvarId_583_);
lean_dec_ref_known(v_x_574_, 1);
v___x_584_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__1));
v___x_585_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameToJson(v_fvarId_583_);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_584_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = lean_box(0);
v___x_588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_586_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
v___x_589_ = l_Lean_Json_mkObj(v___x_588_);
lean_dec_ref_known(v___x_588_, 2);
return v___x_589_;
}
case 2:
{
lean_object* v_mvarId_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v_mvarId_590_ = lean_ctor_get(v_x_574_, 0);
lean_inc(v_mvarId_590_);
lean_dec_ref_known(v_x_574_, 1);
v___x_591_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__8));
v___x_592_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameToJson(v_mvarId_590_);
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_591_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = lean_box(0);
v___x_595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_593_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v___x_596_ = l_Lean_Json_mkObj(v___x_595_);
lean_dec_ref_known(v___x_595_, 2);
return v___x_596_;
}
case 3:
{
lean_object* v_u_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v_u_597_ = lean_ctor_get(v_x_574_, 0);
lean_inc(v_u_597_);
lean_dec_ref_known(v_x_574_, 1);
v___x_598_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__2));
v___x_599_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson(v_u_597_);
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = lean_box(0);
v___x_602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v___x_603_ = l_Lean_Json_mkObj(v___x_602_);
lean_dec_ref_known(v___x_602_, 2);
return v___x_603_;
}
case 4:
{
lean_object* v_declName_604_; lean_object* v_us_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; size_t v_sz_611_; size_t v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v_declName_604_ = lean_ctor_get(v_x_574_, 0);
lean_inc(v_declName_604_);
v_us_605_ = lean_ctor_get(v_x_574_, 1);
lean_inc(v_us_605_);
lean_dec_ref_known(v_x_574_, 2);
v___x_606_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__3));
v___x_607_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameToJson(v_declName_604_);
v___x_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__4));
v___x_610_ = lean_array_mk(v_us_605_);
v_sz_611_ = lean_array_size(v___x_610_);
v___x_612_ = ((size_t)0ULL);
v___x_613_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson_spec__0(v_sz_611_, v___x_612_, v___x_610_);
v___x_614_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_609_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = lean_box(0);
v___x_617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_615_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_608_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
v___x_619_ = l_Lean_Json_mkObj(v___x_618_);
lean_dec_ref_known(v___x_618_, 2);
return v___x_619_;
}
case 5:
{
lean_object* v_fn_620_; lean_object* v_arg_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v_fn_620_ = lean_ctor_get(v_x_574_, 0);
lean_inc_ref(v_fn_620_);
v_arg_621_ = lean_ctor_get(v_x_574_, 1);
lean_inc_ref(v_arg_621_);
lean_dec_ref_known(v_x_574_, 2);
v___x_622_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__5));
v___x_623_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson(v_fn_620_);
v___x_624_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson(v_arg_621_);
v___x_625_ = lean_unsigned_to_nat(2u);
v___x_626_ = lean_mk_empty_array_with_capacity(v___x_625_);
v___x_627_ = lean_array_push(v___x_626_, v___x_623_);
v___x_628_ = lean_array_push(v___x_627_, v___x_624_);
v___x_629_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_622_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = lean_box(0);
v___x_632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_630_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = l_Lean_Json_mkObj(v___x_632_);
lean_dec_ref_known(v___x_632_, 2);
return v___x_633_;
}
case 6:
{
lean_object* v_binderName_634_; lean_object* v_binderType_635_; lean_object* v_body_636_; uint8_t v_binderInfo_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_binderName_634_ = lean_ctor_get(v_x_574_, 0);
lean_inc(v_binderName_634_);
v_binderType_635_ = lean_ctor_get(v_x_574_, 1);
lean_inc_ref(v_binderType_635_);
v_body_636_ = lean_ctor_get(v_x_574_, 2);
lean_inc_ref(v_body_636_);
v_binderInfo_637_ = lean_ctor_get_uint8(v_x_574_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_574_, 3);
v___x_638_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__6));
v___x_639_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__7));
v___x_640_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameToJson(v_binderName_634_);
v___x_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__8));
v___x_643_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson(v_binderType_635_);
v___x_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_642_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v___x_645_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__9));
v___x_646_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson(v_body_636_);
v___x_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_645_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__10));
v___x_649_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson(v_binderInfo_637_);
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_648_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
v___x_651_ = lean_box(0);
v___x_652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_650_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_647_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_644_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
v___x_655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_641_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
v___x_656_ = l_Lean_Json_mkObj(v___x_655_);
lean_dec_ref_known(v___x_655_, 2);
v___x_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_638_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v___x_658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
lean_ctor_set(v___x_658_, 1, v___x_651_);
v___x_659_ = l_Lean_Json_mkObj(v___x_658_);
lean_dec_ref_known(v___x_658_, 2);
return v___x_659_;
}
case 7:
{
lean_object* v_binderName_660_; lean_object* v_binderType_661_; lean_object* v_body_662_; uint8_t v_binderInfo_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v_binderName_660_ = lean_ctor_get(v_x_574_, 0);
lean_inc(v_binderName_660_);
v_binderType_661_ = lean_ctor_get(v_x_574_, 1);
lean_inc_ref(v_binderType_661_);
v_body_662_ = lean_ctor_get(v_x_574_, 2);
lean_inc_ref(v_body_662_);
v_binderInfo_663_ = lean_ctor_get_uint8(v_x_574_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_574_, 3);
v___x_664_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__11));
v___x_665_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__7));
v___x_666_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameToJson(v_binderName_660_);
v___x_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_665_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__8));
v___x_669_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson(v_binderType_661_);
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_668_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v___x_671_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__9));
v___x_672_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson(v_body_662_);
v___x_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_671_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__10));
v___x_675_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoToJson(v_binderInfo_663_);
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_674_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = lean_box(0);
v___x_678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_676_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_673_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
v___x_680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_670_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v___x_681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_667_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = l_Lean_Json_mkObj(v___x_681_);
lean_dec_ref_known(v___x_681_, 2);
v___x_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_664_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
lean_ctor_set(v___x_684_, 1, v___x_677_);
v___x_685_ = l_Lean_Json_mkObj(v___x_684_);
lean_dec_ref_known(v___x_684_, 2);
return v___x_685_;
}
case 8:
{
lean_object* v_declName_686_; lean_object* v_type_687_; lean_object* v_value_688_; lean_object* v_body_689_; uint8_t v_nondep_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v_declName_686_ = lean_ctor_get(v_x_574_, 0);
lean_inc(v_declName_686_);
v_type_687_ = lean_ctor_get(v_x_574_, 1);
lean_inc_ref(v_type_687_);
v_value_688_ = lean_ctor_get(v_x_574_, 2);
lean_inc_ref(v_value_688_);
v_body_689_ = lean_ctor_get(v_x_574_, 3);
lean_inc_ref(v_body_689_);
v_nondep_690_ = lean_ctor_get_uint8(v_x_574_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_x_574_, 4);
v___x_691_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__12));
v___x_692_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__7));
v___x_693_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameToJson(v_declName_686_);
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_692_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__8));
v___x_696_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson(v_type_687_);
v___x_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_695_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__13));
v___x_699_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson(v_value_688_);
v___x_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_698_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___x_701_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__9));
v___x_702_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson(v_body_689_);
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_701_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__14));
v___x_705_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_705_, 0, v_nondep_690_);
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_704_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
v___x_707_ = lean_box(0);
v___x_708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_706_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
v___x_709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_703_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v___x_710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_700_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___x_711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_697_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_694_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
v___x_713_ = l_Lean_Json_mkObj(v___x_712_);
lean_dec_ref_known(v___x_712_, 2);
v___x_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_691_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v___x_715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
lean_ctor_set(v___x_715_, 1, v___x_707_);
v___x_716_ = l_Lean_Json_mkObj(v___x_715_);
lean_dec_ref_known(v___x_715_, 2);
return v___x_716_;
}
case 9:
{
lean_object* v_a_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v_a_717_ = lean_ctor_get(v_x_574_, 0);
lean_inc_ref(v_a_717_);
lean_dec_ref_known(v_x_574_, 1);
v___x_718_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__15));
v___x_719_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_literalToJson(v_a_717_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = lean_box(0);
v___x_722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_720_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
v___x_723_ = l_Lean_Json_mkObj(v___x_722_);
lean_dec_ref_known(v___x_722_, 2);
return v___x_723_;
}
case 10:
{
lean_object* v_expr_724_; 
v_expr_724_ = lean_ctor_get(v_x_574_, 1);
lean_inc_ref(v_expr_724_);
lean_dec_ref_known(v_x_574_, 2);
v_x_574_ = v_expr_724_;
goto _start;
}
default: 
{
lean_object* v_typeName_726_; lean_object* v_idx_727_; lean_object* v_struct_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v_typeName_726_ = lean_ctor_get(v_x_574_, 0);
lean_inc(v_typeName_726_);
v_idx_727_ = lean_ctor_get(v_x_574_, 1);
lean_inc(v_idx_727_);
v_struct_728_ = lean_ctor_get(v_x_574_, 2);
lean_inc_ref(v_struct_728_);
lean_dec_ref_known(v_x_574_, 3);
v___x_729_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__16));
v___x_730_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__17));
v___x_731_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameToJson(v_typeName_726_);
v___x_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_730_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__18));
v___x_734_ = l_Lean_JsonNumber_fromNat(v_idx_727_);
v___x_735_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_733_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__19));
v___x_738_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson(v_struct_728_);
v___x_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_737_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = lean_box(0);
v___x_741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_739_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_736_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_732_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = l_Lean_Json_mkObj(v___x_743_);
lean_dec_ref_known(v___x_743_, 2);
v___x_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_729_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v___x_740_);
v___x_747_ = l_Lean_Json_mkObj(v___x_746_);
lean_dec_ref_known(v___x_746_, 2);
return v___x_747_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f_spec__0(lean_object* v_x_748_, lean_object* v_x_749_){
_start:
{
if (lean_obj_tag(v_x_748_) == 0)
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = l_List_reverse___redArg(v_x_749_);
v___x_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
return v___x_751_;
}
else
{
lean_object* v_head_752_; lean_object* v_tail_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_771_; 
v_head_752_ = lean_ctor_get(v_x_748_, 0);
v_tail_753_ = lean_ctor_get(v_x_748_, 1);
v_isSharedCheck_771_ = !lean_is_exclusive(v_x_748_);
if (v_isSharedCheck_771_ == 0)
{
v___x_755_ = v_x_748_;
v_isShared_756_ = v_isSharedCheck_771_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_tail_753_);
lean_inc(v_head_752_);
lean_dec(v_x_748_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_771_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; 
v___x_757_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f(v_head_752_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_del_object(v___x_755_);
lean_dec(v_tail_753_);
lean_dec(v_x_749_);
v_a_758_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_757_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_757_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; 
v_a_766_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_757_, 1);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 1, v_x_749_);
lean_ctor_set(v___x_755_, 0, v_a_766_);
v___x_768_ = v___x_755_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_766_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_x_749_);
v___x_768_ = v_reuseFailAlloc_770_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
v_x_748_ = v_tail_753_;
v_x_749_ = v___x_768_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f(lean_object* v_j_776_){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__0));
lean_inc(v_j_776_);
v___x_778_ = l_Lean_Json_getObjVal_x3f(v_j_776_, v___x_777_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v___x_779_; lean_object* v___x_780_; 
lean_dec_ref_known(v___x_778_, 1);
v___x_779_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__1));
lean_inc(v_j_776_);
v___x_780_ = l_Lean_Json_getObjVal_x3f(v_j_776_, v___x_779_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v___x_781_; lean_object* v___x_782_; 
lean_dec_ref_known(v___x_780_, 1);
v___x_781_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelToJson___closed__8));
lean_inc(v_j_776_);
v___x_782_ = l_Lean_Json_getObjVal_x3f(v_j_776_, v___x_781_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v___x_783_; lean_object* v___x_784_; 
lean_dec_ref_known(v___x_782_, 1);
v___x_783_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__2));
lean_inc(v_j_776_);
v___x_784_ = l_Lean_Json_getObjVal_x3f(v_j_776_, v___x_783_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v___x_785_; lean_object* v___x_786_; 
lean_dec_ref_known(v___x_784_, 1);
v___x_785_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__3));
lean_inc(v_j_776_);
v___x_786_ = l_Lean_Json_getObjVal_x3f(v_j_776_, v___x_785_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v___x_787_; lean_object* v___x_788_; 
lean_dec_ref_known(v___x_786_, 1);
v___x_787_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__5));
lean_inc(v_j_776_);
v___x_788_ = l_Lean_Json_getObjVal_x3f(v_j_776_, v___x_787_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v___x_789_; lean_object* v___x_790_; 
lean_dec_ref_known(v___x_788_, 1);
v___x_789_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__6));
lean_inc(v_j_776_);
v___x_790_ = l_Lean_Json_getObjVal_x3f(v_j_776_, v___x_789_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v___x_791_; lean_object* v___x_792_; 
lean_dec_ref_known(v___x_790_, 1);
v___x_791_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__11));
lean_inc(v_j_776_);
v___x_792_ = l_Lean_Json_getObjVal_x3f(v_j_776_, v___x_791_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v___x_793_; lean_object* v___x_794_; 
lean_dec_ref_known(v___x_792_, 1);
v___x_793_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__12));
lean_inc(v_j_776_);
v___x_794_ = l_Lean_Json_getObjVal_x3f(v_j_776_, v___x_793_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v___x_795_; lean_object* v___x_796_; 
lean_dec_ref_known(v___x_794_, 1);
v___x_795_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__15));
lean_inc(v_j_776_);
v___x_796_ = l_Lean_Json_getObjVal_x3f(v_j_776_, v___x_795_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; 
lean_dec_ref_known(v___x_796_, 1);
v___x_797_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__16));
lean_inc(v_j_776_);
v___x_798_ = l_Lean_Json_getObjVal_x3f(v_j_776_, v___x_797_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_809_; 
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_809_ == 0)
{
lean_object* v_unused_810_; 
v_unused_810_ = lean_ctor_get(v___x_798_, 0);
lean_dec(v_unused_810_);
v___x_800_ = v___x_798_;
v_isShared_801_ = v_isSharedCheck_809_;
goto v_resetjp_799_;
}
else
{
lean_dec(v___x_798_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_809_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_807_; 
v___x_802_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f___closed__0));
v___x_803_ = lean_unsigned_to_nat(80u);
v___x_804_ = l_Lean_Json_pretty(v_j_776_, v___x_803_);
v___x_805_ = lean_string_append(v___x_802_, v___x_804_);
lean_dec_ref(v___x_804_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v___x_805_);
v___x_807_ = v___x_800_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
else
{
lean_object* v_a_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
lean_dec(v_j_776_);
v_a_811_ = lean_ctor_get(v___x_798_, 0);
lean_inc_n(v_a_811_, 2);
lean_dec_ref_known(v___x_798_, 1);
v___x_812_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__17));
v___x_813_ = l_Lean_Json_getObjVal_x3f(v_a_811_, v___x_812_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_dec(v_a_811_);
v_a_814_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_813_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_813_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
else
{
lean_object* v_a_822_; lean_object* v___x_823_; 
v_a_822_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_a_822_);
lean_dec_ref_known(v___x_813_, 1);
v___x_823_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f(v_a_822_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
lean_dec(v_a_811_);
v_a_824_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v_a_832_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_832_);
lean_dec_ref_known(v___x_823_, 1);
v___x_833_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__18));
lean_inc(v_a_811_);
v___x_834_ = l_Lean_Json_getObjVal_x3f(v_a_811_, v___x_833_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_dec(v_a_832_);
lean_dec(v_a_811_);
v_a_835_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_834_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_834_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_844_; 
v_a_843_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_a_843_);
lean_dec_ref_known(v___x_834_, 1);
v___x_844_ = l_Lean_Json_getNat_x3f(v_a_843_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
lean_dec(v_a_832_);
lean_dec(v_a_811_);
v_a_845_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_844_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_844_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
else
{
lean_object* v_a_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v_a_853_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v___x_844_, 1);
v___x_854_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__19));
v___x_855_ = l_Lean_Json_getObjVal_x3f(v_a_811_, v___x_854_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
lean_dec(v_a_853_);
lean_dec(v_a_832_);
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_865_; 
v_a_864_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_864_);
lean_dec_ref_known(v___x_855_, 1);
v___x_865_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f(v_a_864_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_dec(v_a_853_);
lean_dec(v_a_832_);
return v___x_865_;
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_874_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_874_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_874_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_874_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_870_ = l_Lean_Expr_proj___override(v_a_832_, v_a_853_, v_a_866_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_870_);
v___x_872_ = v___x_868_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
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
else
{
lean_object* v_a_875_; lean_object* v___x_876_; 
lean_dec(v_j_776_);
v_a_875_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_a_875_);
lean_dec_ref_known(v___x_796_, 1);
v___x_876_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_literalFromJson_x3f(v_a_875_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_893_; 
v_a_885_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_893_ == 0)
{
v___x_887_ = v___x_876_;
v_isShared_888_ = v_isSharedCheck_893_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_876_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_893_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_889_; lean_object* v___x_891_; 
v___x_889_ = l_Lean_Expr_lit___override(v_a_885_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_889_);
v___x_891_ = v___x_887_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
lean_dec(v_j_776_);
v_a_894_ = lean_ctor_get(v___x_794_, 0);
lean_inc_n(v_a_894_, 2);
lean_dec_ref_known(v___x_794_, 1);
v___x_895_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__7));
v___x_896_ = l_Lean_Json_getObjVal_x3f(v_a_894_, v___x_895_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_dec(v_a_894_);
v_a_897_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_896_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_896_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_906_; 
v_a_905_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_a_905_);
lean_dec_ref_known(v___x_896_, 1);
v___x_906_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f(v_a_905_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_dec(v_a_894_);
v_a_907_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_906_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v_a_915_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_a_915_);
lean_dec_ref_known(v___x_906_, 1);
v___x_916_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__8));
lean_inc(v_a_894_);
v___x_917_ = l_Lean_Json_getObjVal_x3f(v_a_894_, v___x_916_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_dec(v_a_915_);
lean_dec(v_a_894_);
v_a_918_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_917_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_917_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_927_; 
v_a_926_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_a_926_);
lean_dec_ref_known(v___x_917_, 1);
v___x_927_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f(v_a_926_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_dec(v_a_915_);
lean_dec(v_a_894_);
return v___x_927_;
}
else
{
lean_object* v_a_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_a_928_);
lean_dec_ref_known(v___x_927_, 1);
v___x_929_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__13));
lean_inc(v_a_894_);
v___x_930_ = l_Lean_Json_getObjVal_x3f(v_a_894_, v___x_929_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
lean_dec(v_a_928_);
lean_dec(v_a_915_);
lean_dec(v_a_894_);
v_a_931_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
else
{
lean_object* v_a_939_; lean_object* v___x_940_; 
v_a_939_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_a_939_);
lean_dec_ref_known(v___x_930_, 1);
v___x_940_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f(v_a_939_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_dec(v_a_928_);
lean_dec(v_a_915_);
lean_dec(v_a_894_);
return v___x_940_;
}
else
{
lean_object* v_a_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_941_);
lean_dec_ref_known(v___x_940_, 1);
v___x_942_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__9));
lean_inc(v_a_894_);
v___x_943_ = l_Lean_Json_getObjVal_x3f(v_a_894_, v___x_942_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
lean_dec(v_a_941_);
lean_dec(v_a_928_);
lean_dec(v_a_915_);
lean_dec(v_a_894_);
v_a_944_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_951_ == 0)
{
v___x_946_ = v___x_943_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_944_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
else
{
lean_object* v_a_952_; lean_object* v___x_953_; 
v_a_952_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_a_952_);
lean_dec_ref_known(v___x_943_, 1);
v___x_953_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f(v_a_952_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_dec(v_a_941_);
lean_dec(v_a_928_);
lean_dec(v_a_915_);
lean_dec(v_a_894_);
return v___x_953_;
}
else
{
lean_object* v_a_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_953_, 1);
v___x_955_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__14));
v___x_956_ = l_Lean_Json_getObjVal_x3f(v_a_894_, v___x_955_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
lean_dec(v_a_954_);
lean_dec(v_a_941_);
lean_dec(v_a_928_);
lean_dec(v_a_915_);
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
else
{
lean_object* v_a_965_; lean_object* v___x_966_; 
v_a_965_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_a_965_);
lean_dec_ref_known(v___x_956_, 1);
v___x_966_ = l_Lean_Json_getBool_x3f(v_a_965_);
lean_dec(v_a_965_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_dec(v_a_954_);
lean_dec(v_a_941_);
lean_dec(v_a_928_);
lean_dec(v_a_915_);
v_a_967_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_966_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_966_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_984_; 
v_a_975_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_984_ == 0)
{
v___x_977_ = v___x_966_;
v_isShared_978_ = v_isSharedCheck_984_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_966_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_984_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
uint8_t v___x_979_; lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_979_ = lean_unbox(v_a_975_);
lean_dec(v_a_975_);
v___x_980_ = l_Lean_Expr_letE___override(v_a_915_, v_a_928_, v_a_941_, v_a_954_, v___x_979_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_980_);
v___x_982_ = v___x_977_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
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
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
lean_dec(v_j_776_);
v_a_985_ = lean_ctor_get(v___x_792_, 0);
lean_inc_n(v_a_985_, 2);
lean_dec_ref_known(v___x_792_, 1);
v___x_986_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__7));
v___x_987_ = l_Lean_Json_getObjVal_x3f(v_a_985_, v___x_986_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec(v_a_985_);
v_a_988_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_987_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_987_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_997_; 
v_a_996_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_996_);
lean_dec_ref_known(v___x_987_, 1);
v___x_997_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f(v_a_996_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
lean_dec(v_a_985_);
v_a_998_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_997_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_997_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_a_1006_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_997_, 1);
v___x_1007_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__8));
lean_inc(v_a_985_);
v___x_1008_ = l_Lean_Json_getObjVal_x3f(v_a_985_, v___x_1007_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
lean_dec(v_a_1006_);
lean_dec(v_a_985_);
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_1008_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1008_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1018_; 
v_a_1017_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___x_1008_, 1);
v___x_1018_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f(v_a_1017_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_dec(v_a_1006_);
lean_dec(v_a_985_);
return v___x_1018_;
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___x_1018_, 1);
v___x_1020_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__9));
lean_inc(v_a_985_);
v___x_1021_ = l_Lean_Json_getObjVal_x3f(v_a_985_, v___x_1020_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec(v_a_1019_);
lean_dec(v_a_1006_);
lean_dec(v_a_985_);
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_1021_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1021_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1031_; 
v_a_1030_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1030_);
lean_dec_ref_known(v___x_1021_, 1);
v___x_1031_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f(v_a_1030_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_dec(v_a_1019_);
lean_dec(v_a_1006_);
lean_dec(v_a_985_);
return v___x_1031_;
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v___x_1033_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__10));
v___x_1034_ = l_Lean_Json_getObjVal_x3f(v_a_985_, v___x_1033_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec(v_a_1032_);
lean_dec(v_a_1019_);
lean_dec(v_a_1006_);
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_1034_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1034_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1044_; 
v_a_1043_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1043_);
lean_dec_ref_known(v___x_1034_, 1);
v___x_1044_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoFromJson_x3f(v_a_1043_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec(v_a_1032_);
lean_dec(v_a_1019_);
lean_dec(v_a_1006_);
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1044_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1044_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1062_; 
v_a_1053_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1055_ = v___x_1044_;
v_isShared_1056_ = v_isSharedCheck_1062_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1044_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1062_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
uint8_t v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1057_ = lean_unbox(v_a_1053_);
lean_dec(v_a_1053_);
v___x_1058_ = l_Lean_Expr_forallE___override(v_a_1006_, v_a_1019_, v_a_1032_, v___x_1057_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v___x_1058_);
v___x_1060_ = v___x_1055_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1058_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
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
else
{
lean_object* v_a_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
lean_dec(v_j_776_);
v_a_1063_ = lean_ctor_get(v___x_790_, 0);
lean_inc_n(v_a_1063_, 2);
lean_dec_ref_known(v___x_790_, 1);
v___x_1064_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__7));
v___x_1065_ = l_Lean_Json_getObjVal_x3f(v_a_1063_, v___x_1064_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_dec(v_a_1063_);
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1065_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1065_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1075_; 
v_a_1074_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_a_1074_);
lean_dec_ref_known(v___x_1065_, 1);
v___x_1075_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f(v_a_1074_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
lean_dec(v_a_1063_);
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1075_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1075_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v_a_1084_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v___x_1075_, 1);
v___x_1085_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__8));
lean_inc(v_a_1063_);
v___x_1086_ = l_Lean_Json_getObjVal_x3f(v_a_1063_, v___x_1085_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec(v_a_1084_);
lean_dec(v_a_1063_);
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1086_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1086_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1096_; 
v_a_1095_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1095_);
lean_dec_ref_known(v___x_1086_, 1);
v___x_1096_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f(v_a_1095_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_dec(v_a_1084_);
lean_dec(v_a_1063_);
return v___x_1096_;
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1097_);
lean_dec_ref_known(v___x_1096_, 1);
v___x_1098_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__9));
lean_inc(v_a_1063_);
v___x_1099_ = l_Lean_Json_getObjVal_x3f(v_a_1063_, v___x_1098_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec(v_a_1097_);
lean_dec(v_a_1084_);
lean_dec(v_a_1063_);
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1099_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1099_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1109_; 
v_a_1108_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_a_1108_);
lean_dec_ref_known(v___x_1099_, 1);
v___x_1109_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f(v_a_1108_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_dec(v_a_1097_);
lean_dec(v_a_1084_);
lean_dec(v_a_1063_);
return v___x_1109_;
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref_known(v___x_1109_, 1);
v___x_1111_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__10));
v___x_1112_ = l_Lean_Json_getObjVal_x3f(v_a_1063_, v___x_1111_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec(v_a_1110_);
lean_dec(v_a_1097_);
lean_dec(v_a_1084_);
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1112_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1112_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1122_; 
v_a_1121_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1121_);
lean_dec_ref_known(v___x_1112_, 1);
v___x_1122_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_binderInfoFromJson_x3f(v_a_1121_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_dec(v_a_1110_);
lean_dec(v_a_1097_);
lean_dec(v_a_1084_);
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1122_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1122_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1140_; 
v_a_1131_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1133_ = v___x_1122_;
v_isShared_1134_ = v_isSharedCheck_1140_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1122_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1140_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
uint8_t v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1138_; 
v___x_1135_ = lean_unbox(v_a_1131_);
lean_dec(v_a_1131_);
v___x_1136_ = l_Lean_Expr_lam___override(v_a_1084_, v_a_1097_, v_a_1110_, v___x_1135_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v___x_1136_);
v___x_1138_ = v___x_1133_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
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
else
{
lean_object* v_a_1141_; lean_object* v___x_1142_; 
lean_dec(v_j_776_);
v_a_1141_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_1141_);
lean_dec_ref_known(v___x_788_, 1);
v___x_1142_ = l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f_spec__0(v_a_1141_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1142_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1142_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v_a_1151_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1151_);
lean_dec_ref_known(v___x_1142_, 1);
v___x_1152_ = lean_array_get_size(v_a_1151_);
v___x_1153_ = lean_unsigned_to_nat(2u);
v___x_1154_ = lean_nat_dec_eq(v___x_1152_, v___x_1153_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; 
lean_dec(v_a_1151_);
v___x_1155_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f___closed__2));
return v___x_1155_;
}
else
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1156_ = lean_unsigned_to_nat(0u);
v___x_1157_ = lean_array_fget_borrowed(v_a_1151_, v___x_1156_);
lean_inc(v___x_1157_);
v___x_1158_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f(v___x_1157_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_dec(v_a_1151_);
return v___x_1158_;
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_1158_, 1);
v___x_1160_ = lean_unsigned_to_nat(1u);
v___x_1161_ = lean_array_fget(v_a_1151_, v___x_1160_);
lean_dec(v_a_1151_);
v___x_1162_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f(v___x_1161_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_dec(v_a_1159_);
return v___x_1162_;
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1171_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1165_ = v___x_1162_;
v_isShared_1166_ = v_isSharedCheck_1171_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1162_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1171_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1167_ = l_Lean_Expr_app___override(v_a_1159_, v_a_1163_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v___x_1167_);
v___x_1169_ = v___x_1165_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
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
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_dec(v_j_776_);
v_a_1172_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_786_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_786_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
lean_ctor_set_tag(v___x_1174_, 0);
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1181_; 
v_a_1180_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_1180_);
lean_dec_ref_known(v___x_786_, 1);
v___x_1181_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f(v_a_1180_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
lean_dec(v_j_776_);
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1181_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1181_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v_a_1190_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1190_);
lean_dec_ref_known(v___x_1181_, 1);
v___x_1191_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__4));
v___x_1192_ = l_Lean_Json_getObjVal_x3f(v_j_776_, v___x_1191_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec(v_a_1190_);
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
else
{
lean_object* v_a_1201_; lean_object* v___x_1202_; 
v_a_1201_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_a_1201_);
lean_dec_ref_known(v___x_1192_, 1);
v___x_1202_ = l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f_spec__0(v_a_1201_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec(v_a_1190_);
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1202_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1202_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
else
{
lean_object* v_a_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v_a_1211_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1211_);
lean_dec_ref_known(v___x_1202_, 1);
v___x_1212_ = lean_array_to_list(v_a_1211_);
v___x_1213_ = lean_box(0);
v___x_1214_ = l_List_mapM_loop___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f_spec__0(v___x_1212_, v___x_1213_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
lean_dec(v_a_1190_);
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1214_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1214_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1231_; 
v_a_1223_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1225_ = v___x_1214_;
v_isShared_1226_ = v_isSharedCheck_1231_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1214_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1231_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1227_; lean_object* v___x_1229_; 
v___x_1227_ = l_Lean_Expr_const___override(v_a_1190_, v_a_1223_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v___x_1227_);
v___x_1229_ = v___x_1225_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1227_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
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
lean_object* v_a_1232_; lean_object* v___x_1233_; 
lean_dec(v_j_776_);
v_a_1232_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_1232_);
lean_dec_ref_known(v___x_784_, 1);
v___x_1233_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f(v_a_1232_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1233_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1233_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1250_; 
v_a_1242_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1244_ = v___x_1233_;
v_isShared_1245_ = v_isSharedCheck_1250_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1233_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1250_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1246_; lean_object* v___x_1248_; 
v___x_1246_ = l_Lean_Expr_sort___override(v_a_1242_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___x_1246_);
v___x_1248_ = v___x_1244_;
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
}
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1252_; 
lean_dec(v_j_776_);
v_a_1251_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_1251_);
lean_dec_ref_known(v___x_782_, 1);
v___x_1252_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f(v_a_1251_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___x_1252_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1252_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1269_; 
v_a_1261_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1263_ = v___x_1252_;
v_isShared_1264_ = v_isSharedCheck_1269_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1252_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1269_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; lean_object* v___x_1267_; 
v___x_1265_ = l_Lean_Expr_mvar___override(v_a_1261_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1265_);
v___x_1267_ = v___x_1263_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1271_; 
lean_dec(v_j_776_);
v_a_1270_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v___x_780_, 1);
v___x_1271_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f(v_a_1270_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1271_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1271_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1288_; 
v_a_1280_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1282_ = v___x_1271_;
v_isShared_1283_ = v_isSharedCheck_1288_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1271_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1288_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1284_; lean_object* v___x_1286_; 
v___x_1284_ = l_Lean_Expr_fvar___override(v_a_1280_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 0, v___x_1284_);
v___x_1286_ = v___x_1282_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1290_; 
lean_dec(v_j_776_);
v_a_1289_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_a_1289_);
lean_dec_ref_known(v___x_778_, 1);
v___x_1290_ = l_Lean_Json_getNat_x3f(v_a_1289_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1290_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1290_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1307_; 
v_a_1299_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1301_ = v___x_1290_;
v_isShared_1302_ = v_isSharedCheck_1307_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1290_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1307_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___x_1303_ = l_Lean_Expr_bvar___override(v_a_1299_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v___x_1303_);
v___x_1305_ = v___x_1301_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
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
}
LEAN_EXPORT uint16_t l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgPort(lean_object* v_siteId_1308_){
_start:
{
uint64_t v_h_1309_; uint64_t v___x_1310_; uint64_t v___x_1311_; uint64_t v___x_1312_; uint64_t v___x_1313_; uint16_t v___x_1314_; 
v_h_1309_ = lean_string_hash(v_siteId_1308_);
v___x_1310_ = 55535ULL;
v___x_1311_ = lean_uint64_mod(v_h_1309_, v___x_1310_);
v___x_1312_ = 10000ULL;
v___x_1313_ = lean_uint64_add(v___x_1311_, v___x_1312_);
v___x_1314_ = lean_uint64_to_uint16(v___x_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgPort___boxed(lean_object* v_siteId_1315_){
_start:
{
uint16_t v_res_1316_; lean_object* v_r_1317_; 
v_res_1316_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgPort(v_siteId_1315_);
lean_dec_ref(v_siteId_1315_);
v_r_1317_ = lean_box(v_res_1316_);
return v_r_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___lam__0(lean_object* v___x_1318_, lean_object* v_x_1319_){
_start:
{
if (lean_obj_tag(v_x_1319_) == 0)
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = lean_mk_io_user_error(v___x_1318_);
v___x_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
return v___x_1321_;
}
else
{
lean_object* v_val_1322_; 
lean_dec_ref(v___x_1318_);
v_val_1322_ = lean_ctor_get(v_x_1319_, 0);
lean_inc(v_val_1322_);
return v_val_1322_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___lam__0___boxed(lean_object* v___x_1323_, lean_object* v_x_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___lam__0(v___x_1323_, v_x_1324_);
lean_dec(v_x_1324_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___lam__1(lean_object* v___f_1326_, lean_object* v_x_1327_){
_start:
{
if (lean_obj_tag(v_x_1327_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1337_; 
lean_dec_ref(v___f_1326_);
v_a_1329_ = lean_ctor_get(v_x_1327_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_x_1327_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1331_ = v_x_1327_;
v_isShared_1332_ = v_isSharedCheck_1337_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v_x_1327_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1337_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
lean_object* v___x_1335_; 
v___x_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
return v___x_1335_;
}
}
}
else
{
lean_object* v_a_1338_; 
v_a_1338_ = lean_ctor_get(v_x_1327_, 0);
lean_inc(v_a_1338_);
lean_dec_ref_known(v_x_1327_, 1);
if (lean_obj_tag(v_a_1338_) == 0)
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1347_; 
lean_dec_ref(v___f_1326_);
v_a_1339_ = lean_ctor_get(v_a_1338_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_a_1338_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1341_ = v_a_1338_;
v_isShared_1342_ = v_isSharedCheck_1347_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v_a_1338_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1347_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1339_);
v___x_1344_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
lean_object* v___x_1345_; 
v___x_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
return v___x_1345_;
}
}
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v_a_1348_ = lean_ctor_get(v_a_1338_, 0);
lean_inc(v_a_1348_);
lean_dec_ref_known(v_a_1338_, 1);
v___x_1349_ = lean_io_promise_result_opt(v_a_1348_);
lean_dec(v_a_1348_);
v___x_1350_ = lean_unsigned_to_nat(0u);
v___x_1351_ = 0;
v___x_1352_ = lean_task_map(v___f_1326_, v___x_1349_, v___x_1350_, v___x_1351_);
v___x_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
return v___x_1353_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___lam__1___boxed(lean_object* v___f_1354_, lean_object* v_x_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___lam__1(v___f_1354_, v_x_1355_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg(lean_object* v_client_1364_, lean_object* v_msg_1365_){
_start:
{
lean_object* v_bytes_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v_header_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___f_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; lean_object* v_val_1381_; lean_object* v___x_1390_; 
v_bytes_1367_ = lean_string_to_utf8(v_msg_1365_);
v___x_1368_ = lean_byte_array_size(v_bytes_1367_);
v___x_1369_ = l_Nat_reprFast(v___x_1368_);
v___x_1370_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___closed__0));
v___x_1371_ = lean_string_append(v___x_1369_, v___x_1370_);
v_header_1372_ = lean_string_to_utf8(v___x_1371_);
lean_dec_ref(v___x_1371_);
v___x_1373_ = lean_unsigned_to_nat(2u);
v___x_1374_ = lean_mk_empty_array_with_capacity(v___x_1373_);
v___x_1375_ = lean_array_push(v___x_1374_, v_header_1372_);
v___x_1376_ = lean_array_push(v___x_1375_, v_bytes_1367_);
v___f_1377_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___closed__3));
v___x_1378_ = lean_unsigned_to_nat(0u);
v___x_1379_ = 0;
v___x_1390_ = lean_uv_tcp_send(v_client_1364_, v___x_1376_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1390_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1390_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set_tag(v___x_1393_, 1);
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
v_val_1381_ = v___x_1396_;
goto v___jp_1380_;
}
}
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
v_a_1399_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1390_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1390_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
lean_ctor_set_tag(v___x_1401_, 0);
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
v_val_1381_ = v___x_1404_;
goto v___jp_1380_;
}
}
}
v___jp_1380_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1382_, 0, v_val_1381_);
v___x_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
v___x_1384_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1378_, v___x_1379_, v___x_1383_, v___f_1377_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1384_, 1);
v___x_1386_ = lean_task_pure(v_a_1385_);
v___x_1387_ = l_Std_Async_AsyncTask_block___redArg(v___x_1386_);
return v___x_1387_;
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1389_; 
v_a_1388_ = lean_ctor_get(v___x_1384_, 0);
lean_inc_ref(v_a_1388_);
lean_dec_ref_known(v___x_1384_, 1);
v___x_1389_ = l_Std_Async_AsyncTask_block___redArg(v_a_1388_);
return v___x_1389_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___boxed(lean_object* v_client_1407_, lean_object* v_msg_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg(v_client_1407_, v_msg_1408_);
lean_dec_ref(v_msg_1408_);
lean_dec(v_client_1407_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___lam__1(lean_object* v___f_1411_, lean_object* v_x_1412_){
_start:
{
if (lean_obj_tag(v_x_1412_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1422_; 
lean_dec_ref(v___f_1411_);
v_a_1414_ = lean_ctor_get(v_x_1412_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v_x_1412_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1416_ = v_x_1412_;
v_isShared_1417_ = v_isSharedCheck_1422_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v_x_1412_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1422_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
lean_object* v___x_1420_; 
v___x_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
return v___x_1420_;
}
}
}
else
{
lean_object* v_a_1423_; 
v_a_1423_ = lean_ctor_get(v_x_1412_, 0);
lean_inc(v_a_1423_);
lean_dec_ref_known(v_x_1412_, 1);
if (lean_obj_tag(v_a_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1432_; 
lean_dec_ref(v___f_1411_);
v_a_1424_ = lean_ctor_get(v_a_1423_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_a_1423_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1426_ = v_a_1423_;
v_isShared_1427_ = v_isSharedCheck_1432_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v_a_1423_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1432_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1424_);
v___x_1429_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1430_; 
v___x_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
return v___x_1430_;
}
}
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v_a_1433_ = lean_ctor_get(v_a_1423_, 0);
lean_inc(v_a_1433_);
lean_dec_ref_known(v_a_1423_, 1);
v___x_1434_ = lean_io_promise_result_opt(v_a_1433_);
lean_dec(v_a_1433_);
v___x_1435_ = lean_unsigned_to_nat(0u);
v___x_1436_ = 0;
v___x_1437_ = lean_task_map(v___f_1411_, v___x_1434_, v___x_1435_, v___x_1436_);
v___x_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
return v___x_1438_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___lam__1___boxed(lean_object* v___f_1439_, lean_object* v_x_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___lam__1(v___f_1439_, v_x_1440_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___lam__0(lean_object* v___x_1443_, lean_object* v_x_1444_){
_start:
{
if (lean_obj_tag(v_x_1444_) == 0)
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1445_ = lean_mk_io_user_error(v___x_1443_);
v___x_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
return v___x_1446_;
}
else
{
lean_object* v_val_1447_; 
lean_dec_ref(v___x_1443_);
v_val_1447_ = lean_ctor_get(v_x_1444_, 0);
lean_inc(v_val_1447_);
return v_val_1447_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___lam__0___boxed(lean_object* v___x_1448_, lean_object* v_x_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___lam__0(v___x_1448_, v_x_1449_);
lean_dec(v_x_1449_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg(lean_object* v_client_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v___y_1462_; uint8_t v___y_1463_; uint8_t v___x_1472_; lean_object* v_a_1474_; uint64_t v___x_1501_; lean_object* v___f_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; lean_object* v_val_1506_; lean_object* v___x_1513_; 
v___x_1472_ = 0;
v___x_1501_ = 1ULL;
v___f_1502_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___closed__3));
v___x_1503_ = lean_unsigned_to_nat(0u);
v___x_1504_ = 0;
v___x_1513_ = lean_uv_tcp_recv(v_client_1458_, v___x_1501_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1513_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1513_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
lean_ctor_set_tag(v___x_1516_, 1);
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
v_val_1506_ = v___x_1519_;
goto v___jp_1505_;
}
}
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
v_a_1522_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1513_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1513_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
lean_ctor_set_tag(v___x_1524_, 0);
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
v_val_1506_ = v___x_1527_;
goto v___jp_1505_;
}
}
}
v___jp_1461_:
{
uint8_t v___x_1464_; uint8_t v___x_1465_; 
v___x_1464_ = 10;
v___x_1465_ = lean_uint8_dec_eq(v___y_1463_, v___x_1464_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1466_ = lean_unsigned_to_nat(0u);
v___x_1467_ = lean_byte_array_size(v_a_1459_);
v___x_1468_ = lean_byte_array_size(v___y_1462_);
v___x_1469_ = lean_byte_array_copy_slice(v___y_1462_, v___x_1466_, v_a_1459_, v___x_1467_, v___x_1468_, v___x_1465_);
lean_dec_ref(v___y_1462_);
v_a_1459_ = v___x_1469_;
goto _start;
}
else
{
lean_object* v___x_1471_; 
lean_dec_ref(v___y_1462_);
v___x_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1471_, 0, v_a_1459_);
return v___x_1471_;
}
}
v___jp_1473_:
{
lean_object* v___x_1475_; 
v___x_1475_ = l_Std_Async_AsyncTask_block___redArg(v_a_1474_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1492_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1492_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1492_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
if (lean_obj_tag(v_a_1476_) == 1)
{
lean_object* v_val_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; uint8_t v___x_1483_; 
lean_del_object(v___x_1478_);
v_val_1480_ = lean_ctor_get(v_a_1476_, 0);
lean_inc(v_val_1480_);
lean_dec_ref_known(v_a_1476_, 1);
v___x_1481_ = lean_unsigned_to_nat(0u);
v___x_1482_ = lean_byte_array_size(v_val_1480_);
v___x_1483_ = lean_nat_dec_lt(v___x_1481_, v___x_1482_);
if (v___x_1483_ == 0)
{
lean_object* v___x_1484_; lean_object* v___x_1485_; uint8_t v___x_1486_; 
v___x_1484_ = lean_box(v___x_1472_);
v___x_1485_ = l_outOfBounds___redArg(v___x_1484_);
lean_dec(v___x_1484_);
v___x_1486_ = lean_unbox(v___x_1485_);
lean_dec(v___x_1485_);
v___y_1462_ = v_val_1480_;
v___y_1463_ = v___x_1486_;
goto v___jp_1461_;
}
else
{
uint8_t v___x_1487_; 
v___x_1487_ = lean_byte_array_fget(v_val_1480_, v___x_1481_);
v___y_1462_ = v_val_1480_;
v___y_1463_ = v___x_1487_;
goto v___jp_1461_;
}
}
else
{
lean_object* v___x_1488_; lean_object* v___x_1490_; 
lean_dec(v_a_1476_);
lean_dec_ref(v_a_1459_);
v___x_1488_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___closed__1));
if (v_isShared_1479_ == 0)
{
lean_ctor_set_tag(v___x_1478_, 1);
lean_ctor_set(v___x_1478_, 0, v___x_1488_);
v___x_1490_ = v___x_1478_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1488_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
lean_dec_ref(v_a_1459_);
v_a_1493_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1495_ = v___x_1475_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1475_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1493_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
v___jp_1505_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1507_, 0, v_val_1506_);
v___x_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
v___x_1509_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1503_, v___x_1504_, v___x_1508_, v___f_1502_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v___x_1511_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
lean_dec_ref_known(v___x_1509_, 1);
v___x_1511_ = lean_task_pure(v_a_1510_);
v_a_1474_ = v___x_1511_;
goto v___jp_1473_;
}
else
{
lean_object* v_a_1512_; 
v_a_1512_ = lean_ctor_get(v___x_1509_, 0);
lean_inc_ref(v_a_1512_);
lean_dec_ref_known(v___x_1509_, 1);
v_a_1474_ = v_a_1512_;
goto v___jp_1473_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___boxed(lean_object* v_client_1530_, lean_object* v_a_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg(v_client_1530_, v_a_1531_);
lean_dec(v_client_1530_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__1___redArg(lean_object* v_val_1534_, lean_object* v_client_1535_, lean_object* v_a_1536_){
_start:
{
lean_object* v_a_1539_; lean_object* v___x_1565_; uint8_t v___x_1566_; 
v___x_1565_ = lean_byte_array_size(v_a_1536_);
v___x_1566_ = lean_nat_dec_lt(v___x_1565_, v_val_1534_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; 
v___x_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1567_, 0, v_a_1536_);
return v___x_1567_;
}
else
{
lean_object* v___x_1568_; uint64_t v___x_1569_; lean_object* v___f_1570_; lean_object* v___x_1571_; uint8_t v___x_1572_; lean_object* v_val_1574_; lean_object* v___x_1581_; 
v___x_1568_ = lean_nat_sub(v_val_1534_, v___x_1565_);
v___x_1569_ = lean_uint64_of_nat(v___x_1568_);
lean_dec(v___x_1568_);
v___f_1570_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___closed__3));
v___x_1571_ = lean_unsigned_to_nat(0u);
v___x_1572_ = 0;
v___x_1581_ = lean_uv_tcp_recv(v_client_1535_, v___x_1569_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1581_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1581_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
lean_ctor_set_tag(v___x_1584_, 1);
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
v_val_1574_ = v___x_1587_;
goto v___jp_1573_;
}
}
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
v_a_1590_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1581_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1581_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
lean_ctor_set_tag(v___x_1592_, 0);
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
v_val_1574_ = v___x_1595_;
goto v___jp_1573_;
}
}
}
v___jp_1573_:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1575_, 0, v_val_1574_);
v___x_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
v___x_1577_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1571_, v___x_1572_, v___x_1576_, v___f_1570_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1579_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1577_, 1);
v___x_1579_ = lean_task_pure(v_a_1578_);
v_a_1539_ = v___x_1579_;
goto v___jp_1538_;
}
else
{
lean_object* v_a_1580_; 
v_a_1580_ = lean_ctor_get(v___x_1577_, 0);
lean_inc_ref(v_a_1580_);
lean_dec_ref_known(v___x_1577_, 1);
v_a_1539_ = v_a_1580_;
goto v___jp_1538_;
}
}
}
v___jp_1538_:
{
lean_object* v___x_1540_; 
v___x_1540_ = l_Std_Async_AsyncTask_block___redArg(v_a_1539_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1556_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1543_ = v___x_1540_;
v_isShared_1544_ = v_isSharedCheck_1556_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1540_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1556_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
if (lean_obj_tag(v_a_1541_) == 1)
{
lean_object* v_val_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; lean_object* v___x_1550_; 
lean_del_object(v___x_1543_);
v_val_1545_ = lean_ctor_get(v_a_1541_, 0);
lean_inc(v_val_1545_);
lean_dec_ref_known(v_a_1541_, 1);
v___x_1546_ = lean_unsigned_to_nat(0u);
v___x_1547_ = lean_byte_array_size(v_a_1536_);
v___x_1548_ = lean_byte_array_size(v_val_1545_);
v___x_1549_ = 0;
v___x_1550_ = lean_byte_array_copy_slice(v_val_1545_, v___x_1546_, v_a_1536_, v___x_1547_, v___x_1548_, v___x_1549_);
lean_dec(v_val_1545_);
v_a_1536_ = v___x_1550_;
goto _start;
}
else
{
lean_object* v___x_1552_; lean_object* v___x_1554_; 
lean_dec(v_a_1541_);
lean_dec_ref(v_a_1536_);
v___x_1552_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___closed__1));
if (v_isShared_1544_ == 0)
{
lean_ctor_set_tag(v___x_1543_, 1);
lean_ctor_set(v___x_1543_, 0, v___x_1552_);
v___x_1554_ = v___x_1543_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec_ref(v_a_1536_);
v_a_1557_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1540_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1540_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__1___redArg___boxed(lean_object* v_val_1598_, lean_object* v_client_1599_, lean_object* v_a_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__1___redArg(v_val_1598_, v_client_1599_, v_a_1600_);
lean_dec(v_client_1599_);
lean_dec(v_val_1598_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg(lean_object* v_client_1612_){
_start:
{
lean_object* v_header_1614_; lean_object* v___x_1615_; 
v_header_1614_ = l_ByteArray_empty;
v___x_1615_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg(v_client_1612_, v_header_1614_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1658_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1618_ = v___x_1615_;
v_isShared_1619_ = v_isSharedCheck_1658_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1615_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1658_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
uint8_t v___x_1620_; 
v___x_1620_ = lean_string_validate_utf8(v_a_1616_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; lean_object* v___x_1623_; 
lean_dec(v_a_1616_);
v___x_1621_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___closed__1));
if (v_isShared_1619_ == 0)
{
lean_ctor_set_tag(v___x_1618_, 1);
lean_ctor_set(v___x_1618_, 0, v___x_1621_);
v___x_1623_ = v___x_1618_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
else
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1625_ = lean_string_from_utf8_unchecked(v_a_1616_);
v___x_1626_ = lean_unsigned_to_nat(0u);
v___x_1627_ = lean_string_utf8_byte_size(v___x_1625_);
v___x_1628_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1625_);
lean_ctor_set(v___x_1628_, 1, v___x_1626_);
lean_ctor_set(v___x_1628_, 2, v___x_1627_);
v___x_1629_ = l_String_Slice_toNat_x3f(v___x_1628_);
lean_dec_ref_known(v___x_1628_, 3);
if (lean_obj_tag(v___x_1629_) == 1)
{
lean_object* v_val_1630_; lean_object* v___x_1631_; 
lean_del_object(v___x_1618_);
v_val_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_val_1630_);
lean_dec_ref_known(v___x_1629_, 1);
v___x_1631_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__1___redArg(v_val_1630_, v_client_1612_, v_header_1614_);
lean_dec(v_val_1630_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1645_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1634_ = v___x_1631_;
v_isShared_1635_ = v_isSharedCheck_1645_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1631_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1645_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
uint8_t v___x_1636_; 
v___x_1636_ = lean_string_validate_utf8(v_a_1632_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; lean_object* v___x_1639_; 
lean_dec(v_a_1632_);
v___x_1637_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___closed__3));
if (v_isShared_1635_ == 0)
{
lean_ctor_set_tag(v___x_1634_, 1);
lean_ctor_set(v___x_1634_, 0, v___x_1637_);
v___x_1639_ = v___x_1634_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1637_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
else
{
lean_object* v___x_1641_; lean_object* v___x_1643_; 
v___x_1641_ = lean_string_from_utf8_unchecked(v_a_1632_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v___x_1641_);
v___x_1643_ = v___x_1634_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1641_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
v_a_1646_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1631_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1631_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1656_; 
lean_dec(v___x_1629_);
v___x_1654_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___closed__5));
if (v_isShared_1619_ == 0)
{
lean_ctor_set_tag(v___x_1618_, 1);
lean_ctor_set(v___x_1618_, 0, v___x_1654_);
v___x_1656_ = v___x_1618_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
v_a_1659_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1615_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1615_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___boxed(lean_object* v_client_1667_, lean_object* v_a_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg(v_client_1667_);
lean_dec(v_client_1667_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0(lean_object* v_client_1670_, lean_object* v_inst_1671_, lean_object* v_a_1672_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg(v_client_1670_, v_a_1672_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___boxed(lean_object* v_client_1675_, lean_object* v_inst_1676_, lean_object* v_a_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0(v_client_1675_, v_inst_1676_, v_a_1677_);
lean_dec(v_client_1675_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__1(lean_object* v_val_1680_, lean_object* v_client_1681_, lean_object* v_inst_1682_, lean_object* v_a_1683_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__1___redArg(v_val_1680_, v_client_1681_, v_a_1683_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__1___boxed(lean_object* v_val_1686_, lean_object* v_client_1687_, lean_object* v_inst_1688_, lean_object* v_a_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__1(v_val_1686_, v_client_1687_, v_inst_1688_, v_a_1689_);
lean_dec(v_client_1687_);
lean_dec(v_val_1686_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___lam__0(lean_object* v___y_1692_){
_start:
{
if (lean_obj_tag(v___y_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
v_a_1693_ = lean_ctor_get(v___y_1692_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___y_1692_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___y_1692_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___y_1692_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
else
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
v_a_1701_ = lean_ctor_get(v___y_1692_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___y_1692_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1703_ = v___y_1692_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___y_1692_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1701_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___lam__3(lean_object* v___x_1709_, lean_object* v_x_1710_){
_start:
{
if (lean_obj_tag(v_x_1710_) == 0)
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = lean_mk_io_user_error(v___x_1709_);
v___x_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1711_);
return v___x_1712_;
}
else
{
lean_object* v_val_1713_; 
lean_dec_ref(v___x_1709_);
v_val_1713_ = lean_ctor_get(v_x_1710_, 0);
lean_inc(v_val_1713_);
return v_val_1713_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___lam__3___boxed(lean_object* v___x_1714_, lean_object* v_x_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___lam__3(v___x_1714_, v_x_1715_);
lean_dec(v_x_1715_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___lam__1(lean_object* v___f_1717_, lean_object* v_x_1718_){
_start:
{
if (lean_obj_tag(v_x_1718_) == 0)
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1728_; 
lean_dec_ref(v___f_1717_);
v_a_1720_ = lean_ctor_get(v_x_1718_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v_x_1718_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1722_ = v_x_1718_;
v_isShared_1723_ = v_isSharedCheck_1728_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v_x_1718_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1728_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1720_);
v___x_1725_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
lean_object* v___x_1726_; 
v___x_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
return v___x_1726_;
}
}
}
else
{
lean_object* v_a_1729_; 
v_a_1729_ = lean_ctor_get(v_x_1718_, 0);
lean_inc(v_a_1729_);
lean_dec_ref_known(v_x_1718_, 1);
if (lean_obj_tag(v_a_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1738_; 
lean_dec_ref(v___f_1717_);
v_a_1730_ = lean_ctor_get(v_a_1729_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v_a_1729_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1732_ = v_a_1729_;
v_isShared_1733_ = v_isSharedCheck_1738_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v_a_1729_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1738_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1730_);
v___x_1735_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v___x_1736_; 
v___x_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
return v___x_1736_;
}
}
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; uint8_t v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v_a_1739_ = lean_ctor_get(v_a_1729_, 0);
lean_inc(v_a_1739_);
lean_dec_ref_known(v_a_1729_, 1);
v___x_1740_ = lean_io_promise_result_opt(v_a_1739_);
lean_dec(v_a_1739_);
v___x_1741_ = lean_unsigned_to_nat(0u);
v___x_1742_ = 0;
v___x_1743_ = lean_task_map(v___f_1717_, v___x_1740_, v___x_1741_, v___x_1742_);
v___x_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
return v___x_1744_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___lam__1___boxed(lean_object* v___f_1745_, lean_object* v_x_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___lam__1(v___f_1745_, v_x_1746_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer_spec__0___redArg(lean_object* v_addr_1749_, lean_object* v_as_x27_1750_, lean_object* v_b_1751_){
_start:
{
if (lean_obj_tag(v_as_x27_1750_) == 0)
{
lean_object* v___x_1753_; 
lean_dec_ref(v_addr_1749_);
v___x_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1753_, 0, v_b_1751_);
return v___x_1753_;
}
else
{
lean_object* v_tail_1754_; lean_object* v___x_1759_; 
v_tail_1754_ = lean_ctor_get(v_as_x27_1750_, 1);
v___x_1759_ = lean_uv_tcp_new();
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1786_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1762_ = v___x_1759_;
v_isShared_1763_ = v_isSharedCheck_1786_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1759_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1786_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
lean_inc_ref(v_addr_1749_);
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 0, v_addr_1749_);
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_addr_1749_);
v___x_1765_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
lean_object* v___x_1766_; 
v___x_1766_ = lean_uv_tcp_bind(v_a_1760_, v___x_1765_);
lean_dec_ref(v___x_1765_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1783_; 
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1783_ == 0)
{
lean_object* v_unused_1784_; 
v_unused_1784_ = lean_ctor_get(v___x_1766_, 0);
lean_dec(v_unused_1784_);
v___x_1768_ = v___x_1766_;
v_isShared_1769_ = v_isSharedCheck_1783_;
goto v_resetjp_1767_;
}
else
{
lean_dec(v___x_1766_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1783_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
uint32_t v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = 1;
v___x_1771_ = lean_uv_tcp_listen(v_a_1760_, v___x_1770_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1781_; 
lean_dec(v_b_1751_);
lean_dec_ref(v_addr_1749_);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1781_ == 0)
{
lean_object* v_unused_1782_; 
v_unused_1782_ = lean_ctor_get(v___x_1771_, 0);
lean_dec(v_unused_1782_);
v___x_1773_ = v___x_1771_;
v_isShared_1774_ = v_isSharedCheck_1781_;
goto v_resetjp_1772_;
}
else
{
lean_dec(v___x_1771_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1781_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1769_ == 0)
{
lean_ctor_set_tag(v___x_1768_, 1);
lean_ctor_set(v___x_1768_, 0, v_a_1760_);
v___x_1776_ = v___x_1768_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_a_1760_);
v___x_1776_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
lean_object* v___x_1778_; 
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1776_);
v___x_1778_ = v___x_1773_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1776_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1771_, 1);
lean_del_object(v___x_1768_);
lean_dec(v_a_1760_);
goto v___jp_1755_;
}
}
}
else
{
lean_dec_ref_known(v___x_1766_, 1);
lean_dec(v_a_1760_);
goto v___jp_1755_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1759_, 1);
goto v___jp_1755_;
}
v___jp_1755_:
{
uint32_t v___x_1756_; lean_object* v___x_1757_; 
v___x_1756_ = 100;
v___x_1757_ = l_IO_sleep(v___x_1756_);
v_as_x27_1750_ = v_tail_1754_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer_spec__0___redArg___boxed(lean_object* v_addr_1787_, lean_object* v_as_x27_1788_, lean_object* v_b_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer_spec__0___redArg(v_addr_1787_, v_as_x27_1788_, v_b_1789_);
lean_dec(v_as_x27_1788_);
return v_res_1791_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__1(void){
_start:
{
uint8_t v___x_1793_; uint8_t v___x_1794_; uint8_t v___x_1795_; lean_object* v___x_1796_; 
v___x_1793_ = 1;
v___x_1794_ = 0;
v___x_1795_ = 127;
v___x_1796_ = l_Std_Net_IPv4Addr_ofParts(v___x_1795_, v___x_1794_, v___x_1794_, v___x_1793_);
return v___x_1796_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__2(void){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = lean_unsigned_to_nat(100u);
v___x_1798_ = l_List_range(v___x_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer(lean_object* v_siteId_1803_, lean_object* v_exprJson_1804_){
_start:
{
lean_object* v___y_1807_; lean_object* v_a_1808_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; uint8_t v___y_1831_; lean_object* v_val_1832_; lean_object* v_a_1840_; lean_object* v_a_1892_; lean_object* v___f_1894_; uint16_t v_port_1895_; lean_object* v___x_1896_; lean_object* v_addr_1897_; lean_object* v_server_x3f_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1959_; 
v___f_1894_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__0));
v_port_1895_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgPort(v_siteId_1803_);
v___x_1896_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__1, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__1_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__1);
v_addr_1897_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_addr_1897_, 0, v___x_1896_);
lean_ctor_set_uint16(v_addr_1897_, sizeof(void*)*1, v_port_1895_);
v_server_x3f_1898_ = lean_box(0);
v___x_1899_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__2, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__2_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__2);
v___x_1900_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer_spec__0___redArg(v_addr_1897_, v___x_1899_, v_server_x3f_1898_);
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1903_ = v___x_1900_;
v_isShared_1904_ = v_isSharedCheck_1959_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1900_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1959_;
goto v_resetjp_1902_;
}
v___jp_1806_:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Std_Async_AsyncTask_block___redArg(v_a_1808_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1817_; 
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1817_ == 0)
{
lean_object* v_unused_1818_; 
v_unused_1818_ = lean_ctor_get(v___x_1809_, 0);
lean_dec(v_unused_1818_);
v___x_1811_ = v___x_1809_;
v_isShared_1812_ = v_isSharedCheck_1817_;
goto v_resetjp_1810_;
}
else
{
lean_dec(v___x_1809_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1817_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1813_; lean_object* v___x_1815_; 
v___x_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1813_, 0, v___y_1807_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v___x_1813_);
v___x_1815_ = v___x_1811_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
else
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
lean_dec_ref(v___y_1807_);
v_a_1819_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1809_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1809_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
v___jp_1827_:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1833_, 0, v_val_1832_);
v___x_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
lean_inc_ref(v___y_1828_);
v___x_1835_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___y_1829_, v___y_1831_, v___x_1834_, v___y_1828_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1837_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
lean_dec_ref_known(v___x_1835_, 1);
v___x_1837_ = lean_task_pure(v_a_1836_);
v___y_1807_ = v___y_1830_;
v_a_1808_ = v___x_1837_;
goto v___jp_1806_;
}
else
{
lean_object* v_a_1838_; 
v_a_1838_ = lean_ctor_get(v___x_1835_, 0);
lean_inc_ref(v_a_1838_);
lean_dec_ref_known(v___x_1835_, 1);
v___y_1807_ = v___y_1830_;
v_a_1808_ = v_a_1838_;
goto v___jp_1806_;
}
}
v___jp_1839_:
{
lean_object* v___x_1841_; 
v___x_1841_ = l_Std_Async_AsyncTask_block___redArg(v_a_1840_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref_known(v___x_1841_, 1);
v___x_1843_ = l_Lean_Json_compress(v_exprJson_1804_);
v___x_1844_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg(v_a_1842_, v___x_1843_);
lean_dec_ref(v___x_1843_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v___x_1845_; 
lean_dec_ref_known(v___x_1844_, 1);
v___x_1845_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg(v_a_1842_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___f_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; lean_object* v___x_1850_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1846_);
lean_dec_ref_known(v___x_1845_, 1);
v___f_1847_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___closed__3));
v___x_1848_ = lean_unsigned_to_nat(0u);
v___x_1849_ = 0;
v___x_1850_ = lean_uv_tcp_shutdown(v_a_1842_);
lean_dec(v_a_1842_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1850_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1850_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
lean_ctor_set_tag(v___x_1853_, 1);
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
v___y_1828_ = v___f_1847_;
v___y_1829_ = v___x_1848_;
v___y_1830_ = v_a_1846_;
v___y_1831_ = v___x_1849_;
v_val_1832_ = v___x_1856_;
goto v___jp_1827_;
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
v_a_1859_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1850_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1850_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
lean_ctor_set_tag(v___x_1861_, 0);
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
v___y_1828_ = v___f_1847_;
v___y_1829_ = v___x_1848_;
v___y_1830_ = v_a_1846_;
v___y_1831_ = v___x_1849_;
v_val_1832_ = v___x_1864_;
goto v___jp_1827_;
}
}
}
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
lean_dec(v_a_1842_);
v_a_1867_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1845_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1845_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
lean_dec(v_a_1842_);
v_a_1875_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1844_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1844_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
lean_dec(v_exprJson_1804_);
v_a_1883_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1841_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1841_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
v___jp_1891_:
{
lean_object* v___x_1893_; 
v___x_1893_ = lean_task_pure(v_a_1892_);
v_a_1840_ = v___x_1893_;
goto v___jp_1839_;
}
v_resetjp_1902_:
{
if (lean_obj_tag(v_a_1901_) == 1)
{
lean_object* v_val_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1955_; 
lean_del_object(v___x_1903_);
v_val_1905_ = lean_ctor_get(v_a_1901_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v_a_1901_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1907_ = v_a_1901_;
v_isShared_1908_ = v_isSharedCheck_1955_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_val_1905_);
lean_dec(v_a_1901_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1955_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___f_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; lean_object* v_val_1913_; lean_object* v___x_1938_; 
v___f_1909_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__4));
v___x_1910_ = lean_unsigned_to_nat(0u);
v___x_1911_ = 0;
v___x_1938_ = lean_uv_tcp_accept(v_val_1905_);
lean_dec(v_val_1905_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1938_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1938_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
lean_ctor_set_tag(v___x_1941_, 1);
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
v_val_1913_ = v___x_1944_;
goto v___jp_1912_;
}
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
v_a_1947_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1938_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1938_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
lean_ctor_set_tag(v___x_1949_, 0);
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
v_val_1913_ = v___x_1952_;
goto v___jp_1912_;
}
}
}
v___jp_1912_:
{
lean_object* v___x_1915_; 
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v_val_1913_);
v___x_1915_ = v___x_1907_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_val_1913_);
v___x_1915_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
v___x_1917_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1910_, v___x_1911_, v___x_1916_, v___f_1909_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___x_1917_, 1);
if (lean_obj_tag(v_a_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
v_a_1919_ = lean_ctor_get(v_a_1918_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v_a_1918_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v_a_1918_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v_a_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
v_a_1892_ = v___x_1924_;
goto v___jp_1891_;
}
}
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
v_a_1927_ = lean_ctor_get(v_a_1918_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v_a_1918_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v_a_1918_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v_a_1918_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
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
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
v_a_1892_ = v___x_1932_;
goto v___jp_1891_;
}
}
}
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1936_; 
v_a_1935_ = lean_ctor_get(v___x_1917_, 0);
lean_inc_ref(v_a_1935_);
lean_dec_ref_known(v___x_1917_, 1);
v___x_1936_ = lean_task_map(v___f_1894_, v_a_1935_, v___x_1910_, v___x_1911_);
v_a_1840_ = v___x_1936_;
goto v___jp_1839_;
}
}
}
}
}
else
{
lean_object* v___x_1957_; 
lean_dec(v_a_1901_);
lean_dec(v_exprJson_1804_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 0, v_server_x3f_1898_);
v___x_1957_ = v___x_1903_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_server_x3f_1898_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___boxed(lean_object* v_siteId_1960_, lean_object* v_exprJson_1961_, lean_object* v_a_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer(v_siteId_1960_, v_exprJson_1961_);
lean_dec_ref(v_siteId_1960_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer_spec__0(lean_object* v_addr_1964_, lean_object* v_as_1965_, lean_object* v_as_x27_1966_, lean_object* v_b_1967_, lean_object* v_a_1968_){
_start:
{
lean_object* v___x_1970_; 
v___x_1970_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer_spec__0___redArg(v_addr_1964_, v_as_x27_1966_, v_b_1967_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer_spec__0___boxed(lean_object* v_addr_1971_, lean_object* v_as_1972_, lean_object* v_as_x27_1973_, lean_object* v_b_1974_, lean_object* v_a_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer_spec__0(v_addr_1971_, v_as_1972_, v_as_x27_1973_, v_b_1974_, v_a_1975_);
lean_dec(v_as_x27_1973_);
lean_dec(v_as_1972_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgLoadEnv(lean_object* v_imports_1980_){
_start:
{
lean_object* v___x_1982_; uint32_t v___x_1983_; lean_object* v___x_1984_; uint8_t v___x_1985_; uint8_t v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1982_ = l_Lean_Options_empty;
v___x_1983_ = 0;
v___x_1984_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgLoadEnv___closed__0));
v___x_1985_ = 0;
v___x_1986_ = 2;
v___x_1987_ = lean_box(1);
lean_inc_ref(v_imports_1980_);
v___x_1988_ = l_Lean_importModules(v_imports_1980_, v___x_1982_, v___x_1983_, v___x_1984_, v___x_1985_, v___x_1985_, v___x_1986_, v___x_1987_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_dec_ref(v_imports_1980_);
return v___x_1988_;
}
else
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
lean_dec_ref_known(v___x_1988_, 1);
v___x_1989_ = lean_array_pop(v_imports_1980_);
v___x_1990_ = l_Lean_importModules(v___x_1989_, v___x_1982_, v___x_1983_, v___x_1984_, v___x_1985_, v___x_1985_, v___x_1986_, v___x_1987_);
return v___x_1990_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgLoadEnv___boxed(lean_object* v_imports_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgLoadEnv(v_imports_1991_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval_unsafe__1___redArg(lean_object* v_name_1994_, lean_object* v_env_x27_1995_){
_start:
{
lean_object* v___x_1996_; uint8_t v___x_1997_; lean_object* v___x_1998_; 
v___x_1996_ = l_Lean_Options_empty;
v___x_1997_ = 0;
v___x_1998_ = l_Lean_Environment_evalConst___redArg(v_env_x27_1995_, v___x_1996_, v_name_1994_, v___x_1997_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval_unsafe__1___redArg___boxed(lean_object* v_name_1999_, lean_object* v_env_x27_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval_unsafe__1___redArg(v_name_1999_, v_env_x27_2000_);
lean_dec_ref(v_env_x27_2000_);
lean_dec(v_name_1999_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval_unsafe__1(lean_object* v_00_u03b1_2002_, lean_object* v_name_2003_, lean_object* v_env_x27_2004_){
_start:
{
lean_object* v___x_2005_; uint8_t v___x_2006_; lean_object* v___x_2007_; 
v___x_2005_ = l_Lean_Options_empty;
v___x_2006_ = 0;
v___x_2007_ = l_Lean_Environment_evalConst___redArg(v_env_x27_2004_, v___x_2005_, v_name_2003_, v___x_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval_unsafe__1___boxed(lean_object* v_00_u03b1_2008_, lean_object* v_name_2009_, lean_object* v_env_x27_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval_unsafe__1(v_00_u03b1_2008_, v_name_2009_, v_env_x27_2010_);
lean_dec_ref(v_env_x27_2010_);
lean_dec(v_name_2009_);
return v_res_2011_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__4(void){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = l_Lean_Options_empty;
v___x_2020_ = l_Lean_Core_getMaxHeartbeats(v___x_2019_);
return v___x_2020_;
}
}
static uint16_t _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__5(void){
_start:
{
lean_object* v___x_2021_; uint16_t v___x_2022_; 
v___x_2021_ = l_Lean_Options_empty;
v___x_2022_ = l_Lean_OptionFlags_ofOptions(v___x_2021_);
return v___x_2022_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__6(void){
_start:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2023_ = lean_unsigned_to_nat(1u);
v___x_2024_ = l_Lean_firstFrontendMacroScope;
v___x_2025_ = lean_nat_add(v___x_2024_, v___x_2023_);
return v___x_2025_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__11(void){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2036_ = lean_unsigned_to_nat(32u);
v___x_2037_ = lean_mk_empty_array_with_capacity(v___x_2036_);
v___x_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
return v___x_2038_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12(void){
_start:
{
size_t v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2039_ = ((size_t)5ULL);
v___x_2040_ = lean_unsigned_to_nat(0u);
v___x_2041_ = lean_unsigned_to_nat(32u);
v___x_2042_ = lean_mk_empty_array_with_capacity(v___x_2041_);
v___x_2043_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__11, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__11_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__11);
v___x_2044_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2044_, 0, v___x_2043_);
lean_ctor_set(v___x_2044_, 1, v___x_2042_);
lean_ctor_set(v___x_2044_, 2, v___x_2040_);
lean_ctor_set(v___x_2044_, 3, v___x_2040_);
lean_ctor_set_usize(v___x_2044_, 4, v___x_2039_);
return v___x_2044_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__13(void){
_start:
{
lean_object* v___x_2045_; uint64_t v___x_2046_; lean_object* v___x_2047_; 
v___x_2045_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12);
v___x_2046_ = 0ULL;
v___x_2047_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2047_, 0, v___x_2045_);
lean_ctor_set_uint64(v___x_2047_, sizeof(void*)*1, v___x_2046_);
return v___x_2047_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__14(void){
_start:
{
lean_object* v___x_2048_; 
v___x_2048_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2048_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__15(void){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2049_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__14, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__14_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__14);
v___x_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2049_);
return v___x_2050_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__16(void){
_start:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__15, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__15_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__15);
v___x_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
lean_ctor_set(v___x_2052_, 1, v___x_2051_);
return v___x_2052_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__18(void){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2055_ = l_Lean_Options_empty;
v___x_2056_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__17));
v___x_2057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2056_);
lean_ctor_set(v___x_2057_, 1, v___x_2055_);
return v___x_2057_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__19(void){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2058_ = l_Lean_NameSet_empty;
v___x_2059_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12);
v___x_2060_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2059_);
lean_ctor_set(v___x_2060_, 1, v___x_2059_);
lean_ctor_set(v___x_2060_, 2, v___x_2058_);
return v___x_2060_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__20(void){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; lean_object* v___x_2064_; 
v___x_2061_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12);
v___x_2062_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__15, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__15_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__15);
v___x_2063_ = 1;
v___x_2064_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2064_, 0, v___x_2062_);
lean_ctor_set(v___x_2064_, 1, v___x_2062_);
lean_ctor_set(v___x_2064_, 2, v___x_2061_);
lean_ctor_set_uint8(v___x_2064_, sizeof(void*)*3, v___x_2063_);
return v___x_2064_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__21(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2065_ = l_Lean_maxRecDepth;
v___x_2066_ = l_Lean_Options_empty;
v___x_2067_ = l_Lean_KVMap_instValueNat;
v___x_2068_ = l_Lean_Option_get___redArg(v___x_2067_, v___x_2066_, v___x_2065_);
return v___x_2068_;
}
}
static uint16_t _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__26(void){
_start:
{
uint16_t v___x_2073_; uint16_t v___x_2074_; uint16_t v___x_2075_; 
v___x_2073_ = 512;
v___x_2074_ = lean_uint16_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__5, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__5_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__5);
v___x_2075_ = lean_uint16_land(v___x_2074_, v___x_2073_);
return v___x_2075_;
}
}
static uint8_t _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__27(void){
_start:
{
uint16_t v___x_2076_; uint16_t v___x_2077_; uint8_t v___x_2078_; 
v___x_2076_ = 0;
v___x_2077_ = lean_uint16_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__26, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__26_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__26);
v___x_2078_ = lean_uint16_dec_eq(v___x_2077_, v___x_2076_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg(lean_object* v_env_2079_, lean_object* v_type_2080_, lean_object* v_value_2081_){
_start:
{
lean_object* v_a_2084_; lean_object* v_name_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; uint8_t v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v_decl_2094_; uint8_t v___x_2095_; uint8_t v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; uint16_t v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___y_2122_; lean_object* v___x_2174_; uint8_t v___y_2176_; lean_object* v_env_2197_; uint8_t v___x_2198_; uint8_t v___x_2199_; 
v_name_2087_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__1));
v___x_2088_ = lean_box(0);
v___x_2089_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2089_, 0, v_name_2087_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
lean_ctor_set(v___x_2089_, 2, v_type_2080_);
v___x_2090_ = lean_box(0);
v___x_2091_ = 0;
v___x_2092_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__2));
v___x_2093_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2093_, 0, v___x_2089_);
lean_ctor_set(v___x_2093_, 1, v_value_2081_);
lean_ctor_set(v___x_2093_, 2, v___x_2090_);
lean_ctor_set(v___x_2093_, 3, v___x_2092_);
lean_ctor_set_uint8(v___x_2093_, sizeof(void*)*4, v___x_2091_);
v_decl_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_decl_2094_, 0, v___x_2093_);
v___x_2095_ = 1;
v___x_2096_ = 0;
v___x_2097_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__3));
v___x_2098_ = l_Lean_instInhabitedFileMap_default;
v___x_2099_ = l_Lean_Options_empty;
v___x_2100_ = lean_box(0);
v___x_2101_ = lean_unsigned_to_nat(0u);
v___x_2102_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__4, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__4_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__4);
v___x_2103_ = l_Lean_firstFrontendMacroScope;
v___x_2104_ = lean_box(0);
v___x_2105_ = lean_box(0);
v___x_2106_ = lean_uint16_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__5, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__5_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__5);
v___x_2107_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__6, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__6_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__6);
v___x_2108_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__9));
v___x_2109_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__10));
v___x_2110_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__13, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__13_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__13);
v___x_2111_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__16, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__16_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__16);
v___x_2112_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__17));
v___x_2113_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__18, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__18_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__18);
v___x_2114_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__19, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__19_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__19);
v___x_2115_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__20, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__20_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__20);
v___x_2116_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2116_, 0, v_env_2079_);
lean_ctor_set(v___x_2116_, 1, v___x_2107_);
lean_ctor_set(v___x_2116_, 2, v___x_2108_);
lean_ctor_set(v___x_2116_, 3, v___x_2109_);
lean_ctor_set(v___x_2116_, 4, v___x_2110_);
lean_ctor_set(v___x_2116_, 5, v___x_2111_);
lean_ctor_set(v___x_2116_, 6, v___x_2113_);
lean_ctor_set(v___x_2116_, 7, v___x_2114_);
lean_ctor_set(v___x_2116_, 8, v___x_2115_);
lean_ctor_set(v___x_2116_, 9, v___x_2112_);
v___x_2117_ = lean_io_get_num_heartbeats();
v___x_2118_ = lean_st_mk_ref(v___x_2116_);
v___x_2119_ = l_Lean_inheritedTraceOptions;
v___x_2120_ = lean_st_ref_get(v___x_2119_);
v___x_2174_ = lean_st_ref_get(v___x_2118_);
v_env_2197_ = lean_ctor_get(v___x_2174_, 0);
lean_inc_ref(v_env_2197_);
lean_dec(v___x_2174_);
v___x_2198_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2197_);
lean_dec_ref(v_env_2197_);
v___x_2199_ = lean_uint8_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__27, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__27_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__27);
if (v___x_2199_ == 0)
{
if (v___x_2198_ == 0)
{
v___y_2176_ = v___x_2095_;
goto v___jp_2175_;
}
else
{
lean_inc(v___x_2118_);
v___y_2122_ = v___x_2118_;
goto v___jp_2121_;
}
}
else
{
if (v___x_2198_ == 0)
{
lean_inc(v___x_2118_);
v___y_2122_ = v___x_2118_;
goto v___jp_2121_;
}
else
{
v___y_2176_ = v___x_2096_;
goto v___jp_2175_;
}
}
v___jp_2083_:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = lean_mk_io_user_error(v_a_2084_);
v___x_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
return v___x_2086_;
}
v___jp_2121_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2123_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__21, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__21_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__21);
v___x_2124_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2097_);
lean_ctor_set(v___x_2124_, 1, v___x_2098_);
lean_ctor_set(v___x_2124_, 2, v___x_2099_);
lean_ctor_set(v___x_2124_, 3, v___x_2123_);
lean_ctor_set(v___x_2124_, 4, v___x_2100_);
lean_ctor_set(v___x_2124_, 5, v___x_2088_);
lean_ctor_set(v___x_2124_, 6, v___x_2117_);
lean_ctor_set(v___x_2124_, 7, v___x_2102_);
lean_ctor_set(v___x_2124_, 8, v___x_2100_);
lean_ctor_set(v___x_2124_, 9, v___x_2103_);
lean_ctor_set(v___x_2124_, 10, v___x_2104_);
lean_ctor_set(v___x_2124_, 11, v___x_2120_);
v___x_2125_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
lean_ctor_set(v___x_2125_, 1, v___x_2101_);
lean_ctor_set(v___x_2125_, 2, v___x_2105_);
lean_ctor_set_uint16(v___x_2125_, sizeof(void*)*3, v___x_2106_);
lean_ctor_set_uint8(v___x_2125_, sizeof(void*)*3 + 2, v___x_2096_);
lean_ctor_set_uint8(v___x_2125_, sizeof(void*)*3 + 3, v___x_2096_);
v___x_2126_ = l_Lean_addAndCompile(v_decl_2094_, v___x_2095_, v___x_2096_, v___x_2125_, v___y_2122_);
lean_dec(v___y_2122_);
lean_dec_ref_known(v___x_2125_, 3);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2150_; 
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2150_ == 0)
{
lean_object* v_unused_2151_; 
v_unused_2151_ = lean_ctor_get(v___x_2126_, 0);
lean_dec(v_unused_2151_);
v___x_2128_ = v___x_2126_;
v_isShared_2129_ = v_isSharedCheck_2150_;
goto v_resetjp_2127_;
}
else
{
lean_dec(v___x_2126_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2150_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2130_; lean_object* v_env_2131_; lean_object* v___x_2132_; 
v___x_2130_ = lean_st_ref_get(v___x_2118_);
lean_dec(v___x_2118_);
v_env_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc_ref(v_env_2131_);
lean_dec(v___x_2130_);
v___x_2132_ = l_Lean_Environment_evalConst___redArg(v_env_2131_, v___x_2099_, v_name_2087_, v___x_2096_);
lean_dec_ref(v_env_2131_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2145_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2135_ = v___x_2132_;
v_isShared_2136_ = v_isSharedCheck_2145_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2132_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2145_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2140_; 
v___x_2137_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__22));
v___x_2138_ = lean_string_append(v___x_2137_, v_a_2133_);
lean_dec(v_a_2133_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set_tag(v___x_2135_, 18);
lean_ctor_set(v___x_2135_, 0, v___x_2138_);
v___x_2140_ = v___x_2135_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
lean_object* v___x_2142_; 
if (v_isShared_2129_ == 0)
{
lean_ctor_set_tag(v___x_2128_, 1);
lean_ctor_set(v___x_2128_, 0, v___x_2140_);
v___x_2142_ = v___x_2128_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; 
v_a_2146_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2146_);
lean_dec_ref_known(v___x_2132_, 1);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 0, v_a_2146_);
v___x_2148_ = v___x_2128_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2146_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
else
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2173_; 
lean_dec(v___x_2118_);
v_a_2152_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2154_ = v___x_2126_;
v_isShared_2155_ = v_isSharedCheck_2173_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2126_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2173_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
if (lean_obj_tag(v_a_2152_) == 0)
{
lean_object* v_msg_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2160_; 
v_msg_2156_ = lean_ctor_get(v_a_2152_, 1);
lean_inc_ref(v_msg_2156_);
lean_dec_ref_known(v_a_2152_, 2);
v___x_2157_ = l_Lean_MessageData_toString(v_msg_2156_);
v___x_2158_ = lean_mk_io_user_error(v___x_2157_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 0, v___x_2158_);
v___x_2160_ = v___x_2154_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2158_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
else
{
lean_object* v_id_2162_; lean_object* v___x_2163_; 
lean_del_object(v___x_2154_);
v_id_2162_ = lean_ctor_get(v_a_2152_, 0);
lean_inc(v_id_2162_);
lean_dec_ref_known(v_a_2152_, 2);
v___x_2163_ = l_Lean_InternalExceptionId_getName(v_id_2162_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
lean_dec(v_id_2162_);
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2164_);
lean_dec_ref_known(v___x_2163_, 1);
v___x_2165_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__23));
v___x_2166_ = l_Lean_Name_toString(v_a_2164_, v___x_2095_);
v___x_2167_ = lean_string_append(v___x_2165_, v___x_2166_);
lean_dec_ref(v___x_2166_);
v_a_2084_ = v___x_2167_;
goto v___jp_2083_;
}
else
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
lean_dec_ref_known(v___x_2163_, 1);
v___x_2168_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__24));
v___x_2169_ = l_Nat_reprFast(v_id_2162_);
v___x_2170_ = lean_string_append(v___x_2168_, v___x_2169_);
lean_dec_ref(v___x_2169_);
v___x_2171_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__25));
v___x_2172_ = lean_string_append(v___x_2170_, v___x_2171_);
v_a_2084_ = v___x_2172_;
goto v___jp_2083_;
}
}
}
}
}
v___jp_2175_:
{
lean_object* v___x_2177_; lean_object* v_env_2178_; lean_object* v_nextMacroScope_2179_; lean_object* v_ngen_2180_; lean_object* v_auxDeclNGen_2181_; lean_object* v_traceState_2182_; lean_object* v_recordedDeps_2183_; lean_object* v_messages_2184_; lean_object* v_infoState_2185_; lean_object* v_snapshotTasks_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2195_; 
v___x_2177_ = lean_st_ref_take(v___x_2118_);
v_env_2178_ = lean_ctor_get(v___x_2177_, 0);
v_nextMacroScope_2179_ = lean_ctor_get(v___x_2177_, 1);
v_ngen_2180_ = lean_ctor_get(v___x_2177_, 2);
v_auxDeclNGen_2181_ = lean_ctor_get(v___x_2177_, 3);
v_traceState_2182_ = lean_ctor_get(v___x_2177_, 4);
v_recordedDeps_2183_ = lean_ctor_get(v___x_2177_, 6);
v_messages_2184_ = lean_ctor_get(v___x_2177_, 7);
v_infoState_2185_ = lean_ctor_get(v___x_2177_, 8);
v_snapshotTasks_2186_ = lean_ctor_get(v___x_2177_, 9);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2195_ == 0)
{
lean_object* v_unused_2196_; 
v_unused_2196_ = lean_ctor_get(v___x_2177_, 5);
lean_dec(v_unused_2196_);
v___x_2188_ = v___x_2177_;
v_isShared_2189_ = v_isSharedCheck_2195_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_snapshotTasks_2186_);
lean_inc(v_infoState_2185_);
lean_inc(v_messages_2184_);
lean_inc(v_recordedDeps_2183_);
lean_inc(v_traceState_2182_);
lean_inc(v_auxDeclNGen_2181_);
lean_inc(v_ngen_2180_);
lean_inc(v_nextMacroScope_2179_);
lean_inc(v_env_2178_);
lean_dec(v___x_2177_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2195_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2190_; lean_object* v___x_2192_; 
v___x_2190_ = l_Lean_Kernel_enableDiag(v_env_2178_, v___y_2176_);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 5, v___x_2111_);
lean_ctor_set(v___x_2188_, 0, v___x_2190_);
v___x_2192_ = v___x_2188_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2190_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v_nextMacroScope_2179_);
lean_ctor_set(v_reuseFailAlloc_2194_, 2, v_ngen_2180_);
lean_ctor_set(v_reuseFailAlloc_2194_, 3, v_auxDeclNGen_2181_);
lean_ctor_set(v_reuseFailAlloc_2194_, 4, v_traceState_2182_);
lean_ctor_set(v_reuseFailAlloc_2194_, 5, v___x_2111_);
lean_ctor_set(v_reuseFailAlloc_2194_, 6, v_recordedDeps_2183_);
lean_ctor_set(v_reuseFailAlloc_2194_, 7, v_messages_2184_);
lean_ctor_set(v_reuseFailAlloc_2194_, 8, v_infoState_2185_);
lean_ctor_set(v_reuseFailAlloc_2194_, 9, v_snapshotTasks_2186_);
v___x_2192_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
lean_object* v___x_2193_; 
v___x_2193_ = lean_st_ref_put(v___x_2118_, v___x_2192_);
lean_inc(v___x_2118_);
v___y_2122_ = v___x_2118_;
goto v___jp_2121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___boxed(lean_object* v_env_2200_, lean_object* v_type_2201_, lean_object* v_value_2202_, lean_object* v_a_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg(v_env_2200_, v_type_2201_, v_value_2202_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval(lean_object* v_00_u03b1_2205_, lean_object* v_inst_2206_, lean_object* v_env_2207_, lean_object* v_type_2208_, lean_object* v_value_2209_){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg(v_env_2207_, v_type_2208_, v_value_2209_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___boxed(lean_object* v_00_u03b1_2212_, lean_object* v_inst_2213_, lean_object* v_env_2214_, lean_object* v_type_2215_, lean_object* v_value_2216_, lean_object* v_a_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval(v_00_u03b1_2212_, v_inst_2213_, v_env_2214_, v_type_2215_, v_value_2216_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(lean_object* v_e_2219_){
_start:
{
if (lean_obj_tag(v_e_2219_) == 0)
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2229_; 
v_a_2221_ = lean_ctor_get(v_e_2219_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v_e_2219_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2223_ = v_e_2219_;
v_isShared_2224_ = v_isSharedCheck_2229_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v_e_2219_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2229_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2225_ = lean_mk_io_user_error(v_a_2221_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set_tag(v___x_2223_, 1);
lean_ctor_set(v___x_2223_, 0, v___x_2225_);
v___x_2227_ = v___x_2223_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
v_a_2230_ = lean_ctor_get(v_e_2219_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v_e_2219_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v_e_2219_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v_e_2219_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
lean_ctor_set_tag(v___x_2232_, 0);
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg___boxed(lean_object* v_e_2238_, lean_object* v_a_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v_e_2238_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2(lean_object* v_00_u03b1_2241_, lean_object* v_e_2242_){
_start:
{
lean_object* v___x_2244_; 
v___x_2244_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v_e_2242_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___boxed(lean_object* v_00_u03b1_2245_, lean_object* v_e_2246_, lean_object* v_a_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2(v_00_u03b1_2245_, v_e_2246_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__1(lean_object* v___x_2249_, lean_object* v_x_2250_){
_start:
{
if (lean_obj_tag(v_x_2250_) == 0)
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2251_ = lean_mk_io_user_error(v___x_2249_);
v___x_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
return v___x_2252_;
}
else
{
lean_object* v_val_2253_; 
lean_dec_ref(v___x_2249_);
v_val_2253_ = lean_ctor_get(v_x_2250_, 0);
lean_inc(v_val_2253_);
return v_val_2253_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__1___boxed(lean_object* v___x_2254_, lean_object* v_x_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__1(v___x_2254_, v_x_2255_);
lean_dec(v_x_2255_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__2(lean_object* v___f_2257_, lean_object* v_x_2258_){
_start:
{
if (lean_obj_tag(v_x_2258_) == 0)
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2268_; 
lean_dec_ref(v___f_2257_);
v_a_2260_ = lean_ctor_get(v_x_2258_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v_x_2258_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2262_ = v_x_2258_;
v_isShared_2263_ = v_isSharedCheck_2268_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v_x_2258_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2268_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2265_; 
if (v_isShared_2263_ == 0)
{
v___x_2265_ = v___x_2262_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2260_);
v___x_2265_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
lean_object* v___x_2266_; 
v___x_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
return v___x_2266_;
}
}
}
else
{
lean_object* v_a_2269_; 
v_a_2269_ = lean_ctor_get(v_x_2258_, 0);
lean_inc(v_a_2269_);
lean_dec_ref_known(v_x_2258_, 1);
if (lean_obj_tag(v_a_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2278_; 
lean_dec_ref(v___f_2257_);
v_a_2270_ = lean_ctor_get(v_a_2269_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v_a_2269_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2272_ = v_a_2269_;
v_isShared_2273_ = v_isSharedCheck_2278_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v_a_2269_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2278_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2270_);
v___x_2275_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
lean_object* v___x_2276_; 
v___x_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2275_);
return v___x_2276_;
}
}
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; uint8_t v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v_a_2279_ = lean_ctor_get(v_a_2269_, 0);
lean_inc(v_a_2279_);
lean_dec_ref_known(v_a_2269_, 1);
v___x_2280_ = lean_io_promise_result_opt(v_a_2279_);
lean_dec(v_a_2279_);
v___x_2281_ = lean_unsigned_to_nat(0u);
v___x_2282_ = 0;
v___x_2283_ = lean_task_map(v___f_2257_, v___x_2280_, v___x_2281_, v___x_2282_);
v___x_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
return v___x_2284_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__2___boxed(lean_object* v___f_2285_, lean_object* v_x_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__2(v___f_2285_, v_x_2286_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0___redArg(lean_object* v___x_2289_, lean_object* v___x_2290_, lean_object* v___x_2291_, lean_object* v_a_2292_, lean_object* v_b_2293_){
_start:
{
lean_object* v___x_2294_; 
v___x_2294_ = lean_box(0);
switch(lean_obj_tag(v_a_2292_))
{
case 0:
{
lean_object* v_pos_2295_; lean_object* v___x_2296_; 
v_pos_2295_ = lean_ctor_get(v_a_2292_, 0);
lean_inc(v_pos_2295_);
lean_dec_ref_known(v_a_2292_, 1);
v___x_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2296_, 0, v_pos_2295_);
return v___x_2296_;
}
case 1:
{
lean_object* v_pos_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2306_; 
v_pos_2297_ = lean_ctor_get(v_a_2292_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v_a_2292_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2299_ = v_a_2292_;
v_isShared_2300_ = v_isSharedCheck_2306_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_pos_2297_);
lean_dec(v_a_2292_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2306_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2301_; lean_object* v___x_2303_; 
v___x_2301_ = lean_string_utf8_next_fast(v___x_2289_, v_pos_2297_);
lean_dec(v_pos_2297_);
if (v_isShared_2300_ == 0)
{
lean_ctor_set_tag(v___x_2299_, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2301_);
v___x_2303_ = v___x_2299_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2301_);
v___x_2303_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
v_a_2292_ = v___x_2303_;
v_b_2293_ = v___x_2294_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_2307_; lean_object* v_table_2308_; lean_object* v_stackPos_2309_; lean_object* v_needlePos_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2363_; 
v_needle_2307_ = lean_ctor_get(v_a_2292_, 0);
v_table_2308_ = lean_ctor_get(v_a_2292_, 1);
v_stackPos_2309_ = lean_ctor_get(v_a_2292_, 2);
v_needlePos_2310_ = lean_ctor_get(v_a_2292_, 3);
v_isSharedCheck_2363_ = !lean_is_exclusive(v_a_2292_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2312_ = v_a_2292_;
v_isShared_2313_ = v_isSharedCheck_2363_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_needlePos_2310_);
lean_inc(v_stackPos_2309_);
lean_inc(v_table_2308_);
lean_inc(v_needle_2307_);
lean_dec(v_a_2292_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2363_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v_str_2314_; lean_object* v_startInclusive_2315_; lean_object* v_endExclusive_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; uint8_t v___x_2320_; 
v_str_2314_ = lean_ctor_get(v_needle_2307_, 0);
v_startInclusive_2315_ = lean_ctor_get(v_needle_2307_, 1);
v_endExclusive_2316_ = lean_ctor_get(v_needle_2307_, 2);
v___x_2317_ = lean_nat_sub(v_stackPos_2309_, v_needlePos_2310_);
v___x_2318_ = lean_nat_sub(v_endExclusive_2316_, v_startInclusive_2315_);
v___x_2319_ = lean_nat_add(v___x_2317_, v___x_2318_);
v___x_2320_ = lean_nat_dec_le(v___x_2319_, v___x_2291_);
lean_dec(v___x_2319_);
if (v___x_2320_ == 0)
{
lean_object* v___x_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; 
lean_dec(v___x_2318_);
lean_del_object(v___x_2312_);
lean_dec(v_needlePos_2310_);
lean_dec(v_stackPos_2309_);
lean_dec_ref(v_table_2308_);
lean_dec_ref(v_needle_2307_);
v___x_2321_ = lean_unsigned_to_nat(1u);
v___x_2322_ = lean_nat_add(v___x_2317_, v___x_2321_);
lean_dec(v___x_2317_);
v___x_2323_ = lean_nat_dec_le(v___x_2322_, v___x_2291_);
lean_dec(v___x_2322_);
if (v___x_2323_ == 0)
{
lean_inc(v_b_2293_);
return v_b_2293_;
}
else
{
lean_object* v___x_2324_; 
v___x_2324_ = lean_box(3);
v_a_2292_ = v___x_2324_;
v_b_2293_ = v___x_2294_;
goto _start;
}
}
else
{
uint8_t v_stackByte_2326_; lean_object* v___x_2327_; uint8_t v_patByte_2328_; uint8_t v___x_2329_; 
lean_dec(v___x_2317_);
lean_inc(v_stackPos_2309_);
v_stackByte_2326_ = lean_string_get_byte_fast(v___x_2289_, v_stackPos_2309_);
v___x_2327_ = lean_nat_add(v_startInclusive_2315_, v_needlePos_2310_);
v_patByte_2328_ = lean_string_get_byte_fast(v_str_2314_, v___x_2327_);
v___x_2329_ = lean_uint8_dec_eq(v_stackByte_2326_, v_patByte_2328_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; uint8_t v_decide_2331_; 
lean_dec(v___x_2318_);
v___x_2330_ = lean_unsigned_to_nat(0u);
v_decide_2331_ = lean_nat_dec_eq(v_needlePos_2310_, v___x_2330_);
if (v_decide_2331_ == 0)
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v_newNeedlePos_2334_; uint8_t v___x_2335_; 
v___x_2332_ = lean_unsigned_to_nat(1u);
v___x_2333_ = lean_nat_sub(v_needlePos_2310_, v___x_2332_);
lean_dec(v_needlePos_2310_);
v_newNeedlePos_2334_ = lean_array_fget_borrowed(v_table_2308_, v___x_2333_);
lean_dec(v___x_2333_);
v___x_2335_ = lean_nat_dec_eq(v_newNeedlePos_2334_, v___x_2330_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2337_; 
lean_inc(v_newNeedlePos_2334_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 3, v_newNeedlePos_2334_);
v___x_2337_ = v___x_2312_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_needle_2307_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v_table_2308_);
lean_ctor_set(v_reuseFailAlloc_2339_, 2, v_stackPos_2309_);
lean_ctor_set(v_reuseFailAlloc_2339_, 3, v_newNeedlePos_2334_);
v___x_2337_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
v_a_2292_ = v___x_2337_;
v_b_2293_ = v___x_2294_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_2340_; lean_object* v___x_2342_; 
v_nextStackPos_2340_ = l_String_Slice_posGE___redArg(v___x_2290_, v_stackPos_2309_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 3, v___x_2330_);
lean_ctor_set(v___x_2312_, 2, v_nextStackPos_2340_);
v___x_2342_ = v___x_2312_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_needle_2307_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v_table_2308_);
lean_ctor_set(v_reuseFailAlloc_2344_, 2, v_nextStackPos_2340_);
lean_ctor_set(v_reuseFailAlloc_2344_, 3, v___x_2330_);
v___x_2342_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
v_a_2292_ = v___x_2342_;
v_b_2293_ = v___x_2294_;
goto _start;
}
}
}
else
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v_nextStackPos_2347_; lean_object* v___x_2349_; 
lean_dec(v_needlePos_2310_);
v___x_2345_ = lean_unsigned_to_nat(1u);
v___x_2346_ = lean_nat_add(v_stackPos_2309_, v___x_2345_);
lean_dec(v_stackPos_2309_);
v_nextStackPos_2347_ = l_String_Slice_posGE___redArg(v___x_2290_, v___x_2346_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 3, v___x_2330_);
lean_ctor_set(v___x_2312_, 2, v_nextStackPos_2347_);
v___x_2349_ = v___x_2312_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_needle_2307_);
lean_ctor_set(v_reuseFailAlloc_2351_, 1, v_table_2308_);
lean_ctor_set(v_reuseFailAlloc_2351_, 2, v_nextStackPos_2347_);
lean_ctor_set(v_reuseFailAlloc_2351_, 3, v___x_2330_);
v___x_2349_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
v_a_2292_ = v___x_2349_;
v_b_2293_ = v___x_2294_;
goto _start;
}
}
}
else
{
lean_object* v___x_2352_; lean_object* v_nextStackPos_2353_; lean_object* v_nextNeedlePos_2354_; uint8_t v_decide_2355_; 
v___x_2352_ = lean_unsigned_to_nat(1u);
v_nextStackPos_2353_ = lean_nat_add(v_stackPos_2309_, v___x_2352_);
lean_dec(v_stackPos_2309_);
v_nextNeedlePos_2354_ = lean_nat_add(v_needlePos_2310_, v___x_2352_);
lean_dec(v_needlePos_2310_);
v_decide_2355_ = lean_nat_dec_eq(v_nextNeedlePos_2354_, v___x_2318_);
lean_dec(v___x_2318_);
if (v_decide_2355_ == 0)
{
lean_object* v___x_2357_; 
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 3, v_nextNeedlePos_2354_);
lean_ctor_set(v___x_2312_, 2, v_nextStackPos_2353_);
v___x_2357_ = v___x_2312_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_needle_2307_);
lean_ctor_set(v_reuseFailAlloc_2359_, 1, v_table_2308_);
lean_ctor_set(v_reuseFailAlloc_2359_, 2, v_nextStackPos_2353_);
lean_ctor_set(v_reuseFailAlloc_2359_, 3, v_nextNeedlePos_2354_);
v___x_2357_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
v_a_2292_ = v___x_2357_;
goto _start;
}
}
else
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
lean_del_object(v___x_2312_);
lean_dec_ref(v_table_2308_);
lean_dec_ref(v_needle_2307_);
v___x_2360_ = lean_nat_sub(v_nextStackPos_2353_, v_nextNeedlePos_2354_);
lean_dec(v_nextNeedlePos_2354_);
lean_dec(v_nextStackPos_2353_);
v___x_2361_ = l_String_Slice_pos_x21(v___x_2290_, v___x_2360_);
lean_dec(v___x_2360_);
v___x_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2361_);
return v___x_2362_;
}
}
}
}
}
default: 
{
lean_inc(v_b_2293_);
return v_b_2293_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0___redArg___boxed(lean_object* v___x_2364_, lean_object* v___x_2365_, lean_object* v___x_2366_, lean_object* v_a_2367_, lean_object* v_b_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0___redArg(v___x_2364_, v___x_2365_, v___x_2366_, v_a_2367_, v_b_2368_);
lean_dec(v_b_2368_);
lean_dec(v___x_2366_);
lean_dec_ref(v___x_2365_);
lean_dec_ref(v___x_2364_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__0(lean_object* v_____r_2370_){
_start:
{
uint32_t v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2372_ = 500;
v___x_2373_ = l_IO_sleep(v___x_2372_);
v___x_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__0___boxed(lean_object* v_____r_2375_, lean_object* v___y_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__0(v_____r_2375_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1_spec__1(lean_object* v_s_2378_){
_start:
{
lean_object* v___x_2380_; lean_object* v_putStr_2381_; lean_object* v___x_2382_; 
v___x_2380_ = lean_get_stderr();
v_putStr_2381_ = lean_ctor_get(v___x_2380_, 4);
lean_inc_ref(v_putStr_2381_);
lean_dec_ref(v___x_2380_);
v___x_2382_ = lean_apply_2(v_putStr_2381_, v_s_2378_, lean_box(0));
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1_spec__1___boxed(lean_object* v_s_2383_, lean_object* v_a_2384_){
_start:
{
lean_object* v_res_2385_; 
v_res_2385_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1_spec__1(v_s_2383_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1(lean_object* v_s_2386_){
_start:
{
uint32_t v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2388_ = 10;
v___x_2389_ = lean_string_push(v_s_2386_, v___x_2388_);
v___x_2390_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1_spec__1(v___x_2389_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1___boxed(lean_object* v_s_2391_, lean_object* v_a_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l_IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1(v_s_2391_);
return v_res_2393_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2399_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__1));
v___x_2400_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_2399_);
return v___x_2400_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2401_ = lean_unsigned_to_nat(0u);
v___x_2402_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__2);
v___x_2403_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__1));
v___x_2404_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2403_);
lean_ctor_set(v___x_2404_, 1, v___x_2402_);
lean_ctor_set(v___x_2404_, 2, v___x_2401_);
lean_ctor_set(v___x_2404_, 3, v___x_2401_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg(lean_object* v_a_2410_, lean_object* v_apply_2411_, lean_object* v___x_2412_){
_start:
{
lean_object* v___y_2415_; lean_object* v___x_2417_; lean_object* v_a_2419_; lean_object* v___y_2434_; lean_object* v_a_2438_; uint8_t v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v_val_2444_; lean_object* v___x_2451_; 
v___x_2417_ = lean_box(0);
v___x_2451_ = lean_uv_tcp_new();
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2540_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2454_ = v___x_2451_;
v_isShared_2455_ = v_isSharedCheck_2540_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2451_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2540_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v_a_2457_; lean_object* v___x_2510_; 
lean_inc_ref(v___x_2412_);
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 0, v___x_2412_);
v___x_2510_ = v___x_2454_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2412_);
v___x_2510_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2509_;
}
v___jp_2456_:
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Std_Async_AsyncTask_block___redArg(v_a_2457_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v___x_2459_; 
lean_dec_ref_known(v___x_2458_, 1);
v___x_2459_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg(v_a_2452_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_a_2460_);
lean_dec_ref_known(v___x_2459_, 1);
v___x_2461_ = l_Lean_Json_parse(v_a_2460_);
v___x_2462_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_2461_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc_n(v_a_2463_, 2);
lean_dec_ref_known(v___x_2462_, 1);
v___x_2464_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__8));
v___x_2465_ = l_Lean_Json_getObjVal_x3f(v_a_2463_, v___x_2464_);
v___x_2466_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_2465_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2467_);
lean_dec_ref_known(v___x_2466_, 1);
v___x_2468_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f(v_a_2467_);
v___x_2469_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_2468_);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v_a_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v_a_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_a_2470_);
lean_dec_ref_known(v___x_2469_, 1);
v___x_2471_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__13));
v___x_2472_ = l_Lean_Json_getObjVal_x3f(v_a_2463_, v___x_2471_);
v___x_2473_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_2472_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_a_2474_);
lean_dec_ref_known(v___x_2473_, 1);
v___x_2475_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f(v_a_2474_);
v___x_2476_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_2475_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; lean_object* v___x_2478_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_a_2477_);
lean_dec_ref_known(v___x_2476_, 1);
lean_inc_ref(v_a_2410_);
v___x_2478_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg(v_a_2410_, v_a_2470_, v_a_2477_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_a_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
lean_inc(v_a_2479_);
lean_dec_ref_known(v___x_2478_, 1);
lean_inc_ref(v_apply_2411_);
v___x_2480_ = lean_apply_1(v_apply_2411_, v_a_2479_);
v___x_2481_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg(v_a_2452_, v___x_2480_);
lean_dec_ref(v___x_2480_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v___f_2482_; lean_object* v___x_2483_; uint8_t v___x_2484_; lean_object* v___x_2485_; 
lean_dec_ref_known(v___x_2481_, 1);
v___f_2482_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__6));
v___x_2483_ = lean_unsigned_to_nat(0u);
v___x_2484_ = 0;
v___x_2485_ = lean_uv_tcp_shutdown(v_a_2452_);
lean_dec(v_a_2452_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2485_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2485_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
lean_ctor_set_tag(v___x_2488_, 1);
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
v___y_2441_ = v___x_2484_;
v___y_2442_ = v___x_2483_;
v___y_2443_ = v___f_2482_;
v_val_2444_ = v___x_2491_;
goto v___jp_2440_;
}
}
}
else
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
v_a_2494_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___x_2485_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2485_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
lean_ctor_set_tag(v___x_2496_, 0);
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
v___y_2441_ = v___x_2484_;
v___y_2442_ = v___x_2483_;
v___y_2443_ = v___f_2482_;
v_val_2444_ = v___x_2499_;
goto v___jp_2440_;
}
}
}
}
else
{
lean_dec(v_a_2452_);
v___y_2434_ = v___x_2481_;
goto v___jp_2433_;
}
}
else
{
lean_object* v_a_2502_; 
lean_dec(v_a_2452_);
v_a_2502_ = lean_ctor_get(v___x_2478_, 0);
lean_inc(v_a_2502_);
lean_dec_ref_known(v___x_2478_, 1);
v_a_2419_ = v_a_2502_;
goto v___jp_2418_;
}
}
else
{
lean_object* v_a_2503_; 
lean_dec(v_a_2470_);
lean_dec(v_a_2452_);
v_a_2503_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_a_2503_);
lean_dec_ref_known(v___x_2476_, 1);
v_a_2419_ = v_a_2503_;
goto v___jp_2418_;
}
}
else
{
lean_object* v_a_2504_; 
lean_dec(v_a_2470_);
lean_dec(v_a_2452_);
v_a_2504_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_a_2504_);
lean_dec_ref_known(v___x_2473_, 1);
v_a_2419_ = v_a_2504_;
goto v___jp_2418_;
}
}
else
{
lean_object* v_a_2505_; 
lean_dec(v_a_2463_);
lean_dec(v_a_2452_);
v_a_2505_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_a_2505_);
lean_dec_ref_known(v___x_2469_, 1);
v_a_2419_ = v_a_2505_;
goto v___jp_2418_;
}
}
else
{
lean_object* v_a_2506_; 
lean_dec(v_a_2463_);
lean_dec(v_a_2452_);
v_a_2506_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2506_);
lean_dec_ref_known(v___x_2466_, 1);
v_a_2419_ = v_a_2506_;
goto v___jp_2418_;
}
}
else
{
lean_object* v_a_2507_; 
lean_dec(v_a_2452_);
v_a_2507_ = lean_ctor_get(v___x_2462_, 0);
lean_inc(v_a_2507_);
lean_dec_ref_known(v___x_2462_, 1);
v_a_2419_ = v_a_2507_;
goto v___jp_2418_;
}
}
else
{
lean_object* v_a_2508_; 
lean_dec(v_a_2452_);
v_a_2508_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_a_2508_);
lean_dec_ref_known(v___x_2459_, 1);
v_a_2419_ = v_a_2508_;
goto v___jp_2418_;
}
}
else
{
lean_dec(v_a_2452_);
v___y_2434_ = v___x_2458_;
goto v___jp_2433_;
}
}
v_reusejp_2509_:
{
lean_object* v___f_2511_; lean_object* v___x_2512_; uint8_t v___x_2513_; lean_object* v_val_2515_; lean_object* v___x_2522_; 
v___f_2511_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__6));
v___x_2512_ = lean_unsigned_to_nat(0u);
v___x_2513_ = 0;
v___x_2522_ = lean_uv_tcp_connect(v_a_2452_, v___x_2510_);
lean_dec_ref(v___x_2510_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2522_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2522_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
lean_ctor_set_tag(v___x_2525_, 1);
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2523_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
v_val_2515_ = v___x_2528_;
goto v___jp_2514_;
}
}
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
v_a_2531_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2522_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2522_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
lean_ctor_set_tag(v___x_2533_, 0);
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
v_val_2515_ = v___x_2536_;
goto v___jp_2514_;
}
}
}
v___jp_2514_:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2516_, 0, v_val_2515_);
v___x_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2516_);
v___x_2518_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2512_, v___x_2513_, v___x_2517_, v___f_2511_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v_a_2519_; lean_object* v___x_2520_; 
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_a_2519_);
lean_dec_ref_known(v___x_2518_, 1);
v___x_2520_ = lean_task_pure(v_a_2519_);
v_a_2457_ = v___x_2520_;
goto v___jp_2456_;
}
else
{
lean_object* v_a_2521_; 
v_a_2521_ = lean_ctor_get(v___x_2518_, 0);
lean_inc_ref(v_a_2521_);
lean_dec_ref_known(v___x_2518_, 1);
v_a_2457_ = v_a_2521_;
goto v___jp_2456_;
}
}
}
}
}
else
{
lean_object* v_a_2541_; 
v_a_2541_ = lean_ctor_get(v___x_2451_, 0);
lean_inc(v_a_2541_);
lean_dec_ref_known(v___x_2451_, 1);
v_a_2419_ = v_a_2541_;
goto v___jp_2418_;
}
v___jp_2414_:
{
if (lean_obj_tag(v___y_2415_) == 0)
{
lean_dec_ref_known(v___y_2415_, 1);
goto _start;
}
else
{
lean_dec_ref(v___x_2412_);
lean_dec_ref(v_apply_2411_);
lean_dec_ref(v_a_2410_);
return v___y_2415_;
}
}
v___jp_2418_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2420_ = lean_io_error_to_string(v_a_2419_);
v___x_2421_ = lean_unsigned_to_nat(0u);
v___x_2422_ = lean_string_utf8_byte_size(v___x_2420_);
lean_inc_ref(v___x_2420_);
v___x_2423_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2420_);
lean_ctor_set(v___x_2423_, 1, v___x_2421_);
lean_ctor_set(v___x_2423_, 2, v___x_2422_);
v___x_2424_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__3);
v___x_2425_ = lean_box(0);
v___x_2426_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0___redArg(v___x_2420_, v___x_2423_, v___x_2422_, v___x_2424_, v___x_2425_);
lean_dec_ref_known(v___x_2423_, 3);
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2427_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__4));
v___x_2428_ = lean_string_append(v___x_2427_, v___x_2420_);
lean_dec_ref(v___x_2420_);
v___x_2429_ = l_IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1(v___x_2428_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; lean_object* v___x_2431_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc(v_a_2430_);
lean_dec_ref_known(v___x_2429_, 1);
v___x_2431_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__0(v_a_2430_);
v___y_2415_ = v___x_2431_;
goto v___jp_2414_;
}
else
{
v___y_2415_ = v___x_2429_;
goto v___jp_2414_;
}
}
else
{
lean_object* v___x_2432_; 
lean_dec_ref_known(v___x_2426_, 1);
lean_dec_ref(v___x_2420_);
v___x_2432_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__0(v___x_2417_);
v___y_2415_ = v___x_2432_;
goto v___jp_2414_;
}
}
v___jp_2433_:
{
if (lean_obj_tag(v___y_2434_) == 0)
{
lean_dec_ref_known(v___y_2434_, 1);
goto _start;
}
else
{
lean_object* v_a_2436_; 
v_a_2436_ = lean_ctor_get(v___y_2434_, 0);
lean_inc(v_a_2436_);
lean_dec_ref_known(v___y_2434_, 1);
v_a_2419_ = v_a_2436_;
goto v___jp_2418_;
}
}
v___jp_2437_:
{
lean_object* v___x_2439_; 
v___x_2439_ = l_Std_Async_AsyncTask_block___redArg(v_a_2438_);
v___y_2434_ = v___x_2439_;
goto v___jp_2433_;
}
v___jp_2440_:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2445_, 0, v_val_2444_);
v___x_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2445_);
lean_inc_ref(v___y_2443_);
v___x_2447_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___y_2442_, v___y_2441_, v___x_2446_, v___y_2443_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_a_2448_; lean_object* v___x_2449_; 
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
lean_inc(v_a_2448_);
lean_dec_ref_known(v___x_2447_, 1);
v___x_2449_ = lean_task_pure(v_a_2448_);
v_a_2438_ = v___x_2449_;
goto v___jp_2437_;
}
else
{
lean_object* v_a_2450_; 
v_a_2450_ = lean_ctor_get(v___x_2447_, 0);
lean_inc_ref(v_a_2450_);
lean_dec_ref_known(v___x_2447_, 1);
v_a_2438_ = v_a_2450_;
goto v___jp_2437_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___boxed(lean_object* v_a_2542_, lean_object* v_apply_2543_, lean_object* v___x_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg(v_a_2542_, v_apply_2543_, v___x_2544_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* lean_idbg_client_loop(lean_object* v_siteId_2547_, lean_object* v_imports_2548_, lean_object* v_apply_2549_){
_start:
{
lean_object* v___x_2551_; 
v___x_2551_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgLoadEnv(v_imports_2548_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; uint16_t v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
lean_inc(v_a_2552_);
lean_dec_ref_known(v___x_2551_, 1);
v___x_2553_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgPort(v_siteId_2547_);
lean_dec_ref(v_siteId_2547_);
v___x_2554_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__1, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__1_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__1);
v___x_2555_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
lean_ctor_set_uint16(v___x_2555_, sizeof(void*)*1, v___x_2553_);
v___x_2556_ = lean_box(0);
v___x_2557_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg(v_a_2552_, v_apply_2549_, v___x_2555_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2564_ == 0)
{
lean_object* v_unused_2565_; 
v_unused_2565_ = lean_ctor_get(v___x_2557_, 0);
lean_dec(v_unused_2565_);
v___x_2559_ = v___x_2557_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_dec(v___x_2557_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v___x_2556_);
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2556_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
else
{
return v___x_2557_;
}
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
lean_dec_ref(v_apply_2549_);
lean_dec_ref(v_siteId_2547_);
v_a_2566_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2551_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2551_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_a_2566_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl___boxed(lean_object* v_siteId_2574_, lean_object* v_imports_2575_, lean_object* v_apply_2576_, lean_object* v_a_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = lean_idbg_client_loop(v_siteId_2574_, v_imports_2575_, v_apply_2576_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0(lean_object* v___x_2579_, lean_object* v___x_2580_, lean_object* v___x_2581_, lean_object* v_inst_2582_, lean_object* v_R_2583_, lean_object* v_a_2584_, lean_object* v_b_2585_, lean_object* v_c_2586_){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0___redArg(v___x_2579_, v___x_2580_, v___x_2581_, v_a_2584_, v_b_2585_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0___boxed(lean_object* v___x_2588_, lean_object* v___x_2589_, lean_object* v___x_2590_, lean_object* v_inst_2591_, lean_object* v_R_2592_, lean_object* v_a_2593_, lean_object* v_b_2594_, lean_object* v_c_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0(v___x_2588_, v___x_2589_, v___x_2590_, v_inst_2591_, v_R_2592_, v_a_2593_, v_b_2594_, v_c_2595_);
lean_dec(v_b_2594_);
lean_dec(v___x_2590_);
lean_dec_ref(v___x_2589_);
lean_dec_ref(v___x_2588_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3(lean_object* v_a_2597_, lean_object* v_apply_2598_, lean_object* v___x_2599_, lean_object* v_inst_2600_, lean_object* v_a_2601_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg(v_a_2597_, v_apply_2598_, v___x_2599_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___boxed(lean_object* v_a_2604_, lean_object* v_apply_2605_, lean_object* v___x_2606_, lean_object* v_inst_2607_, lean_object* v_a_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3(v_a_2604_, v_apply_2605_, v___x_2606_, v_inst_2607_, v_a_2608_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___redArg(){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = l_Lean_Elab_Do_instInhabitedControlInfo_default;
v___x_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2612_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___redArg___boxed(lean_object* v_a_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___redArg();
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg(lean_object* v_x_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_){
_start:
{
lean_object* v___x_2624_; 
v___x_2624_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___redArg();
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___boxed(lean_object* v_x_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg(v_x_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_);
lean_dec(v_a_2631_);
lean_dec_ref(v_a_2630_);
lean_dec(v_a_2629_);
lean_dec_ref(v_a_2628_);
lean_dec(v_a_2627_);
lean_dec_ref(v_a_2626_);
lean_dec(v_x_2625_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1(){
_start:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2676_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2677_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4));
v___x_2678_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__18));
v___x_2679_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___boxed), 8, 0);
v___x_2680_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2676_, v___x_2677_, v___x_2678_, v___x_2679_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___boxed(lean_object* v_a_2681_){
_start:
{
lean_object* v_res_2682_; 
v_res_2682_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1();
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(lean_object* v_e_2683_, lean_object* v___y_2684_){
_start:
{
uint8_t v___x_2686_; 
v___x_2686_ = l_Lean_Expr_hasMVar(v_e_2683_);
if (v___x_2686_ == 0)
{
lean_object* v___x_2687_; 
v___x_2687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2687_, 0, v_e_2683_);
return v___x_2687_;
}
else
{
lean_object* v___x_2688_; lean_object* v_mctx_2689_; lean_object* v___x_2690_; lean_object* v_fst_2691_; lean_object* v_snd_2692_; lean_object* v___x_2693_; lean_object* v_cache_2694_; lean_object* v_zetaDeltaFVarIds_2695_; lean_object* v_postponed_2696_; lean_object* v_diag_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2706_; 
v___x_2688_ = lean_st_ref_get(v___y_2684_);
v_mctx_2689_ = lean_ctor_get(v___x_2688_, 0);
lean_inc_ref(v_mctx_2689_);
lean_dec(v___x_2688_);
v___x_2690_ = l_Lean_instantiateMVarsCore(v_mctx_2689_, v_e_2683_);
v_fst_2691_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_fst_2691_);
v_snd_2692_ = lean_ctor_get(v___x_2690_, 1);
lean_inc(v_snd_2692_);
lean_dec_ref(v___x_2690_);
v___x_2693_ = lean_st_ref_take(v___y_2684_);
v_cache_2694_ = lean_ctor_get(v___x_2693_, 1);
v_zetaDeltaFVarIds_2695_ = lean_ctor_get(v___x_2693_, 2);
v_postponed_2696_ = lean_ctor_get(v___x_2693_, 3);
v_diag_2697_ = lean_ctor_get(v___x_2693_, 4);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2706_ == 0)
{
lean_object* v_unused_2707_; 
v_unused_2707_ = lean_ctor_get(v___x_2693_, 0);
lean_dec(v_unused_2707_);
v___x_2699_ = v___x_2693_;
v_isShared_2700_ = v_isSharedCheck_2706_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_diag_2697_);
lean_inc(v_postponed_2696_);
lean_inc(v_zetaDeltaFVarIds_2695_);
lean_inc(v_cache_2694_);
lean_dec(v___x_2693_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2706_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2702_; 
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 0, v_snd_2692_);
v___x_2702_ = v___x_2699_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_snd_2692_);
lean_ctor_set(v_reuseFailAlloc_2705_, 1, v_cache_2694_);
lean_ctor_set(v_reuseFailAlloc_2705_, 2, v_zetaDeltaFVarIds_2695_);
lean_ctor_set(v_reuseFailAlloc_2705_, 3, v_postponed_2696_);
lean_ctor_set(v_reuseFailAlloc_2705_, 4, v_diag_2697_);
v___x_2702_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2703_ = lean_st_ref_put(v___y_2684_, v___x_2702_);
v___x_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2704_, 0, v_fst_2691_);
return v___x_2704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg___boxed(lean_object* v_e_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(v_e_2708_, v___y_2709_);
lean_dec(v___y_2709_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3(lean_object* v_e_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(v_e_2712_, v___y_2716_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___boxed(lean_object* v_e_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3(v_e_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___redArg(lean_object* v_lctx_2730_, lean_object* v_x_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v_keyedConfig_2739_; uint8_t v_trackZetaDelta_2740_; lean_object* v_zetaDeltaSet_2741_; lean_object* v_localInstances_2742_; lean_object* v_defEqCtx_x3f_2743_; lean_object* v_synthPendingDepth_2744_; lean_object* v_customCanUnfoldPredicate_x3f_2745_; uint8_t v_univApprox_2746_; uint8_t v_inTypeClassResolution_2747_; uint8_t v_cacheInferType_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v_keyedConfig_2739_ = lean_ctor_get(v___y_2734_, 0);
v_trackZetaDelta_2740_ = lean_ctor_get_uint8(v___y_2734_, sizeof(void*)*7);
v_zetaDeltaSet_2741_ = lean_ctor_get(v___y_2734_, 1);
v_localInstances_2742_ = lean_ctor_get(v___y_2734_, 3);
v_defEqCtx_x3f_2743_ = lean_ctor_get(v___y_2734_, 4);
v_synthPendingDepth_2744_ = lean_ctor_get(v___y_2734_, 5);
v_customCanUnfoldPredicate_x3f_2745_ = lean_ctor_get(v___y_2734_, 6);
v_univApprox_2746_ = lean_ctor_get_uint8(v___y_2734_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2747_ = lean_ctor_get_uint8(v___y_2734_, sizeof(void*)*7 + 2);
v_cacheInferType_2748_ = lean_ctor_get_uint8(v___y_2734_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_2745_);
lean_inc(v_synthPendingDepth_2744_);
lean_inc(v_defEqCtx_x3f_2743_);
lean_inc_ref(v_localInstances_2742_);
lean_inc(v_zetaDeltaSet_2741_);
lean_inc_ref(v_keyedConfig_2739_);
v___x_2749_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2749_, 0, v_keyedConfig_2739_);
lean_ctor_set(v___x_2749_, 1, v_zetaDeltaSet_2741_);
lean_ctor_set(v___x_2749_, 2, v_lctx_2730_);
lean_ctor_set(v___x_2749_, 3, v_localInstances_2742_);
lean_ctor_set(v___x_2749_, 4, v_defEqCtx_x3f_2743_);
lean_ctor_set(v___x_2749_, 5, v_synthPendingDepth_2744_);
lean_ctor_set(v___x_2749_, 6, v_customCanUnfoldPredicate_x3f_2745_);
lean_ctor_set_uint8(v___x_2749_, sizeof(void*)*7, v_trackZetaDelta_2740_);
lean_ctor_set_uint8(v___x_2749_, sizeof(void*)*7 + 1, v_univApprox_2746_);
lean_ctor_set_uint8(v___x_2749_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2747_);
lean_ctor_set_uint8(v___x_2749_, sizeof(void*)*7 + 3, v_cacheInferType_2748_);
lean_inc(v___y_2737_);
lean_inc_ref(v___y_2736_);
lean_inc(v___y_2735_);
lean_inc(v___y_2733_);
lean_inc_ref(v___y_2732_);
v___x_2750_ = lean_apply_7(v_x_2731_, v___y_2732_, v___y_2733_, v___x_2749_, v___y_2735_, v___y_2736_, v___y_2737_, lean_box(0));
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2750_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2750_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
else
{
return v___x_2750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___redArg___boxed(lean_object* v_lctx_2759_, lean_object* v_x_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___redArg(v_lctx_2759_, v_x_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4(lean_object* v_00_u03b1_2769_, lean_object* v_lctx_2770_, lean_object* v_x_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v___x_2779_; 
v___x_2779_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___redArg(v_lctx_2770_, v_x_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___boxed(lean_object* v_00_u03b1_2780_, lean_object* v_lctx_2781_, lean_object* v_x_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4(v_00_u03b1_2780_, v_lctx_2781_, v_x_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg___lam__0(lean_object* v_k_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v_b_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v___x_2800_; 
lean_inc(v___y_2798_);
lean_inc_ref(v___y_2797_);
lean_inc(v___y_2796_);
lean_inc_ref(v___y_2795_);
lean_inc(v___y_2793_);
lean_inc_ref(v___y_2792_);
v___x_2800_ = lean_apply_8(v_k_2791_, v_b_2794_, v___y_2792_, v___y_2793_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, lean_box(0));
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg___lam__0___boxed(lean_object* v_k_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v_b_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg___lam__0(v_k_2801_, v___y_2802_, v___y_2803_, v_b_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg(lean_object* v_name_2811_, uint8_t v_bi_2812_, lean_object* v_type_2813_, lean_object* v_k_2814_, uint8_t v_kind_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v___f_2823_; lean_object* v___x_2824_; 
lean_inc(v___y_2817_);
lean_inc_ref(v___y_2816_);
v___f_2823_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2823_, 0, v_k_2814_);
lean_closure_set(v___f_2823_, 1, v___y_2816_);
lean_closure_set(v___f_2823_, 2, v___y_2817_);
v___x_2824_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2811_, v_bi_2812_, v_type_2813_, v___f_2823_, v_kind_2815_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
if (lean_obj_tag(v___x_2824_) == 0)
{
return v___x_2824_;
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2824_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2824_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2825_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg___boxed(lean_object* v_name_2833_, lean_object* v_bi_2834_, lean_object* v_type_2835_, lean_object* v_k_2836_, lean_object* v_kind_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
uint8_t v_bi_boxed_2845_; uint8_t v_kind_boxed_2846_; lean_object* v_res_2847_; 
v_bi_boxed_2845_ = lean_unbox(v_bi_2834_);
v_kind_boxed_2846_ = lean_unbox(v_kind_2837_);
v_res_2847_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg(v_name_2833_, v_bi_boxed_2845_, v_type_2835_, v_k_2836_, v_kind_boxed_2846_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5(lean_object* v_00_u03b1_2848_, lean_object* v_name_2849_, uint8_t v_bi_2850_, lean_object* v_type_2851_, lean_object* v_k_2852_, uint8_t v_kind_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_){
_start:
{
lean_object* v___x_2861_; 
v___x_2861_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg(v_name_2849_, v_bi_2850_, v_type_2851_, v_k_2852_, v_kind_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___boxed(lean_object* v_00_u03b1_2862_, lean_object* v_name_2863_, lean_object* v_bi_2864_, lean_object* v_type_2865_, lean_object* v_k_2866_, lean_object* v_kind_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
uint8_t v_bi_boxed_2875_; uint8_t v_kind_boxed_2876_; lean_object* v_res_2877_; 
v_bi_boxed_2875_ = lean_unbox(v_bi_2864_);
v_kind_boxed_2876_ = lean_unbox(v_kind_2867_);
v_res_2877_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5(v_00_u03b1_2862_, v_name_2863_, v_bi_boxed_2875_, v_type_2865_, v_k_2866_, v_kind_boxed_2876_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
return v_res_2877_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8(lean_object* v_opts_2878_, lean_object* v_opt_2879_){
_start:
{
lean_object* v_name_2880_; lean_object* v_defValue_2881_; lean_object* v_map_2882_; lean_object* v___x_2883_; 
v_name_2880_ = lean_ctor_get(v_opt_2879_, 0);
v_defValue_2881_ = lean_ctor_get(v_opt_2879_, 1);
v_map_2882_ = lean_ctor_get(v_opts_2878_, 0);
v___x_2883_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2882_, v_name_2880_);
if (lean_obj_tag(v___x_2883_) == 0)
{
uint8_t v___x_2884_; 
v___x_2884_ = lean_unbox(v_defValue_2881_);
return v___x_2884_;
}
else
{
lean_object* v_val_2885_; 
v_val_2885_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_val_2885_);
lean_dec_ref_known(v___x_2883_, 1);
if (lean_obj_tag(v_val_2885_) == 1)
{
uint8_t v_v_2886_; 
v_v_2886_ = lean_ctor_get_uint8(v_val_2885_, 0);
lean_dec_ref_known(v_val_2885_, 0);
return v_v_2886_;
}
else
{
uint8_t v___x_2887_; 
lean_dec(v_val_2885_);
v___x_2887_ = lean_unbox(v_defValue_2881_);
return v___x_2887_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8___boxed(lean_object* v_opts_2888_, lean_object* v_opt_2889_){
_start:
{
uint8_t v_res_2890_; lean_object* v_r_2891_; 
v_res_2890_ = l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8(v_opts_2888_, v_opt_2889_);
lean_dec_ref(v_opt_2889_);
lean_dec_ref(v_opts_2888_);
v_r_2891_ = lean_box(v_res_2890_);
return v_r_2891_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0(uint8_t v_suppressElabErrors_2899_, uint8_t v___y_2900_, lean_object* v_x_2901_){
_start:
{
if (lean_obj_tag(v_x_2901_) == 1)
{
lean_object* v_pre_2902_; 
v_pre_2902_ = lean_ctor_get(v_x_2901_, 0);
switch(lean_obj_tag(v_pre_2902_))
{
case 1:
{
lean_object* v_pre_2903_; 
v_pre_2903_ = lean_ctor_get(v_pre_2902_, 0);
switch(lean_obj_tag(v_pre_2903_))
{
case 0:
{
lean_object* v_str_2904_; lean_object* v_str_2905_; lean_object* v___x_2906_; uint8_t v___x_2907_; 
v_str_2904_ = lean_ctor_get(v_x_2901_, 1);
v_str_2905_ = lean_ctor_get(v_pre_2902_, 1);
v___x_2906_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__8));
v___x_2907_ = lean_string_dec_eq(v_str_2905_, v___x_2906_);
if (v___x_2907_ == 0)
{
lean_object* v___x_2908_; uint8_t v___x_2909_; 
v___x_2908_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__0));
v___x_2909_ = lean_string_dec_eq(v_str_2905_, v___x_2908_);
if (v___x_2909_ == 0)
{
return v___x_2909_;
}
else
{
lean_object* v___x_2910_; uint8_t v___x_2911_; 
v___x_2910_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__1));
v___x_2911_ = lean_string_dec_eq(v_str_2904_, v___x_2910_);
if (v___x_2911_ == 0)
{
return v___x_2911_;
}
else
{
return v_suppressElabErrors_2899_;
}
}
}
else
{
lean_object* v___x_2912_; uint8_t v___x_2913_; 
v___x_2912_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__2));
v___x_2913_ = lean_string_dec_eq(v_str_2904_, v___x_2912_);
if (v___x_2913_ == 0)
{
return v___x_2913_;
}
else
{
return v_suppressElabErrors_2899_;
}
}
}
case 1:
{
lean_object* v_pre_2914_; 
v_pre_2914_ = lean_ctor_get(v_pre_2903_, 0);
if (lean_obj_tag(v_pre_2914_) == 0)
{
lean_object* v_str_2915_; lean_object* v_str_2916_; lean_object* v_str_2917_; lean_object* v___x_2918_; uint8_t v___x_2919_; 
v_str_2915_ = lean_ctor_get(v_x_2901_, 1);
v_str_2916_ = lean_ctor_get(v_pre_2902_, 1);
v_str_2917_ = lean_ctor_get(v_pre_2903_, 1);
v___x_2918_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__3));
v___x_2919_ = lean_string_dec_eq(v_str_2917_, v___x_2918_);
if (v___x_2919_ == 0)
{
return v___x_2919_;
}
else
{
lean_object* v___x_2920_; uint8_t v___x_2921_; 
v___x_2920_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__4));
v___x_2921_ = lean_string_dec_eq(v_str_2916_, v___x_2920_);
if (v___x_2921_ == 0)
{
return v___x_2921_;
}
else
{
lean_object* v___x_2922_; uint8_t v___x_2923_; 
v___x_2922_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__5));
v___x_2923_ = lean_string_dec_eq(v_str_2915_, v___x_2922_);
if (v___x_2923_ == 0)
{
return v___x_2923_;
}
else
{
return v_suppressElabErrors_2899_;
}
}
}
}
else
{
return v___y_2900_;
}
}
default: 
{
return v___y_2900_;
}
}
}
case 0:
{
lean_object* v_str_2924_; lean_object* v___x_2925_; uint8_t v___x_2926_; 
v_str_2924_ = lean_ctor_get(v_x_2901_, 1);
v___x_2925_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__6));
v___x_2926_ = lean_string_dec_eq(v_str_2924_, v___x_2925_);
if (v___x_2926_ == 0)
{
return v___x_2926_;
}
else
{
return v_suppressElabErrors_2899_;
}
}
default: 
{
return v___y_2900_;
}
}
}
else
{
return v___y_2900_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___boxed(lean_object* v_suppressElabErrors_2927_, lean_object* v___y_2928_, lean_object* v_x_2929_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2930_; uint8_t v___y_33745__boxed_2931_; uint8_t v_res_2932_; lean_object* v_r_2933_; 
v_suppressElabErrors_boxed_2930_ = lean_unbox(v_suppressElabErrors_2927_);
v___y_33745__boxed_2931_ = lean_unbox(v___y_2928_);
v_res_2932_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0(v_suppressElabErrors_boxed_2930_, v___y_33745__boxed_2931_, v_x_2929_);
lean_dec(v_x_2929_);
v_r_2933_ = lean_box(v_res_2932_);
return v_r_2933_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0(void){
_start:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2934_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__14, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__14_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__14);
v___x_2935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2934_);
return v___x_2935_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__1(void){
_start:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2936_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0);
v___x_2937_ = lean_unsigned_to_nat(0u);
v___x_2938_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
lean_ctor_set(v___x_2938_, 1, v___x_2937_);
lean_ctor_set(v___x_2938_, 2, v___x_2937_);
lean_ctor_set(v___x_2938_, 3, v___x_2937_);
lean_ctor_set(v___x_2938_, 4, v___x_2936_);
lean_ctor_set(v___x_2938_, 5, v___x_2936_);
lean_ctor_set(v___x_2938_, 6, v___x_2936_);
lean_ctor_set(v___x_2938_, 7, v___x_2936_);
lean_ctor_set(v___x_2938_, 8, v___x_2936_);
lean_ctor_set(v___x_2938_, 9, v___x_2936_);
lean_ctor_set(v___x_2938_, 10, v___x_2936_);
return v___x_2938_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__2(void){
_start:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2939_ = lean_unsigned_to_nat(32u);
v___x_2940_ = lean_mk_empty_array_with_capacity(v___x_2939_);
v___x_2941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
return v___x_2941_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__3(void){
_start:
{
size_t v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2942_ = ((size_t)5ULL);
v___x_2943_ = lean_unsigned_to_nat(0u);
v___x_2944_ = lean_unsigned_to_nat(32u);
v___x_2945_ = lean_mk_empty_array_with_capacity(v___x_2944_);
v___x_2946_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__2);
v___x_2947_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2947_, 0, v___x_2946_);
lean_ctor_set(v___x_2947_, 1, v___x_2945_);
lean_ctor_set(v___x_2947_, 2, v___x_2943_);
lean_ctor_set(v___x_2947_, 3, v___x_2943_);
lean_ctor_set_usize(v___x_2947_, 4, v___x_2942_);
return v___x_2947_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__4(void){
_start:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2948_ = lean_box(1);
v___x_2949_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__3);
v___x_2950_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0);
v___x_2951_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
lean_ctor_set(v___x_2951_, 1, v___x_2949_);
lean_ctor_set(v___x_2951_, 2, v___x_2948_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19(lean_object* v_msgData_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
lean_object* v___x_2956_; lean_object* v_toCold_2957_; lean_object* v_env_2958_; lean_object* v_options_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2956_ = lean_st_ref_get(v___y_2954_);
v_toCold_2957_ = lean_ctor_get(v___y_2953_, 0);
v_env_2958_ = lean_ctor_get(v___x_2956_, 0);
lean_inc_ref(v_env_2958_);
lean_dec(v___x_2956_);
v_options_2959_ = lean_ctor_get(v_toCold_2957_, 2);
v___x_2960_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__1);
v___x_2961_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__4);
lean_inc_ref(v_options_2959_);
v___x_2962_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2962_, 0, v_env_2958_);
lean_ctor_set(v___x_2962_, 1, v___x_2960_);
lean_ctor_set(v___x_2962_, 2, v___x_2961_);
lean_ctor_set(v___x_2962_, 3, v_options_2959_);
v___x_2963_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2962_);
lean_ctor_set(v___x_2963_, 1, v_msgData_2952_);
v___x_2964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2963_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___boxed(lean_object* v_msgData_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19(v_msgData_2965_, v___y_2966_, v___y_2967_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13(lean_object* v_ref_2971_, lean_object* v_msgData_2972_, uint8_t v_severity_2973_, uint8_t v_isSilent_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
lean_object* v___y_2979_; uint8_t v___y_2980_; uint8_t v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v_toCold_2986_; lean_object* v___y_2987_; lean_object* v___y_3016_; lean_object* v___y_3017_; uint8_t v___y_3018_; lean_object* v___y_3019_; uint8_t v___y_3020_; lean_object* v___y_3021_; uint8_t v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3043_; lean_object* v___y_3044_; uint8_t v___y_3045_; uint8_t v___y_3046_; uint8_t v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; uint8_t v___y_3053_; uint8_t v___y_3054_; uint8_t v___y_3055_; uint8_t v___x_3066_; uint8_t v___y_3068_; uint8_t v___y_3069_; uint8_t v___y_3070_; uint8_t v___y_3072_; uint8_t v___x_3080_; 
v___x_3066_ = 2;
v___x_3080_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2973_, v___x_3066_);
if (v___x_3080_ == 0)
{
v___y_3072_ = v___x_3080_;
goto v___jp_3071_;
}
else
{
uint8_t v___x_3081_; 
lean_inc_ref(v_msgData_2972_);
v___x_3081_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2972_);
v___y_3072_ = v___x_3081_;
goto v___jp_3071_;
}
v___jp_2978_:
{
lean_object* v_currNamespace_2988_; lean_object* v_openDecls_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v_env_2994_; lean_object* v_nextMacroScope_2995_; lean_object* v_ngen_2996_; lean_object* v_auxDeclNGen_2997_; lean_object* v_traceState_2998_; lean_object* v_cache_2999_; lean_object* v_recordedDeps_3000_; lean_object* v_messages_3001_; lean_object* v_infoState_3002_; lean_object* v_snapshotTasks_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3014_; 
v_currNamespace_2988_ = lean_ctor_get(v_toCold_2986_, 4);
v_openDecls_2989_ = lean_ctor_get(v_toCold_2986_, 5);
lean_inc(v_openDecls_2989_);
lean_inc(v_currNamespace_2988_);
v___x_2990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2990_, 0, v_currNamespace_2988_);
lean_ctor_set(v___x_2990_, 1, v_openDecls_2989_);
v___x_2991_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2990_);
lean_ctor_set(v___x_2991_, 1, v___y_2985_);
lean_inc_ref(v___y_2979_);
lean_inc_ref(v___y_2984_);
v___x_2992_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2992_, 0, v___y_2984_);
lean_ctor_set(v___x_2992_, 1, v___y_2983_);
lean_ctor_set(v___x_2992_, 2, v___y_2982_);
lean_ctor_set(v___x_2992_, 3, v___y_2979_);
lean_ctor_set(v___x_2992_, 4, v___x_2991_);
lean_ctor_set_uint8(v___x_2992_, sizeof(void*)*5, v___y_2981_);
lean_ctor_set_uint8(v___x_2992_, sizeof(void*)*5 + 1, v___y_2980_);
lean_ctor_set_uint8(v___x_2992_, sizeof(void*)*5 + 2, v_isSilent_2974_);
v___x_2993_ = lean_st_ref_take(v___y_2987_);
v_env_2994_ = lean_ctor_get(v___x_2993_, 0);
v_nextMacroScope_2995_ = lean_ctor_get(v___x_2993_, 1);
v_ngen_2996_ = lean_ctor_get(v___x_2993_, 2);
v_auxDeclNGen_2997_ = lean_ctor_get(v___x_2993_, 3);
v_traceState_2998_ = lean_ctor_get(v___x_2993_, 4);
v_cache_2999_ = lean_ctor_get(v___x_2993_, 5);
v_recordedDeps_3000_ = lean_ctor_get(v___x_2993_, 6);
v_messages_3001_ = lean_ctor_get(v___x_2993_, 7);
v_infoState_3002_ = lean_ctor_get(v___x_2993_, 8);
v_snapshotTasks_3003_ = lean_ctor_get(v___x_2993_, 9);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3005_ = v___x_2993_;
v_isShared_3006_ = v_isSharedCheck_3014_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_snapshotTasks_3003_);
lean_inc(v_infoState_3002_);
lean_inc(v_messages_3001_);
lean_inc(v_recordedDeps_3000_);
lean_inc(v_cache_2999_);
lean_inc(v_traceState_2998_);
lean_inc(v_auxDeclNGen_2997_);
lean_inc(v_ngen_2996_);
lean_inc(v_nextMacroScope_2995_);
lean_inc(v_env_2994_);
lean_dec(v___x_2993_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3014_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3010_; 
v___x_3007_ = lean_box(0);
v___x_3008_ = l_Lean_MessageLog_add(v___x_2992_, v_messages_3001_);
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 7, v___x_3008_);
v___x_3010_ = v___x_3005_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_env_2994_);
lean_ctor_set(v_reuseFailAlloc_3013_, 1, v_nextMacroScope_2995_);
lean_ctor_set(v_reuseFailAlloc_3013_, 2, v_ngen_2996_);
lean_ctor_set(v_reuseFailAlloc_3013_, 3, v_auxDeclNGen_2997_);
lean_ctor_set(v_reuseFailAlloc_3013_, 4, v_traceState_2998_);
lean_ctor_set(v_reuseFailAlloc_3013_, 5, v_cache_2999_);
lean_ctor_set(v_reuseFailAlloc_3013_, 6, v_recordedDeps_3000_);
lean_ctor_set(v_reuseFailAlloc_3013_, 7, v___x_3008_);
lean_ctor_set(v_reuseFailAlloc_3013_, 8, v_infoState_3002_);
lean_ctor_set(v_reuseFailAlloc_3013_, 9, v_snapshotTasks_3003_);
v___x_3010_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3011_ = lean_st_ref_put(v___y_2987_, v___x_3010_);
v___x_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3007_);
return v___x_3012_;
}
}
}
v___jp_3015_:
{
lean_object* v_fileName_3024_; lean_object* v_fileMap_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3041_; 
v_fileName_3024_ = lean_ctor_get(v___y_3019_, 0);
v_fileMap_3025_ = lean_ctor_get(v___y_3019_, 1);
v___x_3026_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2972_);
v___x_3027_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19(v___x_3026_, v___y_2975_, v___y_2976_);
v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3030_ = v___x_3027_;
v_isShared_3031_ = v_isSharedCheck_3041_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_3027_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3041_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
lean_inc_ref_n(v_fileMap_3025_, 2);
v___x_3032_ = l_Lean_FileMap_toPosition(v_fileMap_3025_, v___y_3021_);
lean_dec(v___y_3021_);
v___x_3033_ = l_Lean_FileMap_toPosition(v_fileMap_3025_, v___y_3023_);
lean_dec(v___y_3023_);
v___x_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
v___x_3035_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___closed__0));
if (v___y_3022_ == 0)
{
lean_del_object(v___x_3030_);
lean_dec_ref(v___y_3017_);
v___y_2979_ = v___x_3035_;
v___y_2980_ = v___y_3018_;
v___y_2981_ = v___y_3020_;
v___y_2982_ = v___x_3034_;
v___y_2983_ = v___x_3032_;
v___y_2984_ = v_fileName_3024_;
v___y_2985_ = v_a_3028_;
v_toCold_2986_ = v___y_3016_;
v___y_2987_ = v___y_2976_;
goto v___jp_2978_;
}
else
{
uint8_t v___x_3036_; 
lean_inc(v_a_3028_);
v___x_3036_ = l_Lean_MessageData_hasTag(v___y_3017_, v_a_3028_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; lean_object* v___x_3039_; 
lean_dec_ref_known(v___x_3034_, 1);
lean_dec_ref(v___x_3032_);
lean_dec(v_a_3028_);
v___x_3037_ = lean_box(0);
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 0, v___x_3037_);
v___x_3039_ = v___x_3030_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3037_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
else
{
lean_del_object(v___x_3030_);
v___y_2979_ = v___x_3035_;
v___y_2980_ = v___y_3018_;
v___y_2981_ = v___y_3020_;
v___y_2982_ = v___x_3034_;
v___y_2983_ = v___x_3032_;
v___y_2984_ = v_fileName_3024_;
v___y_2985_ = v_a_3028_;
v_toCold_2986_ = v___y_3016_;
v___y_2987_ = v___y_2976_;
goto v___jp_2978_;
}
}
}
}
v___jp_3042_:
{
lean_object* v___x_3050_; 
v___x_3050_ = l_Lean_Syntax_getTailPos_x3f(v___y_3048_, v___y_3047_);
lean_dec(v___y_3048_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_inc(v___y_3049_);
v___y_3016_ = v___y_3043_;
v___y_3017_ = v___y_3044_;
v___y_3018_ = v___y_3046_;
v___y_3019_ = v___y_3043_;
v___y_3020_ = v___y_3047_;
v___y_3021_ = v___y_3049_;
v___y_3022_ = v___y_3045_;
v___y_3023_ = v___y_3049_;
goto v___jp_3015_;
}
else
{
lean_object* v_val_3051_; 
v_val_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_val_3051_);
lean_dec_ref_known(v___x_3050_, 1);
v___y_3016_ = v___y_3043_;
v___y_3017_ = v___y_3044_;
v___y_3018_ = v___y_3046_;
v___y_3019_ = v___y_3043_;
v___y_3020_ = v___y_3047_;
v___y_3021_ = v___y_3049_;
v___y_3022_ = v___y_3045_;
v___y_3023_ = v_val_3051_;
goto v___jp_3015_;
}
}
v___jp_3052_:
{
lean_object* v_toCold_3056_; lean_object* v_ref_3057_; uint8_t v_suppressElabErrors_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___f_3061_; lean_object* v_ref_3062_; lean_object* v___x_3063_; 
v_toCold_3056_ = lean_ctor_get(v___y_2975_, 0);
v_ref_3057_ = lean_ctor_get(v___y_2975_, 2);
v_suppressElabErrors_3058_ = lean_ctor_get_uint8(v___y_2975_, sizeof(void*)*3 + 2);
v___x_3059_ = lean_box(v_suppressElabErrors_3058_);
v___x_3060_ = lean_box(v___y_3053_);
v___f_3061_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3061_, 0, v___x_3059_);
lean_closure_set(v___f_3061_, 1, v___x_3060_);
v_ref_3062_ = l_Lean_replaceRef(v_ref_2971_, v_ref_3057_);
v___x_3063_ = l_Lean_Syntax_getPos_x3f(v_ref_3062_, v___y_3054_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v___x_3064_; 
v___x_3064_ = lean_unsigned_to_nat(0u);
v___y_3043_ = v_toCold_3056_;
v___y_3044_ = v___f_3061_;
v___y_3045_ = v_suppressElabErrors_3058_;
v___y_3046_ = v___y_3055_;
v___y_3047_ = v___y_3054_;
v___y_3048_ = v_ref_3062_;
v___y_3049_ = v___x_3064_;
goto v___jp_3042_;
}
else
{
lean_object* v_val_3065_; 
v_val_3065_ = lean_ctor_get(v___x_3063_, 0);
lean_inc(v_val_3065_);
lean_dec_ref_known(v___x_3063_, 1);
v___y_3043_ = v_toCold_3056_;
v___y_3044_ = v___f_3061_;
v___y_3045_ = v_suppressElabErrors_3058_;
v___y_3046_ = v___y_3055_;
v___y_3047_ = v___y_3054_;
v___y_3048_ = v_ref_3062_;
v___y_3049_ = v_val_3065_;
goto v___jp_3042_;
}
}
v___jp_3067_:
{
if (v___y_3070_ == 0)
{
v___y_3053_ = v___y_3068_;
v___y_3054_ = v___y_3069_;
v___y_3055_ = v_severity_2973_;
goto v___jp_3052_;
}
else
{
v___y_3053_ = v___y_3068_;
v___y_3054_ = v___y_3069_;
v___y_3055_ = v___x_3066_;
goto v___jp_3052_;
}
}
v___jp_3071_:
{
if (v___y_3072_ == 0)
{
uint8_t v___x_3073_; uint8_t v___x_3074_; 
v___x_3073_ = 1;
v___x_3074_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2973_, v___x_3073_);
if (v___x_3074_ == 0)
{
v___y_3068_ = v___y_3072_;
v___y_3069_ = v___y_3072_;
v___y_3070_ = v___x_3074_;
goto v___jp_3067_;
}
else
{
lean_object* v___x_3075_; lean_object* v___x_3076_; uint8_t v___x_3077_; 
v___x_3075_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2975_);
v___x_3076_ = l_Lean_warningAsError;
v___x_3077_ = l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8(v___x_3075_, v___x_3076_);
lean_dec_ref(v___x_3075_);
v___y_3068_ = v___y_3072_;
v___y_3069_ = v___y_3072_;
v___y_3070_ = v___x_3077_;
goto v___jp_3067_;
}
}
else
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
lean_dec_ref(v_msgData_2972_);
v___x_3078_ = lean_box(0);
v___x_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3078_);
return v___x_3079_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___boxed(lean_object* v_ref_3082_, lean_object* v_msgData_3083_, lean_object* v_severity_3084_, lean_object* v_isSilent_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
uint8_t v_severity_boxed_3089_; uint8_t v_isSilent_boxed_3090_; lean_object* v_res_3091_; 
v_severity_boxed_3089_ = lean_unbox(v_severity_3084_);
v_isSilent_boxed_3090_ = lean_unbox(v_isSilent_3085_);
v_res_3091_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13(v_ref_3082_, v_msgData_3083_, v_severity_boxed_3089_, v_isSilent_boxed_3090_, v___y_3086_, v___y_3087_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec(v_ref_3082_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9(lean_object* v_ref_3092_, lean_object* v_msgData_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_){
_start:
{
uint8_t v___x_3097_; uint8_t v___x_3098_; lean_object* v___x_3099_; 
v___x_3097_ = 0;
v___x_3098_ = 0;
v___x_3099_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13(v_ref_3092_, v_msgData_3093_, v___x_3097_, v___x_3098_, v___y_3094_, v___y_3095_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9___boxed(lean_object* v_ref_3100_, lean_object* v_msgData_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9(v_ref_3100_, v_msgData_3101_, v___y_3102_, v___y_3103_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v_ref_3100_);
return v_res_3105_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3107_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__0));
v___x_3108_ = l_Lean_stringToMessageData(v___x_3107_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0(lean_object* v___x_3109_, lean_object* v___x_3110_, lean_object* v_ref_3111_, lean_object* v_x_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
lean_object* v_ref_3116_; lean_object* v___x_3117_; 
v_ref_3116_ = lean_ctor_get(v___y_3113_, 2);
v___x_3117_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer(v___x_3109_, v___x_3110_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3131_; 
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3120_ = v___x_3117_;
v_isShared_3121_ = v_isSharedCheck_3131_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3117_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3131_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
if (lean_obj_tag(v_a_3118_) == 1)
{
lean_object* v_val_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
lean_del_object(v___x_3120_);
v_val_3122_ = lean_ctor_get(v_a_3118_, 0);
lean_inc(v_val_3122_);
lean_dec_ref_known(v_a_3118_, 1);
v___x_3123_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__1, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__1_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__1);
v___x_3124_ = l_Lean_stringToMessageData(v_val_3122_);
v___x_3125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3123_);
lean_ctor_set(v___x_3125_, 1, v___x_3124_);
v___x_3126_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9(v_ref_3111_, v___x_3125_, v___y_3113_, v___y_3114_);
return v___x_3126_;
}
else
{
lean_object* v___x_3127_; lean_object* v___x_3129_; 
lean_dec(v_a_3118_);
v___x_3127_ = lean_box(0);
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 0, v___x_3127_);
v___x_3129_ = v___x_3120_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v___x_3127_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3143_; 
v_a_3132_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3134_ = v___x_3117_;
v_isShared_3135_ = v_isSharedCheck_3143_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3117_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3143_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3141_; 
v___x_3136_ = lean_io_error_to_string(v_a_3132_);
v___x_3137_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3136_);
v___x_3138_ = l_Lean_MessageData_ofFormat(v___x_3137_);
lean_inc(v_ref_3116_);
v___x_3139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3139_, 0, v_ref_3116_);
lean_ctor_set(v___x_3139_, 1, v___x_3138_);
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 0, v___x_3139_);
v___x_3141_ = v___x_3134_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_3139_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___boxed(lean_object* v___x_3144_, lean_object* v___x_3145_, lean_object* v_ref_3146_, lean_object* v_x_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v_res_3151_; 
v_res_3151_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0(v___x_3144_, v___x_3145_, v_ref_3146_, v_x_3147_, v___y_3148_, v___y_3149_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v_ref_3146_);
lean_dec_ref(v___x_3144_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__1(lean_object* v___x_3152_, lean_object* v___x_3153_, uint8_t v___x_3154_, uint8_t v___x_3155_, uint8_t v___x_3156_, lean_object* v_fVar_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
lean_inc_ref(v_fVar_3157_);
v___x_3165_ = l_Lean_mkAppN(v_fVar_3157_, v___x_3152_);
v___x_3166_ = lean_array_push(v___x_3153_, v_fVar_3157_);
v___x_3167_ = l_Lean_Meta_mkLambdaFVars(v___x_3166_, v___x_3165_, v___x_3154_, v___x_3155_, v___x_3154_, v___x_3155_, v___x_3156_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
lean_dec_ref(v___x_3166_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__1___boxed(lean_object* v___x_3168_, lean_object* v___x_3169_, lean_object* v___x_3170_, lean_object* v___x_3171_, lean_object* v___x_3172_, lean_object* v_fVar_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_){
_start:
{
uint8_t v___x_34192__boxed_3181_; uint8_t v___x_34193__boxed_3182_; uint8_t v___x_34194__boxed_3183_; lean_object* v_res_3184_; 
v___x_34192__boxed_3181_ = lean_unbox(v___x_3170_);
v___x_34193__boxed_3182_ = lean_unbox(v___x_3171_);
v___x_34194__boxed_3183_ = lean_unbox(v___x_3172_);
v_res_3184_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__1(v___x_3168_, v___x_3169_, v___x_34192__boxed_3181_, v___x_34193__boxed_3182_, v___x_34194__boxed_3183_, v_fVar_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec_ref(v___x_3168_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__2(lean_object* v___x_3185_, lean_object* v_a_3186_, uint8_t v___x_3187_, uint8_t v___x_3188_, uint8_t v___x_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_){
_start:
{
lean_object* v___x_3197_; 
v___x_3197_ = l_Lean_Meta_mkLambdaFVars(v___x_3185_, v_a_3186_, v___x_3187_, v___x_3188_, v___x_3187_, v___x_3188_, v___x_3189_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
if (lean_obj_tag(v___x_3197_) == 0)
{
lean_object* v_a_3198_; lean_object* v___x_3199_; 
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
lean_inc_n(v_a_3198_, 2);
lean_dec_ref_known(v___x_3197_, 1);
lean_inc(v___y_3193_);
v___x_3199_ = lean_infer_type(v_a_3198_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v_a_3200_; lean_object* v___x_3201_; lean_object* v_a_3202_; lean_object* v___x_3203_; lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3212_; 
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
lean_inc(v_a_3200_);
lean_dec_ref_known(v___x_3199_, 1);
v___x_3201_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(v_a_3198_, v___y_3193_);
v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
lean_inc(v_a_3202_);
lean_dec_ref(v___x_3201_);
v___x_3203_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(v_a_3200_, v___y_3193_);
lean_dec(v___y_3193_);
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3206_ = v___x_3203_;
v_isShared_3207_ = v_isSharedCheck_3212_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3203_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3212_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3208_; lean_object* v___x_3210_; 
v___x_3208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3208_, 0, v_a_3202_);
lean_ctor_set(v___x_3208_, 1, v_a_3204_);
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 0, v___x_3208_);
v___x_3210_ = v___x_3206_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___x_3208_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
else
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
lean_dec(v_a_3198_);
lean_dec(v___y_3193_);
v_a_3213_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3215_ = v___x_3199_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3199_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3216_ == 0)
{
v___x_3218_ = v___x_3215_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
}
else
{
lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3228_; 
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
v_a_3221_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3223_ = v___x_3197_;
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___x_3197_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3226_; 
if (v_isShared_3224_ == 0)
{
v___x_3226_ = v___x_3223_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3221_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__2___boxed(lean_object* v___x_3229_, lean_object* v_a_3230_, lean_object* v___x_3231_, lean_object* v___x_3232_, lean_object* v___x_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
uint8_t v___x_34234__boxed_3241_; uint8_t v___x_34235__boxed_3242_; uint8_t v___x_34236__boxed_3243_; lean_object* v_res_3244_; 
v___x_34234__boxed_3241_ = lean_unbox(v___x_3231_);
v___x_34235__boxed_3242_ = lean_unbox(v___x_3232_);
v___x_34236__boxed_3243_ = lean_unbox(v___x_3233_);
v_res_3244_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__2(v___x_3229_, v_a_3230_, v___x_34234__boxed_3241_, v___x_34235__boxed_3242_, v___x_34236__boxed_3243_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec_ref(v___x_3229_);
return v_res_3244_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4(void){
_start:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3253_ = lean_box(0);
v___x_3254_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__3));
v___x_3255_ = l_Lean_Expr_const___override(v___x_3254_, v___x_3253_);
return v___x_3255_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__7(void){
_start:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3260_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__0));
v___x_3261_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__6));
v___x_3262_ = l_Lean_Expr_const___override(v___x_3261_, v___x_3260_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10(lean_object* v_as_3263_, size_t v_i_3264_, size_t v_stop_3265_, lean_object* v_b_3266_){
_start:
{
uint8_t v___x_3267_; 
v___x_3267_ = lean_usize_dec_eq(v_i_3264_, v_stop_3265_);
if (v___x_3267_ == 0)
{
lean_object* v___x_3268_; size_t v___x_3269_; size_t v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
v___x_3268_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4);
v___x_3269_ = ((size_t)1ULL);
v___x_3270_ = lean_usize_sub(v_i_3264_, v___x_3269_);
v___x_3271_ = lean_array_uget_borrowed(v_as_3263_, v___x_3270_);
v___x_3272_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__7);
lean_inc(v___x_3271_);
v___x_3273_ = l_Lean_mkApp3(v___x_3272_, v___x_3268_, v___x_3271_, v_b_3266_);
v_i_3264_ = v___x_3270_;
v_b_3266_ = v___x_3273_;
goto _start;
}
else
{
return v_b_3266_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___boxed(lean_object* v_as_3275_, lean_object* v_i_3276_, lean_object* v_stop_3277_, lean_object* v_b_3278_){
_start:
{
size_t v_i_boxed_3279_; size_t v_stop_boxed_3280_; lean_object* v_res_3281_; 
v_i_boxed_3279_ = lean_unbox_usize(v_i_3276_);
lean_dec(v_i_3276_);
v_stop_boxed_3280_ = lean_unbox_usize(v_stop_3277_);
lean_dec(v_stop_3277_);
v_res_3281_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10(v_as_3275_, v_i_boxed_3279_, v_stop_boxed_3280_, v_b_3278_);
lean_dec_ref(v_as_3275_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7(lean_object* v_init_3282_, lean_object* v_l_3283_){
_start:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; uint8_t v___x_3287_; 
v___x_3284_ = lean_array_mk(v_l_3283_);
v___x_3285_ = lean_array_get_size(v___x_3284_);
v___x_3286_ = lean_unsigned_to_nat(0u);
v___x_3287_ = lean_nat_dec_lt(v___x_3286_, v___x_3285_);
if (v___x_3287_ == 0)
{
lean_dec_ref(v___x_3284_);
return v_init_3282_;
}
else
{
size_t v___x_3288_; size_t v___x_3289_; lean_object* v___x_3290_; 
v___x_3288_ = lean_usize_of_nat(v___x_3285_);
v___x_3289_ = ((size_t)0ULL);
v___x_3290_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10(v___x_3284_, v___x_3288_, v___x_3289_, v_init_3282_);
lean_dec_ref(v___x_3284_);
return v___x_3290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___redArg(lean_object* v_as_3291_, size_t v_sz_3292_, size_t v_i_3293_, lean_object* v_b_3294_){
_start:
{
uint8_t v___x_3296_; 
v___x_3296_ = lean_usize_dec_lt(v_i_3293_, v_sz_3292_);
if (v___x_3296_ == 0)
{
lean_object* v___x_3297_; 
v___x_3297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3297_, 0, v_b_3294_);
return v___x_3297_;
}
else
{
lean_object* v_snd_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3315_; 
v_snd_3298_ = lean_ctor_get(v_b_3294_, 1);
v_isSharedCheck_3315_ = !lean_is_exclusive(v_b_3294_);
if (v_isSharedCheck_3315_ == 0)
{
lean_object* v_unused_3316_; 
v_unused_3316_ = lean_ctor_get(v_b_3294_, 0);
lean_dec(v_unused_3316_);
v___x_3300_ = v_b_3294_;
v_isShared_3301_ = v_isSharedCheck_3315_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_snd_3298_);
lean_dec(v_b_3294_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3315_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3302_; lean_object* v_a_3304_; lean_object* v_a_3311_; 
v___x_3302_ = lean_box(0);
v_a_3311_ = lean_array_uget_borrowed(v_as_3291_, v_i_3293_);
if (lean_obj_tag(v_a_3311_) == 0)
{
v_a_3304_ = v_snd_3298_;
goto v___jp_3303_;
}
else
{
lean_object* v_val_3312_; uint8_t v___x_3313_; 
v_val_3312_ = lean_ctor_get(v_a_3311_, 0);
v___x_3313_ = l_Lean_LocalDecl_isAuxDecl(v_val_3312_);
if (v___x_3313_ == 0)
{
lean_object* v___x_3314_; 
lean_inc(v_val_3312_);
v___x_3314_ = lean_array_push(v_snd_3298_, v_val_3312_);
v_a_3304_ = v___x_3314_;
goto v___jp_3303_;
}
else
{
v_a_3304_ = v_snd_3298_;
goto v___jp_3303_;
}
}
v___jp_3303_:
{
lean_object* v___x_3306_; 
if (v_isShared_3301_ == 0)
{
lean_ctor_set(v___x_3300_, 1, v_a_3304_);
lean_ctor_set(v___x_3300_, 0, v___x_3302_);
v___x_3306_ = v___x_3300_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v___x_3302_);
lean_ctor_set(v_reuseFailAlloc_3310_, 1, v_a_3304_);
v___x_3306_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
size_t v___x_3307_; size_t v___x_3308_; 
v___x_3307_ = ((size_t)1ULL);
v___x_3308_ = lean_usize_add(v_i_3293_, v___x_3307_);
v_i_3293_ = v___x_3308_;
v_b_3294_ = v___x_3306_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___redArg___boxed(lean_object* v_as_3317_, lean_object* v_sz_3318_, lean_object* v_i_3319_, lean_object* v_b_3320_, lean_object* v___y_3321_){
_start:
{
size_t v_sz_boxed_3322_; size_t v_i_boxed_3323_; lean_object* v_res_3324_; 
v_sz_boxed_3322_ = lean_unbox_usize(v_sz_3318_);
lean_dec(v_sz_3318_);
v_i_boxed_3323_ = lean_unbox_usize(v_i_3319_);
lean_dec(v_i_3319_);
v_res_3324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___redArg(v_as_3317_, v_sz_boxed_3322_, v_i_boxed_3323_, v_b_3320_);
lean_dec_ref(v_as_3317_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1(lean_object* v_as_3325_, size_t v_sz_3326_, size_t v_i_3327_, lean_object* v_b_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
uint8_t v___x_3336_; 
v___x_3336_ = lean_usize_dec_lt(v_i_3327_, v_sz_3326_);
if (v___x_3336_ == 0)
{
lean_object* v___x_3337_; 
v___x_3337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3337_, 0, v_b_3328_);
return v___x_3337_;
}
else
{
lean_object* v_snd_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3355_; 
v_snd_3338_ = lean_ctor_get(v_b_3328_, 1);
v_isSharedCheck_3355_ = !lean_is_exclusive(v_b_3328_);
if (v_isSharedCheck_3355_ == 0)
{
lean_object* v_unused_3356_; 
v_unused_3356_ = lean_ctor_get(v_b_3328_, 0);
lean_dec(v_unused_3356_);
v___x_3340_ = v_b_3328_;
v_isShared_3341_ = v_isSharedCheck_3355_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_snd_3338_);
lean_dec(v_b_3328_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3355_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3342_; lean_object* v_a_3344_; lean_object* v_a_3351_; 
v___x_3342_ = lean_box(0);
v_a_3351_ = lean_array_uget_borrowed(v_as_3325_, v_i_3327_);
if (lean_obj_tag(v_a_3351_) == 0)
{
v_a_3344_ = v_snd_3338_;
goto v___jp_3343_;
}
else
{
lean_object* v_val_3352_; uint8_t v___x_3353_; 
v_val_3352_ = lean_ctor_get(v_a_3351_, 0);
v___x_3353_ = l_Lean_LocalDecl_isAuxDecl(v_val_3352_);
if (v___x_3353_ == 0)
{
lean_object* v___x_3354_; 
lean_inc(v_val_3352_);
v___x_3354_ = lean_array_push(v_snd_3338_, v_val_3352_);
v_a_3344_ = v___x_3354_;
goto v___jp_3343_;
}
else
{
v_a_3344_ = v_snd_3338_;
goto v___jp_3343_;
}
}
v___jp_3343_:
{
lean_object* v___x_3346_; 
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 1, v_a_3344_);
lean_ctor_set(v___x_3340_, 0, v___x_3342_);
v___x_3346_ = v___x_3340_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3342_);
lean_ctor_set(v_reuseFailAlloc_3350_, 1, v_a_3344_);
v___x_3346_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
size_t v___x_3347_; size_t v___x_3348_; lean_object* v___x_3349_; 
v___x_3347_ = ((size_t)1ULL);
v___x_3348_ = lean_usize_add(v_i_3327_, v___x_3347_);
v___x_3349_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___redArg(v_as_3325_, v_sz_3326_, v___x_3348_, v___x_3346_);
return v___x_3349_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1___boxed(lean_object* v_as_3357_, lean_object* v_sz_3358_, lean_object* v_i_3359_, lean_object* v_b_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
size_t v_sz_boxed_3368_; size_t v_i_boxed_3369_; lean_object* v_res_3370_; 
v_sz_boxed_3368_ = lean_unbox_usize(v_sz_3358_);
lean_dec(v_sz_3358_);
v_i_boxed_3369_ = lean_unbox_usize(v_i_3359_);
lean_dec(v_i_3359_);
v_res_3370_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1(v_as_3357_, v_sz_boxed_3368_, v_i_boxed_3369_, v_b_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec_ref(v_as_3357_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___redArg(lean_object* v_as_3371_, size_t v_sz_3372_, size_t v_i_3373_, lean_object* v_b_3374_){
_start:
{
uint8_t v___x_3376_; 
v___x_3376_ = lean_usize_dec_lt(v_i_3373_, v_sz_3372_);
if (v___x_3376_ == 0)
{
lean_object* v___x_3377_; 
v___x_3377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3377_, 0, v_b_3374_);
return v___x_3377_;
}
else
{
lean_object* v_snd_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3395_; 
v_snd_3378_ = lean_ctor_get(v_b_3374_, 1);
v_isSharedCheck_3395_ = !lean_is_exclusive(v_b_3374_);
if (v_isSharedCheck_3395_ == 0)
{
lean_object* v_unused_3396_; 
v_unused_3396_ = lean_ctor_get(v_b_3374_, 0);
lean_dec(v_unused_3396_);
v___x_3380_ = v_b_3374_;
v_isShared_3381_ = v_isSharedCheck_3395_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_snd_3378_);
lean_dec(v_b_3374_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3395_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3382_; lean_object* v_a_3384_; lean_object* v_a_3391_; 
v___x_3382_ = lean_box(0);
v_a_3391_ = lean_array_uget_borrowed(v_as_3371_, v_i_3373_);
if (lean_obj_tag(v_a_3391_) == 0)
{
v_a_3384_ = v_snd_3378_;
goto v___jp_3383_;
}
else
{
lean_object* v_val_3392_; uint8_t v___x_3393_; 
v_val_3392_ = lean_ctor_get(v_a_3391_, 0);
v___x_3393_ = l_Lean_LocalDecl_isAuxDecl(v_val_3392_);
if (v___x_3393_ == 0)
{
lean_object* v___x_3394_; 
lean_inc(v_val_3392_);
v___x_3394_ = lean_array_push(v_snd_3378_, v_val_3392_);
v_a_3384_ = v___x_3394_;
goto v___jp_3383_;
}
else
{
v_a_3384_ = v_snd_3378_;
goto v___jp_3383_;
}
}
v___jp_3383_:
{
lean_object* v___x_3386_; 
if (v_isShared_3381_ == 0)
{
lean_ctor_set(v___x_3380_, 1, v_a_3384_);
lean_ctor_set(v___x_3380_, 0, v___x_3382_);
v___x_3386_ = v___x_3380_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3382_);
lean_ctor_set(v_reuseFailAlloc_3390_, 1, v_a_3384_);
v___x_3386_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
size_t v___x_3387_; size_t v___x_3388_; 
v___x_3387_ = ((size_t)1ULL);
v___x_3388_ = lean_usize_add(v_i_3373_, v___x_3387_);
v_i_3373_ = v___x_3388_;
v_b_3374_ = v___x_3386_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___redArg___boxed(lean_object* v_as_3397_, lean_object* v_sz_3398_, lean_object* v_i_3399_, lean_object* v_b_3400_, lean_object* v___y_3401_){
_start:
{
size_t v_sz_boxed_3402_; size_t v_i_boxed_3403_; lean_object* v_res_3404_; 
v_sz_boxed_3402_ = lean_unbox_usize(v_sz_3398_);
lean_dec(v_sz_3398_);
v_i_boxed_3403_ = lean_unbox_usize(v_i_3399_);
lean_dec(v_i_3399_);
v_res_3404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___redArg(v_as_3397_, v_sz_boxed_3402_, v_i_boxed_3403_, v_b_3400_);
lean_dec_ref(v_as_3397_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6(lean_object* v_as_3405_, size_t v_sz_3406_, size_t v_i_3407_, lean_object* v_b_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
uint8_t v___x_3416_; 
v___x_3416_ = lean_usize_dec_lt(v_i_3407_, v_sz_3406_);
if (v___x_3416_ == 0)
{
lean_object* v___x_3417_; 
v___x_3417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3417_, 0, v_b_3408_);
return v___x_3417_;
}
else
{
lean_object* v_snd_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3435_; 
v_snd_3418_ = lean_ctor_get(v_b_3408_, 1);
v_isSharedCheck_3435_ = !lean_is_exclusive(v_b_3408_);
if (v_isSharedCheck_3435_ == 0)
{
lean_object* v_unused_3436_; 
v_unused_3436_ = lean_ctor_get(v_b_3408_, 0);
lean_dec(v_unused_3436_);
v___x_3420_ = v_b_3408_;
v_isShared_3421_ = v_isSharedCheck_3435_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_snd_3418_);
lean_dec(v_b_3408_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3435_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3422_; lean_object* v_a_3424_; lean_object* v_a_3431_; 
v___x_3422_ = lean_box(0);
v_a_3431_ = lean_array_uget_borrowed(v_as_3405_, v_i_3407_);
if (lean_obj_tag(v_a_3431_) == 0)
{
v_a_3424_ = v_snd_3418_;
goto v___jp_3423_;
}
else
{
lean_object* v_val_3432_; uint8_t v___x_3433_; 
v_val_3432_ = lean_ctor_get(v_a_3431_, 0);
v___x_3433_ = l_Lean_LocalDecl_isAuxDecl(v_val_3432_);
if (v___x_3433_ == 0)
{
lean_object* v___x_3434_; 
lean_inc(v_val_3432_);
v___x_3434_ = lean_array_push(v_snd_3418_, v_val_3432_);
v_a_3424_ = v___x_3434_;
goto v___jp_3423_;
}
else
{
v_a_3424_ = v_snd_3418_;
goto v___jp_3423_;
}
}
v___jp_3423_:
{
lean_object* v___x_3426_; 
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 1, v_a_3424_);
lean_ctor_set(v___x_3420_, 0, v___x_3422_);
v___x_3426_ = v___x_3420_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v___x_3422_);
lean_ctor_set(v_reuseFailAlloc_3430_, 1, v_a_3424_);
v___x_3426_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
size_t v___x_3427_; size_t v___x_3428_; lean_object* v___x_3429_; 
v___x_3427_ = ((size_t)1ULL);
v___x_3428_ = lean_usize_add(v_i_3407_, v___x_3427_);
v___x_3429_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___redArg(v_as_3405_, v_sz_3406_, v___x_3428_, v___x_3426_);
return v___x_3429_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6___boxed(lean_object* v_as_3437_, lean_object* v_sz_3438_, lean_object* v_i_3439_, lean_object* v_b_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_){
_start:
{
size_t v_sz_boxed_3448_; size_t v_i_boxed_3449_; lean_object* v_res_3450_; 
v_sz_boxed_3448_ = lean_unbox_usize(v_sz_3438_);
lean_dec(v_sz_3438_);
v_i_boxed_3449_ = lean_unbox_usize(v_i_3439_);
lean_dec(v_i_3439_);
v_res_3450_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6(v_as_3437_, v_sz_boxed_3448_, v_i_boxed_3449_, v_b_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec_ref(v_as_3437_);
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0(lean_object* v_init_3451_, lean_object* v_n_3452_, lean_object* v_b_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
if (lean_obj_tag(v_n_3452_) == 0)
{
lean_object* v_cs_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; size_t v_sz_3464_; size_t v___x_3465_; lean_object* v___x_3466_; 
v_cs_3461_ = lean_ctor_get(v_n_3452_, 0);
v___x_3462_ = lean_box(0);
v___x_3463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3462_);
lean_ctor_set(v___x_3463_, 1, v_b_3453_);
v_sz_3464_ = lean_array_size(v_cs_3461_);
v___x_3465_ = ((size_t)0ULL);
v___x_3466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__5(v_init_3451_, v_cs_3461_, v_sz_3464_, v___x_3465_, v___x_3463_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3481_; 
v_a_3467_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3469_ = v___x_3466_;
v_isShared_3470_ = v_isSharedCheck_3481_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v___x_3466_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3481_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v_fst_3471_; 
v_fst_3471_ = lean_ctor_get(v_a_3467_, 0);
if (lean_obj_tag(v_fst_3471_) == 0)
{
lean_object* v_snd_3472_; lean_object* v___x_3473_; lean_object* v___x_3475_; 
v_snd_3472_ = lean_ctor_get(v_a_3467_, 1);
lean_inc(v_snd_3472_);
lean_dec(v_a_3467_);
v___x_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3473_, 0, v_snd_3472_);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 0, v___x_3473_);
v___x_3475_ = v___x_3469_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3473_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
else
{
lean_object* v_val_3477_; lean_object* v___x_3479_; 
lean_inc_ref(v_fst_3471_);
lean_dec(v_a_3467_);
v_val_3477_ = lean_ctor_get(v_fst_3471_, 0);
lean_inc(v_val_3477_);
lean_dec_ref_known(v_fst_3471_, 1);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 0, v_val_3477_);
v___x_3479_ = v___x_3469_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_val_3477_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
}
else
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
v_a_3482_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3484_ = v___x_3466_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3466_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3487_; 
if (v_isShared_3485_ == 0)
{
v___x_3487_ = v___x_3484_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3482_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
else
{
lean_object* v_vs_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; size_t v_sz_3493_; size_t v___x_3494_; lean_object* v___x_3495_; 
v_vs_3490_ = lean_ctor_get(v_n_3452_, 0);
v___x_3491_ = lean_box(0);
v___x_3492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3491_);
lean_ctor_set(v___x_3492_, 1, v_b_3453_);
v_sz_3493_ = lean_array_size(v_vs_3490_);
v___x_3494_ = ((size_t)0ULL);
v___x_3495_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6(v_vs_3490_, v_sz_3493_, v___x_3494_, v___x_3492_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3510_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3498_ = v___x_3495_;
v_isShared_3499_ = v_isSharedCheck_3510_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3495_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3510_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v_fst_3500_; 
v_fst_3500_ = lean_ctor_get(v_a_3496_, 0);
if (lean_obj_tag(v_fst_3500_) == 0)
{
lean_object* v_snd_3501_; lean_object* v___x_3502_; lean_object* v___x_3504_; 
v_snd_3501_ = lean_ctor_get(v_a_3496_, 1);
lean_inc(v_snd_3501_);
lean_dec(v_a_3496_);
v___x_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3502_, 0, v_snd_3501_);
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 0, v___x_3502_);
v___x_3504_ = v___x_3498_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3502_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
else
{
lean_object* v_val_3506_; lean_object* v___x_3508_; 
lean_inc_ref(v_fst_3500_);
lean_dec(v_a_3496_);
v_val_3506_ = lean_ctor_get(v_fst_3500_, 0);
lean_inc(v_val_3506_);
lean_dec_ref_known(v_fst_3500_, 1);
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 0, v_val_3506_);
v___x_3508_ = v___x_3498_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_val_3506_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
}
else
{
lean_object* v_a_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3518_; 
v_a_3511_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3513_ = v___x_3495_;
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_a_3511_);
lean_dec(v___x_3495_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3516_; 
if (v_isShared_3514_ == 0)
{
v___x_3516_ = v___x_3513_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_a_3511_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__5(lean_object* v_init_3519_, lean_object* v_as_3520_, size_t v_sz_3521_, size_t v_i_3522_, lean_object* v_b_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
uint8_t v___x_3531_; 
v___x_3531_ = lean_usize_dec_lt(v_i_3522_, v_sz_3521_);
if (v___x_3531_ == 0)
{
lean_object* v___x_3532_; 
v___x_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3532_, 0, v_b_3523_);
return v___x_3532_;
}
else
{
lean_object* v_snd_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3567_; 
v_snd_3533_ = lean_ctor_get(v_b_3523_, 1);
v_isSharedCheck_3567_ = !lean_is_exclusive(v_b_3523_);
if (v_isSharedCheck_3567_ == 0)
{
lean_object* v_unused_3568_; 
v_unused_3568_ = lean_ctor_get(v_b_3523_, 0);
lean_dec(v_unused_3568_);
v___x_3535_ = v_b_3523_;
v_isShared_3536_ = v_isSharedCheck_3567_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_snd_3533_);
lean_dec(v_b_3523_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3567_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3537_; lean_object* v_a_3538_; lean_object* v___x_3539_; 
v___x_3537_ = lean_box(0);
v_a_3538_ = lean_array_uget_borrowed(v_as_3520_, v_i_3522_);
lean_inc(v_snd_3533_);
v___x_3539_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0(v_init_3519_, v_a_3538_, v_snd_3533_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3558_; 
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3542_ = v___x_3539_;
v_isShared_3543_ = v_isSharedCheck_3558_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3539_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3558_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
if (lean_obj_tag(v_a_3540_) == 0)
{
lean_object* v___x_3544_; lean_object* v___x_3546_; 
v___x_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3544_, 0, v_a_3540_);
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 0, v___x_3544_);
v___x_3546_ = v___x_3535_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v___x_3544_);
lean_ctor_set(v_reuseFailAlloc_3550_, 1, v_snd_3533_);
v___x_3546_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
lean_object* v___x_3548_; 
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 0, v___x_3546_);
v___x_3548_ = v___x_3542_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v___x_3546_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
else
{
lean_object* v_a_3551_; lean_object* v___x_3553_; 
lean_del_object(v___x_3542_);
lean_dec(v_snd_3533_);
v_a_3551_ = lean_ctor_get(v_a_3540_, 0);
lean_inc(v_a_3551_);
lean_dec_ref_known(v_a_3540_, 1);
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 1, v_a_3551_);
lean_ctor_set(v___x_3535_, 0, v___x_3537_);
v___x_3553_ = v___x_3535_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3537_);
lean_ctor_set(v_reuseFailAlloc_3557_, 1, v_a_3551_);
v___x_3553_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
size_t v___x_3554_; size_t v___x_3555_; 
v___x_3554_ = ((size_t)1ULL);
v___x_3555_ = lean_usize_add(v_i_3522_, v___x_3554_);
v_i_3522_ = v___x_3555_;
v_b_3523_ = v___x_3553_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
lean_del_object(v___x_3535_);
lean_dec(v_snd_3533_);
v_a_3559_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_3539_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3539_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3564_; 
if (v_isShared_3562_ == 0)
{
v___x_3564_ = v___x_3561_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3559_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__5___boxed(lean_object* v_init_3569_, lean_object* v_as_3570_, lean_object* v_sz_3571_, lean_object* v_i_3572_, lean_object* v_b_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_){
_start:
{
size_t v_sz_boxed_3581_; size_t v_i_boxed_3582_; lean_object* v_res_3583_; 
v_sz_boxed_3581_ = lean_unbox_usize(v_sz_3571_);
lean_dec(v_sz_3571_);
v_i_boxed_3582_ = lean_unbox_usize(v_i_3572_);
lean_dec(v_i_3572_);
v_res_3583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__5(v_init_3569_, v_as_3570_, v_sz_boxed_3581_, v_i_boxed_3582_, v_b_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
lean_dec(v___y_3579_);
lean_dec_ref(v___y_3578_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
lean_dec_ref(v_as_3570_);
lean_dec_ref(v_init_3569_);
return v_res_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0___boxed(lean_object* v_init_3584_, lean_object* v_n_3585_, lean_object* v_b_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0(v_init_3584_, v_n_3585_, v_b_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec_ref(v_n_3585_);
lean_dec_ref(v_init_3584_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0(lean_object* v_t_3595_, lean_object* v_init_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_){
_start:
{
lean_object* v_root_3604_; lean_object* v_tail_3605_; lean_object* v___x_3606_; 
v_root_3604_ = lean_ctor_get(v_t_3595_, 0);
v_tail_3605_ = lean_ctor_get(v_t_3595_, 1);
lean_inc_ref(v_init_3596_);
v___x_3606_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0(v_init_3596_, v_root_3604_, v_init_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
lean_dec_ref(v_init_3596_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3643_; 
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3609_ = v___x_3606_;
v_isShared_3610_ = v_isSharedCheck_3643_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3606_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3643_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
if (lean_obj_tag(v_a_3607_) == 0)
{
lean_object* v_a_3611_; lean_object* v___x_3613_; 
v_a_3611_ = lean_ctor_get(v_a_3607_, 0);
lean_inc(v_a_3611_);
lean_dec_ref_known(v_a_3607_, 1);
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 0, v_a_3611_);
v___x_3613_ = v___x_3609_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_a_3611_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; size_t v_sz_3618_; size_t v___x_3619_; lean_object* v___x_3620_; 
lean_del_object(v___x_3609_);
v_a_3615_ = lean_ctor_get(v_a_3607_, 0);
lean_inc(v_a_3615_);
lean_dec_ref_known(v_a_3607_, 1);
v___x_3616_ = lean_box(0);
v___x_3617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3616_);
lean_ctor_set(v___x_3617_, 1, v_a_3615_);
v_sz_3618_ = lean_array_size(v_tail_3605_);
v___x_3619_ = ((size_t)0ULL);
v___x_3620_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1(v_tail_3605_, v_sz_3618_, v___x_3619_, v___x_3617_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3634_; 
v_a_3621_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3623_ = v___x_3620_;
v_isShared_3624_ = v_isSharedCheck_3634_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3620_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3634_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v_fst_3625_; 
v_fst_3625_ = lean_ctor_get(v_a_3621_, 0);
if (lean_obj_tag(v_fst_3625_) == 0)
{
lean_object* v_snd_3626_; lean_object* v___x_3628_; 
v_snd_3626_ = lean_ctor_get(v_a_3621_, 1);
lean_inc(v_snd_3626_);
lean_dec(v_a_3621_);
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 0, v_snd_3626_);
v___x_3628_ = v___x_3623_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_snd_3626_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
else
{
lean_object* v_val_3630_; lean_object* v___x_3632_; 
lean_inc_ref(v_fst_3625_);
lean_dec(v_a_3621_);
v_val_3630_ = lean_ctor_get(v_fst_3625_, 0);
lean_inc(v_val_3630_);
lean_dec_ref_known(v_fst_3625_, 1);
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 0, v_val_3630_);
v___x_3632_ = v___x_3623_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_val_3630_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
}
else
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
v_a_3635_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3637_ = v___x_3620_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3620_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
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
}
}
}
else
{
lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3651_; 
v_a_3644_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3646_ = v___x_3606_;
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v___x_3606_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3649_; 
if (v_isShared_3647_ == 0)
{
v___x_3649_ = v___x_3646_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3644_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0___boxed(lean_object* v_t_3652_, lean_object* v_init_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_){
_start:
{
lean_object* v_res_3661_; 
v_res_3661_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0(v_t_3652_, v_init_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_);
lean_dec(v___y_3659_);
lean_dec_ref(v___y_3658_);
lean_dec(v___y_3657_);
lean_dec_ref(v___y_3656_);
lean_dec(v___y_3655_);
lean_dec_ref(v___y_3654_);
lean_dec_ref(v_t_3652_);
return v_res_3661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__1(size_t v_sz_3662_, size_t v_i_3663_, lean_object* v_bs_3664_){
_start:
{
uint8_t v___x_3665_; 
v___x_3665_ = lean_usize_dec_lt(v_i_3663_, v_sz_3662_);
if (v___x_3665_ == 0)
{
return v_bs_3664_;
}
else
{
lean_object* v_v_3666_; lean_object* v___x_3667_; lean_object* v_bs_x27_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; size_t v___x_3671_; size_t v___x_3672_; lean_object* v___x_3673_; 
v_v_3666_ = lean_array_uget(v_bs_3664_, v_i_3663_);
v___x_3667_ = lean_unsigned_to_nat(0u);
v_bs_x27_3668_ = lean_array_uset(v_bs_3664_, v_i_3663_, v___x_3667_);
v___x_3669_ = l_Lean_LocalDecl_fvarId(v_v_3666_);
lean_dec(v_v_3666_);
v___x_3670_ = l_Lean_mkFVar(v___x_3669_);
v___x_3671_ = ((size_t)1ULL);
v___x_3672_ = lean_usize_add(v_i_3663_, v___x_3671_);
v___x_3673_ = lean_array_uset(v_bs_x27_3668_, v_i_3663_, v___x_3670_);
v_i_3663_ = v___x_3672_;
v_bs_3664_ = v___x_3673_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__1___boxed(lean_object* v_sz_3675_, lean_object* v_i_3676_, lean_object* v_bs_3677_){
_start:
{
size_t v_sz_boxed_3678_; size_t v_i_boxed_3679_; lean_object* v_res_3680_; 
v_sz_boxed_3678_ = lean_unbox_usize(v_sz_3675_);
lean_dec(v_sz_3675_);
v_i_boxed_3679_ = lean_unbox_usize(v_i_3676_);
lean_dec(v_i_3676_);
v_res_3680_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__1(v_sz_boxed_3678_, v_i_boxed_3679_, v_bs_3677_);
return v_res_3680_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3686_ = lean_box(0);
v___x_3687_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__1));
v___x_3688_ = l_Lean_Expr_const___override(v___x_3687_, v___x_3686_);
return v___x_3688_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6(void){
_start:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3694_ = lean_box(0);
v___x_3695_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__5));
v___x_3696_ = l_Lean_mkConst(v___x_3695_, v___x_3694_);
return v___x_3696_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; 
v___x_3701_ = lean_box(0);
v___x_3702_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__8));
v___x_3703_ = l_Lean_mkConst(v___x_3702_, v___x_3701_);
return v___x_3703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg(size_t v_sz_3704_, size_t v_i_3705_, lean_object* v_bs_3706_){
_start:
{
uint8_t v___x_3708_; 
v___x_3708_ = lean_usize_dec_lt(v_i_3705_, v_sz_3704_);
if (v___x_3708_ == 0)
{
lean_object* v___x_3709_; 
v___x_3709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3709_, 0, v_bs_3706_);
return v___x_3709_;
}
else
{
lean_object* v_v_3710_; lean_object* v_module_3711_; uint8_t v_importAll_3712_; uint8_t v_isExported_3713_; uint8_t v_isMeta_3714_; lean_object* v___x_3715_; lean_object* v_bs_x27_3716_; lean_object* v___x_3717_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3740_; 
v_v_3710_ = lean_array_uget_borrowed(v_bs_3706_, v_i_3705_);
v_module_3711_ = lean_ctor_get(v_v_3710_, 0);
lean_inc(v_module_3711_);
v_importAll_3712_ = lean_ctor_get_uint8(v_v_3710_, sizeof(void*)*1);
v_isExported_3713_ = lean_ctor_get_uint8(v_v_3710_, sizeof(void*)*1 + 1);
v_isMeta_3714_ = lean_ctor_get_uint8(v_v_3710_, sizeof(void*)*1 + 2);
v___x_3715_ = lean_unsigned_to_nat(0u);
v_bs_x27_3716_ = lean_array_uset(v_bs_3706_, v_i_3705_, v___x_3715_);
v___x_3717_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_module_3711_);
if (v_importAll_3712_ == 0)
{
lean_object* v___x_3743_; 
v___x_3743_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6);
v___y_3740_ = v___x_3743_;
goto v___jp_3739_;
}
else
{
lean_object* v___x_3744_; 
v___x_3744_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9);
v___y_3740_ = v___x_3744_;
goto v___jp_3739_;
}
v___jp_3718_:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; size_t v___x_3730_; size_t v___x_3731_; lean_object* v___x_3732_; 
v___x_3722_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__2);
v___x_3723_ = lean_unsigned_to_nat(4u);
v___x_3724_ = lean_mk_empty_array_with_capacity(v___x_3723_);
v___x_3725_ = lean_array_push(v___x_3724_, v___x_3717_);
lean_inc_ref(v___y_3719_);
v___x_3726_ = lean_array_push(v___x_3725_, v___y_3719_);
lean_inc_ref(v___y_3720_);
v___x_3727_ = lean_array_push(v___x_3726_, v___y_3720_);
lean_inc_ref(v___y_3721_);
v___x_3728_ = lean_array_push(v___x_3727_, v___y_3721_);
v___x_3729_ = l_Lean_mkAppN(v___x_3722_, v___x_3728_);
lean_dec_ref(v___x_3728_);
v___x_3730_ = ((size_t)1ULL);
v___x_3731_ = lean_usize_add(v_i_3705_, v___x_3730_);
v___x_3732_ = lean_array_uset(v_bs_x27_3716_, v_i_3705_, v___x_3729_);
v_i_3705_ = v___x_3731_;
v_bs_3706_ = v___x_3732_;
goto _start;
}
v___jp_3734_:
{
if (v_isMeta_3714_ == 0)
{
lean_object* v___x_3737_; 
v___x_3737_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6);
v___y_3719_ = v___y_3735_;
v___y_3720_ = v___y_3736_;
v___y_3721_ = v___x_3737_;
goto v___jp_3718_;
}
else
{
lean_object* v___x_3738_; 
v___x_3738_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9);
v___y_3719_ = v___y_3735_;
v___y_3720_ = v___y_3736_;
v___y_3721_ = v___x_3738_;
goto v___jp_3718_;
}
}
v___jp_3739_:
{
if (v_isExported_3713_ == 0)
{
lean_object* v___x_3741_; 
v___x_3741_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6);
v___y_3735_ = v___y_3740_;
v___y_3736_ = v___x_3741_;
goto v___jp_3734_;
}
else
{
lean_object* v___x_3742_; 
v___x_3742_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9);
v___y_3735_ = v___y_3740_;
v___y_3736_ = v___x_3742_;
goto v___jp_3734_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___boxed(lean_object* v_sz_3745_, lean_object* v_i_3746_, lean_object* v_bs_3747_, lean_object* v___y_3748_){
_start:
{
size_t v_sz_boxed_3749_; size_t v_i_boxed_3750_; lean_object* v_res_3751_; 
v_sz_boxed_3749_ = lean_unbox_usize(v_sz_3745_);
lean_dec(v_sz_3745_);
v_i_boxed_3750_ = lean_unbox_usize(v_i_3746_);
lean_dec(v_i_3746_);
v_res_3751_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg(v_sz_boxed_3749_, v_i_boxed_3750_, v_bs_3747_);
return v_res_3751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12_spec__20___redArg(lean_object* v_x_3752_, lean_object* v_x_3753_, lean_object* v_x_3754_, lean_object* v_x_3755_){
_start:
{
lean_object* v_ks_3756_; lean_object* v_vs_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3781_; 
v_ks_3756_ = lean_ctor_get(v_x_3752_, 0);
v_vs_3757_ = lean_ctor_get(v_x_3752_, 1);
v_isSharedCheck_3781_ = !lean_is_exclusive(v_x_3752_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3759_ = v_x_3752_;
v_isShared_3760_ = v_isSharedCheck_3781_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_vs_3757_);
lean_inc(v_ks_3756_);
lean_dec(v_x_3752_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3781_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3761_; uint8_t v___x_3762_; 
v___x_3761_ = lean_array_get_size(v_ks_3756_);
v___x_3762_ = lean_nat_dec_lt(v_x_3753_, v___x_3761_);
if (v___x_3762_ == 0)
{
lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3766_; 
lean_dec(v_x_3753_);
v___x_3763_ = lean_array_push(v_ks_3756_, v_x_3754_);
v___x_3764_ = lean_array_push(v_vs_3757_, v_x_3755_);
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 1, v___x_3764_);
lean_ctor_set(v___x_3759_, 0, v___x_3763_);
v___x_3766_ = v___x_3759_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v___x_3763_);
lean_ctor_set(v_reuseFailAlloc_3767_, 1, v___x_3764_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
else
{
lean_object* v_k_x27_3768_; uint8_t v___x_3769_; 
v_k_x27_3768_ = lean_array_fget_borrowed(v_ks_3756_, v_x_3753_);
v___x_3769_ = l_Lean_instBEqFVarId_beq(v_x_3754_, v_k_x27_3768_);
if (v___x_3769_ == 0)
{
lean_object* v___x_3771_; 
if (v_isShared_3760_ == 0)
{
v___x_3771_ = v___x_3759_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_ks_3756_);
lean_ctor_set(v_reuseFailAlloc_3775_, 1, v_vs_3757_);
v___x_3771_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3772_ = lean_unsigned_to_nat(1u);
v___x_3773_ = lean_nat_add(v_x_3753_, v___x_3772_);
lean_dec(v_x_3753_);
v_x_3752_ = v___x_3771_;
v_x_3753_ = v___x_3773_;
goto _start;
}
}
else
{
lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3779_; 
v___x_3776_ = lean_array_fset(v_ks_3756_, v_x_3753_, v_x_3754_);
v___x_3777_ = lean_array_fset(v_vs_3757_, v_x_3753_, v_x_3755_);
lean_dec(v_x_3753_);
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 1, v___x_3777_);
lean_ctor_set(v___x_3759_, 0, v___x_3776_);
v___x_3779_ = v___x_3759_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___x_3776_);
lean_ctor_set(v_reuseFailAlloc_3780_, 1, v___x_3777_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12___redArg(lean_object* v_n_3782_, lean_object* v_k_3783_, lean_object* v_v_3784_){
_start:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3785_ = lean_unsigned_to_nat(0u);
v___x_3786_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12_spec__20___redArg(v_n_3782_, v___x_3785_, v_k_3783_, v_v_3784_);
return v___x_3786_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_3787_; 
v___x_3787_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_3787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg(lean_object* v_x_3788_, size_t v_x_3789_, size_t v_x_3790_, lean_object* v_x_3791_, lean_object* v_x_3792_){
_start:
{
if (lean_obj_tag(v_x_3788_) == 0)
{
lean_object* v_es_3793_; size_t v___x_3794_; size_t v___x_3795_; lean_object* v_j_3796_; lean_object* v___x_3797_; uint8_t v___x_3798_; 
v_es_3793_ = lean_ctor_get(v_x_3788_, 0);
v___x_3794_ = ((size_t)31ULL);
v___x_3795_ = lean_usize_land(v_x_3789_, v___x_3794_);
v_j_3796_ = lean_usize_to_nat(v___x_3795_);
v___x_3797_ = lean_array_get_size(v_es_3793_);
v___x_3798_ = lean_nat_dec_lt(v_j_3796_, v___x_3797_);
if (v___x_3798_ == 0)
{
lean_dec(v_j_3796_);
lean_dec(v_x_3792_);
lean_dec(v_x_3791_);
return v_x_3788_;
}
else
{
lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3837_; 
lean_inc_ref(v_es_3793_);
v_isSharedCheck_3837_ = !lean_is_exclusive(v_x_3788_);
if (v_isSharedCheck_3837_ == 0)
{
lean_object* v_unused_3838_; 
v_unused_3838_ = lean_ctor_get(v_x_3788_, 0);
lean_dec(v_unused_3838_);
v___x_3800_ = v_x_3788_;
v_isShared_3801_ = v_isSharedCheck_3837_;
goto v_resetjp_3799_;
}
else
{
lean_dec(v_x_3788_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3837_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v_v_3802_; lean_object* v___x_3803_; lean_object* v_xs_x27_3804_; lean_object* v___y_3806_; 
v_v_3802_ = lean_array_fget(v_es_3793_, v_j_3796_);
v___x_3803_ = lean_box(0);
v_xs_x27_3804_ = lean_array_fset(v_es_3793_, v_j_3796_, v___x_3803_);
switch(lean_obj_tag(v_v_3802_))
{
case 0:
{
lean_object* v_key_3811_; lean_object* v_val_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3822_; 
v_key_3811_ = lean_ctor_get(v_v_3802_, 0);
v_val_3812_ = lean_ctor_get(v_v_3802_, 1);
v_isSharedCheck_3822_ = !lean_is_exclusive(v_v_3802_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3814_ = v_v_3802_;
v_isShared_3815_ = v_isSharedCheck_3822_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_val_3812_);
lean_inc(v_key_3811_);
lean_dec(v_v_3802_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3822_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
uint8_t v___x_3816_; 
v___x_3816_ = l_Lean_instBEqFVarId_beq(v_x_3791_, v_key_3811_);
if (v___x_3816_ == 0)
{
lean_object* v___x_3817_; lean_object* v___x_3818_; 
lean_del_object(v___x_3814_);
v___x_3817_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3811_, v_val_3812_, v_x_3791_, v_x_3792_);
v___x_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3817_);
v___y_3806_ = v___x_3818_;
goto v___jp_3805_;
}
else
{
lean_object* v___x_3820_; 
lean_dec(v_val_3812_);
lean_dec(v_key_3811_);
if (v_isShared_3815_ == 0)
{
lean_ctor_set(v___x_3814_, 1, v_x_3792_);
lean_ctor_set(v___x_3814_, 0, v_x_3791_);
v___x_3820_ = v___x_3814_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_x_3791_);
lean_ctor_set(v_reuseFailAlloc_3821_, 1, v_x_3792_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
v___y_3806_ = v___x_3820_;
goto v___jp_3805_;
}
}
}
}
case 1:
{
lean_object* v_node_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3835_; 
v_node_3823_ = lean_ctor_get(v_v_3802_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v_v_3802_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3825_ = v_v_3802_;
v_isShared_3826_ = v_isSharedCheck_3835_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_node_3823_);
lean_dec(v_v_3802_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3835_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
size_t v___x_3827_; size_t v___x_3828_; size_t v___x_3829_; size_t v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3833_; 
v___x_3827_ = ((size_t)5ULL);
v___x_3828_ = lean_usize_shift_right(v_x_3789_, v___x_3827_);
v___x_3829_ = ((size_t)1ULL);
v___x_3830_ = lean_usize_add(v_x_3790_, v___x_3829_);
v___x_3831_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg(v_node_3823_, v___x_3828_, v___x_3830_, v_x_3791_, v_x_3792_);
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 0, v___x_3831_);
v___x_3833_ = v___x_3825_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3831_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
v___y_3806_ = v___x_3833_;
goto v___jp_3805_;
}
}
}
default: 
{
lean_object* v___x_3836_; 
v___x_3836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3836_, 0, v_x_3791_);
lean_ctor_set(v___x_3836_, 1, v_x_3792_);
v___y_3806_ = v___x_3836_;
goto v___jp_3805_;
}
}
v___jp_3805_:
{
lean_object* v___x_3807_; lean_object* v___x_3809_; 
v___x_3807_ = lean_array_fset(v_xs_x27_3804_, v_j_3796_, v___y_3806_);
lean_dec(v_j_3796_);
if (v_isShared_3801_ == 0)
{
lean_ctor_set(v___x_3800_, 0, v___x_3807_);
v___x_3809_ = v___x_3800_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v___x_3807_);
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
}
else
{
lean_object* v_ks_3839_; lean_object* v_vs_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3858_; 
v_ks_3839_ = lean_ctor_get(v_x_3788_, 0);
v_vs_3840_ = lean_ctor_get(v_x_3788_, 1);
v_isSharedCheck_3858_ = !lean_is_exclusive(v_x_3788_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3842_ = v_x_3788_;
v_isShared_3843_ = v_isSharedCheck_3858_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_vs_3840_);
lean_inc(v_ks_3839_);
lean_dec(v_x_3788_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3858_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3845_; 
if (v_isShared_3843_ == 0)
{
v___x_3845_ = v___x_3842_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_ks_3839_);
lean_ctor_set(v_reuseFailAlloc_3857_, 1, v_vs_3840_);
v___x_3845_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
lean_object* v_newNode_3846_; size_t v___x_3847_; uint8_t v___x_3848_; 
v_newNode_3846_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12___redArg(v___x_3845_, v_x_3791_, v_x_3792_);
v___x_3847_ = ((size_t)7ULL);
v___x_3848_ = lean_usize_dec_le(v___x_3847_, v_x_3790_);
if (v___x_3848_ == 0)
{
lean_object* v___x_3849_; lean_object* v___x_3850_; uint8_t v___x_3851_; 
v___x_3849_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3846_);
v___x_3850_ = lean_unsigned_to_nat(4u);
v___x_3851_ = lean_nat_dec_lt(v___x_3849_, v___x_3850_);
lean_dec(v___x_3849_);
if (v___x_3851_ == 0)
{
lean_object* v_ks_3852_; lean_object* v_vs_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; 
v_ks_3852_ = lean_ctor_get(v_newNode_3846_, 0);
lean_inc_ref(v_ks_3852_);
v_vs_3853_ = lean_ctor_get(v_newNode_3846_, 1);
lean_inc_ref(v_vs_3853_);
lean_dec_ref(v_newNode_3846_);
v___x_3854_ = lean_unsigned_to_nat(0u);
v___x_3855_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg___closed__0);
v___x_3856_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___redArg(v_x_3790_, v_ks_3852_, v_vs_3853_, v___x_3854_, v___x_3855_);
lean_dec_ref(v_vs_3853_);
lean_dec_ref(v_ks_3852_);
return v___x_3856_;
}
else
{
return v_newNode_3846_;
}
}
else
{
return v_newNode_3846_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___redArg(size_t v_depth_3859_, lean_object* v_keys_3860_, lean_object* v_vals_3861_, lean_object* v_i_3862_, lean_object* v_entries_3863_){
_start:
{
lean_object* v___x_3864_; uint8_t v___x_3865_; 
v___x_3864_ = lean_array_get_size(v_keys_3860_);
v___x_3865_ = lean_nat_dec_lt(v_i_3862_, v___x_3864_);
if (v___x_3865_ == 0)
{
lean_dec(v_i_3862_);
return v_entries_3863_;
}
else
{
lean_object* v_k_3866_; lean_object* v_v_3867_; uint64_t v___x_3868_; size_t v_h_3869_; size_t v___x_3870_; lean_object* v___x_3871_; size_t v___x_3872_; size_t v___x_3873_; size_t v___x_3874_; size_t v_h_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
v_k_3866_ = lean_array_fget_borrowed(v_keys_3860_, v_i_3862_);
v_v_3867_ = lean_array_fget_borrowed(v_vals_3861_, v_i_3862_);
v___x_3868_ = l_Lean_instHashableFVarId_hash(v_k_3866_);
v_h_3869_ = lean_uint64_to_usize(v___x_3868_);
v___x_3870_ = ((size_t)5ULL);
v___x_3871_ = lean_unsigned_to_nat(1u);
v___x_3872_ = ((size_t)1ULL);
v___x_3873_ = lean_usize_sub(v_depth_3859_, v___x_3872_);
v___x_3874_ = lean_usize_mul(v___x_3870_, v___x_3873_);
v_h_3875_ = lean_usize_shift_right(v_h_3869_, v___x_3874_);
v___x_3876_ = lean_nat_add(v_i_3862_, v___x_3871_);
lean_dec(v_i_3862_);
lean_inc(v_v_3867_);
lean_inc(v_k_3866_);
v___x_3877_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg(v_entries_3863_, v_h_3875_, v_depth_3859_, v_k_3866_, v_v_3867_);
v_i_3862_ = v___x_3876_;
v_entries_3863_ = v___x_3877_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___redArg___boxed(lean_object* v_depth_3879_, lean_object* v_keys_3880_, lean_object* v_vals_3881_, lean_object* v_i_3882_, lean_object* v_entries_3883_){
_start:
{
size_t v_depth_boxed_3884_; lean_object* v_res_3885_; 
v_depth_boxed_3884_ = lean_unbox_usize(v_depth_3879_);
lean_dec(v_depth_3879_);
v_res_3885_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___redArg(v_depth_boxed_3884_, v_keys_3880_, v_vals_3881_, v_i_3882_, v_entries_3883_);
lean_dec_ref(v_vals_3881_);
lean_dec_ref(v_keys_3880_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg___boxed(lean_object* v_x_3886_, lean_object* v_x_3887_, lean_object* v_x_3888_, lean_object* v_x_3889_, lean_object* v_x_3890_){
_start:
{
size_t v_x_35207__boxed_3891_; size_t v_x_35208__boxed_3892_; lean_object* v_res_3893_; 
v_x_35207__boxed_3891_ = lean_unbox_usize(v_x_3887_);
lean_dec(v_x_3887_);
v_x_35208__boxed_3892_ = lean_unbox_usize(v_x_3888_);
lean_dec(v_x_3888_);
v_res_3893_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg(v_x_3886_, v_x_35207__boxed_3891_, v_x_35208__boxed_3892_, v_x_3889_, v_x_3890_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2___redArg(lean_object* v_x_3894_, lean_object* v_x_3895_, lean_object* v_x_3896_){
_start:
{
uint64_t v___x_3897_; size_t v___x_3898_; size_t v___x_3899_; lean_object* v___x_3900_; 
v___x_3897_ = l_Lean_instHashableFVarId_hash(v_x_3895_);
v___x_3898_ = lean_uint64_to_usize(v___x_3897_);
v___x_3899_ = ((size_t)1ULL);
v___x_3900_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg(v_x_3894_, v___x_3898_, v___x_3899_, v_x_3895_, v_x_3896_);
return v___x_3900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__11(lean_object* v_as_3901_, size_t v_i_3902_, size_t v_stop_3903_, lean_object* v_b_3904_){
_start:
{
lean_object* v___y_3906_; uint8_t v___x_3910_; 
v___x_3910_ = lean_usize_dec_eq(v_i_3902_, v_stop_3903_);
if (v___x_3910_ == 0)
{
lean_object* v_fvarIdToDecl_3911_; lean_object* v_decls_3912_; lean_object* v_auxDeclToFullName_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v_fvarIdToDecl_3911_ = lean_ctor_get(v_b_3904_, 0);
v_decls_3912_ = lean_ctor_get(v_b_3904_, 1);
v_auxDeclToFullName_3913_ = lean_ctor_get(v_b_3904_, 2);
v___x_3914_ = lean_array_uget_borrowed(v_as_3901_, v_i_3902_);
v___x_3915_ = l_Lean_LocalDecl_fvarId(v___x_3914_);
lean_inc_ref(v_b_3904_);
v___x_3916_ = lean_local_ctx_find(v_b_3904_, v___x_3915_);
if (lean_obj_tag(v___x_3916_) == 0)
{
v___y_3906_ = v_b_3904_;
goto v___jp_3905_;
}
else
{
lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3942_; 
lean_inc(v_auxDeclToFullName_3913_);
lean_inc_ref(v_decls_3912_);
lean_inc_ref(v_fvarIdToDecl_3911_);
v_isSharedCheck_3942_ = !lean_is_exclusive(v_b_3904_);
if (v_isSharedCheck_3942_ == 0)
{
lean_object* v_unused_3943_; lean_object* v_unused_3944_; lean_object* v_unused_3945_; 
v_unused_3943_ = lean_ctor_get(v_b_3904_, 2);
lean_dec(v_unused_3943_);
v_unused_3944_ = lean_ctor_get(v_b_3904_, 1);
lean_dec(v_unused_3944_);
v_unused_3945_ = lean_ctor_get(v_b_3904_, 0);
lean_dec(v_unused_3945_);
v___x_3918_ = v_b_3904_;
v_isShared_3919_ = v_isSharedCheck_3942_;
goto v_resetjp_3917_;
}
else
{
lean_dec(v_b_3904_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3942_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v_val_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3941_; 
v_val_3920_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3922_ = v___x_3916_;
v_isShared_3923_ = v_isSharedCheck_3941_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_val_3920_);
lean_dec(v___x_3916_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3941_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
uint8_t v___x_3924_; lean_object* v___x_3925_; lean_object* v___y_3927_; lean_object* v___y_3928_; lean_object* v___y_3937_; lean_object* v_fvarId_3940_; 
v___x_3924_ = 1;
v___x_3925_ = l_Lean_LocalDecl_setNondep(v_val_3920_, v___x_3924_);
v_fvarId_3940_ = lean_ctor_get(v___x_3925_, 1);
lean_inc(v_fvarId_3940_);
v___y_3937_ = v_fvarId_3940_;
goto v___jp_3936_;
v___jp_3926_:
{
lean_object* v___x_3930_; 
if (v_isShared_3923_ == 0)
{
lean_ctor_set(v___x_3922_, 0, v___x_3925_);
v___x_3930_ = v___x_3922_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3925_);
v___x_3930_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
lean_object* v___x_3931_; lean_object* v___x_3933_; 
v___x_3931_ = l_Lean_PersistentArray_set___redArg(v_decls_3912_, v___y_3928_, v___x_3930_);
lean_dec(v___y_3928_);
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 1, v___x_3931_);
lean_ctor_set(v___x_3918_, 0, v___y_3927_);
v___x_3933_ = v___x_3918_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___y_3927_);
lean_ctor_set(v_reuseFailAlloc_3934_, 1, v___x_3931_);
lean_ctor_set(v_reuseFailAlloc_3934_, 2, v_auxDeclToFullName_3913_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
v___y_3906_ = v___x_3933_;
goto v___jp_3905_;
}
}
}
v___jp_3936_:
{
lean_object* v___x_3938_; lean_object* v_index_3939_; 
lean_inc_ref(v___x_3925_);
v___x_3938_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2___redArg(v_fvarIdToDecl_3911_, v___y_3937_, v___x_3925_);
v_index_3939_ = lean_ctor_get(v___x_3925_, 0);
lean_inc(v_index_3939_);
v___y_3927_ = v___x_3938_;
v___y_3928_ = v_index_3939_;
goto v___jp_3926_;
}
}
}
}
}
else
{
return v_b_3904_;
}
v___jp_3905_:
{
size_t v___x_3907_; size_t v___x_3908_; 
v___x_3907_ = ((size_t)1ULL);
v___x_3908_ = lean_usize_add(v_i_3902_, v___x_3907_);
v_i_3902_ = v___x_3908_;
v_b_3904_ = v___y_3906_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__11___boxed(lean_object* v_as_3946_, lean_object* v_i_3947_, lean_object* v_stop_3948_, lean_object* v_b_3949_){
_start:
{
size_t v_i_boxed_3950_; size_t v_stop_boxed_3951_; lean_object* v_res_3952_; 
v_i_boxed_3950_ = lean_unbox_usize(v_i_3947_);
lean_dec(v_i_3947_);
v_stop_boxed_3951_ = lean_unbox_usize(v_stop_3948_);
lean_dec(v_stop_3948_);
v_res_3952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__11(v_as_3946_, v_i_boxed_3950_, v_stop_boxed_3951_, v_b_3949_);
lean_dec_ref(v_as_3946_);
return v_res_3952_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__15(lean_object* v_msgData_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
lean_object* v___x_3959_; lean_object* v_env_3960_; lean_object* v___x_3961_; lean_object* v_toCold_3962_; lean_object* v_mctx_3963_; lean_object* v_lctx_3964_; lean_object* v_options_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3959_ = lean_st_ref_get(v___y_3957_);
v_env_3960_ = lean_ctor_get(v___x_3959_, 0);
lean_inc_ref(v_env_3960_);
lean_dec(v___x_3959_);
v___x_3961_ = lean_st_ref_get(v___y_3955_);
v_toCold_3962_ = lean_ctor_get(v___y_3956_, 0);
v_mctx_3963_ = lean_ctor_get(v___x_3961_, 0);
lean_inc_ref(v_mctx_3963_);
lean_dec(v___x_3961_);
v_lctx_3964_ = lean_ctor_get(v___y_3954_, 2);
v_options_3965_ = lean_ctor_get(v_toCold_3962_, 2);
lean_inc_ref(v_options_3965_);
lean_inc_ref(v_lctx_3964_);
v___x_3966_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3966_, 0, v_env_3960_);
lean_ctor_set(v___x_3966_, 1, v_mctx_3963_);
lean_ctor_set(v___x_3966_, 2, v_lctx_3964_);
lean_ctor_set(v___x_3966_, 3, v_options_3965_);
v___x_3967_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3966_);
lean_ctor_set(v___x_3967_, 1, v_msgData_3953_);
v___x_3968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3967_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__15___boxed(lean_object* v_msgData_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_){
_start:
{
lean_object* v_res_3975_; 
v_res_3975_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__15(v_msgData_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3970_);
return v_res_3975_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0(void){
_start:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; 
v___x_3976_ = lean_box(1);
v___x_3977_ = l_Lean_MessageData_ofFormat(v___x_3976_);
return v___x_3977_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__3(void){
_start:
{
lean_object* v___x_3981_; lean_object* v___x_3982_; 
v___x_3981_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__2));
v___x_3982_ = l_Lean_MessageData_ofFormat(v___x_3981_);
return v___x_3982_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23(lean_object* v_x_3983_, lean_object* v_x_3984_){
_start:
{
if (lean_obj_tag(v_x_3984_) == 0)
{
return v_x_3983_;
}
else
{
lean_object* v_head_3985_; lean_object* v_tail_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_4008_; 
v_head_3985_ = lean_ctor_get(v_x_3984_, 0);
v_tail_3986_ = lean_ctor_get(v_x_3984_, 1);
v_isSharedCheck_4008_ = !lean_is_exclusive(v_x_3984_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_3988_ = v_x_3984_;
v_isShared_3989_ = v_isSharedCheck_4008_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_tail_3986_);
lean_inc(v_head_3985_);
lean_dec(v_x_3984_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_4008_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v_before_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_4006_; 
v_before_3990_ = lean_ctor_get(v_head_3985_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v_head_3985_);
if (v_isSharedCheck_4006_ == 0)
{
lean_object* v_unused_4007_; 
v_unused_4007_ = lean_ctor_get(v_head_3985_, 1);
lean_dec(v_unused_4007_);
v___x_3992_ = v_head_3985_;
v_isShared_3993_ = v_isSharedCheck_4006_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_before_3990_);
lean_dec(v_head_3985_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_4006_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3994_; lean_object* v___x_3996_; 
v___x_3994_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0);
if (v_isShared_3993_ == 0)
{
lean_ctor_set_tag(v___x_3992_, 7);
lean_ctor_set(v___x_3992_, 1, v___x_3994_);
lean_ctor_set(v___x_3992_, 0, v_x_3983_);
v___x_3996_ = v___x_3992_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_x_3983_);
lean_ctor_set(v_reuseFailAlloc_4005_, 1, v___x_3994_);
v___x_3996_ = v_reuseFailAlloc_4005_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
lean_object* v___x_3997_; lean_object* v___x_3999_; 
v___x_3997_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__3);
if (v_isShared_3989_ == 0)
{
lean_ctor_set_tag(v___x_3988_, 7);
lean_ctor_set(v___x_3988_, 1, v___x_3997_);
lean_ctor_set(v___x_3988_, 0, v___x_3996_);
v___x_3999_ = v___x_3988_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v___x_3996_);
lean_ctor_set(v_reuseFailAlloc_4004_, 1, v___x_3997_);
v___x_3999_ = v_reuseFailAlloc_4004_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_4000_ = l_Lean_MessageData_ofSyntax(v_before_3990_);
v___x_4001_ = l_Lean_indentD(v___x_4000_);
v___x_4002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4002_, 0, v___x_3999_);
lean_ctor_set(v___x_4002_, 1, v___x_4001_);
v_x_3983_ = v___x_4002_;
v_x_3984_ = v_tail_3986_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__2(void){
_start:
{
lean_object* v___x_4012_; lean_object* v___x_4013_; 
v___x_4012_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__1));
v___x_4013_ = l_Lean_MessageData_ofFormat(v___x_4012_);
return v___x_4013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg(lean_object* v_msgData_4014_, lean_object* v_macroStack_4015_, lean_object* v___y_4016_){
_start:
{
lean_object* v___x_4018_; lean_object* v___x_4019_; uint8_t v___x_4020_; 
v___x_4018_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4016_);
v___x_4019_ = l_Lean_Elab_pp_macroStack;
v___x_4020_ = l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8(v___x_4018_, v___x_4019_);
lean_dec_ref(v___x_4018_);
if (v___x_4020_ == 0)
{
lean_object* v___x_4021_; 
lean_dec(v_macroStack_4015_);
v___x_4021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4021_, 0, v_msgData_4014_);
return v___x_4021_;
}
else
{
if (lean_obj_tag(v_macroStack_4015_) == 0)
{
lean_object* v___x_4022_; 
v___x_4022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4022_, 0, v_msgData_4014_);
return v___x_4022_;
}
else
{
lean_object* v_head_4023_; lean_object* v_after_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4039_; 
v_head_4023_ = lean_ctor_get(v_macroStack_4015_, 0);
lean_inc(v_head_4023_);
v_after_4024_ = lean_ctor_get(v_head_4023_, 1);
v_isSharedCheck_4039_ = !lean_is_exclusive(v_head_4023_);
if (v_isSharedCheck_4039_ == 0)
{
lean_object* v_unused_4040_; 
v_unused_4040_ = lean_ctor_get(v_head_4023_, 0);
lean_dec(v_unused_4040_);
v___x_4026_ = v_head_4023_;
v_isShared_4027_ = v_isSharedCheck_4039_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_after_4024_);
lean_dec(v_head_4023_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4039_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v___x_4028_; lean_object* v___x_4030_; 
v___x_4028_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0);
if (v_isShared_4027_ == 0)
{
lean_ctor_set_tag(v___x_4026_, 7);
lean_ctor_set(v___x_4026_, 1, v___x_4028_);
lean_ctor_set(v___x_4026_, 0, v_msgData_4014_);
v___x_4030_ = v___x_4026_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v_msgData_4014_);
lean_ctor_set(v_reuseFailAlloc_4038_, 1, v___x_4028_);
v___x_4030_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v_msgData_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; 
v___x_4031_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__2);
v___x_4032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4030_);
lean_ctor_set(v___x_4032_, 1, v___x_4031_);
v___x_4033_ = l_Lean_MessageData_ofSyntax(v_after_4024_);
v___x_4034_ = l_Lean_indentD(v___x_4033_);
v_msgData_4035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_4035_, 0, v___x_4032_);
lean_ctor_set(v_msgData_4035_, 1, v___x_4034_);
v___x_4036_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23(v_msgData_4035_, v_macroStack_4015_);
v___x_4037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4037_, 0, v___x_4036_);
return v___x_4037_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___boxed(lean_object* v_msgData_4041_, lean_object* v_macroStack_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_){
_start:
{
lean_object* v_res_4045_; 
v_res_4045_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg(v_msgData_4041_, v_macroStack_4042_, v___y_4043_);
lean_dec_ref(v___y_4043_);
return v_res_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg(lean_object* v_msg_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
lean_object* v_ref_4054_; lean_object* v_macroStack_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v_a_4058_; lean_object* v___x_4059_; lean_object* v_a_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4068_; 
v_ref_4054_ = lean_ctor_get(v___y_4051_, 2);
v_macroStack_4055_ = lean_ctor_get(v___y_4047_, 1);
v___x_4056_ = l_Lean_Elab_getBetterRef(v_ref_4054_, v_macroStack_4055_);
v___x_4057_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__15(v_msg_4046_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
v_a_4058_ = lean_ctor_get(v___x_4057_, 0);
lean_inc(v_a_4058_);
lean_dec_ref(v___x_4057_);
lean_inc(v_macroStack_4055_);
v___x_4059_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg(v_a_4058_, v_macroStack_4055_, v___y_4051_);
v_a_4060_ = lean_ctor_get(v___x_4059_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4059_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4062_ = v___x_4059_;
v_isShared_4063_ = v_isSharedCheck_4068_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_a_4060_);
lean_dec(v___x_4059_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4068_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
lean_object* v___x_4064_; lean_object* v___x_4066_; 
v___x_4064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4064_, 0, v___x_4056_);
lean_ctor_set(v___x_4064_, 1, v_a_4060_);
if (v_isShared_4063_ == 0)
{
lean_ctor_set_tag(v___x_4062_, 1);
lean_ctor_set(v___x_4062_, 0, v___x_4064_);
v___x_4066_ = v___x_4062_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v___x_4064_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg___boxed(lean_object* v_msg_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_){
_start:
{
lean_object* v_res_4077_; 
v_res_4077_ = l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg(v_msg_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_);
lean_dec(v___y_4075_);
lean_dec_ref(v___y_4074_);
lean_dec(v___y_4073_);
lean_dec_ref(v___y_4072_);
lean_dec(v___y_4071_);
lean_dec_ref(v___y_4070_);
return v_res_4077_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__5(void){
_start:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4086_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__0));
v___x_4087_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__4));
v___x_4088_ = l_Lean_Expr_const___override(v___x_4087_, v___x_4086_);
return v___x_4088_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__8(void){
_start:
{
lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4093_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__0));
v___x_4094_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__7));
v___x_4095_ = l_Lean_Expr_const___override(v___x_4094_, v___x_4093_);
return v___x_4095_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__9(void){
_start:
{
lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4096_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4);
v___x_4097_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__8, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__8_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__8);
v___x_4098_ = l_Lean_Expr_app___override(v___x_4097_, v___x_4096_);
return v___x_4098_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__14(void){
_start:
{
lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4108_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__13));
v___x_4109_ = l_String_toRawSubstring_x27(v___x_4108_);
return v___x_4109_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__29(void){
_start:
{
lean_object* v___x_4144_; 
v___x_4144_ = l_Array_mkArray0___redArg();
return v___x_4144_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__33(void){
_start:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; 
v___x_4148_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__32));
v___x_4149_ = l_Lean_stringToMessageData(v___x_4148_);
return v___x_4149_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__35(void){
_start:
{
lean_object* v___x_4151_; lean_object* v___x_4152_; 
v___x_4151_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__34));
v___x_4152_ = l_Lean_stringToMessageData(v___x_4151_);
return v___x_4152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore(lean_object* v_e_4163_, lean_object* v_body_4164_, lean_object* v_ref_4165_, lean_object* v_expectedType_x3f_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_){
_start:
{
lean_object* v_toCold_4174_; lean_object* v_ref_4175_; lean_object* v_fileName_4176_; lean_object* v___x_4177_; 
v_toCold_4174_ = lean_ctor_get(v_a_4171_, 0);
v_ref_4175_ = lean_ctor_get(v_a_4171_, 2);
v_fileName_4176_ = lean_ctor_get(v_toCold_4174_, 0);
lean_inc_ref(v_fileName_4176_);
v___x_4177_ = lean_io_realpath(v_fileName_4176_);
if (lean_obj_tag(v___x_4177_) == 0)
{
lean_object* v_a_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; uint8_t v___x_4181_; lean_object* v___y_4183_; lean_object* v___y_4184_; uint8_t v___y_4185_; lean_object* v___y_4186_; size_t v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; uint8_t v___y_4286_; lean_object* v___y_4287_; size_t v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; uint8_t v___y_4354_; lean_object* v___y_4355_; size_t v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; uint8_t v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v___y_4382_; uint8_t v___y_4383_; size_t v___y_4384_; lean_object* v___y_4385_; lean_object* v___y_4419_; lean_object* v___x_4485_; 
v_a_4178_ = lean_ctor_get(v___x_4177_, 0);
lean_inc(v_a_4178_);
lean_dec_ref_known(v___x_4177_, 1);
v___x_4179_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__0));
v___x_4180_ = lean_string_append(v_a_4178_, v___x_4179_);
v___x_4181_ = 0;
v___x_4485_ = l_Lean_Syntax_getPos_x3f(v_ref_4165_, v___x_4181_);
if (lean_obj_tag(v___x_4485_) == 0)
{
lean_object* v___x_4486_; 
v___x_4486_ = lean_unsigned_to_nat(0u);
v___y_4419_ = v___x_4486_;
goto v___jp_4418_;
}
else
{
lean_object* v_val_4487_; 
v_val_4487_ = lean_ctor_get(v___x_4485_, 0);
lean_inc(v_val_4487_);
lean_dec_ref_known(v___x_4485_, 1);
v___y_4419_ = v_val_4487_;
goto v___jp_4418_;
}
v___jp_4182_:
{
lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; uint8_t v___x_4197_; uint8_t v___x_4198_; lean_object* v___x_4199_; 
v___x_4194_ = lean_box(2);
v___x_4195_ = l_Lean_Syntax_mkStrLit(v___y_4184_, v___x_4194_);
v___x_4196_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__2));
v___x_4197_ = 0;
v___x_4198_ = 0;
v___x_4199_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg(v___x_4196_, v___x_4197_, v___y_4183_, v___y_4186_, v___x_4198_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
if (lean_obj_tag(v___x_4199_) == 0)
{
lean_object* v_a_4200_; lean_object* v___x_4201_; 
v_a_4200_ = lean_ctor_get(v___x_4199_, 0);
lean_inc(v_a_4200_);
lean_dec_ref_known(v___x_4199_, 1);
v___x_4201_ = l_Lean_Elab_Term_exprToSyntax(v_a_4200_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
if (lean_obj_tag(v___x_4201_) == 0)
{
lean_object* v_a_4202_; lean_object* v___x_4203_; lean_object* v_env_4204_; lean_object* v___x_4205_; lean_object* v_env_4206_; lean_object* v___x_4207_; lean_object* v_imports_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; size_t v_sz_4212_; lean_object* v___x_4213_; 
v_a_4202_ = lean_ctor_get(v___x_4201_, 0);
lean_inc(v_a_4202_);
lean_dec_ref_known(v___x_4201_, 1);
v___x_4203_ = lean_st_ref_get(v___y_4193_);
v_env_4204_ = lean_ctor_get(v___x_4203_, 0);
lean_inc_ref(v_env_4204_);
lean_dec(v___x_4203_);
v___x_4205_ = lean_st_ref_get(v___y_4193_);
v_env_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc_ref(v_env_4206_);
lean_dec(v___x_4205_);
v___x_4207_ = l_Lean_Environment_header(v_env_4204_);
lean_dec_ref(v_env_4204_);
v_imports_4208_ = lean_ctor_get(v___x_4207_, 1);
lean_inc_ref(v_imports_4208_);
lean_dec_ref(v___x_4207_);
v___x_4209_ = l_Lean_Environment_mainModule(v_env_4206_);
lean_dec_ref(v_env_4206_);
v___x_4210_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_4210_, 0, v___x_4209_);
lean_ctor_set_uint8(v___x_4210_, sizeof(void*)*1, v___x_4181_);
lean_ctor_set_uint8(v___x_4210_, sizeof(void*)*1 + 1, v___y_4185_);
lean_ctor_set_uint8(v___x_4210_, sizeof(void*)*1 + 2, v___x_4181_);
v___x_4211_ = lean_array_push(v_imports_4208_, v___x_4210_);
v_sz_4212_ = lean_array_size(v___x_4211_);
v___x_4213_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg(v_sz_4212_, v___y_4187_, v___x_4211_);
if (lean_obj_tag(v___x_4213_) == 0)
{
lean_object* v_a_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; 
v_a_4214_ = lean_ctor_get(v___x_4213_, 0);
lean_inc(v_a_4214_);
lean_dec_ref_known(v___x_4213_, 1);
v___x_4215_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__5, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__5_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__5);
v___x_4216_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4);
v___x_4217_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__9, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__9_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__9);
v___x_4218_ = lean_array_to_list(v_a_4214_);
v___x_4219_ = l_List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7(v___x_4217_, v___x_4218_);
v___x_4220_ = l_Lean_mkAppB(v___x_4215_, v___x_4216_, v___x_4219_);
v___x_4221_ = l_Lean_Elab_Term_exprToSyntax(v___x_4220_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
if (lean_obj_tag(v___x_4221_) == 0)
{
lean_object* v_toCold_4222_; lean_object* v_a_4223_; lean_object* v_ref_4224_; lean_object* v_quotContext_4225_; lean_object* v_currMacroScope_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; 
v_toCold_4222_ = lean_ctor_get(v___y_4192_, 0);
v_a_4223_ = lean_ctor_get(v___x_4221_, 0);
lean_inc(v_a_4223_);
lean_dec_ref_known(v___x_4221_, 1);
v_ref_4224_ = lean_ctor_get(v___y_4192_, 2);
v_quotContext_4225_ = lean_ctor_get(v_toCold_4222_, 8);
v_currMacroScope_4226_ = lean_ctor_get(v_toCold_4222_, 9);
v___x_4227_ = l_Lean_SourceInfo_fromRef(v_ref_4224_, v___x_4181_);
v___x_4228_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__11));
v___x_4229_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__12));
v___x_4230_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__14, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__14_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__14);
v___x_4231_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__16));
lean_inc(v_currMacroScope_4226_);
lean_inc(v_quotContext_4225_);
v___x_4232_ = l_Lean_addMacroScope(v_quotContext_4225_, v___x_4231_, v_currMacroScope_4226_);
v___x_4233_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__18));
lean_inc_n(v___x_4227_, 12);
v___x_4234_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4234_, 0, v___x_4227_);
lean_ctor_set(v___x_4234_, 1, v___x_4230_);
lean_ctor_set(v___x_4234_, 2, v___x_4232_);
lean_ctor_set(v___x_4234_, 3, v___x_4233_);
v___x_4235_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__20));
v___x_4236_ = l_Lean_Syntax_node3(v___x_4227_, v___x_4235_, v___x_4195_, v_a_4223_, v_a_4202_);
v___x_4237_ = l_Lean_Syntax_node2(v___x_4227_, v___x_4229_, v___x_4234_, v___x_4236_);
v___x_4238_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__21));
v___x_4239_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4239_, 0, v___x_4227_);
lean_ctor_set(v___x_4239_, 1, v___x_4238_);
v___x_4240_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__22));
v___x_4241_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__23));
v___x_4242_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4242_, 0, v___x_4227_);
lean_ctor_set(v___x_4242_, 1, v___x_4240_);
v___x_4243_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__25));
v___x_4244_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__27));
v___x_4245_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__28));
v___x_4246_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4227_);
lean_ctor_set(v___x_4246_, 1, v___x_4245_);
v___x_4247_ = l_Lean_Syntax_node1(v___x_4227_, v___x_4244_, v___x_4246_);
v___x_4248_ = l_Lean_Syntax_node1(v___x_4227_, v___x_4235_, v___x_4247_);
v___x_4249_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__29, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__29_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__29);
v___x_4250_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4250_, 0, v___x_4227_);
lean_ctor_set(v___x_4250_, 1, v___x_4235_);
lean_ctor_set(v___x_4250_, 2, v___x_4249_);
v___x_4251_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__30));
v___x_4252_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4252_, 0, v___x_4227_);
lean_ctor_set(v___x_4252_, 1, v___x_4251_);
v___x_4253_ = l_Lean_Syntax_node4(v___x_4227_, v___x_4243_, v___x_4248_, v___x_4250_, v___x_4252_, v_body_4164_);
v___x_4254_ = l_Lean_Syntax_node2(v___x_4227_, v___x_4241_, v___x_4242_, v___x_4253_);
v___x_4255_ = l_Lean_Syntax_node3(v___x_4227_, v___x_4228_, v___x_4237_, v___x_4239_, v___x_4254_);
v___x_4256_ = l_Lean_Elab_Term_elabTerm(v___x_4255_, v_expectedType_x3f_4166_, v___y_4185_, v___y_4185_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
return v___x_4256_;
}
else
{
lean_object* v_a_4257_; lean_object* v___x_4259_; uint8_t v_isShared_4260_; uint8_t v_isSharedCheck_4264_; 
lean_dec(v_a_4202_);
lean_dec(v___x_4195_);
lean_dec(v_expectedType_x3f_4166_);
lean_dec(v_body_4164_);
v_a_4257_ = lean_ctor_get(v___x_4221_, 0);
v_isSharedCheck_4264_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4264_ == 0)
{
v___x_4259_ = v___x_4221_;
v_isShared_4260_ = v_isSharedCheck_4264_;
goto v_resetjp_4258_;
}
else
{
lean_inc(v_a_4257_);
lean_dec(v___x_4221_);
v___x_4259_ = lean_box(0);
v_isShared_4260_ = v_isSharedCheck_4264_;
goto v_resetjp_4258_;
}
v_resetjp_4258_:
{
lean_object* v___x_4262_; 
if (v_isShared_4260_ == 0)
{
v___x_4262_ = v___x_4259_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v_a_4257_);
v___x_4262_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
return v___x_4262_;
}
}
}
}
else
{
lean_object* v_a_4265_; lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4272_; 
lean_dec(v_a_4202_);
lean_dec(v___x_4195_);
lean_dec(v_expectedType_x3f_4166_);
lean_dec(v_body_4164_);
v_a_4265_ = lean_ctor_get(v___x_4213_, 0);
v_isSharedCheck_4272_ = !lean_is_exclusive(v___x_4213_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4267_ = v___x_4213_;
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
else
{
lean_inc(v_a_4265_);
lean_dec(v___x_4213_);
v___x_4267_ = lean_box(0);
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
v_resetjp_4266_:
{
lean_object* v___x_4270_; 
if (v_isShared_4268_ == 0)
{
v___x_4270_ = v___x_4267_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_a_4265_);
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
else
{
lean_object* v_a_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4280_; 
lean_dec(v___x_4195_);
lean_dec(v_expectedType_x3f_4166_);
lean_dec(v_body_4164_);
v_a_4273_ = lean_ctor_get(v___x_4201_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4275_ = v___x_4201_;
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_a_4273_);
lean_dec(v___x_4201_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
lean_object* v___x_4278_; 
if (v_isShared_4276_ == 0)
{
v___x_4278_ = v___x_4275_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_a_4273_);
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
else
{
lean_dec(v___x_4195_);
lean_dec(v_expectedType_x3f_4166_);
lean_dec(v_body_4164_);
return v___x_4199_;
}
}
v___jp_4281_:
{
lean_object* v___x_4296_; lean_object* v___x_4297_; uint8_t v___x_4298_; 
v___x_4296_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4294_);
v___x_4297_ = l_Lean_Elab_inServer;
v___x_4298_ = l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8(v___x_4296_, v___x_4297_);
lean_dec_ref(v___x_4296_);
if (v___x_4298_ == 0)
{
lean_dec_ref(v___y_4289_);
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4282_);
lean_dec(v_ref_4165_);
v___y_4183_ = v___y_4283_;
v___y_4184_ = v___y_4284_;
v___y_4185_ = v___y_4286_;
v___y_4186_ = v___y_4287_;
v___y_4187_ = v___y_4288_;
v___y_4188_ = v___y_4290_;
v___y_4189_ = v___y_4291_;
v___y_4190_ = v___y_4292_;
v___y_4191_ = v___y_4293_;
v___y_4192_ = v___y_4294_;
v___y_4193_ = v___y_4295_;
goto v___jp_4182_;
}
else
{
uint8_t v___x_4299_; 
v___x_4299_ = l_Lean_Expr_hasSorry(v___y_4289_);
if (v___x_4299_ == 0)
{
if (v___x_4298_ == 0)
{
lean_dec_ref(v___y_4289_);
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4282_);
lean_dec(v_ref_4165_);
v___y_4183_ = v___y_4283_;
v___y_4184_ = v___y_4284_;
v___y_4185_ = v___y_4286_;
v___y_4186_ = v___y_4287_;
v___y_4187_ = v___y_4288_;
v___y_4188_ = v___y_4290_;
v___y_4189_ = v___y_4291_;
v___y_4190_ = v___y_4292_;
v___y_4191_ = v___y_4293_;
v___y_4192_ = v___y_4294_;
v___y_4193_ = v___y_4295_;
goto v___jp_4182_;
}
else
{
lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___f_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; 
v___x_4300_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__8));
lean_inc_ref(v___y_4283_);
v___x_4301_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson(v___y_4283_);
v___x_4302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4302_, 0, v___x_4300_);
lean_ctor_set(v___x_4302_, 1, v___x_4301_);
v___x_4303_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__13));
v___x_4304_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson(v___y_4289_);
v___x_4305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4305_, 0, v___x_4303_);
lean_ctor_set(v___x_4305_, 1, v___x_4304_);
v___x_4306_ = lean_box(0);
v___x_4307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4307_, 0, v___x_4305_);
lean_ctor_set(v___x_4307_, 1, v___x_4306_);
v___x_4308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4308_, 0, v___x_4302_);
lean_ctor_set(v___x_4308_, 1, v___x_4307_);
v___x_4309_ = l_Lean_Json_mkObj(v___x_4308_);
lean_dec_ref_known(v___x_4308_, 2);
lean_inc(v_ref_4165_);
v___f_4310_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4310_, 0, v___y_4282_);
lean_closure_set(v___f_4310_, 1, v___x_4309_);
lean_closure_set(v___f_4310_, 2, v_ref_4165_);
v___x_4311_ = l_IO_CancelToken_new();
v___x_4312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4312_, 0, v___x_4311_);
v___x_4313_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0));
v___x_4314_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__8));
v___x_4315_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__11));
lean_inc(v___y_4285_);
v___x_4316_ = l_Lean_Name_num___override(v___x_4315_, v___y_4285_);
v___x_4317_ = l_Lean_Name_str___override(v___x_4316_, v___x_4313_);
v___x_4318_ = l_Lean_Name_str___override(v___x_4317_, v___x_4314_);
v___x_4319_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__15));
v___x_4320_ = l_Lean_Name_str___override(v___x_4318_, v___x_4319_);
v___x_4321_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__31));
v___x_4322_ = l_Lean_Name_str___override(v___x_4320_, v___x_4321_);
v___x_4323_ = l_Lean_Name_toString(v___x_4322_, v___y_4286_);
lean_inc_ref(v___x_4312_);
v___x_4324_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___f_4310_, v___x_4312_, v___x_4323_, v___y_4294_, v___y_4295_);
if (lean_obj_tag(v___x_4324_) == 0)
{
lean_object* v_a_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; 
v_a_4325_ = lean_ctor_get(v___x_4324_, 0);
lean_inc(v_a_4325_);
lean_dec_ref_known(v___x_4324_, 1);
v___x_4326_ = lean_box(0);
v___x_4327_ = lean_apply_1(v_a_4325_, v___x_4326_);
v___x_4328_ = lean_io_as_task(v___x_4327_, v___y_4285_);
v___x_4329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4329_, 0, v_ref_4165_);
v___x_4330_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_4329_);
v___x_4331_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4331_, 0, v___x_4329_);
lean_ctor_set(v___x_4331_, 1, v___x_4330_);
lean_ctor_set(v___x_4331_, 2, v___x_4312_);
lean_ctor_set(v___x_4331_, 3, v___x_4328_);
v___x_4332_ = l_Lean_Core_logSnapshotTask___redArg(v___x_4331_, v___y_4295_);
if (lean_obj_tag(v___x_4332_) == 0)
{
lean_dec_ref_known(v___x_4332_, 1);
v___y_4183_ = v___y_4283_;
v___y_4184_ = v___y_4284_;
v___y_4185_ = v___y_4286_;
v___y_4186_ = v___y_4287_;
v___y_4187_ = v___y_4288_;
v___y_4188_ = v___y_4290_;
v___y_4189_ = v___y_4291_;
v___y_4190_ = v___y_4292_;
v___y_4191_ = v___y_4293_;
v___y_4192_ = v___y_4294_;
v___y_4193_ = v___y_4295_;
goto v___jp_4182_;
}
else
{
lean_object* v_a_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4340_; 
lean_dec_ref(v___y_4287_);
lean_dec_ref(v___y_4284_);
lean_dec_ref(v___y_4283_);
lean_dec(v_expectedType_x3f_4166_);
lean_dec(v_body_4164_);
v_a_4333_ = lean_ctor_get(v___x_4332_, 0);
v_isSharedCheck_4340_ = !lean_is_exclusive(v___x_4332_);
if (v_isSharedCheck_4340_ == 0)
{
v___x_4335_ = v___x_4332_;
v_isShared_4336_ = v_isSharedCheck_4340_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_a_4333_);
lean_dec(v___x_4332_);
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
else
{
lean_object* v_a_4341_; lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4348_; 
lean_dec_ref_known(v___x_4312_, 1);
lean_dec_ref(v___y_4287_);
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4284_);
lean_dec_ref(v___y_4283_);
lean_dec(v_expectedType_x3f_4166_);
lean_dec(v_ref_4165_);
lean_dec(v_body_4164_);
v_a_4341_ = lean_ctor_get(v___x_4324_, 0);
v_isSharedCheck_4348_ = !lean_is_exclusive(v___x_4324_);
if (v_isSharedCheck_4348_ == 0)
{
v___x_4343_ = v___x_4324_;
v_isShared_4344_ = v_isSharedCheck_4348_;
goto v_resetjp_4342_;
}
else
{
lean_inc(v_a_4341_);
lean_dec(v___x_4324_);
v___x_4343_ = lean_box(0);
v_isShared_4344_ = v_isSharedCheck_4348_;
goto v_resetjp_4342_;
}
v_resetjp_4342_:
{
lean_object* v___x_4346_; 
if (v_isShared_4344_ == 0)
{
v___x_4346_ = v___x_4343_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4347_; 
v_reuseFailAlloc_4347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4347_, 0, v_a_4341_);
v___x_4346_ = v_reuseFailAlloc_4347_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
return v___x_4346_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_4289_);
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4282_);
lean_dec(v_ref_4165_);
v___y_4183_ = v___y_4283_;
v___y_4184_ = v___y_4284_;
v___y_4185_ = v___y_4286_;
v___y_4186_ = v___y_4287_;
v___y_4187_ = v___y_4288_;
v___y_4188_ = v___y_4290_;
v___y_4189_ = v___y_4291_;
v___y_4190_ = v___y_4292_;
v___y_4191_ = v___y_4293_;
v___y_4192_ = v___y_4294_;
v___y_4193_ = v___y_4295_;
goto v___jp_4182_;
}
}
}
v___jp_4349_:
{
uint8_t v___x_4364_; 
v___x_4364_ = l_Lean_Expr_hasMVar(v___y_4351_);
if (v___x_4364_ == 0)
{
v___y_4282_ = v___y_4350_;
v___y_4283_ = v___y_4351_;
v___y_4284_ = v___y_4352_;
v___y_4285_ = v___y_4353_;
v___y_4286_ = v___y_4354_;
v___y_4287_ = v___y_4355_;
v___y_4288_ = v___y_4356_;
v___y_4289_ = v___y_4357_;
v___y_4290_ = v___y_4358_;
v___y_4291_ = v___y_4359_;
v___y_4292_ = v___y_4360_;
v___y_4293_ = v___y_4361_;
v___y_4294_ = v___y_4362_;
v___y_4295_ = v___y_4363_;
goto v___jp_4281_;
}
else
{
lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v_a_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4374_; 
lean_dec_ref(v___y_4357_);
lean_dec_ref(v___y_4355_);
lean_dec(v___y_4353_);
lean_dec_ref(v___y_4352_);
lean_dec_ref(v___y_4351_);
lean_dec_ref(v___y_4350_);
lean_dec(v_expectedType_x3f_4166_);
lean_dec(v_ref_4165_);
lean_dec(v_body_4164_);
v___x_4365_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__33, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__33_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__33);
v___x_4366_ = l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg(v___x_4365_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
v_a_4367_ = lean_ctor_get(v___x_4366_, 0);
v_isSharedCheck_4374_ = !lean_is_exclusive(v___x_4366_);
if (v_isSharedCheck_4374_ == 0)
{
v___x_4369_ = v___x_4366_;
v_isShared_4370_ = v_isSharedCheck_4374_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_a_4367_);
lean_dec(v___x_4366_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4374_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v___x_4372_; 
if (v_isShared_4370_ == 0)
{
v___x_4372_ = v___x_4369_;
goto v_reusejp_4371_;
}
else
{
lean_object* v_reuseFailAlloc_4373_; 
v_reuseFailAlloc_4373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4373_, 0, v_a_4367_);
v___x_4372_ = v_reuseFailAlloc_4373_;
goto v_reusejp_4371_;
}
v_reusejp_4371_:
{
return v___x_4372_;
}
}
}
}
v___jp_4375_:
{
uint8_t v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___f_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___f_4394_; lean_object* v___x_4395_; 
v___x_4386_ = 1;
v___x_4387_ = lean_box(v___x_4181_);
v___x_4388_ = lean_box(v___y_4379_);
v___x_4389_ = lean_box(v___x_4386_);
lean_inc_ref(v___y_4380_);
v___f_4390_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__1___boxed), 13, 5);
lean_closure_set(v___f_4390_, 0, v___y_4380_);
lean_closure_set(v___f_4390_, 1, v___y_4378_);
lean_closure_set(v___f_4390_, 2, v___x_4387_);
lean_closure_set(v___f_4390_, 3, v___x_4388_);
lean_closure_set(v___f_4390_, 4, v___x_4389_);
v___x_4391_ = lean_box(v___x_4181_);
v___x_4392_ = lean_box(v___y_4379_);
v___x_4393_ = lean_box(v___x_4386_);
v___f_4394_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__2___boxed), 12, 5);
lean_closure_set(v___f_4394_, 0, v___y_4380_);
lean_closure_set(v___f_4394_, 1, v___y_4376_);
lean_closure_set(v___f_4394_, 2, v___x_4391_);
lean_closure_set(v___f_4394_, 3, v___x_4392_);
lean_closure_set(v___f_4394_, 4, v___x_4393_);
v___x_4395_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___redArg(v___y_4385_, v___f_4394_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_);
if (lean_obj_tag(v___x_4395_) == 0)
{
lean_object* v_a_4396_; lean_object* v_fst_4397_; lean_object* v_snd_4398_; uint8_t v___x_4399_; 
v_a_4396_ = lean_ctor_get(v___x_4395_, 0);
lean_inc(v_a_4396_);
lean_dec_ref_known(v___x_4395_, 1);
v_fst_4397_ = lean_ctor_get(v_a_4396_, 0);
lean_inc(v_fst_4397_);
v_snd_4398_ = lean_ctor_get(v_a_4396_, 1);
lean_inc(v_snd_4398_);
lean_dec(v_a_4396_);
v___x_4399_ = l_Lean_Expr_hasMVar(v_fst_4397_);
if (v___x_4399_ == 0)
{
v___y_4350_ = v___y_4377_;
v___y_4351_ = v_snd_4398_;
v___y_4352_ = v___y_4381_;
v___y_4353_ = v___y_4382_;
v___y_4354_ = v___y_4383_;
v___y_4355_ = v___f_4390_;
v___y_4356_ = v___y_4384_;
v___y_4357_ = v_fst_4397_;
v___y_4358_ = v_a_4167_;
v___y_4359_ = v_a_4168_;
v___y_4360_ = v_a_4169_;
v___y_4361_ = v_a_4170_;
v___y_4362_ = v_a_4171_;
v___y_4363_ = v_a_4172_;
goto v___jp_4349_;
}
else
{
lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v_a_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4409_; 
lean_dec(v_snd_4398_);
lean_dec(v_fst_4397_);
lean_dec_ref(v___f_4390_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
lean_dec_ref(v___y_4377_);
lean_dec(v_expectedType_x3f_4166_);
lean_dec(v_ref_4165_);
lean_dec(v_body_4164_);
v___x_4400_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__35, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__35_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__35);
v___x_4401_ = l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg(v___x_4400_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_);
v_a_4402_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4404_ = v___x_4401_;
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_a_4402_);
lean_dec(v___x_4401_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4407_; 
if (v_isShared_4405_ == 0)
{
v___x_4407_ = v___x_4404_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v_a_4402_);
v___x_4407_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
return v___x_4407_;
}
}
}
}
else
{
lean_object* v_a_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4417_; 
lean_dec_ref(v___f_4390_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
lean_dec_ref(v___y_4377_);
lean_dec(v_expectedType_x3f_4166_);
lean_dec(v_ref_4165_);
lean_dec(v_body_4164_);
v_a_4410_ = lean_ctor_get(v___x_4395_, 0);
v_isSharedCheck_4417_ = !lean_is_exclusive(v___x_4395_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4412_ = v___x_4395_;
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_a_4410_);
lean_dec(v___x_4395_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
lean_object* v___x_4415_; 
if (v_isShared_4413_ == 0)
{
v___x_4415_ = v___x_4412_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_a_4410_);
v___x_4415_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
return v___x_4415_;
}
}
}
}
v___jp_4418_:
{
lean_object* v_lctx_4420_; lean_object* v_decls_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; uint64_t v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; 
v_lctx_4420_ = lean_ctor_get(v_a_4169_, 2);
v_decls_4421_ = lean_ctor_get(v_lctx_4420_, 1);
v___x_4422_ = l_Nat_reprFast(v___y_4419_);
v___x_4423_ = lean_string_append(v___x_4180_, v___x_4422_);
lean_dec_ref(v___x_4422_);
v___x_4424_ = lean_string_hash(v___x_4423_);
lean_dec_ref(v___x_4423_);
v___x_4425_ = lean_uint64_to_nat(v___x_4424_);
v___x_4426_ = l_Nat_reprFast(v___x_4425_);
v___x_4427_ = lean_unsigned_to_nat(0u);
v___x_4428_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__36));
v___x_4429_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0(v_decls_4421_, v___x_4428_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_);
if (lean_obj_tag(v___x_4429_) == 0)
{
lean_object* v_a_4430_; size_t v_sz_4431_; size_t v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; uint8_t v___x_4435_; lean_object* v___x_4436_; 
v_a_4430_ = lean_ctor_get(v___x_4429_, 0);
lean_inc_n(v_a_4430_, 2);
lean_dec_ref_known(v___x_4429_, 1);
v_sz_4431_ = lean_array_size(v_a_4430_);
v___x_4432_ = ((size_t)0ULL);
v___x_4433_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__1(v_sz_4431_, v___x_4432_, v_a_4430_);
v___x_4434_ = lean_box(0);
v___x_4435_ = 1;
v___x_4436_ = l_Lean_Elab_Term_elabTerm(v_e_4163_, v___x_4434_, v___x_4435_, v___x_4435_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_);
if (lean_obj_tag(v___x_4436_) == 0)
{
lean_object* v_a_4437_; lean_object* v___x_4438_; 
v_a_4437_ = lean_ctor_get(v___x_4436_, 0);
lean_inc(v_a_4437_);
lean_dec_ref_known(v___x_4436_, 1);
v___x_4438_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_4181_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_);
if (lean_obj_tag(v___x_4438_) == 0)
{
lean_object* v___x_4439_; lean_object* v_a_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; 
lean_dec_ref_known(v___x_4438_, 1);
v___x_4439_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(v_a_4437_, v_a_4170_);
v_a_4440_ = lean_ctor_get(v___x_4439_, 0);
lean_inc(v_a_4440_);
lean_dec_ref(v___x_4439_);
v___x_4441_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__38));
v___x_4442_ = lean_unsigned_to_nat(1u);
v___x_4443_ = lean_mk_empty_array_with_capacity(v___x_4442_);
lean_inc_ref(v___x_4443_);
v___x_4444_ = lean_array_push(v___x_4443_, v_a_4440_);
v___x_4445_ = l_Lean_Meta_mkAppM(v___x_4441_, v___x_4444_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_);
if (lean_obj_tag(v___x_4445_) == 0)
{
lean_object* v_a_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; 
v_a_4446_ = lean_ctor_get(v___x_4445_, 0);
lean_inc(v_a_4446_);
lean_dec_ref_known(v___x_4445_, 1);
v___x_4447_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__41));
lean_inc_ref(v___x_4443_);
v___x_4448_ = lean_array_push(v___x_4443_, v_a_4446_);
v___x_4449_ = l_Lean_Meta_mkAppM(v___x_4447_, v___x_4448_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_);
if (lean_obj_tag(v___x_4449_) == 0)
{
lean_object* v_a_4450_; lean_object* v___x_4451_; 
v_a_4450_ = lean_ctor_get(v___x_4449_, 0);
lean_inc(v_a_4450_);
lean_dec_ref_known(v___x_4449_, 1);
v___x_4451_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_4181_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_);
if (lean_obj_tag(v___x_4451_) == 0)
{
lean_object* v___x_4452_; lean_object* v_a_4453_; lean_object* v___x_4454_; uint8_t v___x_4455_; 
lean_dec_ref_known(v___x_4451_, 1);
v___x_4452_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(v_a_4450_, v_a_4170_);
v_a_4453_ = lean_ctor_get(v___x_4452_, 0);
lean_inc(v_a_4453_);
lean_dec_ref(v___x_4452_);
v___x_4454_ = lean_array_get_size(v_a_4430_);
v___x_4455_ = lean_nat_dec_lt(v___x_4427_, v___x_4454_);
if (v___x_4455_ == 0)
{
lean_dec(v_a_4430_);
lean_inc_ref(v_lctx_4420_);
lean_inc_ref(v___x_4426_);
v___y_4376_ = v_a_4453_;
v___y_4377_ = v___x_4426_;
v___y_4378_ = v___x_4443_;
v___y_4379_ = v___x_4435_;
v___y_4380_ = v___x_4433_;
v___y_4381_ = v___x_4426_;
v___y_4382_ = v___x_4427_;
v___y_4383_ = v___x_4435_;
v___y_4384_ = v___x_4432_;
v___y_4385_ = v_lctx_4420_;
goto v___jp_4375_;
}
else
{
uint8_t v___x_4456_; 
v___x_4456_ = lean_nat_dec_le(v___x_4454_, v___x_4454_);
if (v___x_4456_ == 0)
{
if (v___x_4455_ == 0)
{
lean_dec(v_a_4430_);
lean_inc_ref(v_lctx_4420_);
lean_inc_ref(v___x_4426_);
v___y_4376_ = v_a_4453_;
v___y_4377_ = v___x_4426_;
v___y_4378_ = v___x_4443_;
v___y_4379_ = v___x_4435_;
v___y_4380_ = v___x_4433_;
v___y_4381_ = v___x_4426_;
v___y_4382_ = v___x_4427_;
v___y_4383_ = v___x_4435_;
v___y_4384_ = v___x_4432_;
v___y_4385_ = v_lctx_4420_;
goto v___jp_4375_;
}
else
{
size_t v___x_4457_; lean_object* v___x_4458_; 
v___x_4457_ = lean_usize_of_nat(v___x_4454_);
lean_inc_ref(v_lctx_4420_);
v___x_4458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__11(v_a_4430_, v___x_4432_, v___x_4457_, v_lctx_4420_);
lean_dec(v_a_4430_);
lean_inc_ref(v___x_4426_);
v___y_4376_ = v_a_4453_;
v___y_4377_ = v___x_4426_;
v___y_4378_ = v___x_4443_;
v___y_4379_ = v___x_4435_;
v___y_4380_ = v___x_4433_;
v___y_4381_ = v___x_4426_;
v___y_4382_ = v___x_4427_;
v___y_4383_ = v___x_4435_;
v___y_4384_ = v___x_4432_;
v___y_4385_ = v___x_4458_;
goto v___jp_4375_;
}
}
else
{
size_t v___x_4459_; lean_object* v___x_4460_; 
v___x_4459_ = lean_usize_of_nat(v___x_4454_);
lean_inc_ref(v_lctx_4420_);
v___x_4460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__11(v_a_4430_, v___x_4432_, v___x_4459_, v_lctx_4420_);
lean_dec(v_a_4430_);
lean_inc_ref(v___x_4426_);
v___y_4376_ = v_a_4453_;
v___y_4377_ = v___x_4426_;
v___y_4378_ = v___x_4443_;
v___y_4379_ = v___x_4435_;
v___y_4380_ = v___x_4433_;
v___y_4381_ = v___x_4426_;
v___y_4382_ = v___x_4427_;
v___y_4383_ = v___x_4435_;
v___y_4384_ = v___x_4432_;
v___y_4385_ = v___x_4460_;
goto v___jp_4375_;
}
}
}
else
{
lean_object* v_a_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4468_; 
lean_dec(v_a_4450_);
lean_dec_ref(v___x_4443_);
lean_dec_ref(v___x_4433_);
lean_dec(v_a_4430_);
lean_dec_ref(v___x_4426_);
lean_dec(v_expectedType_x3f_4166_);
lean_dec(v_ref_4165_);
lean_dec(v_body_4164_);
v_a_4461_ = lean_ctor_get(v___x_4451_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4451_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4463_ = v___x_4451_;
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_dec(v___x_4451_);
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
lean_dec_ref(v___x_4443_);
lean_dec_ref(v___x_4433_);
lean_dec(v_a_4430_);
lean_dec_ref(v___x_4426_);
lean_dec(v_expectedType_x3f_4166_);
lean_dec(v_ref_4165_);
lean_dec(v_body_4164_);
return v___x_4449_;
}
}
else
{
lean_dec_ref(v___x_4443_);
lean_dec_ref(v___x_4433_);
lean_dec(v_a_4430_);
lean_dec_ref(v___x_4426_);
lean_dec(v_expectedType_x3f_4166_);
lean_dec(v_ref_4165_);
lean_dec(v_body_4164_);
return v___x_4445_;
}
}
else
{
lean_object* v_a_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4476_; 
lean_dec(v_a_4437_);
lean_dec_ref(v___x_4433_);
lean_dec(v_a_4430_);
lean_dec_ref(v___x_4426_);
lean_dec(v_expectedType_x3f_4166_);
lean_dec(v_ref_4165_);
lean_dec(v_body_4164_);
v_a_4469_ = lean_ctor_get(v___x_4438_, 0);
v_isSharedCheck_4476_ = !lean_is_exclusive(v___x_4438_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4471_ = v___x_4438_;
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_a_4469_);
lean_dec(v___x_4438_);
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
else
{
lean_dec_ref(v___x_4433_);
lean_dec(v_a_4430_);
lean_dec_ref(v___x_4426_);
lean_dec(v_expectedType_x3f_4166_);
lean_dec(v_ref_4165_);
lean_dec(v_body_4164_);
return v___x_4436_;
}
}
else
{
lean_object* v_a_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4484_; 
lean_dec_ref(v___x_4426_);
lean_dec(v_expectedType_x3f_4166_);
lean_dec(v_ref_4165_);
lean_dec(v_body_4164_);
lean_dec(v_e_4163_);
v_a_4477_ = lean_ctor_get(v___x_4429_, 0);
v_isSharedCheck_4484_ = !lean_is_exclusive(v___x_4429_);
if (v_isSharedCheck_4484_ == 0)
{
v___x_4479_ = v___x_4429_;
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_a_4477_);
lean_dec(v___x_4429_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4482_; 
if (v_isShared_4480_ == 0)
{
v___x_4482_ = v___x_4479_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_a_4477_);
v___x_4482_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
return v___x_4482_;
}
}
}
}
}
else
{
lean_object* v_a_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4499_; 
lean_dec(v_expectedType_x3f_4166_);
lean_dec(v_ref_4165_);
lean_dec(v_body_4164_);
lean_dec(v_e_4163_);
v_a_4488_ = lean_ctor_get(v___x_4177_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4177_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4490_ = v___x_4177_;
v_isShared_4491_ = v_isSharedCheck_4499_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_a_4488_);
lean_dec(v___x_4177_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4499_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4497_; 
v___x_4492_ = lean_io_error_to_string(v_a_4488_);
v___x_4493_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4493_, 0, v___x_4492_);
v___x_4494_ = l_Lean_MessageData_ofFormat(v___x_4493_);
lean_inc(v_ref_4175_);
v___x_4495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4495_, 0, v_ref_4175_);
lean_ctor_set(v___x_4495_, 1, v___x_4494_);
if (v_isShared_4491_ == 0)
{
lean_ctor_set(v___x_4490_, 0, v___x_4495_);
v___x_4497_ = v___x_4490_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v___x_4495_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
return v___x_4497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___boxed(lean_object* v_e_4500_, lean_object* v_body_4501_, lean_object* v_ref_4502_, lean_object* v_expectedType_x3f_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_){
_start:
{
lean_object* v_res_4511_; 
v_res_4511_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore(v_e_4500_, v_body_4501_, v_ref_4502_, v_expectedType_x3f_4503_, v_a_4504_, v_a_4505_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_);
lean_dec(v_a_4509_);
lean_dec_ref(v_a_4508_);
lean_dec(v_a_4507_);
lean_dec_ref(v_a_4506_);
lean_dec(v_a_4505_);
lean_dec_ref(v_a_4504_);
return v_res_4511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2(lean_object* v_00_u03b2_4512_, lean_object* v_x_4513_, lean_object* v_x_4514_, lean_object* v_x_4515_){
_start:
{
lean_object* v___x_4516_; 
v___x_4516_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2___redArg(v_x_4513_, v_x_4514_, v_x_4515_);
return v___x_4516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6(size_t v_sz_4517_, size_t v_i_4518_, lean_object* v_bs_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_){
_start:
{
lean_object* v___x_4527_; 
v___x_4527_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg(v_sz_4517_, v_i_4518_, v_bs_4519_);
return v___x_4527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___boxed(lean_object* v_sz_4528_, lean_object* v_i_4529_, lean_object* v_bs_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_){
_start:
{
size_t v_sz_boxed_4538_; size_t v_i_boxed_4539_; lean_object* v_res_4540_; 
v_sz_boxed_4538_ = lean_unbox_usize(v_sz_4528_);
lean_dec(v_sz_4528_);
v_i_boxed_4539_ = lean_unbox_usize(v_i_4529_);
lean_dec(v_i_4529_);
v_res_4540_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6(v_sz_boxed_4538_, v_i_boxed_4539_, v_bs_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_);
lean_dec(v___y_4536_);
lean_dec_ref(v___y_4535_);
lean_dec(v___y_4534_);
lean_dec_ref(v___y_4533_);
lean_dec(v___y_4532_);
lean_dec_ref(v___y_4531_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10(lean_object* v_00_u03b1_4541_, lean_object* v_msg_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_){
_start:
{
lean_object* v___x_4550_; 
v___x_4550_ = l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg(v_msg_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_);
return v___x_4550_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___boxed(lean_object* v_00_u03b1_4551_, lean_object* v_msg_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_){
_start:
{
lean_object* v_res_4560_; 
v_res_4560_ = l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10(v_00_u03b1_4551_, v_msg_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
lean_dec(v___y_4558_);
lean_dec_ref(v___y_4557_);
lean_dec(v___y_4556_);
lean_dec_ref(v___y_4555_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
return v_res_4560_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4(lean_object* v_00_u03b2_4561_, lean_object* v_x_4562_, size_t v_x_4563_, size_t v_x_4564_, lean_object* v_x_4565_, lean_object* v_x_4566_){
_start:
{
lean_object* v___x_4567_; 
v___x_4567_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg(v_x_4562_, v_x_4563_, v_x_4564_, v_x_4565_, v_x_4566_);
return v___x_4567_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4568_, lean_object* v_x_4569_, lean_object* v_x_4570_, lean_object* v_x_4571_, lean_object* v_x_4572_, lean_object* v_x_4573_){
_start:
{
size_t v_x_36679__boxed_4574_; size_t v_x_36680__boxed_4575_; lean_object* v_res_4576_; 
v_x_36679__boxed_4574_ = lean_unbox_usize(v_x_4570_);
lean_dec(v_x_4570_);
v_x_36680__boxed_4575_ = lean_unbox_usize(v_x_4571_);
lean_dec(v_x_4571_);
v_res_4576_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4(v_00_u03b2_4568_, v_x_4569_, v_x_36679__boxed_4574_, v_x_36680__boxed_4575_, v_x_4572_, v_x_4573_);
return v_res_4576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16(lean_object* v_msgData_4577_, lean_object* v_macroStack_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_){
_start:
{
lean_object* v___x_4586_; 
v___x_4586_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg(v_msgData_4577_, v_macroStack_4578_, v___y_4583_);
return v___x_4586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___boxed(lean_object* v_msgData_4587_, lean_object* v_macroStack_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_){
_start:
{
lean_object* v_res_4596_; 
v_res_4596_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16(v_msgData_4587_, v_macroStack_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_);
lean_dec(v___y_4594_);
lean_dec_ref(v___y_4593_);
lean_dec(v___y_4592_);
lean_dec_ref(v___y_4591_);
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
return v_res_4596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8(lean_object* v_as_4597_, size_t v_sz_4598_, size_t v_i_4599_, lean_object* v_b_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_){
_start:
{
lean_object* v___x_4608_; 
v___x_4608_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___redArg(v_as_4597_, v_sz_4598_, v_i_4599_, v_b_4600_);
return v___x_4608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___boxed(lean_object* v_as_4609_, lean_object* v_sz_4610_, lean_object* v_i_4611_, lean_object* v_b_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_){
_start:
{
size_t v_sz_boxed_4620_; size_t v_i_boxed_4621_; lean_object* v_res_4622_; 
v_sz_boxed_4620_ = lean_unbox_usize(v_sz_4610_);
lean_dec(v_sz_4610_);
v_i_boxed_4621_ = lean_unbox_usize(v_i_4611_);
lean_dec(v_i_4611_);
v_res_4622_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8(v_as_4609_, v_sz_boxed_4620_, v_i_boxed_4621_, v_b_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_);
lean_dec(v___y_4618_);
lean_dec_ref(v___y_4617_);
lean_dec(v___y_4616_);
lean_dec_ref(v___y_4615_);
lean_dec(v___y_4614_);
lean_dec_ref(v___y_4613_);
lean_dec_ref(v_as_4609_);
return v_res_4622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12(lean_object* v_00_u03b2_4623_, lean_object* v_n_4624_, lean_object* v_k_4625_, lean_object* v_v_4626_){
_start:
{
lean_object* v___x_4627_; 
v___x_4627_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12___redArg(v_n_4624_, v_k_4625_, v_v_4626_);
return v___x_4627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13(lean_object* v_00_u03b2_4628_, size_t v_depth_4629_, lean_object* v_keys_4630_, lean_object* v_vals_4631_, lean_object* v_heq_4632_, lean_object* v_i_4633_, lean_object* v_entries_4634_){
_start:
{
lean_object* v___x_4635_; 
v___x_4635_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___redArg(v_depth_4629_, v_keys_4630_, v_vals_4631_, v_i_4633_, v_entries_4634_);
return v___x_4635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___boxed(lean_object* v_00_u03b2_4636_, lean_object* v_depth_4637_, lean_object* v_keys_4638_, lean_object* v_vals_4639_, lean_object* v_heq_4640_, lean_object* v_i_4641_, lean_object* v_entries_4642_){
_start:
{
size_t v_depth_boxed_4643_; lean_object* v_res_4644_; 
v_depth_boxed_4643_ = lean_unbox_usize(v_depth_4637_);
lean_dec(v_depth_4637_);
v_res_4644_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13(v_00_u03b2_4636_, v_depth_boxed_4643_, v_keys_4638_, v_vals_4639_, v_heq_4640_, v_i_4641_, v_entries_4642_);
lean_dec_ref(v_vals_4639_);
lean_dec_ref(v_keys_4638_);
return v_res_4644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15(lean_object* v_as_4645_, size_t v_sz_4646_, size_t v_i_4647_, lean_object* v_b_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_){
_start:
{
lean_object* v___x_4656_; 
v___x_4656_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___redArg(v_as_4645_, v_sz_4646_, v_i_4647_, v_b_4648_);
return v___x_4656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___boxed(lean_object* v_as_4657_, lean_object* v_sz_4658_, lean_object* v_i_4659_, lean_object* v_b_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_){
_start:
{
size_t v_sz_boxed_4668_; size_t v_i_boxed_4669_; lean_object* v_res_4670_; 
v_sz_boxed_4668_ = lean_unbox_usize(v_sz_4658_);
lean_dec(v_sz_4658_);
v_i_boxed_4669_ = lean_unbox_usize(v_i_4659_);
lean_dec(v_i_4659_);
v_res_4670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15(v_as_4657_, v_sz_boxed_4668_, v_i_boxed_4669_, v_b_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_);
lean_dec(v___y_4666_);
lean_dec_ref(v___y_4665_);
lean_dec(v___y_4664_);
lean_dec_ref(v___y_4663_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec_ref(v_as_4657_);
return v_res_4670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12_spec__20(lean_object* v_00_u03b2_4671_, lean_object* v_x_4672_, lean_object* v_x_4673_, lean_object* v_x_4674_, lean_object* v_x_4675_){
_start:
{
lean_object* v___x_4676_; 
v___x_4676_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12_spec__20___redArg(v_x_4672_, v_x_4673_, v_x_4674_, v_x_4675_);
return v___x_4676_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; 
v___x_4677_ = lean_box(0);
v___x_4678_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_4679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4679_, 0, v___x_4678_);
lean_ctor_set(v___x_4679_, 1, v___x_4677_);
return v___x_4679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg(){
_start:
{
lean_object* v___x_4681_; lean_object* v___x_4682_; 
v___x_4681_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0);
v___x_4682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4682_, 0, v___x_4681_);
return v___x_4682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___boxed(lean_object* v___y_4683_){
_start:
{
lean_object* v_res_4684_; 
v_res_4684_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg();
return v_res_4684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0(lean_object* v_00_u03b1_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_){
_start:
{
lean_object* v___x_4693_; 
v___x_4693_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg();
return v___x_4693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___boxed(lean_object* v_00_u03b1_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_){
_start:
{
lean_object* v_res_4702_; 
v_res_4702_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0(v_00_u03b1_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_);
lean_dec(v___y_4700_);
lean_dec_ref(v___y_4699_);
lean_dec(v___y_4698_);
lean_dec_ref(v___y_4697_);
lean_dec(v___y_4696_);
lean_dec_ref(v___y_4695_);
return v_res_4702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm(lean_object* v_stx_4709_, lean_object* v_expectedType_x3f_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_){
_start:
{
lean_object* v___x_4718_; uint8_t v___x_4719_; 
v___x_4718_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__1));
lean_inc(v_stx_4709_);
v___x_4719_ = l_Lean_Syntax_isOfKind(v_stx_4709_, v___x_4718_);
if (v___x_4719_ == 0)
{
lean_object* v___x_4720_; 
lean_dec(v_expectedType_x3f_4710_);
lean_dec(v_stx_4709_);
v___x_4720_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg();
return v___x_4720_;
}
else
{
lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v_body_4724_; lean_object* v___x_4725_; 
v___x_4721_ = lean_unsigned_to_nat(1u);
v___x_4722_ = l_Lean_Syntax_getArg(v_stx_4709_, v___x_4721_);
v___x_4723_ = lean_unsigned_to_nat(3u);
v_body_4724_ = l_Lean_Syntax_getArg(v_stx_4709_, v___x_4723_);
v___x_4725_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore(v___x_4722_, v_body_4724_, v_stx_4709_, v_expectedType_x3f_4710_, v_a_4711_, v_a_4712_, v_a_4713_, v_a_4714_, v_a_4715_, v_a_4716_);
return v___x_4725_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___boxed(lean_object* v_stx_4726_, lean_object* v_expectedType_x3f_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_){
_start:
{
lean_object* v_res_4735_; 
v_res_4735_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm(v_stx_4726_, v_expectedType_x3f_4727_, v_a_4728_, v_a_4729_, v_a_4730_, v_a_4731_, v_a_4732_, v_a_4733_);
lean_dec(v_a_4733_);
lean_dec_ref(v_a_4732_);
lean_dec(v_a_4731_);
lean_dec_ref(v_a_4730_);
lean_dec(v_a_4729_);
lean_dec_ref(v_a_4728_);
return v_res_4735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1(){
_start:
{
lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; 
v___x_4741_ = l_Lean_Elab_Term_termElabAttribute;
v___x_4742_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__1));
v___x_4743_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1___closed__1));
v___x_4744_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___boxed), 9, 0);
v___x_4745_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4741_, v___x_4742_, v___x_4743_, v___x_4744_);
return v___x_4745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1___boxed(lean_object* v_a_4746_){
_start:
{
lean_object* v_res_4747_; 
v_res_4747_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1();
return v_res_4747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___redArg(){
_start:
{
lean_object* v___x_4749_; lean_object* v___x_4750_; 
v___x_4749_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0);
v___x_4750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4750_, 0, v___x_4749_);
return v___x_4750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___redArg___boxed(lean_object* v___y_4751_){
_start:
{
lean_object* v_res_4752_; 
v_res_4752_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___redArg();
return v_res_4752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0(lean_object* v_00_u03b1_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_){
_start:
{
lean_object* v___x_4762_; 
v___x_4762_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___redArg();
return v___x_4762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___boxed(lean_object* v_00_u03b1_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_){
_start:
{
lean_object* v_res_4772_; 
v_res_4772_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0(v_00_u03b1_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_, v___y_4770_);
lean_dec(v___y_4770_);
lean_dec_ref(v___y_4769_);
lean_dec(v___y_4768_);
lean_dec_ref(v___y_4767_);
lean_dec(v___y_4766_);
lean_dec_ref(v___y_4765_);
lean_dec_ref(v___y_4764_);
return v_res_4772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___lam__0(lean_object* v_a_4773_, lean_object* v___x_4774_, lean_object* v_stx_4775_, lean_object* v_body_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_){
_start:
{
lean_object* v___x_4785_; lean_object* v___x_4786_; 
v___x_4785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4785_, 0, v_a_4773_);
v___x_4786_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore(v___x_4774_, v_body_4776_, v_stx_4775_, v___x_4785_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_);
return v___x_4786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___lam__0___boxed(lean_object* v_a_4787_, lean_object* v___x_4788_, lean_object* v_stx_4789_, lean_object* v_body_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_){
_start:
{
lean_object* v_res_4799_; 
v_res_4799_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___lam__0(v_a_4787_, v___x_4788_, v_stx_4789_, v_body_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
lean_dec(v___y_4797_);
lean_dec_ref(v___y_4796_);
lean_dec(v___y_4795_);
lean_dec_ref(v___y_4794_);
lean_dec(v___y_4793_);
lean_dec_ref(v___y_4792_);
lean_dec_ref(v___y_4791_);
return v_res_4799_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__2(void){
_start:
{
lean_object* v___x_4803_; lean_object* v___x_4804_; 
v___x_4803_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__1));
v___x_4804_ = l_Lean_MessageData_ofFormat(v___x_4803_);
return v___x_4804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg(lean_object* v_stx_4805_, lean_object* v_dec_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_){
_start:
{
lean_object* v___x_4815_; uint8_t v___x_4816_; 
v___x_4815_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4));
lean_inc(v_stx_4805_);
v___x_4816_ = l_Lean_Syntax_isOfKind(v_stx_4805_, v___x_4815_);
if (v___x_4816_ == 0)
{
lean_object* v___x_4817_; 
lean_dec_ref(v_dec_4806_);
lean_dec(v_stx_4805_);
v___x_4817_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___redArg();
return v___x_4817_;
}
else
{
lean_object* v_doBlockResultType_4818_; lean_object* v___x_4819_; lean_object* v_tk_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; 
v_doBlockResultType_4818_ = lean_ctor_get(v_a_4807_, 3);
v___x_4819_ = lean_unsigned_to_nat(0u);
v_tk_4820_ = l_Lean_Syntax_getArg(v_stx_4805_, v___x_4819_);
v___x_4821_ = lean_unsigned_to_nat(1u);
v___x_4822_ = l_Lean_Syntax_getArg(v_stx_4805_, v___x_4821_);
lean_inc_ref(v_doBlockResultType_4818_);
v___x_4823_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_4818_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_, v_a_4813_);
if (lean_obj_tag(v___x_4823_) == 0)
{
lean_object* v_a_4824_; lean_object* v___f_4825_; lean_object* v___x_4826_; 
v_a_4824_ = lean_ctor_get(v___x_4823_, 0);
lean_inc(v_a_4824_);
lean_dec_ref_known(v___x_4823_, 1);
v___f_4825_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___lam__0___boxed), 12, 3);
lean_closure_set(v___f_4825_, 0, v_a_4824_);
lean_closure_set(v___f_4825_, 1, v___x_4822_);
lean_closure_set(v___f_4825_, 2, v_stx_4805_);
v___x_4826_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4806_, v_tk_4820_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_, v_a_4813_);
lean_dec(v_tk_4820_);
if (lean_obj_tag(v___x_4826_) == 0)
{
lean_object* v_a_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; 
v_a_4827_ = lean_ctor_get(v___x_4826_, 0);
lean_inc(v_a_4827_);
lean_dec_ref_known(v___x_4826_, 1);
v___x_4828_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__2, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__2_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__2);
v___x_4829_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4829_, 0, v_a_4827_);
v___x_4830_ = lean_box(0);
v___x_4831_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_4828_, v___x_4829_, v___f_4825_, v___x_4830_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_, v_a_4813_);
return v___x_4831_;
}
else
{
lean_object* v_a_4832_; lean_object* v___x_4834_; uint8_t v_isShared_4835_; uint8_t v_isSharedCheck_4839_; 
lean_dec_ref(v___f_4825_);
v_a_4832_ = lean_ctor_get(v___x_4826_, 0);
v_isSharedCheck_4839_ = !lean_is_exclusive(v___x_4826_);
if (v_isSharedCheck_4839_ == 0)
{
v___x_4834_ = v___x_4826_;
v_isShared_4835_ = v_isSharedCheck_4839_;
goto v_resetjp_4833_;
}
else
{
lean_inc(v_a_4832_);
lean_dec(v___x_4826_);
v___x_4834_ = lean_box(0);
v_isShared_4835_ = v_isSharedCheck_4839_;
goto v_resetjp_4833_;
}
v_resetjp_4833_:
{
lean_object* v___x_4837_; 
if (v_isShared_4835_ == 0)
{
v___x_4837_ = v___x_4834_;
goto v_reusejp_4836_;
}
else
{
lean_object* v_reuseFailAlloc_4838_; 
v_reuseFailAlloc_4838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4838_, 0, v_a_4832_);
v___x_4837_ = v_reuseFailAlloc_4838_;
goto v_reusejp_4836_;
}
v_reusejp_4836_:
{
return v___x_4837_;
}
}
}
}
else
{
lean_dec(v___x_4822_);
lean_dec(v_tk_4820_);
lean_dec_ref(v_dec_4806_);
lean_dec(v_stx_4805_);
return v___x_4823_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___boxed(lean_object* v_stx_4840_, lean_object* v_dec_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_){
_start:
{
lean_object* v_res_4850_; 
v_res_4850_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg(v_stx_4840_, v_dec_4841_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_);
lean_dec(v_a_4848_);
lean_dec_ref(v_a_4847_);
lean_dec(v_a_4846_);
lean_dec_ref(v_a_4845_);
lean_dec(v_a_4844_);
lean_dec_ref(v_a_4843_);
lean_dec_ref(v_a_4842_);
return v_res_4850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1(){
_start:
{
lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; 
v___x_4856_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4857_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4));
v___x_4858_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1___closed__1));
v___x_4859_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___boxed), 10, 0);
v___x_4860_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4856_, v___x_4857_, v___x_4858_, v___x_4859_);
return v___x_4860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1___boxed(lean_object* v_a_4861_){
_start:
{
lean_object* v_res_4862_; 
v_res_4862_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1();
return v_res_4862_;
}
}
lean_object* runtime_initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_TCP(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Idbg(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_TCP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Idbg(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
lean_object* initialize_Std_Async_TCP(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Idbg(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Async_TCP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Idbg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Idbg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Idbg(builtin);
}
#ifdef __cplusplus
}
#endif
