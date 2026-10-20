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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___boxed(lean_object*, lean_object*);
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
lean_object* v_a_1172_; lean_object* v___x_1173_; 
v_a_1172_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_1172_);
lean_dec_ref_known(v___x_786_, 1);
v___x_1173_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f(v_a_1172_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
lean_dec(v_j_776_);
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1176_ = v___x_1173_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1173_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
else
{
lean_object* v_a_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v_a_1182_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v___x_1173_, 1);
v___x_1183_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__4));
v___x_1184_ = l_Lean_Json_getObjVal_x3f(v_j_776_, v___x_1183_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_dec(v_a_1182_);
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1184_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1184_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1194_; 
v_a_1193_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_a_1193_);
lean_dec_ref_known(v___x_1184_, 1);
v___x_1194_ = l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f_spec__0(v_a_1193_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
lean_dec(v_a_1182_);
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1194_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1194_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v_a_1203_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1203_);
lean_dec_ref_known(v___x_1194_, 1);
v___x_1204_ = lean_array_to_list(v_a_1203_);
v___x_1205_ = lean_box(0);
v___x_1206_ = l_List_mapM_loop___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f_spec__0(v___x_1204_, v___x_1205_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
lean_dec(v_a_1182_);
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1206_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1206_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1223_; 
v_a_1215_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1217_ = v___x_1206_;
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1206_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1221_; 
v___x_1219_ = l_Lean_Expr_const___override(v_a_1182_, v_a_1215_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1219_);
v___x_1221_ = v___x_1217_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1219_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
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
lean_object* v_a_1224_; lean_object* v___x_1225_; 
lean_dec(v_j_776_);
v_a_1224_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_1224_);
lean_dec_ref_known(v___x_784_, 1);
v___x_1225_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_levelFromJson_x3f(v_a_1224_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1225_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1225_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1242_; 
v_a_1234_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1236_ = v___x_1225_;
v_isShared_1237_ = v_isSharedCheck_1242_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1225_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1242_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1238_; lean_object* v___x_1240_; 
v___x_1238_ = l_Lean_Expr_sort___override(v_a_1234_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 0, v___x_1238_);
v___x_1240_ = v___x_1236_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1244_; 
lean_dec(v_j_776_);
v_a_1243_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_1243_);
lean_dec_ref_known(v___x_782_, 1);
v___x_1244_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f(v_a_1243_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1244_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1244_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1261_; 
v_a_1253_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1255_ = v___x_1244_;
v_isShared_1256_ = v_isSharedCheck_1261_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1244_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1261_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1257_ = l_Lean_Expr_mvar___override(v_a_1253_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 0, v___x_1257_);
v___x_1259_ = v___x_1255_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1263_; 
lean_dec(v_j_776_);
v_a_1262_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_1262_);
lean_dec_ref_known(v___x_780_, 1);
v___x_1263_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_nameFromJson_x3f(v_a_1262_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1263_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1263_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1280_; 
v_a_1272_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1274_ = v___x_1263_;
v_isShared_1275_ = v_isSharedCheck_1280_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1263_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1280_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1276_ = l_Lean_Expr_fvar___override(v_a_1272_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1276_);
v___x_1278_ = v___x_1274_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1282_; 
lean_dec(v_j_776_);
v_a_1281_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_a_1281_);
lean_dec_ref_known(v___x_778_, 1);
v___x_1282_ = l_Lean_Json_getNat_x3f(v_a_1281_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1299_; 
v_a_1291_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1293_ = v___x_1282_;
v_isShared_1294_ = v_isSharedCheck_1299_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1282_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1299_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1295_; lean_object* v___x_1297_; 
v___x_1295_ = l_Lean_Expr_bvar___override(v_a_1291_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v___x_1295_);
v___x_1297_ = v___x_1293_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1295_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
}
}
LEAN_EXPORT uint16_t l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgPort(lean_object* v_siteId_1300_){
_start:
{
uint64_t v_h_1301_; uint64_t v___x_1302_; uint64_t v___x_1303_; uint64_t v___x_1304_; uint64_t v___x_1305_; uint16_t v___x_1306_; 
v_h_1301_ = lean_string_hash(v_siteId_1300_);
v___x_1302_ = 55535ULL;
v___x_1303_ = lean_uint64_mod(v_h_1301_, v___x_1302_);
v___x_1304_ = 10000ULL;
v___x_1305_ = lean_uint64_add(v___x_1303_, v___x_1304_);
v___x_1306_ = lean_uint64_to_uint16(v___x_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgPort___boxed(lean_object* v_siteId_1307_){
_start:
{
uint16_t v_res_1308_; lean_object* v_r_1309_; 
v_res_1308_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgPort(v_siteId_1307_);
lean_dec_ref(v_siteId_1307_);
v_r_1309_ = lean_box(v_res_1308_);
return v_r_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___lam__0(lean_object* v___x_1310_, lean_object* v_x_1311_){
_start:
{
if (lean_obj_tag(v_x_1311_) == 0)
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = lean_mk_io_user_error(v___x_1310_);
v___x_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
return v___x_1313_;
}
else
{
lean_object* v_val_1314_; 
lean_dec_ref(v___x_1310_);
v_val_1314_ = lean_ctor_get(v_x_1311_, 0);
lean_inc(v_val_1314_);
return v_val_1314_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___lam__0___boxed(lean_object* v___x_1315_, lean_object* v_x_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___lam__0(v___x_1315_, v_x_1316_);
lean_dec(v_x_1316_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___lam__1(lean_object* v___f_1318_, lean_object* v_x_1319_){
_start:
{
if (lean_obj_tag(v_x_1319_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1329_; 
lean_dec_ref(v___f_1318_);
v_a_1321_ = lean_ctor_get(v_x_1319_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_x_1319_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1323_ = v_x_1319_;
v_isShared_1324_ = v_isSharedCheck_1329_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v_x_1319_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1329_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
return v___x_1327_;
}
}
}
else
{
lean_object* v_a_1330_; 
v_a_1330_ = lean_ctor_get(v_x_1319_, 0);
lean_inc(v_a_1330_);
lean_dec_ref_known(v_x_1319_, 1);
if (lean_obj_tag(v_a_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1339_; 
lean_dec_ref(v___f_1318_);
v_a_1331_ = lean_ctor_get(v_a_1330_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v_a_1330_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1333_ = v_a_1330_;
v_isShared_1334_ = v_isSharedCheck_1339_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v_a_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1339_;
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
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1331_);
v___x_1336_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
return v___x_1337_;
}
}
}
else
{
lean_object* v_a_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v_a_1340_ = lean_ctor_get(v_a_1330_, 0);
lean_inc(v_a_1340_);
lean_dec_ref_known(v_a_1330_, 1);
v___x_1341_ = lean_io_promise_result_opt(v_a_1340_);
lean_dec(v_a_1340_);
v___x_1342_ = lean_unsigned_to_nat(0u);
v___x_1343_ = 0;
v___x_1344_ = lean_task_map(v___f_1318_, v___x_1341_, v___x_1342_, v___x_1343_);
v___x_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
return v___x_1345_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___lam__1___boxed(lean_object* v___f_1346_, lean_object* v_x_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___lam__1(v___f_1346_, v_x_1347_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg(lean_object* v_client_1356_, lean_object* v_msg_1357_){
_start:
{
lean_object* v_bytes_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v_header_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___f_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; lean_object* v_val_1373_; lean_object* v___x_1382_; 
v_bytes_1359_ = lean_string_to_utf8(v_msg_1357_);
v___x_1360_ = lean_byte_array_size(v_bytes_1359_);
v___x_1361_ = l_Nat_reprFast(v___x_1360_);
v___x_1362_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___closed__0));
v___x_1363_ = lean_string_append(v___x_1361_, v___x_1362_);
v_header_1364_ = lean_string_to_utf8(v___x_1363_);
v___x_1365_ = lean_unsigned_to_nat(2u);
v___x_1366_ = lean_mk_empty_array_with_capacity(v___x_1365_);
v___x_1367_ = lean_array_push(v___x_1366_, v_header_1364_);
v___x_1368_ = lean_array_push(v___x_1367_, v_bytes_1359_);
v___f_1369_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___closed__3));
v___x_1370_ = lean_unsigned_to_nat(0u);
v___x_1371_ = 0;
v___x_1382_ = lean_uv_tcp_send(v_client_1356_, v___x_1368_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v___x_1382_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1382_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
lean_ctor_set_tag(v___x_1385_, 1);
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
v_val_1373_ = v___x_1388_;
goto v___jp_1372_;
}
}
}
else
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
v_a_1391_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1382_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1382_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set_tag(v___x_1393_, 0);
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
v_val_1373_ = v___x_1396_;
goto v___jp_1372_;
}
}
}
v___jp_1372_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1374_, 0, v_val_1373_);
v___x_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
v___x_1376_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1370_, v___x_1371_, v___x_1375_, v___f_1369_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref_known(v___x_1376_, 1);
v___x_1378_ = lean_task_pure(v_a_1377_);
v___x_1379_ = l_Std_Async_AsyncTask_block___redArg(v___x_1378_);
return v___x_1379_;
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1381_; 
v_a_1380_ = lean_ctor_get(v___x_1376_, 0);
lean_inc_ref(v_a_1380_);
lean_dec_ref_known(v___x_1376_, 1);
v___x_1381_ = l_Std_Async_AsyncTask_block___redArg(v_a_1380_);
return v___x_1381_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___boxed(lean_object* v_client_1399_, lean_object* v_msg_1400_, lean_object* v_a_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg(v_client_1399_, v_msg_1400_);
lean_dec(v_client_1399_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___lam__1(lean_object* v___f_1403_, lean_object* v_x_1404_){
_start:
{
if (lean_obj_tag(v_x_1404_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1414_; 
lean_dec_ref(v___f_1403_);
v_a_1406_ = lean_ctor_get(v_x_1404_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_x_1404_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1408_ = v_x_1404_;
v_isShared_1409_ = v_isSharedCheck_1414_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v_x_1404_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1414_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1406_);
v___x_1411_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1412_; 
v___x_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
return v___x_1412_;
}
}
}
else
{
lean_object* v_a_1415_; 
v_a_1415_ = lean_ctor_get(v_x_1404_, 0);
lean_inc(v_a_1415_);
lean_dec_ref_known(v_x_1404_, 1);
if (lean_obj_tag(v_a_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1424_; 
lean_dec_ref(v___f_1403_);
v_a_1416_ = lean_ctor_get(v_a_1415_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v_a_1415_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1418_ = v_a_1415_;
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v_a_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1422_; 
v___x_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
return v___x_1422_;
}
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v_a_1425_ = lean_ctor_get(v_a_1415_, 0);
lean_inc(v_a_1425_);
lean_dec_ref_known(v_a_1415_, 1);
v___x_1426_ = lean_io_promise_result_opt(v_a_1425_);
lean_dec(v_a_1425_);
v___x_1427_ = lean_unsigned_to_nat(0u);
v___x_1428_ = 0;
v___x_1429_ = lean_task_map(v___f_1403_, v___x_1426_, v___x_1427_, v___x_1428_);
v___x_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
return v___x_1430_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___lam__1___boxed(lean_object* v___f_1431_, lean_object* v_x_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___lam__1(v___f_1431_, v_x_1432_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___lam__0(lean_object* v___x_1435_, lean_object* v_x_1436_){
_start:
{
if (lean_obj_tag(v_x_1436_) == 0)
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = lean_mk_io_user_error(v___x_1435_);
v___x_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
return v___x_1438_;
}
else
{
lean_object* v_val_1439_; 
lean_dec_ref(v___x_1435_);
v_val_1439_ = lean_ctor_get(v_x_1436_, 0);
lean_inc(v_val_1439_);
return v_val_1439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___lam__0___boxed(lean_object* v___x_1440_, lean_object* v_x_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___lam__0(v___x_1440_, v_x_1441_);
lean_dec(v_x_1441_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg(lean_object* v_client_1450_, lean_object* v_a_1451_){
_start:
{
lean_object* v___y_1454_; uint8_t v___y_1455_; uint8_t v___x_1464_; lean_object* v_a_1466_; uint64_t v___x_1493_; lean_object* v___f_1494_; lean_object* v___x_1495_; uint8_t v___x_1496_; lean_object* v_val_1498_; lean_object* v___x_1505_; 
v___x_1464_ = 0;
v___x_1493_ = 1ULL;
v___f_1494_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___closed__3));
v___x_1495_ = lean_unsigned_to_nat(0u);
v___x_1496_ = 0;
v___x_1505_ = lean_uv_tcp_recv(v_client_1450_, v___x_1493_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1505_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1505_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
lean_ctor_set_tag(v___x_1508_, 1);
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
v_val_1498_ = v___x_1511_;
goto v___jp_1497_;
}
}
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
v_a_1514_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1505_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1505_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
lean_ctor_set_tag(v___x_1516_, 0);
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
v_val_1498_ = v___x_1519_;
goto v___jp_1497_;
}
}
}
v___jp_1453_:
{
uint8_t v___x_1456_; uint8_t v___x_1457_; 
v___x_1456_ = 10;
v___x_1457_ = lean_uint8_dec_eq(v___y_1455_, v___x_1456_);
if (v___x_1457_ == 0)
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1458_ = lean_unsigned_to_nat(0u);
v___x_1459_ = lean_byte_array_size(v_a_1451_);
v___x_1460_ = lean_byte_array_size(v___y_1454_);
v___x_1461_ = lean_byte_array_copy_slice(v___y_1454_, v___x_1458_, v_a_1451_, v___x_1459_, v___x_1460_, v___x_1457_);
lean_dec_ref(v___y_1454_);
v_a_1451_ = v___x_1461_;
goto _start;
}
else
{
lean_object* v___x_1463_; 
lean_dec_ref(v___y_1454_);
v___x_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1463_, 0, v_a_1451_);
return v___x_1463_;
}
}
v___jp_1465_:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Std_Async_AsyncTask_block___redArg(v_a_1466_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1484_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1470_ = v___x_1467_;
v_isShared_1471_ = v_isSharedCheck_1484_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1467_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1484_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
if (lean_obj_tag(v_a_1468_) == 1)
{
lean_object* v_val_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; uint8_t v___x_1475_; 
lean_del_object(v___x_1470_);
v_val_1472_ = lean_ctor_get(v_a_1468_, 0);
lean_inc(v_val_1472_);
lean_dec_ref_known(v_a_1468_, 1);
v___x_1473_ = lean_unsigned_to_nat(0u);
v___x_1474_ = lean_byte_array_size(v_val_1472_);
v___x_1475_ = lean_nat_dec_lt(v___x_1473_, v___x_1474_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; lean_object* v___x_1477_; uint8_t v___x_1478_; 
v___x_1476_ = lean_box(v___x_1464_);
v___x_1477_ = l_outOfBounds___redArg(v___x_1476_);
lean_dec(v___x_1476_);
v___x_1478_ = lean_unbox(v___x_1477_);
lean_dec(v___x_1477_);
v___y_1454_ = v_val_1472_;
v___y_1455_ = v___x_1478_;
goto v___jp_1453_;
}
else
{
uint8_t v___x_1479_; 
v___x_1479_ = lean_byte_array_fget(v_val_1472_, v___x_1473_);
v___y_1454_ = v_val_1472_;
v___y_1455_ = v___x_1479_;
goto v___jp_1453_;
}
}
else
{
lean_object* v___x_1480_; lean_object* v___x_1482_; 
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1451_);
v___x_1480_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___closed__1));
if (v_isShared_1471_ == 0)
{
lean_ctor_set_tag(v___x_1470_, 1);
lean_ctor_set(v___x_1470_, 0, v___x_1480_);
v___x_1482_ = v___x_1470_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1480_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec_ref(v_a_1451_);
v_a_1485_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1467_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1467_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
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
v___jp_1497_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1499_, 0, v_val_1498_);
v___x_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
v___x_1501_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1495_, v___x_1496_, v___x_1500_, v___f_1494_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; lean_object* v___x_1503_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_a_1502_);
lean_dec_ref_known(v___x_1501_, 1);
v___x_1503_ = lean_task_pure(v_a_1502_);
v_a_1466_ = v___x_1503_;
goto v___jp_1465_;
}
else
{
lean_object* v_a_1504_; 
v_a_1504_ = lean_ctor_get(v___x_1501_, 0);
lean_inc_ref(v_a_1504_);
lean_dec_ref_known(v___x_1501_, 1);
v_a_1466_ = v_a_1504_;
goto v___jp_1465_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___boxed(lean_object* v_client_1522_, lean_object* v_a_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg(v_client_1522_, v_a_1523_);
lean_dec(v_client_1522_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__1___redArg(lean_object* v_val_1526_, lean_object* v_client_1527_, lean_object* v_a_1528_){
_start:
{
lean_object* v_a_1531_; lean_object* v___x_1557_; uint8_t v___x_1558_; 
v___x_1557_ = lean_byte_array_size(v_a_1528_);
v___x_1558_ = lean_nat_dec_lt(v___x_1557_, v_val_1526_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1559_, 0, v_a_1528_);
return v___x_1559_;
}
else
{
lean_object* v___x_1560_; uint64_t v___x_1561_; lean_object* v___f_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; lean_object* v_val_1566_; lean_object* v___x_1573_; 
v___x_1560_ = lean_nat_sub(v_val_1526_, v___x_1557_);
v___x_1561_ = lean_uint64_of_nat(v___x_1560_);
lean_dec(v___x_1560_);
v___f_1562_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___closed__3));
v___x_1563_ = lean_unsigned_to_nat(0u);
v___x_1564_ = 0;
v___x_1573_ = lean_uv_tcp_recv(v_client_1527_, v___x_1561_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1573_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1573_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
lean_ctor_set_tag(v___x_1576_, 1);
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
v_val_1566_ = v___x_1579_;
goto v___jp_1565_;
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
v_a_1582_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1573_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1573_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
lean_ctor_set_tag(v___x_1584_, 0);
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
v_val_1566_ = v___x_1587_;
goto v___jp_1565_;
}
}
}
v___jp_1565_:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1567_, 0, v_val_1566_);
v___x_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
v___x_1569_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1563_, v___x_1564_, v___x_1568_, v___f_1562_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1571_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___x_1569_, 1);
v___x_1571_ = lean_task_pure(v_a_1570_);
v_a_1531_ = v___x_1571_;
goto v___jp_1530_;
}
else
{
lean_object* v_a_1572_; 
v_a_1572_ = lean_ctor_get(v___x_1569_, 0);
lean_inc_ref(v_a_1572_);
lean_dec_ref_known(v___x_1569_, 1);
v_a_1531_ = v_a_1572_;
goto v___jp_1530_;
}
}
}
v___jp_1530_:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Std_Async_AsyncTask_block___redArg(v_a_1531_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1548_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1535_ = v___x_1532_;
v_isShared_1536_ = v_isSharedCheck_1548_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1532_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1548_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
if (lean_obj_tag(v_a_1533_) == 1)
{
lean_object* v_val_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; uint8_t v___x_1541_; lean_object* v___x_1542_; 
lean_del_object(v___x_1535_);
v_val_1537_ = lean_ctor_get(v_a_1533_, 0);
lean_inc(v_val_1537_);
lean_dec_ref_known(v_a_1533_, 1);
v___x_1538_ = lean_unsigned_to_nat(0u);
v___x_1539_ = lean_byte_array_size(v_a_1528_);
v___x_1540_ = lean_byte_array_size(v_val_1537_);
v___x_1541_ = 0;
v___x_1542_ = lean_byte_array_copy_slice(v_val_1537_, v___x_1538_, v_a_1528_, v___x_1539_, v___x_1540_, v___x_1541_);
lean_dec(v_val_1537_);
v_a_1528_ = v___x_1542_;
goto _start;
}
else
{
lean_object* v___x_1544_; lean_object* v___x_1546_; 
lean_dec(v_a_1533_);
lean_dec_ref(v_a_1528_);
v___x_1544_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg___closed__1));
if (v_isShared_1536_ == 0)
{
lean_ctor_set_tag(v___x_1535_, 1);
lean_ctor_set(v___x_1535_, 0, v___x_1544_);
v___x_1546_ = v___x_1535_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1544_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
lean_dec_ref(v_a_1528_);
v_a_1549_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1532_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1532_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1549_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__1___redArg___boxed(lean_object* v_val_1590_, lean_object* v_client_1591_, lean_object* v_a_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__1___redArg(v_val_1590_, v_client_1591_, v_a_1592_);
lean_dec(v_client_1591_);
lean_dec(v_val_1590_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg(lean_object* v_client_1604_){
_start:
{
lean_object* v_header_1606_; lean_object* v___x_1607_; 
v_header_1606_ = l_ByteArray_empty;
v___x_1607_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg(v_client_1604_, v_header_1606_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1650_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1610_ = v___x_1607_;
v_isShared_1611_ = v_isSharedCheck_1650_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1607_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1650_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
uint8_t v___x_1612_; 
v___x_1612_ = lean_string_validate_utf8(v_a_1608_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; lean_object* v___x_1615_; 
lean_dec(v_a_1608_);
v___x_1613_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___closed__1));
if (v_isShared_1611_ == 0)
{
lean_ctor_set_tag(v___x_1610_, 1);
lean_ctor_set(v___x_1610_, 0, v___x_1613_);
v___x_1615_ = v___x_1610_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1613_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
else
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1617_ = lean_string_from_utf8_unchecked(v_a_1608_);
v___x_1618_ = lean_unsigned_to_nat(0u);
v___x_1619_ = lean_string_utf8_byte_size(v___x_1617_);
v___x_1620_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1617_);
lean_ctor_set(v___x_1620_, 1, v___x_1618_);
lean_ctor_set(v___x_1620_, 2, v___x_1619_);
v___x_1621_ = l_String_Slice_toNat_x3f(v___x_1620_);
lean_dec_ref_known(v___x_1620_, 3);
if (lean_obj_tag(v___x_1621_) == 1)
{
lean_object* v_val_1622_; lean_object* v___x_1623_; 
lean_del_object(v___x_1610_);
v_val_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_val_1622_);
lean_dec_ref_known(v___x_1621_, 1);
v___x_1623_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__1___redArg(v_val_1622_, v_client_1604_, v_header_1606_);
lean_dec(v_val_1622_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1637_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1626_ = v___x_1623_;
v_isShared_1627_ = v_isSharedCheck_1637_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1623_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1637_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
uint8_t v___x_1628_; 
v___x_1628_ = lean_string_validate_utf8(v_a_1624_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; lean_object* v___x_1631_; 
lean_dec(v_a_1624_);
v___x_1629_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___closed__3));
if (v_isShared_1627_ == 0)
{
lean_ctor_set_tag(v___x_1626_, 1);
lean_ctor_set(v___x_1626_, 0, v___x_1629_);
v___x_1631_ = v___x_1626_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
else
{
lean_object* v___x_1633_; lean_object* v___x_1635_; 
v___x_1633_ = lean_string_from_utf8_unchecked(v_a_1624_);
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 0, v___x_1633_);
v___x_1635_ = v___x_1626_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1633_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
v_a_1638_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1623_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1623_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
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
lean_object* v___x_1646_; lean_object* v___x_1648_; 
lean_dec(v___x_1621_);
v___x_1646_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___closed__5));
if (v_isShared_1611_ == 0)
{
lean_ctor_set_tag(v___x_1610_, 1);
lean_ctor_set(v___x_1610_, 0, v___x_1646_);
v___x_1648_ = v___x_1610_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1646_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
v_a_1651_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1607_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1607_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg___boxed(lean_object* v_client_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg(v_client_1659_);
lean_dec(v_client_1659_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0(lean_object* v_client_1662_, lean_object* v_inst_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___redArg(v_client_1662_, v_a_1664_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0___boxed(lean_object* v_client_1667_, lean_object* v_inst_1668_, lean_object* v_a_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__0(v_client_1667_, v_inst_1668_, v_a_1669_);
lean_dec(v_client_1667_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__1(lean_object* v_val_1672_, lean_object* v_client_1673_, lean_object* v_inst_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__1___redArg(v_val_1672_, v_client_1673_, v_a_1675_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__1___boxed(lean_object* v_val_1678_, lean_object* v_client_1679_, lean_object* v_inst_1680_, lean_object* v_a_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg_spec__1(v_val_1678_, v_client_1679_, v_inst_1680_, v_a_1681_);
lean_dec(v_client_1679_);
lean_dec(v_val_1678_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___lam__0(lean_object* v___y_1684_){
_start:
{
if (lean_obj_tag(v___y_1684_) == 0)
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
v_a_1685_ = lean_ctor_get(v___y_1684_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___y_1684_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___y_1684_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___y_1684_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
v_a_1693_ = lean_ctor_get(v___y_1684_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___y_1684_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___y_1684_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___y_1684_);
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
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___lam__3(lean_object* v___x_1701_, lean_object* v_x_1702_){
_start:
{
if (lean_obj_tag(v_x_1702_) == 0)
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = lean_mk_io_user_error(v___x_1701_);
v___x_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1703_);
return v___x_1704_;
}
else
{
lean_object* v_val_1705_; 
lean_dec_ref(v___x_1701_);
v_val_1705_ = lean_ctor_get(v_x_1702_, 0);
lean_inc(v_val_1705_);
return v_val_1705_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___lam__3___boxed(lean_object* v___x_1706_, lean_object* v_x_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___lam__3(v___x_1706_, v_x_1707_);
lean_dec(v_x_1707_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___lam__1(lean_object* v___f_1709_, lean_object* v_x_1710_){
_start:
{
if (lean_obj_tag(v_x_1710_) == 0)
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1720_; 
lean_dec_ref(v___f_1709_);
v_a_1712_ = lean_ctor_get(v_x_1710_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v_x_1710_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1714_ = v_x_1710_;
v_isShared_1715_ = v_isSharedCheck_1720_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v_x_1710_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1720_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
lean_object* v___x_1718_; 
v___x_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1717_);
return v___x_1718_;
}
}
}
else
{
lean_object* v_a_1721_; 
v_a_1721_ = lean_ctor_get(v_x_1710_, 0);
lean_inc(v_a_1721_);
lean_dec_ref_known(v_x_1710_, 1);
if (lean_obj_tag(v_a_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1730_; 
lean_dec_ref(v___f_1709_);
v_a_1722_ = lean_ctor_get(v_a_1721_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_a_1721_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1724_ = v_a_1721_;
v_isShared_1725_ = v_isSharedCheck_1730_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v_a_1721_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1730_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1722_);
v___x_1727_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_object* v___x_1728_; 
v___x_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1727_);
return v___x_1728_;
}
}
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; uint8_t v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v_a_1731_ = lean_ctor_get(v_a_1721_, 0);
lean_inc(v_a_1731_);
lean_dec_ref_known(v_a_1721_, 1);
v___x_1732_ = lean_io_promise_result_opt(v_a_1731_);
lean_dec(v_a_1731_);
v___x_1733_ = lean_unsigned_to_nat(0u);
v___x_1734_ = 0;
v___x_1735_ = lean_task_map(v___f_1709_, v___x_1732_, v___x_1733_, v___x_1734_);
v___x_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
return v___x_1736_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___lam__1___boxed(lean_object* v___f_1737_, lean_object* v_x_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___lam__1(v___f_1737_, v_x_1738_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer_spec__0___redArg(lean_object* v_addr_1741_, lean_object* v_as_x27_1742_, lean_object* v_b_1743_){
_start:
{
if (lean_obj_tag(v_as_x27_1742_) == 0)
{
lean_object* v___x_1745_; 
lean_dec_ref(v_addr_1741_);
v___x_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1745_, 0, v_b_1743_);
return v___x_1745_;
}
else
{
lean_object* v_tail_1746_; lean_object* v___x_1751_; 
v_tail_1746_ = lean_ctor_get(v_as_x27_1742_, 1);
v___x_1751_ = lean_uv_tcp_new();
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1778_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1754_ = v___x_1751_;
v_isShared_1755_ = v_isSharedCheck_1778_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1751_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1778_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
lean_inc_ref(v_addr_1741_);
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 0, v_addr_1741_);
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_addr_1741_);
v___x_1757_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
lean_object* v___x_1758_; 
v___x_1758_ = lean_uv_tcp_bind(v_a_1752_, v___x_1757_);
lean_dec_ref(v___x_1757_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1775_; 
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1775_ == 0)
{
lean_object* v_unused_1776_; 
v_unused_1776_ = lean_ctor_get(v___x_1758_, 0);
lean_dec(v_unused_1776_);
v___x_1760_ = v___x_1758_;
v_isShared_1761_ = v_isSharedCheck_1775_;
goto v_resetjp_1759_;
}
else
{
lean_dec(v___x_1758_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1775_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
uint32_t v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = 1;
v___x_1763_ = lean_uv_tcp_listen(v_a_1752_, v___x_1762_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1773_; 
lean_dec(v_b_1743_);
lean_dec_ref(v_addr_1741_);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1773_ == 0)
{
lean_object* v_unused_1774_; 
v_unused_1774_ = lean_ctor_get(v___x_1763_, 0);
lean_dec(v_unused_1774_);
v___x_1765_ = v___x_1763_;
v_isShared_1766_ = v_isSharedCheck_1773_;
goto v_resetjp_1764_;
}
else
{
lean_dec(v___x_1763_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1773_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1761_ == 0)
{
lean_ctor_set_tag(v___x_1760_, 1);
lean_ctor_set(v___x_1760_, 0, v_a_1752_);
v___x_1768_ = v___x_1760_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_a_1752_);
v___x_1768_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
lean_object* v___x_1770_; 
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1768_);
v___x_1770_ = v___x_1765_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1768_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1763_, 1);
lean_del_object(v___x_1760_);
lean_dec(v_a_1752_);
goto v___jp_1747_;
}
}
}
else
{
lean_dec_ref_known(v___x_1758_, 1);
lean_dec(v_a_1752_);
goto v___jp_1747_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1751_, 1);
goto v___jp_1747_;
}
v___jp_1747_:
{
uint32_t v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = 100;
v___x_1749_ = l_IO_sleep(v___x_1748_);
v_as_x27_1742_ = v_tail_1746_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer_spec__0___redArg___boxed(lean_object* v_addr_1779_, lean_object* v_as_x27_1780_, lean_object* v_b_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer_spec__0___redArg(v_addr_1779_, v_as_x27_1780_, v_b_1781_);
lean_dec(v_as_x27_1780_);
return v_res_1783_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__1(void){
_start:
{
uint8_t v___x_1785_; uint8_t v___x_1786_; uint8_t v___x_1787_; lean_object* v___x_1788_; 
v___x_1785_ = 1;
v___x_1786_ = 0;
v___x_1787_ = 127;
v___x_1788_ = l_Std_Net_IPv4Addr_ofParts(v___x_1787_, v___x_1786_, v___x_1786_, v___x_1785_);
return v___x_1788_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__2(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = lean_unsigned_to_nat(100u);
v___x_1790_ = l_List_range(v___x_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer(lean_object* v_siteId_1795_, lean_object* v_exprJson_1796_){
_start:
{
lean_object* v___y_1799_; lean_object* v_a_1800_; uint8_t v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v_val_1824_; lean_object* v_a_1832_; lean_object* v_a_1884_; lean_object* v___f_1886_; uint16_t v_port_1887_; lean_object* v___x_1888_; lean_object* v_addr_1889_; lean_object* v_server_x3f_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1951_; 
v___f_1886_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__0));
v_port_1887_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgPort(v_siteId_1795_);
v___x_1888_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__1, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__1_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__1);
v_addr_1889_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_addr_1889_, 0, v___x_1888_);
lean_ctor_set_uint16(v_addr_1889_, sizeof(void*)*1, v_port_1887_);
v_server_x3f_1890_ = lean_box(0);
v___x_1891_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__2, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__2_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__2);
v___x_1892_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer_spec__0___redArg(v_addr_1889_, v___x_1891_, v_server_x3f_1890_);
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1951_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1951_;
goto v_resetjp_1894_;
}
v___jp_1798_:
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Std_Async_AsyncTask_block___redArg(v_a_1800_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1809_; 
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1809_ == 0)
{
lean_object* v_unused_1810_; 
v_unused_1810_ = lean_ctor_get(v___x_1801_, 0);
lean_dec(v_unused_1810_);
v___x_1803_ = v___x_1801_;
v_isShared_1804_ = v_isSharedCheck_1809_;
goto v_resetjp_1802_;
}
else
{
lean_dec(v___x_1801_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1809_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1805_; lean_object* v___x_1807_; 
v___x_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1805_, 0, v___y_1799_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v___x_1805_);
v___x_1807_ = v___x_1803_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1805_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec_ref(v___y_1799_);
v_a_1811_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1801_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1801_);
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
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
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
}
v___jp_1819_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1825_, 0, v_val_1824_);
v___x_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
lean_inc_ref(v___y_1822_);
v___x_1827_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___y_1821_, v___y_1820_, v___x_1826_, v___y_1822_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; lean_object* v___x_1829_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_a_1828_);
lean_dec_ref_known(v___x_1827_, 1);
v___x_1829_ = lean_task_pure(v_a_1828_);
v___y_1799_ = v___y_1823_;
v_a_1800_ = v___x_1829_;
goto v___jp_1798_;
}
else
{
lean_object* v_a_1830_; 
v_a_1830_ = lean_ctor_get(v___x_1827_, 0);
lean_inc_ref(v_a_1830_);
lean_dec_ref_known(v___x_1827_, 1);
v___y_1799_ = v___y_1823_;
v_a_1800_ = v_a_1830_;
goto v___jp_1798_;
}
}
v___jp_1831_:
{
lean_object* v___x_1833_; 
v___x_1833_ = l_Std_Async_AsyncTask_block___redArg(v_a_1832_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1834_);
lean_dec_ref_known(v___x_1833_, 1);
v___x_1835_ = l_Lean_Json_compress(v_exprJson_1796_);
v___x_1836_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg(v_a_1834_, v___x_1835_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v___x_1837_; 
lean_dec_ref_known(v___x_1836_, 1);
v___x_1837_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg(v_a_1834_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___f_1839_; lean_object* v___x_1840_; uint8_t v___x_1841_; lean_object* v___x_1842_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_a_1838_);
lean_dec_ref_known(v___x_1837_, 1);
v___f_1839_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg___closed__3));
v___x_1840_ = lean_unsigned_to_nat(0u);
v___x_1841_ = 0;
v___x_1842_ = lean_uv_tcp_shutdown(v_a_1834_);
lean_dec(v_a_1834_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1842_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1842_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
lean_ctor_set_tag(v___x_1845_, 1);
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
v___y_1820_ = v___x_1841_;
v___y_1821_ = v___x_1840_;
v___y_1822_ = v___f_1839_;
v___y_1823_ = v_a_1838_;
v_val_1824_ = v___x_1848_;
goto v___jp_1819_;
}
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
v_a_1851_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1842_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1842_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
lean_ctor_set_tag(v___x_1853_, 0);
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
v___y_1820_ = v___x_1841_;
v___y_1821_ = v___x_1840_;
v___y_1822_ = v___f_1839_;
v___y_1823_ = v_a_1838_;
v_val_1824_ = v___x_1856_;
goto v___jp_1819_;
}
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_dec(v_a_1834_);
v_a_1859_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1837_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1837_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
lean_dec(v_a_1834_);
v_a_1867_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1836_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1836_);
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
lean_dec(v_exprJson_1796_);
v_a_1875_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1833_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1833_);
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
v___jp_1883_:
{
lean_object* v___x_1885_; 
v___x_1885_ = lean_task_pure(v_a_1884_);
v_a_1832_ = v___x_1885_;
goto v___jp_1831_;
}
v_resetjp_1894_:
{
if (lean_obj_tag(v_a_1893_) == 1)
{
lean_object* v_val_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1947_; 
lean_del_object(v___x_1895_);
v_val_1897_ = lean_ctor_get(v_a_1893_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v_a_1893_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1899_ = v_a_1893_;
v_isShared_1900_ = v_isSharedCheck_1947_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_val_1897_);
lean_dec(v_a_1893_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1947_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___f_1901_; lean_object* v___x_1902_; uint8_t v___x_1903_; lean_object* v_val_1905_; lean_object* v___x_1930_; 
v___f_1901_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__4));
v___x_1902_ = lean_unsigned_to_nat(0u);
v___x_1903_ = 0;
v___x_1930_ = lean_uv_tcp_accept(v_val_1897_);
lean_dec(v_val_1897_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1930_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1930_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set_tag(v___x_1933_, 1);
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
v_val_1905_ = v___x_1936_;
goto v___jp_1904_;
}
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
v_a_1939_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1930_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1930_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
lean_ctor_set_tag(v___x_1941_, 0);
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
v_val_1905_ = v___x_1944_;
goto v___jp_1904_;
}
}
}
v___jp_1904_:
{
lean_object* v___x_1907_; 
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v_val_1905_);
v___x_1907_ = v___x_1899_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_val_1905_);
v___x_1907_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
v___x_1909_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1902_, v___x_1903_, v___x_1908_, v___f_1901_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_a_1910_);
lean_dec_ref_known(v___x_1909_, 1);
if (lean_obj_tag(v_a_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
v_a_1911_ = lean_ctor_get(v_a_1910_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v_a_1910_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v_a_1910_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v_a_1910_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
v_a_1884_ = v___x_1916_;
goto v___jp_1883_;
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
v_a_1919_ = lean_ctor_get(v_a_1910_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v_a_1910_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v_a_1910_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v_a_1910_);
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
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
v_a_1884_ = v___x_1924_;
goto v___jp_1883_;
}
}
}
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1928_; 
v_a_1927_ = lean_ctor_get(v___x_1909_, 0);
lean_inc_ref(v_a_1927_);
lean_dec_ref_known(v___x_1909_, 1);
v___x_1928_ = lean_task_map(v___f_1886_, v_a_1927_, v___x_1902_, v___x_1903_);
v_a_1832_ = v___x_1928_;
goto v___jp_1831_;
}
}
}
}
}
else
{
lean_object* v___x_1949_; 
lean_dec(v_a_1893_);
lean_dec(v_exprJson_1796_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 0, v_server_x3f_1890_);
v___x_1949_ = v___x_1895_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_server_x3f_1890_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___boxed(lean_object* v_siteId_1952_, lean_object* v_exprJson_1953_, lean_object* v_a_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer(v_siteId_1952_, v_exprJson_1953_);
lean_dec_ref(v_siteId_1952_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer_spec__0(lean_object* v_addr_1956_, lean_object* v_as_1957_, lean_object* v_as_x27_1958_, lean_object* v_b_1959_, lean_object* v_a_1960_){
_start:
{
lean_object* v___x_1962_; 
v___x_1962_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer_spec__0___redArg(v_addr_1956_, v_as_x27_1958_, v_b_1959_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer_spec__0___boxed(lean_object* v_addr_1963_, lean_object* v_as_1964_, lean_object* v_as_x27_1965_, lean_object* v_b_1966_, lean_object* v_a_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer_spec__0(v_addr_1963_, v_as_1964_, v_as_x27_1965_, v_b_1966_, v_a_1967_);
lean_dec(v_as_x27_1965_);
lean_dec(v_as_1964_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgLoadEnv(lean_object* v_imports_1972_){
_start:
{
lean_object* v___x_1974_; uint32_t v___x_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; uint8_t v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1974_ = l_Lean_Options_empty;
v___x_1975_ = 0;
v___x_1976_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgLoadEnv___closed__0));
v___x_1977_ = 0;
v___x_1978_ = 2;
v___x_1979_ = lean_box(1);
lean_inc_ref(v_imports_1972_);
v___x_1980_ = l_Lean_importModules(v_imports_1972_, v___x_1974_, v___x_1975_, v___x_1976_, v___x_1977_, v___x_1977_, v___x_1978_, v___x_1979_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_dec_ref(v_imports_1972_);
return v___x_1980_;
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
lean_dec_ref_known(v___x_1980_, 1);
v___x_1981_ = lean_array_pop(v_imports_1972_);
v___x_1982_ = l_Lean_importModules(v___x_1981_, v___x_1974_, v___x_1975_, v___x_1976_, v___x_1977_, v___x_1977_, v___x_1978_, v___x_1979_);
return v___x_1982_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgLoadEnv___boxed(lean_object* v_imports_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgLoadEnv(v_imports_1983_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval_unsafe__1___redArg(lean_object* v_name_1986_, lean_object* v_env_x27_1987_){
_start:
{
lean_object* v___x_1988_; uint8_t v___x_1989_; lean_object* v___x_1990_; 
v___x_1988_ = l_Lean_Options_empty;
v___x_1989_ = 0;
v___x_1990_ = l_Lean_Environment_evalConst___redArg(v_env_x27_1987_, v___x_1988_, v_name_1986_, v___x_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval_unsafe__1___redArg___boxed(lean_object* v_name_1991_, lean_object* v_env_x27_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval_unsafe__1___redArg(v_name_1991_, v_env_x27_1992_);
lean_dec_ref(v_env_x27_1992_);
lean_dec(v_name_1991_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval_unsafe__1(lean_object* v_00_u03b1_1994_, lean_object* v_name_1995_, lean_object* v_env_x27_1996_){
_start:
{
lean_object* v___x_1997_; uint8_t v___x_1998_; lean_object* v___x_1999_; 
v___x_1997_ = l_Lean_Options_empty;
v___x_1998_ = 0;
v___x_1999_ = l_Lean_Environment_evalConst___redArg(v_env_x27_1996_, v___x_1997_, v_name_1995_, v___x_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval_unsafe__1___boxed(lean_object* v_00_u03b1_2000_, lean_object* v_name_2001_, lean_object* v_env_x27_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval_unsafe__1(v_00_u03b1_2000_, v_name_2001_, v_env_x27_2002_);
lean_dec_ref(v_env_x27_2002_);
lean_dec(v_name_2001_);
return v_res_2003_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__4(void){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2011_ = l_Lean_Options_empty;
v___x_2012_ = l_Lean_Core_getMaxHeartbeats(v___x_2011_);
return v___x_2012_;
}
}
static uint16_t _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__5(void){
_start:
{
lean_object* v___x_2013_; uint16_t v___x_2014_; 
v___x_2013_ = l_Lean_Options_empty;
v___x_2014_ = l_Lean_OptionFlags_ofOptions(v___x_2013_);
return v___x_2014_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__6(void){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2015_ = lean_unsigned_to_nat(1u);
v___x_2016_ = l_Lean_firstFrontendMacroScope;
v___x_2017_ = lean_nat_add(v___x_2016_, v___x_2015_);
return v___x_2017_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__11(void){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2028_ = lean_unsigned_to_nat(32u);
v___x_2029_ = lean_mk_empty_array_with_capacity(v___x_2028_);
v___x_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
return v___x_2030_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12(void){
_start:
{
size_t v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2031_ = ((size_t)5ULL);
v___x_2032_ = lean_unsigned_to_nat(0u);
v___x_2033_ = lean_unsigned_to_nat(32u);
v___x_2034_ = lean_mk_empty_array_with_capacity(v___x_2033_);
v___x_2035_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__11, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__11_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__11);
v___x_2036_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
lean_ctor_set(v___x_2036_, 1, v___x_2034_);
lean_ctor_set(v___x_2036_, 2, v___x_2032_);
lean_ctor_set(v___x_2036_, 3, v___x_2032_);
lean_ctor_set_usize(v___x_2036_, 4, v___x_2031_);
return v___x_2036_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__13(void){
_start:
{
lean_object* v___x_2037_; uint64_t v___x_2038_; lean_object* v___x_2039_; 
v___x_2037_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12);
v___x_2038_ = 0ULL;
v___x_2039_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2039_, 0, v___x_2037_);
lean_ctor_set_uint64(v___x_2039_, sizeof(void*)*1, v___x_2038_);
return v___x_2039_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__14(void){
_start:
{
lean_object* v___x_2040_; 
v___x_2040_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2040_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__15(void){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2041_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__14, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__14_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__14);
v___x_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2041_);
return v___x_2042_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__16(void){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__15, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__15_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__15);
v___x_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2043_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
return v___x_2044_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__18(void){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2047_ = lean_unsigned_to_nat(0u);
v___x_2048_ = l_Lean_Options_empty;
v___x_2049_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__17));
v___x_2050_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2049_);
lean_ctor_set(v___x_2050_, 1, v___x_2048_);
lean_ctor_set(v___x_2050_, 2, v___x_2049_);
lean_ctor_set(v___x_2050_, 3, v___x_2047_);
lean_ctor_set(v___x_2050_, 4, v___x_2047_);
lean_ctor_set(v___x_2050_, 5, v___x_2047_);
return v___x_2050_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__19(void){
_start:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2051_ = l_Lean_NameSet_empty;
v___x_2052_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12);
v___x_2053_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
lean_ctor_set(v___x_2053_, 1, v___x_2052_);
lean_ctor_set(v___x_2053_, 2, v___x_2051_);
return v___x_2053_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__20(void){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; uint8_t v___x_2056_; lean_object* v___x_2057_; 
v___x_2054_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12);
v___x_2055_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__15, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__15_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__15);
v___x_2056_ = 1;
v___x_2057_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2057_, 0, v___x_2055_);
lean_ctor_set(v___x_2057_, 1, v___x_2055_);
lean_ctor_set(v___x_2057_, 2, v___x_2054_);
lean_ctor_set_uint8(v___x_2057_, sizeof(void*)*3, v___x_2056_);
return v___x_2057_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__21(void){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2058_ = l_Lean_maxRecDepth;
v___x_2059_ = l_Lean_Options_empty;
v___x_2060_ = l_Lean_KVMap_instValueNat;
v___x_2061_ = l_Lean_Option_get___redArg(v___x_2060_, v___x_2059_, v___x_2058_);
return v___x_2061_;
}
}
static uint16_t _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__26(void){
_start:
{
uint16_t v___x_2066_; uint16_t v___x_2067_; uint16_t v___x_2068_; 
v___x_2066_ = 512;
v___x_2067_ = lean_uint16_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__5, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__5_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__5);
v___x_2068_ = lean_uint16_land(v___x_2067_, v___x_2066_);
return v___x_2068_;
}
}
static uint8_t _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__27(void){
_start:
{
uint16_t v___x_2069_; uint16_t v___x_2070_; uint8_t v___x_2071_; 
v___x_2069_ = 0;
v___x_2070_ = lean_uint16_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__26, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__26_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__26);
v___x_2071_ = lean_uint16_dec_eq(v___x_2070_, v___x_2069_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg(lean_object* v_env_2072_, lean_object* v_type_2073_, lean_object* v_value_2074_){
_start:
{
lean_object* v_a_2077_; lean_object* v_name_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; uint8_t v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v_decl_2087_; uint8_t v___x_2088_; uint8_t v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; uint16_t v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___y_2115_; lean_object* v___x_2167_; uint8_t v___y_2169_; lean_object* v_env_2190_; uint8_t v___x_2191_; uint8_t v___x_2192_; 
v_name_2080_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__1));
v___x_2081_ = lean_box(0);
v___x_2082_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2082_, 0, v_name_2080_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
lean_ctor_set(v___x_2082_, 2, v_type_2073_);
v___x_2083_ = lean_box(0);
v___x_2084_ = 0;
v___x_2085_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__2));
v___x_2086_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2086_, 0, v___x_2082_);
lean_ctor_set(v___x_2086_, 1, v_value_2074_);
lean_ctor_set(v___x_2086_, 2, v___x_2083_);
lean_ctor_set(v___x_2086_, 3, v___x_2085_);
lean_ctor_set_uint8(v___x_2086_, sizeof(void*)*4, v___x_2084_);
v_decl_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_decl_2087_, 0, v___x_2086_);
v___x_2088_ = 1;
v___x_2089_ = 0;
v___x_2090_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__3));
v___x_2091_ = l_Lean_instInhabitedFileMap_default;
v___x_2092_ = l_Lean_Options_empty;
v___x_2093_ = lean_box(0);
v___x_2094_ = lean_unsigned_to_nat(0u);
v___x_2095_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__4, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__4_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__4);
v___x_2096_ = l_Lean_firstFrontendMacroScope;
v___x_2097_ = lean_box(0);
v___x_2098_ = lean_box(0);
v___x_2099_ = lean_uint16_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__5, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__5_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__5);
v___x_2100_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__6, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__6_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__6);
v___x_2101_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__9));
v___x_2102_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__10));
v___x_2103_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__13, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__13_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__13);
v___x_2104_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__16, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__16_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__16);
v___x_2105_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__17));
v___x_2106_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__18, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__18_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__18);
v___x_2107_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__19, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__19_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__19);
v___x_2108_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__20, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__20_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__20);
v___x_2109_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2109_, 0, v_env_2072_);
lean_ctor_set(v___x_2109_, 1, v___x_2100_);
lean_ctor_set(v___x_2109_, 2, v___x_2101_);
lean_ctor_set(v___x_2109_, 3, v___x_2102_);
lean_ctor_set(v___x_2109_, 4, v___x_2103_);
lean_ctor_set(v___x_2109_, 5, v___x_2104_);
lean_ctor_set(v___x_2109_, 6, v___x_2106_);
lean_ctor_set(v___x_2109_, 7, v___x_2107_);
lean_ctor_set(v___x_2109_, 8, v___x_2108_);
lean_ctor_set(v___x_2109_, 9, v___x_2105_);
v___x_2110_ = lean_io_get_num_heartbeats();
v___x_2111_ = lean_st_mk_ref(v___x_2109_);
v___x_2112_ = l_Lean_inheritedTraceOptions;
v___x_2113_ = lean_st_ref_get(v___x_2112_);
v___x_2167_ = lean_st_ref_get(v___x_2111_);
v_env_2190_ = lean_ctor_get(v___x_2167_, 0);
lean_inc_ref(v_env_2190_);
lean_dec(v___x_2167_);
v___x_2191_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2190_);
lean_dec_ref(v_env_2190_);
v___x_2192_ = lean_uint8_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__27, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__27_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__27);
if (v___x_2192_ == 0)
{
if (v___x_2191_ == 0)
{
v___y_2169_ = v___x_2088_;
goto v___jp_2168_;
}
else
{
lean_inc(v___x_2111_);
v___y_2115_ = v___x_2111_;
goto v___jp_2114_;
}
}
else
{
if (v___x_2191_ == 0)
{
lean_inc(v___x_2111_);
v___y_2115_ = v___x_2111_;
goto v___jp_2114_;
}
else
{
v___y_2169_ = v___x_2089_;
goto v___jp_2168_;
}
}
v___jp_2076_:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = lean_mk_io_user_error(v_a_2077_);
v___x_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
return v___x_2079_;
}
v___jp_2114_:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2116_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__21, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__21_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__21);
v___x_2117_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2090_);
lean_ctor_set(v___x_2117_, 1, v___x_2091_);
lean_ctor_set(v___x_2117_, 2, v___x_2092_);
lean_ctor_set(v___x_2117_, 3, v___x_2116_);
lean_ctor_set(v___x_2117_, 4, v___x_2093_);
lean_ctor_set(v___x_2117_, 5, v___x_2081_);
lean_ctor_set(v___x_2117_, 6, v___x_2110_);
lean_ctor_set(v___x_2117_, 7, v___x_2095_);
lean_ctor_set(v___x_2117_, 8, v___x_2093_);
lean_ctor_set(v___x_2117_, 9, v___x_2096_);
lean_ctor_set(v___x_2117_, 10, v___x_2097_);
lean_ctor_set(v___x_2117_, 11, v___x_2113_);
v___x_2118_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
lean_ctor_set(v___x_2118_, 1, v___x_2094_);
lean_ctor_set(v___x_2118_, 2, v___x_2098_);
lean_ctor_set_uint16(v___x_2118_, sizeof(void*)*3, v___x_2099_);
lean_ctor_set_uint8(v___x_2118_, sizeof(void*)*3 + 2, v___x_2089_);
lean_ctor_set_uint8(v___x_2118_, sizeof(void*)*3 + 3, v___x_2089_);
v___x_2119_ = l_Lean_addAndCompile(v_decl_2087_, v___x_2088_, v___x_2089_, v___x_2118_, v___y_2115_);
lean_dec(v___y_2115_);
lean_dec_ref_known(v___x_2118_, 3);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2143_; 
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2143_ == 0)
{
lean_object* v_unused_2144_; 
v_unused_2144_ = lean_ctor_get(v___x_2119_, 0);
lean_dec(v_unused_2144_);
v___x_2121_ = v___x_2119_;
v_isShared_2122_ = v_isSharedCheck_2143_;
goto v_resetjp_2120_;
}
else
{
lean_dec(v___x_2119_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2143_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2123_; lean_object* v_env_2124_; lean_object* v___x_2125_; 
v___x_2123_ = lean_st_ref_get(v___x_2111_);
lean_dec(v___x_2111_);
v_env_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc_ref(v_env_2124_);
lean_dec(v___x_2123_);
v___x_2125_ = l_Lean_Environment_evalConst___redArg(v_env_2124_, v___x_2092_, v_name_2080_, v___x_2089_);
lean_dec_ref(v_env_2124_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2138_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2128_ = v___x_2125_;
v_isShared_2129_ = v_isSharedCheck_2138_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2125_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2138_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2133_; 
v___x_2130_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__22));
v___x_2131_ = lean_string_append(v___x_2130_, v_a_2126_);
lean_dec(v_a_2126_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set_tag(v___x_2128_, 18);
lean_ctor_set(v___x_2128_, 0, v___x_2131_);
v___x_2133_ = v___x_2128_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
lean_object* v___x_2135_; 
if (v_isShared_2122_ == 0)
{
lean_ctor_set_tag(v___x_2121_, 1);
lean_ctor_set(v___x_2121_, 0, v___x_2133_);
v___x_2135_ = v___x_2121_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2133_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2141_; 
v_a_2139_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v___x_2125_, 1);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v_a_2139_);
v___x_2141_ = v___x_2121_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2139_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2166_; 
lean_dec(v___x_2111_);
v_a_2145_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2147_ = v___x_2119_;
v_isShared_2148_ = v_isSharedCheck_2166_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2119_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2166_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
if (lean_obj_tag(v_a_2145_) == 0)
{
lean_object* v_msg_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2153_; 
v_msg_2149_ = lean_ctor_get(v_a_2145_, 1);
lean_inc_ref(v_msg_2149_);
lean_dec_ref_known(v_a_2145_, 2);
v___x_2150_ = l_Lean_MessageData_toString(v_msg_2149_);
v___x_2151_ = lean_mk_io_user_error(v___x_2150_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 0, v___x_2151_);
v___x_2153_ = v___x_2147_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2151_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
else
{
lean_object* v_id_2155_; lean_object* v___x_2156_; 
lean_del_object(v___x_2147_);
v_id_2155_ = lean_ctor_get(v_a_2145_, 0);
lean_inc(v_id_2155_);
lean_dec_ref_known(v_a_2145_, 2);
v___x_2156_ = l_Lean_InternalExceptionId_getName(v_id_2155_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
lean_dec(v_id_2155_);
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2157_);
lean_dec_ref_known(v___x_2156_, 1);
v___x_2158_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__23));
v___x_2159_ = l_Lean_Name_toString(v_a_2157_, v___x_2088_);
v___x_2160_ = lean_string_append(v___x_2158_, v___x_2159_);
lean_dec_ref(v___x_2159_);
v_a_2077_ = v___x_2160_;
goto v___jp_2076_;
}
else
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
lean_dec_ref_known(v___x_2156_, 1);
v___x_2161_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__24));
v___x_2162_ = l_Nat_reprFast(v_id_2155_);
v___x_2163_ = lean_string_append(v___x_2161_, v___x_2162_);
lean_dec_ref(v___x_2162_);
v___x_2164_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__25));
v___x_2165_ = lean_string_append(v___x_2163_, v___x_2164_);
v_a_2077_ = v___x_2165_;
goto v___jp_2076_;
}
}
}
}
}
v___jp_2168_:
{
lean_object* v___x_2170_; lean_object* v_env_2171_; lean_object* v_nextMacroScope_2172_; lean_object* v_ngen_2173_; lean_object* v_auxDeclNGen_2174_; lean_object* v_traceState_2175_; lean_object* v_recordedDeps_2176_; lean_object* v_messages_2177_; lean_object* v_infoState_2178_; lean_object* v_snapshotTasks_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2188_; 
v___x_2170_ = lean_st_ref_take(v___x_2111_);
v_env_2171_ = lean_ctor_get(v___x_2170_, 0);
v_nextMacroScope_2172_ = lean_ctor_get(v___x_2170_, 1);
v_ngen_2173_ = lean_ctor_get(v___x_2170_, 2);
v_auxDeclNGen_2174_ = lean_ctor_get(v___x_2170_, 3);
v_traceState_2175_ = lean_ctor_get(v___x_2170_, 4);
v_recordedDeps_2176_ = lean_ctor_get(v___x_2170_, 6);
v_messages_2177_ = lean_ctor_get(v___x_2170_, 7);
v_infoState_2178_ = lean_ctor_get(v___x_2170_, 8);
v_snapshotTasks_2179_ = lean_ctor_get(v___x_2170_, 9);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2188_ == 0)
{
lean_object* v_unused_2189_; 
v_unused_2189_ = lean_ctor_get(v___x_2170_, 5);
lean_dec(v_unused_2189_);
v___x_2181_ = v___x_2170_;
v_isShared_2182_ = v_isSharedCheck_2188_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_snapshotTasks_2179_);
lean_inc(v_infoState_2178_);
lean_inc(v_messages_2177_);
lean_inc(v_recordedDeps_2176_);
lean_inc(v_traceState_2175_);
lean_inc(v_auxDeclNGen_2174_);
lean_inc(v_ngen_2173_);
lean_inc(v_nextMacroScope_2172_);
lean_inc(v_env_2171_);
lean_dec(v___x_2170_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2188_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2183_; lean_object* v___x_2185_; 
v___x_2183_ = l_Lean_Kernel_enableDiag(v_env_2171_, v___y_2169_);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 5, v___x_2104_);
lean_ctor_set(v___x_2181_, 0, v___x_2183_);
v___x_2185_ = v___x_2181_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2183_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_nextMacroScope_2172_);
lean_ctor_set(v_reuseFailAlloc_2187_, 2, v_ngen_2173_);
lean_ctor_set(v_reuseFailAlloc_2187_, 3, v_auxDeclNGen_2174_);
lean_ctor_set(v_reuseFailAlloc_2187_, 4, v_traceState_2175_);
lean_ctor_set(v_reuseFailAlloc_2187_, 5, v___x_2104_);
lean_ctor_set(v_reuseFailAlloc_2187_, 6, v_recordedDeps_2176_);
lean_ctor_set(v_reuseFailAlloc_2187_, 7, v_messages_2177_);
lean_ctor_set(v_reuseFailAlloc_2187_, 8, v_infoState_2178_);
lean_ctor_set(v_reuseFailAlloc_2187_, 9, v_snapshotTasks_2179_);
v___x_2185_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
lean_object* v___x_2186_; 
v___x_2186_ = lean_st_ref_put(v___x_2111_, v___x_2185_);
lean_inc(v___x_2111_);
v___y_2115_ = v___x_2111_;
goto v___jp_2114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___boxed(lean_object* v_env_2193_, lean_object* v_type_2194_, lean_object* v_value_2195_, lean_object* v_a_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg(v_env_2193_, v_type_2194_, v_value_2195_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval(lean_object* v_00_u03b1_2198_, lean_object* v_inst_2199_, lean_object* v_env_2200_, lean_object* v_type_2201_, lean_object* v_value_2202_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg(v_env_2200_, v_type_2201_, v_value_2202_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___boxed(lean_object* v_00_u03b1_2205_, lean_object* v_inst_2206_, lean_object* v_env_2207_, lean_object* v_type_2208_, lean_object* v_value_2209_, lean_object* v_a_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval(v_00_u03b1_2205_, v_inst_2206_, v_env_2207_, v_type_2208_, v_value_2209_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(lean_object* v_e_2212_){
_start:
{
if (lean_obj_tag(v_e_2212_) == 0)
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2222_; 
v_a_2214_ = lean_ctor_get(v_e_2212_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v_e_2212_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2216_ = v_e_2212_;
v_isShared_2217_ = v_isSharedCheck_2222_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v_e_2212_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2222_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2218_; lean_object* v___x_2220_; 
v___x_2218_ = lean_mk_io_user_error(v_a_2214_);
if (v_isShared_2217_ == 0)
{
lean_ctor_set_tag(v___x_2216_, 1);
lean_ctor_set(v___x_2216_, 0, v___x_2218_);
v___x_2220_ = v___x_2216_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2218_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
v_a_2223_ = lean_ctor_get(v_e_2212_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_e_2212_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v_e_2212_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v_e_2212_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
lean_ctor_set_tag(v___x_2225_, 0);
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg___boxed(lean_object* v_e_2231_, lean_object* v_a_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v_e_2231_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2(lean_object* v_00_u03b1_2234_, lean_object* v_e_2235_){
_start:
{
lean_object* v___x_2237_; 
v___x_2237_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v_e_2235_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___boxed(lean_object* v_00_u03b1_2238_, lean_object* v_e_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2(v_00_u03b1_2238_, v_e_2239_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__1(lean_object* v___x_2242_, lean_object* v_x_2243_){
_start:
{
if (lean_obj_tag(v_x_2243_) == 0)
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = lean_mk_io_user_error(v___x_2242_);
v___x_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
return v___x_2245_;
}
else
{
lean_object* v_val_2246_; 
lean_dec_ref(v___x_2242_);
v_val_2246_ = lean_ctor_get(v_x_2243_, 0);
lean_inc(v_val_2246_);
return v_val_2246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__1___boxed(lean_object* v___x_2247_, lean_object* v_x_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__1(v___x_2247_, v_x_2248_);
lean_dec(v_x_2248_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__2(lean_object* v___f_2250_, lean_object* v_x_2251_){
_start:
{
if (lean_obj_tag(v_x_2251_) == 0)
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2261_; 
lean_dec_ref(v___f_2250_);
v_a_2253_ = lean_ctor_get(v_x_2251_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v_x_2251_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2255_ = v_x_2251_;
v_isShared_2256_ = v_isSharedCheck_2261_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v_x_2251_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2261_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2253_);
v___x_2258_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
lean_object* v___x_2259_; 
v___x_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
return v___x_2259_;
}
}
}
else
{
lean_object* v_a_2262_; 
v_a_2262_ = lean_ctor_get(v_x_2251_, 0);
lean_inc(v_a_2262_);
lean_dec_ref_known(v_x_2251_, 1);
if (lean_obj_tag(v_a_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2271_; 
lean_dec_ref(v___f_2250_);
v_a_2263_ = lean_ctor_get(v_a_2262_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v_a_2262_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2265_ = v_a_2262_;
v_isShared_2266_ = v_isSharedCheck_2271_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v_a_2262_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2271_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
lean_object* v___x_2269_; 
v___x_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
return v___x_2269_;
}
}
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; uint8_t v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v_a_2272_ = lean_ctor_get(v_a_2262_, 0);
lean_inc(v_a_2272_);
lean_dec_ref_known(v_a_2262_, 1);
v___x_2273_ = lean_io_promise_result_opt(v_a_2272_);
lean_dec(v_a_2272_);
v___x_2274_ = lean_unsigned_to_nat(0u);
v___x_2275_ = 0;
v___x_2276_ = lean_task_map(v___f_2250_, v___x_2273_, v___x_2274_, v___x_2275_);
v___x_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
return v___x_2277_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__2___boxed(lean_object* v___f_2278_, lean_object* v_x_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__2(v___f_2278_, v_x_2279_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0___redArg(lean_object* v___x_2282_, lean_object* v___x_2283_, lean_object* v___x_2284_, lean_object* v_a_2285_, lean_object* v_b_2286_){
_start:
{
lean_object* v___x_2287_; 
v___x_2287_ = lean_box(0);
switch(lean_obj_tag(v_a_2285_))
{
case 0:
{
lean_object* v_pos_2288_; lean_object* v___x_2289_; 
v_pos_2288_ = lean_ctor_get(v_a_2285_, 0);
lean_inc(v_pos_2288_);
lean_dec_ref_known(v_a_2285_, 1);
v___x_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2289_, 0, v_pos_2288_);
return v___x_2289_;
}
case 1:
{
lean_object* v_pos_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2299_; 
v_pos_2290_ = lean_ctor_get(v_a_2285_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v_a_2285_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2292_ = v_a_2285_;
v_isShared_2293_ = v_isSharedCheck_2299_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_pos_2290_);
lean_dec(v_a_2285_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2299_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2294_; lean_object* v___x_2296_; 
v___x_2294_ = lean_string_utf8_next_fast(v___x_2282_, v_pos_2290_);
lean_dec(v_pos_2290_);
if (v_isShared_2293_ == 0)
{
lean_ctor_set_tag(v___x_2292_, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2294_);
v___x_2296_ = v___x_2292_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2294_);
v___x_2296_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
v_a_2285_ = v___x_2296_;
v_b_2286_ = v___x_2287_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_2300_; lean_object* v_table_2301_; lean_object* v_stackPos_2302_; lean_object* v_needlePos_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2356_; 
v_needle_2300_ = lean_ctor_get(v_a_2285_, 0);
v_table_2301_ = lean_ctor_get(v_a_2285_, 1);
v_stackPos_2302_ = lean_ctor_get(v_a_2285_, 2);
v_needlePos_2303_ = lean_ctor_get(v_a_2285_, 3);
v_isSharedCheck_2356_ = !lean_is_exclusive(v_a_2285_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2305_ = v_a_2285_;
v_isShared_2306_ = v_isSharedCheck_2356_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_needlePos_2303_);
lean_inc(v_stackPos_2302_);
lean_inc(v_table_2301_);
lean_inc(v_needle_2300_);
lean_dec(v_a_2285_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2356_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v_str_2307_; lean_object* v_startInclusive_2308_; lean_object* v_endExclusive_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; uint8_t v___x_2313_; 
v_str_2307_ = lean_ctor_get(v_needle_2300_, 0);
v_startInclusive_2308_ = lean_ctor_get(v_needle_2300_, 1);
v_endExclusive_2309_ = lean_ctor_get(v_needle_2300_, 2);
v___x_2310_ = lean_nat_sub(v_stackPos_2302_, v_needlePos_2303_);
v___x_2311_ = lean_nat_sub(v_endExclusive_2309_, v_startInclusive_2308_);
v___x_2312_ = lean_nat_add(v___x_2310_, v___x_2311_);
v___x_2313_ = lean_nat_dec_le(v___x_2312_, v___x_2284_);
lean_dec(v___x_2312_);
if (v___x_2313_ == 0)
{
lean_object* v___x_2314_; lean_object* v___x_2315_; uint8_t v___x_2316_; 
lean_dec(v___x_2311_);
lean_del_object(v___x_2305_);
lean_dec(v_needlePos_2303_);
lean_dec(v_stackPos_2302_);
lean_dec_ref(v_table_2301_);
lean_dec_ref(v_needle_2300_);
v___x_2314_ = lean_unsigned_to_nat(1u);
v___x_2315_ = lean_nat_add(v___x_2310_, v___x_2314_);
lean_dec(v___x_2310_);
v___x_2316_ = lean_nat_dec_le(v___x_2315_, v___x_2284_);
lean_dec(v___x_2315_);
if (v___x_2316_ == 0)
{
lean_inc(v_b_2286_);
return v_b_2286_;
}
else
{
lean_object* v___x_2317_; 
v___x_2317_ = lean_box(3);
v_a_2285_ = v___x_2317_;
v_b_2286_ = v___x_2287_;
goto _start;
}
}
else
{
uint8_t v_stackByte_2319_; lean_object* v___x_2320_; uint8_t v_patByte_2321_; uint8_t v___x_2322_; 
lean_dec(v___x_2310_);
lean_inc(v_stackPos_2302_);
v_stackByte_2319_ = lean_string_get_byte_fast(v___x_2282_, v_stackPos_2302_);
v___x_2320_ = lean_nat_add(v_startInclusive_2308_, v_needlePos_2303_);
v_patByte_2321_ = lean_string_get_byte_fast(v_str_2307_, v___x_2320_);
v___x_2322_ = lean_uint8_dec_eq(v_stackByte_2319_, v_patByte_2321_);
if (v___x_2322_ == 0)
{
lean_object* v___x_2323_; uint8_t v_decide_2324_; 
lean_dec(v___x_2311_);
v___x_2323_ = lean_unsigned_to_nat(0u);
v_decide_2324_ = lean_nat_dec_eq(v_needlePos_2303_, v___x_2323_);
if (v_decide_2324_ == 0)
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v_newNeedlePos_2327_; uint8_t v___x_2328_; 
v___x_2325_ = lean_unsigned_to_nat(1u);
v___x_2326_ = lean_nat_sub(v_needlePos_2303_, v___x_2325_);
lean_dec(v_needlePos_2303_);
v_newNeedlePos_2327_ = lean_array_fget_borrowed(v_table_2301_, v___x_2326_);
lean_dec(v___x_2326_);
v___x_2328_ = lean_nat_dec_eq(v_newNeedlePos_2327_, v___x_2323_);
if (v___x_2328_ == 0)
{
lean_object* v___x_2330_; 
lean_inc(v_newNeedlePos_2327_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 3, v_newNeedlePos_2327_);
v___x_2330_ = v___x_2305_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_needle_2300_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_table_2301_);
lean_ctor_set(v_reuseFailAlloc_2332_, 2, v_stackPos_2302_);
lean_ctor_set(v_reuseFailAlloc_2332_, 3, v_newNeedlePos_2327_);
v___x_2330_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
v_a_2285_ = v___x_2330_;
v_b_2286_ = v___x_2287_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_2333_; lean_object* v___x_2335_; 
v_nextStackPos_2333_ = l_String_Slice_posGE___redArg(v___x_2283_, v_stackPos_2302_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 3, v___x_2323_);
lean_ctor_set(v___x_2305_, 2, v_nextStackPos_2333_);
v___x_2335_ = v___x_2305_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_needle_2300_);
lean_ctor_set(v_reuseFailAlloc_2337_, 1, v_table_2301_);
lean_ctor_set(v_reuseFailAlloc_2337_, 2, v_nextStackPos_2333_);
lean_ctor_set(v_reuseFailAlloc_2337_, 3, v___x_2323_);
v___x_2335_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
v_a_2285_ = v___x_2335_;
v_b_2286_ = v___x_2287_;
goto _start;
}
}
}
else
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v_nextStackPos_2340_; lean_object* v___x_2342_; 
lean_dec(v_needlePos_2303_);
v___x_2338_ = lean_unsigned_to_nat(1u);
v___x_2339_ = lean_nat_add(v_stackPos_2302_, v___x_2338_);
lean_dec(v_stackPos_2302_);
v_nextStackPos_2340_ = l_String_Slice_posGE___redArg(v___x_2283_, v___x_2339_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 3, v___x_2323_);
lean_ctor_set(v___x_2305_, 2, v_nextStackPos_2340_);
v___x_2342_ = v___x_2305_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_needle_2300_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v_table_2301_);
lean_ctor_set(v_reuseFailAlloc_2344_, 2, v_nextStackPos_2340_);
lean_ctor_set(v_reuseFailAlloc_2344_, 3, v___x_2323_);
v___x_2342_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
v_a_2285_ = v___x_2342_;
v_b_2286_ = v___x_2287_;
goto _start;
}
}
}
else
{
lean_object* v___x_2345_; lean_object* v_nextStackPos_2346_; lean_object* v_nextNeedlePos_2347_; uint8_t v_decide_2348_; 
v___x_2345_ = lean_unsigned_to_nat(1u);
v_nextStackPos_2346_ = lean_nat_add(v_stackPos_2302_, v___x_2345_);
lean_dec(v_stackPos_2302_);
v_nextNeedlePos_2347_ = lean_nat_add(v_needlePos_2303_, v___x_2345_);
lean_dec(v_needlePos_2303_);
v_decide_2348_ = lean_nat_dec_eq(v_nextNeedlePos_2347_, v___x_2311_);
lean_dec(v___x_2311_);
if (v_decide_2348_ == 0)
{
lean_object* v___x_2350_; 
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 3, v_nextNeedlePos_2347_);
lean_ctor_set(v___x_2305_, 2, v_nextStackPos_2346_);
v___x_2350_ = v___x_2305_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_needle_2300_);
lean_ctor_set(v_reuseFailAlloc_2352_, 1, v_table_2301_);
lean_ctor_set(v_reuseFailAlloc_2352_, 2, v_nextStackPos_2346_);
lean_ctor_set(v_reuseFailAlloc_2352_, 3, v_nextNeedlePos_2347_);
v___x_2350_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
v_a_2285_ = v___x_2350_;
goto _start;
}
}
else
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
lean_del_object(v___x_2305_);
lean_dec_ref(v_table_2301_);
lean_dec_ref(v_needle_2300_);
v___x_2353_ = lean_nat_sub(v_nextStackPos_2346_, v_nextNeedlePos_2347_);
lean_dec(v_nextNeedlePos_2347_);
lean_dec(v_nextStackPos_2346_);
v___x_2354_ = l_String_Slice_pos_x21(v___x_2283_, v___x_2353_);
lean_dec(v___x_2353_);
v___x_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2354_);
return v___x_2355_;
}
}
}
}
}
default: 
{
lean_inc(v_b_2286_);
return v_b_2286_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0___redArg___boxed(lean_object* v___x_2357_, lean_object* v___x_2358_, lean_object* v___x_2359_, lean_object* v_a_2360_, lean_object* v_b_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0___redArg(v___x_2357_, v___x_2358_, v___x_2359_, v_a_2360_, v_b_2361_);
lean_dec(v_b_2361_);
lean_dec(v___x_2359_);
lean_dec_ref(v___x_2358_);
lean_dec_ref(v___x_2357_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__0(lean_object* v_____r_2363_){
_start:
{
uint32_t v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2365_ = 500;
v___x_2366_ = l_IO_sleep(v___x_2365_);
v___x_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__0___boxed(lean_object* v_____r_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__0(v_____r_2368_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1_spec__1(lean_object* v_s_2371_){
_start:
{
lean_object* v___x_2373_; lean_object* v_putStr_2374_; lean_object* v___x_2375_; 
v___x_2373_ = lean_get_stderr();
v_putStr_2374_ = lean_ctor_get(v___x_2373_, 4);
lean_inc_ref(v_putStr_2374_);
lean_dec_ref(v___x_2373_);
v___x_2375_ = lean_apply_2(v_putStr_2374_, v_s_2371_, lean_box(0));
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1_spec__1___boxed(lean_object* v_s_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1_spec__1(v_s_2376_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1(lean_object* v_s_2379_){
_start:
{
uint32_t v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2381_ = 10;
v___x_2382_ = lean_string_push(v_s_2379_, v___x_2381_);
v___x_2383_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1_spec__1(v___x_2382_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1___boxed(lean_object* v_s_2384_, lean_object* v_a_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1(v_s_2384_);
return v_res_2386_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2392_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__1));
v___x_2393_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_2392_);
return v___x_2393_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2394_ = lean_unsigned_to_nat(0u);
v___x_2395_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__2);
v___x_2396_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__1));
v___x_2397_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2396_);
lean_ctor_set(v___x_2397_, 1, v___x_2395_);
lean_ctor_set(v___x_2397_, 2, v___x_2394_);
lean_ctor_set(v___x_2397_, 3, v___x_2394_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg(lean_object* v_a_2403_, lean_object* v_apply_2404_, lean_object* v___x_2405_){
_start:
{
lean_object* v___y_2408_; lean_object* v___x_2410_; lean_object* v_a_2412_; lean_object* v_a_2427_; lean_object* v___y_2432_; uint8_t v___y_2433_; lean_object* v___y_2434_; lean_object* v_val_2435_; lean_object* v___x_2442_; 
v___x_2410_ = lean_box(0);
v___x_2442_ = lean_uv_tcp_new();
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2533_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2533_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2533_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v_a_2448_; lean_object* v___x_2503_; 
lean_inc_ref(v___x_2405_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 0, v___x_2405_);
v___x_2503_ = v___x_2445_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2405_);
v___x_2503_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2502_;
}
v___jp_2447_:
{
lean_object* v___x_2449_; 
v___x_2449_ = l_Std_Async_AsyncTask_block___redArg(v_a_2448_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v___x_2450_; 
lean_dec_ref_known(v___x_2449_, 1);
v___x_2450_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg(v_a_2443_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_a_2451_);
lean_dec_ref_known(v___x_2450_, 1);
v___x_2452_ = l_Lean_Json_parse(v_a_2451_);
v___x_2453_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_2452_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc_n(v_a_2454_, 2);
lean_dec_ref_known(v___x_2453_, 1);
v___x_2455_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__8));
v___x_2456_ = l_Lean_Json_getObjVal_x3f(v_a_2454_, v___x_2455_);
v___x_2457_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_2456_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_a_2458_);
lean_dec_ref_known(v___x_2457_, 1);
v___x_2459_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f(v_a_2458_);
v___x_2460_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_2459_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_a_2461_);
lean_dec_ref_known(v___x_2460_, 1);
v___x_2462_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__13));
v___x_2463_ = l_Lean_Json_getObjVal_x3f(v_a_2454_, v___x_2462_);
v___x_2464_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_2463_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v_a_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
lean_inc(v_a_2465_);
lean_dec_ref_known(v___x_2464_, 1);
v___x_2466_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f(v_a_2465_);
v___x_2467_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_2466_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; lean_object* v___x_2469_; 
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_a_2468_);
lean_dec_ref_known(v___x_2467_, 1);
lean_inc_ref(v_a_2403_);
v___x_2469_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg(v_a_2403_, v_a_2461_, v_a_2468_);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v_a_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
v_a_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_a_2470_);
lean_dec_ref_known(v___x_2469_, 1);
lean_inc_ref(v_apply_2404_);
v___x_2471_ = lean_apply_1(v_apply_2404_, v_a_2470_);
v___x_2472_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg(v_a_2443_, v___x_2471_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v___f_2473_; lean_object* v___x_2474_; uint8_t v___x_2475_; lean_object* v___x_2476_; 
lean_dec_ref_known(v___x_2472_, 1);
v___f_2473_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__6));
v___x_2474_ = lean_unsigned_to_nat(0u);
v___x_2475_ = 0;
v___x_2476_ = lean_uv_tcp_shutdown(v_a_2443_);
lean_dec(v_a_2443_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2476_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2476_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
lean_ctor_set_tag(v___x_2479_, 1);
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
v___y_2432_ = v___f_2473_;
v___y_2433_ = v___x_2475_;
v___y_2434_ = v___x_2474_;
v_val_2435_ = v___x_2482_;
goto v___jp_2431_;
}
}
}
else
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
v_a_2485_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2476_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2476_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
lean_ctor_set_tag(v___x_2487_, 0);
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
v___y_2432_ = v___f_2473_;
v___y_2433_ = v___x_2475_;
v___y_2434_ = v___x_2474_;
v_val_2435_ = v___x_2490_;
goto v___jp_2431_;
}
}
}
}
else
{
lean_object* v_a_2493_; 
lean_dec(v_a_2443_);
v_a_2493_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_a_2493_);
lean_dec_ref_known(v___x_2472_, 1);
v_a_2412_ = v_a_2493_;
goto v___jp_2411_;
}
}
else
{
lean_object* v_a_2494_; 
lean_dec(v_a_2443_);
v_a_2494_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_a_2494_);
lean_dec_ref_known(v___x_2469_, 1);
v_a_2412_ = v_a_2494_;
goto v___jp_2411_;
}
}
else
{
lean_object* v_a_2495_; 
lean_dec(v_a_2461_);
lean_dec(v_a_2443_);
v_a_2495_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_a_2495_);
lean_dec_ref_known(v___x_2467_, 1);
v_a_2412_ = v_a_2495_;
goto v___jp_2411_;
}
}
else
{
lean_object* v_a_2496_; 
lean_dec(v_a_2461_);
lean_dec(v_a_2443_);
v_a_2496_ = lean_ctor_get(v___x_2464_, 0);
lean_inc(v_a_2496_);
lean_dec_ref_known(v___x_2464_, 1);
v_a_2412_ = v_a_2496_;
goto v___jp_2411_;
}
}
else
{
lean_object* v_a_2497_; 
lean_dec(v_a_2454_);
lean_dec(v_a_2443_);
v_a_2497_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_a_2497_);
lean_dec_ref_known(v___x_2460_, 1);
v_a_2412_ = v_a_2497_;
goto v___jp_2411_;
}
}
else
{
lean_object* v_a_2498_; 
lean_dec(v_a_2454_);
lean_dec(v_a_2443_);
v_a_2498_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_a_2498_);
lean_dec_ref_known(v___x_2457_, 1);
v_a_2412_ = v_a_2498_;
goto v___jp_2411_;
}
}
else
{
lean_object* v_a_2499_; 
lean_dec(v_a_2443_);
v_a_2499_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_a_2499_);
lean_dec_ref_known(v___x_2453_, 1);
v_a_2412_ = v_a_2499_;
goto v___jp_2411_;
}
}
else
{
lean_object* v_a_2500_; 
lean_dec(v_a_2443_);
v_a_2500_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_a_2500_);
lean_dec_ref_known(v___x_2450_, 1);
v_a_2412_ = v_a_2500_;
goto v___jp_2411_;
}
}
else
{
lean_object* v_a_2501_; 
lean_dec(v_a_2443_);
v_a_2501_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2501_);
lean_dec_ref_known(v___x_2449_, 1);
v_a_2412_ = v_a_2501_;
goto v___jp_2411_;
}
}
v_reusejp_2502_:
{
lean_object* v___f_2504_; lean_object* v___x_2505_; uint8_t v___x_2506_; lean_object* v_val_2508_; lean_object* v___x_2515_; 
v___f_2504_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__6));
v___x_2505_ = lean_unsigned_to_nat(0u);
v___x_2506_ = 0;
v___x_2515_ = lean_uv_tcp_connect(v_a_2443_, v___x_2503_);
lean_dec_ref(v___x_2503_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2515_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2515_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
lean_ctor_set_tag(v___x_2518_, 1);
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
v_val_2508_ = v___x_2521_;
goto v___jp_2507_;
}
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
v_a_2524_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2515_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2515_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
lean_ctor_set_tag(v___x_2526_, 0);
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
v_val_2508_ = v___x_2529_;
goto v___jp_2507_;
}
}
}
v___jp_2507_:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2509_, 0, v_val_2508_);
v___x_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
v___x_2511_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2505_, v___x_2506_, v___x_2510_, v___f_2504_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; lean_object* v___x_2513_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2512_);
lean_dec_ref_known(v___x_2511_, 1);
v___x_2513_ = lean_task_pure(v_a_2512_);
v_a_2448_ = v___x_2513_;
goto v___jp_2447_;
}
else
{
lean_object* v_a_2514_; 
v_a_2514_ = lean_ctor_get(v___x_2511_, 0);
lean_inc_ref(v_a_2514_);
lean_dec_ref_known(v___x_2511_, 1);
v_a_2448_ = v_a_2514_;
goto v___jp_2447_;
}
}
}
}
}
else
{
lean_object* v_a_2534_; 
v_a_2534_ = lean_ctor_get(v___x_2442_, 0);
lean_inc(v_a_2534_);
lean_dec_ref_known(v___x_2442_, 1);
v_a_2412_ = v_a_2534_;
goto v___jp_2411_;
}
v___jp_2407_:
{
if (lean_obj_tag(v___y_2408_) == 0)
{
lean_dec_ref_known(v___y_2408_, 1);
goto _start;
}
else
{
lean_dec_ref(v___x_2405_);
lean_dec_ref(v_apply_2404_);
lean_dec_ref(v_a_2403_);
return v___y_2408_;
}
}
v___jp_2411_:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2413_ = lean_io_error_to_string(v_a_2412_);
v___x_2414_ = lean_unsigned_to_nat(0u);
v___x_2415_ = lean_string_utf8_byte_size(v___x_2413_);
lean_inc_ref(v___x_2413_);
v___x_2416_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2413_);
lean_ctor_set(v___x_2416_, 1, v___x_2414_);
lean_ctor_set(v___x_2416_, 2, v___x_2415_);
v___x_2417_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__3);
v___x_2418_ = lean_box(0);
v___x_2419_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0___redArg(v___x_2413_, v___x_2416_, v___x_2415_, v___x_2417_, v___x_2418_);
lean_dec_ref_known(v___x_2416_, 3);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2420_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__4));
v___x_2421_ = lean_string_append(v___x_2420_, v___x_2413_);
lean_dec_ref(v___x_2413_);
v___x_2422_ = l_IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1(v___x_2421_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2423_; lean_object* v___x_2424_; 
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_a_2423_);
lean_dec_ref_known(v___x_2422_, 1);
v___x_2424_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__0(v_a_2423_);
v___y_2408_ = v___x_2424_;
goto v___jp_2407_;
}
else
{
lean_dec_ref(v___x_2405_);
lean_dec_ref(v_apply_2404_);
lean_dec_ref(v_a_2403_);
return v___x_2422_;
}
}
else
{
lean_object* v___x_2425_; 
lean_dec_ref_known(v___x_2419_, 1);
lean_dec_ref(v___x_2413_);
v___x_2425_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__0(v___x_2410_);
v___y_2408_ = v___x_2425_;
goto v___jp_2407_;
}
}
v___jp_2426_:
{
lean_object* v___x_2428_; 
v___x_2428_ = l_Std_Async_AsyncTask_block___redArg(v_a_2427_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_dec_ref_known(v___x_2428_, 1);
goto _start;
}
else
{
lean_object* v_a_2430_; 
v_a_2430_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_a_2430_);
lean_dec_ref_known(v___x_2428_, 1);
v_a_2412_ = v_a_2430_;
goto v___jp_2411_;
}
}
v___jp_2431_:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2436_, 0, v_val_2435_);
v___x_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2436_);
lean_inc_ref(v___y_2432_);
v___x_2438_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___y_2434_, v___y_2433_, v___x_2437_, v___y_2432_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_object* v_a_2439_; lean_object* v___x_2440_; 
v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
lean_inc(v_a_2439_);
lean_dec_ref_known(v___x_2438_, 1);
v___x_2440_ = lean_task_pure(v_a_2439_);
v_a_2427_ = v___x_2440_;
goto v___jp_2426_;
}
else
{
lean_object* v_a_2441_; 
v_a_2441_ = lean_ctor_get(v___x_2438_, 0);
lean_inc_ref(v_a_2441_);
lean_dec_ref_known(v___x_2438_, 1);
v_a_2427_ = v_a_2441_;
goto v___jp_2426_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___boxed(lean_object* v_a_2535_, lean_object* v_apply_2536_, lean_object* v___x_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg(v_a_2535_, v_apply_2536_, v___x_2537_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* lean_idbg_client_loop(lean_object* v_siteId_2540_, lean_object* v_imports_2541_, lean_object* v_apply_2542_){
_start:
{
lean_object* v___x_2544_; 
v___x_2544_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgLoadEnv(v_imports_2541_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; uint16_t v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_a_2545_);
lean_dec_ref_known(v___x_2544_, 1);
v___x_2546_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgPort(v_siteId_2540_);
lean_dec_ref(v_siteId_2540_);
v___x_2547_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__1, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__1_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__1);
v___x_2548_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2548_, 0, v___x_2547_);
lean_ctor_set_uint16(v___x_2548_, sizeof(void*)*1, v___x_2546_);
v___x_2549_ = lean_box(0);
v___x_2550_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg(v_a_2545_, v_apply_2542_, v___x_2548_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2557_; 
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2557_ == 0)
{
lean_object* v_unused_2558_; 
v_unused_2558_ = lean_ctor_get(v___x_2550_, 0);
lean_dec(v_unused_2558_);
v___x_2552_ = v___x_2550_;
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
else
{
lean_dec(v___x_2550_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 0, v___x_2549_);
v___x_2555_ = v___x_2552_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2549_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
else
{
return v___x_2550_;
}
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_dec_ref(v_apply_2542_);
lean_dec_ref(v_siteId_2540_);
v_a_2559_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2544_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2544_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl___boxed(lean_object* v_siteId_2567_, lean_object* v_imports_2568_, lean_object* v_apply_2569_, lean_object* v_a_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = lean_idbg_client_loop(v_siteId_2567_, v_imports_2568_, v_apply_2569_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0(lean_object* v___x_2572_, lean_object* v___x_2573_, lean_object* v___x_2574_, lean_object* v_inst_2575_, lean_object* v_R_2576_, lean_object* v_a_2577_, lean_object* v_b_2578_, lean_object* v_c_2579_){
_start:
{
lean_object* v___x_2580_; 
v___x_2580_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0___redArg(v___x_2572_, v___x_2573_, v___x_2574_, v_a_2577_, v_b_2578_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0___boxed(lean_object* v___x_2581_, lean_object* v___x_2582_, lean_object* v___x_2583_, lean_object* v_inst_2584_, lean_object* v_R_2585_, lean_object* v_a_2586_, lean_object* v_b_2587_, lean_object* v_c_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0(v___x_2581_, v___x_2582_, v___x_2583_, v_inst_2584_, v_R_2585_, v_a_2586_, v_b_2587_, v_c_2588_);
lean_dec(v_b_2587_);
lean_dec(v___x_2583_);
lean_dec_ref(v___x_2582_);
lean_dec_ref(v___x_2581_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3(lean_object* v_a_2590_, lean_object* v_apply_2591_, lean_object* v___x_2592_, lean_object* v_inst_2593_, lean_object* v_a_2594_){
_start:
{
lean_object* v___x_2596_; 
v___x_2596_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg(v_a_2590_, v_apply_2591_, v___x_2592_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___boxed(lean_object* v_a_2597_, lean_object* v_apply_2598_, lean_object* v___x_2599_, lean_object* v_inst_2600_, lean_object* v_a_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3(v_a_2597_, v_apply_2598_, v___x_2599_, v_inst_2600_, v_a_2601_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___redArg(){
_start:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2605_ = l_Lean_Elab_Do_instInhabitedControlInfo_default;
v___x_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2605_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___redArg___boxed(lean_object* v_a_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___redArg();
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg(lean_object* v_x_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_){
_start:
{
lean_object* v___x_2617_; 
v___x_2617_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___redArg();
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___boxed(lean_object* v_x_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg(v_x_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_);
lean_dec(v_a_2624_);
lean_dec_ref(v_a_2623_);
lean_dec(v_a_2622_);
lean_dec_ref(v_a_2621_);
lean_dec(v_a_2620_);
lean_dec_ref(v_a_2619_);
lean_dec(v_x_2618_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1(){
_start:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2669_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2670_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4));
v___x_2671_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__18));
v___x_2672_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___boxed), 8, 0);
v___x_2673_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2669_, v___x_2670_, v___x_2671_, v___x_2672_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___boxed(lean_object* v_a_2674_){
_start:
{
lean_object* v_res_2675_; 
v_res_2675_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1();
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(lean_object* v_e_2676_, lean_object* v___y_2677_){
_start:
{
uint8_t v___x_2679_; 
v___x_2679_ = l_Lean_Expr_hasMVar(v_e_2676_);
if (v___x_2679_ == 0)
{
lean_object* v___x_2680_; 
v___x_2680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2680_, 0, v_e_2676_);
return v___x_2680_;
}
else
{
lean_object* v___x_2681_; lean_object* v_mctx_2682_; lean_object* v___x_2683_; lean_object* v_fst_2684_; lean_object* v_snd_2685_; lean_object* v___x_2686_; lean_object* v_cache_2687_; lean_object* v_zetaDeltaFVarIds_2688_; lean_object* v_postponed_2689_; lean_object* v_diag_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2699_; 
v___x_2681_ = lean_st_ref_get(v___y_2677_);
v_mctx_2682_ = lean_ctor_get(v___x_2681_, 0);
lean_inc_ref(v_mctx_2682_);
lean_dec(v___x_2681_);
v___x_2683_ = l_Lean_instantiateMVarsCore(v_mctx_2682_, v_e_2676_);
v_fst_2684_ = lean_ctor_get(v___x_2683_, 0);
lean_inc(v_fst_2684_);
v_snd_2685_ = lean_ctor_get(v___x_2683_, 1);
lean_inc(v_snd_2685_);
lean_dec_ref(v___x_2683_);
v___x_2686_ = lean_st_ref_take(v___y_2677_);
v_cache_2687_ = lean_ctor_get(v___x_2686_, 1);
v_zetaDeltaFVarIds_2688_ = lean_ctor_get(v___x_2686_, 2);
v_postponed_2689_ = lean_ctor_get(v___x_2686_, 3);
v_diag_2690_ = lean_ctor_get(v___x_2686_, 4);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2699_ == 0)
{
lean_object* v_unused_2700_; 
v_unused_2700_ = lean_ctor_get(v___x_2686_, 0);
lean_dec(v_unused_2700_);
v___x_2692_ = v___x_2686_;
v_isShared_2693_ = v_isSharedCheck_2699_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_diag_2690_);
lean_inc(v_postponed_2689_);
lean_inc(v_zetaDeltaFVarIds_2688_);
lean_inc(v_cache_2687_);
lean_dec(v___x_2686_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2699_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v_snd_2685_);
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_snd_2685_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v_cache_2687_);
lean_ctor_set(v_reuseFailAlloc_2698_, 2, v_zetaDeltaFVarIds_2688_);
lean_ctor_set(v_reuseFailAlloc_2698_, 3, v_postponed_2689_);
lean_ctor_set(v_reuseFailAlloc_2698_, 4, v_diag_2690_);
v___x_2695_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2696_ = lean_st_ref_put(v___y_2677_, v___x_2695_);
v___x_2697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2697_, 0, v_fst_2684_);
return v___x_2697_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg___boxed(lean_object* v_e_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(v_e_2701_, v___y_2702_);
lean_dec(v___y_2702_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3(lean_object* v_e_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v___x_2713_; 
v___x_2713_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(v_e_2705_, v___y_2709_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___boxed(lean_object* v_e_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3(v_e_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___redArg(lean_object* v_lctx_2723_, lean_object* v_x_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v_keyedConfig_2732_; uint8_t v_trackZetaDelta_2733_; lean_object* v_zetaDeltaSet_2734_; lean_object* v_localInstances_2735_; lean_object* v_defEqCtx_x3f_2736_; lean_object* v_synthPendingDepth_2737_; lean_object* v_customCanUnfoldPredicate_x3f_2738_; uint8_t v_univApprox_2739_; uint8_t v_inTypeClassResolution_2740_; uint8_t v_cacheInferType_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
v_keyedConfig_2732_ = lean_ctor_get(v___y_2727_, 0);
v_trackZetaDelta_2733_ = lean_ctor_get_uint8(v___y_2727_, sizeof(void*)*7);
v_zetaDeltaSet_2734_ = lean_ctor_get(v___y_2727_, 1);
v_localInstances_2735_ = lean_ctor_get(v___y_2727_, 3);
v_defEqCtx_x3f_2736_ = lean_ctor_get(v___y_2727_, 4);
v_synthPendingDepth_2737_ = lean_ctor_get(v___y_2727_, 5);
v_customCanUnfoldPredicate_x3f_2738_ = lean_ctor_get(v___y_2727_, 6);
v_univApprox_2739_ = lean_ctor_get_uint8(v___y_2727_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2740_ = lean_ctor_get_uint8(v___y_2727_, sizeof(void*)*7 + 2);
v_cacheInferType_2741_ = lean_ctor_get_uint8(v___y_2727_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_2738_);
lean_inc(v_synthPendingDepth_2737_);
lean_inc(v_defEqCtx_x3f_2736_);
lean_inc_ref(v_localInstances_2735_);
lean_inc(v_zetaDeltaSet_2734_);
lean_inc_ref(v_keyedConfig_2732_);
v___x_2742_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2742_, 0, v_keyedConfig_2732_);
lean_ctor_set(v___x_2742_, 1, v_zetaDeltaSet_2734_);
lean_ctor_set(v___x_2742_, 2, v_lctx_2723_);
lean_ctor_set(v___x_2742_, 3, v_localInstances_2735_);
lean_ctor_set(v___x_2742_, 4, v_defEqCtx_x3f_2736_);
lean_ctor_set(v___x_2742_, 5, v_synthPendingDepth_2737_);
lean_ctor_set(v___x_2742_, 6, v_customCanUnfoldPredicate_x3f_2738_);
lean_ctor_set_uint8(v___x_2742_, sizeof(void*)*7, v_trackZetaDelta_2733_);
lean_ctor_set_uint8(v___x_2742_, sizeof(void*)*7 + 1, v_univApprox_2739_);
lean_ctor_set_uint8(v___x_2742_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2740_);
lean_ctor_set_uint8(v___x_2742_, sizeof(void*)*7 + 3, v_cacheInferType_2741_);
lean_inc(v___y_2730_);
lean_inc_ref(v___y_2729_);
lean_inc(v___y_2728_);
lean_inc(v___y_2726_);
lean_inc_ref(v___y_2725_);
v___x_2743_ = lean_apply_7(v_x_2724_, v___y_2725_, v___y_2726_, v___x_2742_, v___y_2728_, v___y_2729_, v___y_2730_, lean_box(0));
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2743_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2743_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
else
{
return v___x_2743_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___redArg___boxed(lean_object* v_lctx_2752_, lean_object* v_x_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___redArg(v_lctx_2752_, v_x_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4(lean_object* v_00_u03b1_2762_, lean_object* v_lctx_2763_, lean_object* v_x_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
lean_object* v___x_2772_; 
v___x_2772_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___redArg(v_lctx_2763_, v_x_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___boxed(lean_object* v_00_u03b1_2773_, lean_object* v_lctx_2774_, lean_object* v_x_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4(v_00_u03b1_2773_, v_lctx_2774_, v_x_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg___lam__0(lean_object* v_k_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v_b_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v___x_2793_; 
lean_inc(v___y_2791_);
lean_inc_ref(v___y_2790_);
lean_inc(v___y_2789_);
lean_inc_ref(v___y_2788_);
lean_inc(v___y_2786_);
lean_inc_ref(v___y_2785_);
v___x_2793_ = lean_apply_8(v_k_2784_, v_b_2787_, v___y_2785_, v___y_2786_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, lean_box(0));
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg___lam__0___boxed(lean_object* v_k_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v_b_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg___lam__0(v_k_2794_, v___y_2795_, v___y_2796_, v_b_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg(lean_object* v_name_2804_, uint8_t v_bi_2805_, lean_object* v_type_2806_, lean_object* v_k_2807_, uint8_t v_kind_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
lean_object* v___f_2816_; lean_object* v___x_2817_; 
lean_inc(v___y_2810_);
lean_inc_ref(v___y_2809_);
v___f_2816_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2816_, 0, v_k_2807_);
lean_closure_set(v___f_2816_, 1, v___y_2809_);
lean_closure_set(v___f_2816_, 2, v___y_2810_);
v___x_2817_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2804_, v_bi_2805_, v_type_2806_, v___f_2816_, v_kind_2808_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
if (lean_obj_tag(v___x_2817_) == 0)
{
return v___x_2817_;
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2817_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2817_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg___boxed(lean_object* v_name_2826_, lean_object* v_bi_2827_, lean_object* v_type_2828_, lean_object* v_k_2829_, lean_object* v_kind_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
uint8_t v_bi_boxed_2838_; uint8_t v_kind_boxed_2839_; lean_object* v_res_2840_; 
v_bi_boxed_2838_ = lean_unbox(v_bi_2827_);
v_kind_boxed_2839_ = lean_unbox(v_kind_2830_);
v_res_2840_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg(v_name_2826_, v_bi_boxed_2838_, v_type_2828_, v_k_2829_, v_kind_boxed_2839_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec(v___y_2832_);
lean_dec_ref(v___y_2831_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5(lean_object* v_00_u03b1_2841_, lean_object* v_name_2842_, uint8_t v_bi_2843_, lean_object* v_type_2844_, lean_object* v_k_2845_, uint8_t v_kind_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v___x_2854_; 
v___x_2854_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg(v_name_2842_, v_bi_2843_, v_type_2844_, v_k_2845_, v_kind_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___boxed(lean_object* v_00_u03b1_2855_, lean_object* v_name_2856_, lean_object* v_bi_2857_, lean_object* v_type_2858_, lean_object* v_k_2859_, lean_object* v_kind_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
uint8_t v_bi_boxed_2868_; uint8_t v_kind_boxed_2869_; lean_object* v_res_2870_; 
v_bi_boxed_2868_ = lean_unbox(v_bi_2857_);
v_kind_boxed_2869_ = lean_unbox(v_kind_2860_);
v_res_2870_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5(v_00_u03b1_2855_, v_name_2856_, v_bi_boxed_2868_, v_type_2858_, v_k_2859_, v_kind_boxed_2869_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
return v_res_2870_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8(lean_object* v_opts_2871_, lean_object* v_opt_2872_){
_start:
{
lean_object* v_name_2873_; lean_object* v_defValue_2874_; lean_object* v_map_2875_; lean_object* v___x_2876_; 
v_name_2873_ = lean_ctor_get(v_opt_2872_, 0);
v_defValue_2874_ = lean_ctor_get(v_opt_2872_, 1);
v_map_2875_ = lean_ctor_get(v_opts_2871_, 0);
v___x_2876_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2875_, v_name_2873_);
if (lean_obj_tag(v___x_2876_) == 0)
{
uint8_t v___x_2877_; 
v___x_2877_ = lean_unbox(v_defValue_2874_);
return v___x_2877_;
}
else
{
lean_object* v_val_2878_; 
v_val_2878_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_val_2878_);
lean_dec_ref_known(v___x_2876_, 1);
if (lean_obj_tag(v_val_2878_) == 1)
{
uint8_t v_v_2879_; 
v_v_2879_ = lean_ctor_get_uint8(v_val_2878_, 0);
lean_dec_ref_known(v_val_2878_, 0);
return v_v_2879_;
}
else
{
uint8_t v___x_2880_; 
lean_dec(v_val_2878_);
v___x_2880_ = lean_unbox(v_defValue_2874_);
return v___x_2880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8___boxed(lean_object* v_opts_2881_, lean_object* v_opt_2882_){
_start:
{
uint8_t v_res_2883_; lean_object* v_r_2884_; 
v_res_2883_ = l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8(v_opts_2881_, v_opt_2882_);
lean_dec_ref(v_opt_2882_);
lean_dec_ref(v_opts_2881_);
v_r_2884_ = lean_box(v_res_2883_);
return v_r_2884_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0(uint8_t v_suppressElabErrors_2892_, lean_object* v_x_2893_){
_start:
{
if (lean_obj_tag(v_x_2893_) == 1)
{
lean_object* v_pre_2894_; 
v_pre_2894_ = lean_ctor_get(v_x_2893_, 0);
switch(lean_obj_tag(v_pre_2894_))
{
case 1:
{
lean_object* v_pre_2895_; 
v_pre_2895_ = lean_ctor_get(v_pre_2894_, 0);
switch(lean_obj_tag(v_pre_2895_))
{
case 0:
{
lean_object* v_str_2896_; lean_object* v_str_2897_; lean_object* v___x_2898_; uint8_t v___x_2899_; 
v_str_2896_ = lean_ctor_get(v_x_2893_, 1);
v_str_2897_ = lean_ctor_get(v_pre_2894_, 1);
v___x_2898_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__8));
v___x_2899_ = lean_string_dec_eq(v_str_2897_, v___x_2898_);
if (v___x_2899_ == 0)
{
lean_object* v___x_2900_; uint8_t v___x_2901_; 
v___x_2900_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__0));
v___x_2901_ = lean_string_dec_eq(v_str_2897_, v___x_2900_);
if (v___x_2901_ == 0)
{
return v___x_2901_;
}
else
{
lean_object* v___x_2902_; uint8_t v___x_2903_; 
v___x_2902_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__1));
v___x_2903_ = lean_string_dec_eq(v_str_2896_, v___x_2902_);
if (v___x_2903_ == 0)
{
return v___x_2903_;
}
else
{
return v_suppressElabErrors_2892_;
}
}
}
else
{
lean_object* v___x_2904_; uint8_t v___x_2905_; 
v___x_2904_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__2));
v___x_2905_ = lean_string_dec_eq(v_str_2896_, v___x_2904_);
if (v___x_2905_ == 0)
{
return v___x_2905_;
}
else
{
return v_suppressElabErrors_2892_;
}
}
}
case 1:
{
lean_object* v_pre_2906_; 
v_pre_2906_ = lean_ctor_get(v_pre_2895_, 0);
if (lean_obj_tag(v_pre_2906_) == 0)
{
lean_object* v_str_2907_; lean_object* v_str_2908_; lean_object* v_str_2909_; lean_object* v___x_2910_; uint8_t v___x_2911_; 
v_str_2907_ = lean_ctor_get(v_x_2893_, 1);
v_str_2908_ = lean_ctor_get(v_pre_2894_, 1);
v_str_2909_ = lean_ctor_get(v_pre_2895_, 1);
v___x_2910_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__3));
v___x_2911_ = lean_string_dec_eq(v_str_2909_, v___x_2910_);
if (v___x_2911_ == 0)
{
return v___x_2911_;
}
else
{
lean_object* v___x_2912_; uint8_t v___x_2913_; 
v___x_2912_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__4));
v___x_2913_ = lean_string_dec_eq(v_str_2908_, v___x_2912_);
if (v___x_2913_ == 0)
{
return v___x_2913_;
}
else
{
lean_object* v___x_2914_; uint8_t v___x_2915_; 
v___x_2914_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__5));
v___x_2915_ = lean_string_dec_eq(v_str_2907_, v___x_2914_);
if (v___x_2915_ == 0)
{
return v___x_2915_;
}
else
{
return v_suppressElabErrors_2892_;
}
}
}
}
else
{
uint8_t v___x_2916_; 
v___x_2916_ = 0;
return v___x_2916_;
}
}
default: 
{
uint8_t v___x_2917_; 
v___x_2917_ = 0;
return v___x_2917_;
}
}
}
case 0:
{
lean_object* v_str_2918_; lean_object* v___x_2919_; uint8_t v___x_2920_; 
v_str_2918_ = lean_ctor_get(v_x_2893_, 1);
v___x_2919_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__6));
v___x_2920_ = lean_string_dec_eq(v_str_2918_, v___x_2919_);
if (v___x_2920_ == 0)
{
return v___x_2920_;
}
else
{
return v_suppressElabErrors_2892_;
}
}
default: 
{
uint8_t v___x_2921_; 
v___x_2921_ = 0;
return v___x_2921_;
}
}
}
else
{
uint8_t v___x_2922_; 
v___x_2922_ = 0;
return v___x_2922_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___boxed(lean_object* v_suppressElabErrors_2923_, lean_object* v_x_2924_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2925_; uint8_t v_res_2926_; lean_object* v_r_2927_; 
v_suppressElabErrors_boxed_2925_ = lean_unbox(v_suppressElabErrors_2923_);
v_res_2926_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0(v_suppressElabErrors_boxed_2925_, v_x_2924_);
lean_dec(v_x_2924_);
v_r_2927_ = lean_box(v_res_2926_);
return v_r_2927_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0(void){
_start:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2928_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__14, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__14_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__14);
v___x_2929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2928_);
return v___x_2929_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__1(void){
_start:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2930_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2931_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0);
v___x_2932_ = lean_unsigned_to_nat(0u);
v___x_2933_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2932_);
lean_ctor_set(v___x_2933_, 1, v___x_2932_);
lean_ctor_set(v___x_2933_, 2, v___x_2932_);
lean_ctor_set(v___x_2933_, 3, v___x_2932_);
lean_ctor_set(v___x_2933_, 4, v___x_2931_);
lean_ctor_set(v___x_2933_, 5, v___x_2931_);
lean_ctor_set(v___x_2933_, 6, v___x_2931_);
lean_ctor_set(v___x_2933_, 7, v___x_2931_);
lean_ctor_set(v___x_2933_, 8, v___x_2931_);
lean_ctor_set(v___x_2933_, 9, v___x_2931_);
lean_ctor_set(v___x_2933_, 10, v___x_2931_);
lean_ctor_set(v___x_2933_, 11, v___x_2930_);
return v___x_2933_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__2(void){
_start:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2934_ = lean_unsigned_to_nat(32u);
v___x_2935_ = lean_mk_empty_array_with_capacity(v___x_2934_);
v___x_2936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2935_);
return v___x_2936_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__3(void){
_start:
{
size_t v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2937_ = ((size_t)5ULL);
v___x_2938_ = lean_unsigned_to_nat(0u);
v___x_2939_ = lean_unsigned_to_nat(32u);
v___x_2940_ = lean_mk_empty_array_with_capacity(v___x_2939_);
v___x_2941_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__2);
v___x_2942_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
lean_ctor_set(v___x_2942_, 1, v___x_2940_);
lean_ctor_set(v___x_2942_, 2, v___x_2938_);
lean_ctor_set(v___x_2942_, 3, v___x_2938_);
lean_ctor_set_usize(v___x_2942_, 4, v___x_2937_);
return v___x_2942_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__4(void){
_start:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2943_ = lean_box(1);
v___x_2944_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__3);
v___x_2945_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0);
v___x_2946_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2945_);
lean_ctor_set(v___x_2946_, 1, v___x_2944_);
lean_ctor_set(v___x_2946_, 2, v___x_2943_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19(lean_object* v_msgData_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
lean_object* v___x_2951_; lean_object* v_toCold_2952_; lean_object* v_env_2953_; lean_object* v_options_2954_; uint8_t v___x_2955_; lean_object* v_env_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2951_ = lean_st_ref_get(v___y_2949_);
v_toCold_2952_ = lean_ctor_get(v___y_2948_, 0);
v_env_2953_ = lean_ctor_get(v___x_2951_, 0);
lean_inc_ref(v_env_2953_);
lean_dec(v___x_2951_);
v_options_2954_ = lean_ctor_get(v_toCold_2952_, 2);
v___x_2955_ = 0;
v_env_2956_ = l_Lean_Environment_setRecordingDeps(v_env_2953_, v___x_2955_);
v___x_2957_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__1);
v___x_2958_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__4);
lean_inc_ref(v_options_2954_);
v___x_2959_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2959_, 0, v_env_2956_);
lean_ctor_set(v___x_2959_, 1, v___x_2957_);
lean_ctor_set(v___x_2959_, 2, v___x_2958_);
lean_ctor_set(v___x_2959_, 3, v_options_2954_);
v___x_2960_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
lean_ctor_set(v___x_2960_, 1, v_msgData_2947_);
v___x_2961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___boxed(lean_object* v_msgData_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19(v_msgData_2962_, v___y_2963_, v___y_2964_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13(lean_object* v_ref_2968_, lean_object* v_msgData_2969_, uint8_t v_severity_2970_, uint8_t v_isSilent_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
uint8_t v___y_2976_; uint8_t v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v_toCold_2983_; lean_object* v___y_2984_; lean_object* v___y_3013_; lean_object* v___y_3014_; uint8_t v___y_3015_; uint8_t v___y_3016_; uint8_t v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; uint8_t v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; uint8_t v___y_3043_; lean_object* v___y_3044_; uint8_t v___y_3045_; lean_object* v___y_3046_; uint8_t v___y_3050_; uint8_t v___y_3051_; uint8_t v___x_3061_; uint8_t v___y_3063_; uint8_t v___x_3069_; 
v___x_3061_ = 2;
v___x_3069_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2970_, v___x_3061_);
if (v___x_3069_ == 0)
{
v___y_3063_ = v___x_3069_;
goto v___jp_3062_;
}
else
{
uint8_t v___x_3070_; 
lean_inc_ref(v_msgData_2969_);
v___x_3070_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2969_);
if (v___x_3070_ == 0)
{
v___y_3063_ = v___x_3070_;
goto v___jp_3062_;
}
else
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
lean_dec_ref(v_msgData_2969_);
v___x_3071_ = lean_box(0);
v___x_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
return v___x_3072_;
}
}
v___jp_2975_:
{
lean_object* v_currNamespace_2985_; lean_object* v_openDecls_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v_env_2991_; lean_object* v_nextMacroScope_2992_; lean_object* v_ngen_2993_; lean_object* v_auxDeclNGen_2994_; lean_object* v_traceState_2995_; lean_object* v_cache_2996_; lean_object* v_recordedDeps_2997_; lean_object* v_messages_2998_; lean_object* v_infoState_2999_; lean_object* v_snapshotTasks_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3011_; 
v_currNamespace_2985_ = lean_ctor_get(v_toCold_2983_, 4);
v_openDecls_2986_ = lean_ctor_get(v_toCold_2983_, 5);
lean_inc(v_openDecls_2986_);
lean_inc(v_currNamespace_2985_);
v___x_2987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2987_, 0, v_currNamespace_2985_);
lean_ctor_set(v___x_2987_, 1, v_openDecls_2986_);
v___x_2988_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
lean_ctor_set(v___x_2988_, 1, v___y_2979_);
lean_inc_ref(v___y_2981_);
lean_inc_ref(v___y_2982_);
v___x_2989_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2989_, 0, v___y_2982_);
lean_ctor_set(v___x_2989_, 1, v___y_2978_);
lean_ctor_set(v___x_2989_, 2, v___y_2980_);
lean_ctor_set(v___x_2989_, 3, v___y_2981_);
lean_ctor_set(v___x_2989_, 4, v___x_2988_);
lean_ctor_set_uint8(v___x_2989_, sizeof(void*)*5, v___y_2976_);
lean_ctor_set_uint8(v___x_2989_, sizeof(void*)*5 + 1, v___y_2977_);
lean_ctor_set_uint8(v___x_2989_, sizeof(void*)*5 + 2, v_isSilent_2971_);
v___x_2990_ = lean_st_ref_take(v___y_2984_);
v_env_2991_ = lean_ctor_get(v___x_2990_, 0);
v_nextMacroScope_2992_ = lean_ctor_get(v___x_2990_, 1);
v_ngen_2993_ = lean_ctor_get(v___x_2990_, 2);
v_auxDeclNGen_2994_ = lean_ctor_get(v___x_2990_, 3);
v_traceState_2995_ = lean_ctor_get(v___x_2990_, 4);
v_cache_2996_ = lean_ctor_get(v___x_2990_, 5);
v_recordedDeps_2997_ = lean_ctor_get(v___x_2990_, 6);
v_messages_2998_ = lean_ctor_get(v___x_2990_, 7);
v_infoState_2999_ = lean_ctor_get(v___x_2990_, 8);
v_snapshotTasks_3000_ = lean_ctor_get(v___x_2990_, 9);
v_isSharedCheck_3011_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3002_ = v___x_2990_;
v_isShared_3003_ = v_isSharedCheck_3011_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_snapshotTasks_3000_);
lean_inc(v_infoState_2999_);
lean_inc(v_messages_2998_);
lean_inc(v_recordedDeps_2997_);
lean_inc(v_cache_2996_);
lean_inc(v_traceState_2995_);
lean_inc(v_auxDeclNGen_2994_);
lean_inc(v_ngen_2993_);
lean_inc(v_nextMacroScope_2992_);
lean_inc(v_env_2991_);
lean_dec(v___x_2990_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3011_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3007_; 
v___x_3004_ = lean_box(0);
v___x_3005_ = l_Lean_MessageLog_add(v___x_2989_, v_messages_2998_);
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 7, v___x_3005_);
v___x_3007_ = v___x_3002_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_env_2991_);
lean_ctor_set(v_reuseFailAlloc_3010_, 1, v_nextMacroScope_2992_);
lean_ctor_set(v_reuseFailAlloc_3010_, 2, v_ngen_2993_);
lean_ctor_set(v_reuseFailAlloc_3010_, 3, v_auxDeclNGen_2994_);
lean_ctor_set(v_reuseFailAlloc_3010_, 4, v_traceState_2995_);
lean_ctor_set(v_reuseFailAlloc_3010_, 5, v_cache_2996_);
lean_ctor_set(v_reuseFailAlloc_3010_, 6, v_recordedDeps_2997_);
lean_ctor_set(v_reuseFailAlloc_3010_, 7, v___x_3005_);
lean_ctor_set(v_reuseFailAlloc_3010_, 8, v_infoState_2999_);
lean_ctor_set(v_reuseFailAlloc_3010_, 9, v_snapshotTasks_3000_);
v___x_3007_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3008_ = lean_st_ref_put(v___y_2984_, v___x_3007_);
v___x_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3004_);
return v___x_3009_;
}
}
}
v___jp_3012_:
{
lean_object* v_fileName_3021_; lean_object* v_fileMap_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3038_; 
v_fileName_3021_ = lean_ctor_get(v___y_3018_, 0);
v_fileMap_3022_ = lean_ctor_get(v___y_3018_, 1);
v___x_3023_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2969_);
v___x_3024_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19(v___x_3023_, v___y_2972_, v___y_2973_);
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3027_ = v___x_3024_;
v_isShared_3028_ = v_isSharedCheck_3038_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_3024_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3038_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
lean_inc_ref_n(v_fileMap_3022_, 2);
v___x_3029_ = l_Lean_FileMap_toPosition(v_fileMap_3022_, v___y_3019_);
lean_dec(v___y_3019_);
v___x_3030_ = l_Lean_FileMap_toPosition(v_fileMap_3022_, v___y_3020_);
lean_dec(v___y_3020_);
v___x_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3030_);
v___x_3032_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___closed__0));
if (v___y_3016_ == 0)
{
lean_del_object(v___x_3027_);
lean_dec_ref(v___y_3013_);
v___y_2976_ = v___y_3015_;
v___y_2977_ = v___y_3017_;
v___y_2978_ = v___x_3029_;
v___y_2979_ = v_a_3025_;
v___y_2980_ = v___x_3031_;
v___y_2981_ = v___x_3032_;
v___y_2982_ = v_fileName_3021_;
v_toCold_2983_ = v___y_3014_;
v___y_2984_ = v___y_2973_;
goto v___jp_2975_;
}
else
{
uint8_t v___x_3033_; 
lean_inc(v_a_3025_);
v___x_3033_ = l_Lean_MessageData_hasTag(v___y_3013_, v_a_3025_);
if (v___x_3033_ == 0)
{
lean_object* v___x_3034_; lean_object* v___x_3036_; 
lean_dec_ref_known(v___x_3031_, 1);
lean_dec_ref(v___x_3029_);
lean_dec(v_a_3025_);
v___x_3034_ = lean_box(0);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 0, v___x_3034_);
v___x_3036_ = v___x_3027_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_3034_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
else
{
lean_del_object(v___x_3027_);
v___y_2976_ = v___y_3015_;
v___y_2977_ = v___y_3017_;
v___y_2978_ = v___x_3029_;
v___y_2979_ = v_a_3025_;
v___y_2980_ = v___x_3031_;
v___y_2981_ = v___x_3032_;
v___y_2982_ = v_fileName_3021_;
v_toCold_2983_ = v___y_3014_;
v___y_2984_ = v___y_2973_;
goto v___jp_2975_;
}
}
}
}
v___jp_3039_:
{
lean_object* v___x_3047_; 
v___x_3047_ = l_Lean_Syntax_getTailPos_x3f(v___y_3044_, v___y_3043_);
lean_dec(v___y_3044_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_inc(v___y_3046_);
v___y_3013_ = v___y_3041_;
v___y_3014_ = v___y_3042_;
v___y_3015_ = v___y_3043_;
v___y_3016_ = v___y_3040_;
v___y_3017_ = v___y_3045_;
v___y_3018_ = v___y_3042_;
v___y_3019_ = v___y_3046_;
v___y_3020_ = v___y_3046_;
goto v___jp_3012_;
}
else
{
lean_object* v_val_3048_; 
v_val_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_val_3048_);
lean_dec_ref_known(v___x_3047_, 1);
v___y_3013_ = v___y_3041_;
v___y_3014_ = v___y_3042_;
v___y_3015_ = v___y_3043_;
v___y_3016_ = v___y_3040_;
v___y_3017_ = v___y_3045_;
v___y_3018_ = v___y_3042_;
v___y_3019_ = v___y_3046_;
v___y_3020_ = v_val_3048_;
goto v___jp_3012_;
}
}
v___jp_3049_:
{
lean_object* v_toCold_3052_; lean_object* v_ref_3053_; uint8_t v_suppressElabErrors_3054_; lean_object* v___x_3055_; lean_object* v___f_3056_; lean_object* v_ref_3057_; lean_object* v___x_3058_; 
v_toCold_3052_ = lean_ctor_get(v___y_2972_, 0);
v_ref_3053_ = lean_ctor_get(v___y_2972_, 2);
v_suppressElabErrors_3054_ = lean_ctor_get_uint8(v___y_2972_, sizeof(void*)*3 + 2);
v___x_3055_ = lean_box(v_suppressElabErrors_3054_);
v___f_3056_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3056_, 0, v___x_3055_);
v_ref_3057_ = l_Lean_replaceRef(v_ref_2968_, v_ref_3053_);
v___x_3058_ = l_Lean_Syntax_getPos_x3f(v_ref_3057_, v___y_3050_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v___x_3059_; 
v___x_3059_ = lean_unsigned_to_nat(0u);
v___y_3040_ = v_suppressElabErrors_3054_;
v___y_3041_ = v___f_3056_;
v___y_3042_ = v_toCold_3052_;
v___y_3043_ = v___y_3050_;
v___y_3044_ = v_ref_3057_;
v___y_3045_ = v___y_3051_;
v___y_3046_ = v___x_3059_;
goto v___jp_3039_;
}
else
{
lean_object* v_val_3060_; 
v_val_3060_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_val_3060_);
lean_dec_ref_known(v___x_3058_, 1);
v___y_3040_ = v_suppressElabErrors_3054_;
v___y_3041_ = v___f_3056_;
v___y_3042_ = v_toCold_3052_;
v___y_3043_ = v___y_3050_;
v___y_3044_ = v_ref_3057_;
v___y_3045_ = v___y_3051_;
v___y_3046_ = v_val_3060_;
goto v___jp_3039_;
}
}
v___jp_3062_:
{
uint8_t v___x_3064_; uint8_t v___x_3065_; 
v___x_3064_ = 1;
v___x_3065_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2970_, v___x_3064_);
if (v___x_3065_ == 0)
{
v___y_3050_ = v___y_3063_;
v___y_3051_ = v_severity_2970_;
goto v___jp_3049_;
}
else
{
lean_object* v___x_3066_; lean_object* v___x_3067_; uint8_t v___x_3068_; 
v___x_3066_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2972_);
v___x_3067_ = l_Lean_warningAsError;
v___x_3068_ = l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8(v___x_3066_, v___x_3067_);
lean_dec_ref(v___x_3066_);
if (v___x_3068_ == 0)
{
v___y_3050_ = v___y_3063_;
v___y_3051_ = v_severity_2970_;
goto v___jp_3049_;
}
else
{
v___y_3050_ = v___y_3063_;
v___y_3051_ = v___x_3061_;
goto v___jp_3049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___boxed(lean_object* v_ref_3073_, lean_object* v_msgData_3074_, lean_object* v_severity_3075_, lean_object* v_isSilent_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
uint8_t v_severity_boxed_3080_; uint8_t v_isSilent_boxed_3081_; lean_object* v_res_3082_; 
v_severity_boxed_3080_ = lean_unbox(v_severity_3075_);
v_isSilent_boxed_3081_ = lean_unbox(v_isSilent_3076_);
v_res_3082_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13(v_ref_3073_, v_msgData_3074_, v_severity_boxed_3080_, v_isSilent_boxed_3081_, v___y_3077_, v___y_3078_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v_ref_3073_);
return v_res_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9(lean_object* v_ref_3083_, lean_object* v_msgData_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
uint8_t v___x_3088_; uint8_t v___x_3089_; lean_object* v___x_3090_; 
v___x_3088_ = 0;
v___x_3089_ = 0;
v___x_3090_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13(v_ref_3083_, v_msgData_3084_, v___x_3088_, v___x_3089_, v___y_3085_, v___y_3086_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9___boxed(lean_object* v_ref_3091_, lean_object* v_msgData_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9(v_ref_3091_, v_msgData_3092_, v___y_3093_, v___y_3094_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec(v_ref_3091_);
return v_res_3096_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3098_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__0));
v___x_3099_ = l_Lean_stringToMessageData(v___x_3098_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0(lean_object* v___x_3100_, lean_object* v___x_3101_, lean_object* v_ref_3102_, lean_object* v_x_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
lean_object* v_ref_3107_; lean_object* v___x_3108_; 
v_ref_3107_ = lean_ctor_get(v___y_3104_, 2);
v___x_3108_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer(v___x_3100_, v___x_3101_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3122_; 
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3111_ = v___x_3108_;
v_isShared_3112_ = v_isSharedCheck_3122_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3108_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3122_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
if (lean_obj_tag(v_a_3109_) == 1)
{
lean_object* v_val_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
lean_del_object(v___x_3111_);
v_val_3113_ = lean_ctor_get(v_a_3109_, 0);
lean_inc(v_val_3113_);
lean_dec_ref_known(v_a_3109_, 1);
v___x_3114_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__1, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__1_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__1);
v___x_3115_ = l_Lean_stringToMessageData(v_val_3113_);
v___x_3116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3114_);
lean_ctor_set(v___x_3116_, 1, v___x_3115_);
v___x_3117_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9(v_ref_3102_, v___x_3116_, v___y_3104_, v___y_3105_);
return v___x_3117_;
}
else
{
lean_object* v___x_3118_; lean_object* v___x_3120_; 
lean_dec(v_a_3109_);
v___x_3118_ = lean_box(0);
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 0, v___x_3118_);
v___x_3120_ = v___x_3111_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3118_);
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
else
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3134_; 
v_a_3123_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3125_ = v___x_3108_;
v_isShared_3126_ = v_isSharedCheck_3134_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3108_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3134_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3132_; 
v___x_3127_ = lean_io_error_to_string(v_a_3123_);
v___x_3128_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3127_);
v___x_3129_ = l_Lean_MessageData_ofFormat(v___x_3128_);
lean_inc(v_ref_3107_);
v___x_3130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3130_, 0, v_ref_3107_);
lean_ctor_set(v___x_3130_, 1, v___x_3129_);
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 0, v___x_3130_);
v___x_3132_ = v___x_3125_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v___x_3130_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___boxed(lean_object* v___x_3135_, lean_object* v___x_3136_, lean_object* v_ref_3137_, lean_object* v_x_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0(v___x_3135_, v___x_3136_, v_ref_3137_, v_x_3138_, v___y_3139_, v___y_3140_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v_ref_3137_);
lean_dec_ref(v___x_3135_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__1(lean_object* v___x_3143_, lean_object* v___x_3144_, uint8_t v___x_3145_, uint8_t v___x_3146_, uint8_t v___x_3147_, lean_object* v_fVar_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
lean_inc_ref(v_fVar_3148_);
v___x_3156_ = l_Lean_mkAppN(v_fVar_3148_, v___x_3143_);
v___x_3157_ = lean_array_push(v___x_3144_, v_fVar_3148_);
v___x_3158_ = l_Lean_Meta_mkLambdaFVars(v___x_3157_, v___x_3156_, v___x_3145_, v___x_3146_, v___x_3145_, v___x_3146_, v___x_3147_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
lean_dec_ref(v___x_3157_);
return v___x_3158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__1___boxed(lean_object* v___x_3159_, lean_object* v___x_3160_, lean_object* v___x_3161_, lean_object* v___x_3162_, lean_object* v___x_3163_, lean_object* v_fVar_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
uint8_t v___x_34327__boxed_3172_; uint8_t v___x_34328__boxed_3173_; uint8_t v___x_34329__boxed_3174_; lean_object* v_res_3175_; 
v___x_34327__boxed_3172_ = lean_unbox(v___x_3161_);
v___x_34328__boxed_3173_ = lean_unbox(v___x_3162_);
v___x_34329__boxed_3174_ = lean_unbox(v___x_3163_);
v_res_3175_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__1(v___x_3159_, v___x_3160_, v___x_34327__boxed_3172_, v___x_34328__boxed_3173_, v___x_34329__boxed_3174_, v_fVar_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec_ref(v___x_3159_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__2(lean_object* v___x_3176_, lean_object* v_a_3177_, uint8_t v___x_3178_, uint8_t v___x_3179_, uint8_t v___x_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
lean_object* v___x_3188_; 
v___x_3188_ = l_Lean_Meta_mkLambdaFVars(v___x_3176_, v_a_3177_, v___x_3178_, v___x_3179_, v___x_3178_, v___x_3179_, v___x_3180_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v_a_3189_; lean_object* v___x_3190_; 
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
lean_inc_n(v_a_3189_, 2);
lean_dec_ref_known(v___x_3188_, 1);
lean_inc(v___y_3184_);
v___x_3190_ = lean_infer_type(v_a_3189_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v_a_3191_; lean_object* v___x_3192_; lean_object* v_a_3193_; lean_object* v___x_3194_; lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3203_; 
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
lean_inc(v_a_3191_);
lean_dec_ref_known(v___x_3190_, 1);
v___x_3192_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(v_a_3189_, v___y_3184_);
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
lean_inc(v_a_3193_);
lean_dec_ref(v___x_3192_);
v___x_3194_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(v_a_3191_, v___y_3184_);
lean_dec(v___y_3184_);
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3197_ = v___x_3194_;
v_isShared_3198_ = v_isSharedCheck_3203_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3194_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3203_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3199_; lean_object* v___x_3201_; 
v___x_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3199_, 0, v_a_3193_);
lean_ctor_set(v___x_3199_, 1, v_a_3195_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 0, v___x_3199_);
v___x_3201_ = v___x_3197_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3199_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
else
{
lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3211_; 
lean_dec(v_a_3189_);
lean_dec(v___y_3184_);
v_a_3204_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3206_ = v___x_3190_;
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3190_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3209_; 
if (v_isShared_3207_ == 0)
{
v___x_3209_ = v___x_3206_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_a_3204_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
}
else
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3219_; 
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
v_a_3212_ = lean_ctor_get(v___x_3188_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3214_ = v___x_3188_;
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3188_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3217_; 
if (v_isShared_3215_ == 0)
{
v___x_3217_ = v___x_3214_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_a_3212_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__2___boxed(lean_object* v___x_3220_, lean_object* v_a_3221_, lean_object* v___x_3222_, lean_object* v___x_3223_, lean_object* v___x_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_){
_start:
{
uint8_t v___x_34369__boxed_3232_; uint8_t v___x_34370__boxed_3233_; uint8_t v___x_34371__boxed_3234_; lean_object* v_res_3235_; 
v___x_34369__boxed_3232_ = lean_unbox(v___x_3222_);
v___x_34370__boxed_3233_ = lean_unbox(v___x_3223_);
v___x_34371__boxed_3234_ = lean_unbox(v___x_3224_);
v_res_3235_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__2(v___x_3220_, v_a_3221_, v___x_34369__boxed_3232_, v___x_34370__boxed_3233_, v___x_34371__boxed_3234_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec_ref(v___x_3220_);
return v_res_3235_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4(void){
_start:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3244_ = lean_box(0);
v___x_3245_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__3));
v___x_3246_ = l_Lean_Expr_const___override(v___x_3245_, v___x_3244_);
return v___x_3246_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__7(void){
_start:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v___x_3251_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__0));
v___x_3252_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__6));
v___x_3253_ = l_Lean_Expr_const___override(v___x_3252_, v___x_3251_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10(lean_object* v_as_3254_, size_t v_i_3255_, size_t v_stop_3256_, lean_object* v_b_3257_){
_start:
{
uint8_t v___x_3258_; 
v___x_3258_ = lean_usize_dec_eq(v_i_3255_, v_stop_3256_);
if (v___x_3258_ == 0)
{
lean_object* v___x_3259_; size_t v___x_3260_; size_t v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3259_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4);
v___x_3260_ = ((size_t)1ULL);
v___x_3261_ = lean_usize_sub(v_i_3255_, v___x_3260_);
v___x_3262_ = lean_array_uget_borrowed(v_as_3254_, v___x_3261_);
v___x_3263_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__7);
lean_inc(v___x_3262_);
v___x_3264_ = l_Lean_mkApp3(v___x_3263_, v___x_3259_, v___x_3262_, v_b_3257_);
v_i_3255_ = v___x_3261_;
v_b_3257_ = v___x_3264_;
goto _start;
}
else
{
return v_b_3257_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___boxed(lean_object* v_as_3266_, lean_object* v_i_3267_, lean_object* v_stop_3268_, lean_object* v_b_3269_){
_start:
{
size_t v_i_boxed_3270_; size_t v_stop_boxed_3271_; lean_object* v_res_3272_; 
v_i_boxed_3270_ = lean_unbox_usize(v_i_3267_);
lean_dec(v_i_3267_);
v_stop_boxed_3271_ = lean_unbox_usize(v_stop_3268_);
lean_dec(v_stop_3268_);
v_res_3272_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10(v_as_3266_, v_i_boxed_3270_, v_stop_boxed_3271_, v_b_3269_);
lean_dec_ref(v_as_3266_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7(lean_object* v_init_3273_, lean_object* v_l_3274_){
_start:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; uint8_t v___x_3278_; 
v___x_3275_ = lean_array_mk(v_l_3274_);
v___x_3276_ = lean_array_get_size(v___x_3275_);
v___x_3277_ = lean_unsigned_to_nat(0u);
v___x_3278_ = lean_nat_dec_lt(v___x_3277_, v___x_3276_);
if (v___x_3278_ == 0)
{
lean_dec_ref(v___x_3275_);
return v_init_3273_;
}
else
{
size_t v___x_3279_; size_t v___x_3280_; lean_object* v___x_3281_; 
v___x_3279_ = lean_usize_of_nat(v___x_3276_);
v___x_3280_ = ((size_t)0ULL);
v___x_3281_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10(v___x_3275_, v___x_3279_, v___x_3280_, v_init_3273_);
lean_dec_ref(v___x_3275_);
return v___x_3281_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___redArg(lean_object* v_as_3282_, size_t v_sz_3283_, size_t v_i_3284_, lean_object* v_b_3285_){
_start:
{
uint8_t v___x_3287_; 
v___x_3287_ = lean_usize_dec_lt(v_i_3284_, v_sz_3283_);
if (v___x_3287_ == 0)
{
lean_object* v___x_3288_; 
v___x_3288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3288_, 0, v_b_3285_);
return v___x_3288_;
}
else
{
lean_object* v_snd_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3306_; 
v_snd_3289_ = lean_ctor_get(v_b_3285_, 1);
v_isSharedCheck_3306_ = !lean_is_exclusive(v_b_3285_);
if (v_isSharedCheck_3306_ == 0)
{
lean_object* v_unused_3307_; 
v_unused_3307_ = lean_ctor_get(v_b_3285_, 0);
lean_dec(v_unused_3307_);
v___x_3291_ = v_b_3285_;
v_isShared_3292_ = v_isSharedCheck_3306_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_snd_3289_);
lean_dec(v_b_3285_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3306_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; lean_object* v_a_3295_; lean_object* v_a_3302_; 
v___x_3293_ = lean_box(0);
v_a_3302_ = lean_array_uget_borrowed(v_as_3282_, v_i_3284_);
if (lean_obj_tag(v_a_3302_) == 0)
{
v_a_3295_ = v_snd_3289_;
goto v___jp_3294_;
}
else
{
lean_object* v_val_3303_; uint8_t v___x_3304_; 
v_val_3303_ = lean_ctor_get(v_a_3302_, 0);
v___x_3304_ = l_Lean_LocalDecl_isAuxDecl(v_val_3303_);
if (v___x_3304_ == 0)
{
lean_object* v___x_3305_; 
lean_inc(v_val_3303_);
v___x_3305_ = lean_array_push(v_snd_3289_, v_val_3303_);
v_a_3295_ = v___x_3305_;
goto v___jp_3294_;
}
else
{
v_a_3295_ = v_snd_3289_;
goto v___jp_3294_;
}
}
v___jp_3294_:
{
lean_object* v___x_3297_; 
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 1, v_a_3295_);
lean_ctor_set(v___x_3291_, 0, v___x_3293_);
v___x_3297_ = v___x_3291_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3293_);
lean_ctor_set(v_reuseFailAlloc_3301_, 1, v_a_3295_);
v___x_3297_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
size_t v___x_3298_; size_t v___x_3299_; 
v___x_3298_ = ((size_t)1ULL);
v___x_3299_ = lean_usize_add(v_i_3284_, v___x_3298_);
v_i_3284_ = v___x_3299_;
v_b_3285_ = v___x_3297_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___redArg___boxed(lean_object* v_as_3308_, lean_object* v_sz_3309_, lean_object* v_i_3310_, lean_object* v_b_3311_, lean_object* v___y_3312_){
_start:
{
size_t v_sz_boxed_3313_; size_t v_i_boxed_3314_; lean_object* v_res_3315_; 
v_sz_boxed_3313_ = lean_unbox_usize(v_sz_3309_);
lean_dec(v_sz_3309_);
v_i_boxed_3314_ = lean_unbox_usize(v_i_3310_);
lean_dec(v_i_3310_);
v_res_3315_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___redArg(v_as_3308_, v_sz_boxed_3313_, v_i_boxed_3314_, v_b_3311_);
lean_dec_ref(v_as_3308_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1(lean_object* v_as_3316_, size_t v_sz_3317_, size_t v_i_3318_, lean_object* v_b_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_){
_start:
{
uint8_t v___x_3327_; 
v___x_3327_ = lean_usize_dec_lt(v_i_3318_, v_sz_3317_);
if (v___x_3327_ == 0)
{
lean_object* v___x_3328_; 
v___x_3328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3328_, 0, v_b_3319_);
return v___x_3328_;
}
else
{
lean_object* v_snd_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3346_; 
v_snd_3329_ = lean_ctor_get(v_b_3319_, 1);
v_isSharedCheck_3346_ = !lean_is_exclusive(v_b_3319_);
if (v_isSharedCheck_3346_ == 0)
{
lean_object* v_unused_3347_; 
v_unused_3347_ = lean_ctor_get(v_b_3319_, 0);
lean_dec(v_unused_3347_);
v___x_3331_ = v_b_3319_;
v_isShared_3332_ = v_isSharedCheck_3346_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_snd_3329_);
lean_dec(v_b_3319_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3346_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3333_; lean_object* v_a_3335_; lean_object* v_a_3342_; 
v___x_3333_ = lean_box(0);
v_a_3342_ = lean_array_uget_borrowed(v_as_3316_, v_i_3318_);
if (lean_obj_tag(v_a_3342_) == 0)
{
v_a_3335_ = v_snd_3329_;
goto v___jp_3334_;
}
else
{
lean_object* v_val_3343_; uint8_t v___x_3344_; 
v_val_3343_ = lean_ctor_get(v_a_3342_, 0);
v___x_3344_ = l_Lean_LocalDecl_isAuxDecl(v_val_3343_);
if (v___x_3344_ == 0)
{
lean_object* v___x_3345_; 
lean_inc(v_val_3343_);
v___x_3345_ = lean_array_push(v_snd_3329_, v_val_3343_);
v_a_3335_ = v___x_3345_;
goto v___jp_3334_;
}
else
{
v_a_3335_ = v_snd_3329_;
goto v___jp_3334_;
}
}
v___jp_3334_:
{
lean_object* v___x_3337_; 
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 1, v_a_3335_);
lean_ctor_set(v___x_3331_, 0, v___x_3333_);
v___x_3337_ = v___x_3331_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v___x_3333_);
lean_ctor_set(v_reuseFailAlloc_3341_, 1, v_a_3335_);
v___x_3337_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
size_t v___x_3338_; size_t v___x_3339_; lean_object* v___x_3340_; 
v___x_3338_ = ((size_t)1ULL);
v___x_3339_ = lean_usize_add(v_i_3318_, v___x_3338_);
v___x_3340_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___redArg(v_as_3316_, v_sz_3317_, v___x_3339_, v___x_3337_);
return v___x_3340_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1___boxed(lean_object* v_as_3348_, lean_object* v_sz_3349_, lean_object* v_i_3350_, lean_object* v_b_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
size_t v_sz_boxed_3359_; size_t v_i_boxed_3360_; lean_object* v_res_3361_; 
v_sz_boxed_3359_ = lean_unbox_usize(v_sz_3349_);
lean_dec(v_sz_3349_);
v_i_boxed_3360_ = lean_unbox_usize(v_i_3350_);
lean_dec(v_i_3350_);
v_res_3361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1(v_as_3348_, v_sz_boxed_3359_, v_i_boxed_3360_, v_b_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_);
lean_dec(v___y_3357_);
lean_dec_ref(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
lean_dec_ref(v_as_3348_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___redArg(lean_object* v_as_3362_, size_t v_sz_3363_, size_t v_i_3364_, lean_object* v_b_3365_){
_start:
{
uint8_t v___x_3367_; 
v___x_3367_ = lean_usize_dec_lt(v_i_3364_, v_sz_3363_);
if (v___x_3367_ == 0)
{
lean_object* v___x_3368_; 
v___x_3368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3368_, 0, v_b_3365_);
return v___x_3368_;
}
else
{
lean_object* v_snd_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3386_; 
v_snd_3369_ = lean_ctor_get(v_b_3365_, 1);
v_isSharedCheck_3386_ = !lean_is_exclusive(v_b_3365_);
if (v_isSharedCheck_3386_ == 0)
{
lean_object* v_unused_3387_; 
v_unused_3387_ = lean_ctor_get(v_b_3365_, 0);
lean_dec(v_unused_3387_);
v___x_3371_ = v_b_3365_;
v_isShared_3372_ = v_isSharedCheck_3386_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_snd_3369_);
lean_dec(v_b_3365_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3386_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3373_; lean_object* v_a_3375_; lean_object* v_a_3382_; 
v___x_3373_ = lean_box(0);
v_a_3382_ = lean_array_uget_borrowed(v_as_3362_, v_i_3364_);
if (lean_obj_tag(v_a_3382_) == 0)
{
v_a_3375_ = v_snd_3369_;
goto v___jp_3374_;
}
else
{
lean_object* v_val_3383_; uint8_t v___x_3384_; 
v_val_3383_ = lean_ctor_get(v_a_3382_, 0);
v___x_3384_ = l_Lean_LocalDecl_isAuxDecl(v_val_3383_);
if (v___x_3384_ == 0)
{
lean_object* v___x_3385_; 
lean_inc(v_val_3383_);
v___x_3385_ = lean_array_push(v_snd_3369_, v_val_3383_);
v_a_3375_ = v___x_3385_;
goto v___jp_3374_;
}
else
{
v_a_3375_ = v_snd_3369_;
goto v___jp_3374_;
}
}
v___jp_3374_:
{
lean_object* v___x_3377_; 
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 1, v_a_3375_);
lean_ctor_set(v___x_3371_, 0, v___x_3373_);
v___x_3377_ = v___x_3371_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3373_);
lean_ctor_set(v_reuseFailAlloc_3381_, 1, v_a_3375_);
v___x_3377_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
size_t v___x_3378_; size_t v___x_3379_; 
v___x_3378_ = ((size_t)1ULL);
v___x_3379_ = lean_usize_add(v_i_3364_, v___x_3378_);
v_i_3364_ = v___x_3379_;
v_b_3365_ = v___x_3377_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___redArg___boxed(lean_object* v_as_3388_, lean_object* v_sz_3389_, lean_object* v_i_3390_, lean_object* v_b_3391_, lean_object* v___y_3392_){
_start:
{
size_t v_sz_boxed_3393_; size_t v_i_boxed_3394_; lean_object* v_res_3395_; 
v_sz_boxed_3393_ = lean_unbox_usize(v_sz_3389_);
lean_dec(v_sz_3389_);
v_i_boxed_3394_ = lean_unbox_usize(v_i_3390_);
lean_dec(v_i_3390_);
v_res_3395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___redArg(v_as_3388_, v_sz_boxed_3393_, v_i_boxed_3394_, v_b_3391_);
lean_dec_ref(v_as_3388_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6(lean_object* v_as_3396_, size_t v_sz_3397_, size_t v_i_3398_, lean_object* v_b_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_){
_start:
{
uint8_t v___x_3407_; 
v___x_3407_ = lean_usize_dec_lt(v_i_3398_, v_sz_3397_);
if (v___x_3407_ == 0)
{
lean_object* v___x_3408_; 
v___x_3408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3408_, 0, v_b_3399_);
return v___x_3408_;
}
else
{
lean_object* v_snd_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3426_; 
v_snd_3409_ = lean_ctor_get(v_b_3399_, 1);
v_isSharedCheck_3426_ = !lean_is_exclusive(v_b_3399_);
if (v_isSharedCheck_3426_ == 0)
{
lean_object* v_unused_3427_; 
v_unused_3427_ = lean_ctor_get(v_b_3399_, 0);
lean_dec(v_unused_3427_);
v___x_3411_ = v_b_3399_;
v_isShared_3412_ = v_isSharedCheck_3426_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_snd_3409_);
lean_dec(v_b_3399_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3426_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3413_; lean_object* v_a_3415_; lean_object* v_a_3422_; 
v___x_3413_ = lean_box(0);
v_a_3422_ = lean_array_uget_borrowed(v_as_3396_, v_i_3398_);
if (lean_obj_tag(v_a_3422_) == 0)
{
v_a_3415_ = v_snd_3409_;
goto v___jp_3414_;
}
else
{
lean_object* v_val_3423_; uint8_t v___x_3424_; 
v_val_3423_ = lean_ctor_get(v_a_3422_, 0);
v___x_3424_ = l_Lean_LocalDecl_isAuxDecl(v_val_3423_);
if (v___x_3424_ == 0)
{
lean_object* v___x_3425_; 
lean_inc(v_val_3423_);
v___x_3425_ = lean_array_push(v_snd_3409_, v_val_3423_);
v_a_3415_ = v___x_3425_;
goto v___jp_3414_;
}
else
{
v_a_3415_ = v_snd_3409_;
goto v___jp_3414_;
}
}
v___jp_3414_:
{
lean_object* v___x_3417_; 
if (v_isShared_3412_ == 0)
{
lean_ctor_set(v___x_3411_, 1, v_a_3415_);
lean_ctor_set(v___x_3411_, 0, v___x_3413_);
v___x_3417_ = v___x_3411_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3413_);
lean_ctor_set(v_reuseFailAlloc_3421_, 1, v_a_3415_);
v___x_3417_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
size_t v___x_3418_; size_t v___x_3419_; lean_object* v___x_3420_; 
v___x_3418_ = ((size_t)1ULL);
v___x_3419_ = lean_usize_add(v_i_3398_, v___x_3418_);
v___x_3420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___redArg(v_as_3396_, v_sz_3397_, v___x_3419_, v___x_3417_);
return v___x_3420_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6___boxed(lean_object* v_as_3428_, lean_object* v_sz_3429_, lean_object* v_i_3430_, lean_object* v_b_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_){
_start:
{
size_t v_sz_boxed_3439_; size_t v_i_boxed_3440_; lean_object* v_res_3441_; 
v_sz_boxed_3439_ = lean_unbox_usize(v_sz_3429_);
lean_dec(v_sz_3429_);
v_i_boxed_3440_ = lean_unbox_usize(v_i_3430_);
lean_dec(v_i_3430_);
v_res_3441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6(v_as_3428_, v_sz_boxed_3439_, v_i_boxed_3440_, v_b_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_);
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec_ref(v_as_3428_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0(lean_object* v_init_3442_, lean_object* v_n_3443_, lean_object* v_b_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
if (lean_obj_tag(v_n_3443_) == 0)
{
lean_object* v_cs_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; size_t v_sz_3455_; size_t v___x_3456_; lean_object* v___x_3457_; 
v_cs_3452_ = lean_ctor_get(v_n_3443_, 0);
v___x_3453_ = lean_box(0);
v___x_3454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3453_);
lean_ctor_set(v___x_3454_, 1, v_b_3444_);
v_sz_3455_ = lean_array_size(v_cs_3452_);
v___x_3456_ = ((size_t)0ULL);
v___x_3457_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__5(v_init_3442_, v_cs_3452_, v_sz_3455_, v___x_3456_, v___x_3454_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3472_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3460_ = v___x_3457_;
v_isShared_3461_ = v_isSharedCheck_3472_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3458_);
lean_dec(v___x_3457_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3472_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v_fst_3462_; 
v_fst_3462_ = lean_ctor_get(v_a_3458_, 0);
if (lean_obj_tag(v_fst_3462_) == 0)
{
lean_object* v_snd_3463_; lean_object* v___x_3464_; lean_object* v___x_3466_; 
v_snd_3463_ = lean_ctor_get(v_a_3458_, 1);
lean_inc(v_snd_3463_);
lean_dec(v_a_3458_);
v___x_3464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3464_, 0, v_snd_3463_);
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 0, v___x_3464_);
v___x_3466_ = v___x_3460_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3464_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
else
{
lean_object* v_val_3468_; lean_object* v___x_3470_; 
lean_inc_ref(v_fst_3462_);
lean_dec(v_a_3458_);
v_val_3468_ = lean_ctor_get(v_fst_3462_, 0);
lean_inc(v_val_3468_);
lean_dec_ref_known(v_fst_3462_, 1);
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 0, v_val_3468_);
v___x_3470_ = v___x_3460_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_val_3468_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
v_a_3473_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3457_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3457_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3478_; 
if (v_isShared_3476_ == 0)
{
v___x_3478_ = v___x_3475_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
else
{
lean_object* v_vs_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; size_t v_sz_3484_; size_t v___x_3485_; lean_object* v___x_3486_; 
v_vs_3481_ = lean_ctor_get(v_n_3443_, 0);
v___x_3482_ = lean_box(0);
v___x_3483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3482_);
lean_ctor_set(v___x_3483_, 1, v_b_3444_);
v_sz_3484_ = lean_array_size(v_vs_3481_);
v___x_3485_ = ((size_t)0ULL);
v___x_3486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6(v_vs_3481_, v_sz_3484_, v___x_3485_, v___x_3483_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3501_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3489_ = v___x_3486_;
v_isShared_3490_ = v_isSharedCheck_3501_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3486_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3501_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v_fst_3491_; 
v_fst_3491_ = lean_ctor_get(v_a_3487_, 0);
if (lean_obj_tag(v_fst_3491_) == 0)
{
lean_object* v_snd_3492_; lean_object* v___x_3493_; lean_object* v___x_3495_; 
v_snd_3492_ = lean_ctor_get(v_a_3487_, 1);
lean_inc(v_snd_3492_);
lean_dec(v_a_3487_);
v___x_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3493_, 0, v_snd_3492_);
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 0, v___x_3493_);
v___x_3495_ = v___x_3489_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3493_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
else
{
lean_object* v_val_3497_; lean_object* v___x_3499_; 
lean_inc_ref(v_fst_3491_);
lean_dec(v_a_3487_);
v_val_3497_ = lean_ctor_get(v_fst_3491_, 0);
lean_inc(v_val_3497_);
lean_dec_ref_known(v_fst_3491_, 1);
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 0, v_val_3497_);
v___x_3499_ = v___x_3489_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_val_3497_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
else
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3509_; 
v_a_3502_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3504_ = v___x_3486_;
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3486_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3507_; 
if (v_isShared_3505_ == 0)
{
v___x_3507_ = v___x_3504_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_a_3502_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__5(lean_object* v_init_3510_, lean_object* v_as_3511_, size_t v_sz_3512_, size_t v_i_3513_, lean_object* v_b_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
uint8_t v___x_3522_; 
v___x_3522_ = lean_usize_dec_lt(v_i_3513_, v_sz_3512_);
if (v___x_3522_ == 0)
{
lean_object* v___x_3523_; 
v___x_3523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3523_, 0, v_b_3514_);
return v___x_3523_;
}
else
{
lean_object* v_snd_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3558_; 
v_snd_3524_ = lean_ctor_get(v_b_3514_, 1);
v_isSharedCheck_3558_ = !lean_is_exclusive(v_b_3514_);
if (v_isSharedCheck_3558_ == 0)
{
lean_object* v_unused_3559_; 
v_unused_3559_ = lean_ctor_get(v_b_3514_, 0);
lean_dec(v_unused_3559_);
v___x_3526_ = v_b_3514_;
v_isShared_3527_ = v_isSharedCheck_3558_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_snd_3524_);
lean_dec(v_b_3514_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3558_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3528_; lean_object* v_a_3529_; lean_object* v___x_3530_; 
v___x_3528_ = lean_box(0);
v_a_3529_ = lean_array_uget_borrowed(v_as_3511_, v_i_3513_);
lean_inc(v_snd_3524_);
v___x_3530_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0(v_init_3510_, v_a_3529_, v_snd_3524_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3549_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3533_ = v___x_3530_;
v_isShared_3534_ = v_isSharedCheck_3549_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3530_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3549_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
if (lean_obj_tag(v_a_3531_) == 0)
{
lean_object* v___x_3535_; lean_object* v___x_3537_; 
v___x_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3535_, 0, v_a_3531_);
if (v_isShared_3527_ == 0)
{
lean_ctor_set(v___x_3526_, 0, v___x_3535_);
v___x_3537_ = v___x_3526_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3535_);
lean_ctor_set(v_reuseFailAlloc_3541_, 1, v_snd_3524_);
v___x_3537_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
lean_object* v___x_3539_; 
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 0, v___x_3537_);
v___x_3539_ = v___x_3533_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3537_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
else
{
lean_object* v_a_3542_; lean_object* v___x_3544_; 
lean_del_object(v___x_3533_);
lean_dec(v_snd_3524_);
v_a_3542_ = lean_ctor_get(v_a_3531_, 0);
lean_inc(v_a_3542_);
lean_dec_ref_known(v_a_3531_, 1);
if (v_isShared_3527_ == 0)
{
lean_ctor_set(v___x_3526_, 1, v_a_3542_);
lean_ctor_set(v___x_3526_, 0, v___x_3528_);
v___x_3544_ = v___x_3526_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3528_);
lean_ctor_set(v_reuseFailAlloc_3548_, 1, v_a_3542_);
v___x_3544_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
size_t v___x_3545_; size_t v___x_3546_; 
v___x_3545_ = ((size_t)1ULL);
v___x_3546_ = lean_usize_add(v_i_3513_, v___x_3545_);
v_i_3513_ = v___x_3546_;
v_b_3514_ = v___x_3544_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3557_; 
lean_del_object(v___x_3526_);
lean_dec(v_snd_3524_);
v_a_3550_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3552_ = v___x_3530_;
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_a_3550_);
lean_dec(v___x_3530_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3555_; 
if (v_isShared_3553_ == 0)
{
v___x_3555_ = v___x_3552_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_a_3550_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
return v___x_3555_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__5___boxed(lean_object* v_init_3560_, lean_object* v_as_3561_, lean_object* v_sz_3562_, lean_object* v_i_3563_, lean_object* v_b_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_){
_start:
{
size_t v_sz_boxed_3572_; size_t v_i_boxed_3573_; lean_object* v_res_3574_; 
v_sz_boxed_3572_ = lean_unbox_usize(v_sz_3562_);
lean_dec(v_sz_3562_);
v_i_boxed_3573_ = lean_unbox_usize(v_i_3563_);
lean_dec(v_i_3563_);
v_res_3574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__5(v_init_3560_, v_as_3561_, v_sz_boxed_3572_, v_i_boxed_3573_, v_b_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec_ref(v_as_3561_);
lean_dec_ref(v_init_3560_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0___boxed(lean_object* v_init_3575_, lean_object* v_n_3576_, lean_object* v_b_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0(v_init_3575_, v_n_3576_, v_b_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_);
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3579_);
lean_dec_ref(v___y_3578_);
lean_dec_ref(v_n_3576_);
lean_dec_ref(v_init_3575_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0(lean_object* v_t_3586_, lean_object* v_init_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v_root_3595_; lean_object* v_tail_3596_; lean_object* v___x_3597_; 
v_root_3595_ = lean_ctor_get(v_t_3586_, 0);
v_tail_3596_ = lean_ctor_get(v_t_3586_, 1);
lean_inc_ref(v_init_3587_);
v___x_3597_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0(v_init_3587_, v_root_3595_, v_init_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
lean_dec_ref(v_init_3587_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3634_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3600_ = v___x_3597_;
v_isShared_3601_ = v_isSharedCheck_3634_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3597_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3634_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
if (lean_obj_tag(v_a_3598_) == 0)
{
lean_object* v_a_3602_; lean_object* v___x_3604_; 
v_a_3602_ = lean_ctor_get(v_a_3598_, 0);
lean_inc(v_a_3602_);
lean_dec_ref_known(v_a_3598_, 1);
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 0, v_a_3602_);
v___x_3604_ = v___x_3600_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3602_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
else
{
lean_object* v_a_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; size_t v_sz_3609_; size_t v___x_3610_; lean_object* v___x_3611_; 
lean_del_object(v___x_3600_);
v_a_3606_ = lean_ctor_get(v_a_3598_, 0);
lean_inc(v_a_3606_);
lean_dec_ref_known(v_a_3598_, 1);
v___x_3607_ = lean_box(0);
v___x_3608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3607_);
lean_ctor_set(v___x_3608_, 1, v_a_3606_);
v_sz_3609_ = lean_array_size(v_tail_3596_);
v___x_3610_ = ((size_t)0ULL);
v___x_3611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1(v_tail_3596_, v_sz_3609_, v___x_3610_, v___x_3608_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
if (lean_obj_tag(v___x_3611_) == 0)
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3625_; 
v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3614_ = v___x_3611_;
v_isShared_3615_ = v_isSharedCheck_3625_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3611_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3625_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v_fst_3616_; 
v_fst_3616_ = lean_ctor_get(v_a_3612_, 0);
if (lean_obj_tag(v_fst_3616_) == 0)
{
lean_object* v_snd_3617_; lean_object* v___x_3619_; 
v_snd_3617_ = lean_ctor_get(v_a_3612_, 1);
lean_inc(v_snd_3617_);
lean_dec(v_a_3612_);
if (v_isShared_3615_ == 0)
{
lean_ctor_set(v___x_3614_, 0, v_snd_3617_);
v___x_3619_ = v___x_3614_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_snd_3617_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
else
{
lean_object* v_val_3621_; lean_object* v___x_3623_; 
lean_inc_ref(v_fst_3616_);
lean_dec(v_a_3612_);
v_val_3621_ = lean_ctor_get(v_fst_3616_, 0);
lean_inc(v_val_3621_);
lean_dec_ref_known(v_fst_3616_, 1);
if (v_isShared_3615_ == 0)
{
lean_ctor_set(v___x_3614_, 0, v_val_3621_);
v___x_3623_ = v___x_3614_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_val_3621_);
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
else
{
lean_object* v_a_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3633_; 
v_a_3626_ = lean_ctor_get(v___x_3611_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3628_ = v___x_3611_;
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_a_3626_);
lean_dec(v___x_3611_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3631_; 
if (v_isShared_3629_ == 0)
{
v___x_3631_ = v___x_3628_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_a_3626_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
}
}
}
}
}
}
else
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
v_a_3635_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3637_ = v___x_3597_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3597_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0___boxed(lean_object* v_t_3643_, lean_object* v_init_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
lean_object* v_res_3652_; 
v_res_3652_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0(v_t_3643_, v_init_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
lean_dec(v___y_3648_);
lean_dec_ref(v___y_3647_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec_ref(v_t_3643_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__1(size_t v_sz_3653_, size_t v_i_3654_, lean_object* v_bs_3655_){
_start:
{
uint8_t v___x_3656_; 
v___x_3656_ = lean_usize_dec_lt(v_i_3654_, v_sz_3653_);
if (v___x_3656_ == 0)
{
return v_bs_3655_;
}
else
{
lean_object* v_v_3657_; lean_object* v___x_3658_; lean_object* v_bs_x27_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; size_t v___x_3662_; size_t v___x_3663_; lean_object* v___x_3664_; 
v_v_3657_ = lean_array_uget(v_bs_3655_, v_i_3654_);
v___x_3658_ = lean_unsigned_to_nat(0u);
v_bs_x27_3659_ = lean_array_uset(v_bs_3655_, v_i_3654_, v___x_3658_);
v___x_3660_ = l_Lean_LocalDecl_fvarId(v_v_3657_);
lean_dec(v_v_3657_);
v___x_3661_ = l_Lean_mkFVar(v___x_3660_);
v___x_3662_ = ((size_t)1ULL);
v___x_3663_ = lean_usize_add(v_i_3654_, v___x_3662_);
v___x_3664_ = lean_array_uset(v_bs_x27_3659_, v_i_3654_, v___x_3661_);
v_i_3654_ = v___x_3663_;
v_bs_3655_ = v___x_3664_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__1___boxed(lean_object* v_sz_3666_, lean_object* v_i_3667_, lean_object* v_bs_3668_){
_start:
{
size_t v_sz_boxed_3669_; size_t v_i_boxed_3670_; lean_object* v_res_3671_; 
v_sz_boxed_3669_ = lean_unbox_usize(v_sz_3666_);
lean_dec(v_sz_3666_);
v_i_boxed_3670_ = lean_unbox_usize(v_i_3667_);
lean_dec(v_i_3667_);
v_res_3671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__1(v_sz_boxed_3669_, v_i_boxed_3670_, v_bs_3668_);
return v_res_3671_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3677_ = lean_box(0);
v___x_3678_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__1));
v___x_3679_ = l_Lean_Expr_const___override(v___x_3678_, v___x_3677_);
return v___x_3679_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6(void){
_start:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3685_ = lean_box(0);
v___x_3686_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__5));
v___x_3687_ = l_Lean_mkConst(v___x_3686_, v___x_3685_);
return v___x_3687_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v___x_3692_ = lean_box(0);
v___x_3693_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__8));
v___x_3694_ = l_Lean_mkConst(v___x_3693_, v___x_3692_);
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg(size_t v_sz_3695_, size_t v_i_3696_, lean_object* v_bs_3697_){
_start:
{
uint8_t v___x_3699_; 
v___x_3699_ = lean_usize_dec_lt(v_i_3696_, v_sz_3695_);
if (v___x_3699_ == 0)
{
lean_object* v___x_3700_; 
v___x_3700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3700_, 0, v_bs_3697_);
return v___x_3700_;
}
else
{
lean_object* v_v_3701_; lean_object* v_module_3702_; uint8_t v_importAll_3703_; uint8_t v_isExported_3704_; uint8_t v_isMeta_3705_; lean_object* v___x_3706_; lean_object* v_bs_x27_3707_; lean_object* v___x_3708_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3731_; 
v_v_3701_ = lean_array_uget_borrowed(v_bs_3697_, v_i_3696_);
v_module_3702_ = lean_ctor_get(v_v_3701_, 0);
lean_inc(v_module_3702_);
v_importAll_3703_ = lean_ctor_get_uint8(v_v_3701_, sizeof(void*)*1);
v_isExported_3704_ = lean_ctor_get_uint8(v_v_3701_, sizeof(void*)*1 + 1);
v_isMeta_3705_ = lean_ctor_get_uint8(v_v_3701_, sizeof(void*)*1 + 2);
v___x_3706_ = lean_unsigned_to_nat(0u);
v_bs_x27_3707_ = lean_array_uset(v_bs_3697_, v_i_3696_, v___x_3706_);
v___x_3708_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_module_3702_);
if (v_importAll_3703_ == 0)
{
lean_object* v___x_3734_; 
v___x_3734_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6);
v___y_3731_ = v___x_3734_;
goto v___jp_3730_;
}
else
{
lean_object* v___x_3735_; 
v___x_3735_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9);
v___y_3731_ = v___x_3735_;
goto v___jp_3730_;
}
v___jp_3709_:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; size_t v___x_3721_; size_t v___x_3722_; lean_object* v___x_3723_; 
v___x_3713_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__2);
v___x_3714_ = lean_unsigned_to_nat(4u);
v___x_3715_ = lean_mk_empty_array_with_capacity(v___x_3714_);
v___x_3716_ = lean_array_push(v___x_3715_, v___x_3708_);
lean_inc_ref(v___y_3711_);
v___x_3717_ = lean_array_push(v___x_3716_, v___y_3711_);
lean_inc_ref(v___y_3710_);
v___x_3718_ = lean_array_push(v___x_3717_, v___y_3710_);
lean_inc_ref(v___y_3712_);
v___x_3719_ = lean_array_push(v___x_3718_, v___y_3712_);
v___x_3720_ = l_Lean_mkAppN(v___x_3713_, v___x_3719_);
lean_dec_ref(v___x_3719_);
v___x_3721_ = ((size_t)1ULL);
v___x_3722_ = lean_usize_add(v_i_3696_, v___x_3721_);
v___x_3723_ = lean_array_uset(v_bs_x27_3707_, v_i_3696_, v___x_3720_);
v_i_3696_ = v___x_3722_;
v_bs_3697_ = v___x_3723_;
goto _start;
}
v___jp_3725_:
{
if (v_isMeta_3705_ == 0)
{
lean_object* v___x_3728_; 
v___x_3728_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6);
v___y_3710_ = v___y_3727_;
v___y_3711_ = v___y_3726_;
v___y_3712_ = v___x_3728_;
goto v___jp_3709_;
}
else
{
lean_object* v___x_3729_; 
v___x_3729_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9);
v___y_3710_ = v___y_3727_;
v___y_3711_ = v___y_3726_;
v___y_3712_ = v___x_3729_;
goto v___jp_3709_;
}
}
v___jp_3730_:
{
if (v_isExported_3704_ == 0)
{
lean_object* v___x_3732_; 
v___x_3732_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6);
v___y_3726_ = v___y_3731_;
v___y_3727_ = v___x_3732_;
goto v___jp_3725_;
}
else
{
lean_object* v___x_3733_; 
v___x_3733_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9);
v___y_3726_ = v___y_3731_;
v___y_3727_ = v___x_3733_;
goto v___jp_3725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___boxed(lean_object* v_sz_3736_, lean_object* v_i_3737_, lean_object* v_bs_3738_, lean_object* v___y_3739_){
_start:
{
size_t v_sz_boxed_3740_; size_t v_i_boxed_3741_; lean_object* v_res_3742_; 
v_sz_boxed_3740_ = lean_unbox_usize(v_sz_3736_);
lean_dec(v_sz_3736_);
v_i_boxed_3741_ = lean_unbox_usize(v_i_3737_);
lean_dec(v_i_3737_);
v_res_3742_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg(v_sz_boxed_3740_, v_i_boxed_3741_, v_bs_3738_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12_spec__20___redArg(lean_object* v_x_3743_, lean_object* v_x_3744_, lean_object* v_x_3745_, lean_object* v_x_3746_){
_start:
{
lean_object* v_ks_3747_; lean_object* v_vs_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3772_; 
v_ks_3747_ = lean_ctor_get(v_x_3743_, 0);
v_vs_3748_ = lean_ctor_get(v_x_3743_, 1);
v_isSharedCheck_3772_ = !lean_is_exclusive(v_x_3743_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3750_ = v_x_3743_;
v_isShared_3751_ = v_isSharedCheck_3772_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_vs_3748_);
lean_inc(v_ks_3747_);
lean_dec(v_x_3743_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3772_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3752_; uint8_t v___x_3753_; 
v___x_3752_ = lean_array_get_size(v_ks_3747_);
v___x_3753_ = lean_nat_dec_lt(v_x_3744_, v___x_3752_);
if (v___x_3753_ == 0)
{
lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3757_; 
lean_dec(v_x_3744_);
v___x_3754_ = lean_array_push(v_ks_3747_, v_x_3745_);
v___x_3755_ = lean_array_push(v_vs_3748_, v_x_3746_);
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 1, v___x_3755_);
lean_ctor_set(v___x_3750_, 0, v___x_3754_);
v___x_3757_ = v___x_3750_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v___x_3754_);
lean_ctor_set(v_reuseFailAlloc_3758_, 1, v___x_3755_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
}
}
else
{
lean_object* v_k_x27_3759_; uint8_t v___x_3760_; 
v_k_x27_3759_ = lean_array_fget_borrowed(v_ks_3747_, v_x_3744_);
v___x_3760_ = l_Lean_instBEqFVarId_beq(v_x_3745_, v_k_x27_3759_);
if (v___x_3760_ == 0)
{
lean_object* v___x_3762_; 
if (v_isShared_3751_ == 0)
{
v___x_3762_ = v___x_3750_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_ks_3747_);
lean_ctor_set(v_reuseFailAlloc_3766_, 1, v_vs_3748_);
v___x_3762_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3763_ = lean_unsigned_to_nat(1u);
v___x_3764_ = lean_nat_add(v_x_3744_, v___x_3763_);
lean_dec(v_x_3744_);
v_x_3743_ = v___x_3762_;
v_x_3744_ = v___x_3764_;
goto _start;
}
}
else
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3770_; 
v___x_3767_ = lean_array_fset(v_ks_3747_, v_x_3744_, v_x_3745_);
v___x_3768_ = lean_array_fset(v_vs_3748_, v_x_3744_, v_x_3746_);
lean_dec(v_x_3744_);
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 1, v___x_3768_);
lean_ctor_set(v___x_3750_, 0, v___x_3767_);
v___x_3770_ = v___x_3750_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3767_);
lean_ctor_set(v_reuseFailAlloc_3771_, 1, v___x_3768_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12___redArg(lean_object* v_n_3773_, lean_object* v_k_3774_, lean_object* v_v_3775_){
_start:
{
lean_object* v___x_3776_; lean_object* v___x_3777_; 
v___x_3776_ = lean_unsigned_to_nat(0u);
v___x_3777_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12_spec__20___redArg(v_n_3773_, v___x_3776_, v_k_3774_, v_v_3775_);
return v___x_3777_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_3778_; 
v___x_3778_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_3778_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg(lean_object* v_x_3779_, size_t v_x_3780_, size_t v_x_3781_, lean_object* v_x_3782_, lean_object* v_x_3783_){
_start:
{
if (lean_obj_tag(v_x_3779_) == 0)
{
lean_object* v_es_3784_; size_t v___x_3785_; size_t v___x_3786_; lean_object* v_j_3787_; lean_object* v___x_3788_; uint8_t v___x_3789_; 
v_es_3784_ = lean_ctor_get(v_x_3779_, 0);
v___x_3785_ = ((size_t)31ULL);
v___x_3786_ = lean_usize_land(v_x_3780_, v___x_3785_);
v_j_3787_ = lean_usize_to_nat(v___x_3786_);
v___x_3788_ = lean_array_get_size(v_es_3784_);
v___x_3789_ = lean_nat_dec_lt(v_j_3787_, v___x_3788_);
if (v___x_3789_ == 0)
{
lean_dec(v_j_3787_);
lean_dec(v_x_3783_);
lean_dec(v_x_3782_);
return v_x_3779_;
}
else
{
lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3828_; 
lean_inc_ref(v_es_3784_);
v_isSharedCheck_3828_ = !lean_is_exclusive(v_x_3779_);
if (v_isSharedCheck_3828_ == 0)
{
lean_object* v_unused_3829_; 
v_unused_3829_ = lean_ctor_get(v_x_3779_, 0);
lean_dec(v_unused_3829_);
v___x_3791_ = v_x_3779_;
v_isShared_3792_ = v_isSharedCheck_3828_;
goto v_resetjp_3790_;
}
else
{
lean_dec(v_x_3779_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3828_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v_v_3793_; lean_object* v___x_3794_; lean_object* v_xs_x27_3795_; lean_object* v___y_3797_; 
v_v_3793_ = lean_array_fget(v_es_3784_, v_j_3787_);
v___x_3794_ = lean_box(0);
v_xs_x27_3795_ = lean_array_fset(v_es_3784_, v_j_3787_, v___x_3794_);
switch(lean_obj_tag(v_v_3793_))
{
case 0:
{
lean_object* v_key_3802_; lean_object* v_val_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3813_; 
v_key_3802_ = lean_ctor_get(v_v_3793_, 0);
v_val_3803_ = lean_ctor_get(v_v_3793_, 1);
v_isSharedCheck_3813_ = !lean_is_exclusive(v_v_3793_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3805_ = v_v_3793_;
v_isShared_3806_ = v_isSharedCheck_3813_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_val_3803_);
lean_inc(v_key_3802_);
lean_dec(v_v_3793_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3813_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
uint8_t v___x_3807_; 
v___x_3807_ = l_Lean_instBEqFVarId_beq(v_x_3782_, v_key_3802_);
if (v___x_3807_ == 0)
{
lean_object* v___x_3808_; lean_object* v___x_3809_; 
lean_del_object(v___x_3805_);
v___x_3808_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3802_, v_val_3803_, v_x_3782_, v_x_3783_);
v___x_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3808_);
v___y_3797_ = v___x_3809_;
goto v___jp_3796_;
}
else
{
lean_object* v___x_3811_; 
lean_dec(v_val_3803_);
lean_dec(v_key_3802_);
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 1, v_x_3783_);
lean_ctor_set(v___x_3805_, 0, v_x_3782_);
v___x_3811_ = v___x_3805_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_x_3782_);
lean_ctor_set(v_reuseFailAlloc_3812_, 1, v_x_3783_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
v___y_3797_ = v___x_3811_;
goto v___jp_3796_;
}
}
}
}
case 1:
{
lean_object* v_node_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3826_; 
v_node_3814_ = lean_ctor_get(v_v_3793_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v_v_3793_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3816_ = v_v_3793_;
v_isShared_3817_ = v_isSharedCheck_3826_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_node_3814_);
lean_dec(v_v_3793_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3826_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
size_t v___x_3818_; size_t v___x_3819_; size_t v___x_3820_; size_t v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3824_; 
v___x_3818_ = ((size_t)5ULL);
v___x_3819_ = lean_usize_shift_right(v_x_3780_, v___x_3818_);
v___x_3820_ = ((size_t)1ULL);
v___x_3821_ = lean_usize_add(v_x_3781_, v___x_3820_);
v___x_3822_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg(v_node_3814_, v___x_3819_, v___x_3821_, v_x_3782_, v_x_3783_);
if (v_isShared_3817_ == 0)
{
lean_ctor_set(v___x_3816_, 0, v___x_3822_);
v___x_3824_ = v___x_3816_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v___x_3822_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
v___y_3797_ = v___x_3824_;
goto v___jp_3796_;
}
}
}
default: 
{
lean_object* v___x_3827_; 
v___x_3827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3827_, 0, v_x_3782_);
lean_ctor_set(v___x_3827_, 1, v_x_3783_);
v___y_3797_ = v___x_3827_;
goto v___jp_3796_;
}
}
v___jp_3796_:
{
lean_object* v___x_3798_; lean_object* v___x_3800_; 
v___x_3798_ = lean_array_fset(v_xs_x27_3795_, v_j_3787_, v___y_3797_);
lean_dec(v_j_3787_);
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 0, v___x_3798_);
v___x_3800_ = v___x_3791_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___x_3798_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
}
}
else
{
lean_object* v_ks_3830_; lean_object* v_vs_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3849_; 
v_ks_3830_ = lean_ctor_get(v_x_3779_, 0);
v_vs_3831_ = lean_ctor_get(v_x_3779_, 1);
v_isSharedCheck_3849_ = !lean_is_exclusive(v_x_3779_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3833_ = v_x_3779_;
v_isShared_3834_ = v_isSharedCheck_3849_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_vs_3831_);
lean_inc(v_ks_3830_);
lean_dec(v_x_3779_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3849_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v___x_3836_; 
if (v_isShared_3834_ == 0)
{
v___x_3836_ = v___x_3833_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_ks_3830_);
lean_ctor_set(v_reuseFailAlloc_3848_, 1, v_vs_3831_);
v___x_3836_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
lean_object* v_newNode_3837_; size_t v___x_3838_; uint8_t v___x_3839_; 
v_newNode_3837_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12___redArg(v___x_3836_, v_x_3782_, v_x_3783_);
v___x_3838_ = ((size_t)7ULL);
v___x_3839_ = lean_usize_dec_le(v___x_3838_, v_x_3781_);
if (v___x_3839_ == 0)
{
lean_object* v___x_3840_; lean_object* v___x_3841_; uint8_t v___x_3842_; 
v___x_3840_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3837_);
v___x_3841_ = lean_unsigned_to_nat(4u);
v___x_3842_ = lean_nat_dec_lt(v___x_3840_, v___x_3841_);
lean_dec(v___x_3840_);
if (v___x_3842_ == 0)
{
lean_object* v_ks_3843_; lean_object* v_vs_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; 
v_ks_3843_ = lean_ctor_get(v_newNode_3837_, 0);
lean_inc_ref(v_ks_3843_);
v_vs_3844_ = lean_ctor_get(v_newNode_3837_, 1);
lean_inc_ref(v_vs_3844_);
lean_dec_ref(v_newNode_3837_);
v___x_3845_ = lean_unsigned_to_nat(0u);
v___x_3846_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg___closed__0);
v___x_3847_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___redArg(v_x_3781_, v_ks_3843_, v_vs_3844_, v___x_3845_, v___x_3846_);
lean_dec_ref(v_vs_3844_);
lean_dec_ref(v_ks_3843_);
return v___x_3847_;
}
else
{
return v_newNode_3837_;
}
}
else
{
return v_newNode_3837_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___redArg(size_t v_depth_3850_, lean_object* v_keys_3851_, lean_object* v_vals_3852_, lean_object* v_i_3853_, lean_object* v_entries_3854_){
_start:
{
lean_object* v___x_3855_; uint8_t v___x_3856_; 
v___x_3855_ = lean_array_get_size(v_keys_3851_);
v___x_3856_ = lean_nat_dec_lt(v_i_3853_, v___x_3855_);
if (v___x_3856_ == 0)
{
lean_dec(v_i_3853_);
return v_entries_3854_;
}
else
{
lean_object* v_k_3857_; lean_object* v_v_3858_; uint64_t v___x_3859_; size_t v_h_3860_; size_t v___x_3861_; lean_object* v___x_3862_; size_t v___x_3863_; size_t v___x_3864_; size_t v___x_3865_; size_t v_h_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; 
v_k_3857_ = lean_array_fget_borrowed(v_keys_3851_, v_i_3853_);
v_v_3858_ = lean_array_fget_borrowed(v_vals_3852_, v_i_3853_);
v___x_3859_ = l_Lean_instHashableFVarId_hash(v_k_3857_);
v_h_3860_ = lean_uint64_to_usize(v___x_3859_);
v___x_3861_ = ((size_t)5ULL);
v___x_3862_ = lean_unsigned_to_nat(1u);
v___x_3863_ = ((size_t)1ULL);
v___x_3864_ = lean_usize_sub(v_depth_3850_, v___x_3863_);
v___x_3865_ = lean_usize_mul(v___x_3861_, v___x_3864_);
v_h_3866_ = lean_usize_shift_right(v_h_3860_, v___x_3865_);
v___x_3867_ = lean_nat_add(v_i_3853_, v___x_3862_);
lean_dec(v_i_3853_);
lean_inc(v_v_3858_);
lean_inc(v_k_3857_);
v___x_3868_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg(v_entries_3854_, v_h_3866_, v_depth_3850_, v_k_3857_, v_v_3858_);
v_i_3853_ = v___x_3867_;
v_entries_3854_ = v___x_3868_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___redArg___boxed(lean_object* v_depth_3870_, lean_object* v_keys_3871_, lean_object* v_vals_3872_, lean_object* v_i_3873_, lean_object* v_entries_3874_){
_start:
{
size_t v_depth_boxed_3875_; lean_object* v_res_3876_; 
v_depth_boxed_3875_ = lean_unbox_usize(v_depth_3870_);
lean_dec(v_depth_3870_);
v_res_3876_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___redArg(v_depth_boxed_3875_, v_keys_3871_, v_vals_3872_, v_i_3873_, v_entries_3874_);
lean_dec_ref(v_vals_3872_);
lean_dec_ref(v_keys_3871_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg___boxed(lean_object* v_x_3877_, lean_object* v_x_3878_, lean_object* v_x_3879_, lean_object* v_x_3880_, lean_object* v_x_3881_){
_start:
{
size_t v_x_35342__boxed_3882_; size_t v_x_35343__boxed_3883_; lean_object* v_res_3884_; 
v_x_35342__boxed_3882_ = lean_unbox_usize(v_x_3878_);
lean_dec(v_x_3878_);
v_x_35343__boxed_3883_ = lean_unbox_usize(v_x_3879_);
lean_dec(v_x_3879_);
v_res_3884_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg(v_x_3877_, v_x_35342__boxed_3882_, v_x_35343__boxed_3883_, v_x_3880_, v_x_3881_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2___redArg(lean_object* v_x_3885_, lean_object* v_x_3886_, lean_object* v_x_3887_){
_start:
{
uint64_t v___x_3888_; size_t v___x_3889_; size_t v___x_3890_; lean_object* v___x_3891_; 
v___x_3888_ = l_Lean_instHashableFVarId_hash(v_x_3886_);
v___x_3889_ = lean_uint64_to_usize(v___x_3888_);
v___x_3890_ = ((size_t)1ULL);
v___x_3891_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg(v_x_3885_, v___x_3889_, v___x_3890_, v_x_3886_, v_x_3887_);
return v___x_3891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__11(lean_object* v_as_3892_, size_t v_i_3893_, size_t v_stop_3894_, lean_object* v_b_3895_){
_start:
{
lean_object* v___y_3897_; uint8_t v___x_3901_; 
v___x_3901_ = lean_usize_dec_eq(v_i_3893_, v_stop_3894_);
if (v___x_3901_ == 0)
{
lean_object* v_fvarIdToDecl_3902_; lean_object* v_decls_3903_; lean_object* v_auxDeclToFullName_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v_fvarIdToDecl_3902_ = lean_ctor_get(v_b_3895_, 0);
v_decls_3903_ = lean_ctor_get(v_b_3895_, 1);
v_auxDeclToFullName_3904_ = lean_ctor_get(v_b_3895_, 2);
v___x_3905_ = lean_array_uget_borrowed(v_as_3892_, v_i_3893_);
v___x_3906_ = l_Lean_LocalDecl_fvarId(v___x_3905_);
lean_inc_ref(v_b_3895_);
v___x_3907_ = lean_local_ctx_find(v_b_3895_, v___x_3906_);
if (lean_obj_tag(v___x_3907_) == 0)
{
v___y_3897_ = v_b_3895_;
goto v___jp_3896_;
}
else
{
lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3933_; 
lean_inc(v_auxDeclToFullName_3904_);
lean_inc_ref(v_decls_3903_);
lean_inc_ref(v_fvarIdToDecl_3902_);
v_isSharedCheck_3933_ = !lean_is_exclusive(v_b_3895_);
if (v_isSharedCheck_3933_ == 0)
{
lean_object* v_unused_3934_; lean_object* v_unused_3935_; lean_object* v_unused_3936_; 
v_unused_3934_ = lean_ctor_get(v_b_3895_, 2);
lean_dec(v_unused_3934_);
v_unused_3935_ = lean_ctor_get(v_b_3895_, 1);
lean_dec(v_unused_3935_);
v_unused_3936_ = lean_ctor_get(v_b_3895_, 0);
lean_dec(v_unused_3936_);
v___x_3909_ = v_b_3895_;
v_isShared_3910_ = v_isSharedCheck_3933_;
goto v_resetjp_3908_;
}
else
{
lean_dec(v_b_3895_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3933_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v_val_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3932_; 
v_val_3911_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3913_ = v___x_3907_;
v_isShared_3914_ = v_isSharedCheck_3932_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_val_3911_);
lean_dec(v___x_3907_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3932_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
uint8_t v___x_3915_; lean_object* v___x_3916_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3928_; lean_object* v_fvarId_3931_; 
v___x_3915_ = 1;
v___x_3916_ = l_Lean_LocalDecl_setNondep(v_val_3911_, v___x_3915_);
v_fvarId_3931_ = lean_ctor_get(v___x_3916_, 1);
lean_inc(v_fvarId_3931_);
v___y_3928_ = v_fvarId_3931_;
goto v___jp_3927_;
v___jp_3917_:
{
lean_object* v___x_3921_; 
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 0, v___x_3916_);
v___x_3921_ = v___x_3913_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3916_);
v___x_3921_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
lean_object* v___x_3922_; lean_object* v___x_3924_; 
v___x_3922_ = l_Lean_PersistentArray_set___redArg(v_decls_3903_, v___y_3919_, v___x_3921_);
lean_dec(v___y_3919_);
if (v_isShared_3910_ == 0)
{
lean_ctor_set(v___x_3909_, 1, v___x_3922_);
lean_ctor_set(v___x_3909_, 0, v___y_3918_);
v___x_3924_ = v___x_3909_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___y_3918_);
lean_ctor_set(v_reuseFailAlloc_3925_, 1, v___x_3922_);
lean_ctor_set(v_reuseFailAlloc_3925_, 2, v_auxDeclToFullName_3904_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
v___y_3897_ = v___x_3924_;
goto v___jp_3896_;
}
}
}
v___jp_3927_:
{
lean_object* v___x_3929_; lean_object* v_index_3930_; 
lean_inc_ref(v___x_3916_);
v___x_3929_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2___redArg(v_fvarIdToDecl_3902_, v___y_3928_, v___x_3916_);
v_index_3930_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_index_3930_);
v___y_3918_ = v___x_3929_;
v___y_3919_ = v_index_3930_;
goto v___jp_3917_;
}
}
}
}
}
else
{
return v_b_3895_;
}
v___jp_3896_:
{
size_t v___x_3898_; size_t v___x_3899_; 
v___x_3898_ = ((size_t)1ULL);
v___x_3899_ = lean_usize_add(v_i_3893_, v___x_3898_);
v_i_3893_ = v___x_3899_;
v_b_3895_ = v___y_3897_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__11___boxed(lean_object* v_as_3937_, lean_object* v_i_3938_, lean_object* v_stop_3939_, lean_object* v_b_3940_){
_start:
{
size_t v_i_boxed_3941_; size_t v_stop_boxed_3942_; lean_object* v_res_3943_; 
v_i_boxed_3941_ = lean_unbox_usize(v_i_3938_);
lean_dec(v_i_3938_);
v_stop_boxed_3942_ = lean_unbox_usize(v_stop_3939_);
lean_dec(v_stop_3939_);
v_res_3943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__11(v_as_3937_, v_i_boxed_3941_, v_stop_boxed_3942_, v_b_3940_);
lean_dec_ref(v_as_3937_);
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__15(lean_object* v_msgData_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
lean_object* v___x_3950_; lean_object* v_env_3951_; uint8_t v___x_3952_; lean_object* v_env_3953_; lean_object* v___x_3954_; lean_object* v_toCold_3955_; lean_object* v_mctx_3956_; lean_object* v_lctx_3957_; lean_object* v_options_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3950_ = lean_st_ref_get(v___y_3948_);
v_env_3951_ = lean_ctor_get(v___x_3950_, 0);
lean_inc_ref(v_env_3951_);
lean_dec(v___x_3950_);
v___x_3952_ = 0;
v_env_3953_ = l_Lean_Environment_setRecordingDeps(v_env_3951_, v___x_3952_);
v___x_3954_ = lean_st_ref_get(v___y_3946_);
v_toCold_3955_ = lean_ctor_get(v___y_3947_, 0);
v_mctx_3956_ = lean_ctor_get(v___x_3954_, 0);
lean_inc_ref(v_mctx_3956_);
lean_dec(v___x_3954_);
v_lctx_3957_ = lean_ctor_get(v___y_3945_, 2);
v_options_3958_ = lean_ctor_get(v_toCold_3955_, 2);
lean_inc_ref(v_options_3958_);
lean_inc_ref(v_lctx_3957_);
v___x_3959_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3959_, 0, v_env_3953_);
lean_ctor_set(v___x_3959_, 1, v_mctx_3956_);
lean_ctor_set(v___x_3959_, 2, v_lctx_3957_);
lean_ctor_set(v___x_3959_, 3, v_options_3958_);
v___x_3960_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3959_);
lean_ctor_set(v___x_3960_, 1, v_msgData_3944_);
v___x_3961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3960_);
return v___x_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__15___boxed(lean_object* v_msgData_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_){
_start:
{
lean_object* v_res_3968_; 
v_res_3968_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__15(v_msgData_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec_ref(v___y_3963_);
return v_res_3968_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0(void){
_start:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3969_ = lean_box(1);
v___x_3970_ = l_Lean_MessageData_ofFormat(v___x_3969_);
return v___x_3970_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__3(void){
_start:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3974_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__2));
v___x_3975_ = l_Lean_MessageData_ofFormat(v___x_3974_);
return v___x_3975_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23(lean_object* v_x_3976_, lean_object* v_x_3977_){
_start:
{
if (lean_obj_tag(v_x_3977_) == 0)
{
return v_x_3976_;
}
else
{
lean_object* v_head_3978_; lean_object* v_tail_3979_; lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_4001_; 
v_head_3978_ = lean_ctor_get(v_x_3977_, 0);
v_tail_3979_ = lean_ctor_get(v_x_3977_, 1);
v_isSharedCheck_4001_ = !lean_is_exclusive(v_x_3977_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3981_ = v_x_3977_;
v_isShared_3982_ = v_isSharedCheck_4001_;
goto v_resetjp_3980_;
}
else
{
lean_inc(v_tail_3979_);
lean_inc(v_head_3978_);
lean_dec(v_x_3977_);
v___x_3981_ = lean_box(0);
v_isShared_3982_ = v_isSharedCheck_4001_;
goto v_resetjp_3980_;
}
v_resetjp_3980_:
{
lean_object* v_before_3983_; lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_3999_; 
v_before_3983_ = lean_ctor_get(v_head_3978_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v_head_3978_);
if (v_isSharedCheck_3999_ == 0)
{
lean_object* v_unused_4000_; 
v_unused_4000_ = lean_ctor_get(v_head_3978_, 1);
lean_dec(v_unused_4000_);
v___x_3985_ = v_head_3978_;
v_isShared_3986_ = v_isSharedCheck_3999_;
goto v_resetjp_3984_;
}
else
{
lean_inc(v_before_3983_);
lean_dec(v_head_3978_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_3999_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
lean_object* v___x_3987_; lean_object* v___x_3989_; 
v___x_3987_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0);
if (v_isShared_3986_ == 0)
{
lean_ctor_set_tag(v___x_3985_, 7);
lean_ctor_set(v___x_3985_, 1, v___x_3987_);
lean_ctor_set(v___x_3985_, 0, v_x_3976_);
v___x_3989_ = v___x_3985_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_x_3976_);
lean_ctor_set(v_reuseFailAlloc_3998_, 1, v___x_3987_);
v___x_3989_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
lean_object* v___x_3990_; lean_object* v___x_3992_; 
v___x_3990_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__3);
if (v_isShared_3982_ == 0)
{
lean_ctor_set_tag(v___x_3981_, 7);
lean_ctor_set(v___x_3981_, 1, v___x_3990_);
lean_ctor_set(v___x_3981_, 0, v___x_3989_);
v___x_3992_ = v___x_3981_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v___x_3989_);
lean_ctor_set(v_reuseFailAlloc_3997_, 1, v___x_3990_);
v___x_3992_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3993_ = l_Lean_MessageData_ofSyntax(v_before_3983_);
v___x_3994_ = l_Lean_indentD(v___x_3993_);
v___x_3995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3992_);
lean_ctor_set(v___x_3995_, 1, v___x_3994_);
v_x_3976_ = v___x_3995_;
v_x_3977_ = v_tail_3979_;
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
lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4005_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__1));
v___x_4006_ = l_Lean_MessageData_ofFormat(v___x_4005_);
return v___x_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg(lean_object* v_msgData_4007_, lean_object* v_macroStack_4008_, lean_object* v___y_4009_){
_start:
{
lean_object* v___x_4011_; lean_object* v___x_4012_; uint8_t v___x_4013_; 
v___x_4011_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4009_);
v___x_4012_ = l_Lean_Elab_pp_macroStack;
v___x_4013_ = l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8(v___x_4011_, v___x_4012_);
lean_dec_ref(v___x_4011_);
if (v___x_4013_ == 0)
{
lean_object* v___x_4014_; 
lean_dec(v_macroStack_4008_);
v___x_4014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4014_, 0, v_msgData_4007_);
return v___x_4014_;
}
else
{
if (lean_obj_tag(v_macroStack_4008_) == 0)
{
lean_object* v___x_4015_; 
v___x_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4015_, 0, v_msgData_4007_);
return v___x_4015_;
}
else
{
lean_object* v_head_4016_; lean_object* v_after_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4032_; 
v_head_4016_ = lean_ctor_get(v_macroStack_4008_, 0);
lean_inc(v_head_4016_);
v_after_4017_ = lean_ctor_get(v_head_4016_, 1);
v_isSharedCheck_4032_ = !lean_is_exclusive(v_head_4016_);
if (v_isSharedCheck_4032_ == 0)
{
lean_object* v_unused_4033_; 
v_unused_4033_ = lean_ctor_get(v_head_4016_, 0);
lean_dec(v_unused_4033_);
v___x_4019_ = v_head_4016_;
v_isShared_4020_ = v_isSharedCheck_4032_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_after_4017_);
lean_dec(v_head_4016_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4032_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4021_; lean_object* v___x_4023_; 
v___x_4021_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0);
if (v_isShared_4020_ == 0)
{
lean_ctor_set_tag(v___x_4019_, 7);
lean_ctor_set(v___x_4019_, 1, v___x_4021_);
lean_ctor_set(v___x_4019_, 0, v_msgData_4007_);
v___x_4023_ = v___x_4019_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v_msgData_4007_);
lean_ctor_set(v_reuseFailAlloc_4031_, 1, v___x_4021_);
v___x_4023_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v_msgData_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4024_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__2);
v___x_4025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4025_, 0, v___x_4023_);
lean_ctor_set(v___x_4025_, 1, v___x_4024_);
v___x_4026_ = l_Lean_MessageData_ofSyntax(v_after_4017_);
v___x_4027_ = l_Lean_indentD(v___x_4026_);
v_msgData_4028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_4028_, 0, v___x_4025_);
lean_ctor_set(v_msgData_4028_, 1, v___x_4027_);
v___x_4029_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23(v_msgData_4028_, v_macroStack_4008_);
v___x_4030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4030_, 0, v___x_4029_);
return v___x_4030_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___boxed(lean_object* v_msgData_4034_, lean_object* v_macroStack_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg(v_msgData_4034_, v_macroStack_4035_, v___y_4036_);
lean_dec_ref(v___y_4036_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg(lean_object* v_msg_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_){
_start:
{
lean_object* v_ref_4047_; lean_object* v_macroStack_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v_a_4051_; lean_object* v___x_4052_; lean_object* v_a_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4061_; 
v_ref_4047_ = lean_ctor_get(v___y_4044_, 2);
v_macroStack_4048_ = lean_ctor_get(v___y_4040_, 1);
v___x_4049_ = l_Lean_Elab_getBetterRef(v_ref_4047_, v_macroStack_4048_);
v___x_4050_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__15(v_msg_4039_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_);
v_a_4051_ = lean_ctor_get(v___x_4050_, 0);
lean_inc(v_a_4051_);
lean_dec_ref(v___x_4050_);
lean_inc(v_macroStack_4048_);
v___x_4052_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg(v_a_4051_, v_macroStack_4048_, v___y_4044_);
v_a_4053_ = lean_ctor_get(v___x_4052_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_4052_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4055_ = v___x_4052_;
v_isShared_4056_ = v_isSharedCheck_4061_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_a_4053_);
lean_dec(v___x_4052_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4061_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4057_; lean_object* v___x_4059_; 
v___x_4057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4057_, 0, v___x_4049_);
lean_ctor_set(v___x_4057_, 1, v_a_4053_);
if (v_isShared_4056_ == 0)
{
lean_ctor_set_tag(v___x_4055_, 1);
lean_ctor_set(v___x_4055_, 0, v___x_4057_);
v___x_4059_ = v___x_4055_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v___x_4057_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg___boxed(lean_object* v_msg_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
lean_object* v_res_4070_; 
v_res_4070_ = l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg(v_msg_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_);
lean_dec(v___y_4068_);
lean_dec_ref(v___y_4067_);
lean_dec(v___y_4066_);
lean_dec_ref(v___y_4065_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
return v_res_4070_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__5(void){
_start:
{
lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4079_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__0));
v___x_4080_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__4));
v___x_4081_ = l_Lean_Expr_const___override(v___x_4080_, v___x_4079_);
return v___x_4081_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__8(void){
_start:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4086_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__0));
v___x_4087_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__7));
v___x_4088_ = l_Lean_Expr_const___override(v___x_4087_, v___x_4086_);
return v___x_4088_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__9(void){
_start:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; 
v___x_4089_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4);
v___x_4090_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__8, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__8_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__8);
v___x_4091_ = l_Lean_Expr_app___override(v___x_4090_, v___x_4089_);
return v___x_4091_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__14(void){
_start:
{
lean_object* v___x_4101_; lean_object* v___x_4102_; 
v___x_4101_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__13));
v___x_4102_ = l_String_toRawSubstring_x27(v___x_4101_);
return v___x_4102_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__29(void){
_start:
{
lean_object* v___x_4137_; 
v___x_4137_ = l_Array_mkArray0___redArg();
return v___x_4137_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__33(void){
_start:
{
lean_object* v___x_4141_; lean_object* v___x_4142_; 
v___x_4141_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__32));
v___x_4142_ = l_Lean_stringToMessageData(v___x_4141_);
return v___x_4142_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__35(void){
_start:
{
lean_object* v___x_4144_; lean_object* v___x_4145_; 
v___x_4144_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__34));
v___x_4145_ = l_Lean_stringToMessageData(v___x_4144_);
return v___x_4145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore(lean_object* v_e_4156_, lean_object* v_body_4157_, lean_object* v_ref_4158_, lean_object* v_expectedType_x3f_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_){
_start:
{
lean_object* v_toCold_4167_; lean_object* v_ref_4168_; lean_object* v_fileName_4169_; lean_object* v___x_4170_; 
v_toCold_4167_ = lean_ctor_get(v_a_4164_, 0);
v_ref_4168_ = lean_ctor_get(v_a_4164_, 2);
v_fileName_4169_ = lean_ctor_get(v_toCold_4167_, 0);
lean_inc_ref(v_fileName_4169_);
v___x_4170_ = lean_io_realpath(v_fileName_4169_);
if (lean_obj_tag(v___x_4170_) == 0)
{
lean_object* v_a_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; uint8_t v___x_4174_; lean_object* v___y_4176_; uint8_t v___y_4177_; size_t v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4275_; lean_object* v___y_4276_; uint8_t v___y_4277_; lean_object* v___y_4278_; size_t v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4343_; lean_object* v___y_4344_; uint8_t v___y_4345_; lean_object* v___y_4346_; size_t v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v___y_4356_; uint8_t v___y_4369_; lean_object* v___y_4370_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v___y_4373_; uint8_t v___y_4374_; lean_object* v___y_4375_; size_t v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4412_; lean_object* v___x_4475_; 
v_a_4171_ = lean_ctor_get(v___x_4170_, 0);
lean_inc(v_a_4171_);
lean_dec_ref_known(v___x_4170_, 1);
v___x_4172_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__0));
v___x_4173_ = lean_string_append(v_a_4171_, v___x_4172_);
v___x_4174_ = 0;
v___x_4475_ = l_Lean_Syntax_getPos_x3f(v_ref_4158_, v___x_4174_);
if (lean_obj_tag(v___x_4475_) == 0)
{
lean_object* v___x_4476_; 
v___x_4476_ = lean_unsigned_to_nat(0u);
v___y_4412_ = v___x_4476_;
goto v___jp_4411_;
}
else
{
lean_object* v_val_4477_; 
v_val_4477_ = lean_ctor_get(v___x_4475_, 0);
lean_inc(v_val_4477_);
lean_dec_ref_known(v___x_4475_, 1);
v___y_4412_ = v_val_4477_;
goto v___jp_4411_;
}
v___jp_4175_:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; uint8_t v___x_4190_; uint8_t v___x_4191_; lean_object* v___x_4192_; 
v___x_4187_ = lean_box(2);
v___x_4188_ = l_Lean_Syntax_mkStrLit(v___y_4180_, v___x_4187_);
v___x_4189_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__2));
v___x_4190_ = 0;
v___x_4191_ = 0;
v___x_4192_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg(v___x_4189_, v___x_4190_, v___y_4176_, v___y_4179_, v___x_4191_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
if (lean_obj_tag(v___x_4192_) == 0)
{
lean_object* v_a_4193_; lean_object* v___x_4194_; 
v_a_4193_ = lean_ctor_get(v___x_4192_, 0);
lean_inc(v_a_4193_);
lean_dec_ref_known(v___x_4192_, 1);
v___x_4194_ = l_Lean_Elab_Term_exprToSyntax(v_a_4193_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
if (lean_obj_tag(v___x_4194_) == 0)
{
lean_object* v_a_4195_; lean_object* v___x_4196_; lean_object* v_env_4197_; lean_object* v___x_4198_; lean_object* v_env_4199_; lean_object* v___x_4200_; lean_object* v_imports_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; size_t v_sz_4205_; lean_object* v___x_4206_; 
v_a_4195_ = lean_ctor_get(v___x_4194_, 0);
lean_inc(v_a_4195_);
lean_dec_ref_known(v___x_4194_, 1);
v___x_4196_ = lean_st_ref_get(v___y_4186_);
v_env_4197_ = lean_ctor_get(v___x_4196_, 0);
lean_inc_ref(v_env_4197_);
lean_dec(v___x_4196_);
v___x_4198_ = lean_st_ref_get(v___y_4186_);
v_env_4199_ = lean_ctor_get(v___x_4198_, 0);
lean_inc_ref(v_env_4199_);
lean_dec(v___x_4198_);
v___x_4200_ = l_Lean_Environment_header(v_env_4197_);
lean_dec_ref(v_env_4197_);
v_imports_4201_ = lean_ctor_get(v___x_4200_, 1);
lean_inc_ref(v_imports_4201_);
lean_dec_ref(v___x_4200_);
v___x_4202_ = l_Lean_Environment_mainModule(v_env_4199_);
lean_dec_ref(v_env_4199_);
v___x_4203_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_4203_, 0, v___x_4202_);
lean_ctor_set_uint8(v___x_4203_, sizeof(void*)*1, v___x_4174_);
lean_ctor_set_uint8(v___x_4203_, sizeof(void*)*1 + 1, v___y_4177_);
lean_ctor_set_uint8(v___x_4203_, sizeof(void*)*1 + 2, v___x_4174_);
v___x_4204_ = lean_array_push(v_imports_4201_, v___x_4203_);
v_sz_4205_ = lean_array_size(v___x_4204_);
v___x_4206_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg(v_sz_4205_, v___y_4178_, v___x_4204_);
if (lean_obj_tag(v___x_4206_) == 0)
{
lean_object* v_a_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
v_a_4207_ = lean_ctor_get(v___x_4206_, 0);
lean_inc(v_a_4207_);
lean_dec_ref_known(v___x_4206_, 1);
v___x_4208_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__5, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__5_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__5);
v___x_4209_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4);
v___x_4210_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__9, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__9_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__9);
v___x_4211_ = lean_array_to_list(v_a_4207_);
v___x_4212_ = l_List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7(v___x_4210_, v___x_4211_);
v___x_4213_ = l_Lean_mkAppB(v___x_4208_, v___x_4209_, v___x_4212_);
v___x_4214_ = l_Lean_Elab_Term_exprToSyntax(v___x_4213_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
if (lean_obj_tag(v___x_4214_) == 0)
{
lean_object* v_toCold_4215_; lean_object* v_a_4216_; lean_object* v_ref_4217_; lean_object* v_quotContext_4218_; lean_object* v_currMacroScope_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; 
v_toCold_4215_ = lean_ctor_get(v___y_4185_, 0);
v_a_4216_ = lean_ctor_get(v___x_4214_, 0);
lean_inc(v_a_4216_);
lean_dec_ref_known(v___x_4214_, 1);
v_ref_4217_ = lean_ctor_get(v___y_4185_, 2);
v_quotContext_4218_ = lean_ctor_get(v_toCold_4215_, 8);
v_currMacroScope_4219_ = lean_ctor_get(v_toCold_4215_, 9);
v___x_4220_ = l_Lean_SourceInfo_fromRef(v_ref_4217_, v___x_4174_);
v___x_4221_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__11));
v___x_4222_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__12));
v___x_4223_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__14, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__14_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__14);
v___x_4224_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__16));
lean_inc(v_currMacroScope_4219_);
lean_inc(v_quotContext_4218_);
v___x_4225_ = l_Lean_addMacroScope(v_quotContext_4218_, v___x_4224_, v_currMacroScope_4219_);
v___x_4226_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__18));
lean_inc_n(v___x_4220_, 12);
v___x_4227_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4227_, 0, v___x_4220_);
lean_ctor_set(v___x_4227_, 1, v___x_4223_);
lean_ctor_set(v___x_4227_, 2, v___x_4225_);
lean_ctor_set(v___x_4227_, 3, v___x_4226_);
v___x_4228_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__20));
v___x_4229_ = l_Lean_Syntax_node3(v___x_4220_, v___x_4228_, v___x_4188_, v_a_4216_, v_a_4195_);
v___x_4230_ = l_Lean_Syntax_node2(v___x_4220_, v___x_4222_, v___x_4227_, v___x_4229_);
v___x_4231_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__21));
v___x_4232_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4232_, 0, v___x_4220_);
lean_ctor_set(v___x_4232_, 1, v___x_4231_);
v___x_4233_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__22));
v___x_4234_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__23));
v___x_4235_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4235_, 0, v___x_4220_);
lean_ctor_set(v___x_4235_, 1, v___x_4233_);
v___x_4236_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__25));
v___x_4237_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__27));
v___x_4238_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__28));
v___x_4239_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4239_, 0, v___x_4220_);
lean_ctor_set(v___x_4239_, 1, v___x_4238_);
v___x_4240_ = l_Lean_Syntax_node1(v___x_4220_, v___x_4237_, v___x_4239_);
v___x_4241_ = l_Lean_Syntax_node1(v___x_4220_, v___x_4228_, v___x_4240_);
v___x_4242_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__29, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__29_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__29);
v___x_4243_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4220_);
lean_ctor_set(v___x_4243_, 1, v___x_4228_);
lean_ctor_set(v___x_4243_, 2, v___x_4242_);
v___x_4244_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__30));
v___x_4245_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4245_, 0, v___x_4220_);
lean_ctor_set(v___x_4245_, 1, v___x_4244_);
v___x_4246_ = l_Lean_Syntax_node4(v___x_4220_, v___x_4236_, v___x_4241_, v___x_4243_, v___x_4245_, v_body_4157_);
v___x_4247_ = l_Lean_Syntax_node2(v___x_4220_, v___x_4234_, v___x_4235_, v___x_4246_);
v___x_4248_ = l_Lean_Syntax_node3(v___x_4220_, v___x_4221_, v___x_4230_, v___x_4232_, v___x_4247_);
v___x_4249_ = l_Lean_Elab_Term_elabTerm(v___x_4248_, v_expectedType_x3f_4159_, v___y_4177_, v___y_4177_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
return v___x_4249_;
}
else
{
lean_object* v_a_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4257_; 
lean_dec(v_a_4195_);
lean_dec(v___x_4188_);
lean_dec(v_expectedType_x3f_4159_);
lean_dec(v_body_4157_);
v_a_4250_ = lean_ctor_get(v___x_4214_, 0);
v_isSharedCheck_4257_ = !lean_is_exclusive(v___x_4214_);
if (v_isSharedCheck_4257_ == 0)
{
v___x_4252_ = v___x_4214_;
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_a_4250_);
lean_dec(v___x_4214_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
lean_object* v___x_4255_; 
if (v_isShared_4253_ == 0)
{
v___x_4255_ = v___x_4252_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4256_; 
v_reuseFailAlloc_4256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4256_, 0, v_a_4250_);
v___x_4255_ = v_reuseFailAlloc_4256_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
return v___x_4255_;
}
}
}
}
else
{
lean_object* v_a_4258_; lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4265_; 
lean_dec(v_a_4195_);
lean_dec(v___x_4188_);
lean_dec(v_expectedType_x3f_4159_);
lean_dec(v_body_4157_);
v_a_4258_ = lean_ctor_get(v___x_4206_, 0);
v_isSharedCheck_4265_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4265_ == 0)
{
v___x_4260_ = v___x_4206_;
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
else
{
lean_inc(v_a_4258_);
lean_dec(v___x_4206_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v___x_4263_; 
if (v_isShared_4261_ == 0)
{
v___x_4263_ = v___x_4260_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v_a_4258_);
v___x_4263_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
return v___x_4263_;
}
}
}
}
else
{
lean_object* v_a_4266_; lean_object* v___x_4268_; uint8_t v_isShared_4269_; uint8_t v_isSharedCheck_4273_; 
lean_dec(v___x_4188_);
lean_dec(v_expectedType_x3f_4159_);
lean_dec(v_body_4157_);
v_a_4266_ = lean_ctor_get(v___x_4194_, 0);
v_isSharedCheck_4273_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4273_ == 0)
{
v___x_4268_ = v___x_4194_;
v_isShared_4269_ = v_isSharedCheck_4273_;
goto v_resetjp_4267_;
}
else
{
lean_inc(v_a_4266_);
lean_dec(v___x_4194_);
v___x_4268_ = lean_box(0);
v_isShared_4269_ = v_isSharedCheck_4273_;
goto v_resetjp_4267_;
}
v_resetjp_4267_:
{
lean_object* v___x_4271_; 
if (v_isShared_4269_ == 0)
{
v___x_4271_ = v___x_4268_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v_a_4266_);
v___x_4271_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
return v___x_4271_;
}
}
}
}
else
{
lean_dec(v___x_4188_);
lean_dec(v_expectedType_x3f_4159_);
lean_dec(v_body_4157_);
return v___x_4192_;
}
}
v___jp_4274_:
{
lean_object* v___x_4289_; lean_object* v___x_4290_; uint8_t v___x_4291_; 
v___x_4289_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4287_);
v___x_4290_ = l_Lean_Elab_inServer;
v___x_4291_ = l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8(v___x_4289_, v___x_4290_);
lean_dec_ref(v___x_4289_);
if (v___x_4291_ == 0)
{
lean_dec_ref(v___y_4281_);
lean_dec(v___y_4278_);
lean_dec_ref(v___y_4275_);
lean_dec(v_ref_4158_);
v___y_4176_ = v___y_4276_;
v___y_4177_ = v___y_4277_;
v___y_4178_ = v___y_4279_;
v___y_4179_ = v___y_4280_;
v___y_4180_ = v___y_4282_;
v___y_4181_ = v___y_4283_;
v___y_4182_ = v___y_4284_;
v___y_4183_ = v___y_4285_;
v___y_4184_ = v___y_4286_;
v___y_4185_ = v___y_4287_;
v___y_4186_ = v___y_4288_;
goto v___jp_4175_;
}
else
{
uint8_t v___x_4292_; 
v___x_4292_ = l_Lean_Expr_hasSorry(v___y_4281_);
if (v___x_4292_ == 0)
{
lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___f_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
v___x_4293_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__8));
lean_inc_ref(v___y_4276_);
v___x_4294_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson(v___y_4276_);
v___x_4295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4295_, 0, v___x_4293_);
lean_ctor_set(v___x_4295_, 1, v___x_4294_);
v___x_4296_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__13));
v___x_4297_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson(v___y_4281_);
v___x_4298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4298_, 0, v___x_4296_);
lean_ctor_set(v___x_4298_, 1, v___x_4297_);
v___x_4299_ = lean_box(0);
v___x_4300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4300_, 0, v___x_4298_);
lean_ctor_set(v___x_4300_, 1, v___x_4299_);
v___x_4301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4301_, 0, v___x_4295_);
lean_ctor_set(v___x_4301_, 1, v___x_4300_);
v___x_4302_ = l_Lean_Json_mkObj(v___x_4301_);
lean_dec_ref_known(v___x_4301_, 2);
lean_inc(v_ref_4158_);
v___f_4303_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4303_, 0, v___y_4275_);
lean_closure_set(v___f_4303_, 1, v___x_4302_);
lean_closure_set(v___f_4303_, 2, v_ref_4158_);
v___x_4304_ = l_IO_CancelToken_new();
v___x_4305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4305_, 0, v___x_4304_);
v___x_4306_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0));
v___x_4307_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__8));
v___x_4308_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__11));
lean_inc(v___y_4278_);
v___x_4309_ = l_Lean_Name_num___override(v___x_4308_, v___y_4278_);
v___x_4310_ = l_Lean_Name_str___override(v___x_4309_, v___x_4306_);
v___x_4311_ = l_Lean_Name_str___override(v___x_4310_, v___x_4307_);
v___x_4312_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__15));
v___x_4313_ = l_Lean_Name_str___override(v___x_4311_, v___x_4312_);
v___x_4314_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__31));
v___x_4315_ = l_Lean_Name_str___override(v___x_4313_, v___x_4314_);
v___x_4316_ = l_Lean_Name_toString(v___x_4315_, v___y_4277_);
lean_inc_ref(v___x_4305_);
v___x_4317_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___f_4303_, v___x_4305_, v___x_4316_, v___y_4287_, v___y_4288_);
if (lean_obj_tag(v___x_4317_) == 0)
{
lean_object* v_a_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; 
v_a_4318_ = lean_ctor_get(v___x_4317_, 0);
lean_inc(v_a_4318_);
lean_dec_ref_known(v___x_4317_, 1);
v___x_4319_ = lean_box(0);
v___x_4320_ = lean_apply_1(v_a_4318_, v___x_4319_);
v___x_4321_ = lean_io_as_task(v___x_4320_, v___y_4278_);
v___x_4322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4322_, 0, v_ref_4158_);
v___x_4323_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_4322_);
v___x_4324_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4324_, 0, v___x_4322_);
lean_ctor_set(v___x_4324_, 1, v___x_4323_);
lean_ctor_set(v___x_4324_, 2, v___x_4305_);
lean_ctor_set(v___x_4324_, 3, v___x_4321_);
v___x_4325_ = l_Lean_Core_logSnapshotTask___redArg(v___x_4324_, v___y_4288_);
if (lean_obj_tag(v___x_4325_) == 0)
{
lean_dec_ref_known(v___x_4325_, 1);
v___y_4176_ = v___y_4276_;
v___y_4177_ = v___y_4277_;
v___y_4178_ = v___y_4279_;
v___y_4179_ = v___y_4280_;
v___y_4180_ = v___y_4282_;
v___y_4181_ = v___y_4283_;
v___y_4182_ = v___y_4284_;
v___y_4183_ = v___y_4285_;
v___y_4184_ = v___y_4286_;
v___y_4185_ = v___y_4287_;
v___y_4186_ = v___y_4288_;
goto v___jp_4175_;
}
else
{
lean_object* v_a_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4333_; 
lean_dec_ref(v___y_4282_);
lean_dec_ref(v___y_4280_);
lean_dec_ref(v___y_4276_);
lean_dec(v_expectedType_x3f_4159_);
lean_dec(v_body_4157_);
v_a_4326_ = lean_ctor_get(v___x_4325_, 0);
v_isSharedCheck_4333_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4333_ == 0)
{
v___x_4328_ = v___x_4325_;
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_a_4326_);
lean_dec(v___x_4325_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v___x_4331_; 
if (v_isShared_4329_ == 0)
{
v___x_4331_ = v___x_4328_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v_a_4326_);
v___x_4331_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
return v___x_4331_;
}
}
}
}
else
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4341_; 
lean_dec_ref_known(v___x_4305_, 1);
lean_dec_ref(v___y_4282_);
lean_dec_ref(v___y_4280_);
lean_dec(v___y_4278_);
lean_dec_ref(v___y_4276_);
lean_dec(v_expectedType_x3f_4159_);
lean_dec(v_ref_4158_);
lean_dec(v_body_4157_);
v_a_4334_ = lean_ctor_get(v___x_4317_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4317_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4336_ = v___x_4317_;
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_a_4334_);
lean_dec(v___x_4317_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v___x_4339_; 
if (v_isShared_4337_ == 0)
{
v___x_4339_ = v___x_4336_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_a_4334_);
v___x_4339_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
return v___x_4339_;
}
}
}
}
else
{
lean_dec_ref(v___y_4281_);
lean_dec(v___y_4278_);
lean_dec_ref(v___y_4275_);
lean_dec(v_ref_4158_);
v___y_4176_ = v___y_4276_;
v___y_4177_ = v___y_4277_;
v___y_4178_ = v___y_4279_;
v___y_4179_ = v___y_4280_;
v___y_4180_ = v___y_4282_;
v___y_4181_ = v___y_4283_;
v___y_4182_ = v___y_4284_;
v___y_4183_ = v___y_4285_;
v___y_4184_ = v___y_4286_;
v___y_4185_ = v___y_4287_;
v___y_4186_ = v___y_4288_;
goto v___jp_4175_;
}
}
}
v___jp_4342_:
{
uint8_t v___x_4357_; 
v___x_4357_ = l_Lean_Expr_hasMVar(v___y_4344_);
if (v___x_4357_ == 0)
{
v___y_4275_ = v___y_4343_;
v___y_4276_ = v___y_4344_;
v___y_4277_ = v___y_4345_;
v___y_4278_ = v___y_4346_;
v___y_4279_ = v___y_4347_;
v___y_4280_ = v___y_4348_;
v___y_4281_ = v___y_4349_;
v___y_4282_ = v___y_4350_;
v___y_4283_ = v___y_4351_;
v___y_4284_ = v___y_4352_;
v___y_4285_ = v___y_4353_;
v___y_4286_ = v___y_4354_;
v___y_4287_ = v___y_4355_;
v___y_4288_ = v___y_4356_;
goto v___jp_4274_;
}
else
{
lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v_a_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4367_; 
lean_dec_ref(v___y_4350_);
lean_dec_ref(v___y_4349_);
lean_dec_ref(v___y_4348_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4344_);
lean_dec_ref(v___y_4343_);
lean_dec(v_expectedType_x3f_4159_);
lean_dec(v_ref_4158_);
lean_dec(v_body_4157_);
v___x_4358_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__33, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__33_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__33);
v___x_4359_ = l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg(v___x_4358_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_);
v_a_4360_ = lean_ctor_get(v___x_4359_, 0);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4359_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4362_ = v___x_4359_;
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_a_4360_);
lean_dec(v___x_4359_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v___x_4365_; 
if (v_isShared_4363_ == 0)
{
v___x_4365_ = v___x_4362_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_a_4360_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
return v___x_4365_;
}
}
}
}
v___jp_4368_:
{
uint8_t v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___f_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___f_4387_; lean_object* v___x_4388_; 
v___x_4379_ = 1;
v___x_4380_ = lean_box(v___x_4174_);
v___x_4381_ = lean_box(v___y_4369_);
v___x_4382_ = lean_box(v___x_4379_);
lean_inc_ref(v___y_4371_);
v___f_4383_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__1___boxed), 13, 5);
lean_closure_set(v___f_4383_, 0, v___y_4371_);
lean_closure_set(v___f_4383_, 1, v___y_4373_);
lean_closure_set(v___f_4383_, 2, v___x_4380_);
lean_closure_set(v___f_4383_, 3, v___x_4381_);
lean_closure_set(v___f_4383_, 4, v___x_4382_);
v___x_4384_ = lean_box(v___x_4174_);
v___x_4385_ = lean_box(v___y_4369_);
v___x_4386_ = lean_box(v___x_4379_);
v___f_4387_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__2___boxed), 12, 5);
lean_closure_set(v___f_4387_, 0, v___y_4371_);
lean_closure_set(v___f_4387_, 1, v___y_4370_);
lean_closure_set(v___f_4387_, 2, v___x_4384_);
lean_closure_set(v___f_4387_, 3, v___x_4385_);
lean_closure_set(v___f_4387_, 4, v___x_4386_);
v___x_4388_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___redArg(v___y_4378_, v___f_4387_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_);
if (lean_obj_tag(v___x_4388_) == 0)
{
lean_object* v_a_4389_; lean_object* v_fst_4390_; lean_object* v_snd_4391_; uint8_t v___x_4392_; 
v_a_4389_ = lean_ctor_get(v___x_4388_, 0);
lean_inc(v_a_4389_);
lean_dec_ref_known(v___x_4388_, 1);
v_fst_4390_ = lean_ctor_get(v_a_4389_, 0);
lean_inc(v_fst_4390_);
v_snd_4391_ = lean_ctor_get(v_a_4389_, 1);
lean_inc(v_snd_4391_);
lean_dec(v_a_4389_);
v___x_4392_ = l_Lean_Expr_hasMVar(v_fst_4390_);
if (v___x_4392_ == 0)
{
v___y_4343_ = v___y_4372_;
v___y_4344_ = v_snd_4391_;
v___y_4345_ = v___y_4374_;
v___y_4346_ = v___y_4375_;
v___y_4347_ = v___y_4376_;
v___y_4348_ = v___f_4383_;
v___y_4349_ = v_fst_4390_;
v___y_4350_ = v___y_4377_;
v___y_4351_ = v_a_4160_;
v___y_4352_ = v_a_4161_;
v___y_4353_ = v_a_4162_;
v___y_4354_ = v_a_4163_;
v___y_4355_ = v_a_4164_;
v___y_4356_ = v_a_4165_;
goto v___jp_4342_;
}
else
{
lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v_a_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4402_; 
lean_dec(v_snd_4391_);
lean_dec(v_fst_4390_);
lean_dec_ref(v___f_4383_);
lean_dec_ref(v___y_4377_);
lean_dec(v___y_4375_);
lean_dec_ref(v___y_4372_);
lean_dec(v_expectedType_x3f_4159_);
lean_dec(v_ref_4158_);
lean_dec(v_body_4157_);
v___x_4393_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__35, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__35_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__35);
v___x_4394_ = l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg(v___x_4393_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_);
v_a_4395_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4402_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4402_ == 0)
{
v___x_4397_ = v___x_4394_;
v_isShared_4398_ = v_isSharedCheck_4402_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_a_4395_);
lean_dec(v___x_4394_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4402_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
lean_object* v___x_4400_; 
if (v_isShared_4398_ == 0)
{
v___x_4400_ = v___x_4397_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v_a_4395_);
v___x_4400_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
return v___x_4400_;
}
}
}
}
else
{
lean_object* v_a_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4410_; 
lean_dec_ref(v___f_4383_);
lean_dec_ref(v___y_4377_);
lean_dec(v___y_4375_);
lean_dec_ref(v___y_4372_);
lean_dec(v_expectedType_x3f_4159_);
lean_dec(v_ref_4158_);
lean_dec(v_body_4157_);
v_a_4403_ = lean_ctor_get(v___x_4388_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4388_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4405_ = v___x_4388_;
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_a_4403_);
lean_dec(v___x_4388_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4408_; 
if (v_isShared_4406_ == 0)
{
v___x_4408_ = v___x_4405_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_a_4403_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
}
v___jp_4411_:
{
lean_object* v_lctx_4413_; lean_object* v_decls_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; uint64_t v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; 
v_lctx_4413_ = lean_ctor_get(v_a_4162_, 2);
v_decls_4414_ = lean_ctor_get(v_lctx_4413_, 1);
v___x_4415_ = l_Nat_reprFast(v___y_4412_);
v___x_4416_ = lean_string_append(v___x_4173_, v___x_4415_);
lean_dec_ref(v___x_4415_);
v___x_4417_ = lean_string_hash(v___x_4416_);
lean_dec_ref(v___x_4416_);
v___x_4418_ = lean_uint64_to_nat(v___x_4417_);
v___x_4419_ = l_Nat_reprFast(v___x_4418_);
v___x_4420_ = lean_unsigned_to_nat(0u);
v___x_4421_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__36));
v___x_4422_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0(v_decls_4414_, v___x_4421_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_);
if (lean_obj_tag(v___x_4422_) == 0)
{
lean_object* v_a_4423_; size_t v_sz_4424_; size_t v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; uint8_t v___x_4428_; lean_object* v___x_4429_; 
v_a_4423_ = lean_ctor_get(v___x_4422_, 0);
lean_inc_n(v_a_4423_, 2);
lean_dec_ref_known(v___x_4422_, 1);
v_sz_4424_ = lean_array_size(v_a_4423_);
v___x_4425_ = ((size_t)0ULL);
v___x_4426_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__1(v_sz_4424_, v___x_4425_, v_a_4423_);
v___x_4427_ = lean_box(0);
v___x_4428_ = 1;
v___x_4429_ = l_Lean_Elab_Term_elabTerm(v_e_4156_, v___x_4427_, v___x_4428_, v___x_4428_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_);
if (lean_obj_tag(v___x_4429_) == 0)
{
lean_object* v_a_4430_; lean_object* v___x_4431_; 
v_a_4430_ = lean_ctor_get(v___x_4429_, 0);
lean_inc(v_a_4430_);
lean_dec_ref_known(v___x_4429_, 1);
v___x_4431_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_4174_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_);
if (lean_obj_tag(v___x_4431_) == 0)
{
lean_object* v___x_4432_; lean_object* v_a_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; 
lean_dec_ref_known(v___x_4431_, 1);
v___x_4432_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(v_a_4430_, v_a_4163_);
v_a_4433_ = lean_ctor_get(v___x_4432_, 0);
lean_inc(v_a_4433_);
lean_dec_ref(v___x_4432_);
v___x_4434_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__38));
v___x_4435_ = lean_unsigned_to_nat(1u);
v___x_4436_ = lean_mk_empty_array_with_capacity(v___x_4435_);
lean_inc_ref(v___x_4436_);
v___x_4437_ = lean_array_push(v___x_4436_, v_a_4433_);
v___x_4438_ = l_Lean_Meta_mkAppM(v___x_4434_, v___x_4437_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_);
if (lean_obj_tag(v___x_4438_) == 0)
{
lean_object* v_a_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; 
v_a_4439_ = lean_ctor_get(v___x_4438_, 0);
lean_inc(v_a_4439_);
lean_dec_ref_known(v___x_4438_, 1);
v___x_4440_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__41));
lean_inc_ref(v___x_4436_);
v___x_4441_ = lean_array_push(v___x_4436_, v_a_4439_);
v___x_4442_ = l_Lean_Meta_mkAppM(v___x_4440_, v___x_4441_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_);
if (lean_obj_tag(v___x_4442_) == 0)
{
lean_object* v_a_4443_; lean_object* v___x_4444_; 
v_a_4443_ = lean_ctor_get(v___x_4442_, 0);
lean_inc(v_a_4443_);
lean_dec_ref_known(v___x_4442_, 1);
v___x_4444_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_4174_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_);
if (lean_obj_tag(v___x_4444_) == 0)
{
lean_object* v___x_4445_; lean_object* v_a_4446_; lean_object* v___x_4447_; uint8_t v___x_4448_; 
lean_dec_ref_known(v___x_4444_, 1);
v___x_4445_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(v_a_4443_, v_a_4163_);
v_a_4446_ = lean_ctor_get(v___x_4445_, 0);
lean_inc(v_a_4446_);
lean_dec_ref(v___x_4445_);
v___x_4447_ = lean_array_get_size(v_a_4423_);
v___x_4448_ = lean_nat_dec_lt(v___x_4420_, v___x_4447_);
if (v___x_4448_ == 0)
{
lean_dec(v_a_4423_);
lean_inc_ref(v_lctx_4413_);
lean_inc_ref(v___x_4419_);
v___y_4369_ = v___x_4428_;
v___y_4370_ = v_a_4446_;
v___y_4371_ = v___x_4426_;
v___y_4372_ = v___x_4419_;
v___y_4373_ = v___x_4436_;
v___y_4374_ = v___x_4428_;
v___y_4375_ = v___x_4420_;
v___y_4376_ = v___x_4425_;
v___y_4377_ = v___x_4419_;
v___y_4378_ = v_lctx_4413_;
goto v___jp_4368_;
}
else
{
size_t v___x_4449_; lean_object* v___x_4450_; 
v___x_4449_ = lean_usize_of_nat(v___x_4447_);
lean_inc_ref(v_lctx_4413_);
v___x_4450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__11(v_a_4423_, v___x_4425_, v___x_4449_, v_lctx_4413_);
lean_dec(v_a_4423_);
lean_inc_ref(v___x_4419_);
v___y_4369_ = v___x_4428_;
v___y_4370_ = v_a_4446_;
v___y_4371_ = v___x_4426_;
v___y_4372_ = v___x_4419_;
v___y_4373_ = v___x_4436_;
v___y_4374_ = v___x_4428_;
v___y_4375_ = v___x_4420_;
v___y_4376_ = v___x_4425_;
v___y_4377_ = v___x_4419_;
v___y_4378_ = v___x_4450_;
goto v___jp_4368_;
}
}
else
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4458_; 
lean_dec(v_a_4443_);
lean_dec_ref(v___x_4436_);
lean_dec_ref(v___x_4426_);
lean_dec(v_a_4423_);
lean_dec_ref(v___x_4419_);
lean_dec(v_expectedType_x3f_4159_);
lean_dec(v_ref_4158_);
lean_dec(v_body_4157_);
v_a_4451_ = lean_ctor_get(v___x_4444_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4453_ = v___x_4444_;
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4444_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4456_; 
if (v_isShared_4454_ == 0)
{
v___x_4456_ = v___x_4453_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
}
else
{
lean_dec_ref(v___x_4436_);
lean_dec_ref(v___x_4426_);
lean_dec(v_a_4423_);
lean_dec_ref(v___x_4419_);
lean_dec(v_expectedType_x3f_4159_);
lean_dec(v_ref_4158_);
lean_dec(v_body_4157_);
return v___x_4442_;
}
}
else
{
lean_dec_ref(v___x_4436_);
lean_dec_ref(v___x_4426_);
lean_dec(v_a_4423_);
lean_dec_ref(v___x_4419_);
lean_dec(v_expectedType_x3f_4159_);
lean_dec(v_ref_4158_);
lean_dec(v_body_4157_);
return v___x_4438_;
}
}
else
{
lean_object* v_a_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4466_; 
lean_dec(v_a_4430_);
lean_dec_ref(v___x_4426_);
lean_dec(v_a_4423_);
lean_dec_ref(v___x_4419_);
lean_dec(v_expectedType_x3f_4159_);
lean_dec(v_ref_4158_);
lean_dec(v_body_4157_);
v_a_4459_ = lean_ctor_get(v___x_4431_, 0);
v_isSharedCheck_4466_ = !lean_is_exclusive(v___x_4431_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4461_ = v___x_4431_;
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_a_4459_);
lean_dec(v___x_4431_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v___x_4464_; 
if (v_isShared_4462_ == 0)
{
v___x_4464_ = v___x_4461_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_a_4459_);
v___x_4464_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
return v___x_4464_;
}
}
}
}
else
{
lean_dec_ref(v___x_4426_);
lean_dec(v_a_4423_);
lean_dec_ref(v___x_4419_);
lean_dec(v_expectedType_x3f_4159_);
lean_dec(v_ref_4158_);
lean_dec(v_body_4157_);
return v___x_4429_;
}
}
else
{
lean_object* v_a_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4474_; 
lean_dec_ref(v___x_4419_);
lean_dec(v_expectedType_x3f_4159_);
lean_dec(v_ref_4158_);
lean_dec(v_body_4157_);
lean_dec(v_e_4156_);
v_a_4467_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4474_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4474_ == 0)
{
v___x_4469_ = v___x_4422_;
v_isShared_4470_ = v_isSharedCheck_4474_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_a_4467_);
lean_dec(v___x_4422_);
v___x_4469_ = lean_box(0);
v_isShared_4470_ = v_isSharedCheck_4474_;
goto v_resetjp_4468_;
}
v_resetjp_4468_:
{
lean_object* v___x_4472_; 
if (v_isShared_4470_ == 0)
{
v___x_4472_ = v___x_4469_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4473_; 
v_reuseFailAlloc_4473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4473_, 0, v_a_4467_);
v___x_4472_ = v_reuseFailAlloc_4473_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
return v___x_4472_;
}
}
}
}
}
else
{
lean_object* v_a_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4489_; 
lean_dec(v_expectedType_x3f_4159_);
lean_dec(v_ref_4158_);
lean_dec(v_body_4157_);
lean_dec(v_e_4156_);
v_a_4478_ = lean_ctor_get(v___x_4170_, 0);
v_isSharedCheck_4489_ = !lean_is_exclusive(v___x_4170_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4480_ = v___x_4170_;
v_isShared_4481_ = v_isSharedCheck_4489_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_a_4478_);
lean_dec(v___x_4170_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4489_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4487_; 
v___x_4482_ = lean_io_error_to_string(v_a_4478_);
v___x_4483_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4483_, 0, v___x_4482_);
v___x_4484_ = l_Lean_MessageData_ofFormat(v___x_4483_);
lean_inc(v_ref_4168_);
v___x_4485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4485_, 0, v_ref_4168_);
lean_ctor_set(v___x_4485_, 1, v___x_4484_);
if (v_isShared_4481_ == 0)
{
lean_ctor_set(v___x_4480_, 0, v___x_4485_);
v___x_4487_ = v___x_4480_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v___x_4485_);
v___x_4487_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
return v___x_4487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___boxed(lean_object* v_e_4490_, lean_object* v_body_4491_, lean_object* v_ref_4492_, lean_object* v_expectedType_x3f_4493_, lean_object* v_a_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_){
_start:
{
lean_object* v_res_4501_; 
v_res_4501_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore(v_e_4490_, v_body_4491_, v_ref_4492_, v_expectedType_x3f_4493_, v_a_4494_, v_a_4495_, v_a_4496_, v_a_4497_, v_a_4498_, v_a_4499_);
lean_dec(v_a_4499_);
lean_dec_ref(v_a_4498_);
lean_dec(v_a_4497_);
lean_dec_ref(v_a_4496_);
lean_dec(v_a_4495_);
lean_dec_ref(v_a_4494_);
return v_res_4501_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2(lean_object* v_00_u03b2_4502_, lean_object* v_x_4503_, lean_object* v_x_4504_, lean_object* v_x_4505_){
_start:
{
lean_object* v___x_4506_; 
v___x_4506_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2___redArg(v_x_4503_, v_x_4504_, v_x_4505_);
return v___x_4506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6(size_t v_sz_4507_, size_t v_i_4508_, lean_object* v_bs_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_){
_start:
{
lean_object* v___x_4517_; 
v___x_4517_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg(v_sz_4507_, v_i_4508_, v_bs_4509_);
return v___x_4517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___boxed(lean_object* v_sz_4518_, lean_object* v_i_4519_, lean_object* v_bs_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_){
_start:
{
size_t v_sz_boxed_4528_; size_t v_i_boxed_4529_; lean_object* v_res_4530_; 
v_sz_boxed_4528_ = lean_unbox_usize(v_sz_4518_);
lean_dec(v_sz_4518_);
v_i_boxed_4529_ = lean_unbox_usize(v_i_4519_);
lean_dec(v_i_4519_);
v_res_4530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6(v_sz_boxed_4528_, v_i_boxed_4529_, v_bs_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
lean_dec(v___y_4524_);
lean_dec_ref(v___y_4523_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
return v_res_4530_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10(lean_object* v_00_u03b1_4531_, lean_object* v_msg_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
lean_object* v___x_4540_; 
v___x_4540_ = l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg(v_msg_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
return v___x_4540_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___boxed(lean_object* v_00_u03b1_4541_, lean_object* v_msg_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10(v_00_u03b1_4541_, v_msg_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_);
lean_dec(v___y_4548_);
lean_dec_ref(v___y_4547_);
lean_dec(v___y_4546_);
lean_dec_ref(v___y_4545_);
lean_dec(v___y_4544_);
lean_dec_ref(v___y_4543_);
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4(lean_object* v_00_u03b2_4551_, lean_object* v_x_4552_, size_t v_x_4553_, size_t v_x_4554_, lean_object* v_x_4555_, lean_object* v_x_4556_){
_start:
{
lean_object* v___x_4557_; 
v___x_4557_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg(v_x_4552_, v_x_4553_, v_x_4554_, v_x_4555_, v_x_4556_);
return v___x_4557_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4558_, lean_object* v_x_4559_, lean_object* v_x_4560_, lean_object* v_x_4561_, lean_object* v_x_4562_, lean_object* v_x_4563_){
_start:
{
size_t v_x_36810__boxed_4564_; size_t v_x_36811__boxed_4565_; lean_object* v_res_4566_; 
v_x_36810__boxed_4564_ = lean_unbox_usize(v_x_4560_);
lean_dec(v_x_4560_);
v_x_36811__boxed_4565_ = lean_unbox_usize(v_x_4561_);
lean_dec(v_x_4561_);
v_res_4566_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4(v_00_u03b2_4558_, v_x_4559_, v_x_36810__boxed_4564_, v_x_36811__boxed_4565_, v_x_4562_, v_x_4563_);
return v_res_4566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16(lean_object* v_msgData_4567_, lean_object* v_macroStack_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_){
_start:
{
lean_object* v___x_4576_; 
v___x_4576_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg(v_msgData_4567_, v_macroStack_4568_, v___y_4573_);
return v___x_4576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___boxed(lean_object* v_msgData_4577_, lean_object* v_macroStack_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_){
_start:
{
lean_object* v_res_4586_; 
v_res_4586_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16(v_msgData_4577_, v_macroStack_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_);
lean_dec(v___y_4584_);
lean_dec_ref(v___y_4583_);
lean_dec(v___y_4582_);
lean_dec_ref(v___y_4581_);
lean_dec(v___y_4580_);
lean_dec_ref(v___y_4579_);
return v_res_4586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8(lean_object* v_as_4587_, size_t v_sz_4588_, size_t v_i_4589_, lean_object* v_b_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_){
_start:
{
lean_object* v___x_4598_; 
v___x_4598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___redArg(v_as_4587_, v_sz_4588_, v_i_4589_, v_b_4590_);
return v___x_4598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___boxed(lean_object* v_as_4599_, lean_object* v_sz_4600_, lean_object* v_i_4601_, lean_object* v_b_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_){
_start:
{
size_t v_sz_boxed_4610_; size_t v_i_boxed_4611_; lean_object* v_res_4612_; 
v_sz_boxed_4610_ = lean_unbox_usize(v_sz_4600_);
lean_dec(v_sz_4600_);
v_i_boxed_4611_ = lean_unbox_usize(v_i_4601_);
lean_dec(v_i_4601_);
v_res_4612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8(v_as_4599_, v_sz_boxed_4610_, v_i_boxed_4611_, v_b_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_);
lean_dec(v___y_4608_);
lean_dec_ref(v___y_4607_);
lean_dec(v___y_4606_);
lean_dec_ref(v___y_4605_);
lean_dec(v___y_4604_);
lean_dec_ref(v___y_4603_);
lean_dec_ref(v_as_4599_);
return v_res_4612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12(lean_object* v_00_u03b2_4613_, lean_object* v_n_4614_, lean_object* v_k_4615_, lean_object* v_v_4616_){
_start:
{
lean_object* v___x_4617_; 
v___x_4617_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12___redArg(v_n_4614_, v_k_4615_, v_v_4616_);
return v___x_4617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13(lean_object* v_00_u03b2_4618_, size_t v_depth_4619_, lean_object* v_keys_4620_, lean_object* v_vals_4621_, lean_object* v_heq_4622_, lean_object* v_i_4623_, lean_object* v_entries_4624_){
_start:
{
lean_object* v___x_4625_; 
v___x_4625_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___redArg(v_depth_4619_, v_keys_4620_, v_vals_4621_, v_i_4623_, v_entries_4624_);
return v___x_4625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___boxed(lean_object* v_00_u03b2_4626_, lean_object* v_depth_4627_, lean_object* v_keys_4628_, lean_object* v_vals_4629_, lean_object* v_heq_4630_, lean_object* v_i_4631_, lean_object* v_entries_4632_){
_start:
{
size_t v_depth_boxed_4633_; lean_object* v_res_4634_; 
v_depth_boxed_4633_ = lean_unbox_usize(v_depth_4627_);
lean_dec(v_depth_4627_);
v_res_4634_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13(v_00_u03b2_4626_, v_depth_boxed_4633_, v_keys_4628_, v_vals_4629_, v_heq_4630_, v_i_4631_, v_entries_4632_);
lean_dec_ref(v_vals_4629_);
lean_dec_ref(v_keys_4628_);
return v_res_4634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15(lean_object* v_as_4635_, size_t v_sz_4636_, size_t v_i_4637_, lean_object* v_b_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_){
_start:
{
lean_object* v___x_4646_; 
v___x_4646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___redArg(v_as_4635_, v_sz_4636_, v_i_4637_, v_b_4638_);
return v___x_4646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___boxed(lean_object* v_as_4647_, lean_object* v_sz_4648_, lean_object* v_i_4649_, lean_object* v_b_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_){
_start:
{
size_t v_sz_boxed_4658_; size_t v_i_boxed_4659_; lean_object* v_res_4660_; 
v_sz_boxed_4658_ = lean_unbox_usize(v_sz_4648_);
lean_dec(v_sz_4648_);
v_i_boxed_4659_ = lean_unbox_usize(v_i_4649_);
lean_dec(v_i_4649_);
v_res_4660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15(v_as_4647_, v_sz_boxed_4658_, v_i_boxed_4659_, v_b_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_);
lean_dec(v___y_4656_);
lean_dec_ref(v___y_4655_);
lean_dec(v___y_4654_);
lean_dec_ref(v___y_4653_);
lean_dec(v___y_4652_);
lean_dec_ref(v___y_4651_);
lean_dec_ref(v_as_4647_);
return v_res_4660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12_spec__20(lean_object* v_00_u03b2_4661_, lean_object* v_x_4662_, lean_object* v_x_4663_, lean_object* v_x_4664_, lean_object* v_x_4665_){
_start:
{
lean_object* v___x_4666_; 
v___x_4666_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12_spec__20___redArg(v_x_4662_, v_x_4663_, v_x_4664_, v_x_4665_);
return v___x_4666_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; 
v___x_4667_ = lean_box(0);
v___x_4668_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_4669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4669_, 0, v___x_4668_);
lean_ctor_set(v___x_4669_, 1, v___x_4667_);
return v___x_4669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg(){
_start:
{
lean_object* v___x_4671_; lean_object* v___x_4672_; 
v___x_4671_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0);
v___x_4672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4672_, 0, v___x_4671_);
return v___x_4672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___boxed(lean_object* v___y_4673_){
_start:
{
lean_object* v_res_4674_; 
v_res_4674_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg();
return v_res_4674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0(lean_object* v_00_u03b1_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_){
_start:
{
lean_object* v___x_4683_; 
v___x_4683_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg();
return v___x_4683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___boxed(lean_object* v_00_u03b1_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_){
_start:
{
lean_object* v_res_4692_; 
v_res_4692_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0(v_00_u03b1_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_);
lean_dec(v___y_4690_);
lean_dec_ref(v___y_4689_);
lean_dec(v___y_4688_);
lean_dec_ref(v___y_4687_);
lean_dec(v___y_4686_);
lean_dec_ref(v___y_4685_);
return v_res_4692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm(lean_object* v_stx_4699_, lean_object* v_expectedType_x3f_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_){
_start:
{
lean_object* v___x_4708_; uint8_t v___x_4709_; 
v___x_4708_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__1));
lean_inc(v_stx_4699_);
v___x_4709_ = l_Lean_Syntax_isOfKind(v_stx_4699_, v___x_4708_);
if (v___x_4709_ == 0)
{
lean_object* v___x_4710_; 
lean_dec(v_expectedType_x3f_4700_);
lean_dec(v_stx_4699_);
v___x_4710_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg();
return v___x_4710_;
}
else
{
lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v_body_4714_; lean_object* v___x_4715_; 
v___x_4711_ = lean_unsigned_to_nat(1u);
v___x_4712_ = l_Lean_Syntax_getArg(v_stx_4699_, v___x_4711_);
v___x_4713_ = lean_unsigned_to_nat(3u);
v_body_4714_ = l_Lean_Syntax_getArg(v_stx_4699_, v___x_4713_);
v___x_4715_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore(v___x_4712_, v_body_4714_, v_stx_4699_, v_expectedType_x3f_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_);
return v___x_4715_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___boxed(lean_object* v_stx_4716_, lean_object* v_expectedType_x3f_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_){
_start:
{
lean_object* v_res_4725_; 
v_res_4725_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm(v_stx_4716_, v_expectedType_x3f_4717_, v_a_4718_, v_a_4719_, v_a_4720_, v_a_4721_, v_a_4722_, v_a_4723_);
lean_dec(v_a_4723_);
lean_dec_ref(v_a_4722_);
lean_dec(v_a_4721_);
lean_dec_ref(v_a_4720_);
lean_dec(v_a_4719_);
lean_dec_ref(v_a_4718_);
return v_res_4725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1(){
_start:
{
lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; 
v___x_4731_ = l_Lean_Elab_Term_termElabAttribute;
v___x_4732_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__1));
v___x_4733_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1___closed__1));
v___x_4734_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___boxed), 9, 0);
v___x_4735_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4731_, v___x_4732_, v___x_4733_, v___x_4734_);
return v___x_4735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1___boxed(lean_object* v_a_4736_){
_start:
{
lean_object* v_res_4737_; 
v_res_4737_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1();
return v_res_4737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___redArg(){
_start:
{
lean_object* v___x_4739_; lean_object* v___x_4740_; 
v___x_4739_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0);
v___x_4740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4740_, 0, v___x_4739_);
return v___x_4740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___redArg___boxed(lean_object* v___y_4741_){
_start:
{
lean_object* v_res_4742_; 
v_res_4742_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___redArg();
return v_res_4742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0(lean_object* v_00_u03b1_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_){
_start:
{
lean_object* v___x_4752_; 
v___x_4752_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___redArg();
return v___x_4752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___boxed(lean_object* v_00_u03b1_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_){
_start:
{
lean_object* v_res_4762_; 
v_res_4762_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0(v_00_u03b1_4753_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_);
lean_dec(v___y_4760_);
lean_dec_ref(v___y_4759_);
lean_dec(v___y_4758_);
lean_dec_ref(v___y_4757_);
lean_dec(v___y_4756_);
lean_dec_ref(v___y_4755_);
lean_dec_ref(v___y_4754_);
return v_res_4762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___lam__0(lean_object* v_a_4763_, lean_object* v___x_4764_, lean_object* v_stx_4765_, lean_object* v_body_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_){
_start:
{
lean_object* v___x_4775_; lean_object* v___x_4776_; 
v___x_4775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4775_, 0, v_a_4763_);
v___x_4776_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore(v___x_4764_, v_body_4766_, v_stx_4765_, v___x_4775_, v___y_4768_, v___y_4769_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_);
return v___x_4776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___lam__0___boxed(lean_object* v_a_4777_, lean_object* v___x_4778_, lean_object* v_stx_4779_, lean_object* v_body_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_){
_start:
{
lean_object* v_res_4789_; 
v_res_4789_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___lam__0(v_a_4777_, v___x_4778_, v_stx_4779_, v_body_4780_, v___y_4781_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_);
lean_dec(v___y_4787_);
lean_dec_ref(v___y_4786_);
lean_dec(v___y_4785_);
lean_dec_ref(v___y_4784_);
lean_dec(v___y_4783_);
lean_dec_ref(v___y_4782_);
lean_dec_ref(v___y_4781_);
return v_res_4789_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__2(void){
_start:
{
lean_object* v___x_4793_; lean_object* v___x_4794_; 
v___x_4793_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__1));
v___x_4794_ = l_Lean_MessageData_ofFormat(v___x_4793_);
return v___x_4794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg(lean_object* v_stx_4795_, lean_object* v_dec_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_){
_start:
{
lean_object* v___x_4805_; uint8_t v___x_4806_; 
v___x_4805_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4));
lean_inc(v_stx_4795_);
v___x_4806_ = l_Lean_Syntax_isOfKind(v_stx_4795_, v___x_4805_);
if (v___x_4806_ == 0)
{
lean_object* v___x_4807_; 
lean_dec_ref(v_dec_4796_);
lean_dec(v_stx_4795_);
v___x_4807_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___redArg();
return v___x_4807_;
}
else
{
lean_object* v_doBlockResultType_4808_; lean_object* v___x_4809_; lean_object* v_tk_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; 
v_doBlockResultType_4808_ = lean_ctor_get(v_a_4797_, 3);
v___x_4809_ = lean_unsigned_to_nat(0u);
v_tk_4810_ = l_Lean_Syntax_getArg(v_stx_4795_, v___x_4809_);
v___x_4811_ = lean_unsigned_to_nat(1u);
v___x_4812_ = l_Lean_Syntax_getArg(v_stx_4795_, v___x_4811_);
lean_inc_ref(v_doBlockResultType_4808_);
v___x_4813_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_4808_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_);
if (lean_obj_tag(v___x_4813_) == 0)
{
lean_object* v_a_4814_; lean_object* v___f_4815_; lean_object* v___x_4816_; 
v_a_4814_ = lean_ctor_get(v___x_4813_, 0);
lean_inc(v_a_4814_);
lean_dec_ref_known(v___x_4813_, 1);
v___f_4815_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___lam__0___boxed), 12, 3);
lean_closure_set(v___f_4815_, 0, v_a_4814_);
lean_closure_set(v___f_4815_, 1, v___x_4812_);
lean_closure_set(v___f_4815_, 2, v_stx_4795_);
v___x_4816_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4796_, v_tk_4810_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_);
lean_dec(v_tk_4810_);
if (lean_obj_tag(v___x_4816_) == 0)
{
lean_object* v_a_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; 
v_a_4817_ = lean_ctor_get(v___x_4816_, 0);
lean_inc(v_a_4817_);
lean_dec_ref_known(v___x_4816_, 1);
v___x_4818_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__2, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__2_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__2);
v___x_4819_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4819_, 0, v_a_4817_);
v___x_4820_ = lean_box(0);
v___x_4821_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_4818_, v___x_4819_, v___f_4815_, v___x_4820_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_);
return v___x_4821_;
}
else
{
lean_object* v_a_4822_; lean_object* v___x_4824_; uint8_t v_isShared_4825_; uint8_t v_isSharedCheck_4829_; 
lean_dec_ref(v___f_4815_);
v_a_4822_ = lean_ctor_get(v___x_4816_, 0);
v_isSharedCheck_4829_ = !lean_is_exclusive(v___x_4816_);
if (v_isSharedCheck_4829_ == 0)
{
v___x_4824_ = v___x_4816_;
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
else
{
lean_inc(v_a_4822_);
lean_dec(v___x_4816_);
v___x_4824_ = lean_box(0);
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
v_resetjp_4823_:
{
lean_object* v___x_4827_; 
if (v_isShared_4825_ == 0)
{
v___x_4827_ = v___x_4824_;
goto v_reusejp_4826_;
}
else
{
lean_object* v_reuseFailAlloc_4828_; 
v_reuseFailAlloc_4828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4828_, 0, v_a_4822_);
v___x_4827_ = v_reuseFailAlloc_4828_;
goto v_reusejp_4826_;
}
v_reusejp_4826_:
{
return v___x_4827_;
}
}
}
}
else
{
lean_dec(v___x_4812_);
lean_dec(v_tk_4810_);
lean_dec_ref(v_dec_4796_);
lean_dec(v_stx_4795_);
return v___x_4813_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___boxed(lean_object* v_stx_4830_, lean_object* v_dec_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_){
_start:
{
lean_object* v_res_4840_; 
v_res_4840_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg(v_stx_4830_, v_dec_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_);
lean_dec(v_a_4838_);
lean_dec_ref(v_a_4837_);
lean_dec(v_a_4836_);
lean_dec_ref(v_a_4835_);
lean_dec(v_a_4834_);
lean_dec_ref(v_a_4833_);
lean_dec_ref(v_a_4832_);
return v_res_4840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1(){
_start:
{
lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; 
v___x_4846_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4847_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4));
v___x_4848_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1___closed__1));
v___x_4849_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___boxed), 10, 0);
v___x_4850_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4846_, v___x_4847_, v___x_4848_, v___x_4849_);
return v___x_4850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1___boxed(lean_object* v_a_4851_){
_start:
{
lean_object* v_res_4852_; 
v_res_4852_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1();
return v_res_4852_;
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
