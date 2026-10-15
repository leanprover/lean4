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
lean_object* v___y_1807_; lean_object* v_a_1808_; lean_object* v___y_1828_; lean_object* v___y_1829_; uint8_t v___y_1830_; lean_object* v___y_1831_; lean_object* v_val_1832_; lean_object* v_a_1840_; lean_object* v_a_1892_; lean_object* v___f_1894_; uint16_t v_port_1895_; lean_object* v___x_1896_; lean_object* v_addr_1897_; lean_object* v_server_x3f_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1959_; 
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
lean_inc_ref(v___y_1831_);
v___x_1835_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___y_1829_, v___y_1830_, v___x_1834_, v___y_1831_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1837_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
lean_dec_ref_known(v___x_1835_, 1);
v___x_1837_ = lean_task_pure(v_a_1836_);
v___y_1807_ = v___y_1828_;
v_a_1808_ = v___x_1837_;
goto v___jp_1806_;
}
else
{
lean_object* v_a_1838_; 
v_a_1838_ = lean_ctor_get(v___x_1835_, 0);
lean_inc_ref(v_a_1838_);
lean_dec_ref_known(v___x_1835_, 1);
v___y_1807_ = v___y_1828_;
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
v___y_1828_ = v_a_1846_;
v___y_1829_ = v___x_1848_;
v___y_1830_ = v___x_1849_;
v___y_1831_ = v___f_1847_;
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
v___y_1828_ = v_a_1846_;
v___y_1829_ = v___x_1848_;
v___y_1830_ = v___x_1849_;
v___y_1831_ = v___f_1847_;
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
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2055_ = lean_unsigned_to_nat(0u);
v___x_2056_ = l_Lean_Options_empty;
v___x_2057_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__17));
v___x_2058_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
lean_ctor_set(v___x_2058_, 1, v___x_2056_);
lean_ctor_set(v___x_2058_, 2, v___x_2057_);
lean_ctor_set(v___x_2058_, 3, v___x_2055_);
lean_ctor_set(v___x_2058_, 4, v___x_2055_);
lean_ctor_set(v___x_2058_, 5, v___x_2055_);
return v___x_2058_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__19(void){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2059_ = l_Lean_NameSet_empty;
v___x_2060_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12);
v___x_2061_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
lean_ctor_set(v___x_2061_, 1, v___x_2060_);
lean_ctor_set(v___x_2061_, 2, v___x_2059_);
return v___x_2061_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__20(void){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; lean_object* v___x_2065_; 
v___x_2062_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__12);
v___x_2063_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__15, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__15_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__15);
v___x_2064_ = 1;
v___x_2065_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2065_, 0, v___x_2063_);
lean_ctor_set(v___x_2065_, 1, v___x_2063_);
lean_ctor_set(v___x_2065_, 2, v___x_2062_);
lean_ctor_set_uint8(v___x_2065_, sizeof(void*)*3, v___x_2064_);
return v___x_2065_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__21(void){
_start:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2066_ = l_Lean_maxRecDepth;
v___x_2067_ = l_Lean_Options_empty;
v___x_2068_ = l_Lean_KVMap_instValueNat;
v___x_2069_ = l_Lean_Option_get___redArg(v___x_2068_, v___x_2067_, v___x_2066_);
return v___x_2069_;
}
}
static uint16_t _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__26(void){
_start:
{
uint16_t v___x_2074_; uint16_t v___x_2075_; uint16_t v___x_2076_; 
v___x_2074_ = 512;
v___x_2075_ = lean_uint16_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__5, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__5_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__5);
v___x_2076_ = lean_uint16_land(v___x_2075_, v___x_2074_);
return v___x_2076_;
}
}
static uint8_t _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__27(void){
_start:
{
uint16_t v___x_2077_; uint16_t v___x_2078_; uint8_t v___x_2079_; 
v___x_2077_ = 0;
v___x_2078_ = lean_uint16_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__26, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__26_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__26);
v___x_2079_ = lean_uint16_dec_eq(v___x_2078_, v___x_2077_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg(lean_object* v_env_2080_, lean_object* v_type_2081_, lean_object* v_value_2082_){
_start:
{
lean_object* v_a_2085_; lean_object* v_name_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v_decl_2095_; uint8_t v___x_2096_; uint8_t v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; uint16_t v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___y_2123_; lean_object* v___x_2175_; uint8_t v___y_2177_; lean_object* v_env_2198_; uint8_t v___x_2199_; uint8_t v___x_2200_; 
v_name_2088_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__1));
v___x_2089_ = lean_box(0);
v___x_2090_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2090_, 0, v_name_2088_);
lean_ctor_set(v___x_2090_, 1, v___x_2089_);
lean_ctor_set(v___x_2090_, 2, v_type_2081_);
v___x_2091_ = lean_box(0);
v___x_2092_ = 0;
v___x_2093_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__2));
v___x_2094_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2094_, 0, v___x_2090_);
lean_ctor_set(v___x_2094_, 1, v_value_2082_);
lean_ctor_set(v___x_2094_, 2, v___x_2091_);
lean_ctor_set(v___x_2094_, 3, v___x_2093_);
lean_ctor_set_uint8(v___x_2094_, sizeof(void*)*4, v___x_2092_);
v_decl_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_decl_2095_, 0, v___x_2094_);
v___x_2096_ = 1;
v___x_2097_ = 0;
v___x_2098_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__3));
v___x_2099_ = l_Lean_instInhabitedFileMap_default;
v___x_2100_ = l_Lean_Options_empty;
v___x_2101_ = lean_box(0);
v___x_2102_ = lean_unsigned_to_nat(0u);
v___x_2103_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__4, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__4_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__4);
v___x_2104_ = l_Lean_firstFrontendMacroScope;
v___x_2105_ = lean_box(0);
v___x_2106_ = lean_box(0);
v___x_2107_ = lean_uint16_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__5, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__5_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__5);
v___x_2108_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__6, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__6_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__6);
v___x_2109_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__9));
v___x_2110_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__10));
v___x_2111_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__13, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__13_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__13);
v___x_2112_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__16, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__16_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__16);
v___x_2113_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__17));
v___x_2114_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__18, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__18_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__18);
v___x_2115_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__19, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__19_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__19);
v___x_2116_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__20, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__20_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__20);
v___x_2117_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2117_, 0, v_env_2080_);
lean_ctor_set(v___x_2117_, 1, v___x_2108_);
lean_ctor_set(v___x_2117_, 2, v___x_2109_);
lean_ctor_set(v___x_2117_, 3, v___x_2110_);
lean_ctor_set(v___x_2117_, 4, v___x_2111_);
lean_ctor_set(v___x_2117_, 5, v___x_2112_);
lean_ctor_set(v___x_2117_, 6, v___x_2114_);
lean_ctor_set(v___x_2117_, 7, v___x_2115_);
lean_ctor_set(v___x_2117_, 8, v___x_2116_);
lean_ctor_set(v___x_2117_, 9, v___x_2113_);
v___x_2118_ = lean_io_get_num_heartbeats();
v___x_2119_ = lean_st_mk_ref(v___x_2117_);
v___x_2120_ = l_Lean_inheritedTraceOptions;
v___x_2121_ = lean_st_ref_get(v___x_2120_);
v___x_2175_ = lean_st_ref_get(v___x_2119_);
v_env_2198_ = lean_ctor_get(v___x_2175_, 0);
lean_inc_ref(v_env_2198_);
lean_dec(v___x_2175_);
v___x_2199_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2198_);
lean_dec_ref(v_env_2198_);
v___x_2200_ = lean_uint8_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__27, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__27_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__27);
if (v___x_2200_ == 0)
{
if (v___x_2199_ == 0)
{
v___y_2177_ = v___x_2096_;
goto v___jp_2176_;
}
else
{
lean_inc(v___x_2119_);
v___y_2123_ = v___x_2119_;
goto v___jp_2122_;
}
}
else
{
if (v___x_2199_ == 0)
{
lean_inc(v___x_2119_);
v___y_2123_ = v___x_2119_;
goto v___jp_2122_;
}
else
{
v___y_2177_ = v___x_2097_;
goto v___jp_2176_;
}
}
v___jp_2084_:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2086_ = lean_mk_io_user_error(v_a_2085_);
v___x_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
return v___x_2087_;
}
v___jp_2122_:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2124_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__21, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__21_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__21);
v___x_2125_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2098_);
lean_ctor_set(v___x_2125_, 1, v___x_2099_);
lean_ctor_set(v___x_2125_, 2, v___x_2100_);
lean_ctor_set(v___x_2125_, 3, v___x_2124_);
lean_ctor_set(v___x_2125_, 4, v___x_2101_);
lean_ctor_set(v___x_2125_, 5, v___x_2089_);
lean_ctor_set(v___x_2125_, 6, v___x_2118_);
lean_ctor_set(v___x_2125_, 7, v___x_2103_);
lean_ctor_set(v___x_2125_, 8, v___x_2101_);
lean_ctor_set(v___x_2125_, 9, v___x_2104_);
lean_ctor_set(v___x_2125_, 10, v___x_2105_);
lean_ctor_set(v___x_2125_, 11, v___x_2121_);
v___x_2126_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
lean_ctor_set(v___x_2126_, 1, v___x_2102_);
lean_ctor_set(v___x_2126_, 2, v___x_2106_);
lean_ctor_set_uint16(v___x_2126_, sizeof(void*)*3, v___x_2107_);
lean_ctor_set_uint8(v___x_2126_, sizeof(void*)*3 + 2, v___x_2097_);
lean_ctor_set_uint8(v___x_2126_, sizeof(void*)*3 + 3, v___x_2097_);
v___x_2127_ = l_Lean_addAndCompile(v_decl_2095_, v___x_2096_, v___x_2097_, v___x_2126_, v___y_2123_);
lean_dec(v___y_2123_);
lean_dec_ref_known(v___x_2126_, 3);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2151_; 
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2151_ == 0)
{
lean_object* v_unused_2152_; 
v_unused_2152_ = lean_ctor_get(v___x_2127_, 0);
lean_dec(v_unused_2152_);
v___x_2129_ = v___x_2127_;
v_isShared_2130_ = v_isSharedCheck_2151_;
goto v_resetjp_2128_;
}
else
{
lean_dec(v___x_2127_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2151_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2131_; lean_object* v_env_2132_; lean_object* v___x_2133_; 
v___x_2131_ = lean_st_ref_get(v___x_2119_);
lean_dec(v___x_2119_);
v_env_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc_ref(v_env_2132_);
lean_dec(v___x_2131_);
v___x_2133_ = l_Lean_Environment_evalConst___redArg(v_env_2132_, v___x_2100_, v_name_2088_, v___x_2097_);
lean_dec_ref(v_env_2132_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2146_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2146_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2146_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2141_; 
v___x_2138_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__22));
v___x_2139_ = lean_string_append(v___x_2138_, v_a_2134_);
lean_dec(v_a_2134_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set_tag(v___x_2136_, 18);
lean_ctor_set(v___x_2136_, 0, v___x_2139_);
v___x_2141_ = v___x_2136_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2139_);
v___x_2141_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
lean_object* v___x_2143_; 
if (v_isShared_2130_ == 0)
{
lean_ctor_set_tag(v___x_2129_, 1);
lean_ctor_set(v___x_2129_, 0, v___x_2141_);
v___x_2143_ = v___x_2129_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
else
{
lean_object* v_a_2147_; lean_object* v___x_2149_; 
v_a_2147_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2147_);
lean_dec_ref_known(v___x_2133_, 1);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 0, v_a_2147_);
v___x_2149_ = v___x_2129_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2147_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2174_; 
lean_dec(v___x_2119_);
v_a_2153_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2155_ = v___x_2127_;
v_isShared_2156_ = v_isSharedCheck_2174_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2127_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2174_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
if (lean_obj_tag(v_a_2153_) == 0)
{
lean_object* v_msg_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2161_; 
v_msg_2157_ = lean_ctor_get(v_a_2153_, 1);
lean_inc_ref(v_msg_2157_);
lean_dec_ref_known(v_a_2153_, 2);
v___x_2158_ = l_Lean_MessageData_toString(v_msg_2157_);
v___x_2159_ = lean_mk_io_user_error(v___x_2158_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 0, v___x_2159_);
v___x_2161_ = v___x_2155_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
else
{
lean_object* v_id_2163_; lean_object* v___x_2164_; 
lean_del_object(v___x_2155_);
v_id_2163_ = lean_ctor_get(v_a_2153_, 0);
lean_inc(v_id_2163_);
lean_dec_ref_known(v_a_2153_, 2);
v___x_2164_ = l_Lean_InternalExceptionId_getName(v_id_2163_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
lean_dec(v_id_2163_);
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2165_);
lean_dec_ref_known(v___x_2164_, 1);
v___x_2166_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__23));
v___x_2167_ = l_Lean_Name_toString(v_a_2165_, v___x_2096_);
v___x_2168_ = lean_string_append(v___x_2166_, v___x_2167_);
lean_dec_ref(v___x_2167_);
v_a_2085_ = v___x_2168_;
goto v___jp_2084_;
}
else
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
lean_dec_ref_known(v___x_2164_, 1);
v___x_2169_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__24));
v___x_2170_ = l_Nat_reprFast(v_id_2163_);
v___x_2171_ = lean_string_append(v___x_2169_, v___x_2170_);
lean_dec_ref(v___x_2170_);
v___x_2172_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__25));
v___x_2173_ = lean_string_append(v___x_2171_, v___x_2172_);
v_a_2085_ = v___x_2173_;
goto v___jp_2084_;
}
}
}
}
}
v___jp_2176_:
{
lean_object* v___x_2178_; lean_object* v_env_2179_; lean_object* v_nextMacroScope_2180_; lean_object* v_ngen_2181_; lean_object* v_auxDeclNGen_2182_; lean_object* v_traceState_2183_; lean_object* v_recordedDeps_2184_; lean_object* v_messages_2185_; lean_object* v_infoState_2186_; lean_object* v_snapshotTasks_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2196_; 
v___x_2178_ = lean_st_ref_take(v___x_2119_);
v_env_2179_ = lean_ctor_get(v___x_2178_, 0);
v_nextMacroScope_2180_ = lean_ctor_get(v___x_2178_, 1);
v_ngen_2181_ = lean_ctor_get(v___x_2178_, 2);
v_auxDeclNGen_2182_ = lean_ctor_get(v___x_2178_, 3);
v_traceState_2183_ = lean_ctor_get(v___x_2178_, 4);
v_recordedDeps_2184_ = lean_ctor_get(v___x_2178_, 6);
v_messages_2185_ = lean_ctor_get(v___x_2178_, 7);
v_infoState_2186_ = lean_ctor_get(v___x_2178_, 8);
v_snapshotTasks_2187_ = lean_ctor_get(v___x_2178_, 9);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2196_ == 0)
{
lean_object* v_unused_2197_; 
v_unused_2197_ = lean_ctor_get(v___x_2178_, 5);
lean_dec(v_unused_2197_);
v___x_2189_ = v___x_2178_;
v_isShared_2190_ = v_isSharedCheck_2196_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_snapshotTasks_2187_);
lean_inc(v_infoState_2186_);
lean_inc(v_messages_2185_);
lean_inc(v_recordedDeps_2184_);
lean_inc(v_traceState_2183_);
lean_inc(v_auxDeclNGen_2182_);
lean_inc(v_ngen_2181_);
lean_inc(v_nextMacroScope_2180_);
lean_inc(v_env_2179_);
lean_dec(v___x_2178_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2196_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2191_; lean_object* v___x_2193_; 
v___x_2191_ = l_Lean_Kernel_enableDiag(v_env_2179_, v___y_2177_);
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 5, v___x_2112_);
lean_ctor_set(v___x_2189_, 0, v___x_2191_);
v___x_2193_ = v___x_2189_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2191_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_nextMacroScope_2180_);
lean_ctor_set(v_reuseFailAlloc_2195_, 2, v_ngen_2181_);
lean_ctor_set(v_reuseFailAlloc_2195_, 3, v_auxDeclNGen_2182_);
lean_ctor_set(v_reuseFailAlloc_2195_, 4, v_traceState_2183_);
lean_ctor_set(v_reuseFailAlloc_2195_, 5, v___x_2112_);
lean_ctor_set(v_reuseFailAlloc_2195_, 6, v_recordedDeps_2184_);
lean_ctor_set(v_reuseFailAlloc_2195_, 7, v_messages_2185_);
lean_ctor_set(v_reuseFailAlloc_2195_, 8, v_infoState_2186_);
lean_ctor_set(v_reuseFailAlloc_2195_, 9, v_snapshotTasks_2187_);
v___x_2193_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
lean_object* v___x_2194_; 
v___x_2194_ = lean_st_ref_put(v___x_2119_, v___x_2193_);
lean_inc(v___x_2119_);
v___y_2123_ = v___x_2119_;
goto v___jp_2122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___boxed(lean_object* v_env_2201_, lean_object* v_type_2202_, lean_object* v_value_2203_, lean_object* v_a_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg(v_env_2201_, v_type_2202_, v_value_2203_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval(lean_object* v_00_u03b1_2206_, lean_object* v_inst_2207_, lean_object* v_env_2208_, lean_object* v_type_2209_, lean_object* v_value_2210_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg(v_env_2208_, v_type_2209_, v_value_2210_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___boxed(lean_object* v_00_u03b1_2213_, lean_object* v_inst_2214_, lean_object* v_env_2215_, lean_object* v_type_2216_, lean_object* v_value_2217_, lean_object* v_a_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval(v_00_u03b1_2213_, v_inst_2214_, v_env_2215_, v_type_2216_, v_value_2217_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(lean_object* v_e_2220_){
_start:
{
if (lean_obj_tag(v_e_2220_) == 0)
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2230_; 
v_a_2222_ = lean_ctor_get(v_e_2220_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_e_2220_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2224_ = v_e_2220_;
v_isShared_2225_ = v_isSharedCheck_2230_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v_e_2220_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2230_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2226_; lean_object* v___x_2228_; 
v___x_2226_ = lean_mk_io_user_error(v_a_2222_);
if (v_isShared_2225_ == 0)
{
lean_ctor_set_tag(v___x_2224_, 1);
lean_ctor_set(v___x_2224_, 0, v___x_2226_);
v___x_2228_ = v___x_2224_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2226_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
v_a_2231_ = lean_ctor_get(v_e_2220_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v_e_2220_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v_e_2220_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v_e_2220_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
lean_ctor_set_tag(v___x_2233_, 0);
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg___boxed(lean_object* v_e_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v_e_2239_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2(lean_object* v_00_u03b1_2242_, lean_object* v_e_2243_){
_start:
{
lean_object* v___x_2245_; 
v___x_2245_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v_e_2243_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___boxed(lean_object* v_00_u03b1_2246_, lean_object* v_e_2247_, lean_object* v_a_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2(v_00_u03b1_2246_, v_e_2247_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__1(lean_object* v___x_2250_, lean_object* v_x_2251_){
_start:
{
if (lean_obj_tag(v_x_2251_) == 0)
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = lean_mk_io_user_error(v___x_2250_);
v___x_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
return v___x_2253_;
}
else
{
lean_object* v_val_2254_; 
lean_dec_ref(v___x_2250_);
v_val_2254_ = lean_ctor_get(v_x_2251_, 0);
lean_inc(v_val_2254_);
return v_val_2254_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__1___boxed(lean_object* v___x_2255_, lean_object* v_x_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__1(v___x_2255_, v_x_2256_);
lean_dec(v_x_2256_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__2(lean_object* v___f_2258_, lean_object* v_x_2259_){
_start:
{
if (lean_obj_tag(v_x_2259_) == 0)
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2269_; 
lean_dec_ref(v___f_2258_);
v_a_2261_ = lean_ctor_get(v_x_2259_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v_x_2259_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2263_ = v_x_2259_;
v_isShared_2264_ = v_isSharedCheck_2269_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v_x_2259_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2269_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
lean_object* v___x_2267_; 
v___x_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
return v___x_2267_;
}
}
}
else
{
lean_object* v_a_2270_; 
v_a_2270_ = lean_ctor_get(v_x_2259_, 0);
lean_inc(v_a_2270_);
lean_dec_ref_known(v_x_2259_, 1);
if (lean_obj_tag(v_a_2270_) == 0)
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2279_; 
lean_dec_ref(v___f_2258_);
v_a_2271_ = lean_ctor_get(v_a_2270_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v_a_2270_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2273_ = v_a_2270_;
v_isShared_2274_ = v_isSharedCheck_2279_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v_a_2270_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2279_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2276_; 
if (v_isShared_2274_ == 0)
{
v___x_2276_ = v___x_2273_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2271_);
v___x_2276_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
lean_object* v___x_2277_; 
v___x_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
return v___x_2277_;
}
}
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; uint8_t v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v_a_2280_ = lean_ctor_get(v_a_2270_, 0);
lean_inc(v_a_2280_);
lean_dec_ref_known(v_a_2270_, 1);
v___x_2281_ = lean_io_promise_result_opt(v_a_2280_);
lean_dec(v_a_2280_);
v___x_2282_ = lean_unsigned_to_nat(0u);
v___x_2283_ = 0;
v___x_2284_ = lean_task_map(v___f_2258_, v___x_2281_, v___x_2282_, v___x_2283_);
v___x_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2284_);
return v___x_2285_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__2___boxed(lean_object* v___f_2286_, lean_object* v_x_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__2(v___f_2286_, v_x_2287_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0___redArg(lean_object* v___x_2290_, lean_object* v___x_2291_, lean_object* v___x_2292_, lean_object* v_a_2293_, lean_object* v_b_2294_){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = lean_box(0);
switch(lean_obj_tag(v_a_2293_))
{
case 0:
{
lean_object* v_pos_2296_; lean_object* v___x_2297_; 
v_pos_2296_ = lean_ctor_get(v_a_2293_, 0);
lean_inc(v_pos_2296_);
lean_dec_ref_known(v_a_2293_, 1);
v___x_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2297_, 0, v_pos_2296_);
return v___x_2297_;
}
case 1:
{
lean_object* v_pos_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2307_; 
v_pos_2298_ = lean_ctor_get(v_a_2293_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v_a_2293_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2300_ = v_a_2293_;
v_isShared_2301_ = v_isSharedCheck_2307_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_pos_2298_);
lean_dec(v_a_2293_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2307_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2302_; lean_object* v___x_2304_; 
v___x_2302_ = lean_string_utf8_next_fast(v___x_2290_, v_pos_2298_);
lean_dec(v_pos_2298_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set_tag(v___x_2300_, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2302_);
v___x_2304_ = v___x_2300_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2302_);
v___x_2304_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
v_a_2293_ = v___x_2304_;
v_b_2294_ = v___x_2295_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_2308_; lean_object* v_table_2309_; lean_object* v_stackPos_2310_; lean_object* v_needlePos_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2364_; 
v_needle_2308_ = lean_ctor_get(v_a_2293_, 0);
v_table_2309_ = lean_ctor_get(v_a_2293_, 1);
v_stackPos_2310_ = lean_ctor_get(v_a_2293_, 2);
v_needlePos_2311_ = lean_ctor_get(v_a_2293_, 3);
v_isSharedCheck_2364_ = !lean_is_exclusive(v_a_2293_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2313_ = v_a_2293_;
v_isShared_2314_ = v_isSharedCheck_2364_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_needlePos_2311_);
lean_inc(v_stackPos_2310_);
lean_inc(v_table_2309_);
lean_inc(v_needle_2308_);
lean_dec(v_a_2293_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2364_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v_str_2315_; lean_object* v_startInclusive_2316_; lean_object* v_endExclusive_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; uint8_t v___x_2321_; 
v_str_2315_ = lean_ctor_get(v_needle_2308_, 0);
v_startInclusive_2316_ = lean_ctor_get(v_needle_2308_, 1);
v_endExclusive_2317_ = lean_ctor_get(v_needle_2308_, 2);
v___x_2318_ = lean_nat_sub(v_stackPos_2310_, v_needlePos_2311_);
v___x_2319_ = lean_nat_sub(v_endExclusive_2317_, v_startInclusive_2316_);
v___x_2320_ = lean_nat_add(v___x_2318_, v___x_2319_);
v___x_2321_ = lean_nat_dec_le(v___x_2320_, v___x_2292_);
lean_dec(v___x_2320_);
if (v___x_2321_ == 0)
{
lean_object* v___x_2322_; lean_object* v___x_2323_; uint8_t v___x_2324_; 
lean_dec(v___x_2319_);
lean_del_object(v___x_2313_);
lean_dec(v_needlePos_2311_);
lean_dec(v_stackPos_2310_);
lean_dec_ref(v_table_2309_);
lean_dec_ref(v_needle_2308_);
v___x_2322_ = lean_unsigned_to_nat(1u);
v___x_2323_ = lean_nat_add(v___x_2318_, v___x_2322_);
lean_dec(v___x_2318_);
v___x_2324_ = lean_nat_dec_le(v___x_2323_, v___x_2292_);
lean_dec(v___x_2323_);
if (v___x_2324_ == 0)
{
lean_inc(v_b_2294_);
return v_b_2294_;
}
else
{
lean_object* v___x_2325_; 
v___x_2325_ = lean_box(3);
v_a_2293_ = v___x_2325_;
v_b_2294_ = v___x_2295_;
goto _start;
}
}
else
{
uint8_t v_stackByte_2327_; lean_object* v___x_2328_; uint8_t v_patByte_2329_; uint8_t v___x_2330_; 
lean_dec(v___x_2318_);
lean_inc(v_stackPos_2310_);
v_stackByte_2327_ = lean_string_get_byte_fast(v___x_2290_, v_stackPos_2310_);
v___x_2328_ = lean_nat_add(v_startInclusive_2316_, v_needlePos_2311_);
v_patByte_2329_ = lean_string_get_byte_fast(v_str_2315_, v___x_2328_);
v___x_2330_ = lean_uint8_dec_eq(v_stackByte_2327_, v_patByte_2329_);
if (v___x_2330_ == 0)
{
lean_object* v___x_2331_; uint8_t v_decide_2332_; 
lean_dec(v___x_2319_);
v___x_2331_ = lean_unsigned_to_nat(0u);
v_decide_2332_ = lean_nat_dec_eq(v_needlePos_2311_, v___x_2331_);
if (v_decide_2332_ == 0)
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v_newNeedlePos_2335_; uint8_t v___x_2336_; 
v___x_2333_ = lean_unsigned_to_nat(1u);
v___x_2334_ = lean_nat_sub(v_needlePos_2311_, v___x_2333_);
lean_dec(v_needlePos_2311_);
v_newNeedlePos_2335_ = lean_array_fget_borrowed(v_table_2309_, v___x_2334_);
lean_dec(v___x_2334_);
v___x_2336_ = lean_nat_dec_eq(v_newNeedlePos_2335_, v___x_2331_);
if (v___x_2336_ == 0)
{
lean_object* v___x_2338_; 
lean_inc(v_newNeedlePos_2335_);
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 3, v_newNeedlePos_2335_);
v___x_2338_ = v___x_2313_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_needle_2308_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_table_2309_);
lean_ctor_set(v_reuseFailAlloc_2340_, 2, v_stackPos_2310_);
lean_ctor_set(v_reuseFailAlloc_2340_, 3, v_newNeedlePos_2335_);
v___x_2338_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
v_a_2293_ = v___x_2338_;
v_b_2294_ = v___x_2295_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_2341_; lean_object* v___x_2343_; 
v_nextStackPos_2341_ = l_String_Slice_posGE___redArg(v___x_2291_, v_stackPos_2310_);
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 3, v___x_2331_);
lean_ctor_set(v___x_2313_, 2, v_nextStackPos_2341_);
v___x_2343_ = v___x_2313_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_needle_2308_);
lean_ctor_set(v_reuseFailAlloc_2345_, 1, v_table_2309_);
lean_ctor_set(v_reuseFailAlloc_2345_, 2, v_nextStackPos_2341_);
lean_ctor_set(v_reuseFailAlloc_2345_, 3, v___x_2331_);
v___x_2343_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
v_a_2293_ = v___x_2343_;
v_b_2294_ = v___x_2295_;
goto _start;
}
}
}
else
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v_nextStackPos_2348_; lean_object* v___x_2350_; 
lean_dec(v_needlePos_2311_);
v___x_2346_ = lean_unsigned_to_nat(1u);
v___x_2347_ = lean_nat_add(v_stackPos_2310_, v___x_2346_);
lean_dec(v_stackPos_2310_);
v_nextStackPos_2348_ = l_String_Slice_posGE___redArg(v___x_2291_, v___x_2347_);
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 3, v___x_2331_);
lean_ctor_set(v___x_2313_, 2, v_nextStackPos_2348_);
v___x_2350_ = v___x_2313_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_needle_2308_);
lean_ctor_set(v_reuseFailAlloc_2352_, 1, v_table_2309_);
lean_ctor_set(v_reuseFailAlloc_2352_, 2, v_nextStackPos_2348_);
lean_ctor_set(v_reuseFailAlloc_2352_, 3, v___x_2331_);
v___x_2350_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
v_a_2293_ = v___x_2350_;
v_b_2294_ = v___x_2295_;
goto _start;
}
}
}
else
{
lean_object* v___x_2353_; lean_object* v_nextStackPos_2354_; lean_object* v_nextNeedlePos_2355_; uint8_t v_decide_2356_; 
v___x_2353_ = lean_unsigned_to_nat(1u);
v_nextStackPos_2354_ = lean_nat_add(v_stackPos_2310_, v___x_2353_);
lean_dec(v_stackPos_2310_);
v_nextNeedlePos_2355_ = lean_nat_add(v_needlePos_2311_, v___x_2353_);
lean_dec(v_needlePos_2311_);
v_decide_2356_ = lean_nat_dec_eq(v_nextNeedlePos_2355_, v___x_2319_);
lean_dec(v___x_2319_);
if (v_decide_2356_ == 0)
{
lean_object* v___x_2358_; 
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 3, v_nextNeedlePos_2355_);
lean_ctor_set(v___x_2313_, 2, v_nextStackPos_2354_);
v___x_2358_ = v___x_2313_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_needle_2308_);
lean_ctor_set(v_reuseFailAlloc_2360_, 1, v_table_2309_);
lean_ctor_set(v_reuseFailAlloc_2360_, 2, v_nextStackPos_2354_);
lean_ctor_set(v_reuseFailAlloc_2360_, 3, v_nextNeedlePos_2355_);
v___x_2358_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
v_a_2293_ = v___x_2358_;
goto _start;
}
}
else
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
lean_del_object(v___x_2313_);
lean_dec_ref(v_table_2309_);
lean_dec_ref(v_needle_2308_);
v___x_2361_ = lean_nat_sub(v_nextStackPos_2354_, v_nextNeedlePos_2355_);
lean_dec(v_nextNeedlePos_2355_);
lean_dec(v_nextStackPos_2354_);
v___x_2362_ = l_String_Slice_pos_x21(v___x_2291_, v___x_2361_);
lean_dec(v___x_2361_);
v___x_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2362_);
return v___x_2363_;
}
}
}
}
}
default: 
{
lean_inc(v_b_2294_);
return v_b_2294_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0___redArg___boxed(lean_object* v___x_2365_, lean_object* v___x_2366_, lean_object* v___x_2367_, lean_object* v_a_2368_, lean_object* v_b_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0___redArg(v___x_2365_, v___x_2366_, v___x_2367_, v_a_2368_, v_b_2369_);
lean_dec(v_b_2369_);
lean_dec(v___x_2367_);
lean_dec_ref(v___x_2366_);
lean_dec_ref(v___x_2365_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__0(lean_object* v_____r_2371_){
_start:
{
uint32_t v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2373_ = 500;
v___x_2374_ = l_IO_sleep(v___x_2373_);
v___x_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__0___boxed(lean_object* v_____r_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__0(v_____r_2376_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1_spec__1(lean_object* v_s_2379_){
_start:
{
lean_object* v___x_2381_; lean_object* v_putStr_2382_; lean_object* v___x_2383_; 
v___x_2381_ = lean_get_stderr();
v_putStr_2382_ = lean_ctor_get(v___x_2381_, 4);
lean_inc_ref(v_putStr_2382_);
lean_dec_ref(v___x_2381_);
v___x_2383_ = lean_apply_2(v_putStr_2382_, v_s_2379_, lean_box(0));
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1_spec__1___boxed(lean_object* v_s_2384_, lean_object* v_a_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1_spec__1(v_s_2384_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1(lean_object* v_s_2387_){
_start:
{
uint32_t v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2389_ = 10;
v___x_2390_ = lean_string_push(v_s_2387_, v___x_2389_);
v___x_2391_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1_spec__1(v___x_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1___boxed(lean_object* v_s_2392_, lean_object* v_a_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l_IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1(v_s_2392_);
return v_res_2394_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2400_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__1));
v___x_2401_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_2400_);
return v___x_2401_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2402_ = lean_unsigned_to_nat(0u);
v___x_2403_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__2);
v___x_2404_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__1));
v___x_2405_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2404_);
lean_ctor_set(v___x_2405_, 1, v___x_2403_);
lean_ctor_set(v___x_2405_, 2, v___x_2402_);
lean_ctor_set(v___x_2405_, 3, v___x_2402_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg(lean_object* v_a_2411_, lean_object* v_apply_2412_, lean_object* v___x_2413_){
_start:
{
lean_object* v___y_2416_; lean_object* v___x_2418_; lean_object* v_a_2420_; lean_object* v___y_2435_; lean_object* v_a_2439_; lean_object* v___y_2442_; lean_object* v___y_2443_; uint8_t v___y_2444_; lean_object* v_val_2445_; lean_object* v___x_2452_; 
v___x_2418_ = lean_box(0);
v___x_2452_ = lean_uv_tcp_new();
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2541_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2455_ = v___x_2452_;
v_isShared_2456_ = v_isSharedCheck_2541_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2452_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2541_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v_a_2458_; lean_object* v___x_2511_; 
lean_inc_ref(v___x_2413_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v___x_2413_);
v___x_2511_ = v___x_2455_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2413_);
v___x_2511_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2510_;
}
v___jp_2457_:
{
lean_object* v___x_2459_; 
v___x_2459_ = l_Std_Async_AsyncTask_block___redArg(v_a_2458_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v___x_2460_; 
lean_dec_ref_known(v___x_2459_, 1);
v___x_2460_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_recvMsg(v_a_2453_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_a_2461_);
lean_dec_ref_known(v___x_2460_, 1);
v___x_2462_ = l_Lean_Json_parse(v_a_2461_);
v___x_2463_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_2462_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc_n(v_a_2464_, 2);
lean_dec_ref_known(v___x_2463_, 1);
v___x_2465_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__8));
v___x_2466_ = l_Lean_Json_getObjVal_x3f(v_a_2464_, v___x_2465_);
v___x_2467_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_2466_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_a_2468_);
lean_dec_ref_known(v___x_2467_, 1);
v___x_2469_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f(v_a_2468_);
v___x_2470_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_2469_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v_a_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v_a_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_a_2471_);
lean_dec_ref_known(v___x_2470_, 1);
v___x_2472_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__13));
v___x_2473_ = l_Lean_Json_getObjVal_x3f(v_a_2464_, v___x_2472_);
v___x_2474_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_2473_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v_a_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_a_2475_);
lean_dec_ref_known(v___x_2474_, 1);
v___x_2476_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprFromJson_x3f(v_a_2475_);
v___x_2477_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_2476_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; lean_object* v___x_2479_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_a_2478_);
lean_dec_ref_known(v___x_2477_, 1);
lean_inc_ref(v_a_2411_);
v___x_2479_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg(v_a_2411_, v_a_2471_, v_a_2478_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v_a_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
lean_inc(v_a_2480_);
lean_dec_ref_known(v___x_2479_, 1);
lean_inc_ref(v_apply_2412_);
v___x_2481_ = lean_apply_1(v_apply_2412_, v_a_2480_);
v___x_2482_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_sendMsg(v_a_2453_, v___x_2481_);
lean_dec_ref(v___x_2481_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v___f_2483_; lean_object* v___x_2484_; uint8_t v___x_2485_; lean_object* v___x_2486_; 
lean_dec_ref_known(v___x_2482_, 1);
v___f_2483_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__6));
v___x_2484_ = lean_unsigned_to_nat(0u);
v___x_2485_ = 0;
v___x_2486_ = lean_uv_tcp_shutdown(v_a_2453_);
lean_dec(v_a_2453_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2486_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2486_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
lean_ctor_set_tag(v___x_2489_, 1);
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
v___y_2442_ = v___x_2484_;
v___y_2443_ = v___f_2483_;
v___y_2444_ = v___x_2485_;
v_val_2445_ = v___x_2492_;
goto v___jp_2441_;
}
}
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
v_a_2495_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2486_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2486_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
lean_ctor_set_tag(v___x_2497_, 0);
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
v___y_2442_ = v___x_2484_;
v___y_2443_ = v___f_2483_;
v___y_2444_ = v___x_2485_;
v_val_2445_ = v___x_2500_;
goto v___jp_2441_;
}
}
}
}
else
{
lean_dec(v_a_2453_);
v___y_2435_ = v___x_2482_;
goto v___jp_2434_;
}
}
else
{
lean_object* v_a_2503_; 
lean_dec(v_a_2453_);
v_a_2503_ = lean_ctor_get(v___x_2479_, 0);
lean_inc(v_a_2503_);
lean_dec_ref_known(v___x_2479_, 1);
v_a_2420_ = v_a_2503_;
goto v___jp_2419_;
}
}
else
{
lean_object* v_a_2504_; 
lean_dec(v_a_2471_);
lean_dec(v_a_2453_);
v_a_2504_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_a_2504_);
lean_dec_ref_known(v___x_2477_, 1);
v_a_2420_ = v_a_2504_;
goto v___jp_2419_;
}
}
else
{
lean_object* v_a_2505_; 
lean_dec(v_a_2471_);
lean_dec(v_a_2453_);
v_a_2505_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_a_2505_);
lean_dec_ref_known(v___x_2474_, 1);
v_a_2420_ = v_a_2505_;
goto v___jp_2419_;
}
}
else
{
lean_object* v_a_2506_; 
lean_dec(v_a_2464_);
lean_dec(v_a_2453_);
v_a_2506_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_a_2506_);
lean_dec_ref_known(v___x_2470_, 1);
v_a_2420_ = v_a_2506_;
goto v___jp_2419_;
}
}
else
{
lean_object* v_a_2507_; 
lean_dec(v_a_2464_);
lean_dec(v_a_2453_);
v_a_2507_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_a_2507_);
lean_dec_ref_known(v___x_2467_, 1);
v_a_2420_ = v_a_2507_;
goto v___jp_2419_;
}
}
else
{
lean_object* v_a_2508_; 
lean_dec(v_a_2453_);
v_a_2508_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_a_2508_);
lean_dec_ref_known(v___x_2463_, 1);
v_a_2420_ = v_a_2508_;
goto v___jp_2419_;
}
}
else
{
lean_object* v_a_2509_; 
lean_dec(v_a_2453_);
v_a_2509_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_a_2509_);
lean_dec_ref_known(v___x_2460_, 1);
v_a_2420_ = v_a_2509_;
goto v___jp_2419_;
}
}
else
{
lean_dec(v_a_2453_);
v___y_2435_ = v___x_2459_;
goto v___jp_2434_;
}
}
v_reusejp_2510_:
{
lean_object* v___f_2512_; lean_object* v___x_2513_; uint8_t v___x_2514_; lean_object* v_val_2516_; lean_object* v___x_2523_; 
v___f_2512_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__6));
v___x_2513_ = lean_unsigned_to_nat(0u);
v___x_2514_ = 0;
v___x_2523_ = lean_uv_tcp_connect(v_a_2453_, v___x_2511_);
lean_dec_ref(v___x_2511_);
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
v_val_2516_ = v___x_2529_;
goto v___jp_2515_;
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
v_val_2516_ = v___x_2537_;
goto v___jp_2515_;
}
}
}
v___jp_2515_:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2517_, 0, v_val_2516_);
v___x_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2517_);
v___x_2519_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2513_, v___x_2514_, v___x_2518_, v___f_2512_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v_a_2520_; lean_object* v___x_2521_; 
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_a_2520_);
lean_dec_ref_known(v___x_2519_, 1);
v___x_2521_ = lean_task_pure(v_a_2520_);
v_a_2458_ = v___x_2521_;
goto v___jp_2457_;
}
else
{
lean_object* v_a_2522_; 
v_a_2522_ = lean_ctor_get(v___x_2519_, 0);
lean_inc_ref(v_a_2522_);
lean_dec_ref_known(v___x_2519_, 1);
v_a_2458_ = v_a_2522_;
goto v___jp_2457_;
}
}
}
}
}
else
{
lean_object* v_a_2542_; 
v_a_2542_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_a_2542_);
lean_dec_ref_known(v___x_2452_, 1);
v_a_2420_ = v_a_2542_;
goto v___jp_2419_;
}
v___jp_2415_:
{
if (lean_obj_tag(v___y_2416_) == 0)
{
lean_dec_ref_known(v___y_2416_, 1);
goto _start;
}
else
{
lean_dec_ref(v___x_2413_);
lean_dec_ref(v_apply_2412_);
lean_dec_ref(v_a_2411_);
return v___y_2416_;
}
}
v___jp_2419_:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2421_ = lean_io_error_to_string(v_a_2420_);
v___x_2422_ = lean_unsigned_to_nat(0u);
v___x_2423_ = lean_string_utf8_byte_size(v___x_2421_);
lean_inc_ref(v___x_2421_);
v___x_2424_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2421_);
lean_ctor_set(v___x_2424_, 1, v___x_2422_);
lean_ctor_set(v___x_2424_, 2, v___x_2423_);
v___x_2425_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__3);
v___x_2426_ = lean_box(0);
v___x_2427_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0___redArg(v___x_2421_, v___x_2424_, v___x_2423_, v___x_2425_, v___x_2426_);
lean_dec_ref_known(v___x_2424_, 3);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2428_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___closed__4));
v___x_2429_ = lean_string_append(v___x_2428_, v___x_2421_);
lean_dec_ref(v___x_2421_);
v___x_2430_ = l_IO_eprintln___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__1(v___x_2429_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_a_2431_; lean_object* v___x_2432_; 
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_a_2431_);
lean_dec_ref_known(v___x_2430_, 1);
v___x_2432_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__0(v_a_2431_);
v___y_2416_ = v___x_2432_;
goto v___jp_2415_;
}
else
{
v___y_2416_ = v___x_2430_;
goto v___jp_2415_;
}
}
else
{
lean_object* v___x_2433_; 
lean_dec_ref_known(v___x_2427_, 1);
lean_dec_ref(v___x_2421_);
v___x_2433_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___lam__0(v___x_2418_);
v___y_2416_ = v___x_2433_;
goto v___jp_2415_;
}
}
v___jp_2434_:
{
if (lean_obj_tag(v___y_2435_) == 0)
{
lean_dec_ref_known(v___y_2435_, 1);
goto _start;
}
else
{
lean_object* v_a_2437_; 
v_a_2437_ = lean_ctor_get(v___y_2435_, 0);
lean_inc(v_a_2437_);
lean_dec_ref_known(v___y_2435_, 1);
v_a_2420_ = v_a_2437_;
goto v___jp_2419_;
}
}
v___jp_2438_:
{
lean_object* v___x_2440_; 
v___x_2440_ = l_Std_Async_AsyncTask_block___redArg(v_a_2439_);
v___y_2435_ = v___x_2440_;
goto v___jp_2434_;
}
v___jp_2441_:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2446_, 0, v_val_2445_);
v___x_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2446_);
lean_inc_ref(v___y_2443_);
v___x_2448_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___y_2442_, v___y_2444_, v___x_2447_, v___y_2443_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_object* v_a_2449_; lean_object* v___x_2450_; 
v_a_2449_ = lean_ctor_get(v___x_2448_, 0);
lean_inc(v_a_2449_);
lean_dec_ref_known(v___x_2448_, 1);
v___x_2450_ = lean_task_pure(v_a_2449_);
v_a_2439_ = v___x_2450_;
goto v___jp_2438_;
}
else
{
lean_object* v_a_2451_; 
v_a_2451_ = lean_ctor_get(v___x_2448_, 0);
lean_inc_ref(v_a_2451_);
lean_dec_ref_known(v___x_2448_, 1);
v_a_2439_ = v_a_2451_;
goto v___jp_2438_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg___boxed(lean_object* v_a_2543_, lean_object* v_apply_2544_, lean_object* v___x_2545_, lean_object* v___y_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg(v_a_2543_, v_apply_2544_, v___x_2545_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* lean_idbg_client_loop(lean_object* v_siteId_2548_, lean_object* v_imports_2549_, lean_object* v_apply_2550_){
_start:
{
lean_object* v___x_2552_; 
v___x_2552_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgLoadEnv(v_imports_2549_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; uint16_t v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref_known(v___x_2552_, 1);
v___x_2554_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgPort(v_siteId_2548_);
lean_dec_ref(v_siteId_2548_);
v___x_2555_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__1, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__1_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer___closed__1);
v___x_2556_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2556_, 0, v___x_2555_);
lean_ctor_set_uint16(v___x_2556_, sizeof(void*)*1, v___x_2554_);
v___x_2557_ = lean_box(0);
v___x_2558_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg(v_a_2553_, v_apply_2550_, v___x_2556_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2565_; 
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2565_ == 0)
{
lean_object* v_unused_2566_; 
v_unused_2566_ = lean_ctor_get(v___x_2558_, 0);
lean_dec(v_unused_2566_);
v___x_2560_ = v___x_2558_;
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
else
{
lean_dec(v___x_2558_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 0, v___x_2557_);
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2557_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
else
{
return v___x_2558_;
}
}
else
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
lean_dec_ref(v_apply_2550_);
lean_dec_ref(v_siteId_2548_);
v_a_2567_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2569_ = v___x_2552_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2552_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2570_ == 0)
{
v___x_2572_ = v___x_2569_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2567_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl___boxed(lean_object* v_siteId_2575_, lean_object* v_imports_2576_, lean_object* v_apply_2577_, lean_object* v_a_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = lean_idbg_client_loop(v_siteId_2575_, v_imports_2576_, v_apply_2577_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0(lean_object* v___x_2580_, lean_object* v___x_2581_, lean_object* v___x_2582_, lean_object* v_inst_2583_, lean_object* v_R_2584_, lean_object* v_a_2585_, lean_object* v_b_2586_, lean_object* v_c_2587_){
_start:
{
lean_object* v___x_2588_; 
v___x_2588_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0___redArg(v___x_2580_, v___x_2581_, v___x_2582_, v_a_2585_, v_b_2586_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0___boxed(lean_object* v___x_2589_, lean_object* v___x_2590_, lean_object* v___x_2591_, lean_object* v_inst_2592_, lean_object* v_R_2593_, lean_object* v_a_2594_, lean_object* v_b_2595_, lean_object* v_c_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__0(v___x_2589_, v___x_2590_, v___x_2591_, v_inst_2592_, v_R_2593_, v_a_2594_, v_b_2595_, v_c_2596_);
lean_dec(v_b_2595_);
lean_dec(v___x_2591_);
lean_dec_ref(v___x_2590_);
lean_dec_ref(v___x_2589_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3(lean_object* v_a_2598_, lean_object* v_apply_2599_, lean_object* v___x_2600_, lean_object* v_inst_2601_, lean_object* v_a_2602_){
_start:
{
lean_object* v___x_2604_; 
v___x_2604_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___redArg(v_a_2598_, v_apply_2599_, v___x_2600_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3___boxed(lean_object* v_a_2605_, lean_object* v_apply_2606_, lean_object* v___x_2607_, lean_object* v_inst_2608_, lean_object* v_a_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__3(v_a_2605_, v_apply_2606_, v___x_2607_, v_inst_2608_, v_a_2609_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___redArg(){
_start:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2613_ = l_Lean_Elab_Do_instInhabitedControlInfo_default;
v___x_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2613_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___redArg___boxed(lean_object* v_a_2615_){
_start:
{
lean_object* v_res_2616_; 
v_res_2616_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___redArg();
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg(lean_object* v_x_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_){
_start:
{
lean_object* v___x_2625_; 
v___x_2625_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___redArg();
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___boxed(lean_object* v_x_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg(v_x_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_);
lean_dec(v_a_2632_);
lean_dec_ref(v_a_2631_);
lean_dec(v_a_2630_);
lean_dec_ref(v_a_2629_);
lean_dec(v_a_2628_);
lean_dec_ref(v_a_2627_);
lean_dec(v_x_2626_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1(){
_start:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2677_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2678_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4));
v___x_2679_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__18));
v___x_2680_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___boxed), 8, 0);
v___x_2681_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2677_, v___x_2678_, v___x_2679_, v___x_2680_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___boxed(lean_object* v_a_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1();
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(lean_object* v_e_2684_, lean_object* v___y_2685_){
_start:
{
uint8_t v___x_2687_; 
v___x_2687_ = l_Lean_Expr_hasMVar(v_e_2684_);
if (v___x_2687_ == 0)
{
lean_object* v___x_2688_; 
v___x_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2688_, 0, v_e_2684_);
return v___x_2688_;
}
else
{
lean_object* v___x_2689_; lean_object* v_mctx_2690_; lean_object* v___x_2691_; lean_object* v_fst_2692_; lean_object* v_snd_2693_; lean_object* v___x_2694_; lean_object* v_cache_2695_; lean_object* v_zetaDeltaFVarIds_2696_; lean_object* v_postponed_2697_; lean_object* v_diag_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2707_; 
v___x_2689_ = lean_st_ref_get(v___y_2685_);
v_mctx_2690_ = lean_ctor_get(v___x_2689_, 0);
lean_inc_ref(v_mctx_2690_);
lean_dec(v___x_2689_);
v___x_2691_ = l_Lean_instantiateMVarsCore(v_mctx_2690_, v_e_2684_);
v_fst_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_fst_2692_);
v_snd_2693_ = lean_ctor_get(v___x_2691_, 1);
lean_inc(v_snd_2693_);
lean_dec_ref(v___x_2691_);
v___x_2694_ = lean_st_ref_take(v___y_2685_);
v_cache_2695_ = lean_ctor_get(v___x_2694_, 1);
v_zetaDeltaFVarIds_2696_ = lean_ctor_get(v___x_2694_, 2);
v_postponed_2697_ = lean_ctor_get(v___x_2694_, 3);
v_diag_2698_ = lean_ctor_get(v___x_2694_, 4);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2707_ == 0)
{
lean_object* v_unused_2708_; 
v_unused_2708_ = lean_ctor_get(v___x_2694_, 0);
lean_dec(v_unused_2708_);
v___x_2700_ = v___x_2694_;
v_isShared_2701_ = v_isSharedCheck_2707_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_diag_2698_);
lean_inc(v_postponed_2697_);
lean_inc(v_zetaDeltaFVarIds_2696_);
lean_inc(v_cache_2695_);
lean_dec(v___x_2694_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2707_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 0, v_snd_2693_);
v___x_2703_ = v___x_2700_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_snd_2693_);
lean_ctor_set(v_reuseFailAlloc_2706_, 1, v_cache_2695_);
lean_ctor_set(v_reuseFailAlloc_2706_, 2, v_zetaDeltaFVarIds_2696_);
lean_ctor_set(v_reuseFailAlloc_2706_, 3, v_postponed_2697_);
lean_ctor_set(v_reuseFailAlloc_2706_, 4, v_diag_2698_);
v___x_2703_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2704_ = lean_st_ref_put(v___y_2685_, v___x_2703_);
v___x_2705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2705_, 0, v_fst_2692_);
return v___x_2705_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg___boxed(lean_object* v_e_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(v_e_2709_, v___y_2710_);
lean_dec(v___y_2710_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3(lean_object* v_e_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v___x_2721_; 
v___x_2721_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(v_e_2713_, v___y_2717_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___boxed(lean_object* v_e_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3(v_e_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___redArg(lean_object* v_lctx_2731_, lean_object* v_x_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v_keyedConfig_2740_; uint8_t v_trackZetaDelta_2741_; lean_object* v_zetaDeltaSet_2742_; lean_object* v_localInstances_2743_; lean_object* v_defEqCtx_x3f_2744_; lean_object* v_synthPendingDepth_2745_; lean_object* v_customCanUnfoldPredicate_x3f_2746_; uint8_t v_univApprox_2747_; uint8_t v_inTypeClassResolution_2748_; uint8_t v_cacheInferType_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v_keyedConfig_2740_ = lean_ctor_get(v___y_2735_, 0);
v_trackZetaDelta_2741_ = lean_ctor_get_uint8(v___y_2735_, sizeof(void*)*7);
v_zetaDeltaSet_2742_ = lean_ctor_get(v___y_2735_, 1);
v_localInstances_2743_ = lean_ctor_get(v___y_2735_, 3);
v_defEqCtx_x3f_2744_ = lean_ctor_get(v___y_2735_, 4);
v_synthPendingDepth_2745_ = lean_ctor_get(v___y_2735_, 5);
v_customCanUnfoldPredicate_x3f_2746_ = lean_ctor_get(v___y_2735_, 6);
v_univApprox_2747_ = lean_ctor_get_uint8(v___y_2735_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2748_ = lean_ctor_get_uint8(v___y_2735_, sizeof(void*)*7 + 2);
v_cacheInferType_2749_ = lean_ctor_get_uint8(v___y_2735_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_2746_);
lean_inc(v_synthPendingDepth_2745_);
lean_inc(v_defEqCtx_x3f_2744_);
lean_inc_ref(v_localInstances_2743_);
lean_inc(v_zetaDeltaSet_2742_);
lean_inc_ref(v_keyedConfig_2740_);
v___x_2750_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2750_, 0, v_keyedConfig_2740_);
lean_ctor_set(v___x_2750_, 1, v_zetaDeltaSet_2742_);
lean_ctor_set(v___x_2750_, 2, v_lctx_2731_);
lean_ctor_set(v___x_2750_, 3, v_localInstances_2743_);
lean_ctor_set(v___x_2750_, 4, v_defEqCtx_x3f_2744_);
lean_ctor_set(v___x_2750_, 5, v_synthPendingDepth_2745_);
lean_ctor_set(v___x_2750_, 6, v_customCanUnfoldPredicate_x3f_2746_);
lean_ctor_set_uint8(v___x_2750_, sizeof(void*)*7, v_trackZetaDelta_2741_);
lean_ctor_set_uint8(v___x_2750_, sizeof(void*)*7 + 1, v_univApprox_2747_);
lean_ctor_set_uint8(v___x_2750_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2748_);
lean_ctor_set_uint8(v___x_2750_, sizeof(void*)*7 + 3, v_cacheInferType_2749_);
lean_inc(v___y_2738_);
lean_inc_ref(v___y_2737_);
lean_inc(v___y_2736_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
v___x_2751_ = lean_apply_7(v_x_2732_, v___y_2733_, v___y_2734_, v___x_2750_, v___y_2736_, v___y_2737_, v___y_2738_, lean_box(0));
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2751_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2751_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
else
{
return v___x_2751_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___redArg___boxed(lean_object* v_lctx_2760_, lean_object* v_x_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___redArg(v_lctx_2760_, v_x_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4(lean_object* v_00_u03b1_2770_, lean_object* v_lctx_2771_, lean_object* v_x_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v___x_2780_; 
v___x_2780_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___redArg(v_lctx_2771_, v_x_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___boxed(lean_object* v_00_u03b1_2781_, lean_object* v_lctx_2782_, lean_object* v_x_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4(v_00_u03b1_2781_, v_lctx_2782_, v_x_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
return v_res_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg___lam__0(lean_object* v_k_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v_b_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
lean_object* v___x_2801_; 
lean_inc(v___y_2799_);
lean_inc_ref(v___y_2798_);
lean_inc(v___y_2797_);
lean_inc_ref(v___y_2796_);
lean_inc(v___y_2794_);
lean_inc_ref(v___y_2793_);
v___x_2801_ = lean_apply_8(v_k_2792_, v_b_2795_, v___y_2793_, v___y_2794_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, lean_box(0));
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg___lam__0___boxed(lean_object* v_k_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v_b_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg___lam__0(v_k_2802_, v___y_2803_, v___y_2804_, v_b_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg(lean_object* v_name_2812_, uint8_t v_bi_2813_, lean_object* v_type_2814_, lean_object* v_k_2815_, uint8_t v_kind_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
lean_object* v___f_2824_; lean_object* v___x_2825_; 
lean_inc(v___y_2818_);
lean_inc_ref(v___y_2817_);
v___f_2824_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2824_, 0, v_k_2815_);
lean_closure_set(v___f_2824_, 1, v___y_2817_);
lean_closure_set(v___f_2824_, 2, v___y_2818_);
v___x_2825_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2812_, v_bi_2813_, v_type_2814_, v___f_2824_, v_kind_2816_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
if (lean_obj_tag(v___x_2825_) == 0)
{
return v___x_2825_;
}
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2825_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2825_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2826_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg___boxed(lean_object* v_name_2834_, lean_object* v_bi_2835_, lean_object* v_type_2836_, lean_object* v_k_2837_, lean_object* v_kind_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
uint8_t v_bi_boxed_2846_; uint8_t v_kind_boxed_2847_; lean_object* v_res_2848_; 
v_bi_boxed_2846_ = lean_unbox(v_bi_2835_);
v_kind_boxed_2847_ = lean_unbox(v_kind_2838_);
v_res_2848_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg(v_name_2834_, v_bi_boxed_2846_, v_type_2836_, v_k_2837_, v_kind_boxed_2847_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5(lean_object* v_00_u03b1_2849_, lean_object* v_name_2850_, uint8_t v_bi_2851_, lean_object* v_type_2852_, lean_object* v_k_2853_, uint8_t v_kind_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
lean_object* v___x_2862_; 
v___x_2862_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg(v_name_2850_, v_bi_2851_, v_type_2852_, v_k_2853_, v_kind_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___boxed(lean_object* v_00_u03b1_2863_, lean_object* v_name_2864_, lean_object* v_bi_2865_, lean_object* v_type_2866_, lean_object* v_k_2867_, lean_object* v_kind_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
uint8_t v_bi_boxed_2876_; uint8_t v_kind_boxed_2877_; lean_object* v_res_2878_; 
v_bi_boxed_2876_ = lean_unbox(v_bi_2865_);
v_kind_boxed_2877_ = lean_unbox(v_kind_2868_);
v_res_2878_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5(v_00_u03b1_2863_, v_name_2864_, v_bi_boxed_2876_, v_type_2866_, v_k_2867_, v_kind_boxed_2877_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
return v_res_2878_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8(lean_object* v_opts_2879_, lean_object* v_opt_2880_){
_start:
{
lean_object* v_name_2881_; lean_object* v_defValue_2882_; lean_object* v_map_2883_; lean_object* v___x_2884_; 
v_name_2881_ = lean_ctor_get(v_opt_2880_, 0);
v_defValue_2882_ = lean_ctor_get(v_opt_2880_, 1);
v_map_2883_ = lean_ctor_get(v_opts_2879_, 0);
v___x_2884_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2883_, v_name_2881_);
if (lean_obj_tag(v___x_2884_) == 0)
{
uint8_t v___x_2885_; 
v___x_2885_ = lean_unbox(v_defValue_2882_);
return v___x_2885_;
}
else
{
lean_object* v_val_2886_; 
v_val_2886_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_val_2886_);
lean_dec_ref_known(v___x_2884_, 1);
if (lean_obj_tag(v_val_2886_) == 1)
{
uint8_t v_v_2887_; 
v_v_2887_ = lean_ctor_get_uint8(v_val_2886_, 0);
lean_dec_ref_known(v_val_2886_, 0);
return v_v_2887_;
}
else
{
uint8_t v___x_2888_; 
lean_dec(v_val_2886_);
v___x_2888_ = lean_unbox(v_defValue_2882_);
return v___x_2888_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8___boxed(lean_object* v_opts_2889_, lean_object* v_opt_2890_){
_start:
{
uint8_t v_res_2891_; lean_object* v_r_2892_; 
v_res_2891_ = l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8(v_opts_2889_, v_opt_2890_);
lean_dec_ref(v_opt_2890_);
lean_dec_ref(v_opts_2889_);
v_r_2892_ = lean_box(v_res_2891_);
return v_r_2892_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0(uint8_t v_suppressElabErrors_2900_, uint8_t v___y_2901_, lean_object* v_x_2902_){
_start:
{
if (lean_obj_tag(v_x_2902_) == 1)
{
lean_object* v_pre_2903_; 
v_pre_2903_ = lean_ctor_get(v_x_2902_, 0);
switch(lean_obj_tag(v_pre_2903_))
{
case 1:
{
lean_object* v_pre_2904_; 
v_pre_2904_ = lean_ctor_get(v_pre_2903_, 0);
switch(lean_obj_tag(v_pre_2904_))
{
case 0:
{
lean_object* v_str_2905_; lean_object* v_str_2906_; lean_object* v___x_2907_; uint8_t v___x_2908_; 
v_str_2905_ = lean_ctor_get(v_x_2902_, 1);
v_str_2906_ = lean_ctor_get(v_pre_2903_, 1);
v___x_2907_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__8));
v___x_2908_ = lean_string_dec_eq(v_str_2906_, v___x_2907_);
if (v___x_2908_ == 0)
{
lean_object* v___x_2909_; uint8_t v___x_2910_; 
v___x_2909_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__0));
v___x_2910_ = lean_string_dec_eq(v_str_2906_, v___x_2909_);
if (v___x_2910_ == 0)
{
return v___x_2910_;
}
else
{
lean_object* v___x_2911_; uint8_t v___x_2912_; 
v___x_2911_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__1));
v___x_2912_ = lean_string_dec_eq(v_str_2905_, v___x_2911_);
if (v___x_2912_ == 0)
{
return v___x_2912_;
}
else
{
return v_suppressElabErrors_2900_;
}
}
}
else
{
lean_object* v___x_2913_; uint8_t v___x_2914_; 
v___x_2913_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__2));
v___x_2914_ = lean_string_dec_eq(v_str_2905_, v___x_2913_);
if (v___x_2914_ == 0)
{
return v___x_2914_;
}
else
{
return v_suppressElabErrors_2900_;
}
}
}
case 1:
{
lean_object* v_pre_2915_; 
v_pre_2915_ = lean_ctor_get(v_pre_2904_, 0);
if (lean_obj_tag(v_pre_2915_) == 0)
{
lean_object* v_str_2916_; lean_object* v_str_2917_; lean_object* v_str_2918_; lean_object* v___x_2919_; uint8_t v___x_2920_; 
v_str_2916_ = lean_ctor_get(v_x_2902_, 1);
v_str_2917_ = lean_ctor_get(v_pre_2903_, 1);
v_str_2918_ = lean_ctor_get(v_pre_2904_, 1);
v___x_2919_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__3));
v___x_2920_ = lean_string_dec_eq(v_str_2918_, v___x_2919_);
if (v___x_2920_ == 0)
{
return v___x_2920_;
}
else
{
lean_object* v___x_2921_; uint8_t v___x_2922_; 
v___x_2921_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__4));
v___x_2922_ = lean_string_dec_eq(v_str_2917_, v___x_2921_);
if (v___x_2922_ == 0)
{
return v___x_2922_;
}
else
{
lean_object* v___x_2923_; uint8_t v___x_2924_; 
v___x_2923_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__5));
v___x_2924_ = lean_string_dec_eq(v_str_2916_, v___x_2923_);
if (v___x_2924_ == 0)
{
return v___x_2924_;
}
else
{
return v_suppressElabErrors_2900_;
}
}
}
}
else
{
return v___y_2901_;
}
}
default: 
{
return v___y_2901_;
}
}
}
case 0:
{
lean_object* v_str_2925_; lean_object* v___x_2926_; uint8_t v___x_2927_; 
v_str_2925_ = lean_ctor_get(v_x_2902_, 1);
v___x_2926_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__6));
v___x_2927_ = lean_string_dec_eq(v_str_2925_, v___x_2926_);
if (v___x_2927_ == 0)
{
return v___x_2927_;
}
else
{
return v_suppressElabErrors_2900_;
}
}
default: 
{
return v___y_2901_;
}
}
}
else
{
return v___y_2901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___boxed(lean_object* v_suppressElabErrors_2928_, lean_object* v___y_2929_, lean_object* v_x_2930_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2931_; uint8_t v___y_33763__boxed_2932_; uint8_t v_res_2933_; lean_object* v_r_2934_; 
v_suppressElabErrors_boxed_2931_ = lean_unbox(v_suppressElabErrors_2928_);
v___y_33763__boxed_2932_ = lean_unbox(v___y_2929_);
v_res_2933_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0(v_suppressElabErrors_boxed_2931_, v___y_33763__boxed_2932_, v_x_2930_);
lean_dec(v_x_2930_);
v_r_2934_ = lean_box(v_res_2933_);
return v_r_2934_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0(void){
_start:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2935_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__14, &l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__14_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgCompileAndEval___redArg___closed__14);
v___x_2936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2935_);
return v___x_2936_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__1(void){
_start:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2937_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2938_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0);
v___x_2939_ = lean_unsigned_to_nat(0u);
v___x_2940_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2939_);
lean_ctor_set(v___x_2940_, 1, v___x_2939_);
lean_ctor_set(v___x_2940_, 2, v___x_2939_);
lean_ctor_set(v___x_2940_, 3, v___x_2939_);
lean_ctor_set(v___x_2940_, 4, v___x_2938_);
lean_ctor_set(v___x_2940_, 5, v___x_2938_);
lean_ctor_set(v___x_2940_, 6, v___x_2938_);
lean_ctor_set(v___x_2940_, 7, v___x_2938_);
lean_ctor_set(v___x_2940_, 8, v___x_2938_);
lean_ctor_set(v___x_2940_, 9, v___x_2938_);
lean_ctor_set(v___x_2940_, 10, v___x_2938_);
lean_ctor_set(v___x_2940_, 11, v___x_2937_);
return v___x_2940_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__2(void){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2941_ = lean_unsigned_to_nat(32u);
v___x_2942_ = lean_mk_empty_array_with_capacity(v___x_2941_);
v___x_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2942_);
return v___x_2943_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__3(void){
_start:
{
size_t v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2944_ = ((size_t)5ULL);
v___x_2945_ = lean_unsigned_to_nat(0u);
v___x_2946_ = lean_unsigned_to_nat(32u);
v___x_2947_ = lean_mk_empty_array_with_capacity(v___x_2946_);
v___x_2948_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__2);
v___x_2949_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
lean_ctor_set(v___x_2949_, 1, v___x_2947_);
lean_ctor_set(v___x_2949_, 2, v___x_2945_);
lean_ctor_set(v___x_2949_, 3, v___x_2945_);
lean_ctor_set_usize(v___x_2949_, 4, v___x_2944_);
return v___x_2949_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__4(void){
_start:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2950_ = lean_box(1);
v___x_2951_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__3);
v___x_2952_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0);
v___x_2953_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2952_);
lean_ctor_set(v___x_2953_, 1, v___x_2951_);
lean_ctor_set(v___x_2953_, 2, v___x_2950_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19(lean_object* v_msgData_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v___x_2958_; lean_object* v_toCold_2959_; lean_object* v_env_2960_; lean_object* v_options_2961_; uint8_t v___x_2962_; lean_object* v_env_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2958_ = lean_st_ref_get(v___y_2956_);
v_toCold_2959_ = lean_ctor_get(v___y_2955_, 0);
v_env_2960_ = lean_ctor_get(v___x_2958_, 0);
lean_inc_ref(v_env_2960_);
lean_dec(v___x_2958_);
v_options_2961_ = lean_ctor_get(v_toCold_2959_, 2);
v___x_2962_ = 0;
v_env_2963_ = l_Lean_Environment_setRecordingDeps(v_env_2960_, v___x_2962_);
v___x_2964_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__1);
v___x_2965_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__4);
lean_inc_ref(v_options_2961_);
v___x_2966_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2966_, 0, v_env_2963_);
lean_ctor_set(v___x_2966_, 1, v___x_2964_);
lean_ctor_set(v___x_2966_, 2, v___x_2965_);
lean_ctor_set(v___x_2966_, 3, v_options_2961_);
v___x_2967_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2966_);
lean_ctor_set(v___x_2967_, 1, v_msgData_2954_);
v___x_2968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2967_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___boxed(lean_object* v_msgData_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19(v_msgData_2969_, v___y_2970_, v___y_2971_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13(lean_object* v_ref_2975_, lean_object* v_msgData_2976_, uint8_t v_severity_2977_, uint8_t v_isSilent_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v___y_2983_; lean_object* v___y_2984_; uint8_t v___y_2985_; lean_object* v___y_2986_; uint8_t v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v_toCold_2990_; lean_object* v___y_2991_; lean_object* v___y_3020_; lean_object* v___y_3021_; uint8_t v___y_3022_; uint8_t v___y_3023_; lean_object* v___y_3024_; uint8_t v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; uint8_t v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; uint8_t v___y_3051_; uint8_t v___y_3052_; lean_object* v___y_3053_; uint8_t v___y_3057_; uint8_t v___y_3058_; uint8_t v___y_3059_; uint8_t v___x_3070_; uint8_t v___y_3072_; uint8_t v___y_3073_; uint8_t v___y_3074_; uint8_t v___y_3076_; uint8_t v___x_3084_; 
v___x_3070_ = 2;
v___x_3084_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2977_, v___x_3070_);
if (v___x_3084_ == 0)
{
v___y_3076_ = v___x_3084_;
goto v___jp_3075_;
}
else
{
uint8_t v___x_3085_; 
lean_inc_ref(v_msgData_2976_);
v___x_3085_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2976_);
v___y_3076_ = v___x_3085_;
goto v___jp_3075_;
}
v___jp_2982_:
{
lean_object* v_currNamespace_2992_; lean_object* v_openDecls_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v_env_2998_; lean_object* v_nextMacroScope_2999_; lean_object* v_ngen_3000_; lean_object* v_auxDeclNGen_3001_; lean_object* v_traceState_3002_; lean_object* v_cache_3003_; lean_object* v_recordedDeps_3004_; lean_object* v_messages_3005_; lean_object* v_infoState_3006_; lean_object* v_snapshotTasks_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3018_; 
v_currNamespace_2992_ = lean_ctor_get(v_toCold_2990_, 4);
v_openDecls_2993_ = lean_ctor_get(v_toCold_2990_, 5);
lean_inc(v_openDecls_2993_);
lean_inc(v_currNamespace_2992_);
v___x_2994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2994_, 0, v_currNamespace_2992_);
lean_ctor_set(v___x_2994_, 1, v_openDecls_2993_);
v___x_2995_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2994_);
lean_ctor_set(v___x_2995_, 1, v___y_2989_);
lean_inc_ref(v___y_2983_);
lean_inc_ref(v___y_2984_);
v___x_2996_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2996_, 0, v___y_2984_);
lean_ctor_set(v___x_2996_, 1, v___y_2988_);
lean_ctor_set(v___x_2996_, 2, v___y_2986_);
lean_ctor_set(v___x_2996_, 3, v___y_2983_);
lean_ctor_set(v___x_2996_, 4, v___x_2995_);
lean_ctor_set_uint8(v___x_2996_, sizeof(void*)*5, v___y_2987_);
lean_ctor_set_uint8(v___x_2996_, sizeof(void*)*5 + 1, v___y_2985_);
lean_ctor_set_uint8(v___x_2996_, sizeof(void*)*5 + 2, v_isSilent_2978_);
v___x_2997_ = lean_st_ref_take(v___y_2991_);
v_env_2998_ = lean_ctor_get(v___x_2997_, 0);
v_nextMacroScope_2999_ = lean_ctor_get(v___x_2997_, 1);
v_ngen_3000_ = lean_ctor_get(v___x_2997_, 2);
v_auxDeclNGen_3001_ = lean_ctor_get(v___x_2997_, 3);
v_traceState_3002_ = lean_ctor_get(v___x_2997_, 4);
v_cache_3003_ = lean_ctor_get(v___x_2997_, 5);
v_recordedDeps_3004_ = lean_ctor_get(v___x_2997_, 6);
v_messages_3005_ = lean_ctor_get(v___x_2997_, 7);
v_infoState_3006_ = lean_ctor_get(v___x_2997_, 8);
v_snapshotTasks_3007_ = lean_ctor_get(v___x_2997_, 9);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3009_ = v___x_2997_;
v_isShared_3010_ = v_isSharedCheck_3018_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_snapshotTasks_3007_);
lean_inc(v_infoState_3006_);
lean_inc(v_messages_3005_);
lean_inc(v_recordedDeps_3004_);
lean_inc(v_cache_3003_);
lean_inc(v_traceState_3002_);
lean_inc(v_auxDeclNGen_3001_);
lean_inc(v_ngen_3000_);
lean_inc(v_nextMacroScope_2999_);
lean_inc(v_env_2998_);
lean_dec(v___x_2997_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3018_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3014_; 
v___x_3011_ = lean_box(0);
v___x_3012_ = l_Lean_MessageLog_add(v___x_2996_, v_messages_3005_);
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 7, v___x_3012_);
v___x_3014_ = v___x_3009_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_env_2998_);
lean_ctor_set(v_reuseFailAlloc_3017_, 1, v_nextMacroScope_2999_);
lean_ctor_set(v_reuseFailAlloc_3017_, 2, v_ngen_3000_);
lean_ctor_set(v_reuseFailAlloc_3017_, 3, v_auxDeclNGen_3001_);
lean_ctor_set(v_reuseFailAlloc_3017_, 4, v_traceState_3002_);
lean_ctor_set(v_reuseFailAlloc_3017_, 5, v_cache_3003_);
lean_ctor_set(v_reuseFailAlloc_3017_, 6, v_recordedDeps_3004_);
lean_ctor_set(v_reuseFailAlloc_3017_, 7, v___x_3012_);
lean_ctor_set(v_reuseFailAlloc_3017_, 8, v_infoState_3006_);
lean_ctor_set(v_reuseFailAlloc_3017_, 9, v_snapshotTasks_3007_);
v___x_3014_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3015_ = lean_st_ref_put(v___y_2991_, v___x_3014_);
v___x_3016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3011_);
return v___x_3016_;
}
}
}
v___jp_3019_:
{
lean_object* v_fileName_3028_; lean_object* v_fileMap_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3045_; 
v_fileName_3028_ = lean_ctor_get(v___y_3024_, 0);
v_fileMap_3029_ = lean_ctor_get(v___y_3024_, 1);
v___x_3030_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2976_);
v___x_3031_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19(v___x_3030_, v___y_2979_, v___y_2980_);
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3034_ = v___x_3031_;
v_isShared_3035_ = v_isSharedCheck_3045_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_3031_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3045_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
lean_inc_ref_n(v_fileMap_3029_, 2);
v___x_3036_ = l_Lean_FileMap_toPosition(v_fileMap_3029_, v___y_3026_);
lean_dec(v___y_3026_);
v___x_3037_ = l_Lean_FileMap_toPosition(v_fileMap_3029_, v___y_3027_);
lean_dec(v___y_3027_);
v___x_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3037_);
v___x_3039_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___closed__0));
if (v___y_3022_ == 0)
{
lean_del_object(v___x_3034_);
lean_dec_ref(v___y_3020_);
v___y_2983_ = v___x_3039_;
v___y_2984_ = v_fileName_3028_;
v___y_2985_ = v___y_3023_;
v___y_2986_ = v___x_3038_;
v___y_2987_ = v___y_3025_;
v___y_2988_ = v___x_3036_;
v___y_2989_ = v_a_3032_;
v_toCold_2990_ = v___y_3021_;
v___y_2991_ = v___y_2980_;
goto v___jp_2982_;
}
else
{
uint8_t v___x_3040_; 
lean_inc(v_a_3032_);
v___x_3040_ = l_Lean_MessageData_hasTag(v___y_3020_, v_a_3032_);
if (v___x_3040_ == 0)
{
lean_object* v___x_3041_; lean_object* v___x_3043_; 
lean_dec_ref_known(v___x_3038_, 1);
lean_dec_ref(v___x_3036_);
lean_dec(v_a_3032_);
v___x_3041_ = lean_box(0);
if (v_isShared_3035_ == 0)
{
lean_ctor_set(v___x_3034_, 0, v___x_3041_);
v___x_3043_ = v___x_3034_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v___x_3041_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
else
{
lean_del_object(v___x_3034_);
v___y_2983_ = v___x_3039_;
v___y_2984_ = v_fileName_3028_;
v___y_2985_ = v___y_3023_;
v___y_2986_ = v___x_3038_;
v___y_2987_ = v___y_3025_;
v___y_2988_ = v___x_3036_;
v___y_2989_ = v_a_3032_;
v_toCold_2990_ = v___y_3021_;
v___y_2991_ = v___y_2980_;
goto v___jp_2982_;
}
}
}
}
v___jp_3046_:
{
lean_object* v___x_3054_; 
v___x_3054_ = l_Lean_Syntax_getTailPos_x3f(v___y_3050_, v___y_3052_);
lean_dec(v___y_3050_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_inc(v___y_3053_);
v___y_3020_ = v___y_3048_;
v___y_3021_ = v___y_3049_;
v___y_3022_ = v___y_3047_;
v___y_3023_ = v___y_3051_;
v___y_3024_ = v___y_3049_;
v___y_3025_ = v___y_3052_;
v___y_3026_ = v___y_3053_;
v___y_3027_ = v___y_3053_;
goto v___jp_3019_;
}
else
{
lean_object* v_val_3055_; 
v_val_3055_ = lean_ctor_get(v___x_3054_, 0);
lean_inc(v_val_3055_);
lean_dec_ref_known(v___x_3054_, 1);
v___y_3020_ = v___y_3048_;
v___y_3021_ = v___y_3049_;
v___y_3022_ = v___y_3047_;
v___y_3023_ = v___y_3051_;
v___y_3024_ = v___y_3049_;
v___y_3025_ = v___y_3052_;
v___y_3026_ = v___y_3053_;
v___y_3027_ = v_val_3055_;
goto v___jp_3019_;
}
}
v___jp_3056_:
{
lean_object* v_toCold_3060_; lean_object* v_ref_3061_; uint8_t v_suppressElabErrors_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___f_3065_; lean_object* v_ref_3066_; lean_object* v___x_3067_; 
v_toCold_3060_ = lean_ctor_get(v___y_2979_, 0);
v_ref_3061_ = lean_ctor_get(v___y_2979_, 2);
v_suppressElabErrors_3062_ = lean_ctor_get_uint8(v___y_2979_, sizeof(void*)*3 + 2);
v___x_3063_ = lean_box(v_suppressElabErrors_3062_);
v___x_3064_ = lean_box(v___y_3057_);
v___f_3065_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3065_, 0, v___x_3063_);
lean_closure_set(v___f_3065_, 1, v___x_3064_);
v_ref_3066_ = l_Lean_replaceRef(v_ref_2975_, v_ref_3061_);
v___x_3067_ = l_Lean_Syntax_getPos_x3f(v_ref_3066_, v___y_3058_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v___x_3068_; 
v___x_3068_ = lean_unsigned_to_nat(0u);
v___y_3047_ = v_suppressElabErrors_3062_;
v___y_3048_ = v___f_3065_;
v___y_3049_ = v_toCold_3060_;
v___y_3050_ = v_ref_3066_;
v___y_3051_ = v___y_3059_;
v___y_3052_ = v___y_3058_;
v___y_3053_ = v___x_3068_;
goto v___jp_3046_;
}
else
{
lean_object* v_val_3069_; 
v_val_3069_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_val_3069_);
lean_dec_ref_known(v___x_3067_, 1);
v___y_3047_ = v_suppressElabErrors_3062_;
v___y_3048_ = v___f_3065_;
v___y_3049_ = v_toCold_3060_;
v___y_3050_ = v_ref_3066_;
v___y_3051_ = v___y_3059_;
v___y_3052_ = v___y_3058_;
v___y_3053_ = v_val_3069_;
goto v___jp_3046_;
}
}
v___jp_3071_:
{
if (v___y_3074_ == 0)
{
v___y_3057_ = v___y_3072_;
v___y_3058_ = v___y_3073_;
v___y_3059_ = v_severity_2977_;
goto v___jp_3056_;
}
else
{
v___y_3057_ = v___y_3072_;
v___y_3058_ = v___y_3073_;
v___y_3059_ = v___x_3070_;
goto v___jp_3056_;
}
}
v___jp_3075_:
{
if (v___y_3076_ == 0)
{
uint8_t v___x_3077_; uint8_t v___x_3078_; 
v___x_3077_ = 1;
v___x_3078_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2977_, v___x_3077_);
if (v___x_3078_ == 0)
{
v___y_3072_ = v___y_3076_;
v___y_3073_ = v___y_3076_;
v___y_3074_ = v___x_3078_;
goto v___jp_3071_;
}
else
{
lean_object* v___x_3079_; lean_object* v___x_3080_; uint8_t v___x_3081_; 
v___x_3079_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2979_);
v___x_3080_ = l_Lean_warningAsError;
v___x_3081_ = l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8(v___x_3079_, v___x_3080_);
lean_dec_ref(v___x_3079_);
v___y_3072_ = v___y_3076_;
v___y_3073_ = v___y_3076_;
v___y_3074_ = v___x_3081_;
goto v___jp_3071_;
}
}
else
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
lean_dec_ref(v_msgData_2976_);
v___x_3082_ = lean_box(0);
v___x_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3082_);
return v___x_3083_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___boxed(lean_object* v_ref_3086_, lean_object* v_msgData_3087_, lean_object* v_severity_3088_, lean_object* v_isSilent_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_){
_start:
{
uint8_t v_severity_boxed_3093_; uint8_t v_isSilent_boxed_3094_; lean_object* v_res_3095_; 
v_severity_boxed_3093_ = lean_unbox(v_severity_3088_);
v_isSilent_boxed_3094_ = lean_unbox(v_isSilent_3089_);
v_res_3095_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13(v_ref_3086_, v_msgData_3087_, v_severity_boxed_3093_, v_isSilent_boxed_3094_, v___y_3090_, v___y_3091_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec(v_ref_3086_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9(lean_object* v_ref_3096_, lean_object* v_msgData_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_){
_start:
{
uint8_t v___x_3101_; uint8_t v___x_3102_; lean_object* v___x_3103_; 
v___x_3101_ = 0;
v___x_3102_ = 0;
v___x_3103_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13(v_ref_3096_, v_msgData_3097_, v___x_3101_, v___x_3102_, v___y_3098_, v___y_3099_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9___boxed(lean_object* v_ref_3104_, lean_object* v_msgData_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
lean_object* v_res_3109_; 
v_res_3109_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9(v_ref_3104_, v_msgData_3105_, v___y_3106_, v___y_3107_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v_ref_3104_);
return v_res_3109_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3111_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__0));
v___x_3112_ = l_Lean_stringToMessageData(v___x_3111_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0(lean_object* v___x_3113_, lean_object* v___x_3114_, lean_object* v_ref_3115_, lean_object* v_x_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_){
_start:
{
lean_object* v_ref_3120_; lean_object* v___x_3121_; 
v_ref_3120_ = lean_ctor_get(v___y_3117_, 2);
v___x_3121_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_idbgServer(v___x_3113_, v___x_3114_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3135_; 
v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3124_ = v___x_3121_;
v_isShared_3125_ = v_isSharedCheck_3135_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3121_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3135_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
if (lean_obj_tag(v_a_3122_) == 1)
{
lean_object* v_val_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
lean_del_object(v___x_3124_);
v_val_3126_ = lean_ctor_get(v_a_3122_, 0);
lean_inc(v_val_3126_);
lean_dec_ref_known(v_a_3122_, 1);
v___x_3127_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__1, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__1_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__1);
v___x_3128_ = l_Lean_stringToMessageData(v_val_3126_);
v___x_3129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3127_);
lean_ctor_set(v___x_3129_, 1, v___x_3128_);
v___x_3130_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9(v_ref_3115_, v___x_3129_, v___y_3117_, v___y_3118_);
return v___x_3130_;
}
else
{
lean_object* v___x_3131_; lean_object* v___x_3133_; 
lean_dec(v_a_3122_);
v___x_3131_ = lean_box(0);
if (v_isShared_3125_ == 0)
{
lean_ctor_set(v___x_3124_, 0, v___x_3131_);
v___x_3133_ = v___x_3124_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3131_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3147_; 
v_a_3136_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3138_ = v___x_3121_;
v_isShared_3139_ = v_isSharedCheck_3147_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3121_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3147_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3145_; 
v___x_3140_ = lean_io_error_to_string(v_a_3136_);
v___x_3141_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3140_);
v___x_3142_ = l_Lean_MessageData_ofFormat(v___x_3141_);
lean_inc(v_ref_3120_);
v___x_3143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3143_, 0, v_ref_3120_);
lean_ctor_set(v___x_3143_, 1, v___x_3142_);
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 0, v___x_3143_);
v___x_3145_ = v___x_3138_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v___x_3143_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___boxed(lean_object* v___x_3148_, lean_object* v___x_3149_, lean_object* v_ref_3150_, lean_object* v_x_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0(v___x_3148_, v___x_3149_, v_ref_3150_, v_x_3151_, v___y_3152_, v___y_3153_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v_ref_3150_);
lean_dec_ref(v___x_3148_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__1(lean_object* v___x_3156_, lean_object* v___x_3157_, uint8_t v___x_3158_, uint8_t v___x_3159_, uint8_t v___x_3160_, lean_object* v_fVar_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_){
_start:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
lean_inc_ref(v_fVar_3161_);
v___x_3169_ = l_Lean_mkAppN(v_fVar_3161_, v___x_3156_);
v___x_3170_ = lean_array_push(v___x_3157_, v_fVar_3161_);
v___x_3171_ = l_Lean_Meta_mkLambdaFVars(v___x_3170_, v___x_3169_, v___x_3158_, v___x_3159_, v___x_3158_, v___x_3159_, v___x_3160_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
lean_dec_ref(v___x_3170_);
return v___x_3171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__1___boxed(lean_object* v___x_3172_, lean_object* v___x_3173_, lean_object* v___x_3174_, lean_object* v___x_3175_, lean_object* v___x_3176_, lean_object* v_fVar_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
uint8_t v___x_34215__boxed_3185_; uint8_t v___x_34216__boxed_3186_; uint8_t v___x_34217__boxed_3187_; lean_object* v_res_3188_; 
v___x_34215__boxed_3185_ = lean_unbox(v___x_3174_);
v___x_34216__boxed_3186_ = lean_unbox(v___x_3175_);
v___x_34217__boxed_3187_ = lean_unbox(v___x_3176_);
v_res_3188_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__1(v___x_3172_, v___x_3173_, v___x_34215__boxed_3185_, v___x_34216__boxed_3186_, v___x_34217__boxed_3187_, v_fVar_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec_ref(v___x_3172_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__2(lean_object* v___x_3189_, lean_object* v_a_3190_, uint8_t v___x_3191_, uint8_t v___x_3192_, uint8_t v___x_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_){
_start:
{
lean_object* v___x_3201_; 
v___x_3201_ = l_Lean_Meta_mkLambdaFVars(v___x_3189_, v_a_3190_, v___x_3191_, v___x_3192_, v___x_3191_, v___x_3192_, v___x_3193_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_object* v_a_3202_; lean_object* v___x_3203_; 
v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
lean_inc_n(v_a_3202_, 2);
lean_dec_ref_known(v___x_3201_, 1);
lean_inc(v___y_3197_);
v___x_3203_ = lean_infer_type(v_a_3202_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3204_; lean_object* v___x_3205_; lean_object* v_a_3206_; lean_object* v___x_3207_; lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3216_; 
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
lean_inc(v_a_3204_);
lean_dec_ref_known(v___x_3203_, 1);
v___x_3205_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(v_a_3202_, v___y_3197_);
v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
lean_inc(v_a_3206_);
lean_dec_ref(v___x_3205_);
v___x_3207_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(v_a_3204_, v___y_3197_);
lean_dec(v___y_3197_);
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3210_ = v___x_3207_;
v_isShared_3211_ = v_isSharedCheck_3216_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3207_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3216_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3212_; lean_object* v___x_3214_; 
v___x_3212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3212_, 0, v_a_3206_);
lean_ctor_set(v___x_3212_, 1, v_a_3208_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 0, v___x_3212_);
v___x_3214_ = v___x_3210_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3212_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
else
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3224_; 
lean_dec(v_a_3202_);
lean_dec(v___y_3197_);
v_a_3217_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3219_ = v___x_3203_;
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3203_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3222_; 
if (v_isShared_3220_ == 0)
{
v___x_3222_ = v___x_3219_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_a_3217_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
}
else
{
lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3232_; 
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
v_a_3225_ = lean_ctor_get(v___x_3201_, 0);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3227_ = v___x_3201_;
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___x_3201_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3230_; 
if (v_isShared_3228_ == 0)
{
v___x_3230_ = v___x_3227_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_a_3225_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
return v___x_3230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__2___boxed(lean_object* v___x_3233_, lean_object* v_a_3234_, lean_object* v___x_3235_, lean_object* v___x_3236_, lean_object* v___x_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_){
_start:
{
uint8_t v___x_34257__boxed_3245_; uint8_t v___x_34258__boxed_3246_; uint8_t v___x_34259__boxed_3247_; lean_object* v_res_3248_; 
v___x_34257__boxed_3245_ = lean_unbox(v___x_3235_);
v___x_34258__boxed_3246_ = lean_unbox(v___x_3236_);
v___x_34259__boxed_3247_ = lean_unbox(v___x_3237_);
v_res_3248_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__2(v___x_3233_, v_a_3234_, v___x_34257__boxed_3245_, v___x_34258__boxed_3246_, v___x_34259__boxed_3247_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec_ref(v___x_3233_);
return v_res_3248_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4(void){
_start:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3257_ = lean_box(0);
v___x_3258_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__3));
v___x_3259_ = l_Lean_Expr_const___override(v___x_3258_, v___x_3257_);
return v___x_3259_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__7(void){
_start:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3264_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__0));
v___x_3265_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__6));
v___x_3266_ = l_Lean_Expr_const___override(v___x_3265_, v___x_3264_);
return v___x_3266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10(lean_object* v_as_3267_, size_t v_i_3268_, size_t v_stop_3269_, lean_object* v_b_3270_){
_start:
{
uint8_t v___x_3271_; 
v___x_3271_ = lean_usize_dec_eq(v_i_3268_, v_stop_3269_);
if (v___x_3271_ == 0)
{
lean_object* v___x_3272_; size_t v___x_3273_; size_t v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3272_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4);
v___x_3273_ = ((size_t)1ULL);
v___x_3274_ = lean_usize_sub(v_i_3268_, v___x_3273_);
v___x_3275_ = lean_array_uget_borrowed(v_as_3267_, v___x_3274_);
v___x_3276_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__7);
lean_inc(v___x_3275_);
v___x_3277_ = l_Lean_mkApp3(v___x_3276_, v___x_3272_, v___x_3275_, v_b_3270_);
v_i_3268_ = v___x_3274_;
v_b_3270_ = v___x_3277_;
goto _start;
}
else
{
return v_b_3270_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___boxed(lean_object* v_as_3279_, lean_object* v_i_3280_, lean_object* v_stop_3281_, lean_object* v_b_3282_){
_start:
{
size_t v_i_boxed_3283_; size_t v_stop_boxed_3284_; lean_object* v_res_3285_; 
v_i_boxed_3283_ = lean_unbox_usize(v_i_3280_);
lean_dec(v_i_3280_);
v_stop_boxed_3284_ = lean_unbox_usize(v_stop_3281_);
lean_dec(v_stop_3281_);
v_res_3285_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10(v_as_3279_, v_i_boxed_3283_, v_stop_boxed_3284_, v_b_3282_);
lean_dec_ref(v_as_3279_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7(lean_object* v_init_3286_, lean_object* v_l_3287_){
_start:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; uint8_t v___x_3291_; 
v___x_3288_ = lean_array_mk(v_l_3287_);
v___x_3289_ = lean_array_get_size(v___x_3288_);
v___x_3290_ = lean_unsigned_to_nat(0u);
v___x_3291_ = lean_nat_dec_lt(v___x_3290_, v___x_3289_);
if (v___x_3291_ == 0)
{
lean_dec_ref(v___x_3288_);
return v_init_3286_;
}
else
{
size_t v___x_3292_; size_t v___x_3293_; lean_object* v___x_3294_; 
v___x_3292_ = lean_usize_of_nat(v___x_3289_);
v___x_3293_ = ((size_t)0ULL);
v___x_3294_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10(v___x_3288_, v___x_3292_, v___x_3293_, v_init_3286_);
lean_dec_ref(v___x_3288_);
return v___x_3294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___redArg(lean_object* v_as_3295_, size_t v_sz_3296_, size_t v_i_3297_, lean_object* v_b_3298_){
_start:
{
uint8_t v___x_3300_; 
v___x_3300_ = lean_usize_dec_lt(v_i_3297_, v_sz_3296_);
if (v___x_3300_ == 0)
{
lean_object* v___x_3301_; 
v___x_3301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3301_, 0, v_b_3298_);
return v___x_3301_;
}
else
{
lean_object* v_snd_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3319_; 
v_snd_3302_ = lean_ctor_get(v_b_3298_, 1);
v_isSharedCheck_3319_ = !lean_is_exclusive(v_b_3298_);
if (v_isSharedCheck_3319_ == 0)
{
lean_object* v_unused_3320_; 
v_unused_3320_ = lean_ctor_get(v_b_3298_, 0);
lean_dec(v_unused_3320_);
v___x_3304_ = v_b_3298_;
v_isShared_3305_ = v_isSharedCheck_3319_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_snd_3302_);
lean_dec(v_b_3298_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3319_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3306_; lean_object* v_a_3308_; lean_object* v_a_3315_; 
v___x_3306_ = lean_box(0);
v_a_3315_ = lean_array_uget_borrowed(v_as_3295_, v_i_3297_);
if (lean_obj_tag(v_a_3315_) == 0)
{
v_a_3308_ = v_snd_3302_;
goto v___jp_3307_;
}
else
{
lean_object* v_val_3316_; uint8_t v___x_3317_; 
v_val_3316_ = lean_ctor_get(v_a_3315_, 0);
v___x_3317_ = l_Lean_LocalDecl_isAuxDecl(v_val_3316_);
if (v___x_3317_ == 0)
{
lean_object* v___x_3318_; 
lean_inc(v_val_3316_);
v___x_3318_ = lean_array_push(v_snd_3302_, v_val_3316_);
v_a_3308_ = v___x_3318_;
goto v___jp_3307_;
}
else
{
v_a_3308_ = v_snd_3302_;
goto v___jp_3307_;
}
}
v___jp_3307_:
{
lean_object* v___x_3310_; 
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 1, v_a_3308_);
lean_ctor_set(v___x_3304_, 0, v___x_3306_);
v___x_3310_ = v___x_3304_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3306_);
lean_ctor_set(v_reuseFailAlloc_3314_, 1, v_a_3308_);
v___x_3310_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
size_t v___x_3311_; size_t v___x_3312_; 
v___x_3311_ = ((size_t)1ULL);
v___x_3312_ = lean_usize_add(v_i_3297_, v___x_3311_);
v_i_3297_ = v___x_3312_;
v_b_3298_ = v___x_3310_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___redArg___boxed(lean_object* v_as_3321_, lean_object* v_sz_3322_, lean_object* v_i_3323_, lean_object* v_b_3324_, lean_object* v___y_3325_){
_start:
{
size_t v_sz_boxed_3326_; size_t v_i_boxed_3327_; lean_object* v_res_3328_; 
v_sz_boxed_3326_ = lean_unbox_usize(v_sz_3322_);
lean_dec(v_sz_3322_);
v_i_boxed_3327_ = lean_unbox_usize(v_i_3323_);
lean_dec(v_i_3323_);
v_res_3328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___redArg(v_as_3321_, v_sz_boxed_3326_, v_i_boxed_3327_, v_b_3324_);
lean_dec_ref(v_as_3321_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1(lean_object* v_as_3329_, size_t v_sz_3330_, size_t v_i_3331_, lean_object* v_b_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
uint8_t v___x_3340_; 
v___x_3340_ = lean_usize_dec_lt(v_i_3331_, v_sz_3330_);
if (v___x_3340_ == 0)
{
lean_object* v___x_3341_; 
v___x_3341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3341_, 0, v_b_3332_);
return v___x_3341_;
}
else
{
lean_object* v_snd_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3359_; 
v_snd_3342_ = lean_ctor_get(v_b_3332_, 1);
v_isSharedCheck_3359_ = !lean_is_exclusive(v_b_3332_);
if (v_isSharedCheck_3359_ == 0)
{
lean_object* v_unused_3360_; 
v_unused_3360_ = lean_ctor_get(v_b_3332_, 0);
lean_dec(v_unused_3360_);
v___x_3344_ = v_b_3332_;
v_isShared_3345_ = v_isSharedCheck_3359_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_snd_3342_);
lean_dec(v_b_3332_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3359_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3346_; lean_object* v_a_3348_; lean_object* v_a_3355_; 
v___x_3346_ = lean_box(0);
v_a_3355_ = lean_array_uget_borrowed(v_as_3329_, v_i_3331_);
if (lean_obj_tag(v_a_3355_) == 0)
{
v_a_3348_ = v_snd_3342_;
goto v___jp_3347_;
}
else
{
lean_object* v_val_3356_; uint8_t v___x_3357_; 
v_val_3356_ = lean_ctor_get(v_a_3355_, 0);
v___x_3357_ = l_Lean_LocalDecl_isAuxDecl(v_val_3356_);
if (v___x_3357_ == 0)
{
lean_object* v___x_3358_; 
lean_inc(v_val_3356_);
v___x_3358_ = lean_array_push(v_snd_3342_, v_val_3356_);
v_a_3348_ = v___x_3358_;
goto v___jp_3347_;
}
else
{
v_a_3348_ = v_snd_3342_;
goto v___jp_3347_;
}
}
v___jp_3347_:
{
lean_object* v___x_3350_; 
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 1, v_a_3348_);
lean_ctor_set(v___x_3344_, 0, v___x_3346_);
v___x_3350_ = v___x_3344_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3346_);
lean_ctor_set(v_reuseFailAlloc_3354_, 1, v_a_3348_);
v___x_3350_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
size_t v___x_3351_; size_t v___x_3352_; lean_object* v___x_3353_; 
v___x_3351_ = ((size_t)1ULL);
v___x_3352_ = lean_usize_add(v_i_3331_, v___x_3351_);
v___x_3353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___redArg(v_as_3329_, v_sz_3330_, v___x_3352_, v___x_3350_);
return v___x_3353_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1___boxed(lean_object* v_as_3361_, lean_object* v_sz_3362_, lean_object* v_i_3363_, lean_object* v_b_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_){
_start:
{
size_t v_sz_boxed_3372_; size_t v_i_boxed_3373_; lean_object* v_res_3374_; 
v_sz_boxed_3372_ = lean_unbox_usize(v_sz_3362_);
lean_dec(v_sz_3362_);
v_i_boxed_3373_ = lean_unbox_usize(v_i_3363_);
lean_dec(v_i_3363_);
v_res_3374_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1(v_as_3361_, v_sz_boxed_3372_, v_i_boxed_3373_, v_b_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec(v___y_3368_);
lean_dec_ref(v___y_3367_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
lean_dec_ref(v_as_3361_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___redArg(lean_object* v_as_3375_, size_t v_sz_3376_, size_t v_i_3377_, lean_object* v_b_3378_){
_start:
{
uint8_t v___x_3380_; 
v___x_3380_ = lean_usize_dec_lt(v_i_3377_, v_sz_3376_);
if (v___x_3380_ == 0)
{
lean_object* v___x_3381_; 
v___x_3381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3381_, 0, v_b_3378_);
return v___x_3381_;
}
else
{
lean_object* v_snd_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3399_; 
v_snd_3382_ = lean_ctor_get(v_b_3378_, 1);
v_isSharedCheck_3399_ = !lean_is_exclusive(v_b_3378_);
if (v_isSharedCheck_3399_ == 0)
{
lean_object* v_unused_3400_; 
v_unused_3400_ = lean_ctor_get(v_b_3378_, 0);
lean_dec(v_unused_3400_);
v___x_3384_ = v_b_3378_;
v_isShared_3385_ = v_isSharedCheck_3399_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_snd_3382_);
lean_dec(v_b_3378_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3399_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3386_; lean_object* v_a_3388_; lean_object* v_a_3395_; 
v___x_3386_ = lean_box(0);
v_a_3395_ = lean_array_uget_borrowed(v_as_3375_, v_i_3377_);
if (lean_obj_tag(v_a_3395_) == 0)
{
v_a_3388_ = v_snd_3382_;
goto v___jp_3387_;
}
else
{
lean_object* v_val_3396_; uint8_t v___x_3397_; 
v_val_3396_ = lean_ctor_get(v_a_3395_, 0);
v___x_3397_ = l_Lean_LocalDecl_isAuxDecl(v_val_3396_);
if (v___x_3397_ == 0)
{
lean_object* v___x_3398_; 
lean_inc(v_val_3396_);
v___x_3398_ = lean_array_push(v_snd_3382_, v_val_3396_);
v_a_3388_ = v___x_3398_;
goto v___jp_3387_;
}
else
{
v_a_3388_ = v_snd_3382_;
goto v___jp_3387_;
}
}
v___jp_3387_:
{
lean_object* v___x_3390_; 
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 1, v_a_3388_);
lean_ctor_set(v___x_3384_, 0, v___x_3386_);
v___x_3390_ = v___x_3384_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v___x_3386_);
lean_ctor_set(v_reuseFailAlloc_3394_, 1, v_a_3388_);
v___x_3390_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
size_t v___x_3391_; size_t v___x_3392_; 
v___x_3391_ = ((size_t)1ULL);
v___x_3392_ = lean_usize_add(v_i_3377_, v___x_3391_);
v_i_3377_ = v___x_3392_;
v_b_3378_ = v___x_3390_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___redArg___boxed(lean_object* v_as_3401_, lean_object* v_sz_3402_, lean_object* v_i_3403_, lean_object* v_b_3404_, lean_object* v___y_3405_){
_start:
{
size_t v_sz_boxed_3406_; size_t v_i_boxed_3407_; lean_object* v_res_3408_; 
v_sz_boxed_3406_ = lean_unbox_usize(v_sz_3402_);
lean_dec(v_sz_3402_);
v_i_boxed_3407_ = lean_unbox_usize(v_i_3403_);
lean_dec(v_i_3403_);
v_res_3408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___redArg(v_as_3401_, v_sz_boxed_3406_, v_i_boxed_3407_, v_b_3404_);
lean_dec_ref(v_as_3401_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6(lean_object* v_as_3409_, size_t v_sz_3410_, size_t v_i_3411_, lean_object* v_b_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
uint8_t v___x_3420_; 
v___x_3420_ = lean_usize_dec_lt(v_i_3411_, v_sz_3410_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; 
v___x_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3421_, 0, v_b_3412_);
return v___x_3421_;
}
else
{
lean_object* v_snd_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3439_; 
v_snd_3422_ = lean_ctor_get(v_b_3412_, 1);
v_isSharedCheck_3439_ = !lean_is_exclusive(v_b_3412_);
if (v_isSharedCheck_3439_ == 0)
{
lean_object* v_unused_3440_; 
v_unused_3440_ = lean_ctor_get(v_b_3412_, 0);
lean_dec(v_unused_3440_);
v___x_3424_ = v_b_3412_;
v_isShared_3425_ = v_isSharedCheck_3439_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_snd_3422_);
lean_dec(v_b_3412_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3439_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3426_; lean_object* v_a_3428_; lean_object* v_a_3435_; 
v___x_3426_ = lean_box(0);
v_a_3435_ = lean_array_uget_borrowed(v_as_3409_, v_i_3411_);
if (lean_obj_tag(v_a_3435_) == 0)
{
v_a_3428_ = v_snd_3422_;
goto v___jp_3427_;
}
else
{
lean_object* v_val_3436_; uint8_t v___x_3437_; 
v_val_3436_ = lean_ctor_get(v_a_3435_, 0);
v___x_3437_ = l_Lean_LocalDecl_isAuxDecl(v_val_3436_);
if (v___x_3437_ == 0)
{
lean_object* v___x_3438_; 
lean_inc(v_val_3436_);
v___x_3438_ = lean_array_push(v_snd_3422_, v_val_3436_);
v_a_3428_ = v___x_3438_;
goto v___jp_3427_;
}
else
{
v_a_3428_ = v_snd_3422_;
goto v___jp_3427_;
}
}
v___jp_3427_:
{
lean_object* v___x_3430_; 
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 1, v_a_3428_);
lean_ctor_set(v___x_3424_, 0, v___x_3426_);
v___x_3430_ = v___x_3424_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3426_);
lean_ctor_set(v_reuseFailAlloc_3434_, 1, v_a_3428_);
v___x_3430_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
size_t v___x_3431_; size_t v___x_3432_; lean_object* v___x_3433_; 
v___x_3431_ = ((size_t)1ULL);
v___x_3432_ = lean_usize_add(v_i_3411_, v___x_3431_);
v___x_3433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___redArg(v_as_3409_, v_sz_3410_, v___x_3432_, v___x_3430_);
return v___x_3433_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6___boxed(lean_object* v_as_3441_, lean_object* v_sz_3442_, lean_object* v_i_3443_, lean_object* v_b_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_){
_start:
{
size_t v_sz_boxed_3452_; size_t v_i_boxed_3453_; lean_object* v_res_3454_; 
v_sz_boxed_3452_ = lean_unbox_usize(v_sz_3442_);
lean_dec(v_sz_3442_);
v_i_boxed_3453_ = lean_unbox_usize(v_i_3443_);
lean_dec(v_i_3443_);
v_res_3454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6(v_as_3441_, v_sz_boxed_3452_, v_i_boxed_3453_, v_b_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec_ref(v_as_3441_);
return v_res_3454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0(lean_object* v_init_3455_, lean_object* v_n_3456_, lean_object* v_b_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_){
_start:
{
if (lean_obj_tag(v_n_3456_) == 0)
{
lean_object* v_cs_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; size_t v_sz_3468_; size_t v___x_3469_; lean_object* v___x_3470_; 
v_cs_3465_ = lean_ctor_get(v_n_3456_, 0);
v___x_3466_ = lean_box(0);
v___x_3467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3466_);
lean_ctor_set(v___x_3467_, 1, v_b_3457_);
v_sz_3468_ = lean_array_size(v_cs_3465_);
v___x_3469_ = ((size_t)0ULL);
v___x_3470_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__5(v_init_3455_, v_cs_3465_, v_sz_3468_, v___x_3469_, v___x_3467_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
if (lean_obj_tag(v___x_3470_) == 0)
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3485_; 
v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3473_ = v___x_3470_;
v_isShared_3474_ = v_isSharedCheck_3485_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3470_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3485_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v_fst_3475_; 
v_fst_3475_ = lean_ctor_get(v_a_3471_, 0);
if (lean_obj_tag(v_fst_3475_) == 0)
{
lean_object* v_snd_3476_; lean_object* v___x_3477_; lean_object* v___x_3479_; 
v_snd_3476_ = lean_ctor_get(v_a_3471_, 1);
lean_inc(v_snd_3476_);
lean_dec(v_a_3471_);
v___x_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3477_, 0, v_snd_3476_);
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 0, v___x_3477_);
v___x_3479_ = v___x_3473_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v___x_3477_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
else
{
lean_object* v_val_3481_; lean_object* v___x_3483_; 
lean_inc_ref(v_fst_3475_);
lean_dec(v_a_3471_);
v_val_3481_ = lean_ctor_get(v_fst_3475_, 0);
lean_inc(v_val_3481_);
lean_dec_ref_known(v_fst_3475_, 1);
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 0, v_val_3481_);
v___x_3483_ = v___x_3473_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_val_3481_);
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
else
{
lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3493_; 
v_a_3486_ = lean_ctor_get(v___x_3470_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3488_ = v___x_3470_;
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___x_3470_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3491_; 
if (v_isShared_3489_ == 0)
{
v___x_3491_ = v___x_3488_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_a_3486_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
}
else
{
lean_object* v_vs_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; size_t v_sz_3497_; size_t v___x_3498_; lean_object* v___x_3499_; 
v_vs_3494_ = lean_ctor_get(v_n_3456_, 0);
v___x_3495_ = lean_box(0);
v___x_3496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3495_);
lean_ctor_set(v___x_3496_, 1, v_b_3457_);
v_sz_3497_ = lean_array_size(v_vs_3494_);
v___x_3498_ = ((size_t)0ULL);
v___x_3499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6(v_vs_3494_, v_sz_3497_, v___x_3498_, v___x_3496_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3514_; 
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3502_ = v___x_3499_;
v_isShared_3503_ = v_isSharedCheck_3514_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_dec(v___x_3499_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3514_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v_fst_3504_; 
v_fst_3504_ = lean_ctor_get(v_a_3500_, 0);
if (lean_obj_tag(v_fst_3504_) == 0)
{
lean_object* v_snd_3505_; lean_object* v___x_3506_; lean_object* v___x_3508_; 
v_snd_3505_ = lean_ctor_get(v_a_3500_, 1);
lean_inc(v_snd_3505_);
lean_dec(v_a_3500_);
v___x_3506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3506_, 0, v_snd_3505_);
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 0, v___x_3506_);
v___x_3508_ = v___x_3502_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v___x_3506_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
else
{
lean_object* v_val_3510_; lean_object* v___x_3512_; 
lean_inc_ref(v_fst_3504_);
lean_dec(v_a_3500_);
v_val_3510_ = lean_ctor_get(v_fst_3504_, 0);
lean_inc(v_val_3510_);
lean_dec_ref_known(v_fst_3504_, 1);
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 0, v_val_3510_);
v___x_3512_ = v___x_3502_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_val_3510_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
}
}
else
{
lean_object* v_a_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3522_; 
v_a_3515_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3517_ = v___x_3499_;
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_a_3515_);
lean_dec(v___x_3499_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3520_; 
if (v_isShared_3518_ == 0)
{
v___x_3520_ = v___x_3517_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_a_3515_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__5(lean_object* v_init_3523_, lean_object* v_as_3524_, size_t v_sz_3525_, size_t v_i_3526_, lean_object* v_b_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
uint8_t v___x_3535_; 
v___x_3535_ = lean_usize_dec_lt(v_i_3526_, v_sz_3525_);
if (v___x_3535_ == 0)
{
lean_object* v___x_3536_; 
v___x_3536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3536_, 0, v_b_3527_);
return v___x_3536_;
}
else
{
lean_object* v_snd_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3571_; 
v_snd_3537_ = lean_ctor_get(v_b_3527_, 1);
v_isSharedCheck_3571_ = !lean_is_exclusive(v_b_3527_);
if (v_isSharedCheck_3571_ == 0)
{
lean_object* v_unused_3572_; 
v_unused_3572_ = lean_ctor_get(v_b_3527_, 0);
lean_dec(v_unused_3572_);
v___x_3539_ = v_b_3527_;
v_isShared_3540_ = v_isSharedCheck_3571_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_snd_3537_);
lean_dec(v_b_3527_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3571_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3541_; lean_object* v_a_3542_; lean_object* v___x_3543_; 
v___x_3541_ = lean_box(0);
v_a_3542_ = lean_array_uget_borrowed(v_as_3524_, v_i_3526_);
lean_inc(v_snd_3537_);
v___x_3543_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0(v_init_3523_, v_a_3542_, v_snd_3537_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3562_; 
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3546_ = v___x_3543_;
v_isShared_3547_ = v_isSharedCheck_3562_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_3543_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3562_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
if (lean_obj_tag(v_a_3544_) == 0)
{
lean_object* v___x_3548_; lean_object* v___x_3550_; 
v___x_3548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3548_, 0, v_a_3544_);
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 0, v___x_3548_);
v___x_3550_ = v___x_3539_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3548_);
lean_ctor_set(v_reuseFailAlloc_3554_, 1, v_snd_3537_);
v___x_3550_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
lean_object* v___x_3552_; 
if (v_isShared_3547_ == 0)
{
lean_ctor_set(v___x_3546_, 0, v___x_3550_);
v___x_3552_ = v___x_3546_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v___x_3550_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
}
else
{
lean_object* v_a_3555_; lean_object* v___x_3557_; 
lean_del_object(v___x_3546_);
lean_dec(v_snd_3537_);
v_a_3555_ = lean_ctor_get(v_a_3544_, 0);
lean_inc(v_a_3555_);
lean_dec_ref_known(v_a_3544_, 1);
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 1, v_a_3555_);
lean_ctor_set(v___x_3539_, 0, v___x_3541_);
v___x_3557_ = v___x_3539_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v___x_3541_);
lean_ctor_set(v_reuseFailAlloc_3561_, 1, v_a_3555_);
v___x_3557_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
size_t v___x_3558_; size_t v___x_3559_; 
v___x_3558_ = ((size_t)1ULL);
v___x_3559_ = lean_usize_add(v_i_3526_, v___x_3558_);
v_i_3526_ = v___x_3559_;
v_b_3527_ = v___x_3557_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3570_; 
lean_del_object(v___x_3539_);
lean_dec(v_snd_3537_);
v_a_3563_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3565_ = v___x_3543_;
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_3543_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3568_; 
if (v_isShared_3566_ == 0)
{
v___x_3568_ = v___x_3565_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__5___boxed(lean_object* v_init_3573_, lean_object* v_as_3574_, lean_object* v_sz_3575_, lean_object* v_i_3576_, lean_object* v_b_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_){
_start:
{
size_t v_sz_boxed_3585_; size_t v_i_boxed_3586_; lean_object* v_res_3587_; 
v_sz_boxed_3585_ = lean_unbox_usize(v_sz_3575_);
lean_dec(v_sz_3575_);
v_i_boxed_3586_ = lean_unbox_usize(v_i_3576_);
lean_dec(v_i_3576_);
v_res_3587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__5(v_init_3573_, v_as_3574_, v_sz_boxed_3585_, v_i_boxed_3586_, v_b_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_);
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3579_);
lean_dec_ref(v___y_3578_);
lean_dec_ref(v_as_3574_);
lean_dec_ref(v_init_3573_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0___boxed(lean_object* v_init_3588_, lean_object* v_n_3589_, lean_object* v_b_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_){
_start:
{
lean_object* v_res_3598_; 
v_res_3598_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0(v_init_3588_, v_n_3589_, v_b_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec_ref(v_n_3589_);
lean_dec_ref(v_init_3588_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0(lean_object* v_t_3599_, lean_object* v_init_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_){
_start:
{
lean_object* v_root_3608_; lean_object* v_tail_3609_; lean_object* v___x_3610_; 
v_root_3608_ = lean_ctor_get(v_t_3599_, 0);
v_tail_3609_ = lean_ctor_get(v_t_3599_, 1);
lean_inc_ref(v_init_3600_);
v___x_3610_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0(v_init_3600_, v_root_3608_, v_init_3600_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_);
lean_dec_ref(v_init_3600_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3647_; 
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3613_ = v___x_3610_;
v_isShared_3614_ = v_isSharedCheck_3647_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3610_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3647_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
if (lean_obj_tag(v_a_3611_) == 0)
{
lean_object* v_a_3615_; lean_object* v___x_3617_; 
v_a_3615_ = lean_ctor_get(v_a_3611_, 0);
lean_inc(v_a_3615_);
lean_dec_ref_known(v_a_3611_, 1);
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 0, v_a_3615_);
v___x_3617_ = v___x_3613_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3615_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
else
{
lean_object* v_a_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; size_t v_sz_3622_; size_t v___x_3623_; lean_object* v___x_3624_; 
lean_del_object(v___x_3613_);
v_a_3619_ = lean_ctor_get(v_a_3611_, 0);
lean_inc(v_a_3619_);
lean_dec_ref_known(v_a_3611_, 1);
v___x_3620_ = lean_box(0);
v___x_3621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3620_);
lean_ctor_set(v___x_3621_, 1, v_a_3619_);
v_sz_3622_ = lean_array_size(v_tail_3609_);
v___x_3623_ = ((size_t)0ULL);
v___x_3624_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1(v_tail_3609_, v_sz_3622_, v___x_3623_, v___x_3621_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3638_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3627_ = v___x_3624_;
v_isShared_3628_ = v_isSharedCheck_3638_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3624_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3638_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v_fst_3629_; 
v_fst_3629_ = lean_ctor_get(v_a_3625_, 0);
if (lean_obj_tag(v_fst_3629_) == 0)
{
lean_object* v_snd_3630_; lean_object* v___x_3632_; 
v_snd_3630_ = lean_ctor_get(v_a_3625_, 1);
lean_inc(v_snd_3630_);
lean_dec(v_a_3625_);
if (v_isShared_3628_ == 0)
{
lean_ctor_set(v___x_3627_, 0, v_snd_3630_);
v___x_3632_ = v___x_3627_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_snd_3630_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
else
{
lean_object* v_val_3634_; lean_object* v___x_3636_; 
lean_inc_ref(v_fst_3629_);
lean_dec(v_a_3625_);
v_val_3634_ = lean_ctor_get(v_fst_3629_, 0);
lean_inc(v_val_3634_);
lean_dec_ref_known(v_fst_3629_, 1);
if (v_isShared_3628_ == 0)
{
lean_ctor_set(v___x_3627_, 0, v_val_3634_);
v___x_3636_ = v___x_3627_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_val_3634_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
}
}
else
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3646_; 
v_a_3639_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3646_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3646_ == 0)
{
v___x_3641_ = v___x_3624_;
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3624_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3644_; 
if (v_isShared_3642_ == 0)
{
v___x_3644_ = v___x_3641_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_a_3639_);
v___x_3644_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
return v___x_3644_;
}
}
}
}
}
}
else
{
lean_object* v_a_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3655_; 
v_a_3648_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3650_ = v___x_3610_;
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_a_3648_);
lean_dec(v___x_3610_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3653_; 
if (v_isShared_3651_ == 0)
{
v___x_3653_ = v___x_3650_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_a_3648_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0___boxed(lean_object* v_t_3656_, lean_object* v_init_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_){
_start:
{
lean_object* v_res_3665_; 
v_res_3665_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0(v_t_3656_, v_init_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_);
lean_dec(v___y_3663_);
lean_dec_ref(v___y_3662_);
lean_dec(v___y_3661_);
lean_dec_ref(v___y_3660_);
lean_dec(v___y_3659_);
lean_dec_ref(v___y_3658_);
lean_dec_ref(v_t_3656_);
return v_res_3665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__1(size_t v_sz_3666_, size_t v_i_3667_, lean_object* v_bs_3668_){
_start:
{
uint8_t v___x_3669_; 
v___x_3669_ = lean_usize_dec_lt(v_i_3667_, v_sz_3666_);
if (v___x_3669_ == 0)
{
return v_bs_3668_;
}
else
{
lean_object* v_v_3670_; lean_object* v___x_3671_; lean_object* v_bs_x27_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; size_t v___x_3675_; size_t v___x_3676_; lean_object* v___x_3677_; 
v_v_3670_ = lean_array_uget(v_bs_3668_, v_i_3667_);
v___x_3671_ = lean_unsigned_to_nat(0u);
v_bs_x27_3672_ = lean_array_uset(v_bs_3668_, v_i_3667_, v___x_3671_);
v___x_3673_ = l_Lean_LocalDecl_fvarId(v_v_3670_);
lean_dec(v_v_3670_);
v___x_3674_ = l_Lean_mkFVar(v___x_3673_);
v___x_3675_ = ((size_t)1ULL);
v___x_3676_ = lean_usize_add(v_i_3667_, v___x_3675_);
v___x_3677_ = lean_array_uset(v_bs_x27_3672_, v_i_3667_, v___x_3674_);
v_i_3667_ = v___x_3676_;
v_bs_3668_ = v___x_3677_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__1___boxed(lean_object* v_sz_3679_, lean_object* v_i_3680_, lean_object* v_bs_3681_){
_start:
{
size_t v_sz_boxed_3682_; size_t v_i_boxed_3683_; lean_object* v_res_3684_; 
v_sz_boxed_3682_ = lean_unbox_usize(v_sz_3679_);
lean_dec(v_sz_3679_);
v_i_boxed_3683_ = lean_unbox_usize(v_i_3680_);
lean_dec(v_i_3680_);
v_res_3684_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__1(v_sz_boxed_3682_, v_i_boxed_3683_, v_bs_3681_);
return v_res_3684_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
v___x_3690_ = lean_box(0);
v___x_3691_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__1));
v___x_3692_ = l_Lean_Expr_const___override(v___x_3691_, v___x_3690_);
return v___x_3692_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6(void){
_start:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
v___x_3698_ = lean_box(0);
v___x_3699_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__5));
v___x_3700_ = l_Lean_mkConst(v___x_3699_, v___x_3698_);
return v___x_3700_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3705_ = lean_box(0);
v___x_3706_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__8));
v___x_3707_ = l_Lean_mkConst(v___x_3706_, v___x_3705_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg(size_t v_sz_3708_, size_t v_i_3709_, lean_object* v_bs_3710_){
_start:
{
uint8_t v___x_3712_; 
v___x_3712_ = lean_usize_dec_lt(v_i_3709_, v_sz_3708_);
if (v___x_3712_ == 0)
{
lean_object* v___x_3713_; 
v___x_3713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3713_, 0, v_bs_3710_);
return v___x_3713_;
}
else
{
lean_object* v_v_3714_; lean_object* v_module_3715_; uint8_t v_importAll_3716_; uint8_t v_isExported_3717_; uint8_t v_isMeta_3718_; lean_object* v___x_3719_; lean_object* v_bs_x27_3720_; lean_object* v___x_3721_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3744_; 
v_v_3714_ = lean_array_uget_borrowed(v_bs_3710_, v_i_3709_);
v_module_3715_ = lean_ctor_get(v_v_3714_, 0);
lean_inc(v_module_3715_);
v_importAll_3716_ = lean_ctor_get_uint8(v_v_3714_, sizeof(void*)*1);
v_isExported_3717_ = lean_ctor_get_uint8(v_v_3714_, sizeof(void*)*1 + 1);
v_isMeta_3718_ = lean_ctor_get_uint8(v_v_3714_, sizeof(void*)*1 + 2);
v___x_3719_ = lean_unsigned_to_nat(0u);
v_bs_x27_3720_ = lean_array_uset(v_bs_3710_, v_i_3709_, v___x_3719_);
v___x_3721_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_module_3715_);
if (v_importAll_3716_ == 0)
{
lean_object* v___x_3747_; 
v___x_3747_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6);
v___y_3744_ = v___x_3747_;
goto v___jp_3743_;
}
else
{
lean_object* v___x_3748_; 
v___x_3748_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9);
v___y_3744_ = v___x_3748_;
goto v___jp_3743_;
}
v___jp_3722_:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; size_t v___x_3734_; size_t v___x_3735_; lean_object* v___x_3736_; 
v___x_3726_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__2);
v___x_3727_ = lean_unsigned_to_nat(4u);
v___x_3728_ = lean_mk_empty_array_with_capacity(v___x_3727_);
v___x_3729_ = lean_array_push(v___x_3728_, v___x_3721_);
lean_inc_ref(v___y_3724_);
v___x_3730_ = lean_array_push(v___x_3729_, v___y_3724_);
lean_inc_ref(v___y_3723_);
v___x_3731_ = lean_array_push(v___x_3730_, v___y_3723_);
lean_inc_ref(v___y_3725_);
v___x_3732_ = lean_array_push(v___x_3731_, v___y_3725_);
v___x_3733_ = l_Lean_mkAppN(v___x_3726_, v___x_3732_);
lean_dec_ref(v___x_3732_);
v___x_3734_ = ((size_t)1ULL);
v___x_3735_ = lean_usize_add(v_i_3709_, v___x_3734_);
v___x_3736_ = lean_array_uset(v_bs_x27_3720_, v_i_3709_, v___x_3733_);
v_i_3709_ = v___x_3735_;
v_bs_3710_ = v___x_3736_;
goto _start;
}
v___jp_3738_:
{
if (v_isMeta_3718_ == 0)
{
lean_object* v___x_3741_; 
v___x_3741_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6);
v___y_3723_ = v___y_3740_;
v___y_3724_ = v___y_3739_;
v___y_3725_ = v___x_3741_;
goto v___jp_3722_;
}
else
{
lean_object* v___x_3742_; 
v___x_3742_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9);
v___y_3723_ = v___y_3740_;
v___y_3724_ = v___y_3739_;
v___y_3725_ = v___x_3742_;
goto v___jp_3722_;
}
}
v___jp_3743_:
{
if (v_isExported_3717_ == 0)
{
lean_object* v___x_3745_; 
v___x_3745_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6);
v___y_3739_ = v___y_3744_;
v___y_3740_ = v___x_3745_;
goto v___jp_3738_;
}
else
{
lean_object* v___x_3746_; 
v___x_3746_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9);
v___y_3739_ = v___y_3744_;
v___y_3740_ = v___x_3746_;
goto v___jp_3738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___boxed(lean_object* v_sz_3749_, lean_object* v_i_3750_, lean_object* v_bs_3751_, lean_object* v___y_3752_){
_start:
{
size_t v_sz_boxed_3753_; size_t v_i_boxed_3754_; lean_object* v_res_3755_; 
v_sz_boxed_3753_ = lean_unbox_usize(v_sz_3749_);
lean_dec(v_sz_3749_);
v_i_boxed_3754_ = lean_unbox_usize(v_i_3750_);
lean_dec(v_i_3750_);
v_res_3755_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg(v_sz_boxed_3753_, v_i_boxed_3754_, v_bs_3751_);
return v_res_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12_spec__20___redArg(lean_object* v_x_3756_, lean_object* v_x_3757_, lean_object* v_x_3758_, lean_object* v_x_3759_){
_start:
{
lean_object* v_ks_3760_; lean_object* v_vs_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3785_; 
v_ks_3760_ = lean_ctor_get(v_x_3756_, 0);
v_vs_3761_ = lean_ctor_get(v_x_3756_, 1);
v_isSharedCheck_3785_ = !lean_is_exclusive(v_x_3756_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3763_ = v_x_3756_;
v_isShared_3764_ = v_isSharedCheck_3785_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_vs_3761_);
lean_inc(v_ks_3760_);
lean_dec(v_x_3756_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3785_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3765_; uint8_t v___x_3766_; 
v___x_3765_ = lean_array_get_size(v_ks_3760_);
v___x_3766_ = lean_nat_dec_lt(v_x_3757_, v___x_3765_);
if (v___x_3766_ == 0)
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3770_; 
lean_dec(v_x_3757_);
v___x_3767_ = lean_array_push(v_ks_3760_, v_x_3758_);
v___x_3768_ = lean_array_push(v_vs_3761_, v_x_3759_);
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 1, v___x_3768_);
lean_ctor_set(v___x_3763_, 0, v___x_3767_);
v___x_3770_ = v___x_3763_;
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
else
{
lean_object* v_k_x27_3772_; uint8_t v___x_3773_; 
v_k_x27_3772_ = lean_array_fget_borrowed(v_ks_3760_, v_x_3757_);
v___x_3773_ = l_Lean_instBEqFVarId_beq(v_x_3758_, v_k_x27_3772_);
if (v___x_3773_ == 0)
{
lean_object* v___x_3775_; 
if (v_isShared_3764_ == 0)
{
v___x_3775_ = v___x_3763_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_ks_3760_);
lean_ctor_set(v_reuseFailAlloc_3779_, 1, v_vs_3761_);
v___x_3775_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
lean_object* v___x_3776_; lean_object* v___x_3777_; 
v___x_3776_ = lean_unsigned_to_nat(1u);
v___x_3777_ = lean_nat_add(v_x_3757_, v___x_3776_);
lean_dec(v_x_3757_);
v_x_3756_ = v___x_3775_;
v_x_3757_ = v___x_3777_;
goto _start;
}
}
else
{
lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3783_; 
v___x_3780_ = lean_array_fset(v_ks_3760_, v_x_3757_, v_x_3758_);
v___x_3781_ = lean_array_fset(v_vs_3761_, v_x_3757_, v_x_3759_);
lean_dec(v_x_3757_);
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 1, v___x_3781_);
lean_ctor_set(v___x_3763_, 0, v___x_3780_);
v___x_3783_ = v___x_3763_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3780_);
lean_ctor_set(v_reuseFailAlloc_3784_, 1, v___x_3781_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
return v___x_3783_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12___redArg(lean_object* v_n_3786_, lean_object* v_k_3787_, lean_object* v_v_3788_){
_start:
{
lean_object* v___x_3789_; lean_object* v___x_3790_; 
v___x_3789_ = lean_unsigned_to_nat(0u);
v___x_3790_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12_spec__20___redArg(v_n_3786_, v___x_3789_, v_k_3787_, v_v_3788_);
return v___x_3790_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_3791_; 
v___x_3791_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg(lean_object* v_x_3792_, size_t v_x_3793_, size_t v_x_3794_, lean_object* v_x_3795_, lean_object* v_x_3796_){
_start:
{
if (lean_obj_tag(v_x_3792_) == 0)
{
lean_object* v_es_3797_; size_t v___x_3798_; size_t v___x_3799_; lean_object* v_j_3800_; lean_object* v___x_3801_; uint8_t v___x_3802_; 
v_es_3797_ = lean_ctor_get(v_x_3792_, 0);
v___x_3798_ = ((size_t)31ULL);
v___x_3799_ = lean_usize_land(v_x_3793_, v___x_3798_);
v_j_3800_ = lean_usize_to_nat(v___x_3799_);
v___x_3801_ = lean_array_get_size(v_es_3797_);
v___x_3802_ = lean_nat_dec_lt(v_j_3800_, v___x_3801_);
if (v___x_3802_ == 0)
{
lean_dec(v_j_3800_);
lean_dec(v_x_3796_);
lean_dec(v_x_3795_);
return v_x_3792_;
}
else
{
lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3841_; 
lean_inc_ref(v_es_3797_);
v_isSharedCheck_3841_ = !lean_is_exclusive(v_x_3792_);
if (v_isSharedCheck_3841_ == 0)
{
lean_object* v_unused_3842_; 
v_unused_3842_ = lean_ctor_get(v_x_3792_, 0);
lean_dec(v_unused_3842_);
v___x_3804_ = v_x_3792_;
v_isShared_3805_ = v_isSharedCheck_3841_;
goto v_resetjp_3803_;
}
else
{
lean_dec(v_x_3792_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3841_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v_v_3806_; lean_object* v___x_3807_; lean_object* v_xs_x27_3808_; lean_object* v___y_3810_; 
v_v_3806_ = lean_array_fget(v_es_3797_, v_j_3800_);
v___x_3807_ = lean_box(0);
v_xs_x27_3808_ = lean_array_fset(v_es_3797_, v_j_3800_, v___x_3807_);
switch(lean_obj_tag(v_v_3806_))
{
case 0:
{
lean_object* v_key_3815_; lean_object* v_val_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3826_; 
v_key_3815_ = lean_ctor_get(v_v_3806_, 0);
v_val_3816_ = lean_ctor_get(v_v_3806_, 1);
v_isSharedCheck_3826_ = !lean_is_exclusive(v_v_3806_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3818_ = v_v_3806_;
v_isShared_3819_ = v_isSharedCheck_3826_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_val_3816_);
lean_inc(v_key_3815_);
lean_dec(v_v_3806_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3826_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
uint8_t v___x_3820_; 
v___x_3820_ = l_Lean_instBEqFVarId_beq(v_x_3795_, v_key_3815_);
if (v___x_3820_ == 0)
{
lean_object* v___x_3821_; lean_object* v___x_3822_; 
lean_del_object(v___x_3818_);
v___x_3821_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3815_, v_val_3816_, v_x_3795_, v_x_3796_);
v___x_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3821_);
v___y_3810_ = v___x_3822_;
goto v___jp_3809_;
}
else
{
lean_object* v___x_3824_; 
lean_dec(v_val_3816_);
lean_dec(v_key_3815_);
if (v_isShared_3819_ == 0)
{
lean_ctor_set(v___x_3818_, 1, v_x_3796_);
lean_ctor_set(v___x_3818_, 0, v_x_3795_);
v___x_3824_ = v___x_3818_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_x_3795_);
lean_ctor_set(v_reuseFailAlloc_3825_, 1, v_x_3796_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
v___y_3810_ = v___x_3824_;
goto v___jp_3809_;
}
}
}
}
case 1:
{
lean_object* v_node_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3839_; 
v_node_3827_ = lean_ctor_get(v_v_3806_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v_v_3806_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3829_ = v_v_3806_;
v_isShared_3830_ = v_isSharedCheck_3839_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_node_3827_);
lean_dec(v_v_3806_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3839_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
size_t v___x_3831_; size_t v___x_3832_; size_t v___x_3833_; size_t v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3837_; 
v___x_3831_ = ((size_t)5ULL);
v___x_3832_ = lean_usize_shift_right(v_x_3793_, v___x_3831_);
v___x_3833_ = ((size_t)1ULL);
v___x_3834_ = lean_usize_add(v_x_3794_, v___x_3833_);
v___x_3835_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg(v_node_3827_, v___x_3832_, v___x_3834_, v_x_3795_, v_x_3796_);
if (v_isShared_3830_ == 0)
{
lean_ctor_set(v___x_3829_, 0, v___x_3835_);
v___x_3837_ = v___x_3829_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v___x_3835_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
v___y_3810_ = v___x_3837_;
goto v___jp_3809_;
}
}
}
default: 
{
lean_object* v___x_3840_; 
v___x_3840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3840_, 0, v_x_3795_);
lean_ctor_set(v___x_3840_, 1, v_x_3796_);
v___y_3810_ = v___x_3840_;
goto v___jp_3809_;
}
}
v___jp_3809_:
{
lean_object* v___x_3811_; lean_object* v___x_3813_; 
v___x_3811_ = lean_array_fset(v_xs_x27_3808_, v_j_3800_, v___y_3810_);
lean_dec(v_j_3800_);
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 0, v___x_3811_);
v___x_3813_ = v___x_3804_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3811_);
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
}
else
{
lean_object* v_ks_3843_; lean_object* v_vs_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3862_; 
v_ks_3843_ = lean_ctor_get(v_x_3792_, 0);
v_vs_3844_ = lean_ctor_get(v_x_3792_, 1);
v_isSharedCheck_3862_ = !lean_is_exclusive(v_x_3792_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3846_ = v_x_3792_;
v_isShared_3847_ = v_isSharedCheck_3862_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_vs_3844_);
lean_inc(v_ks_3843_);
lean_dec(v_x_3792_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3862_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3849_; 
if (v_isShared_3847_ == 0)
{
v___x_3849_ = v___x_3846_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_ks_3843_);
lean_ctor_set(v_reuseFailAlloc_3861_, 1, v_vs_3844_);
v___x_3849_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
lean_object* v_newNode_3850_; size_t v___x_3851_; uint8_t v___x_3852_; 
v_newNode_3850_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12___redArg(v___x_3849_, v_x_3795_, v_x_3796_);
v___x_3851_ = ((size_t)7ULL);
v___x_3852_ = lean_usize_dec_le(v___x_3851_, v_x_3794_);
if (v___x_3852_ == 0)
{
lean_object* v___x_3853_; lean_object* v___x_3854_; uint8_t v___x_3855_; 
v___x_3853_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3850_);
v___x_3854_ = lean_unsigned_to_nat(4u);
v___x_3855_ = lean_nat_dec_lt(v___x_3853_, v___x_3854_);
lean_dec(v___x_3853_);
if (v___x_3855_ == 0)
{
lean_object* v_ks_3856_; lean_object* v_vs_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; 
v_ks_3856_ = lean_ctor_get(v_newNode_3850_, 0);
lean_inc_ref(v_ks_3856_);
v_vs_3857_ = lean_ctor_get(v_newNode_3850_, 1);
lean_inc_ref(v_vs_3857_);
lean_dec_ref(v_newNode_3850_);
v___x_3858_ = lean_unsigned_to_nat(0u);
v___x_3859_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg___closed__0);
v___x_3860_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___redArg(v_x_3794_, v_ks_3856_, v_vs_3857_, v___x_3858_, v___x_3859_);
lean_dec_ref(v_vs_3857_);
lean_dec_ref(v_ks_3856_);
return v___x_3860_;
}
else
{
return v_newNode_3850_;
}
}
else
{
return v_newNode_3850_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___redArg(size_t v_depth_3863_, lean_object* v_keys_3864_, lean_object* v_vals_3865_, lean_object* v_i_3866_, lean_object* v_entries_3867_){
_start:
{
lean_object* v___x_3868_; uint8_t v___x_3869_; 
v___x_3868_ = lean_array_get_size(v_keys_3864_);
v___x_3869_ = lean_nat_dec_lt(v_i_3866_, v___x_3868_);
if (v___x_3869_ == 0)
{
lean_dec(v_i_3866_);
return v_entries_3867_;
}
else
{
lean_object* v_k_3870_; lean_object* v_v_3871_; uint64_t v___x_3872_; size_t v_h_3873_; size_t v___x_3874_; lean_object* v___x_3875_; size_t v___x_3876_; size_t v___x_3877_; size_t v___x_3878_; size_t v_h_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v_k_3870_ = lean_array_fget_borrowed(v_keys_3864_, v_i_3866_);
v_v_3871_ = lean_array_fget_borrowed(v_vals_3865_, v_i_3866_);
v___x_3872_ = l_Lean_instHashableFVarId_hash(v_k_3870_);
v_h_3873_ = lean_uint64_to_usize(v___x_3872_);
v___x_3874_ = ((size_t)5ULL);
v___x_3875_ = lean_unsigned_to_nat(1u);
v___x_3876_ = ((size_t)1ULL);
v___x_3877_ = lean_usize_sub(v_depth_3863_, v___x_3876_);
v___x_3878_ = lean_usize_mul(v___x_3874_, v___x_3877_);
v_h_3879_ = lean_usize_shift_right(v_h_3873_, v___x_3878_);
v___x_3880_ = lean_nat_add(v_i_3866_, v___x_3875_);
lean_dec(v_i_3866_);
lean_inc(v_v_3871_);
lean_inc(v_k_3870_);
v___x_3881_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg(v_entries_3867_, v_h_3879_, v_depth_3863_, v_k_3870_, v_v_3871_);
v_i_3866_ = v___x_3880_;
v_entries_3867_ = v___x_3881_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___redArg___boxed(lean_object* v_depth_3883_, lean_object* v_keys_3884_, lean_object* v_vals_3885_, lean_object* v_i_3886_, lean_object* v_entries_3887_){
_start:
{
size_t v_depth_boxed_3888_; lean_object* v_res_3889_; 
v_depth_boxed_3888_ = lean_unbox_usize(v_depth_3883_);
lean_dec(v_depth_3883_);
v_res_3889_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___redArg(v_depth_boxed_3888_, v_keys_3884_, v_vals_3885_, v_i_3886_, v_entries_3887_);
lean_dec_ref(v_vals_3885_);
lean_dec_ref(v_keys_3884_);
return v_res_3889_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg___boxed(lean_object* v_x_3890_, lean_object* v_x_3891_, lean_object* v_x_3892_, lean_object* v_x_3893_, lean_object* v_x_3894_){
_start:
{
size_t v_x_35230__boxed_3895_; size_t v_x_35231__boxed_3896_; lean_object* v_res_3897_; 
v_x_35230__boxed_3895_ = lean_unbox_usize(v_x_3891_);
lean_dec(v_x_3891_);
v_x_35231__boxed_3896_ = lean_unbox_usize(v_x_3892_);
lean_dec(v_x_3892_);
v_res_3897_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg(v_x_3890_, v_x_35230__boxed_3895_, v_x_35231__boxed_3896_, v_x_3893_, v_x_3894_);
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2___redArg(lean_object* v_x_3898_, lean_object* v_x_3899_, lean_object* v_x_3900_){
_start:
{
uint64_t v___x_3901_; size_t v___x_3902_; size_t v___x_3903_; lean_object* v___x_3904_; 
v___x_3901_ = l_Lean_instHashableFVarId_hash(v_x_3899_);
v___x_3902_ = lean_uint64_to_usize(v___x_3901_);
v___x_3903_ = ((size_t)1ULL);
v___x_3904_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg(v_x_3898_, v___x_3902_, v___x_3903_, v_x_3899_, v_x_3900_);
return v___x_3904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__11(lean_object* v_as_3905_, size_t v_i_3906_, size_t v_stop_3907_, lean_object* v_b_3908_){
_start:
{
lean_object* v___y_3910_; uint8_t v___x_3914_; 
v___x_3914_ = lean_usize_dec_eq(v_i_3906_, v_stop_3907_);
if (v___x_3914_ == 0)
{
lean_object* v_fvarIdToDecl_3915_; lean_object* v_decls_3916_; lean_object* v_auxDeclToFullName_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; 
v_fvarIdToDecl_3915_ = lean_ctor_get(v_b_3908_, 0);
v_decls_3916_ = lean_ctor_get(v_b_3908_, 1);
v_auxDeclToFullName_3917_ = lean_ctor_get(v_b_3908_, 2);
v___x_3918_ = lean_array_uget_borrowed(v_as_3905_, v_i_3906_);
v___x_3919_ = l_Lean_LocalDecl_fvarId(v___x_3918_);
lean_inc_ref(v_b_3908_);
v___x_3920_ = lean_local_ctx_find(v_b_3908_, v___x_3919_);
if (lean_obj_tag(v___x_3920_) == 0)
{
v___y_3910_ = v_b_3908_;
goto v___jp_3909_;
}
else
{
lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3946_; 
lean_inc(v_auxDeclToFullName_3917_);
lean_inc_ref(v_decls_3916_);
lean_inc_ref(v_fvarIdToDecl_3915_);
v_isSharedCheck_3946_ = !lean_is_exclusive(v_b_3908_);
if (v_isSharedCheck_3946_ == 0)
{
lean_object* v_unused_3947_; lean_object* v_unused_3948_; lean_object* v_unused_3949_; 
v_unused_3947_ = lean_ctor_get(v_b_3908_, 2);
lean_dec(v_unused_3947_);
v_unused_3948_ = lean_ctor_get(v_b_3908_, 1);
lean_dec(v_unused_3948_);
v_unused_3949_ = lean_ctor_get(v_b_3908_, 0);
lean_dec(v_unused_3949_);
v___x_3922_ = v_b_3908_;
v_isShared_3923_ = v_isSharedCheck_3946_;
goto v_resetjp_3921_;
}
else
{
lean_dec(v_b_3908_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3946_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v_val_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3945_; 
v_val_3924_ = lean_ctor_get(v___x_3920_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3920_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3926_ = v___x_3920_;
v_isShared_3927_ = v_isSharedCheck_3945_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_val_3924_);
lean_dec(v___x_3920_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3945_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
uint8_t v___x_3928_; lean_object* v___x_3929_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3941_; lean_object* v_fvarId_3944_; 
v___x_3928_ = 1;
v___x_3929_ = l_Lean_LocalDecl_setNondep(v_val_3924_, v___x_3928_);
v_fvarId_3944_ = lean_ctor_get(v___x_3929_, 1);
lean_inc(v_fvarId_3944_);
v___y_3941_ = v_fvarId_3944_;
goto v___jp_3940_;
v___jp_3930_:
{
lean_object* v___x_3934_; 
if (v_isShared_3927_ == 0)
{
lean_ctor_set(v___x_3926_, 0, v___x_3929_);
v___x_3934_ = v___x_3926_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v___x_3929_);
v___x_3934_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
lean_object* v___x_3935_; lean_object* v___x_3937_; 
v___x_3935_ = l_Lean_PersistentArray_set___redArg(v_decls_3916_, v___y_3932_, v___x_3934_);
lean_dec(v___y_3932_);
if (v_isShared_3923_ == 0)
{
lean_ctor_set(v___x_3922_, 1, v___x_3935_);
lean_ctor_set(v___x_3922_, 0, v___y_3931_);
v___x_3937_ = v___x_3922_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v___y_3931_);
lean_ctor_set(v_reuseFailAlloc_3938_, 1, v___x_3935_);
lean_ctor_set(v_reuseFailAlloc_3938_, 2, v_auxDeclToFullName_3917_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
v___y_3910_ = v___x_3937_;
goto v___jp_3909_;
}
}
}
v___jp_3940_:
{
lean_object* v___x_3942_; lean_object* v_index_3943_; 
lean_inc_ref(v___x_3929_);
v___x_3942_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2___redArg(v_fvarIdToDecl_3915_, v___y_3941_, v___x_3929_);
v_index_3943_ = lean_ctor_get(v___x_3929_, 0);
lean_inc(v_index_3943_);
v___y_3931_ = v___x_3942_;
v___y_3932_ = v_index_3943_;
goto v___jp_3930_;
}
}
}
}
}
else
{
return v_b_3908_;
}
v___jp_3909_:
{
size_t v___x_3911_; size_t v___x_3912_; 
v___x_3911_ = ((size_t)1ULL);
v___x_3912_ = lean_usize_add(v_i_3906_, v___x_3911_);
v_i_3906_ = v___x_3912_;
v_b_3908_ = v___y_3910_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__11___boxed(lean_object* v_as_3950_, lean_object* v_i_3951_, lean_object* v_stop_3952_, lean_object* v_b_3953_){
_start:
{
size_t v_i_boxed_3954_; size_t v_stop_boxed_3955_; lean_object* v_res_3956_; 
v_i_boxed_3954_ = lean_unbox_usize(v_i_3951_);
lean_dec(v_i_3951_);
v_stop_boxed_3955_ = lean_unbox_usize(v_stop_3952_);
lean_dec(v_stop_3952_);
v_res_3956_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__11(v_as_3950_, v_i_boxed_3954_, v_stop_boxed_3955_, v_b_3953_);
lean_dec_ref(v_as_3950_);
return v_res_3956_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__15(lean_object* v_msgData_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_){
_start:
{
lean_object* v___x_3963_; lean_object* v_env_3964_; uint8_t v___x_3965_; lean_object* v_env_3966_; lean_object* v___x_3967_; lean_object* v_toCold_3968_; lean_object* v_mctx_3969_; lean_object* v_lctx_3970_; lean_object* v_options_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3963_ = lean_st_ref_get(v___y_3961_);
v_env_3964_ = lean_ctor_get(v___x_3963_, 0);
lean_inc_ref(v_env_3964_);
lean_dec(v___x_3963_);
v___x_3965_ = 0;
v_env_3966_ = l_Lean_Environment_setRecordingDeps(v_env_3964_, v___x_3965_);
v___x_3967_ = lean_st_ref_get(v___y_3959_);
v_toCold_3968_ = lean_ctor_get(v___y_3960_, 0);
v_mctx_3969_ = lean_ctor_get(v___x_3967_, 0);
lean_inc_ref(v_mctx_3969_);
lean_dec(v___x_3967_);
v_lctx_3970_ = lean_ctor_get(v___y_3958_, 2);
v_options_3971_ = lean_ctor_get(v_toCold_3968_, 2);
lean_inc_ref(v_options_3971_);
lean_inc_ref(v_lctx_3970_);
v___x_3972_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3972_, 0, v_env_3966_);
lean_ctor_set(v___x_3972_, 1, v_mctx_3969_);
lean_ctor_set(v___x_3972_, 2, v_lctx_3970_);
lean_ctor_set(v___x_3972_, 3, v_options_3971_);
v___x_3973_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3972_);
lean_ctor_set(v___x_3973_, 1, v_msgData_3957_);
v___x_3974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3973_);
return v___x_3974_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__15___boxed(lean_object* v_msgData_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__15(v_msgData_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
return v_res_3981_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0(void){
_start:
{
lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3982_ = lean_box(1);
v___x_3983_ = l_Lean_MessageData_ofFormat(v___x_3982_);
return v___x_3983_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__3(void){
_start:
{
lean_object* v___x_3987_; lean_object* v___x_3988_; 
v___x_3987_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__2));
v___x_3988_ = l_Lean_MessageData_ofFormat(v___x_3987_);
return v___x_3988_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23(lean_object* v_x_3989_, lean_object* v_x_3990_){
_start:
{
if (lean_obj_tag(v_x_3990_) == 0)
{
return v_x_3989_;
}
else
{
lean_object* v_head_3991_; lean_object* v_tail_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_4014_; 
v_head_3991_ = lean_ctor_get(v_x_3990_, 0);
v_tail_3992_ = lean_ctor_get(v_x_3990_, 1);
v_isSharedCheck_4014_ = !lean_is_exclusive(v_x_3990_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_3994_ = v_x_3990_;
v_isShared_3995_ = v_isSharedCheck_4014_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_tail_3992_);
lean_inc(v_head_3991_);
lean_dec(v_x_3990_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_4014_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v_before_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4012_; 
v_before_3996_ = lean_ctor_get(v_head_3991_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v_head_3991_);
if (v_isSharedCheck_4012_ == 0)
{
lean_object* v_unused_4013_; 
v_unused_4013_ = lean_ctor_get(v_head_3991_, 1);
lean_dec(v_unused_4013_);
v___x_3998_ = v_head_3991_;
v_isShared_3999_ = v_isSharedCheck_4012_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_before_3996_);
lean_dec(v_head_3991_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4012_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4000_; lean_object* v___x_4002_; 
v___x_4000_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0);
if (v_isShared_3999_ == 0)
{
lean_ctor_set_tag(v___x_3998_, 7);
lean_ctor_set(v___x_3998_, 1, v___x_4000_);
lean_ctor_set(v___x_3998_, 0, v_x_3989_);
v___x_4002_ = v___x_3998_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_x_3989_);
lean_ctor_set(v_reuseFailAlloc_4011_, 1, v___x_4000_);
v___x_4002_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
lean_object* v___x_4003_; lean_object* v___x_4005_; 
v___x_4003_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__3);
if (v_isShared_3995_ == 0)
{
lean_ctor_set_tag(v___x_3994_, 7);
lean_ctor_set(v___x_3994_, 1, v___x_4003_);
lean_ctor_set(v___x_3994_, 0, v___x_4002_);
v___x_4005_ = v___x_3994_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v___x_4002_);
lean_ctor_set(v_reuseFailAlloc_4010_, 1, v___x_4003_);
v___x_4005_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4006_ = l_Lean_MessageData_ofSyntax(v_before_3996_);
v___x_4007_ = l_Lean_indentD(v___x_4006_);
v___x_4008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4008_, 0, v___x_4005_);
lean_ctor_set(v___x_4008_, 1, v___x_4007_);
v_x_3989_ = v___x_4008_;
v_x_3990_ = v_tail_3992_;
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
lean_object* v___x_4018_; lean_object* v___x_4019_; 
v___x_4018_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__1));
v___x_4019_ = l_Lean_MessageData_ofFormat(v___x_4018_);
return v___x_4019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg(lean_object* v_msgData_4020_, lean_object* v_macroStack_4021_, lean_object* v___y_4022_){
_start:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; uint8_t v___x_4026_; 
v___x_4024_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4022_);
v___x_4025_ = l_Lean_Elab_pp_macroStack;
v___x_4026_ = l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8(v___x_4024_, v___x_4025_);
lean_dec_ref(v___x_4024_);
if (v___x_4026_ == 0)
{
lean_object* v___x_4027_; 
lean_dec(v_macroStack_4021_);
v___x_4027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4027_, 0, v_msgData_4020_);
return v___x_4027_;
}
else
{
if (lean_obj_tag(v_macroStack_4021_) == 0)
{
lean_object* v___x_4028_; 
v___x_4028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4028_, 0, v_msgData_4020_);
return v___x_4028_;
}
else
{
lean_object* v_head_4029_; lean_object* v_after_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4045_; 
v_head_4029_ = lean_ctor_get(v_macroStack_4021_, 0);
lean_inc(v_head_4029_);
v_after_4030_ = lean_ctor_get(v_head_4029_, 1);
v_isSharedCheck_4045_ = !lean_is_exclusive(v_head_4029_);
if (v_isSharedCheck_4045_ == 0)
{
lean_object* v_unused_4046_; 
v_unused_4046_ = lean_ctor_get(v_head_4029_, 0);
lean_dec(v_unused_4046_);
v___x_4032_ = v_head_4029_;
v_isShared_4033_ = v_isSharedCheck_4045_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_after_4030_);
lean_dec(v_head_4029_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4045_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4034_; lean_object* v___x_4036_; 
v___x_4034_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0);
if (v_isShared_4033_ == 0)
{
lean_ctor_set_tag(v___x_4032_, 7);
lean_ctor_set(v___x_4032_, 1, v___x_4034_);
lean_ctor_set(v___x_4032_, 0, v_msgData_4020_);
v___x_4036_ = v___x_4032_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_msgData_4020_);
lean_ctor_set(v_reuseFailAlloc_4044_, 1, v___x_4034_);
v___x_4036_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v_msgData_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; 
v___x_4037_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__2);
v___x_4038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4036_);
lean_ctor_set(v___x_4038_, 1, v___x_4037_);
v___x_4039_ = l_Lean_MessageData_ofSyntax(v_after_4030_);
v___x_4040_ = l_Lean_indentD(v___x_4039_);
v_msgData_4041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_4041_, 0, v___x_4038_);
lean_ctor_set(v_msgData_4041_, 1, v___x_4040_);
v___x_4042_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23(v_msgData_4041_, v_macroStack_4021_);
v___x_4043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4042_);
return v___x_4043_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___boxed(lean_object* v_msgData_4047_, lean_object* v_macroStack_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_){
_start:
{
lean_object* v_res_4051_; 
v_res_4051_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg(v_msgData_4047_, v_macroStack_4048_, v___y_4049_);
lean_dec_ref(v___y_4049_);
return v_res_4051_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg(lean_object* v_msg_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_){
_start:
{
lean_object* v_ref_4060_; lean_object* v_macroStack_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v_a_4064_; lean_object* v___x_4065_; lean_object* v_a_4066_; lean_object* v___x_4068_; uint8_t v_isShared_4069_; uint8_t v_isSharedCheck_4074_; 
v_ref_4060_ = lean_ctor_get(v___y_4057_, 2);
v_macroStack_4061_ = lean_ctor_get(v___y_4053_, 1);
v___x_4062_ = l_Lean_Elab_getBetterRef(v_ref_4060_, v_macroStack_4061_);
v___x_4063_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__15(v_msg_4052_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_);
v_a_4064_ = lean_ctor_get(v___x_4063_, 0);
lean_inc(v_a_4064_);
lean_dec_ref(v___x_4063_);
lean_inc(v_macroStack_4061_);
v___x_4065_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg(v_a_4064_, v_macroStack_4061_, v___y_4057_);
v_a_4066_ = lean_ctor_get(v___x_4065_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4065_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4068_ = v___x_4065_;
v_isShared_4069_ = v_isSharedCheck_4074_;
goto v_resetjp_4067_;
}
else
{
lean_inc(v_a_4066_);
lean_dec(v___x_4065_);
v___x_4068_ = lean_box(0);
v_isShared_4069_ = v_isSharedCheck_4074_;
goto v_resetjp_4067_;
}
v_resetjp_4067_:
{
lean_object* v___x_4070_; lean_object* v___x_4072_; 
v___x_4070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4062_);
lean_ctor_set(v___x_4070_, 1, v_a_4066_);
if (v_isShared_4069_ == 0)
{
lean_ctor_set_tag(v___x_4068_, 1);
lean_ctor_set(v___x_4068_, 0, v___x_4070_);
v___x_4072_ = v___x_4068_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v___x_4070_);
v___x_4072_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
return v___x_4072_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg___boxed(lean_object* v_msg_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
lean_object* v_res_4083_; 
v_res_4083_ = l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg(v_msg_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
lean_dec(v___y_4081_);
lean_dec_ref(v___y_4080_);
lean_dec(v___y_4079_);
lean_dec_ref(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
return v_res_4083_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__5(void){
_start:
{
lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
v___x_4092_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__0));
v___x_4093_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__4));
v___x_4094_ = l_Lean_Expr_const___override(v___x_4093_, v___x_4092_);
return v___x_4094_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__8(void){
_start:
{
lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; 
v___x_4099_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__0));
v___x_4100_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__7));
v___x_4101_ = l_Lean_Expr_const___override(v___x_4100_, v___x_4099_);
return v___x_4101_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__9(void){
_start:
{
lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; 
v___x_4102_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4);
v___x_4103_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__8, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__8_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__8);
v___x_4104_ = l_Lean_Expr_app___override(v___x_4103_, v___x_4102_);
return v___x_4104_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__14(void){
_start:
{
lean_object* v___x_4114_; lean_object* v___x_4115_; 
v___x_4114_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__13));
v___x_4115_ = l_String_toRawSubstring_x27(v___x_4114_);
return v___x_4115_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__29(void){
_start:
{
lean_object* v___x_4150_; 
v___x_4150_ = l_Array_mkArray0___redArg();
return v___x_4150_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__33(void){
_start:
{
lean_object* v___x_4154_; lean_object* v___x_4155_; 
v___x_4154_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__32));
v___x_4155_ = l_Lean_stringToMessageData(v___x_4154_);
return v___x_4155_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__35(void){
_start:
{
lean_object* v___x_4157_; lean_object* v___x_4158_; 
v___x_4157_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__34));
v___x_4158_ = l_Lean_stringToMessageData(v___x_4157_);
return v___x_4158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore(lean_object* v_e_4169_, lean_object* v_body_4170_, lean_object* v_ref_4171_, lean_object* v_expectedType_x3f_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_){
_start:
{
lean_object* v_toCold_4180_; lean_object* v_ref_4181_; lean_object* v_fileName_4182_; lean_object* v___x_4183_; 
v_toCold_4180_ = lean_ctor_get(v_a_4177_, 0);
v_ref_4181_ = lean_ctor_get(v_a_4177_, 2);
v_fileName_4182_ = lean_ctor_get(v_toCold_4180_, 0);
lean_inc_ref(v_fileName_4182_);
v___x_4183_ = lean_io_realpath(v_fileName_4182_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_object* v_a_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; uint8_t v___x_4187_; uint8_t v___y_4189_; size_t v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4288_; uint8_t v___y_4289_; lean_object* v___y_4290_; size_t v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4356_; uint8_t v___y_4357_; size_t v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; uint8_t v___y_4382_; lean_object* v___y_4383_; lean_object* v___y_4384_; lean_object* v___y_4385_; lean_object* v___y_4386_; uint8_t v___y_4387_; size_t v___y_4388_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v___y_4425_; lean_object* v___x_4491_; 
v_a_4184_ = lean_ctor_get(v___x_4183_, 0);
lean_inc(v_a_4184_);
lean_dec_ref_known(v___x_4183_, 1);
v___x_4185_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__0));
v___x_4186_ = lean_string_append(v_a_4184_, v___x_4185_);
v___x_4187_ = 0;
v___x_4491_ = l_Lean_Syntax_getPos_x3f(v_ref_4171_, v___x_4187_);
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_object* v___x_4492_; 
v___x_4492_ = lean_unsigned_to_nat(0u);
v___y_4425_ = v___x_4492_;
goto v___jp_4424_;
}
else
{
lean_object* v_val_4493_; 
v_val_4493_ = lean_ctor_get(v___x_4491_, 0);
lean_inc(v_val_4493_);
lean_dec_ref_known(v___x_4491_, 1);
v___y_4425_ = v_val_4493_;
goto v___jp_4424_;
}
v___jp_4188_:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; uint8_t v___x_4203_; uint8_t v___x_4204_; lean_object* v___x_4205_; 
v___x_4200_ = lean_box(2);
v___x_4201_ = l_Lean_Syntax_mkStrLit(v___y_4192_, v___x_4200_);
v___x_4202_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__2));
v___x_4203_ = 0;
v___x_4204_ = 0;
v___x_4205_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg(v___x_4202_, v___x_4203_, v___y_4193_, v___y_4191_, v___x_4204_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v_a_4206_; lean_object* v___x_4207_; 
v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_a_4206_);
lean_dec_ref_known(v___x_4205_, 1);
v___x_4207_ = l_Lean_Elab_Term_exprToSyntax(v_a_4206_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
if (lean_obj_tag(v___x_4207_) == 0)
{
lean_object* v_a_4208_; lean_object* v___x_4209_; lean_object* v_env_4210_; lean_object* v___x_4211_; lean_object* v_env_4212_; lean_object* v___x_4213_; lean_object* v_imports_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; size_t v_sz_4218_; lean_object* v___x_4219_; 
v_a_4208_ = lean_ctor_get(v___x_4207_, 0);
lean_inc(v_a_4208_);
lean_dec_ref_known(v___x_4207_, 1);
v___x_4209_ = lean_st_ref_get(v___y_4199_);
v_env_4210_ = lean_ctor_get(v___x_4209_, 0);
lean_inc_ref(v_env_4210_);
lean_dec(v___x_4209_);
v___x_4211_ = lean_st_ref_get(v___y_4199_);
v_env_4212_ = lean_ctor_get(v___x_4211_, 0);
lean_inc_ref(v_env_4212_);
lean_dec(v___x_4211_);
v___x_4213_ = l_Lean_Environment_header(v_env_4210_);
lean_dec_ref(v_env_4210_);
v_imports_4214_ = lean_ctor_get(v___x_4213_, 1);
lean_inc_ref(v_imports_4214_);
lean_dec_ref(v___x_4213_);
v___x_4215_ = l_Lean_Environment_mainModule(v_env_4212_);
lean_dec_ref(v_env_4212_);
v___x_4216_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_4216_, 0, v___x_4215_);
lean_ctor_set_uint8(v___x_4216_, sizeof(void*)*1, v___x_4187_);
lean_ctor_set_uint8(v___x_4216_, sizeof(void*)*1 + 1, v___y_4189_);
lean_ctor_set_uint8(v___x_4216_, sizeof(void*)*1 + 2, v___x_4187_);
v___x_4217_ = lean_array_push(v_imports_4214_, v___x_4216_);
v_sz_4218_ = lean_array_size(v___x_4217_);
v___x_4219_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg(v_sz_4218_, v___y_4190_, v___x_4217_);
if (lean_obj_tag(v___x_4219_) == 0)
{
lean_object* v_a_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
v_a_4220_ = lean_ctor_get(v___x_4219_, 0);
lean_inc(v_a_4220_);
lean_dec_ref_known(v___x_4219_, 1);
v___x_4221_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__5, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__5_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__5);
v___x_4222_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4);
v___x_4223_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__9, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__9_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__9);
v___x_4224_ = lean_array_to_list(v_a_4220_);
v___x_4225_ = l_List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7(v___x_4223_, v___x_4224_);
v___x_4226_ = l_Lean_mkAppB(v___x_4221_, v___x_4222_, v___x_4225_);
v___x_4227_ = l_Lean_Elab_Term_exprToSyntax(v___x_4226_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_object* v_toCold_4228_; lean_object* v_a_4229_; lean_object* v_ref_4230_; lean_object* v_quotContext_4231_; lean_object* v_currMacroScope_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; 
v_toCold_4228_ = lean_ctor_get(v___y_4198_, 0);
v_a_4229_ = lean_ctor_get(v___x_4227_, 0);
lean_inc(v_a_4229_);
lean_dec_ref_known(v___x_4227_, 1);
v_ref_4230_ = lean_ctor_get(v___y_4198_, 2);
v_quotContext_4231_ = lean_ctor_get(v_toCold_4228_, 8);
v_currMacroScope_4232_ = lean_ctor_get(v_toCold_4228_, 9);
v___x_4233_ = l_Lean_SourceInfo_fromRef(v_ref_4230_, v___x_4187_);
v___x_4234_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__11));
v___x_4235_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__12));
v___x_4236_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__14, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__14_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__14);
v___x_4237_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__16));
lean_inc(v_currMacroScope_4232_);
lean_inc(v_quotContext_4231_);
v___x_4238_ = l_Lean_addMacroScope(v_quotContext_4231_, v___x_4237_, v_currMacroScope_4232_);
v___x_4239_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__18));
lean_inc_n(v___x_4233_, 12);
v___x_4240_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4240_, 0, v___x_4233_);
lean_ctor_set(v___x_4240_, 1, v___x_4236_);
lean_ctor_set(v___x_4240_, 2, v___x_4238_);
lean_ctor_set(v___x_4240_, 3, v___x_4239_);
v___x_4241_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__20));
v___x_4242_ = l_Lean_Syntax_node3(v___x_4233_, v___x_4241_, v___x_4201_, v_a_4229_, v_a_4208_);
v___x_4243_ = l_Lean_Syntax_node2(v___x_4233_, v___x_4235_, v___x_4240_, v___x_4242_);
v___x_4244_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__21));
v___x_4245_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4245_, 0, v___x_4233_);
lean_ctor_set(v___x_4245_, 1, v___x_4244_);
v___x_4246_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__22));
v___x_4247_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__23));
v___x_4248_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4233_);
lean_ctor_set(v___x_4248_, 1, v___x_4246_);
v___x_4249_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__25));
v___x_4250_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__27));
v___x_4251_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__28));
v___x_4252_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4252_, 0, v___x_4233_);
lean_ctor_set(v___x_4252_, 1, v___x_4251_);
v___x_4253_ = l_Lean_Syntax_node1(v___x_4233_, v___x_4250_, v___x_4252_);
v___x_4254_ = l_Lean_Syntax_node1(v___x_4233_, v___x_4241_, v___x_4253_);
v___x_4255_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__29, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__29_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__29);
v___x_4256_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4256_, 0, v___x_4233_);
lean_ctor_set(v___x_4256_, 1, v___x_4241_);
lean_ctor_set(v___x_4256_, 2, v___x_4255_);
v___x_4257_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__30));
v___x_4258_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4258_, 0, v___x_4233_);
lean_ctor_set(v___x_4258_, 1, v___x_4257_);
v___x_4259_ = l_Lean_Syntax_node4(v___x_4233_, v___x_4249_, v___x_4254_, v___x_4256_, v___x_4258_, v_body_4170_);
v___x_4260_ = l_Lean_Syntax_node2(v___x_4233_, v___x_4247_, v___x_4248_, v___x_4259_);
v___x_4261_ = l_Lean_Syntax_node3(v___x_4233_, v___x_4234_, v___x_4243_, v___x_4245_, v___x_4260_);
v___x_4262_ = l_Lean_Elab_Term_elabTerm(v___x_4261_, v_expectedType_x3f_4172_, v___y_4189_, v___y_4189_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
return v___x_4262_;
}
else
{
lean_object* v_a_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4270_; 
lean_dec(v_a_4208_);
lean_dec(v___x_4201_);
lean_dec(v_expectedType_x3f_4172_);
lean_dec(v_body_4170_);
v_a_4263_ = lean_ctor_get(v___x_4227_, 0);
v_isSharedCheck_4270_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4270_ == 0)
{
v___x_4265_ = v___x_4227_;
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_a_4263_);
lean_dec(v___x_4227_);
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
v_reuseFailAlloc_4269_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4278_; 
lean_dec(v_a_4208_);
lean_dec(v___x_4201_);
lean_dec(v_expectedType_x3f_4172_);
lean_dec(v_body_4170_);
v_a_4271_ = lean_ctor_get(v___x_4219_, 0);
v_isSharedCheck_4278_ = !lean_is_exclusive(v___x_4219_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4273_ = v___x_4219_;
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_a_4271_);
lean_dec(v___x_4219_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v___x_4276_; 
if (v_isShared_4274_ == 0)
{
v___x_4276_ = v___x_4273_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_a_4271_);
v___x_4276_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
return v___x_4276_;
}
}
}
}
else
{
lean_object* v_a_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4286_; 
lean_dec(v___x_4201_);
lean_dec(v_expectedType_x3f_4172_);
lean_dec(v_body_4170_);
v_a_4279_ = lean_ctor_get(v___x_4207_, 0);
v_isSharedCheck_4286_ = !lean_is_exclusive(v___x_4207_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4281_ = v___x_4207_;
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_a_4279_);
lean_dec(v___x_4207_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v___x_4284_; 
if (v_isShared_4282_ == 0)
{
v___x_4284_ = v___x_4281_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_a_4279_);
v___x_4284_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
return v___x_4284_;
}
}
}
}
else
{
lean_dec(v___x_4201_);
lean_dec(v_expectedType_x3f_4172_);
lean_dec(v_body_4170_);
return v___x_4205_;
}
}
v___jp_4287_:
{
lean_object* v___x_4302_; lean_object* v___x_4303_; uint8_t v___x_4304_; 
v___x_4302_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4300_);
v___x_4303_ = l_Lean_Elab_inServer;
v___x_4304_ = l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8(v___x_4302_, v___x_4303_);
lean_dec_ref(v___x_4302_);
if (v___x_4304_ == 0)
{
lean_dec_ref(v___y_4294_);
lean_dec(v___y_4293_);
lean_dec_ref(v___y_4288_);
lean_dec(v_ref_4171_);
v___y_4189_ = v___y_4289_;
v___y_4190_ = v___y_4291_;
v___y_4191_ = v___y_4290_;
v___y_4192_ = v___y_4292_;
v___y_4193_ = v___y_4295_;
v___y_4194_ = v___y_4296_;
v___y_4195_ = v___y_4297_;
v___y_4196_ = v___y_4298_;
v___y_4197_ = v___y_4299_;
v___y_4198_ = v___y_4300_;
v___y_4199_ = v___y_4301_;
goto v___jp_4188_;
}
else
{
uint8_t v___x_4305_; 
v___x_4305_ = l_Lean_Expr_hasSorry(v___y_4294_);
if (v___x_4305_ == 0)
{
if (v___x_4304_ == 0)
{
lean_dec_ref(v___y_4294_);
lean_dec(v___y_4293_);
lean_dec_ref(v___y_4288_);
lean_dec(v_ref_4171_);
v___y_4189_ = v___y_4289_;
v___y_4190_ = v___y_4291_;
v___y_4191_ = v___y_4290_;
v___y_4192_ = v___y_4292_;
v___y_4193_ = v___y_4295_;
v___y_4194_ = v___y_4296_;
v___y_4195_ = v___y_4297_;
v___y_4196_ = v___y_4298_;
v___y_4197_ = v___y_4299_;
v___y_4198_ = v___y_4300_;
v___y_4199_ = v___y_4301_;
goto v___jp_4188_;
}
else
{
lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___f_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; 
v___x_4306_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__8));
lean_inc_ref(v___y_4295_);
v___x_4307_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson(v___y_4295_);
v___x_4308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4308_, 0, v___x_4306_);
lean_ctor_set(v___x_4308_, 1, v___x_4307_);
v___x_4309_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson___closed__13));
v___x_4310_ = l___private_Lean_Elab_Idbg_0__Lean_Idbg_exprToJson(v___y_4294_);
v___x_4311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4311_, 0, v___x_4309_);
lean_ctor_set(v___x_4311_, 1, v___x_4310_);
v___x_4312_ = lean_box(0);
v___x_4313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4313_, 0, v___x_4311_);
lean_ctor_set(v___x_4313_, 1, v___x_4312_);
v___x_4314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4308_);
lean_ctor_set(v___x_4314_, 1, v___x_4313_);
v___x_4315_ = l_Lean_Json_mkObj(v___x_4314_);
lean_dec_ref_known(v___x_4314_, 2);
lean_inc(v_ref_4171_);
v___f_4316_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4316_, 0, v___y_4288_);
lean_closure_set(v___f_4316_, 1, v___x_4315_);
lean_closure_set(v___f_4316_, 2, v_ref_4171_);
v___x_4317_ = l_IO_CancelToken_new();
v___x_4318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4318_, 0, v___x_4317_);
v___x_4319_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0));
v___x_4320_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__8));
v___x_4321_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__11));
lean_inc(v___y_4293_);
v___x_4322_ = l_Lean_Name_num___override(v___x_4321_, v___y_4293_);
v___x_4323_ = l_Lean_Name_str___override(v___x_4322_, v___x_4319_);
v___x_4324_ = l_Lean_Name_str___override(v___x_4323_, v___x_4320_);
v___x_4325_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__15));
v___x_4326_ = l_Lean_Name_str___override(v___x_4324_, v___x_4325_);
v___x_4327_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__31));
v___x_4328_ = l_Lean_Name_str___override(v___x_4326_, v___x_4327_);
v___x_4329_ = l_Lean_Name_toString(v___x_4328_, v___y_4289_);
lean_inc_ref(v___x_4318_);
v___x_4330_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___f_4316_, v___x_4318_, v___x_4329_, v___y_4300_, v___y_4301_);
if (lean_obj_tag(v___x_4330_) == 0)
{
lean_object* v_a_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; 
v_a_4331_ = lean_ctor_get(v___x_4330_, 0);
lean_inc(v_a_4331_);
lean_dec_ref_known(v___x_4330_, 1);
v___x_4332_ = lean_box(0);
v___x_4333_ = lean_apply_1(v_a_4331_, v___x_4332_);
v___x_4334_ = lean_io_as_task(v___x_4333_, v___y_4293_);
v___x_4335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4335_, 0, v_ref_4171_);
v___x_4336_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_4335_);
v___x_4337_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4337_, 0, v___x_4335_);
lean_ctor_set(v___x_4337_, 1, v___x_4336_);
lean_ctor_set(v___x_4337_, 2, v___x_4318_);
lean_ctor_set(v___x_4337_, 3, v___x_4334_);
v___x_4338_ = l_Lean_Core_logSnapshotTask___redArg(v___x_4337_, v___y_4301_);
if (lean_obj_tag(v___x_4338_) == 0)
{
lean_dec_ref_known(v___x_4338_, 1);
v___y_4189_ = v___y_4289_;
v___y_4190_ = v___y_4291_;
v___y_4191_ = v___y_4290_;
v___y_4192_ = v___y_4292_;
v___y_4193_ = v___y_4295_;
v___y_4194_ = v___y_4296_;
v___y_4195_ = v___y_4297_;
v___y_4196_ = v___y_4298_;
v___y_4197_ = v___y_4299_;
v___y_4198_ = v___y_4300_;
v___y_4199_ = v___y_4301_;
goto v___jp_4188_;
}
else
{
lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4346_; 
lean_dec_ref(v___y_4295_);
lean_dec_ref(v___y_4292_);
lean_dec_ref(v___y_4290_);
lean_dec(v_expectedType_x3f_4172_);
lean_dec(v_body_4170_);
v_a_4339_ = lean_ctor_get(v___x_4338_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4338_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4341_ = v___x_4338_;
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v___x_4338_);
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
lean_dec_ref_known(v___x_4318_, 1);
lean_dec_ref(v___y_4295_);
lean_dec(v___y_4293_);
lean_dec_ref(v___y_4292_);
lean_dec_ref(v___y_4290_);
lean_dec(v_expectedType_x3f_4172_);
lean_dec(v_ref_4171_);
lean_dec(v_body_4170_);
v_a_4347_ = lean_ctor_get(v___x_4330_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4330_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4349_ = v___x_4330_;
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_a_4347_);
lean_dec(v___x_4330_);
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
else
{
lean_dec_ref(v___y_4294_);
lean_dec(v___y_4293_);
lean_dec_ref(v___y_4288_);
lean_dec(v_ref_4171_);
v___y_4189_ = v___y_4289_;
v___y_4190_ = v___y_4291_;
v___y_4191_ = v___y_4290_;
v___y_4192_ = v___y_4292_;
v___y_4193_ = v___y_4295_;
v___y_4194_ = v___y_4296_;
v___y_4195_ = v___y_4297_;
v___y_4196_ = v___y_4298_;
v___y_4197_ = v___y_4299_;
v___y_4198_ = v___y_4300_;
v___y_4199_ = v___y_4301_;
goto v___jp_4188_;
}
}
}
v___jp_4355_:
{
uint8_t v___x_4370_; 
v___x_4370_ = l_Lean_Expr_hasMVar(v___y_4363_);
if (v___x_4370_ == 0)
{
v___y_4288_ = v___y_4356_;
v___y_4289_ = v___y_4357_;
v___y_4290_ = v___y_4359_;
v___y_4291_ = v___y_4358_;
v___y_4292_ = v___y_4360_;
v___y_4293_ = v___y_4361_;
v___y_4294_ = v___y_4362_;
v___y_4295_ = v___y_4363_;
v___y_4296_ = v___y_4364_;
v___y_4297_ = v___y_4365_;
v___y_4298_ = v___y_4366_;
v___y_4299_ = v___y_4367_;
v___y_4300_ = v___y_4368_;
v___y_4301_ = v___y_4369_;
goto v___jp_4287_;
}
else
{
lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4380_; 
lean_dec_ref(v___y_4363_);
lean_dec_ref(v___y_4362_);
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
lean_dec_ref(v___y_4359_);
lean_dec_ref(v___y_4356_);
lean_dec(v_expectedType_x3f_4172_);
lean_dec(v_ref_4171_);
lean_dec(v_body_4170_);
v___x_4371_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__33, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__33_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__33);
v___x_4372_ = l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg(v___x_4371_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_);
v_a_4373_ = lean_ctor_get(v___x_4372_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___x_4372_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4375_ = v___x_4372_;
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___x_4372_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4378_; 
if (v_isShared_4376_ == 0)
{
v___x_4378_ = v___x_4375_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v_a_4373_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
return v___x_4378_;
}
}
}
}
v___jp_4381_:
{
uint8_t v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___f_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___f_4400_; lean_object* v___x_4401_; 
v___x_4392_ = 1;
v___x_4393_ = lean_box(v___x_4187_);
v___x_4394_ = lean_box(v___y_4382_);
v___x_4395_ = lean_box(v___x_4392_);
lean_inc_ref(v___y_4383_);
v___f_4396_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__1___boxed), 13, 5);
lean_closure_set(v___f_4396_, 0, v___y_4383_);
lean_closure_set(v___f_4396_, 1, v___y_4386_);
lean_closure_set(v___f_4396_, 2, v___x_4393_);
lean_closure_set(v___f_4396_, 3, v___x_4394_);
lean_closure_set(v___f_4396_, 4, v___x_4395_);
v___x_4397_ = lean_box(v___x_4187_);
v___x_4398_ = lean_box(v___y_4382_);
v___x_4399_ = lean_box(v___x_4392_);
v___f_4400_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__2___boxed), 12, 5);
lean_closure_set(v___f_4400_, 0, v___y_4383_);
lean_closure_set(v___f_4400_, 1, v___y_4384_);
lean_closure_set(v___f_4400_, 2, v___x_4397_);
lean_closure_set(v___f_4400_, 3, v___x_4398_);
lean_closure_set(v___f_4400_, 4, v___x_4399_);
v___x_4401_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___redArg(v___y_4391_, v___f_4400_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_object* v_a_4402_; lean_object* v_fst_4403_; lean_object* v_snd_4404_; uint8_t v___x_4405_; 
v_a_4402_ = lean_ctor_get(v___x_4401_, 0);
lean_inc(v_a_4402_);
lean_dec_ref_known(v___x_4401_, 1);
v_fst_4403_ = lean_ctor_get(v_a_4402_, 0);
lean_inc(v_fst_4403_);
v_snd_4404_ = lean_ctor_get(v_a_4402_, 1);
lean_inc(v_snd_4404_);
lean_dec(v_a_4402_);
v___x_4405_ = l_Lean_Expr_hasMVar(v_fst_4403_);
if (v___x_4405_ == 0)
{
v___y_4356_ = v___y_4385_;
v___y_4357_ = v___y_4387_;
v___y_4358_ = v___y_4388_;
v___y_4359_ = v___f_4396_;
v___y_4360_ = v___y_4389_;
v___y_4361_ = v___y_4390_;
v___y_4362_ = v_fst_4403_;
v___y_4363_ = v_snd_4404_;
v___y_4364_ = v_a_4173_;
v___y_4365_ = v_a_4174_;
v___y_4366_ = v_a_4175_;
v___y_4367_ = v_a_4176_;
v___y_4368_ = v_a_4177_;
v___y_4369_ = v_a_4178_;
goto v___jp_4355_;
}
else
{
lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v_a_4408_; lean_object* v___x_4410_; uint8_t v_isShared_4411_; uint8_t v_isSharedCheck_4415_; 
lean_dec(v_snd_4404_);
lean_dec(v_fst_4403_);
lean_dec_ref(v___f_4396_);
lean_dec(v___y_4390_);
lean_dec_ref(v___y_4389_);
lean_dec_ref(v___y_4385_);
lean_dec(v_expectedType_x3f_4172_);
lean_dec(v_ref_4171_);
lean_dec(v_body_4170_);
v___x_4406_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__35, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__35_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__35);
v___x_4407_ = l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg(v___x_4406_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_);
v_a_4408_ = lean_ctor_get(v___x_4407_, 0);
v_isSharedCheck_4415_ = !lean_is_exclusive(v___x_4407_);
if (v_isSharedCheck_4415_ == 0)
{
v___x_4410_ = v___x_4407_;
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
else
{
lean_inc(v_a_4408_);
lean_dec(v___x_4407_);
v___x_4410_ = lean_box(0);
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
v_resetjp_4409_:
{
lean_object* v___x_4413_; 
if (v_isShared_4411_ == 0)
{
v___x_4413_ = v___x_4410_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_a_4408_);
v___x_4413_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
return v___x_4413_;
}
}
}
}
else
{
lean_object* v_a_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4423_; 
lean_dec_ref(v___f_4396_);
lean_dec(v___y_4390_);
lean_dec_ref(v___y_4389_);
lean_dec_ref(v___y_4385_);
lean_dec(v_expectedType_x3f_4172_);
lean_dec(v_ref_4171_);
lean_dec(v_body_4170_);
v_a_4416_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4418_ = v___x_4401_;
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_a_4416_);
lean_dec(v___x_4401_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
lean_object* v___x_4421_; 
if (v_isShared_4419_ == 0)
{
v___x_4421_ = v___x_4418_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v_a_4416_);
v___x_4421_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
return v___x_4421_;
}
}
}
}
v___jp_4424_:
{
lean_object* v_lctx_4426_; lean_object* v_decls_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; uint64_t v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
v_lctx_4426_ = lean_ctor_get(v_a_4175_, 2);
v_decls_4427_ = lean_ctor_get(v_lctx_4426_, 1);
v___x_4428_ = l_Nat_reprFast(v___y_4425_);
v___x_4429_ = lean_string_append(v___x_4186_, v___x_4428_);
lean_dec_ref(v___x_4428_);
v___x_4430_ = lean_string_hash(v___x_4429_);
lean_dec_ref(v___x_4429_);
v___x_4431_ = lean_uint64_to_nat(v___x_4430_);
v___x_4432_ = l_Nat_reprFast(v___x_4431_);
v___x_4433_ = lean_unsigned_to_nat(0u);
v___x_4434_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__36));
v___x_4435_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0(v_decls_4427_, v___x_4434_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_);
if (lean_obj_tag(v___x_4435_) == 0)
{
lean_object* v_a_4436_; size_t v_sz_4437_; size_t v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; uint8_t v___x_4441_; lean_object* v___x_4442_; 
v_a_4436_ = lean_ctor_get(v___x_4435_, 0);
lean_inc_n(v_a_4436_, 2);
lean_dec_ref_known(v___x_4435_, 1);
v_sz_4437_ = lean_array_size(v_a_4436_);
v___x_4438_ = ((size_t)0ULL);
v___x_4439_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__1(v_sz_4437_, v___x_4438_, v_a_4436_);
v___x_4440_ = lean_box(0);
v___x_4441_ = 1;
v___x_4442_ = l_Lean_Elab_Term_elabTerm(v_e_4169_, v___x_4440_, v___x_4441_, v___x_4441_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_);
if (lean_obj_tag(v___x_4442_) == 0)
{
lean_object* v_a_4443_; lean_object* v___x_4444_; 
v_a_4443_ = lean_ctor_get(v___x_4442_, 0);
lean_inc(v_a_4443_);
lean_dec_ref_known(v___x_4442_, 1);
v___x_4444_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_4187_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_);
if (lean_obj_tag(v___x_4444_) == 0)
{
lean_object* v___x_4445_; lean_object* v_a_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; 
lean_dec_ref_known(v___x_4444_, 1);
v___x_4445_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(v_a_4443_, v_a_4176_);
v_a_4446_ = lean_ctor_get(v___x_4445_, 0);
lean_inc(v_a_4446_);
lean_dec_ref(v___x_4445_);
v___x_4447_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__38));
v___x_4448_ = lean_unsigned_to_nat(1u);
v___x_4449_ = lean_mk_empty_array_with_capacity(v___x_4448_);
lean_inc_ref(v___x_4449_);
v___x_4450_ = lean_array_push(v___x_4449_, v_a_4446_);
v___x_4451_ = l_Lean_Meta_mkAppM(v___x_4447_, v___x_4450_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_);
if (lean_obj_tag(v___x_4451_) == 0)
{
lean_object* v_a_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; 
v_a_4452_ = lean_ctor_get(v___x_4451_, 0);
lean_inc(v_a_4452_);
lean_dec_ref_known(v___x_4451_, 1);
v___x_4453_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__41));
lean_inc_ref(v___x_4449_);
v___x_4454_ = lean_array_push(v___x_4449_, v_a_4452_);
v___x_4455_ = l_Lean_Meta_mkAppM(v___x_4453_, v___x_4454_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_);
if (lean_obj_tag(v___x_4455_) == 0)
{
lean_object* v_a_4456_; lean_object* v___x_4457_; 
v_a_4456_ = lean_ctor_get(v___x_4455_, 0);
lean_inc(v_a_4456_);
lean_dec_ref_known(v___x_4455_, 1);
v___x_4457_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_4187_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_);
if (lean_obj_tag(v___x_4457_) == 0)
{
lean_object* v___x_4458_; lean_object* v_a_4459_; lean_object* v___x_4460_; uint8_t v___x_4461_; 
lean_dec_ref_known(v___x_4457_, 1);
v___x_4458_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(v_a_4456_, v_a_4176_);
v_a_4459_ = lean_ctor_get(v___x_4458_, 0);
lean_inc(v_a_4459_);
lean_dec_ref(v___x_4458_);
v___x_4460_ = lean_array_get_size(v_a_4436_);
v___x_4461_ = lean_nat_dec_lt(v___x_4433_, v___x_4460_);
if (v___x_4461_ == 0)
{
lean_dec(v_a_4436_);
lean_inc_ref(v_lctx_4426_);
lean_inc_ref(v___x_4432_);
v___y_4382_ = v___x_4441_;
v___y_4383_ = v___x_4439_;
v___y_4384_ = v_a_4459_;
v___y_4385_ = v___x_4432_;
v___y_4386_ = v___x_4449_;
v___y_4387_ = v___x_4441_;
v___y_4388_ = v___x_4438_;
v___y_4389_ = v___x_4432_;
v___y_4390_ = v___x_4433_;
v___y_4391_ = v_lctx_4426_;
goto v___jp_4381_;
}
else
{
uint8_t v___x_4462_; 
v___x_4462_ = lean_nat_dec_le(v___x_4460_, v___x_4460_);
if (v___x_4462_ == 0)
{
if (v___x_4461_ == 0)
{
lean_dec(v_a_4436_);
lean_inc_ref(v_lctx_4426_);
lean_inc_ref(v___x_4432_);
v___y_4382_ = v___x_4441_;
v___y_4383_ = v___x_4439_;
v___y_4384_ = v_a_4459_;
v___y_4385_ = v___x_4432_;
v___y_4386_ = v___x_4449_;
v___y_4387_ = v___x_4441_;
v___y_4388_ = v___x_4438_;
v___y_4389_ = v___x_4432_;
v___y_4390_ = v___x_4433_;
v___y_4391_ = v_lctx_4426_;
goto v___jp_4381_;
}
else
{
size_t v___x_4463_; lean_object* v___x_4464_; 
v___x_4463_ = lean_usize_of_nat(v___x_4460_);
lean_inc_ref(v_lctx_4426_);
v___x_4464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__11(v_a_4436_, v___x_4438_, v___x_4463_, v_lctx_4426_);
lean_dec(v_a_4436_);
lean_inc_ref(v___x_4432_);
v___y_4382_ = v___x_4441_;
v___y_4383_ = v___x_4439_;
v___y_4384_ = v_a_4459_;
v___y_4385_ = v___x_4432_;
v___y_4386_ = v___x_4449_;
v___y_4387_ = v___x_4441_;
v___y_4388_ = v___x_4438_;
v___y_4389_ = v___x_4432_;
v___y_4390_ = v___x_4433_;
v___y_4391_ = v___x_4464_;
goto v___jp_4381_;
}
}
else
{
size_t v___x_4465_; lean_object* v___x_4466_; 
v___x_4465_ = lean_usize_of_nat(v___x_4460_);
lean_inc_ref(v_lctx_4426_);
v___x_4466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__11(v_a_4436_, v___x_4438_, v___x_4465_, v_lctx_4426_);
lean_dec(v_a_4436_);
lean_inc_ref(v___x_4432_);
v___y_4382_ = v___x_4441_;
v___y_4383_ = v___x_4439_;
v___y_4384_ = v_a_4459_;
v___y_4385_ = v___x_4432_;
v___y_4386_ = v___x_4449_;
v___y_4387_ = v___x_4441_;
v___y_4388_ = v___x_4438_;
v___y_4389_ = v___x_4432_;
v___y_4390_ = v___x_4433_;
v___y_4391_ = v___x_4466_;
goto v___jp_4381_;
}
}
}
else
{
lean_object* v_a_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4474_; 
lean_dec(v_a_4456_);
lean_dec_ref(v___x_4449_);
lean_dec_ref(v___x_4439_);
lean_dec(v_a_4436_);
lean_dec_ref(v___x_4432_);
lean_dec(v_expectedType_x3f_4172_);
lean_dec(v_ref_4171_);
lean_dec(v_body_4170_);
v_a_4467_ = lean_ctor_get(v___x_4457_, 0);
v_isSharedCheck_4474_ = !lean_is_exclusive(v___x_4457_);
if (v_isSharedCheck_4474_ == 0)
{
v___x_4469_ = v___x_4457_;
v_isShared_4470_ = v_isSharedCheck_4474_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_a_4467_);
lean_dec(v___x_4457_);
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
else
{
lean_dec_ref(v___x_4449_);
lean_dec_ref(v___x_4439_);
lean_dec(v_a_4436_);
lean_dec_ref(v___x_4432_);
lean_dec(v_expectedType_x3f_4172_);
lean_dec(v_ref_4171_);
lean_dec(v_body_4170_);
return v___x_4455_;
}
}
else
{
lean_dec_ref(v___x_4449_);
lean_dec_ref(v___x_4439_);
lean_dec(v_a_4436_);
lean_dec_ref(v___x_4432_);
lean_dec(v_expectedType_x3f_4172_);
lean_dec(v_ref_4171_);
lean_dec(v_body_4170_);
return v___x_4451_;
}
}
else
{
lean_object* v_a_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4482_; 
lean_dec(v_a_4443_);
lean_dec_ref(v___x_4439_);
lean_dec(v_a_4436_);
lean_dec_ref(v___x_4432_);
lean_dec(v_expectedType_x3f_4172_);
lean_dec(v_ref_4171_);
lean_dec(v_body_4170_);
v_a_4475_ = lean_ctor_get(v___x_4444_, 0);
v_isSharedCheck_4482_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4482_ == 0)
{
v___x_4477_ = v___x_4444_;
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_a_4475_);
lean_dec(v___x_4444_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v___x_4480_; 
if (v_isShared_4478_ == 0)
{
v___x_4480_ = v___x_4477_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v_a_4475_);
v___x_4480_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
return v___x_4480_;
}
}
}
}
else
{
lean_dec_ref(v___x_4439_);
lean_dec(v_a_4436_);
lean_dec_ref(v___x_4432_);
lean_dec(v_expectedType_x3f_4172_);
lean_dec(v_ref_4171_);
lean_dec(v_body_4170_);
return v___x_4442_;
}
}
else
{
lean_object* v_a_4483_; lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4490_; 
lean_dec_ref(v___x_4432_);
lean_dec(v_expectedType_x3f_4172_);
lean_dec(v_ref_4171_);
lean_dec(v_body_4170_);
lean_dec(v_e_4169_);
v_a_4483_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4490_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4490_ == 0)
{
v___x_4485_ = v___x_4435_;
v_isShared_4486_ = v_isSharedCheck_4490_;
goto v_resetjp_4484_;
}
else
{
lean_inc(v_a_4483_);
lean_dec(v___x_4435_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4490_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
lean_object* v___x_4488_; 
if (v_isShared_4486_ == 0)
{
v___x_4488_ = v___x_4485_;
goto v_reusejp_4487_;
}
else
{
lean_object* v_reuseFailAlloc_4489_; 
v_reuseFailAlloc_4489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4489_, 0, v_a_4483_);
v___x_4488_ = v_reuseFailAlloc_4489_;
goto v_reusejp_4487_;
}
v_reusejp_4487_:
{
return v___x_4488_;
}
}
}
}
}
else
{
lean_object* v_a_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4505_; 
lean_dec(v_expectedType_x3f_4172_);
lean_dec(v_ref_4171_);
lean_dec(v_body_4170_);
lean_dec(v_e_4169_);
v_a_4494_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4505_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4505_ == 0)
{
v___x_4496_ = v___x_4183_;
v_isShared_4497_ = v_isSharedCheck_4505_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_a_4494_);
lean_dec(v___x_4183_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4505_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4503_; 
v___x_4498_ = lean_io_error_to_string(v_a_4494_);
v___x_4499_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4499_, 0, v___x_4498_);
v___x_4500_ = l_Lean_MessageData_ofFormat(v___x_4499_);
lean_inc(v_ref_4181_);
v___x_4501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4501_, 0, v_ref_4181_);
lean_ctor_set(v___x_4501_, 1, v___x_4500_);
if (v_isShared_4497_ == 0)
{
lean_ctor_set(v___x_4496_, 0, v___x_4501_);
v___x_4503_ = v___x_4496_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v___x_4501_);
v___x_4503_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
return v___x_4503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___boxed(lean_object* v_e_4506_, lean_object* v_body_4507_, lean_object* v_ref_4508_, lean_object* v_expectedType_x3f_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_){
_start:
{
lean_object* v_res_4517_; 
v_res_4517_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore(v_e_4506_, v_body_4507_, v_ref_4508_, v_expectedType_x3f_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_);
lean_dec(v_a_4515_);
lean_dec_ref(v_a_4514_);
lean_dec(v_a_4513_);
lean_dec_ref(v_a_4512_);
lean_dec(v_a_4511_);
lean_dec_ref(v_a_4510_);
return v_res_4517_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2(lean_object* v_00_u03b2_4518_, lean_object* v_x_4519_, lean_object* v_x_4520_, lean_object* v_x_4521_){
_start:
{
lean_object* v___x_4522_; 
v___x_4522_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2___redArg(v_x_4519_, v_x_4520_, v_x_4521_);
return v___x_4522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6(size_t v_sz_4523_, size_t v_i_4524_, lean_object* v_bs_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_){
_start:
{
lean_object* v___x_4533_; 
v___x_4533_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg(v_sz_4523_, v_i_4524_, v_bs_4525_);
return v___x_4533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___boxed(lean_object* v_sz_4534_, lean_object* v_i_4535_, lean_object* v_bs_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_){
_start:
{
size_t v_sz_boxed_4544_; size_t v_i_boxed_4545_; lean_object* v_res_4546_; 
v_sz_boxed_4544_ = lean_unbox_usize(v_sz_4534_);
lean_dec(v_sz_4534_);
v_i_boxed_4545_ = lean_unbox_usize(v_i_4535_);
lean_dec(v_i_4535_);
v_res_4546_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6(v_sz_boxed_4544_, v_i_boxed_4545_, v_bs_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_);
lean_dec(v___y_4542_);
lean_dec_ref(v___y_4541_);
lean_dec(v___y_4540_);
lean_dec_ref(v___y_4539_);
lean_dec(v___y_4538_);
lean_dec_ref(v___y_4537_);
return v_res_4546_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10(lean_object* v_00_u03b1_4547_, lean_object* v_msg_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_){
_start:
{
lean_object* v___x_4556_; 
v___x_4556_ = l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg(v_msg_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_);
return v___x_4556_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___boxed(lean_object* v_00_u03b1_4557_, lean_object* v_msg_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_){
_start:
{
lean_object* v_res_4566_; 
v_res_4566_ = l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10(v_00_u03b1_4557_, v_msg_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
lean_dec(v___y_4564_);
lean_dec_ref(v___y_4563_);
lean_dec(v___y_4562_);
lean_dec_ref(v___y_4561_);
lean_dec(v___y_4560_);
lean_dec_ref(v___y_4559_);
return v_res_4566_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4(lean_object* v_00_u03b2_4567_, lean_object* v_x_4568_, size_t v_x_4569_, size_t v_x_4570_, lean_object* v_x_4571_, lean_object* v_x_4572_){
_start:
{
lean_object* v___x_4573_; 
v___x_4573_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg(v_x_4568_, v_x_4569_, v_x_4570_, v_x_4571_, v_x_4572_);
return v___x_4573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4574_, lean_object* v_x_4575_, lean_object* v_x_4576_, lean_object* v_x_4577_, lean_object* v_x_4578_, lean_object* v_x_4579_){
_start:
{
size_t v_x_36704__boxed_4580_; size_t v_x_36705__boxed_4581_; lean_object* v_res_4582_; 
v_x_36704__boxed_4580_ = lean_unbox_usize(v_x_4576_);
lean_dec(v_x_4576_);
v_x_36705__boxed_4581_ = lean_unbox_usize(v_x_4577_);
lean_dec(v_x_4577_);
v_res_4582_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4(v_00_u03b2_4574_, v_x_4575_, v_x_36704__boxed_4580_, v_x_36705__boxed_4581_, v_x_4578_, v_x_4579_);
return v_res_4582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16(lean_object* v_msgData_4583_, lean_object* v_macroStack_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_){
_start:
{
lean_object* v___x_4592_; 
v___x_4592_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg(v_msgData_4583_, v_macroStack_4584_, v___y_4589_);
return v___x_4592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___boxed(lean_object* v_msgData_4593_, lean_object* v_macroStack_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_){
_start:
{
lean_object* v_res_4602_; 
v_res_4602_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16(v_msgData_4593_, v_macroStack_4594_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_);
lean_dec(v___y_4600_);
lean_dec_ref(v___y_4599_);
lean_dec(v___y_4598_);
lean_dec_ref(v___y_4597_);
lean_dec(v___y_4596_);
lean_dec_ref(v___y_4595_);
return v_res_4602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8(lean_object* v_as_4603_, size_t v_sz_4604_, size_t v_i_4605_, lean_object* v_b_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_){
_start:
{
lean_object* v___x_4614_; 
v___x_4614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___redArg(v_as_4603_, v_sz_4604_, v_i_4605_, v_b_4606_);
return v___x_4614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___boxed(lean_object* v_as_4615_, lean_object* v_sz_4616_, lean_object* v_i_4617_, lean_object* v_b_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_){
_start:
{
size_t v_sz_boxed_4626_; size_t v_i_boxed_4627_; lean_object* v_res_4628_; 
v_sz_boxed_4626_ = lean_unbox_usize(v_sz_4616_);
lean_dec(v_sz_4616_);
v_i_boxed_4627_ = lean_unbox_usize(v_i_4617_);
lean_dec(v_i_4617_);
v_res_4628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8(v_as_4615_, v_sz_boxed_4626_, v_i_boxed_4627_, v_b_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_);
lean_dec(v___y_4624_);
lean_dec_ref(v___y_4623_);
lean_dec(v___y_4622_);
lean_dec_ref(v___y_4621_);
lean_dec(v___y_4620_);
lean_dec_ref(v___y_4619_);
lean_dec_ref(v_as_4615_);
return v_res_4628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12(lean_object* v_00_u03b2_4629_, lean_object* v_n_4630_, lean_object* v_k_4631_, lean_object* v_v_4632_){
_start:
{
lean_object* v___x_4633_; 
v___x_4633_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12___redArg(v_n_4630_, v_k_4631_, v_v_4632_);
return v___x_4633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13(lean_object* v_00_u03b2_4634_, size_t v_depth_4635_, lean_object* v_keys_4636_, lean_object* v_vals_4637_, lean_object* v_heq_4638_, lean_object* v_i_4639_, lean_object* v_entries_4640_){
_start:
{
lean_object* v___x_4641_; 
v___x_4641_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___redArg(v_depth_4635_, v_keys_4636_, v_vals_4637_, v_i_4639_, v_entries_4640_);
return v___x_4641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___boxed(lean_object* v_00_u03b2_4642_, lean_object* v_depth_4643_, lean_object* v_keys_4644_, lean_object* v_vals_4645_, lean_object* v_heq_4646_, lean_object* v_i_4647_, lean_object* v_entries_4648_){
_start:
{
size_t v_depth_boxed_4649_; lean_object* v_res_4650_; 
v_depth_boxed_4649_ = lean_unbox_usize(v_depth_4643_);
lean_dec(v_depth_4643_);
v_res_4650_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13(v_00_u03b2_4642_, v_depth_boxed_4649_, v_keys_4644_, v_vals_4645_, v_heq_4646_, v_i_4647_, v_entries_4648_);
lean_dec_ref(v_vals_4645_);
lean_dec_ref(v_keys_4644_);
return v_res_4650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15(lean_object* v_as_4651_, size_t v_sz_4652_, size_t v_i_4653_, lean_object* v_b_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_){
_start:
{
lean_object* v___x_4662_; 
v___x_4662_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___redArg(v_as_4651_, v_sz_4652_, v_i_4653_, v_b_4654_);
return v___x_4662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___boxed(lean_object* v_as_4663_, lean_object* v_sz_4664_, lean_object* v_i_4665_, lean_object* v_b_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_){
_start:
{
size_t v_sz_boxed_4674_; size_t v_i_boxed_4675_; lean_object* v_res_4676_; 
v_sz_boxed_4674_ = lean_unbox_usize(v_sz_4664_);
lean_dec(v_sz_4664_);
v_i_boxed_4675_ = lean_unbox_usize(v_i_4665_);
lean_dec(v_i_4665_);
v_res_4676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15(v_as_4663_, v_sz_boxed_4674_, v_i_boxed_4675_, v_b_4666_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_);
lean_dec(v___y_4672_);
lean_dec_ref(v___y_4671_);
lean_dec(v___y_4670_);
lean_dec_ref(v___y_4669_);
lean_dec(v___y_4668_);
lean_dec_ref(v___y_4667_);
lean_dec_ref(v_as_4663_);
return v_res_4676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12_spec__20(lean_object* v_00_u03b2_4677_, lean_object* v_x_4678_, lean_object* v_x_4679_, lean_object* v_x_4680_, lean_object* v_x_4681_){
_start:
{
lean_object* v___x_4682_; 
v___x_4682_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12_spec__20___redArg(v_x_4678_, v_x_4679_, v_x_4680_, v_x_4681_);
return v___x_4682_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; 
v___x_4683_ = lean_box(0);
v___x_4684_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_4685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4685_, 0, v___x_4684_);
lean_ctor_set(v___x_4685_, 1, v___x_4683_);
return v___x_4685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg(){
_start:
{
lean_object* v___x_4687_; lean_object* v___x_4688_; 
v___x_4687_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0);
v___x_4688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4688_, 0, v___x_4687_);
return v___x_4688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___boxed(lean_object* v___y_4689_){
_start:
{
lean_object* v_res_4690_; 
v_res_4690_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg();
return v_res_4690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0(lean_object* v_00_u03b1_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_){
_start:
{
lean_object* v___x_4699_; 
v___x_4699_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg();
return v___x_4699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___boxed(lean_object* v_00_u03b1_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_){
_start:
{
lean_object* v_res_4708_; 
v_res_4708_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0(v_00_u03b1_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_);
lean_dec(v___y_4706_);
lean_dec_ref(v___y_4705_);
lean_dec(v___y_4704_);
lean_dec_ref(v___y_4703_);
lean_dec(v___y_4702_);
lean_dec_ref(v___y_4701_);
return v_res_4708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm(lean_object* v_stx_4715_, lean_object* v_expectedType_x3f_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_){
_start:
{
lean_object* v___x_4724_; uint8_t v___x_4725_; 
v___x_4724_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__1));
lean_inc(v_stx_4715_);
v___x_4725_ = l_Lean_Syntax_isOfKind(v_stx_4715_, v___x_4724_);
if (v___x_4725_ == 0)
{
lean_object* v___x_4726_; 
lean_dec(v_expectedType_x3f_4716_);
lean_dec(v_stx_4715_);
v___x_4726_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg();
return v___x_4726_;
}
else
{
lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v_body_4730_; lean_object* v___x_4731_; 
v___x_4727_ = lean_unsigned_to_nat(1u);
v___x_4728_ = l_Lean_Syntax_getArg(v_stx_4715_, v___x_4727_);
v___x_4729_ = lean_unsigned_to_nat(3u);
v_body_4730_ = l_Lean_Syntax_getArg(v_stx_4715_, v___x_4729_);
v___x_4731_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore(v___x_4728_, v_body_4730_, v_stx_4715_, v_expectedType_x3f_4716_, v_a_4717_, v_a_4718_, v_a_4719_, v_a_4720_, v_a_4721_, v_a_4722_);
return v___x_4731_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___boxed(lean_object* v_stx_4732_, lean_object* v_expectedType_x3f_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_){
_start:
{
lean_object* v_res_4741_; 
v_res_4741_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm(v_stx_4732_, v_expectedType_x3f_4733_, v_a_4734_, v_a_4735_, v_a_4736_, v_a_4737_, v_a_4738_, v_a_4739_);
lean_dec(v_a_4739_);
lean_dec_ref(v_a_4738_);
lean_dec(v_a_4737_);
lean_dec_ref(v_a_4736_);
lean_dec(v_a_4735_);
lean_dec_ref(v_a_4734_);
return v_res_4741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1(){
_start:
{
lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; 
v___x_4747_ = l_Lean_Elab_Term_termElabAttribute;
v___x_4748_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__1));
v___x_4749_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1___closed__1));
v___x_4750_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___boxed), 9, 0);
v___x_4751_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4747_, v___x_4748_, v___x_4749_, v___x_4750_);
return v___x_4751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1___boxed(lean_object* v_a_4752_){
_start:
{
lean_object* v_res_4753_; 
v_res_4753_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1();
return v_res_4753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___redArg(){
_start:
{
lean_object* v___x_4755_; lean_object* v___x_4756_; 
v___x_4755_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0);
v___x_4756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4756_, 0, v___x_4755_);
return v___x_4756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___redArg___boxed(lean_object* v___y_4757_){
_start:
{
lean_object* v_res_4758_; 
v_res_4758_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___redArg();
return v_res_4758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0(lean_object* v_00_u03b1_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_){
_start:
{
lean_object* v___x_4768_; 
v___x_4768_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___redArg();
return v___x_4768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___boxed(lean_object* v_00_u03b1_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_){
_start:
{
lean_object* v_res_4778_; 
v_res_4778_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0(v_00_u03b1_4769_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_, v___y_4774_, v___y_4775_, v___y_4776_);
lean_dec(v___y_4776_);
lean_dec_ref(v___y_4775_);
lean_dec(v___y_4774_);
lean_dec_ref(v___y_4773_);
lean_dec(v___y_4772_);
lean_dec_ref(v___y_4771_);
lean_dec_ref(v___y_4770_);
return v_res_4778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___lam__0(lean_object* v_a_4779_, lean_object* v___x_4780_, lean_object* v_stx_4781_, lean_object* v_body_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_){
_start:
{
lean_object* v___x_4791_; lean_object* v___x_4792_; 
v___x_4791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4791_, 0, v_a_4779_);
v___x_4792_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore(v___x_4780_, v_body_4782_, v_stx_4781_, v___x_4791_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_);
return v___x_4792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___lam__0___boxed(lean_object* v_a_4793_, lean_object* v___x_4794_, lean_object* v_stx_4795_, lean_object* v_body_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_){
_start:
{
lean_object* v_res_4805_; 
v_res_4805_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___lam__0(v_a_4793_, v___x_4794_, v_stx_4795_, v_body_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_, v___y_4802_, v___y_4803_);
lean_dec(v___y_4803_);
lean_dec_ref(v___y_4802_);
lean_dec(v___y_4801_);
lean_dec_ref(v___y_4800_);
lean_dec(v___y_4799_);
lean_dec_ref(v___y_4798_);
lean_dec_ref(v___y_4797_);
return v_res_4805_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__2(void){
_start:
{
lean_object* v___x_4809_; lean_object* v___x_4810_; 
v___x_4809_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__1));
v___x_4810_ = l_Lean_MessageData_ofFormat(v___x_4809_);
return v___x_4810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg(lean_object* v_stx_4811_, lean_object* v_dec_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_){
_start:
{
lean_object* v___x_4821_; uint8_t v___x_4822_; 
v___x_4821_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4));
lean_inc(v_stx_4811_);
v___x_4822_ = l_Lean_Syntax_isOfKind(v_stx_4811_, v___x_4821_);
if (v___x_4822_ == 0)
{
lean_object* v___x_4823_; 
lean_dec_ref(v_dec_4812_);
lean_dec(v_stx_4811_);
v___x_4823_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___redArg();
return v___x_4823_;
}
else
{
lean_object* v_doBlockResultType_4824_; lean_object* v___x_4825_; lean_object* v_tk_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; 
v_doBlockResultType_4824_ = lean_ctor_get(v_a_4813_, 3);
v___x_4825_ = lean_unsigned_to_nat(0u);
v_tk_4826_ = l_Lean_Syntax_getArg(v_stx_4811_, v___x_4825_);
v___x_4827_ = lean_unsigned_to_nat(1u);
v___x_4828_ = l_Lean_Syntax_getArg(v_stx_4811_, v___x_4827_);
lean_inc_ref(v_doBlockResultType_4824_);
v___x_4829_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_4824_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_);
if (lean_obj_tag(v___x_4829_) == 0)
{
lean_object* v_a_4830_; lean_object* v___f_4831_; lean_object* v___x_4832_; 
v_a_4830_ = lean_ctor_get(v___x_4829_, 0);
lean_inc(v_a_4830_);
lean_dec_ref_known(v___x_4829_, 1);
v___f_4831_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___lam__0___boxed), 12, 3);
lean_closure_set(v___f_4831_, 0, v_a_4830_);
lean_closure_set(v___f_4831_, 1, v___x_4828_);
lean_closure_set(v___f_4831_, 2, v_stx_4811_);
v___x_4832_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4812_, v_tk_4826_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_);
lean_dec(v_tk_4826_);
if (lean_obj_tag(v___x_4832_) == 0)
{
lean_object* v_a_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; 
v_a_4833_ = lean_ctor_get(v___x_4832_, 0);
lean_inc(v_a_4833_);
lean_dec_ref_known(v___x_4832_, 1);
v___x_4834_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__2, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__2_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__2);
v___x_4835_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4835_, 0, v_a_4833_);
v___x_4836_ = lean_box(0);
v___x_4837_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_4834_, v___x_4835_, v___f_4831_, v___x_4836_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_);
return v___x_4837_;
}
else
{
lean_object* v_a_4838_; lean_object* v___x_4840_; uint8_t v_isShared_4841_; uint8_t v_isSharedCheck_4845_; 
lean_dec_ref(v___f_4831_);
v_a_4838_ = lean_ctor_get(v___x_4832_, 0);
v_isSharedCheck_4845_ = !lean_is_exclusive(v___x_4832_);
if (v_isSharedCheck_4845_ == 0)
{
v___x_4840_ = v___x_4832_;
v_isShared_4841_ = v_isSharedCheck_4845_;
goto v_resetjp_4839_;
}
else
{
lean_inc(v_a_4838_);
lean_dec(v___x_4832_);
v___x_4840_ = lean_box(0);
v_isShared_4841_ = v_isSharedCheck_4845_;
goto v_resetjp_4839_;
}
v_resetjp_4839_:
{
lean_object* v___x_4843_; 
if (v_isShared_4841_ == 0)
{
v___x_4843_ = v___x_4840_;
goto v_reusejp_4842_;
}
else
{
lean_object* v_reuseFailAlloc_4844_; 
v_reuseFailAlloc_4844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4844_, 0, v_a_4838_);
v___x_4843_ = v_reuseFailAlloc_4844_;
goto v_reusejp_4842_;
}
v_reusejp_4842_:
{
return v___x_4843_;
}
}
}
}
else
{
lean_dec(v___x_4828_);
lean_dec(v_tk_4826_);
lean_dec_ref(v_dec_4812_);
lean_dec(v_stx_4811_);
return v___x_4829_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___boxed(lean_object* v_stx_4846_, lean_object* v_dec_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_){
_start:
{
lean_object* v_res_4856_; 
v_res_4856_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg(v_stx_4846_, v_dec_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_, v_a_4854_);
lean_dec(v_a_4854_);
lean_dec_ref(v_a_4853_);
lean_dec(v_a_4852_);
lean_dec_ref(v_a_4851_);
lean_dec(v_a_4850_);
lean_dec_ref(v_a_4849_);
lean_dec_ref(v_a_4848_);
return v_res_4856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1(){
_start:
{
lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; 
v___x_4862_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4863_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4));
v___x_4864_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1___closed__1));
v___x_4865_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___boxed), 10, 0);
v___x_4866_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4862_, v___x_4863_, v___x_4864_, v___x_4865_);
return v___x_4866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1___boxed(lean_object* v_a_4867_){
_start:
{
lean_object* v_res_4868_; 
v_res_4868_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1();
return v_res_4868_;
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
