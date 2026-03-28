// Lean compiler output
// Module: Lean.AddDecl
// Imports: public import Lean.Meta.Sorry public import Lean.Util.CollectAxioms public import Lean.OriginalConstKind import all Lean.OriginalConstKind
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Declaration_getNames(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_debug_skipKernelTC;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_addDeclCore(lean_object*, size_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
uint8_t l_Lean_Declaration_hasSorry(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t l_Lean_Expr_isSyntheticSorry(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getSorry_x3f(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_isPrivateName___boxed(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Environment_registerNamespace(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Declaration_getTopLevelNames(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqDefinitionSafety_beq(uint8_t, uint8_t);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* lean_add_decl(lean_object*, size_t, lean_object*, lean_object*);
lean_object* lean_add_decl_without_checking(lean_object*, lean_object*);
lean_object* l_Lean_Environment_AddConstAsyncResult_commitConst(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_async;
lean_object* l_IO_CancelToken_new();
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Core_logSnapshotTask___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_addConstAsync(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t);
uint8_t l_Lean_ConstantKind_ofConstantInfo(lean_object*);
uint8_t l_List_all___redArg(lean_object*, lean_object*);
extern lean_object* l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic;
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
lean_object* lean_elab_environment_to_kernel_env(lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_AddDecl_0__Lean_isNamespaceName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_isNamespaceName___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_registerNamePrefixes_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "warn"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__1_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sorry"};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(187, 250, 156, 61, 219, 107, 141, 135)}};
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(122, 28, 133, 152, 90, 118, 109, 25)}};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__3_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "warn about uses of `sorry` in declarations added to the environment"};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__5_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(218, 70, 28, 226, 178, 151, 16, 11)}};
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(239, 41, 235, 79, 240, 234, 67, 166)}};
static const lean_object* l_Lean_initFn___closed__6_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_warn_sorry;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0 = (const lean_object*)&l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0;
static lean_once_cell_t l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1;
static lean_once_cell_t l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__0;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__1;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__2;
static const lean_array_object l_Lean_warnIfUsesSorry___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_warnIfUsesSorry___closed__3 = (const lean_object*)&l_Lean_warnIfUsesSorry___closed__3_value;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__4;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__5;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__6;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__7;
static const lean_closure_object l_Lean_warnIfUsesSorry___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_warnIfUsesSorry___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_warnIfUsesSorry___closed__8 = (const lean_object*)&l_Lean_warnIfUsesSorry___closed__8_value;
static const lean_string_object l_Lean_warnIfUsesSorry___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "hasSorry"};
static const lean_object* l_Lean_warnIfUsesSorry___closed__9 = (const lean_object*)&l_Lean_warnIfUsesSorry___closed__9_value;
static const lean_ctor_object l_Lean_warnIfUsesSorry___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_warnIfUsesSorry___closed__9_value),LEAN_SCALAR_PTR_LITERAL(111, 250, 94, 52, 248, 92, 138, 251)}};
static const lean_object* l_Lean_warnIfUsesSorry___closed__10 = (const lean_object*)&l_Lean_warnIfUsesSorry___closed__10_value;
static const lean_string_object l_Lean_warnIfUsesSorry___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "declaration uses `"};
static const lean_object* l_Lean_warnIfUsesSorry___closed__11 = (const lean_object*)&l_Lean_warnIfUsesSorry___closed__11_value;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__12;
static const lean_string_object l_Lean_warnIfUsesSorry___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_warnIfUsesSorry___closed__13 = (const lean_object*)&l_Lean_warnIfUsesSorry___closed__13_value;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__14;
static const lean_string_object l_Lean_warnIfUsesSorry___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "declaration uses `sorry`"};
static const lean_object* l_Lean_warnIfUsesSorry___closed__15 = (const lean_object*)&l_Lean_warnIfUsesSorry___closed__15_value;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__16;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__17;
static const lean_ctor_object l_Lean_warnIfUsesSorry___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_warnIfUsesSorry___closed__18 = (const lean_object*)&l_Lean_warnIfUsesSorry___closed__18_value;
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_AddDecl_0__Lean_initFn___closed__0_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "addDecl"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__0_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__0_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__0_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(105, 231, 4, 60, 254, 77, 195, 237)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_initFn___closed__2_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__2_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__2_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_initFn___closed__3_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__2_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__3_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__3_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_initFn___closed__4_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__3_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__4_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__4_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_initFn___closed__5_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "AddDecl"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__5_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__5_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_initFn___closed__6_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__4_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__5_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(15, 97, 208, 69, 128, 127, 228, 3)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__6_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__6_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_initFn___closed__7_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__6_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(162, 171, 242, 31, 173, 26, 83, 224)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__7_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__7_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_initFn___closed__8_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__7_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(131, 0, 147, 169, 205, 191, 49, 101)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__8_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__8_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_initFn___closed__9_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__9_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__9_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_initFn___closed__10_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__8_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__9_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(226, 50, 5, 71, 0, 154, 50, 2)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__10_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__10_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_initFn___closed__11_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__11_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__11_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_initFn___closed__12_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__10_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__11_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(107, 66, 231, 246, 189, 183, 24, 140)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__12_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__12_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_initFn___closed__13_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__12_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(86, 225, 3, 95, 219, 217, 43, 37)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__13_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__13_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_initFn___closed__14_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__13_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__5_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(11, 165, 226, 64, 111, 214, 252, 38)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__14_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__14_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_initFn___closed__15_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__14_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),((lean_object*)(((size_t)(337188874) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(137, 24, 7, 166, 250, 194, 253, 69)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__15_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__15_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_initFn___closed__16_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__16_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__16_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_initFn___closed__17_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__15_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__16_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(26, 77, 113, 4, 170, 120, 135, 144)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__17_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__17_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_initFn___closed__18_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__18_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__18_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_initFn___closed__19_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__17_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__18_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(102, 231, 39, 100, 49, 121, 171, 214)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__19_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__19_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_initFn___closed__20_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__19_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(167, 65, 246, 223, 87, 31, 234, 242)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__20_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__20_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2____boxed(lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg();
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__0;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__1;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__2_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "sorryAx"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__3_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(196, 190, 164, 146, 38, 179, 69, 72)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__4_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__5;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__6;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__7;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__8 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__8_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__9 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__9_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__10_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__10 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__10_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__11;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__12;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__13 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__13_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__14 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__14_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "typechecking declarations "};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__0 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__3_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "type checking"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___closed__0 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___closed__0_value;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Kernel"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___closed__1 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___closed__1_value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(213, 59, 86, 63, 192, 192, 9, 44)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___closed__2 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addDecl___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "adding declarations "};
static const lean_object* l_Lean_addDecl___lam__1___closed__0 = (const lean_object*)&l_Lean_addDecl___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_addDecl___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addDecl___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_addTrace___at___00Lean_addDecl_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_addDecl_spec__0___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00Lean_addDecl_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_addDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_addDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addDecl___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "no matching async adding rules, adding synchronously"};
static const lean_object* l_Lean_addDecl___lam__3___closed__0 = (const lean_object*)&l_Lean_addDecl___lam__3___closed__0_value;
static lean_once_cell_t l_Lean_addDecl___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addDecl___lam__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_addDecl_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_addDecl_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_addDecl___lam__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_isPrivateName___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addDecl___lam__8___closed__0 = (const lean_object*)&l_Lean_addDecl___lam__8___closed__0_value;
static const lean_string_object l_Lean_addDecl___lam__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "no matching exporting rules, exporting as is"};
static const lean_object* l_Lean_addDecl___lam__8___closed__1 = (const lean_object*)&l_Lean_addDecl___lam__8___closed__1_value;
static lean_once_cell_t l_Lean_addDecl___lam__8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addDecl___lam__8___closed__2;
static const lean_string_object l_Lean_addDecl___lam__8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "not exporting private declaration at all"};
static const lean_object* l_Lean_addDecl___lam__8___closed__3 = (const lean_object*)&l_Lean_addDecl___lam__8___closed__3_value;
static lean_once_cell_t l_Lean_addDecl___lam__8___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addDecl___lam__8___closed__4;
static const lean_string_object l_Lean_addDecl___lam__8___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "private decl under `privateInPublic`, exporting as is"};
static const lean_object* l_Lean_addDecl___lam__8___closed__5 = (const lean_object*)&l_Lean_addDecl___lam__8___closed__5_value;
static lean_once_cell_t l_Lean_addDecl___lam__8___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addDecl___lam__8___closed__6;
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__8(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addDecl___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "exporting definition "};
static const lean_object* l_Lean_addDecl___lam__4___closed__0 = (const lean_object*)&l_Lean_addDecl___lam__4___closed__0_value;
static lean_once_cell_t l_Lean_addDecl___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addDecl___lam__4___closed__1;
static const lean_string_object l_Lean_addDecl___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " as axiom"};
static const lean_object* l_Lean_addDecl___lam__4___closed__2 = (const lean_object*)&l_Lean_addDecl___lam__4___closed__2_value;
static lean_once_cell_t l_Lean_addDecl___lam__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addDecl___lam__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__4(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__13(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__10(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__12(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_addDecl_spec__1(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_addDecl___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_addDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_addDecl___closed__0_value_aux_0),((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__0_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 179, 108, 116, 74, 129, 13, 251)}};
static const lean_object* l_Lean_addDecl___closed__0 = (const lean_object*)&l_Lean_addDecl___closed__0_value;
static lean_once_cell_t l_Lean_addDecl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addDecl___closed__1;
static const lean_string_object l_Lean_addDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "exporting opaque "};
static const lean_object* l_Lean_addDecl___closed__2 = (const lean_object*)&l_Lean_addDecl___closed__2_value;
static lean_once_cell_t l_Lean_addDecl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addDecl___closed__3;
static const lean_string_object l_Lean_addDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "exporting theorem "};
static const lean_object* l_Lean_addDecl___closed__4 = (const lean_object*)&l_Lean_addDecl___closed__4_value;
static lean_once_cell_t l_Lean_addDecl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addDecl___closed__5;
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_addDecl_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_addDecl_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addAndCompile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(lean_object* v_opts_1_, lean_object* v_opt_2_){
_start:
{
lean_object* v_name_3_; lean_object* v_defValue_4_; lean_object* v_map_5_; lean_object* v___x_6_; 
v_name_3_ = lean_ctor_get(v_opt_2_, 0);
v_defValue_4_ = lean_ctor_get(v_opt_2_, 1);
v_map_5_ = lean_ctor_get(v_opts_1_, 0);
v___x_6_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5_, v_name_3_);
if (lean_obj_tag(v___x_6_) == 0)
{
uint8_t v___x_7_; 
v___x_7_ = lean_unbox(v_defValue_4_);
return v___x_7_;
}
else
{
lean_object* v_val_8_; 
v_val_8_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_val_8_);
lean_dec_ref(v___x_6_);
if (lean_obj_tag(v_val_8_) == 1)
{
uint8_t v_v_9_; 
v_v_9_ = lean_ctor_get_uint8(v_val_8_, 0);
lean_dec_ref(v_val_8_);
return v_v_9_;
}
else
{
uint8_t v___x_10_; 
lean_dec(v_val_8_);
v___x_10_ = lean_unbox(v_defValue_4_);
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0___boxed(lean_object* v_opts_11_, lean_object* v_opt_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_11_, v_opt_12_);
lean_dec_ref(v_opt_12_);
lean_dec_ref(v_opts_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addDecl(lean_object* v_env_15_, lean_object* v_opts_16_, lean_object* v_decl_17_, lean_object* v_cancelTk_x3f_18_){
_start:
{
lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_19_ = l_Lean_debug_skipKernelTC;
v___x_20_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_16_, v___x_19_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; size_t v___x_22_; lean_object* v___x_23_; 
v___x_21_ = l_Lean_Core_getMaxHeartbeats(v_opts_16_);
v___x_22_ = lean_usize_of_nat(v___x_21_);
lean_dec(v___x_21_);
v___x_23_ = lean_add_decl(v_env_15_, v___x_22_, v_decl_17_, v_cancelTk_x3f_18_);
return v___x_23_;
}
else
{
lean_object* v___x_24_; 
v___x_24_ = lean_add_decl_without_checking(v_env_15_, v_decl_17_);
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addDecl___boxed(lean_object* v_env_25_, lean_object* v_opts_26_, lean_object* v_decl_27_, lean_object* v_cancelTk_x3f_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Kernel_Environment_addDecl(v_env_25_, v_opts_26_, v_decl_27_, v_cancelTk_x3f_28_);
lean_dec(v_cancelTk_x3f_28_);
lean_dec(v_decl_27_);
lean_dec_ref(v_opts_26_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(lean_object* v_env_30_, lean_object* v_opts_31_, lean_object* v_decl_32_, lean_object* v_cancelTk_x3f_33_){
_start:
{
lean_object* v___x_34_; size_t v___x_35_; lean_object* v___x_36_; uint8_t v___x_37_; 
v___x_34_ = l_Lean_Core_getMaxHeartbeats(v_opts_31_);
v___x_35_ = lean_usize_of_nat(v___x_34_);
lean_dec(v___x_34_);
v___x_36_ = l_Lean_debug_skipKernelTC;
v___x_37_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_31_, v___x_36_);
if (v___x_37_ == 0)
{
uint8_t v___x_38_; lean_object* v___x_39_; 
v___x_38_ = 1;
v___x_39_ = l_Lean_Environment_addDeclCore(v_env_30_, v___x_35_, v_decl_32_, v_cancelTk_x3f_33_, v___x_38_);
return v___x_39_;
}
else
{
uint8_t v___x_40_; lean_object* v___x_41_; 
v___x_40_ = 0;
v___x_41_ = l_Lean_Environment_addDeclCore(v_env_30_, v___x_35_, v_decl_32_, v_cancelTk_x3f_33_, v___x_40_);
return v___x_41_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux___boxed(lean_object* v_env_42_, lean_object* v_opts_43_, lean_object* v_decl_44_, lean_object* v_cancelTk_x3f_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_42_, v_opts_43_, v_decl_44_, v_cancelTk_x3f_45_);
lean_dec(v_cancelTk_x3f_45_);
lean_dec(v_decl_44_);
lean_dec_ref(v_opts_43_);
return v_res_46_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_AddDecl_0__Lean_isNamespaceName(lean_object* v_x_47_){
_start:
{
if (lean_obj_tag(v_x_47_) == 1)
{
lean_object* v_pre_48_; 
v_pre_48_ = lean_ctor_get(v_x_47_, 0);
if (lean_obj_tag(v_pre_48_) == 0)
{
uint8_t v___x_49_; 
v___x_49_ = 1;
return v___x_49_;
}
else
{
v_x_47_ = v_pre_48_;
goto _start;
}
}
else
{
uint8_t v___x_51_; 
v___x_51_ = 0;
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_isNamespaceName___boxed(lean_object* v_x_52_){
_start:
{
uint8_t v_res_53_; lean_object* v_r_54_; 
v_res_53_ = l___private_Lean_AddDecl_0__Lean_isNamespaceName(v_x_52_);
lean_dec(v_x_52_);
v_r_54_ = lean_box(v_res_53_);
return v_r_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_registerNamePrefixes_go(lean_object* v_env_55_, lean_object* v_x_56_){
_start:
{
if (lean_obj_tag(v_x_56_) == 1)
{
lean_object* v_pre_57_; uint8_t v___x_58_; 
v_pre_57_ = lean_ctor_get(v_x_56_, 0);
lean_inc(v_pre_57_);
lean_dec_ref(v_x_56_);
v___x_58_ = l___private_Lean_AddDecl_0__Lean_isNamespaceName(v_pre_57_);
if (v___x_58_ == 0)
{
lean_dec(v_pre_57_);
return v_env_55_;
}
else
{
lean_object* v___x_59_; 
lean_inc(v_pre_57_);
v___x_59_ = l_Lean_Environment_registerNamespace(v_env_55_, v_pre_57_);
v_env_55_ = v___x_59_;
v_x_56_ = v_pre_57_;
goto _start;
}
}
else
{
lean_dec(v_x_56_);
return v_env_55_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(lean_object* v_env_61_, lean_object* v_name_62_){
_start:
{
uint32_t v___y_64_; 
if (lean_obj_tag(v_name_62_) == 1)
{
lean_object* v_str_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v_str_68_ = lean_ctor_get(v_name_62_, 1);
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = lean_string_utf8_byte_size(v_str_68_);
lean_inc_ref(v_str_68_);
v___x_71_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_71_, 0, v_str_68_);
lean_ctor_set(v___x_71_, 1, v___x_69_);
lean_ctor_set(v___x_71_, 2, v___x_70_);
v___x_72_ = l_String_Slice_Pos_get_x3f(v___x_71_, v___x_69_);
lean_dec_ref(v___x_71_);
if (lean_obj_tag(v___x_72_) == 0)
{
uint32_t v___x_73_; 
v___x_73_ = 65;
v___y_64_ = v___x_73_;
goto v___jp_63_;
}
else
{
lean_object* v_val_74_; uint32_t v___x_75_; 
v_val_74_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_val_74_);
lean_dec_ref(v___x_72_);
v___x_75_ = lean_unbox_uint32(v_val_74_);
lean_dec(v_val_74_);
v___y_64_ = v___x_75_;
goto v___jp_63_;
}
}
else
{
lean_dec(v_name_62_);
return v_env_61_;
}
v___jp_63_:
{
uint32_t v___x_65_; uint8_t v___x_66_; 
v___x_65_ = 95;
v___x_66_ = lean_uint32_dec_eq(v___y_64_, v___x_65_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; 
v___x_67_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes_go(v_env_61_, v_name_62_);
return v___x_67_;
}
else
{
lean_dec(v_name_62_);
return v_env_61_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(lean_object* v_name_76_, lean_object* v_decl_77_, lean_object* v_ref_78_){
_start:
{
lean_object* v_defValue_80_; lean_object* v_descr_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_108_; 
v_defValue_80_ = lean_ctor_get(v_decl_77_, 0);
v_descr_81_ = lean_ctor_get(v_decl_77_, 1);
v_isSharedCheck_108_ = !lean_is_exclusive(v_decl_77_);
if (v_isSharedCheck_108_ == 0)
{
v___x_83_ = v_decl_77_;
v_isShared_84_ = v_isSharedCheck_108_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_descr_81_);
lean_inc(v_defValue_80_);
lean_dec(v_decl_77_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_108_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_85_; uint8_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_85_ = lean_alloc_ctor(1, 0, 1);
v___x_86_ = lean_unbox(v_defValue_80_);
lean_ctor_set_uint8(v___x_85_, 0, v___x_86_);
lean_inc_n(v_name_76_, 2);
v___x_87_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_87_, 0, v_name_76_);
lean_ctor_set(v___x_87_, 1, v_ref_78_);
lean_ctor_set(v___x_87_, 2, v___x_85_);
lean_ctor_set(v___x_87_, 3, v_descr_81_);
v___x_88_ = lean_register_option(v_name_76_, v___x_87_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_98_; 
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_98_ == 0)
{
lean_object* v_unused_99_; 
v_unused_99_ = lean_ctor_get(v___x_88_, 0);
lean_dec(v_unused_99_);
v___x_90_ = v___x_88_;
v_isShared_91_ = v_isSharedCheck_98_;
goto v_resetjp_89_;
}
else
{
lean_dec(v___x_88_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_98_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_93_; 
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 1, v_defValue_80_);
lean_ctor_set(v___x_83_, 0, v_name_76_);
v___x_93_ = v___x_83_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_name_76_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v_defValue_80_);
v___x_93_ = v_reuseFailAlloc_97_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
lean_object* v___x_95_; 
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 0, v___x_93_);
v___x_95_ = v___x_90_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
else
{
lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_107_; 
lean_del_object(v___x_83_);
lean_dec(v_defValue_80_);
lean_dec(v_name_76_);
v_a_100_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_107_ == 0)
{
v___x_102_ = v___x_88_;
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v___x_88_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_105_; 
if (v_isShared_103_ == 0)
{
v___x_105_ = v___x_102_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_a_100_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_109_, lean_object* v_decl_110_, lean_object* v_ref_111_, lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(v_name_109_, v_decl_110_, v_ref_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_130_ = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_131_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_132_ = ((lean_object*)(l_Lean_initFn___closed__6_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_133_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(v___x_130_, v___x_131_, v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4____boxed(lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_();
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(lean_object* v_msgData_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v___x_142_; lean_object* v_env_143_; lean_object* v___x_144_; lean_object* v_mctx_145_; lean_object* v_lctx_146_; lean_object* v_options_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_142_ = lean_st_ref_get(v___y_140_);
v_env_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc_ref(v_env_143_);
lean_dec(v___x_142_);
v___x_144_ = lean_st_ref_get(v___y_138_);
v_mctx_145_ = lean_ctor_get(v___x_144_, 0);
lean_inc_ref(v_mctx_145_);
lean_dec(v___x_144_);
v_lctx_146_ = lean_ctor_get(v___y_137_, 2);
v_options_147_ = lean_ctor_get(v___y_139_, 2);
lean_inc_ref(v_options_147_);
lean_inc_ref(v_lctx_146_);
v___x_148_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_148_, 0, v_env_143_);
lean_ctor_set(v___x_148_, 1, v_mctx_145_);
lean_ctor_set(v___x_148_, 2, v_lctx_146_);
lean_ctor_set(v___x_148_, 3, v_options_147_);
v___x_149_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v_msgData_136_);
v___x_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0___boxed(lean_object* v_msgData_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(v_msgData_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___lam__0(lean_object* v_s_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_181_; 
lean_inc_ref(v_s_158_);
v___x_165_ = l_Lean_MessageData_ofExpr(v_s_158_);
v___x_166_ = l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(v___x_165_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
v_a_167_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_181_ == 0)
{
v___x_169_ = v___x_166_;
v_isShared_170_ = v_isSharedCheck_181_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_166_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_181_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_171_; uint8_t v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_171_ = lean_st_ref_take(v___y_159_);
v___x_172_ = l_Lean_Expr_isSyntheticSorry(v_s_158_);
lean_dec_ref(v_s_158_);
v___x_173_ = lean_box(v___x_172_);
v___x_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v_a_167_);
v___x_175_ = lean_array_push(v___x_171_, v___x_174_);
v___x_176_ = lean_st_ref_set(v___y_159_, v___x_175_);
v___x_177_ = lean_box(0);
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 0, v___x_177_);
v___x_179_ = v___x_169_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___lam__0___boxed(lean_object* v_s_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_warnIfUsesSorry___lam__0(v_s_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
return v_res_189_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(uint8_t v___y_198_, uint8_t v_suppressElabErrors_199_, lean_object* v_x_200_){
_start:
{
if (lean_obj_tag(v_x_200_) == 1)
{
lean_object* v_pre_201_; 
v_pre_201_ = lean_ctor_get(v_x_200_, 0);
switch(lean_obj_tag(v_pre_201_))
{
case 1:
{
lean_object* v_pre_202_; 
v_pre_202_ = lean_ctor_get(v_pre_201_, 0);
switch(lean_obj_tag(v_pre_202_))
{
case 0:
{
lean_object* v_str_203_; lean_object* v_str_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v_str_203_ = lean_ctor_get(v_x_200_, 1);
v_str_204_ = lean_ctor_get(v_pre_201_, 1);
v___x_205_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__0));
v___x_206_ = lean_string_dec_eq(v_str_204_, v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_207_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__1));
v___x_208_ = lean_string_dec_eq(v_str_204_, v___x_207_);
if (v___x_208_ == 0)
{
return v___y_198_;
}
else
{
lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_209_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__2));
v___x_210_ = lean_string_dec_eq(v_str_203_, v___x_209_);
if (v___x_210_ == 0)
{
return v___y_198_;
}
else
{
return v_suppressElabErrors_199_;
}
}
}
else
{
lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_211_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__3));
v___x_212_ = lean_string_dec_eq(v_str_203_, v___x_211_);
if (v___x_212_ == 0)
{
return v___y_198_;
}
else
{
return v_suppressElabErrors_199_;
}
}
}
case 1:
{
lean_object* v_pre_213_; 
v_pre_213_ = lean_ctor_get(v_pre_202_, 0);
if (lean_obj_tag(v_pre_213_) == 0)
{
lean_object* v_str_214_; lean_object* v_str_215_; lean_object* v_str_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v_str_214_ = lean_ctor_get(v_x_200_, 1);
v_str_215_ = lean_ctor_get(v_pre_201_, 1);
v_str_216_ = lean_ctor_get(v_pre_202_, 1);
v___x_217_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__4));
v___x_218_ = lean_string_dec_eq(v_str_216_, v___x_217_);
if (v___x_218_ == 0)
{
return v___y_198_;
}
else
{
lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_219_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__5));
v___x_220_ = lean_string_dec_eq(v_str_215_, v___x_219_);
if (v___x_220_ == 0)
{
return v___y_198_;
}
else
{
lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_221_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__6));
v___x_222_ = lean_string_dec_eq(v_str_214_, v___x_221_);
if (v___x_222_ == 0)
{
return v___y_198_;
}
else
{
return v_suppressElabErrors_199_;
}
}
}
}
else
{
return v___y_198_;
}
}
default: 
{
return v___y_198_;
}
}
}
case 0:
{
lean_object* v_str_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v_str_223_ = lean_ctor_get(v_x_200_, 1);
v___x_224_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__7));
v___x_225_ = lean_string_dec_eq(v_str_223_, v___x_224_);
if (v___x_225_ == 0)
{
return v___y_198_;
}
else
{
return v_suppressElabErrors_199_;
}
}
default: 
{
return v___y_198_;
}
}
}
else
{
return v___y_198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed(lean_object* v___y_226_, lean_object* v_suppressElabErrors_227_, lean_object* v_x_228_){
_start:
{
uint8_t v___y_15936__boxed_229_; uint8_t v_suppressElabErrors_boxed_230_; uint8_t v_res_231_; lean_object* v_r_232_; 
v___y_15936__boxed_229_ = lean_unbox(v___y_226_);
v_suppressElabErrors_boxed_230_ = lean_unbox(v_suppressElabErrors_227_);
v_res_231_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(v___y_15936__boxed_229_, v_suppressElabErrors_boxed_230_, v_x_228_);
lean_dec(v_x_228_);
v_r_232_ = lean_box(v_res_231_);
return v_r_232_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0(void){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_233_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_236_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1);
v___x_237_ = lean_unsigned_to_nat(0u);
v___x_238_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
lean_ctor_set(v___x_238_, 2, v___x_237_);
lean_ctor_set(v___x_238_, 3, v___x_236_);
lean_ctor_set(v___x_238_, 4, v___x_236_);
lean_ctor_set(v___x_238_, 5, v___x_236_);
lean_ctor_set(v___x_238_, 6, v___x_236_);
lean_ctor_set(v___x_238_, 7, v___x_236_);
lean_ctor_set(v___x_238_, 8, v___x_236_);
return v___x_238_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_239_ = lean_unsigned_to_nat(32u);
v___x_240_ = lean_mk_empty_array_with_capacity(v___x_239_);
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4(void){
_start:
{
size_t v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_242_ = ((size_t)5ULL);
v___x_243_ = lean_unsigned_to_nat(0u);
v___x_244_ = lean_unsigned_to_nat(32u);
v___x_245_ = lean_mk_empty_array_with_capacity(v___x_244_);
v___x_246_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3);
v___x_247_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v___x_245_);
lean_ctor_set(v___x_247_, 2, v___x_243_);
lean_ctor_set(v___x_247_, 3, v___x_243_);
lean_ctor_set_usize(v___x_247_, 4, v___x_242_);
return v___x_247_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_248_ = lean_box(1);
v___x_249_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_250_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1);
v___x_251_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v___x_249_);
lean_ctor_set(v___x_251_, 2, v___x_248_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(lean_object* v_msgData_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v___x_256_; lean_object* v_env_257_; lean_object* v_options_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_256_ = lean_st_ref_get(v___y_254_);
v_env_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc_ref(v_env_257_);
lean_dec(v___x_256_);
v_options_258_ = lean_ctor_get(v___y_253_, 2);
v___x_259_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2);
v___x_260_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5);
lean_inc_ref(v_options_258_);
v___x_261_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_261_, 0, v_env_257_);
lean_ctor_set(v___x_261_, 1, v___x_259_);
lean_ctor_set(v___x_261_, 2, v___x_260_);
lean_ctor_set(v___x_261_, 3, v_options_258_);
v___x_262_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v_msgData_252_);
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___boxed(lean_object* v_msgData_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msgData_264_, v___y_265_, v___y_266_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(lean_object* v_ref_270_, lean_object* v_msgData_271_, uint8_t v_severity_272_, uint8_t v_isSilent_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v___y_278_; lean_object* v___y_279_; uint8_t v___y_280_; lean_object* v___y_281_; lean_object* v___y_282_; uint8_t v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; uint8_t v___y_317_; lean_object* v___y_318_; uint8_t v___y_319_; uint8_t v___y_320_; lean_object* v___y_321_; lean_object* v___y_339_; lean_object* v___y_340_; uint8_t v___y_341_; lean_object* v___y_342_; uint8_t v___y_343_; uint8_t v___y_344_; lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_352_; uint8_t v___y_353_; uint8_t v___y_354_; lean_object* v___y_355_; uint8_t v___y_356_; uint8_t v___x_361_; lean_object* v___y_363_; lean_object* v___y_364_; uint8_t v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; uint8_t v___y_368_; uint8_t v___y_369_; uint8_t v___y_371_; uint8_t v___x_386_; 
v___x_361_ = 2;
v___x_386_ = l_Lean_instBEqMessageSeverity_beq(v_severity_272_, v___x_361_);
if (v___x_386_ == 0)
{
v___y_371_ = v___x_386_;
goto v___jp_370_;
}
else
{
uint8_t v___x_387_; 
lean_inc_ref(v_msgData_271_);
v___x_387_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_271_);
v___y_371_ = v___x_387_;
goto v___jp_370_;
}
v___jp_277_:
{
lean_object* v___x_287_; lean_object* v_currNamespace_288_; lean_object* v_openDecls_289_; lean_object* v_env_290_; lean_object* v_nextMacroScope_291_; lean_object* v_ngen_292_; lean_object* v_auxDeclNGen_293_; lean_object* v_traceState_294_; lean_object* v_cache_295_; lean_object* v_messages_296_; lean_object* v_infoState_297_; lean_object* v_snapshotTasks_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_312_; 
v___x_287_ = lean_st_ref_take(v___y_286_);
v_currNamespace_288_ = lean_ctor_get(v___y_285_, 6);
v_openDecls_289_ = lean_ctor_get(v___y_285_, 7);
v_env_290_ = lean_ctor_get(v___x_287_, 0);
v_nextMacroScope_291_ = lean_ctor_get(v___x_287_, 1);
v_ngen_292_ = lean_ctor_get(v___x_287_, 2);
v_auxDeclNGen_293_ = lean_ctor_get(v___x_287_, 3);
v_traceState_294_ = lean_ctor_get(v___x_287_, 4);
v_cache_295_ = lean_ctor_get(v___x_287_, 5);
v_messages_296_ = lean_ctor_get(v___x_287_, 6);
v_infoState_297_ = lean_ctor_get(v___x_287_, 7);
v_snapshotTasks_298_ = lean_ctor_get(v___x_287_, 8);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_312_ == 0)
{
v___x_300_ = v___x_287_;
v_isShared_301_ = v_isSharedCheck_312_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_snapshotTasks_298_);
lean_inc(v_infoState_297_);
lean_inc(v_messages_296_);
lean_inc(v_cache_295_);
lean_inc(v_traceState_294_);
lean_inc(v_auxDeclNGen_293_);
lean_inc(v_ngen_292_);
lean_inc(v_nextMacroScope_291_);
lean_inc(v_env_290_);
lean_dec(v___x_287_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_312_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
lean_inc(v_openDecls_289_);
lean_inc(v_currNamespace_288_);
v___x_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_302_, 0, v_currNamespace_288_);
lean_ctor_set(v___x_302_, 1, v_openDecls_289_);
v___x_303_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v___y_279_);
lean_inc_ref(v___y_278_);
lean_inc_ref(v___y_282_);
v___x_304_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_304_, 0, v___y_282_);
lean_ctor_set(v___x_304_, 1, v___y_284_);
lean_ctor_set(v___x_304_, 2, v___y_281_);
lean_ctor_set(v___x_304_, 3, v___y_278_);
lean_ctor_set(v___x_304_, 4, v___x_303_);
lean_ctor_set_uint8(v___x_304_, sizeof(void*)*5, v___y_283_);
lean_ctor_set_uint8(v___x_304_, sizeof(void*)*5 + 1, v___y_280_);
lean_ctor_set_uint8(v___x_304_, sizeof(void*)*5 + 2, v_isSilent_273_);
v___x_305_ = l_Lean_MessageLog_add(v___x_304_, v_messages_296_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 6, v___x_305_);
v___x_307_ = v___x_300_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_env_290_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v_nextMacroScope_291_);
lean_ctor_set(v_reuseFailAlloc_311_, 2, v_ngen_292_);
lean_ctor_set(v_reuseFailAlloc_311_, 3, v_auxDeclNGen_293_);
lean_ctor_set(v_reuseFailAlloc_311_, 4, v_traceState_294_);
lean_ctor_set(v_reuseFailAlloc_311_, 5, v_cache_295_);
lean_ctor_set(v_reuseFailAlloc_311_, 6, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_311_, 7, v_infoState_297_);
lean_ctor_set(v_reuseFailAlloc_311_, 8, v_snapshotTasks_298_);
v___x_307_ = v_reuseFailAlloc_311_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = lean_st_ref_set(v___y_286_, v___x_307_);
v___x_309_ = lean_box(0);
v___x_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
return v___x_310_;
}
}
}
v___jp_313_:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_337_; 
v___x_322_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_271_);
v___x_323_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v___x_322_, v___y_274_, v___y_275_);
v_a_324_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_337_ == 0)
{
v___x_326_ = v___x_323_;
v_isShared_327_ = v_isSharedCheck_337_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_323_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_337_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
lean_inc_ref_n(v___y_315_, 2);
v___x_328_ = l_Lean_FileMap_toPosition(v___y_315_, v___y_318_);
lean_dec(v___y_318_);
v___x_329_ = l_Lean_FileMap_toPosition(v___y_315_, v___y_321_);
lean_dec(v___y_321_);
v___x_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
v___x_331_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
if (v___y_319_ == 0)
{
lean_del_object(v___x_326_);
lean_dec_ref(v___y_314_);
v___y_278_ = v___x_331_;
v___y_279_ = v_a_324_;
v___y_280_ = v___y_317_;
v___y_281_ = v___x_330_;
v___y_282_ = v___y_316_;
v___y_283_ = v___y_320_;
v___y_284_ = v___x_328_;
v___y_285_ = v___y_274_;
v___y_286_ = v___y_275_;
goto v___jp_277_;
}
else
{
uint8_t v___x_332_; 
lean_inc(v_a_324_);
v___x_332_ = l_Lean_MessageData_hasTag(v___y_314_, v_a_324_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; lean_object* v___x_335_; 
lean_dec_ref(v___x_330_);
lean_dec_ref(v___x_328_);
lean_dec(v_a_324_);
v___x_333_ = lean_box(0);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 0, v___x_333_);
v___x_335_ = v___x_326_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
else
{
lean_del_object(v___x_326_);
v___y_278_ = v___x_331_;
v___y_279_ = v_a_324_;
v___y_280_ = v___y_317_;
v___y_281_ = v___x_330_;
v___y_282_ = v___y_316_;
v___y_283_ = v___y_320_;
v___y_284_ = v___x_328_;
v___y_285_ = v___y_274_;
v___y_286_ = v___y_275_;
goto v___jp_277_;
}
}
}
}
v___jp_338_:
{
lean_object* v___x_347_; 
v___x_347_ = l_Lean_Syntax_getTailPos_x3f(v___y_345_, v___y_343_);
lean_dec(v___y_345_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_inc(v___y_346_);
v___y_314_ = v___y_339_;
v___y_315_ = v___y_340_;
v___y_316_ = v___y_342_;
v___y_317_ = v___y_341_;
v___y_318_ = v___y_346_;
v___y_319_ = v___y_344_;
v___y_320_ = v___y_343_;
v___y_321_ = v___y_346_;
goto v___jp_313_;
}
else
{
lean_object* v_val_348_; 
v_val_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_val_348_);
lean_dec_ref(v___x_347_);
v___y_314_ = v___y_339_;
v___y_315_ = v___y_340_;
v___y_316_ = v___y_342_;
v___y_317_ = v___y_341_;
v___y_318_ = v___y_346_;
v___y_319_ = v___y_344_;
v___y_320_ = v___y_343_;
v___y_321_ = v_val_348_;
goto v___jp_313_;
}
}
v___jp_349_:
{
lean_object* v_ref_357_; lean_object* v___x_358_; 
v_ref_357_ = l_Lean_replaceRef(v_ref_270_, v___y_355_);
v___x_358_ = l_Lean_Syntax_getPos_x3f(v_ref_357_, v___y_354_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v___x_359_; 
v___x_359_ = lean_unsigned_to_nat(0u);
v___y_339_ = v___y_350_;
v___y_340_ = v___y_351_;
v___y_341_ = v___y_356_;
v___y_342_ = v___y_352_;
v___y_343_ = v___y_354_;
v___y_344_ = v___y_353_;
v___y_345_ = v_ref_357_;
v___y_346_ = v___x_359_;
goto v___jp_338_;
}
else
{
lean_object* v_val_360_; 
v_val_360_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_val_360_);
lean_dec_ref(v___x_358_);
v___y_339_ = v___y_350_;
v___y_340_ = v___y_351_;
v___y_341_ = v___y_356_;
v___y_342_ = v___y_352_;
v___y_343_ = v___y_354_;
v___y_344_ = v___y_353_;
v___y_345_ = v_ref_357_;
v___y_346_ = v_val_360_;
goto v___jp_338_;
}
}
v___jp_362_:
{
if (v___y_369_ == 0)
{
v___y_350_ = v___y_367_;
v___y_351_ = v___y_363_;
v___y_352_ = v___y_364_;
v___y_353_ = v___y_365_;
v___y_354_ = v___y_368_;
v___y_355_ = v___y_366_;
v___y_356_ = v_severity_272_;
goto v___jp_349_;
}
else
{
v___y_350_ = v___y_367_;
v___y_351_ = v___y_363_;
v___y_352_ = v___y_364_;
v___y_353_ = v___y_365_;
v___y_354_ = v___y_368_;
v___y_355_ = v___y_366_;
v___y_356_ = v___x_361_;
goto v___jp_349_;
}
}
v___jp_370_:
{
if (v___y_371_ == 0)
{
lean_object* v_fileName_372_; lean_object* v_fileMap_373_; lean_object* v_options_374_; lean_object* v_ref_375_; uint8_t v_suppressElabErrors_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___f_379_; uint8_t v___x_380_; uint8_t v___x_381_; 
v_fileName_372_ = lean_ctor_get(v___y_274_, 0);
v_fileMap_373_ = lean_ctor_get(v___y_274_, 1);
v_options_374_ = lean_ctor_get(v___y_274_, 2);
v_ref_375_ = lean_ctor_get(v___y_274_, 5);
v_suppressElabErrors_376_ = lean_ctor_get_uint8(v___y_274_, sizeof(void*)*14 + 1);
v___x_377_ = lean_box(v___y_371_);
v___x_378_ = lean_box(v_suppressElabErrors_376_);
v___f_379_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed), 3, 2);
lean_closure_set(v___f_379_, 0, v___x_377_);
lean_closure_set(v___f_379_, 1, v___x_378_);
v___x_380_ = 1;
v___x_381_ = l_Lean_instBEqMessageSeverity_beq(v_severity_272_, v___x_380_);
if (v___x_381_ == 0)
{
v___y_363_ = v_fileMap_373_;
v___y_364_ = v_fileName_372_;
v___y_365_ = v_suppressElabErrors_376_;
v___y_366_ = v_ref_375_;
v___y_367_ = v___f_379_;
v___y_368_ = v___y_371_;
v___y_369_ = v___x_381_;
goto v___jp_362_;
}
else
{
lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_382_ = l_Lean_warningAsError;
v___x_383_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_374_, v___x_382_);
v___y_363_ = v_fileMap_373_;
v___y_364_ = v_fileName_372_;
v___y_365_ = v_suppressElabErrors_376_;
v___y_366_ = v_ref_375_;
v___y_367_ = v___f_379_;
v___y_368_ = v___y_371_;
v___y_369_ = v___x_383_;
goto v___jp_362_;
}
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; 
lean_dec_ref(v_msgData_271_);
v___x_384_ = lean_box(0);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___boxed(lean_object* v_ref_388_, lean_object* v_msgData_389_, lean_object* v_severity_390_, lean_object* v_isSilent_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
uint8_t v_severity_boxed_395_; uint8_t v_isSilent_boxed_396_; lean_object* v_res_397_; 
v_severity_boxed_395_ = lean_unbox(v_severity_390_);
v_isSilent_boxed_396_ = lean_unbox(v_isSilent_391_);
v_res_397_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_388_, v_msgData_389_, v_severity_boxed_395_, v_isSilent_boxed_396_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v_ref_388_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(lean_object* v_msgData_398_, uint8_t v_severity_399_, uint8_t v_isSilent_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_ref_404_; lean_object* v___x_405_; 
v_ref_404_ = lean_ctor_get(v___y_401_, 5);
v___x_405_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_404_, v_msgData_398_, v_severity_399_, v_isSilent_400_, v___y_401_, v___y_402_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4___boxed(lean_object* v_msgData_406_, lean_object* v_severity_407_, lean_object* v_isSilent_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
uint8_t v_severity_boxed_412_; uint8_t v_isSilent_boxed_413_; lean_object* v_res_414_; 
v_severity_boxed_412_ = lean_unbox(v_severity_407_);
v_isSilent_boxed_413_ = lean_unbox(v_isSilent_408_);
v_res_414_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_406_, v_severity_boxed_412_, v_isSilent_boxed_413_, v___y_409_, v___y_410_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(lean_object* v_msgData_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
uint8_t v___x_419_; uint8_t v___x_420_; lean_object* v___x_421_; 
v___x_419_ = 1;
v___x_420_ = 0;
v___x_421_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_415_, v___x_419_, v___x_420_, v___y_416_, v___y_417_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2___boxed(lean_object* v_msgData_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v_msgData_422_, v___y_423_, v___y_424_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(lean_object* v_as_430_, size_t v_sz_431_, size_t v_i_432_, lean_object* v_b_433_){
_start:
{
uint8_t v___x_434_; 
v___x_434_ = lean_usize_dec_lt(v_i_432_, v_sz_431_);
if (v___x_434_ == 0)
{
lean_inc_ref(v_b_433_);
return v_b_433_;
}
else
{
lean_object* v_a_435_; lean_object* v_fst_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v_a_435_ = lean_array_uget_borrowed(v_as_430_, v_i_432_);
v_fst_436_ = lean_ctor_get(v_a_435_, 0);
v___x_437_ = lean_box(0);
v___x_438_ = lean_unbox(v_fst_436_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; size_t v___x_440_; size_t v___x_441_; 
v___x_439_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___closed__0));
v___x_440_ = ((size_t)1ULL);
v___x_441_ = lean_usize_add(v_i_432_, v___x_440_);
v_i_432_ = v___x_441_;
v_b_433_ = v___x_439_;
goto _start;
}
else
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
lean_inc(v_a_435_);
v___x_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_443_, 0, v_a_435_);
v___x_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
v___x_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set(v___x_445_, 1, v___x_437_);
return v___x_445_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___boxed(lean_object* v_as_446_, lean_object* v_sz_447_, lean_object* v_i_448_, lean_object* v_b_449_){
_start:
{
size_t v_sz_boxed_450_; size_t v_i_boxed_451_; lean_object* v_res_452_; 
v_sz_boxed_450_ = lean_unbox_usize(v_sz_447_);
lean_dec(v_sz_447_);
v_i_boxed_451_ = lean_unbox_usize(v_i_448_);
lean_dec(v_i_448_);
v_res_452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v_as_446_, v_sz_boxed_450_, v_i_boxed_451_, v_b_449_);
lean_dec_ref(v_b_449_);
lean_dec_ref(v_as_446_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(lean_object* v_fn_453_, lean_object* v_e_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Expr_getSorry_x3f(v_e_454_);
if (lean_obj_tag(v___x_461_) == 1)
{
lean_object* v_val_462_; lean_object* v___x_463_; 
v_val_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_val_462_);
lean_dec_ref(v___x_461_);
lean_inc(v___y_459_);
lean_inc_ref(v___y_458_);
lean_inc(v___y_457_);
lean_inc_ref(v___y_456_);
lean_inc(v___y_455_);
v___x_463_ = lean_apply_7(v_fn_453_, v_val_462_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, lean_box(0));
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_472_; 
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_472_ == 0)
{
lean_object* v_unused_473_; 
v_unused_473_ = lean_ctor_get(v___x_463_, 0);
lean_dec(v_unused_473_);
v___x_465_ = v___x_463_;
v_isShared_466_ = v_isSharedCheck_472_;
goto v_resetjp_464_;
}
else
{
lean_dec(v___x_463_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_472_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
uint8_t v___x_467_; lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_467_ = 0;
v___x_468_ = lean_box(v___x_467_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 0, v___x_468_);
v___x_470_ = v___x_465_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
v_a_474_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_463_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_463_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
else
{
uint8_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
lean_dec(v___x_461_);
lean_dec_ref(v_fn_453_);
v___x_482_ = 1;
v___x_483_ = lean_box(v___x_482_);
v___x_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
return v___x_484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed(lean_object* v_fn_485_, lean_object* v_e_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(v_fn_485_, v_e_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v_e_486_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_object* v_00_u03b1_494_, lean_object* v_x_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_apply_1(v_x_495_, lean_box(0));
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v_00_u03b1_504_, lean_object* v_x_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(v_00_u03b1_504_, v_x_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(lean_object* v_k_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v_b_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v___x_522_; 
lean_inc(v___y_520_);
lean_inc_ref(v___y_519_);
lean_inc(v___y_518_);
lean_inc_ref(v___y_517_);
lean_inc(v___y_515_);
lean_inc(v___y_514_);
v___x_522_ = lean_apply_8(v_k_513_, v_b_516_, v___y_514_, v___y_515_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, lean_box(0));
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed(lean_object* v_k_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v_b_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(v_k_523_, v___y_524_, v___y_525_, v_b_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_525_);
lean_dec(v___y_524_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(lean_object* v_name_533_, lean_object* v_type_534_, lean_object* v_val_535_, lean_object* v_k_536_, uint8_t v_nondep_537_, uint8_t v_kind_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v___f_546_; lean_object* v___x_547_; 
lean_inc(v___y_540_);
lean_inc(v___y_539_);
v___f_546_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_546_, 0, v_k_536_);
lean_closure_set(v___f_546_, 1, v___y_539_);
lean_closure_set(v___f_546_, 2, v___y_540_);
v___x_547_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_533_, v_type_534_, v_val_535_, v___f_546_, v_nondep_537_, v_kind_538_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
if (lean_obj_tag(v___x_547_) == 0)
{
return v___x_547_;
}
else
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
v_a_548_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_547_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_547_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg___boxed(lean_object* v_name_556_, lean_object* v_type_557_, lean_object* v_val_558_, lean_object* v_k_559_, lean_object* v_nondep_560_, lean_object* v_kind_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
uint8_t v_nondep_boxed_569_; uint8_t v_kind_boxed_570_; lean_object* v_res_571_; 
v_nondep_boxed_569_ = lean_unbox(v_nondep_560_);
v_kind_boxed_570_ = lean_unbox(v_kind_561_);
v_res_571_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_556_, v_type_557_, v_val_558_, v_k_559_, v_nondep_boxed_569_, v_kind_boxed_570_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec(v___y_562_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed(lean_object* v_fvars_572_, lean_object* v_f_573_, lean_object* v_body_574_, lean_object* v_x_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(v_fvars_572_, v_f_573_, v_body_574_, v_x_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec(v___y_576_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(lean_object* v_f_584_, lean_object* v_fvars_585_, lean_object* v_a_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
if (lean_obj_tag(v_a_586_) == 8)
{
lean_object* v_declName_594_; lean_object* v_type_595_; lean_object* v_value_596_; lean_object* v_body_597_; lean_object* v_d_598_; lean_object* v___x_599_; 
v_declName_594_ = lean_ctor_get(v_a_586_, 0);
lean_inc(v_declName_594_);
v_type_595_ = lean_ctor_get(v_a_586_, 1);
lean_inc_ref(v_type_595_);
v_value_596_ = lean_ctor_get(v_a_586_, 2);
lean_inc_ref(v_value_596_);
v_body_597_ = lean_ctor_get(v_a_586_, 3);
lean_inc_ref(v_body_597_);
lean_dec_ref(v_a_586_);
v_d_598_ = lean_expr_instantiate_rev(v_type_595_, v_fvars_585_);
lean_dec_ref(v_type_595_);
lean_inc_ref(v_f_584_);
lean_inc(v___y_592_);
lean_inc_ref(v___y_591_);
lean_inc(v___y_590_);
lean_inc_ref(v___y_589_);
lean_inc(v___y_588_);
lean_inc(v___y_587_);
lean_inc_ref(v_d_598_);
v___x_599_ = lean_apply_8(v_f_584_, v_d_598_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, lean_box(0));
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_v_600_; lean_object* v___x_601_; 
lean_dec_ref(v___x_599_);
v_v_600_ = lean_expr_instantiate_rev(v_value_596_, v_fvars_585_);
lean_dec_ref(v_value_596_);
lean_inc_ref(v_f_584_);
lean_inc(v___y_592_);
lean_inc_ref(v___y_591_);
lean_inc(v___y_590_);
lean_inc_ref(v___y_589_);
lean_inc(v___y_588_);
lean_inc(v___y_587_);
lean_inc_ref(v_v_600_);
v___x_601_ = lean_apply_8(v_f_584_, v_v_600_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, lean_box(0));
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v___f_602_; uint8_t v___x_603_; uint8_t v___x_604_; lean_object* v___x_605_; 
lean_dec_ref(v___x_601_);
v___f_602_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed), 11, 3);
lean_closure_set(v___f_602_, 0, v_fvars_585_);
lean_closure_set(v___f_602_, 1, v_f_584_);
lean_closure_set(v___f_602_, 2, v_body_597_);
v___x_603_ = 0;
v___x_604_ = 0;
v___x_605_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_declName_594_, v_d_598_, v_v_600_, v___f_602_, v___x_603_, v___x_604_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
return v___x_605_;
}
else
{
lean_dec_ref(v_v_600_);
lean_dec_ref(v_d_598_);
lean_dec_ref(v_body_597_);
lean_dec(v_declName_594_);
lean_dec_ref(v_fvars_585_);
lean_dec_ref(v_f_584_);
return v___x_601_;
}
}
else
{
lean_dec_ref(v_d_598_);
lean_dec_ref(v_body_597_);
lean_dec_ref(v_value_596_);
lean_dec(v_declName_594_);
lean_dec_ref(v_fvars_585_);
lean_dec_ref(v_f_584_);
return v___x_599_;
}
}
else
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_expr_instantiate_rev(v_a_586_, v_fvars_585_);
lean_dec_ref(v_fvars_585_);
lean_dec_ref(v_a_586_);
lean_inc(v___y_592_);
lean_inc_ref(v___y_591_);
lean_inc(v___y_590_);
lean_inc_ref(v___y_589_);
lean_inc(v___y_588_);
lean_inc(v___y_587_);
v___x_607_ = lean_apply_8(v_f_584_, v___x_606_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, lean_box(0));
return v___x_607_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(lean_object* v_fvars_608_, lean_object* v_f_609_, lean_object* v_body_610_, lean_object* v_x_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_array_push(v_fvars_608_, v_x_611_);
v___x_620_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_609_, v___x_619_, v_body_610_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___boxed(lean_object* v_f_621_, lean_object* v_fvars_622_, lean_object* v_a_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_621_, v_fvars_622_, v_a_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec(v___y_624_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(lean_object* v_f_634_, lean_object* v_e_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_644_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_634_, v___x_643_, v_e_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___boxed(lean_object* v_f_645_, lean_object* v_e_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v_f_645_, v_e_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec(v___y_647_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(lean_object* v_name_655_, uint8_t v_bi_656_, lean_object* v_type_657_, lean_object* v_k_658_, uint8_t v_kind_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v___f_667_; lean_object* v___x_668_; 
lean_inc(v___y_661_);
lean_inc(v___y_660_);
v___f_667_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_667_, 0, v_k_658_);
lean_closure_set(v___f_667_, 1, v___y_660_);
lean_closure_set(v___f_667_, 2, v___y_661_);
v___x_668_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_655_, v_bi_656_, v_type_657_, v___f_667_, v_kind_659_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
if (lean_obj_tag(v___x_668_) == 0)
{
return v___x_668_;
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_668_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_668_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___boxed(lean_object* v_name_677_, lean_object* v_bi_678_, lean_object* v_type_679_, lean_object* v_k_680_, lean_object* v_kind_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
uint8_t v_bi_boxed_689_; uint8_t v_kind_boxed_690_; lean_object* v_res_691_; 
v_bi_boxed_689_ = lean_unbox(v_bi_678_);
v_kind_boxed_690_ = lean_unbox(v_kind_681_);
v_res_691_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_677_, v_bi_boxed_689_, v_type_679_, v_k_680_, v_kind_boxed_690_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec(v___y_682_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed(lean_object* v_fvars_692_, lean_object* v_f_693_, lean_object* v_body_694_, lean_object* v_x_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(v_fvars_692_, v_f_693_, v_body_694_, v_x_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec(v___y_696_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(lean_object* v_f_704_, lean_object* v_fvars_705_, lean_object* v_a_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
if (lean_obj_tag(v_a_706_) == 7)
{
lean_object* v_binderName_714_; lean_object* v_binderType_715_; lean_object* v_body_716_; uint8_t v_binderInfo_717_; lean_object* v_d_718_; lean_object* v___x_719_; 
v_binderName_714_ = lean_ctor_get(v_a_706_, 0);
lean_inc(v_binderName_714_);
v_binderType_715_ = lean_ctor_get(v_a_706_, 1);
lean_inc_ref(v_binderType_715_);
v_body_716_ = lean_ctor_get(v_a_706_, 2);
lean_inc_ref(v_body_716_);
v_binderInfo_717_ = lean_ctor_get_uint8(v_a_706_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_706_);
v_d_718_ = lean_expr_instantiate_rev(v_binderType_715_, v_fvars_705_);
lean_dec_ref(v_binderType_715_);
lean_inc_ref(v_f_704_);
lean_inc(v___y_712_);
lean_inc_ref(v___y_711_);
lean_inc(v___y_710_);
lean_inc_ref(v___y_709_);
lean_inc(v___y_708_);
lean_inc(v___y_707_);
lean_inc_ref(v_d_718_);
v___x_719_ = lean_apply_8(v_f_704_, v_d_718_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, lean_box(0));
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v___f_720_; uint8_t v___x_721_; lean_object* v___x_722_; 
lean_dec_ref(v___x_719_);
v___f_720_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed), 11, 3);
lean_closure_set(v___f_720_, 0, v_fvars_705_);
lean_closure_set(v___f_720_, 1, v_f_704_);
lean_closure_set(v___f_720_, 2, v_body_716_);
v___x_721_ = 0;
v___x_722_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_714_, v_binderInfo_717_, v_d_718_, v___f_720_, v___x_721_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
return v___x_722_;
}
else
{
lean_dec_ref(v_d_718_);
lean_dec_ref(v_body_716_);
lean_dec(v_binderName_714_);
lean_dec_ref(v_fvars_705_);
lean_dec_ref(v_f_704_);
return v___x_719_;
}
}
else
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = lean_expr_instantiate_rev(v_a_706_, v_fvars_705_);
lean_dec_ref(v_fvars_705_);
lean_dec_ref(v_a_706_);
lean_inc(v___y_712_);
lean_inc_ref(v___y_711_);
lean_inc(v___y_710_);
lean_inc_ref(v___y_709_);
lean_inc(v___y_708_);
lean_inc(v___y_707_);
v___x_724_ = lean_apply_8(v_f_704_, v___x_723_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, lean_box(0));
return v___x_724_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(lean_object* v_fvars_725_, lean_object* v_f_726_, lean_object* v_body_727_, lean_object* v_x_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = lean_array_push(v_fvars_725_, v_x_728_);
v___x_737_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_726_, v___x_736_, v_body_727_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___boxed(lean_object* v_f_738_, lean_object* v_fvars_739_, lean_object* v_a_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_738_, v_fvars_739_, v_a_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec(v___y_741_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(lean_object* v_f_749_, lean_object* v_e_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_759_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_749_, v___x_758_, v_e_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10___boxed(lean_object* v_f_760_, lean_object* v_e_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v_f_760_, v_e_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec(v___y_762_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed(lean_object* v_fvars_770_, lean_object* v_f_771_, lean_object* v_body_772_, lean_object* v_x_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(v_fvars_770_, v_f_771_, v_body_772_, v_x_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec(v___y_774_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(lean_object* v_f_782_, lean_object* v_fvars_783_, lean_object* v_a_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
if (lean_obj_tag(v_a_784_) == 6)
{
lean_object* v_binderName_792_; lean_object* v_binderType_793_; lean_object* v_body_794_; uint8_t v_binderInfo_795_; lean_object* v_d_796_; lean_object* v___x_797_; 
v_binderName_792_ = lean_ctor_get(v_a_784_, 0);
lean_inc(v_binderName_792_);
v_binderType_793_ = lean_ctor_get(v_a_784_, 1);
lean_inc_ref(v_binderType_793_);
v_body_794_ = lean_ctor_get(v_a_784_, 2);
lean_inc_ref(v_body_794_);
v_binderInfo_795_ = lean_ctor_get_uint8(v_a_784_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_784_);
v_d_796_ = lean_expr_instantiate_rev(v_binderType_793_, v_fvars_783_);
lean_dec_ref(v_binderType_793_);
lean_inc_ref(v_f_782_);
lean_inc(v___y_790_);
lean_inc_ref(v___y_789_);
lean_inc(v___y_788_);
lean_inc_ref(v___y_787_);
lean_inc(v___y_786_);
lean_inc(v___y_785_);
lean_inc_ref(v_d_796_);
v___x_797_ = lean_apply_8(v_f_782_, v_d_796_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, lean_box(0));
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v___f_798_; uint8_t v___x_799_; lean_object* v___x_800_; 
lean_dec_ref(v___x_797_);
v___f_798_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed), 11, 3);
lean_closure_set(v___f_798_, 0, v_fvars_783_);
lean_closure_set(v___f_798_, 1, v_f_782_);
lean_closure_set(v___f_798_, 2, v_body_794_);
v___x_799_ = 0;
v___x_800_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_792_, v_binderInfo_795_, v_d_796_, v___f_798_, v___x_799_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
return v___x_800_;
}
else
{
lean_dec_ref(v_d_796_);
lean_dec_ref(v_body_794_);
lean_dec(v_binderName_792_);
lean_dec_ref(v_fvars_783_);
lean_dec_ref(v_f_782_);
return v___x_797_;
}
}
else
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = lean_expr_instantiate_rev(v_a_784_, v_fvars_783_);
lean_dec_ref(v_fvars_783_);
lean_dec_ref(v_a_784_);
lean_inc(v___y_790_);
lean_inc_ref(v___y_789_);
lean_inc(v___y_788_);
lean_inc_ref(v___y_787_);
lean_inc(v___y_786_);
lean_inc(v___y_785_);
v___x_802_ = lean_apply_8(v_f_782_, v___x_801_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, lean_box(0));
return v___x_802_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(lean_object* v_fvars_803_, lean_object* v_f_804_, lean_object* v_body_805_, lean_object* v_x_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = lean_array_push(v_fvars_803_, v_x_806_);
v___x_815_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_804_, v___x_814_, v_body_805_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___boxed(lean_object* v_f_816_, lean_object* v_fvars_817_, lean_object* v_a_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_816_, v_fvars_817_, v_a_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec(v___y_819_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(lean_object* v_f_827_, lean_object* v_e_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_837_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_827_, v___x_836_, v_e_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11___boxed(lean_object* v_f_838_, lean_object* v_e_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v_f_838_, v_e_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec(v___y_840_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(lean_object* v_a_848_, lean_object* v_x_849_){
_start:
{
if (lean_obj_tag(v_x_849_) == 0)
{
lean_object* v___x_850_; 
v___x_850_ = lean_box(0);
return v___x_850_;
}
else
{
lean_object* v_key_851_; lean_object* v_value_852_; lean_object* v_tail_853_; uint8_t v___x_854_; 
v_key_851_ = lean_ctor_get(v_x_849_, 0);
v_value_852_ = lean_ctor_get(v_x_849_, 1);
v_tail_853_ = lean_ctor_get(v_x_849_, 2);
v___x_854_ = lean_expr_eqv(v_key_851_, v_a_848_);
if (v___x_854_ == 0)
{
v_x_849_ = v_tail_853_;
goto _start;
}
else
{
lean_object* v___x_856_; 
lean_inc(v_value_852_);
v___x_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_856_, 0, v_value_852_);
return v___x_856_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_a_857_, lean_object* v_x_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_857_, v_x_858_);
lean_dec(v_x_858_);
lean_dec_ref(v_a_857_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_m_860_, lean_object* v_a_861_){
_start:
{
lean_object* v_buckets_862_; lean_object* v___x_863_; uint64_t v___x_864_; uint64_t v___x_865_; uint64_t v___x_866_; uint64_t v_fold_867_; uint64_t v___x_868_; uint64_t v___x_869_; uint64_t v___x_870_; size_t v___x_871_; size_t v___x_872_; size_t v___x_873_; size_t v___x_874_; size_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_buckets_862_ = lean_ctor_get(v_m_860_, 1);
v___x_863_ = lean_array_get_size(v_buckets_862_);
v___x_864_ = l_Lean_Expr_hash(v_a_861_);
v___x_865_ = 32ULL;
v___x_866_ = lean_uint64_shift_right(v___x_864_, v___x_865_);
v_fold_867_ = lean_uint64_xor(v___x_864_, v___x_866_);
v___x_868_ = 16ULL;
v___x_869_ = lean_uint64_shift_right(v_fold_867_, v___x_868_);
v___x_870_ = lean_uint64_xor(v_fold_867_, v___x_869_);
v___x_871_ = lean_uint64_to_usize(v___x_870_);
v___x_872_ = lean_usize_of_nat(v___x_863_);
v___x_873_ = ((size_t)1ULL);
v___x_874_ = lean_usize_sub(v___x_872_, v___x_873_);
v___x_875_ = lean_usize_land(v___x_871_, v___x_874_);
v___x_876_ = lean_array_uget_borrowed(v_buckets_862_, v___x_875_);
v___x_877_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_861_, v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_m_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_878_, v_a_879_);
lean_dec_ref(v_a_879_);
lean_dec_ref(v_m_878_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_object* v_00_u03b1_881_, lean_object* v_x_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = lean_apply_1(v_x_882_, lean_box(0));
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0___boxed(lean_object* v_00_u03b1_891_, lean_object* v_x_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(v_00_u03b1_891_, v_x_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(lean_object* v_x_900_, lean_object* v_x_901_){
_start:
{
if (lean_obj_tag(v_x_901_) == 0)
{
return v_x_900_;
}
else
{
lean_object* v_key_902_; lean_object* v_value_903_; lean_object* v_tail_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_927_; 
v_key_902_ = lean_ctor_get(v_x_901_, 0);
v_value_903_ = lean_ctor_get(v_x_901_, 1);
v_tail_904_ = lean_ctor_get(v_x_901_, 2);
v_isSharedCheck_927_ = !lean_is_exclusive(v_x_901_);
if (v_isSharedCheck_927_ == 0)
{
v___x_906_ = v_x_901_;
v_isShared_907_ = v_isSharedCheck_927_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_tail_904_);
lean_inc(v_value_903_);
lean_inc(v_key_902_);
lean_dec(v_x_901_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_927_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_908_; uint64_t v___x_909_; uint64_t v___x_910_; uint64_t v___x_911_; uint64_t v_fold_912_; uint64_t v___x_913_; uint64_t v___x_914_; uint64_t v___x_915_; size_t v___x_916_; size_t v___x_917_; size_t v___x_918_; size_t v___x_919_; size_t v___x_920_; lean_object* v___x_921_; lean_object* v___x_923_; 
v___x_908_ = lean_array_get_size(v_x_900_);
v___x_909_ = l_Lean_Expr_hash(v_key_902_);
v___x_910_ = 32ULL;
v___x_911_ = lean_uint64_shift_right(v___x_909_, v___x_910_);
v_fold_912_ = lean_uint64_xor(v___x_909_, v___x_911_);
v___x_913_ = 16ULL;
v___x_914_ = lean_uint64_shift_right(v_fold_912_, v___x_913_);
v___x_915_ = lean_uint64_xor(v_fold_912_, v___x_914_);
v___x_916_ = lean_uint64_to_usize(v___x_915_);
v___x_917_ = lean_usize_of_nat(v___x_908_);
v___x_918_ = ((size_t)1ULL);
v___x_919_ = lean_usize_sub(v___x_917_, v___x_918_);
v___x_920_ = lean_usize_land(v___x_916_, v___x_919_);
v___x_921_ = lean_array_uget_borrowed(v_x_900_, v___x_920_);
lean_inc(v___x_921_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 2, v___x_921_);
v___x_923_ = v___x_906_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_key_902_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_value_903_);
lean_ctor_set(v_reuseFailAlloc_926_, 2, v___x_921_);
v___x_923_ = v_reuseFailAlloc_926_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
lean_object* v___x_924_; 
v___x_924_ = lean_array_uset(v_x_900_, v___x_920_, v___x_923_);
v_x_900_ = v___x_924_;
v_x_901_ = v_tail_904_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(lean_object* v_i_928_, lean_object* v_source_929_, lean_object* v_target_930_){
_start:
{
lean_object* v___x_931_; uint8_t v___x_932_; 
v___x_931_ = lean_array_get_size(v_source_929_);
v___x_932_ = lean_nat_dec_lt(v_i_928_, v___x_931_);
if (v___x_932_ == 0)
{
lean_dec_ref(v_source_929_);
lean_dec(v_i_928_);
return v_target_930_;
}
else
{
lean_object* v_es_933_; lean_object* v___x_934_; lean_object* v_source_935_; lean_object* v_target_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v_es_933_ = lean_array_fget(v_source_929_, v_i_928_);
v___x_934_ = lean_box(0);
v_source_935_ = lean_array_fset(v_source_929_, v_i_928_, v___x_934_);
v_target_936_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_target_930_, v_es_933_);
v___x_937_ = lean_unsigned_to_nat(1u);
v___x_938_ = lean_nat_add(v_i_928_, v___x_937_);
lean_dec(v_i_928_);
v_i_928_ = v___x_938_;
v_source_929_ = v_source_935_;
v_target_930_ = v_target_936_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(lean_object* v_data_940_){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v_nbuckets_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_941_ = lean_array_get_size(v_data_940_);
v___x_942_ = lean_unsigned_to_nat(2u);
v_nbuckets_943_ = lean_nat_mul(v___x_941_, v___x_942_);
v___x_944_ = lean_unsigned_to_nat(0u);
v___x_945_ = lean_box(0);
v___x_946_ = lean_mk_array(v_nbuckets_943_, v___x_945_);
v___x_947_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v___x_944_, v_data_940_, v___x_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(lean_object* v_a_948_, lean_object* v_b_949_, lean_object* v_x_950_){
_start:
{
if (lean_obj_tag(v_x_950_) == 0)
{
lean_dec(v_b_949_);
lean_dec_ref(v_a_948_);
return v_x_950_;
}
else
{
lean_object* v_key_951_; lean_object* v_value_952_; lean_object* v_tail_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_965_; 
v_key_951_ = lean_ctor_get(v_x_950_, 0);
v_value_952_ = lean_ctor_get(v_x_950_, 1);
v_tail_953_ = lean_ctor_get(v_x_950_, 2);
v_isSharedCheck_965_ = !lean_is_exclusive(v_x_950_);
if (v_isSharedCheck_965_ == 0)
{
v___x_955_ = v_x_950_;
v_isShared_956_ = v_isSharedCheck_965_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_tail_953_);
lean_inc(v_value_952_);
lean_inc(v_key_951_);
lean_dec(v_x_950_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_965_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
uint8_t v___x_957_; 
v___x_957_ = lean_expr_eqv(v_key_951_, v_a_948_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; lean_object* v___x_960_; 
v___x_958_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_948_, v_b_949_, v_tail_953_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 2, v___x_958_);
v___x_960_ = v___x_955_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_key_951_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_value_952_);
lean_ctor_set(v_reuseFailAlloc_961_, 2, v___x_958_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
else
{
lean_object* v___x_963_; 
lean_dec(v_value_952_);
lean_dec(v_key_951_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 1, v_b_949_);
lean_ctor_set(v___x_955_, 0, v_a_948_);
v___x_963_ = v___x_955_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_948_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_b_949_);
lean_ctor_set(v_reuseFailAlloc_964_, 2, v_tail_953_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(lean_object* v_a_966_, lean_object* v_x_967_){
_start:
{
if (lean_obj_tag(v_x_967_) == 0)
{
uint8_t v___x_968_; 
v___x_968_ = 0;
return v___x_968_;
}
else
{
lean_object* v_key_969_; lean_object* v_tail_970_; uint8_t v___x_971_; 
v_key_969_ = lean_ctor_get(v_x_967_, 0);
v_tail_970_ = lean_ctor_get(v_x_967_, 2);
v___x_971_ = lean_expr_eqv(v_key_969_, v_a_966_);
if (v___x_971_ == 0)
{
v_x_967_ = v_tail_970_;
goto _start;
}
else
{
return v___x_971_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg___boxed(lean_object* v_a_973_, lean_object* v_x_974_){
_start:
{
uint8_t v_res_975_; lean_object* v_r_976_; 
v_res_975_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_973_, v_x_974_);
lean_dec(v_x_974_);
lean_dec_ref(v_a_973_);
v_r_976_ = lean_box(v_res_975_);
return v_r_976_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(lean_object* v_m_977_, lean_object* v_a_978_, lean_object* v_b_979_){
_start:
{
lean_object* v_size_980_; lean_object* v_buckets_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_1024_; 
v_size_980_ = lean_ctor_get(v_m_977_, 0);
v_buckets_981_ = lean_ctor_get(v_m_977_, 1);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_m_977_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_983_ = v_m_977_;
v_isShared_984_ = v_isSharedCheck_1024_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_buckets_981_);
lean_inc(v_size_980_);
lean_dec(v_m_977_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_1024_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; uint64_t v___x_986_; uint64_t v___x_987_; uint64_t v___x_988_; uint64_t v_fold_989_; uint64_t v___x_990_; uint64_t v___x_991_; uint64_t v___x_992_; size_t v___x_993_; size_t v___x_994_; size_t v___x_995_; size_t v___x_996_; size_t v___x_997_; lean_object* v_bkt_998_; uint8_t v___x_999_; 
v___x_985_ = lean_array_get_size(v_buckets_981_);
v___x_986_ = l_Lean_Expr_hash(v_a_978_);
v___x_987_ = 32ULL;
v___x_988_ = lean_uint64_shift_right(v___x_986_, v___x_987_);
v_fold_989_ = lean_uint64_xor(v___x_986_, v___x_988_);
v___x_990_ = 16ULL;
v___x_991_ = lean_uint64_shift_right(v_fold_989_, v___x_990_);
v___x_992_ = lean_uint64_xor(v_fold_989_, v___x_991_);
v___x_993_ = lean_uint64_to_usize(v___x_992_);
v___x_994_ = lean_usize_of_nat(v___x_985_);
v___x_995_ = ((size_t)1ULL);
v___x_996_ = lean_usize_sub(v___x_994_, v___x_995_);
v___x_997_ = lean_usize_land(v___x_993_, v___x_996_);
v_bkt_998_ = lean_array_uget_borrowed(v_buckets_981_, v___x_997_);
v___x_999_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_978_, v_bkt_998_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; lean_object* v_size_x27_1001_; lean_object* v___x_1002_; lean_object* v_buckets_x27_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; uint8_t v___x_1009_; 
v___x_1000_ = lean_unsigned_to_nat(1u);
v_size_x27_1001_ = lean_nat_add(v_size_980_, v___x_1000_);
lean_dec(v_size_980_);
lean_inc(v_bkt_998_);
v___x_1002_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1002_, 0, v_a_978_);
lean_ctor_set(v___x_1002_, 1, v_b_979_);
lean_ctor_set(v___x_1002_, 2, v_bkt_998_);
v_buckets_x27_1003_ = lean_array_uset(v_buckets_981_, v___x_997_, v___x_1002_);
v___x_1004_ = lean_unsigned_to_nat(4u);
v___x_1005_ = lean_nat_mul(v_size_x27_1001_, v___x_1004_);
v___x_1006_ = lean_unsigned_to_nat(3u);
v___x_1007_ = lean_nat_div(v___x_1005_, v___x_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_array_get_size(v_buckets_x27_1003_);
v___x_1009_ = lean_nat_dec_le(v___x_1007_, v___x_1008_);
lean_dec(v___x_1007_);
if (v___x_1009_ == 0)
{
lean_object* v_val_1010_; lean_object* v___x_1012_; 
v_val_1010_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_buckets_x27_1003_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 1, v_val_1010_);
lean_ctor_set(v___x_983_, 0, v_size_x27_1001_);
v___x_1012_ = v___x_983_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_size_x27_1001_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_val_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
else
{
lean_object* v___x_1015_; 
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 1, v_buckets_x27_1003_);
lean_ctor_set(v___x_983_, 0, v_size_x27_1001_);
v___x_1015_ = v___x_983_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_size_x27_1001_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_buckets_x27_1003_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
else
{
lean_object* v___x_1017_; lean_object* v_buckets_x27_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1022_; 
lean_inc(v_bkt_998_);
v___x_1017_ = lean_box(0);
v_buckets_x27_1018_ = lean_array_uset(v_buckets_981_, v___x_997_, v___x_1017_);
v___x_1019_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_978_, v_b_979_, v_bkt_998_);
v___x_1020_ = lean_array_uset(v_buckets_x27_1018_, v___x_997_, v___x_1019_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 1, v___x_1020_);
v___x_1022_ = v___x_983_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_size_980_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v___x_1020_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(lean_object* v_a_1025_, lean_object* v_e_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1029_ = lean_st_ref_take(v_a_1025_);
v___x_1030_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v___x_1029_, v_e_1026_, v_a_1027_);
v___x_1031_ = lean_st_ref_set(v_a_1025_, v___x_1030_);
v___x_1032_ = lean_box(0);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed(lean_object* v_a_1033_, lean_object* v_e_1034_, lean_object* v_a_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(v_a_1033_, v_e_1034_, v_a_1035_);
lean_dec(v_a_1033_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1038_, lean_object* v_e_1039_, lean_object* v_a_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1038_, v_e_1039_, v_a_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec(v_a_1040_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(lean_object* v_fn_1048_, lean_object* v_e_1049_, lean_object* v_a_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v_a_1058_; lean_object* v___y_1070_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
lean_inc(v_a_1050_);
v___x_1072_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1072_, 0, lean_box(0));
lean_closure_set(v___x_1072_, 1, lean_box(0));
lean_closure_set(v___x_1072_, 2, v_a_1050_);
v___x_1073_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___x_1072_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1110_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1076_ = v___x_1073_;
v_isShared_1077_ = v_isSharedCheck_1110_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1073_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1110_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_a_1074_, v_e_1049_);
lean_dec(v_a_1074_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v___x_1079_; 
lean_del_object(v___x_1076_);
lean_inc_ref(v_fn_1048_);
lean_inc(v___y_1055_);
lean_inc_ref(v___y_1054_);
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
lean_inc(v___y_1051_);
lean_inc_ref(v_e_1049_);
v___x_1079_ = lean_apply_7(v_fn_1048_, v_e_1049_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, lean_box(0));
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; uint8_t v___x_1081_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref(v___x_1079_);
v___x_1081_ = lean_unbox(v_a_1080_);
lean_dec(v_a_1080_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; 
lean_dec_ref(v_fn_1048_);
v___x_1082_ = lean_box(0);
v_a_1058_ = v___x_1082_;
goto v___jp_1057_;
}
else
{
switch(lean_obj_tag(v_e_1049_))
{
case 7:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1083_, 0, v_fn_1048_);
lean_inc_ref(v_e_1049_);
v___x_1084_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v___x_1083_, v_e_1049_, v_a_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
v___y_1070_ = v___x_1084_;
goto v___jp_1069_;
}
case 6:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1085_, 0, v_fn_1048_);
lean_inc_ref(v_e_1049_);
v___x_1086_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v___x_1085_, v_e_1049_, v_a_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
v___y_1070_ = v___x_1086_;
goto v___jp_1069_;
}
case 8:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1087_, 0, v_fn_1048_);
lean_inc_ref(v_e_1049_);
v___x_1088_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v___x_1087_, v_e_1049_, v_a_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
v___y_1070_ = v___x_1088_;
goto v___jp_1069_;
}
case 5:
{
lean_object* v_fn_1089_; lean_object* v_arg_1090_; lean_object* v___x_1091_; 
v_fn_1089_ = lean_ctor_get(v_e_1049_, 0);
v_arg_1090_ = lean_ctor_get(v_e_1049_, 1);
lean_inc_ref(v_fn_1089_);
lean_inc_ref(v_fn_1048_);
v___x_1091_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1048_, v_fn_1089_, v_a_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v___x_1092_; 
lean_dec_ref(v___x_1091_);
lean_inc_ref(v_arg_1090_);
v___x_1092_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1048_, v_arg_1090_, v_a_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
v___y_1070_ = v___x_1092_;
goto v___jp_1069_;
}
else
{
lean_dec_ref(v_fn_1048_);
v___y_1070_ = v___x_1091_;
goto v___jp_1069_;
}
}
case 10:
{
lean_object* v_expr_1093_; lean_object* v___x_1094_; 
v_expr_1093_ = lean_ctor_get(v_e_1049_, 1);
lean_inc_ref(v_expr_1093_);
v___x_1094_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1048_, v_expr_1093_, v_a_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
v___y_1070_ = v___x_1094_;
goto v___jp_1069_;
}
case 11:
{
lean_object* v_struct_1095_; lean_object* v___x_1096_; 
v_struct_1095_ = lean_ctor_get(v_e_1049_, 2);
lean_inc_ref(v_struct_1095_);
v___x_1096_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1048_, v_struct_1095_, v_a_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
v___y_1070_ = v___x_1096_;
goto v___jp_1069_;
}
default: 
{
lean_object* v___x_1097_; 
lean_dec_ref(v_fn_1048_);
v___x_1097_ = lean_box(0);
v_a_1058_ = v___x_1097_;
goto v___jp_1057_;
}
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec_ref(v_e_1049_);
lean_dec_ref(v_fn_1048_);
v_a_1098_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1079_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1079_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
else
{
lean_object* v_val_1106_; lean_object* v___x_1108_; 
lean_dec_ref(v_e_1049_);
lean_dec_ref(v_fn_1048_);
v_val_1106_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_val_1106_);
lean_dec_ref(v___x_1078_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v_val_1106_);
v___x_1108_ = v___x_1076_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_val_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec_ref(v_e_1049_);
lean_dec_ref(v_fn_1048_);
v_a_1111_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1073_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1073_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
v___jp_1057_:
{
lean_object* v___f_1059_; lean_object* v___x_1060_; 
lean_inc(v_a_1050_);
v___f_1059_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1059_, 0, v_a_1050_);
lean_closure_set(v___f_1059_, 1, v_e_1049_);
lean_closure_set(v___f_1059_, 2, v_a_1058_);
v___x_1060_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___f_1059_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1067_ == 0)
{
lean_object* v_unused_1068_; 
v_unused_1068_ = lean_ctor_get(v___x_1060_, 0);
lean_dec(v_unused_1068_);
v___x_1062_ = v___x_1060_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_dec(v___x_1060_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 0, v_a_1058_);
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1058_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
else
{
return v___x_1060_;
}
}
v___jp_1069_:
{
if (lean_obj_tag(v___y_1070_) == 0)
{
lean_object* v_a_1071_; 
v_a_1071_ = lean_ctor_get(v___y_1070_, 0);
lean_inc(v_a_1071_);
lean_dec_ref(v___y_1070_);
v_a_1058_ = v_a_1071_;
goto v___jp_1057_;
}
else
{
lean_dec_ref(v_e_1049_);
return v___y_1070_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1119_ = lean_box(0);
v___x_1120_ = lean_unsigned_to_nat(16u);
v___x_1121_ = lean_mk_array(v___x_1120_, v___x_1119_);
return v___x_1121_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1122_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0);
v___x_1123_ = lean_unsigned_to_nat(0u);
v___x_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
lean_ctor_set(v___x_1124_, 1, v___x_1122_);
return v___x_1124_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1);
v___x_1126_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1126_, 0, lean_box(0));
lean_closure_set(v___x_1126_, 1, lean_box(0));
lean_closure_set(v___x_1126_, 2, v___x_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(lean_object* v_input_1127_, lean_object* v_fn_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v_a_1137_; lean_object* v___x_1138_; 
v___x_1135_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2);
v___x_1136_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1135_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_a_1137_);
lean_dec_ref(v___x_1136_);
v___x_1138_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1128_, v_input_1127_, v_a_1137_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_a_1139_);
lean_dec_ref(v___x_1138_);
v___x_1140_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1140_, 0, lean_box(0));
lean_closure_set(v___x_1140_, 1, lean_box(0));
lean_closure_set(v___x_1140_, 2, v_a_1137_);
v___x_1141_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1140_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1148_ == 0)
{
lean_object* v_unused_1149_; 
v_unused_1149_ = lean_ctor_get(v___x_1141_, 0);
lean_dec(v_unused_1149_);
v___x_1143_ = v___x_1141_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_dec(v___x_1141_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 0, v_a_1139_);
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1139_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
else
{
lean_dec(v_a_1137_);
return v___x_1138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___boxed(lean_object* v_input_1150_, lean_object* v_fn_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1150_, v_fn_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(lean_object* v_input_1159_, lean_object* v_fn_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v___f_1167_; lean_object* v___x_1168_; 
v___f_1167_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1167_, 0, v_fn_1160_);
v___x_1168_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1159_, v___f_1167_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___boxed(lean_object* v_input_1169_, lean_object* v_fn_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_input_1169_, v_fn_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(lean_object* v_fn_1178_, lean_object* v_x_1179_, lean_object* v_x_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
if (lean_obj_tag(v_x_1180_) == 0)
{
lean_object* v___x_1187_; 
lean_dec_ref(v_fn_1178_);
v___x_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1187_, 0, v_x_1179_);
return v___x_1187_;
}
else
{
lean_object* v_head_1188_; lean_object* v_tail_1189_; lean_object* v_type_1190_; lean_object* v___x_1191_; 
v_head_1188_ = lean_ctor_get(v_x_1180_, 0);
lean_inc(v_head_1188_);
v_tail_1189_ = lean_ctor_get(v_x_1180_, 1);
lean_inc(v_tail_1189_);
lean_dec_ref(v_x_1180_);
v_type_1190_ = lean_ctor_get(v_head_1188_, 1);
lean_inc_ref(v_type_1190_);
lean_dec(v_head_1188_);
lean_inc_ref(v_fn_1178_);
v___x_1191_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1190_, v_fn_1178_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_a_1192_);
lean_dec_ref(v___x_1191_);
v_x_1179_ = v_a_1192_;
v_x_1180_ = v_tail_1189_;
goto _start;
}
else
{
lean_dec(v_tail_1189_);
lean_dec_ref(v_fn_1178_);
return v___x_1191_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4___boxed(lean_object* v_fn_1194_, lean_object* v_x_1195_, lean_object* v_x_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1194_, v_x_1195_, v_x_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(lean_object* v_fn_1204_, lean_object* v_x_1205_, lean_object* v_x_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
if (lean_obj_tag(v_x_1206_) == 0)
{
lean_object* v___x_1213_; 
lean_dec_ref(v_fn_1204_);
v___x_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1213_, 0, v_x_1205_);
return v___x_1213_;
}
else
{
lean_object* v_head_1214_; lean_object* v_tail_1215_; lean_object* v___y_1217_; lean_object* v_type_1220_; lean_object* v_ctors_1221_; lean_object* v___x_1222_; 
v_head_1214_ = lean_ctor_get(v_x_1206_, 0);
lean_inc(v_head_1214_);
v_tail_1215_ = lean_ctor_get(v_x_1206_, 1);
lean_inc(v_tail_1215_);
lean_dec_ref(v_x_1206_);
v_type_1220_ = lean_ctor_get(v_head_1214_, 1);
lean_inc_ref(v_type_1220_);
v_ctors_1221_ = lean_ctor_get(v_head_1214_, 2);
lean_inc(v_ctors_1221_);
lean_dec(v_head_1214_);
lean_inc_ref(v_fn_1204_);
v___x_1222_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1220_, v_fn_1204_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v___x_1224_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_a_1223_);
lean_dec_ref(v___x_1222_);
lean_inc_ref(v_fn_1204_);
v___x_1224_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1204_, v_a_1223_, v_ctors_1221_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
v___y_1217_ = v___x_1224_;
goto v___jp_1216_;
}
else
{
lean_dec(v_ctors_1221_);
v___y_1217_ = v___x_1222_;
goto v___jp_1216_;
}
v___jp_1216_:
{
if (lean_obj_tag(v___y_1217_) == 0)
{
lean_object* v_a_1218_; 
v_a_1218_ = lean_ctor_get(v___y_1217_, 0);
lean_inc(v_a_1218_);
lean_dec_ref(v___y_1217_);
v_x_1205_ = v_a_1218_;
v_x_1206_ = v_tail_1215_;
goto _start;
}
else
{
lean_dec(v_tail_1215_);
lean_dec_ref(v_fn_1204_);
return v___y_1217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6___boxed(lean_object* v_fn_1225_, lean_object* v_x_1226_, lean_object* v_x_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1225_, v_x_1226_, v_x_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(lean_object* v_fn_1235_, lean_object* v_x_1236_, lean_object* v_x_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
if (lean_obj_tag(v_x_1237_) == 0)
{
lean_object* v___x_1244_; 
lean_dec_ref(v_fn_1235_);
v___x_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1244_, 0, v_x_1236_);
return v___x_1244_;
}
else
{
lean_object* v_head_1245_; lean_object* v_tail_1246_; lean_object* v___y_1248_; lean_object* v_toConstantVal_1251_; lean_object* v_value_1252_; lean_object* v_type_1253_; lean_object* v___x_1254_; 
v_head_1245_ = lean_ctor_get(v_x_1237_, 0);
lean_inc(v_head_1245_);
v_tail_1246_ = lean_ctor_get(v_x_1237_, 1);
lean_inc(v_tail_1246_);
lean_dec_ref(v_x_1237_);
v_toConstantVal_1251_ = lean_ctor_get(v_head_1245_, 0);
lean_inc_ref(v_toConstantVal_1251_);
v_value_1252_ = lean_ctor_get(v_head_1245_, 1);
lean_inc_ref(v_value_1252_);
lean_dec(v_head_1245_);
v_type_1253_ = lean_ctor_get(v_toConstantVal_1251_, 2);
lean_inc_ref(v_type_1253_);
lean_dec_ref(v_toConstantVal_1251_);
lean_inc_ref(v_fn_1235_);
v___x_1254_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1253_, v_fn_1235_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v___x_1255_; 
lean_dec_ref(v___x_1254_);
lean_inc_ref(v_fn_1235_);
v___x_1255_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1252_, v_fn_1235_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
v___y_1248_ = v___x_1255_;
goto v___jp_1247_;
}
else
{
lean_dec_ref(v_value_1252_);
v___y_1248_ = v___x_1254_;
goto v___jp_1247_;
}
v___jp_1247_:
{
if (lean_obj_tag(v___y_1248_) == 0)
{
lean_object* v_a_1249_; 
v_a_1249_ = lean_ctor_get(v___y_1248_, 0);
lean_inc(v_a_1249_);
lean_dec_ref(v___y_1248_);
v_x_1236_ = v_a_1249_;
v_x_1237_ = v_tail_1246_;
goto _start;
}
else
{
lean_dec(v_tail_1246_);
lean_dec_ref(v_fn_1235_);
return v___y_1248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1256_, lean_object* v_x_1257_, lean_object* v_x_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1256_, v_x_1257_, v_x_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v___y_1259_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(lean_object* v_fn_1266_, lean_object* v_d_1267_, lean_object* v_a_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
switch(lean_obj_tag(v_d_1267_))
{
case 0:
{
lean_object* v_val_1275_; lean_object* v_toConstantVal_1276_; lean_object* v_type_1277_; lean_object* v___x_1278_; 
v_val_1275_ = lean_ctor_get(v_d_1267_, 0);
lean_inc_ref(v_val_1275_);
lean_dec_ref(v_d_1267_);
v_toConstantVal_1276_ = lean_ctor_get(v_val_1275_, 0);
lean_inc_ref(v_toConstantVal_1276_);
lean_dec_ref(v_val_1275_);
v_type_1277_ = lean_ctor_get(v_toConstantVal_1276_, 2);
lean_inc_ref(v_type_1277_);
lean_dec_ref(v_toConstantVal_1276_);
v___x_1278_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1277_, v_fn_1266_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
return v___x_1278_;
}
case 4:
{
lean_object* v___x_1279_; 
lean_dec_ref(v_fn_1266_);
v___x_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1279_, 0, v_a_1268_);
return v___x_1279_;
}
case 5:
{
lean_object* v_defns_1280_; lean_object* v___x_1281_; 
v_defns_1280_ = lean_ctor_get(v_d_1267_, 0);
lean_inc(v_defns_1280_);
lean_dec_ref(v_d_1267_);
v___x_1281_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1266_, v_a_1268_, v_defns_1280_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
return v___x_1281_;
}
case 6:
{
lean_object* v_types_1282_; lean_object* v___x_1283_; 
v_types_1282_ = lean_ctor_get(v_d_1267_, 2);
lean_inc(v_types_1282_);
lean_dec_ref(v_d_1267_);
v___x_1283_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1266_, v_a_1268_, v_types_1282_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
return v___x_1283_;
}
default: 
{
lean_object* v_val_1284_; lean_object* v_toConstantVal_1285_; lean_object* v_value_1286_; lean_object* v_type_1287_; lean_object* v___x_1288_; 
v_val_1284_ = lean_ctor_get(v_d_1267_, 0);
lean_inc_ref(v_val_1284_);
lean_dec(v_d_1267_);
v_toConstantVal_1285_ = lean_ctor_get(v_val_1284_, 0);
lean_inc_ref(v_toConstantVal_1285_);
v_value_1286_ = lean_ctor_get(v_val_1284_, 1);
lean_inc_ref(v_value_1286_);
lean_dec_ref(v_val_1284_);
v_type_1287_ = lean_ctor_get(v_toConstantVal_1285_, 2);
lean_inc_ref(v_type_1287_);
lean_dec_ref(v_toConstantVal_1285_);
lean_inc_ref(v_fn_1266_);
v___x_1288_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1287_, v_fn_1266_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v___x_1289_; 
lean_dec_ref(v___x_1288_);
v___x_1289_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1286_, v_fn_1266_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
return v___x_1289_;
}
else
{
lean_dec_ref(v_value_1286_);
lean_dec_ref(v_fn_1266_);
return v___x_1288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2___boxed(lean_object* v_fn_1290_, lean_object* v_d_1291_, lean_object* v_a_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1290_, v_d_1291_, v_a_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(lean_object* v_decl_1300_, lean_object* v_fn_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = lean_box(0);
v___x_1309_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1301_, v_decl_1300_, v___x_1308_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1___boxed(lean_object* v_decl_1310_, lean_object* v_fn_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1310_, v_fn_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
return v_res_1318_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__0(void){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1319_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__1(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__0, &l_Lean_warnIfUsesSorry___closed__0_once, _init_l_Lean_warnIfUsesSorry___closed__0);
v___x_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
return v___x_1321_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__2(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1322_ = lean_box(1);
v___x_1323_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_1324_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1325_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
lean_ctor_set(v___x_1325_, 1, v___x_1323_);
lean_ctor_set(v___x_1325_, 2, v___x_1322_);
return v___x_1325_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__4(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1328_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1329_ = lean_unsigned_to_nat(0u);
v___x_1330_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
lean_ctor_set(v___x_1330_, 2, v___x_1329_);
lean_ctor_set(v___x_1330_, 3, v___x_1328_);
lean_ctor_set(v___x_1330_, 4, v___x_1328_);
lean_ctor_set(v___x_1330_, 5, v___x_1328_);
lean_ctor_set(v___x_1330_, 6, v___x_1328_);
lean_ctor_set(v___x_1330_, 7, v___x_1328_);
lean_ctor_set(v___x_1330_, 8, v___x_1328_);
return v___x_1330_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__5(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1332_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
lean_ctor_set(v___x_1332_, 2, v___x_1331_);
lean_ctor_set(v___x_1332_, 3, v___x_1331_);
lean_ctor_set(v___x_1332_, 4, v___x_1331_);
lean_ctor_set(v___x_1332_, 5, v___x_1331_);
return v___x_1332_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__6(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
lean_ctor_set(v___x_1334_, 1, v___x_1333_);
lean_ctor_set(v___x_1334_, 2, v___x_1333_);
lean_ctor_set(v___x_1334_, 3, v___x_1333_);
lean_ctor_set(v___x_1334_, 4, v___x_1333_);
return v___x_1334_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__7(void){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1335_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__6, &l_Lean_warnIfUsesSorry___closed__6_once, _init_l_Lean_warnIfUsesSorry___closed__6);
v___x_1336_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_1337_ = lean_box(1);
v___x_1338_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__5, &l_Lean_warnIfUsesSorry___closed__5_once, _init_l_Lean_warnIfUsesSorry___closed__5);
v___x_1339_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__4, &l_Lean_warnIfUsesSorry___closed__4_once, _init_l_Lean_warnIfUsesSorry___closed__4);
v___x_1340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
lean_ctor_set(v___x_1340_, 1, v___x_1338_);
lean_ctor_set(v___x_1340_, 2, v___x_1337_);
lean_ctor_set(v___x_1340_, 3, v___x_1336_);
lean_ctor_set(v___x_1340_, 4, v___x_1335_);
return v___x_1340_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__12(void){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__11));
v___x_1347_ = l_Lean_stringToMessageData(v___x_1346_);
return v___x_1347_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__14(void){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__13));
v___x_1350_ = l_Lean_stringToMessageData(v___x_1349_);
return v___x_1350_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__16(void){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__15));
v___x_1353_ = l_Lean_stringToMessageData(v___x_1352_);
return v___x_1353_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__17(void){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1354_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__16, &l_Lean_warnIfUsesSorry___closed__16_once, _init_l_Lean_warnIfUsesSorry___closed__16);
v___x_1355_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__10));
v___x_1356_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
lean_ctor_set(v___x_1356_, 1, v___x_1354_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry(lean_object* v_decl_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v_options_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v_options_1364_ = lean_ctor_get(v_a_1361_, 2);
v___x_1365_ = l_Lean_warn_sorry;
v___x_1366_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_1364_, v___x_1365_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
lean_dec(v_decl_1360_);
v___x_1367_ = lean_box(0);
v___x_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
return v___x_1368_;
}
else
{
lean_object* v___x_1369_; lean_object* v_messages_1373_; uint8_t v___x_1374_; 
v___x_1369_ = lean_st_ref_get(v_a_1362_);
v_messages_1373_ = lean_ctor_get(v___x_1369_, 6);
lean_inc_ref(v_messages_1373_);
lean_dec(v___x_1369_);
v___x_1374_ = l_Lean_MessageLog_hasErrors(v_messages_1373_);
lean_dec_ref(v_messages_1373_);
if (v___x_1374_ == 0)
{
if (v___x_1366_ == 0)
{
lean_dec(v_decl_1360_);
goto v___jp_1370_;
}
else
{
uint8_t v___x_1375_; 
v___x_1375_ = l_Lean_Declaration_hasSorry(v_decl_1360_);
if (v___x_1375_ == 0)
{
lean_dec(v_decl_1360_);
goto v___jp_1370_;
}
else
{
uint8_t v___x_1376_; uint8_t v___x_1377_; uint8_t v___x_1378_; lean_object* v___x_1379_; uint64_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___f_1391_; lean_object* v___x_1392_; 
v___x_1376_ = 1;
v___x_1377_ = 0;
v___x_1378_ = 2;
v___x_1379_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_1379_, 0, v___x_1374_);
lean_ctor_set_uint8(v___x_1379_, 1, v___x_1374_);
lean_ctor_set_uint8(v___x_1379_, 2, v___x_1374_);
lean_ctor_set_uint8(v___x_1379_, 3, v___x_1374_);
lean_ctor_set_uint8(v___x_1379_, 4, v___x_1374_);
lean_ctor_set_uint8(v___x_1379_, 5, v___x_1375_);
lean_ctor_set_uint8(v___x_1379_, 6, v___x_1375_);
lean_ctor_set_uint8(v___x_1379_, 7, v___x_1374_);
lean_ctor_set_uint8(v___x_1379_, 8, v___x_1375_);
lean_ctor_set_uint8(v___x_1379_, 9, v___x_1376_);
lean_ctor_set_uint8(v___x_1379_, 10, v___x_1377_);
lean_ctor_set_uint8(v___x_1379_, 11, v___x_1375_);
lean_ctor_set_uint8(v___x_1379_, 12, v___x_1375_);
lean_ctor_set_uint8(v___x_1379_, 13, v___x_1375_);
lean_ctor_set_uint8(v___x_1379_, 14, v___x_1378_);
lean_ctor_set_uint8(v___x_1379_, 15, v___x_1375_);
lean_ctor_set_uint8(v___x_1379_, 16, v___x_1375_);
lean_ctor_set_uint8(v___x_1379_, 17, v___x_1375_);
lean_ctor_set_uint8(v___x_1379_, 18, v___x_1375_);
v___x_1380_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1379_);
v___x_1381_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1381_, 0, v___x_1379_);
lean_ctor_set_uint64(v___x_1381_, sizeof(void*)*1, v___x_1380_);
v___x_1382_ = lean_box(1);
v___x_1383_ = lean_unsigned_to_nat(0u);
v___x_1384_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1385_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__3));
v___x_1386_ = lean_box(0);
v___x_1387_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1387_, 0, v___x_1381_);
lean_ctor_set(v___x_1387_, 1, v___x_1382_);
lean_ctor_set(v___x_1387_, 2, v___x_1384_);
lean_ctor_set(v___x_1387_, 3, v___x_1385_);
lean_ctor_set(v___x_1387_, 4, v___x_1386_);
lean_ctor_set(v___x_1387_, 5, v___x_1383_);
lean_ctor_set(v___x_1387_, 6, v___x_1386_);
lean_ctor_set_uint8(v___x_1387_, sizeof(void*)*7, v___x_1374_);
lean_ctor_set_uint8(v___x_1387_, sizeof(void*)*7 + 1, v___x_1374_);
lean_ctor_set_uint8(v___x_1387_, sizeof(void*)*7 + 2, v___x_1374_);
lean_ctor_set_uint8(v___x_1387_, sizeof(void*)*7 + 3, v___x_1366_);
v___x_1388_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__7, &l_Lean_warnIfUsesSorry___closed__7_once, _init_l_Lean_warnIfUsesSorry___closed__7);
v___x_1389_ = lean_st_mk_ref(v___x_1388_);
v___x_1390_ = lean_st_mk_ref(v___x_1385_);
v___f_1391_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__8));
v___x_1392_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1360_, v___f_1391_, v___x_1390_, v___x_1387_, v___x_1389_, v_a_1361_, v_a_1362_);
lean_dec_ref(v___x_1387_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v_val_1396_; lean_object* v___x_1418_; size_t v_sz_1419_; size_t v___x_1420_; lean_object* v___x_1421_; lean_object* v_fst_1422_; 
lean_dec_ref(v___x_1392_);
v___x_1393_ = lean_st_ref_get(v___x_1390_);
lean_dec(v___x_1390_);
v___x_1394_ = lean_st_ref_get(v___x_1389_);
lean_dec(v___x_1389_);
lean_dec(v___x_1394_);
v___x_1418_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__18));
v_sz_1419_ = lean_array_size(v___x_1393_);
v___x_1420_ = ((size_t)0ULL);
v___x_1421_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v___x_1393_, v_sz_1419_, v___x_1420_, v___x_1418_);
v_fst_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_fst_1422_);
lean_dec_ref(v___x_1421_);
if (lean_obj_tag(v_fst_1422_) == 0)
{
goto v___jp_1412_;
}
else
{
lean_object* v_val_1423_; 
v_val_1423_ = lean_ctor_get(v_fst_1422_, 0);
lean_inc(v_val_1423_);
lean_dec_ref(v_fst_1422_);
if (lean_obj_tag(v_val_1423_) == 0)
{
goto v___jp_1412_;
}
else
{
lean_object* v_val_1424_; 
lean_dec(v___x_1393_);
v_val_1424_ = lean_ctor_get(v_val_1423_, 0);
lean_inc(v_val_1424_);
lean_dec_ref(v_val_1423_);
v_val_1396_ = v_val_1424_;
goto v___jp_1395_;
}
}
v___jp_1395_:
{
lean_object* v_snd_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1410_; 
v_snd_1397_ = lean_ctor_get(v_val_1396_, 1);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_val_1396_);
if (v_isSharedCheck_1410_ == 0)
{
lean_object* v_unused_1411_; 
v_unused_1411_ = lean_ctor_get(v_val_1396_, 0);
lean_dec(v_unused_1411_);
v___x_1399_ = v_val_1396_;
v_isShared_1400_ = v_isSharedCheck_1410_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_snd_1397_);
lean_dec(v_val_1396_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1410_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1401_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__10));
v___x_1402_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__12, &l_Lean_warnIfUsesSorry___closed__12_once, _init_l_Lean_warnIfUsesSorry___closed__12);
if (v_isShared_1400_ == 0)
{
lean_ctor_set_tag(v___x_1399_, 7);
lean_ctor_set(v___x_1399_, 0, v___x_1402_);
v___x_1404_ = v___x_1399_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1402_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_snd_1397_);
v___x_1404_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1405_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__14, &l_Lean_warnIfUsesSorry___closed__14_once, _init_l_Lean_warnIfUsesSorry___closed__14);
v___x_1406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1404_);
lean_ctor_set(v___x_1406_, 1, v___x_1405_);
v___x_1407_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1401_);
lean_ctor_set(v___x_1407_, 1, v___x_1406_);
v___x_1408_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1407_, v_a_1361_, v_a_1362_);
return v___x_1408_;
}
}
}
v___jp_1412_:
{
lean_object* v___x_1413_; uint8_t v___x_1414_; 
v___x_1413_ = lean_array_get_size(v___x_1393_);
v___x_1414_ = lean_nat_dec_lt(v___x_1383_, v___x_1413_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
lean_dec(v___x_1393_);
v___x_1415_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__17, &l_Lean_warnIfUsesSorry___closed__17_once, _init_l_Lean_warnIfUsesSorry___closed__17);
v___x_1416_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1415_, v_a_1361_, v_a_1362_);
return v___x_1416_;
}
else
{
lean_object* v___x_1417_; 
v___x_1417_ = lean_array_fget(v___x_1393_, v___x_1383_);
lean_dec(v___x_1393_);
v_val_1396_ = v___x_1417_;
goto v___jp_1395_;
}
}
}
else
{
lean_dec(v___x_1390_);
lean_dec(v___x_1389_);
return v___x_1392_;
}
}
}
}
else
{
lean_dec(v_decl_1360_);
goto v___jp_1370_;
}
v___jp_1370_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = lean_box(0);
v___x_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
return v___x_1372_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___boxed(lean_object* v_decl_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Lean_warnIfUsesSorry(v_decl_1425_, v_a_1426_, v_a_1427_);
lean_dec(v_a_1427_);
lean_dec_ref(v_a_1426_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1430_, lean_object* v_m_1431_, lean_object* v_a_1432_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1431_, v_a_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1434_, lean_object* v_m_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(v_00_u03b2_1434_, v_m_1435_, v_a_1436_);
lean_dec_ref(v_a_1436_);
lean_dec_ref(v_m_1435_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_1438_, lean_object* v_m_1439_, lean_object* v_a_1440_, lean_object* v_b_1441_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_m_1439_, v_a_1440_, v_b_1441_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_1443_, lean_object* v_a_1444_, lean_object* v_x_1445_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1444_, v_x_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1447_, lean_object* v_a_1448_, lean_object* v_x_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(v_00_u03b2_1447_, v_a_1448_, v_x_1449_);
lean_dec(v_x_1449_);
lean_dec_ref(v_a_1448_);
return v_res_1450_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(lean_object* v_00_u03b2_1451_, lean_object* v_a_1452_, lean_object* v_x_1453_){
_start:
{
uint8_t v___x_1454_; 
v___x_1454_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1452_, v_x_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___boxed(lean_object* v_00_u03b2_1455_, lean_object* v_a_1456_, lean_object* v_x_1457_){
_start:
{
uint8_t v_res_1458_; lean_object* v_r_1459_; 
v_res_1458_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(v_00_u03b2_1455_, v_a_1456_, v_x_1457_);
lean_dec(v_x_1457_);
lean_dec_ref(v_a_1456_);
v_r_1459_ = lean_box(v_res_1458_);
return v_r_1459_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17(lean_object* v_00_u03b2_1460_, lean_object* v_data_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_data_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18(lean_object* v_00_u03b2_1463_, lean_object* v_a_1464_, lean_object* v_b_1465_, lean_object* v_x_1466_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1464_, v_b_1465_, v_x_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(lean_object* v_00_u03b1_1468_, lean_object* v_name_1469_, uint8_t v_bi_1470_, lean_object* v_type_1471_, lean_object* v_k_1472_, uint8_t v_kind_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_1469_, v_bi_1470_, v_type_1471_, v_k_1472_, v_kind_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___boxed(lean_object* v_00_u03b1_1482_, lean_object* v_name_1483_, lean_object* v_bi_1484_, lean_object* v_type_1485_, lean_object* v_k_1486_, lean_object* v_kind_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
uint8_t v_bi_boxed_1495_; uint8_t v_kind_boxed_1496_; lean_object* v_res_1497_; 
v_bi_boxed_1495_ = lean_unbox(v_bi_1484_);
v_kind_boxed_1496_ = lean_unbox(v_kind_1487_);
v_res_1497_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(v_00_u03b1_1482_, v_name_1483_, v_bi_boxed_1495_, v_type_1485_, v_k_1486_, v_kind_boxed_1496_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec(v___y_1488_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(lean_object* v_00_u03b1_1498_, lean_object* v_name_1499_, lean_object* v_type_1500_, lean_object* v_val_1501_, lean_object* v_k_1502_, uint8_t v_nondep_1503_, uint8_t v_kind_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_1499_, v_type_1500_, v_val_1501_, v_k_1502_, v_nondep_1503_, v_kind_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___boxed(lean_object* v_00_u03b1_1513_, lean_object* v_name_1514_, lean_object* v_type_1515_, lean_object* v_val_1516_, lean_object* v_k_1517_, lean_object* v_nondep_1518_, lean_object* v_kind_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
uint8_t v_nondep_boxed_1527_; uint8_t v_kind_boxed_1528_; lean_object* v_res_1529_; 
v_nondep_boxed_1527_ = lean_unbox(v_nondep_1518_);
v_kind_boxed_1528_ = lean_unbox(v_kind_1519_);
v_res_1529_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(v_00_u03b1_1513_, v_name_1514_, v_type_1515_, v_val_1516_, v_k_1517_, v_nondep_boxed_1527_, v_kind_boxed_1528_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec(v___y_1520_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18(lean_object* v_00_u03b2_1530_, lean_object* v_i_1531_, lean_object* v_source_1532_, lean_object* v_target_1533_){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v_i_1531_, v_source_1532_, v_target_1533_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22(lean_object* v_00_u03b2_1535_, lean_object* v_x_1536_, lean_object* v_x_1537_){
_start:
{
lean_object* v___x_1538_; 
v___x_1538_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_x_1536_, v_x_1537_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1588_; uint8_t v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1588_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1589_ = 0;
v___x_1590_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__20_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1591_ = l_Lean_registerTraceClass(v___x_1588_, v___x_1589_, v___x_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2____boxed(lean_object* v_a_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_();
return v_res_1593_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1594_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1595_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__0);
v___x_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
return v___x_1596_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__1);
v___x_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(lean_object* v_env_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v___x_1602_; lean_object* v_nextMacroScope_1603_; lean_object* v_ngen_1604_; lean_object* v_auxDeclNGen_1605_; lean_object* v_traceState_1606_; lean_object* v_messages_1607_; lean_object* v_infoState_1608_; lean_object* v_snapshotTasks_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1620_; 
v___x_1602_ = lean_st_ref_take(v___y_1600_);
v_nextMacroScope_1603_ = lean_ctor_get(v___x_1602_, 1);
v_ngen_1604_ = lean_ctor_get(v___x_1602_, 2);
v_auxDeclNGen_1605_ = lean_ctor_get(v___x_1602_, 3);
v_traceState_1606_ = lean_ctor_get(v___x_1602_, 4);
v_messages_1607_ = lean_ctor_get(v___x_1602_, 6);
v_infoState_1608_ = lean_ctor_get(v___x_1602_, 7);
v_snapshotTasks_1609_ = lean_ctor_get(v___x_1602_, 8);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1620_ == 0)
{
lean_object* v_unused_1621_; lean_object* v_unused_1622_; 
v_unused_1621_ = lean_ctor_get(v___x_1602_, 5);
lean_dec(v_unused_1621_);
v_unused_1622_ = lean_ctor_get(v___x_1602_, 0);
lean_dec(v_unused_1622_);
v___x_1611_ = v___x_1602_;
v_isShared_1612_ = v_isSharedCheck_1620_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_snapshotTasks_1609_);
lean_inc(v_infoState_1608_);
lean_inc(v_messages_1607_);
lean_inc(v_traceState_1606_);
lean_inc(v_auxDeclNGen_1605_);
lean_inc(v_ngen_1604_);
lean_inc(v_nextMacroScope_1603_);
lean_dec(v___x_1602_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1620_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1613_; lean_object* v___x_1615_; 
v___x_1613_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2);
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 5, v___x_1613_);
lean_ctor_set(v___x_1611_, 0, v_env_1599_);
v___x_1615_ = v___x_1611_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_env_1599_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_nextMacroScope_1603_);
lean_ctor_set(v_reuseFailAlloc_1619_, 2, v_ngen_1604_);
lean_ctor_set(v_reuseFailAlloc_1619_, 3, v_auxDeclNGen_1605_);
lean_ctor_set(v_reuseFailAlloc_1619_, 4, v_traceState_1606_);
lean_ctor_set(v_reuseFailAlloc_1619_, 5, v___x_1613_);
lean_ctor_set(v_reuseFailAlloc_1619_, 6, v_messages_1607_);
lean_ctor_set(v_reuseFailAlloc_1619_, 7, v_infoState_1608_);
lean_ctor_set(v_reuseFailAlloc_1619_, 8, v_snapshotTasks_1609_);
v___x_1615_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1616_ = lean_st_ref_set(v___y_1600_, v___x_1615_);
v___x_1617_ = lean_box(0);
v___x_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
return v___x_1618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___boxed(lean_object* v_env_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_env_1623_, v___y_1624_);
lean_dec(v___y_1624_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1(lean_object* v_env_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_env_1627_, v___y_1629_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___boxed(lean_object* v_env_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1(v_env_1632_, v___y_1633_, v___y_1634_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2___redArg(lean_object* v_msg_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v_ref_1641_; lean_object* v___x_1642_; lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1651_; 
v_ref_1641_ = lean_ctor_get(v___y_1638_, 5);
v___x_1642_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_1637_, v___y_1638_, v___y_1639_);
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1651_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1651_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1647_; lean_object* v___x_1649_; 
lean_inc(v_ref_1641_);
v___x_1647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1647_, 0, v_ref_1641_);
lean_ctor_set(v___x_1647_, 1, v_a_1643_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set_tag(v___x_1645_, 1);
lean_ctor_set(v___x_1645_, 0, v___x_1647_);
v___x_1649_ = v___x_1645_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msg_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_1652_, v___y_1653_, v___y_1654_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
return v_res_1656_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1657_ = lean_box(0);
v___x_1658_ = l_Lean_interruptExceptionId;
v___x_1659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
lean_ctor_set(v___x_1659_, 1, v___x_1657_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg(){
_start:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v___y_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(lean_object* v_ex_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v___y_1670_; lean_object* v___y_1671_; 
if (lean_obj_tag(v_ex_1665_) == 16)
{
lean_object* v___x_1675_; lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
v___x_1675_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg();
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1675_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1675_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
else
{
v___y_1670_ = v___y_1666_;
v___y_1671_ = v___y_1667_;
goto v___jp_1669_;
}
v___jp_1669_:
{
lean_object* v_options_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v_options_1672_ = lean_ctor_get(v___y_1670_, 2);
lean_inc_ref(v_options_1672_);
v___x_1673_ = l_Lean_Kernel_Exception_toMessageData(v_ex_1665_, v_options_1672_);
v___x_1674_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2___redArg(v___x_1673_, v___y_1670_, v___y_1671_);
return v___x_1674_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg___boxed(lean_object* v_ex_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(v_ex_1684_, v___y_1685_, v___y_1686_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(lean_object* v_x_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
if (lean_obj_tag(v_x_1689_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1694_; 
v_a_1693_ = lean_ctor_get(v_x_1689_, 0);
lean_inc(v_a_1693_);
lean_dec_ref(v_x_1689_);
v___x_1694_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(v_a_1693_, v___y_1690_, v___y_1691_);
return v___x_1694_;
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
v_a_1695_ = lean_ctor_get(v_x_1689_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v_x_1689_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v_x_1689_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v_x_1689_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
lean_ctor_set_tag(v___x_1697_, 0);
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg___boxed(lean_object* v_x_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v_x_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
return v_res_1707_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1708_ = lean_unsigned_to_nat(1u);
v___x_1709_ = l_Lean_Level_ofNat(v___x_1708_);
return v___x_1709_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1710_ = lean_box(0);
v___x_1711_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__0);
v___x_1712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1711_);
lean_ctor_set(v___x_1712_, 1, v___x_1710_);
return v___x_1712_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1719_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__1);
v___x_1720_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__4));
v___x_1721_ = l_Lean_mkConst(v___x_1720_, v___x_1719_);
return v___x_1721_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = lean_unsigned_to_nat(0u);
v___x_1723_ = l_Lean_Level_ofNat(v___x_1722_);
return v___x_1723_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__6);
v___x_1725_ = l_Lean_mkSort(v___x_1724_);
return v___x_1725_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__11(void){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1731_ = lean_box(0);
v___x_1732_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__10));
v___x_1733_ = l_Lean_mkConst(v___x_1732_, v___x_1731_);
return v___x_1733_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__12(void){
_start:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1734_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__11);
v___x_1735_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__7);
v___x_1736_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__5);
v___x_1737_ = l_Lean_mkAppB(v___x_1736_, v___x_1735_, v___x_1734_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg(lean_object* v_as_x27_1743_, lean_object* v_b_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
if (lean_obj_tag(v_as_x27_1743_) == 0)
{
lean_object* v___x_1748_; 
v___x_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1748_, 0, v_b_1744_);
return v___x_1748_;
}
else
{
lean_object* v_head_1749_; lean_object* v_tail_1750_; lean_object* v___x_1751_; lean_object* v_env_1752_; lean_object* v_options_1753_; lean_object* v_cancelTk_x3f_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___y_1758_; uint8_t v___y_1759_; lean_object* v_a_1763_; lean_object* v___x_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
lean_dec_ref(v_b_1744_);
v_head_1749_ = lean_ctor_get(v_as_x27_1743_, 0);
v_tail_1750_ = lean_ctor_get(v_as_x27_1743_, 1);
v___x_1751_ = lean_st_ref_get(v___y_1746_);
v_env_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc_ref(v_env_1752_);
lean_dec(v___x_1751_);
v_options_1753_ = lean_ctor_get(v___y_1745_, 2);
v_cancelTk_x3f_1754_ = lean_ctor_get(v___y_1745_, 12);
v___x_1755_ = lean_box(0);
v___x_1756_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__2));
v___x_1766_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__12, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__12_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__12);
lean_inc(v_head_1749_);
v___x_1767_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1767_, 0, v_head_1749_);
lean_ctor_set(v___x_1767_, 1, v___x_1755_);
lean_ctor_set(v___x_1767_, 2, v___x_1766_);
v___x_1768_ = 0;
v___x_1769_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1769_, 0, v___x_1767_);
lean_ctor_set_uint8(v___x_1769_, sizeof(void*)*1, v___x_1768_);
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
v___x_1771_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_1752_, v_options_1753_, v___x_1770_, v_cancelTk_x3f_1754_);
lean_dec_ref(v___x_1770_);
v___x_1772_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_1771_, v___y_1745_, v___y_1746_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v___x_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1782_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref(v___x_1772_);
v___x_1774_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_1773_, v___y_1746_);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1782_ == 0)
{
lean_object* v_unused_1783_; 
v_unused_1783_ = lean_ctor_get(v___x_1774_, 0);
lean_dec(v_unused_1783_);
v___x_1776_ = v___x_1774_;
v_isShared_1777_ = v_isSharedCheck_1782_;
goto v_resetjp_1775_;
}
else
{
lean_dec(v___x_1774_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1782_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1778_; lean_object* v___x_1780_; 
v___x_1778_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__14));
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v___x_1778_);
v___x_1780_ = v___x_1776_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1778_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
else
{
lean_object* v_a_1784_; 
v_a_1784_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1784_);
lean_dec_ref(v___x_1772_);
v_a_1763_ = v_a_1784_;
goto v___jp_1762_;
}
v___jp_1757_:
{
if (v___y_1759_ == 0)
{
lean_dec_ref(v___y_1758_);
v_as_x27_1743_ = v_tail_1750_;
v_b_1744_ = v___x_1756_;
goto _start;
}
else
{
lean_object* v___x_1761_; 
v___x_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1761_, 0, v___y_1758_);
return v___x_1761_;
}
}
v___jp_1762_:
{
uint8_t v___x_1764_; 
v___x_1764_ = l_Lean_Exception_isInterrupt(v_a_1763_);
if (v___x_1764_ == 0)
{
uint8_t v___x_1765_; 
lean_inc_ref(v_a_1763_);
v___x_1765_ = l_Lean_Exception_isRuntime(v_a_1763_);
v___y_1758_ = v_a_1763_;
v___y_1759_ = v___x_1765_;
goto v___jp_1757_;
}
else
{
v___y_1758_ = v_a_1763_;
v___y_1759_ = v___x_1764_;
goto v___jp_1757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___boxed(lean_object* v_as_x27_1785_, lean_object* v_b_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg(v_as_x27_1785_, v_b_1786_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v_as_x27_1785_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom(lean_object* v_decl_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_){
_start:
{
lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1824_; uint8_t v___y_1825_; lean_object* v_a_1828_; lean_object* v___y_1832_; uint8_t v___y_1833_; lean_object* v_a_1836_; 
switch(lean_obj_tag(v_decl_1791_))
{
case 1:
{
lean_object* v_val_1839_; lean_object* v___x_1840_; lean_object* v_toConstantVal_1841_; lean_object* v_env_1842_; lean_object* v_options_1843_; lean_object* v_cancelTk_x3f_1844_; uint8_t v___x_1845_; lean_object* v___x_1846_; lean_object* v_fallbackDecl_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v_val_1839_ = lean_ctor_get(v_decl_1791_, 0);
v___x_1840_ = lean_st_ref_get(v_a_1793_);
v_toConstantVal_1841_ = lean_ctor_get(v_val_1839_, 0);
v_env_1842_ = lean_ctor_get(v___x_1840_, 0);
lean_inc_ref(v_env_1842_);
lean_dec(v___x_1840_);
v_options_1843_ = lean_ctor_get(v_a_1792_, 2);
v_cancelTk_x3f_1844_ = lean_ctor_get(v_a_1792_, 12);
v___x_1845_ = 0;
lean_inc_ref(v_toConstantVal_1841_);
v___x_1846_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1846_, 0, v_toConstantVal_1841_);
lean_ctor_set_uint8(v___x_1846_, sizeof(void*)*1, v___x_1845_);
v_fallbackDecl_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_1847_, 0, v___x_1846_);
v___x_1848_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_1842_, v_options_1843_, v_fallbackDecl_1847_, v_cancelTk_x3f_1844_);
lean_dec_ref(v_fallbackDecl_1847_);
v___x_1849_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_1848_, v_a_1792_, v_a_1793_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v___x_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1859_; 
lean_dec_ref(v_decl_1791_);
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_a_1850_);
lean_dec_ref(v___x_1849_);
v___x_1851_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_1850_, v_a_1793_);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1859_ == 0)
{
lean_object* v_unused_1860_; 
v_unused_1860_ = lean_ctor_get(v___x_1851_, 0);
lean_dec(v_unused_1860_);
v___x_1853_ = v___x_1851_;
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
else
{
lean_dec(v___x_1851_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1855_; lean_object* v___x_1857_; 
v___x_1855_ = lean_box(0);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v___x_1855_);
v___x_1857_ = v___x_1853_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
else
{
lean_object* v_a_1861_; 
v_a_1861_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_a_1861_);
lean_dec_ref(v___x_1849_);
v_a_1828_ = v_a_1861_;
goto v___jp_1827_;
}
}
case 2:
{
lean_object* v_val_1862_; lean_object* v___x_1863_; lean_object* v_toConstantVal_1864_; lean_object* v_env_1865_; lean_object* v_options_1866_; lean_object* v_cancelTk_x3f_1867_; uint8_t v___x_1868_; lean_object* v___x_1869_; lean_object* v_fallbackDecl_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v_val_1862_ = lean_ctor_get(v_decl_1791_, 0);
v___x_1863_ = lean_st_ref_get(v_a_1793_);
v_toConstantVal_1864_ = lean_ctor_get(v_val_1862_, 0);
v_env_1865_ = lean_ctor_get(v___x_1863_, 0);
lean_inc_ref(v_env_1865_);
lean_dec(v___x_1863_);
v_options_1866_ = lean_ctor_get(v_a_1792_, 2);
v_cancelTk_x3f_1867_ = lean_ctor_get(v_a_1792_, 12);
v___x_1868_ = 0;
lean_inc_ref(v_toConstantVal_1864_);
v___x_1869_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1869_, 0, v_toConstantVal_1864_);
lean_ctor_set_uint8(v___x_1869_, sizeof(void*)*1, v___x_1868_);
v_fallbackDecl_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_1870_, 0, v___x_1869_);
v___x_1871_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_1865_, v_options_1866_, v_fallbackDecl_1870_, v_cancelTk_x3f_1867_);
lean_dec_ref(v_fallbackDecl_1870_);
v___x_1872_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_1871_, v_a_1792_, v_a_1793_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1882_; 
lean_dec_ref(v_decl_1791_);
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref(v___x_1872_);
v___x_1874_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_1873_, v_a_1793_);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1882_ == 0)
{
lean_object* v_unused_1883_; 
v_unused_1883_ = lean_ctor_get(v___x_1874_, 0);
lean_dec(v_unused_1883_);
v___x_1876_ = v___x_1874_;
v_isShared_1877_ = v_isSharedCheck_1882_;
goto v_resetjp_1875_;
}
else
{
lean_dec(v___x_1874_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1882_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1878_ = lean_box(0);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v___x_1878_);
v___x_1880_ = v___x_1876_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
else
{
lean_object* v_a_1884_; 
v_a_1884_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1884_);
lean_dec_ref(v___x_1872_);
v_a_1836_ = v_a_1884_;
goto v___jp_1835_;
}
}
default: 
{
v___y_1796_ = v_a_1792_;
v___y_1797_ = v_a_1793_;
goto v___jp_1795_;
}
}
v___jp_1795_:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1798_ = l_Lean_Declaration_getNames(v_decl_1791_);
v___x_1799_ = lean_box(0);
v___x_1800_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__2));
v___x_1801_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg(v___x_1798_, v___x_1800_, v___y_1796_, v___y_1797_);
lean_dec(v___x_1798_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1814_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1804_ = v___x_1801_;
v_isShared_1805_ = v_isSharedCheck_1814_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1801_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1814_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v_fst_1806_; 
v_fst_1806_ = lean_ctor_get(v_a_1802_, 0);
lean_inc(v_fst_1806_);
lean_dec(v_a_1802_);
if (lean_obj_tag(v_fst_1806_) == 0)
{
lean_object* v___x_1808_; 
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1799_);
v___x_1808_ = v___x_1804_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1799_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
else
{
lean_object* v_val_1810_; lean_object* v___x_1812_; 
v_val_1810_ = lean_ctor_get(v_fst_1806_, 0);
lean_inc(v_val_1810_);
lean_dec_ref(v_fst_1806_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v_val_1810_);
v___x_1812_ = v___x_1804_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_val_1810_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
else
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1822_; 
v_a_1815_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1817_ = v___x_1801_;
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1801_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
}
v___jp_1823_:
{
if (v___y_1825_ == 0)
{
lean_dec_ref(v___y_1824_);
v___y_1796_ = v_a_1792_;
v___y_1797_ = v_a_1793_;
goto v___jp_1795_;
}
else
{
lean_object* v___x_1826_; 
lean_dec(v_decl_1791_);
v___x_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1826_, 0, v___y_1824_);
return v___x_1826_;
}
}
v___jp_1827_:
{
uint8_t v___x_1829_; 
v___x_1829_ = l_Lean_Exception_isInterrupt(v_a_1828_);
if (v___x_1829_ == 0)
{
uint8_t v___x_1830_; 
lean_inc_ref(v_a_1828_);
v___x_1830_ = l_Lean_Exception_isRuntime(v_a_1828_);
v___y_1824_ = v_a_1828_;
v___y_1825_ = v___x_1830_;
goto v___jp_1823_;
}
else
{
v___y_1824_ = v_a_1828_;
v___y_1825_ = v___x_1829_;
goto v___jp_1823_;
}
}
v___jp_1831_:
{
if (v___y_1833_ == 0)
{
lean_dec_ref(v___y_1832_);
v___y_1796_ = v_a_1792_;
v___y_1797_ = v_a_1793_;
goto v___jp_1795_;
}
else
{
lean_object* v___x_1834_; 
lean_dec(v_decl_1791_);
v___x_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1834_, 0, v___y_1832_);
return v___x_1834_;
}
}
v___jp_1835_:
{
uint8_t v___x_1837_; 
v___x_1837_ = l_Lean_Exception_isInterrupt(v_a_1836_);
if (v___x_1837_ == 0)
{
uint8_t v___x_1838_; 
lean_inc_ref(v_a_1836_);
v___x_1838_ = l_Lean_Exception_isRuntime(v_a_1836_);
v___y_1832_ = v_a_1836_;
v___y_1833_ = v___x_1838_;
goto v___jp_1831_;
}
else
{
v___y_1832_ = v_a_1836_;
v___y_1833_ = v___x_1837_;
goto v___jp_1831_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom___boxed(lean_object* v_decl_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom(v_decl_1885_, v_a_1886_, v_a_1887_);
lean_dec(v_a_1887_);
lean_dec_ref(v_a_1886_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0(lean_object* v_00_u03b1_1890_, lean_object* v_x_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v_x_1891_, v___y_1892_, v___y_1893_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___boxed(lean_object* v_00_u03b1_1896_, lean_object* v_x_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0(v_00_u03b1_1896_, v_x_1897_, v___y_1898_, v___y_1899_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2(lean_object* v_as_1902_, lean_object* v_as_x27_1903_, lean_object* v_b_1904_, lean_object* v_a_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg(v_as_x27_1903_, v_b_1904_, v___y_1906_, v___y_1907_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___boxed(lean_object* v_as_1910_, lean_object* v_as_x27_1911_, lean_object* v_b_1912_, lean_object* v_a_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2(v_as_1910_, v_as_x27_1911_, v_b_1912_, v_a_1913_, v___y_1914_, v___y_1915_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v_as_x27_1911_);
lean_dec(v_as_1910_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3(v_00_u03b1_1923_, v___y_1924_, v___y_1925_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0(lean_object* v_00_u03b1_1928_, lean_object* v_ex_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v___x_1933_; 
v___x_1933_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(v_ex_1929_, v___y_1930_, v___y_1931_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1934_, lean_object* v_ex_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0(v_00_u03b1_1934_, v_ex_1935_, v___y_1936_, v___y_1937_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1940_, lean_object* v_msg_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_1941_, v___y_1942_, v___y_1943_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1946_, lean_object* v_msg_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2(v_00_u03b1_1946_, v_msg_1947_, v___y_1948_, v___y_1949_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
return v_res_1951_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1952_ = lean_unsigned_to_nat(32u);
v___x_1953_ = lean_mk_empty_array_with_capacity(v___x_1952_);
v___x_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
return v___x_1954_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1955_ = ((size_t)5ULL);
v___x_1956_ = lean_unsigned_to_nat(0u);
v___x_1957_ = lean_unsigned_to_nat(32u);
v___x_1958_ = lean_mk_empty_array_with_capacity(v___x_1957_);
v___x_1959_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__0);
v___x_1960_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1960_, 0, v___x_1959_);
lean_ctor_set(v___x_1960_, 1, v___x_1958_);
lean_ctor_set(v___x_1960_, 2, v___x_1956_);
lean_ctor_set(v___x_1960_, 3, v___x_1956_);
lean_ctor_set_usize(v___x_1960_, 4, v___x_1955_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(lean_object* v___y_1961_){
_start:
{
lean_object* v___x_1963_; lean_object* v_traceState_1964_; lean_object* v_traces_1965_; lean_object* v___x_1966_; lean_object* v_traceState_1967_; lean_object* v_env_1968_; lean_object* v_nextMacroScope_1969_; lean_object* v_ngen_1970_; lean_object* v_auxDeclNGen_1971_; lean_object* v_cache_1972_; lean_object* v_messages_1973_; lean_object* v_infoState_1974_; lean_object* v_snapshotTasks_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1994_; 
v___x_1963_ = lean_st_ref_get(v___y_1961_);
v_traceState_1964_ = lean_ctor_get(v___x_1963_, 4);
lean_inc_ref(v_traceState_1964_);
lean_dec(v___x_1963_);
v_traces_1965_ = lean_ctor_get(v_traceState_1964_, 0);
lean_inc_ref(v_traces_1965_);
lean_dec_ref(v_traceState_1964_);
v___x_1966_ = lean_st_ref_take(v___y_1961_);
v_traceState_1967_ = lean_ctor_get(v___x_1966_, 4);
v_env_1968_ = lean_ctor_get(v___x_1966_, 0);
v_nextMacroScope_1969_ = lean_ctor_get(v___x_1966_, 1);
v_ngen_1970_ = lean_ctor_get(v___x_1966_, 2);
v_auxDeclNGen_1971_ = lean_ctor_get(v___x_1966_, 3);
v_cache_1972_ = lean_ctor_get(v___x_1966_, 5);
v_messages_1973_ = lean_ctor_get(v___x_1966_, 6);
v_infoState_1974_ = lean_ctor_get(v___x_1966_, 7);
v_snapshotTasks_1975_ = lean_ctor_get(v___x_1966_, 8);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1977_ = v___x_1966_;
v_isShared_1978_ = v_isSharedCheck_1994_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_snapshotTasks_1975_);
lean_inc(v_infoState_1974_);
lean_inc(v_messages_1973_);
lean_inc(v_cache_1972_);
lean_inc(v_traceState_1967_);
lean_inc(v_auxDeclNGen_1971_);
lean_inc(v_ngen_1970_);
lean_inc(v_nextMacroScope_1969_);
lean_inc(v_env_1968_);
lean_dec(v___x_1966_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1994_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
uint64_t v_tid_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1992_; 
v_tid_1979_ = lean_ctor_get_uint64(v_traceState_1967_, sizeof(void*)*1);
v_isSharedCheck_1992_ = !lean_is_exclusive(v_traceState_1967_);
if (v_isSharedCheck_1992_ == 0)
{
lean_object* v_unused_1993_; 
v_unused_1993_ = lean_ctor_get(v_traceState_1967_, 0);
lean_dec(v_unused_1993_);
v___x_1981_ = v_traceState_1967_;
v_isShared_1982_ = v_isSharedCheck_1992_;
goto v_resetjp_1980_;
}
else
{
lean_dec(v_traceState_1967_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1992_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1983_; lean_object* v___x_1985_; 
v___x_1983_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__1);
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 0, v___x_1983_);
v___x_1985_ = v___x_1981_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1983_);
lean_ctor_set_uint64(v_reuseFailAlloc_1991_, sizeof(void*)*1, v_tid_1979_);
v___x_1985_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
lean_object* v___x_1987_; 
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 4, v___x_1985_);
v___x_1987_ = v___x_1977_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_env_1968_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v_nextMacroScope_1969_);
lean_ctor_set(v_reuseFailAlloc_1990_, 2, v_ngen_1970_);
lean_ctor_set(v_reuseFailAlloc_1990_, 3, v_auxDeclNGen_1971_);
lean_ctor_set(v_reuseFailAlloc_1990_, 4, v___x_1985_);
lean_ctor_set(v_reuseFailAlloc_1990_, 5, v_cache_1972_);
lean_ctor_set(v_reuseFailAlloc_1990_, 6, v_messages_1973_);
lean_ctor_set(v_reuseFailAlloc_1990_, 7, v_infoState_1974_);
lean_ctor_set(v_reuseFailAlloc_1990_, 8, v_snapshotTasks_1975_);
v___x_1987_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1988_ = lean_st_ref_set(v___y_1961_, v___x_1987_);
v___x_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1989_, 0, v_traces_1965_);
return v___x_1989_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___boxed(lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v___y_1995_);
lean_dec(v___y_1995_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1(lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v___x_2001_; 
v___x_2001_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v___y_1999_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___boxed(lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1(v___y_2002_, v___y_2003_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___redArg(lean_object* v_category_2006_, lean_object* v_opts_2007_, lean_object* v_act_2008_, lean_object* v_decl_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
lean_inc(v___y_2011_);
lean_inc_ref(v___y_2010_);
v___x_2013_ = lean_apply_2(v_act_2008_, v___y_2010_, v___y_2011_);
v___x_2014_ = l_Lean_profileitIOUnsafe___redArg(v_category_2006_, v_opts_2007_, v___x_2013_, v_decl_2009_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___redArg___boxed(lean_object* v_category_2015_, lean_object* v_opts_2016_, lean_object* v_act_2017_, lean_object* v_decl_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___redArg(v_category_2015_, v_opts_2016_, v_act_2017_, v_decl_2018_, v___y_2019_, v___y_2020_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec_ref(v_opts_2016_);
lean_dec_ref(v_category_2015_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3(lean_object* v_00_u03b1_2023_, lean_object* v_category_2024_, lean_object* v_opts_2025_, lean_object* v_act_2026_, lean_object* v_decl_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v___x_2031_; 
v___x_2031_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___redArg(v_category_2024_, v_opts_2025_, v_act_2026_, v_decl_2027_, v___y_2028_, v___y_2029_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___boxed(lean_object* v_00_u03b1_2032_, lean_object* v_category_2033_, lean_object* v_opts_2034_, lean_object* v_act_2035_, lean_object* v_decl_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3(v_00_u03b1_2032_, v_category_2033_, v_opts_2034_, v_act_2035_, v_decl_2036_, v___y_2037_, v___y_2038_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec_ref(v_opts_2034_);
lean_dec_ref(v_category_2033_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__0(lean_object* v_a_2041_, lean_object* v_a_2042_){
_start:
{
if (lean_obj_tag(v_a_2041_) == 0)
{
lean_object* v___x_2043_; 
v___x_2043_ = l_List_reverse___redArg(v_a_2042_);
return v___x_2043_;
}
else
{
lean_object* v_head_2044_; lean_object* v_tail_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2054_; 
v_head_2044_ = lean_ctor_get(v_a_2041_, 0);
v_tail_2045_ = lean_ctor_get(v_a_2041_, 1);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_a_2041_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2047_ = v_a_2041_;
v_isShared_2048_ = v_isSharedCheck_2054_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_tail_2045_);
lean_inc(v_head_2044_);
lean_dec(v_a_2041_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2054_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2049_; lean_object* v___x_2051_; 
v___x_2049_ = l_Lean_MessageData_ofName(v_head_2044_);
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 1, v_a_2042_);
lean_ctor_set(v___x_2047_, 0, v___x_2049_);
v___x_2051_ = v___x_2047_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2049_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_a_2042_);
v___x_2051_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
v_a_2041_ = v_tail_2045_;
v_a_2042_ = v___x_2051_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__0));
v___x_2057_ = l_Lean_stringToMessageData(v___x_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0(lean_object* v_decl_2058_, lean_object* v_x_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2063_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__1, &l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__1);
v___x_2064_ = l_Lean_Declaration_getTopLevelNames(v_decl_2058_);
v___x_2065_ = lean_box(0);
v___x_2066_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__0(v___x_2064_, v___x_2065_);
v___x_2067_ = l_Lean_MessageData_ofList(v___x_2066_);
v___x_2068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2063_);
lean_ctor_set(v___x_2068_, 1, v___x_2067_);
v___x_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___boxed(lean_object* v_decl_2070_, lean_object* v_x_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0(v_decl_2070_, v_x_2071_, v___y_2072_, v___y_2073_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec_ref(v_x_2071_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__5(lean_object* v_opts_2076_, lean_object* v_opt_2077_){
_start:
{
lean_object* v_name_2078_; lean_object* v_defValue_2079_; lean_object* v_map_2080_; lean_object* v___x_2081_; 
v_name_2078_ = lean_ctor_get(v_opt_2077_, 0);
v_defValue_2079_ = lean_ctor_get(v_opt_2077_, 1);
v_map_2080_ = lean_ctor_get(v_opts_2076_, 0);
v___x_2081_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2080_, v_name_2078_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_inc(v_defValue_2079_);
return v_defValue_2079_;
}
else
{
lean_object* v_val_2082_; 
v_val_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_val_2082_);
lean_dec_ref(v___x_2081_);
if (lean_obj_tag(v_val_2082_) == 3)
{
lean_object* v_v_2083_; 
v_v_2083_ = lean_ctor_get(v_val_2082_, 0);
lean_inc(v_v_2083_);
lean_dec_ref(v_val_2082_);
return v_v_2083_;
}
else
{
lean_dec(v_val_2082_);
lean_inc(v_defValue_2079_);
return v_defValue_2079_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__5___boxed(lean_object* v_opts_2084_, lean_object* v_opt_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__5(v_opts_2084_, v_opt_2085_);
lean_dec_ref(v_opt_2085_);
lean_dec_ref(v_opts_2084_);
return v_res_2086_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__2(lean_object* v_e_2087_){
_start:
{
if (lean_obj_tag(v_e_2087_) == 0)
{
uint8_t v___x_2088_; 
v___x_2088_ = 2;
return v___x_2088_;
}
else
{
uint8_t v___x_2089_; 
v___x_2089_ = 0;
return v___x_2089_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__2___boxed(lean_object* v_e_2090_){
_start:
{
uint8_t v_res_2091_; lean_object* v_r_2092_; 
v_res_2091_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__2(v_e_2090_);
lean_dec_ref(v_e_2090_);
v_r_2092_ = lean_box(v_res_2091_);
return v_r_2092_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4___redArg(lean_object* v_x_2093_){
_start:
{
if (lean_obj_tag(v_x_2093_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
v_a_2095_ = lean_ctor_get(v_x_2093_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v_x_2093_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v_x_2093_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v_x_2093_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
lean_ctor_set_tag(v___x_2097_, 1);
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
v_a_2103_ = lean_ctor_get(v_x_2093_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_x_2093_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v_x_2093_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v_x_2093_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
lean_ctor_set_tag(v___x_2105_, 0);
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4___redArg___boxed(lean_object* v_x_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4___redArg(v_x_2111_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__3_spec__5(size_t v_sz_2114_, size_t v_i_2115_, lean_object* v_bs_2116_){
_start:
{
uint8_t v___x_2117_; 
v___x_2117_ = lean_usize_dec_lt(v_i_2115_, v_sz_2114_);
if (v___x_2117_ == 0)
{
return v_bs_2116_;
}
else
{
lean_object* v_v_2118_; lean_object* v_msg_2119_; lean_object* v___x_2120_; lean_object* v_bs_x27_2121_; size_t v___x_2122_; size_t v___x_2123_; lean_object* v___x_2124_; 
v_v_2118_ = lean_array_uget_borrowed(v_bs_2116_, v_i_2115_);
v_msg_2119_ = lean_ctor_get(v_v_2118_, 1);
lean_inc_ref(v_msg_2119_);
v___x_2120_ = lean_unsigned_to_nat(0u);
v_bs_x27_2121_ = lean_array_uset(v_bs_2116_, v_i_2115_, v___x_2120_);
v___x_2122_ = ((size_t)1ULL);
v___x_2123_ = lean_usize_add(v_i_2115_, v___x_2122_);
v___x_2124_ = lean_array_uset(v_bs_x27_2121_, v_i_2115_, v_msg_2119_);
v_i_2115_ = v___x_2123_;
v_bs_2116_ = v___x_2124_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__3_spec__5___boxed(lean_object* v_sz_2126_, lean_object* v_i_2127_, lean_object* v_bs_2128_){
_start:
{
size_t v_sz_boxed_2129_; size_t v_i_boxed_2130_; lean_object* v_res_2131_; 
v_sz_boxed_2129_ = lean_unbox_usize(v_sz_2126_);
lean_dec(v_sz_2126_);
v_i_boxed_2130_ = lean_unbox_usize(v_i_2127_);
lean_dec(v_i_2127_);
v_res_2131_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__3_spec__5(v_sz_boxed_2129_, v_i_boxed_2130_, v_bs_2128_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__3(lean_object* v_oldTraces_2132_, lean_object* v_data_2133_, lean_object* v_ref_2134_, lean_object* v_msg_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v_fileName_2139_; lean_object* v_fileMap_2140_; lean_object* v_options_2141_; lean_object* v_currRecDepth_2142_; lean_object* v_maxRecDepth_2143_; lean_object* v_ref_2144_; lean_object* v_currNamespace_2145_; lean_object* v_openDecls_2146_; lean_object* v_initHeartbeats_2147_; lean_object* v_maxHeartbeats_2148_; lean_object* v_quotContext_2149_; lean_object* v_currMacroScope_2150_; uint8_t v_diag_2151_; lean_object* v_cancelTk_x3f_2152_; uint8_t v_suppressElabErrors_2153_; lean_object* v_inheritedTraceOptions_2154_; lean_object* v___x_2155_; lean_object* v_traceState_2156_; lean_object* v_traces_2157_; lean_object* v_ref_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; size_t v_sz_2161_; size_t v___x_2162_; lean_object* v___x_2163_; lean_object* v_msg_2164_; lean_object* v___x_2165_; lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2203_; 
v_fileName_2139_ = lean_ctor_get(v___y_2136_, 0);
v_fileMap_2140_ = lean_ctor_get(v___y_2136_, 1);
v_options_2141_ = lean_ctor_get(v___y_2136_, 2);
v_currRecDepth_2142_ = lean_ctor_get(v___y_2136_, 3);
v_maxRecDepth_2143_ = lean_ctor_get(v___y_2136_, 4);
v_ref_2144_ = lean_ctor_get(v___y_2136_, 5);
v_currNamespace_2145_ = lean_ctor_get(v___y_2136_, 6);
v_openDecls_2146_ = lean_ctor_get(v___y_2136_, 7);
v_initHeartbeats_2147_ = lean_ctor_get(v___y_2136_, 8);
v_maxHeartbeats_2148_ = lean_ctor_get(v___y_2136_, 9);
v_quotContext_2149_ = lean_ctor_get(v___y_2136_, 10);
v_currMacroScope_2150_ = lean_ctor_get(v___y_2136_, 11);
v_diag_2151_ = lean_ctor_get_uint8(v___y_2136_, sizeof(void*)*14);
v_cancelTk_x3f_2152_ = lean_ctor_get(v___y_2136_, 12);
v_suppressElabErrors_2153_ = lean_ctor_get_uint8(v___y_2136_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2154_ = lean_ctor_get(v___y_2136_, 13);
v___x_2155_ = lean_st_ref_get(v___y_2137_);
v_traceState_2156_ = lean_ctor_get(v___x_2155_, 4);
lean_inc_ref(v_traceState_2156_);
lean_dec(v___x_2155_);
v_traces_2157_ = lean_ctor_get(v_traceState_2156_, 0);
lean_inc_ref(v_traces_2157_);
lean_dec_ref(v_traceState_2156_);
v_ref_2158_ = l_Lean_replaceRef(v_ref_2134_, v_ref_2144_);
lean_inc_ref(v_inheritedTraceOptions_2154_);
lean_inc(v_cancelTk_x3f_2152_);
lean_inc(v_currMacroScope_2150_);
lean_inc(v_quotContext_2149_);
lean_inc(v_maxHeartbeats_2148_);
lean_inc(v_initHeartbeats_2147_);
lean_inc(v_openDecls_2146_);
lean_inc(v_currNamespace_2145_);
lean_inc(v_maxRecDepth_2143_);
lean_inc(v_currRecDepth_2142_);
lean_inc_ref(v_options_2141_);
lean_inc_ref(v_fileMap_2140_);
lean_inc_ref(v_fileName_2139_);
v___x_2159_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2159_, 0, v_fileName_2139_);
lean_ctor_set(v___x_2159_, 1, v_fileMap_2140_);
lean_ctor_set(v___x_2159_, 2, v_options_2141_);
lean_ctor_set(v___x_2159_, 3, v_currRecDepth_2142_);
lean_ctor_set(v___x_2159_, 4, v_maxRecDepth_2143_);
lean_ctor_set(v___x_2159_, 5, v_ref_2158_);
lean_ctor_set(v___x_2159_, 6, v_currNamespace_2145_);
lean_ctor_set(v___x_2159_, 7, v_openDecls_2146_);
lean_ctor_set(v___x_2159_, 8, v_initHeartbeats_2147_);
lean_ctor_set(v___x_2159_, 9, v_maxHeartbeats_2148_);
lean_ctor_set(v___x_2159_, 10, v_quotContext_2149_);
lean_ctor_set(v___x_2159_, 11, v_currMacroScope_2150_);
lean_ctor_set(v___x_2159_, 12, v_cancelTk_x3f_2152_);
lean_ctor_set(v___x_2159_, 13, v_inheritedTraceOptions_2154_);
lean_ctor_set_uint8(v___x_2159_, sizeof(void*)*14, v_diag_2151_);
lean_ctor_set_uint8(v___x_2159_, sizeof(void*)*14 + 1, v_suppressElabErrors_2153_);
v___x_2160_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2157_);
lean_dec_ref(v_traces_2157_);
v_sz_2161_ = lean_array_size(v___x_2160_);
v___x_2162_ = ((size_t)0ULL);
v___x_2163_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__3_spec__5(v_sz_2161_, v___x_2162_, v___x_2160_);
v_msg_2164_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2164_, 0, v_data_2133_);
lean_ctor_set(v_msg_2164_, 1, v_msg_2135_);
lean_ctor_set(v_msg_2164_, 2, v___x_2163_);
v___x_2165_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2164_, v___x_2159_, v___y_2137_);
lean_dec_ref(v___x_2159_);
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2168_ = v___x_2165_;
v_isShared_2169_ = v_isSharedCheck_2203_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2165_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2203_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2170_; lean_object* v_traceState_2171_; lean_object* v_env_2172_; lean_object* v_nextMacroScope_2173_; lean_object* v_ngen_2174_; lean_object* v_auxDeclNGen_2175_; lean_object* v_cache_2176_; lean_object* v_messages_2177_; lean_object* v_infoState_2178_; lean_object* v_snapshotTasks_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2202_; 
v___x_2170_ = lean_st_ref_take(v___y_2137_);
v_traceState_2171_ = lean_ctor_get(v___x_2170_, 4);
v_env_2172_ = lean_ctor_get(v___x_2170_, 0);
v_nextMacroScope_2173_ = lean_ctor_get(v___x_2170_, 1);
v_ngen_2174_ = lean_ctor_get(v___x_2170_, 2);
v_auxDeclNGen_2175_ = lean_ctor_get(v___x_2170_, 3);
v_cache_2176_ = lean_ctor_get(v___x_2170_, 5);
v_messages_2177_ = lean_ctor_get(v___x_2170_, 6);
v_infoState_2178_ = lean_ctor_get(v___x_2170_, 7);
v_snapshotTasks_2179_ = lean_ctor_get(v___x_2170_, 8);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2181_ = v___x_2170_;
v_isShared_2182_ = v_isSharedCheck_2202_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_snapshotTasks_2179_);
lean_inc(v_infoState_2178_);
lean_inc(v_messages_2177_);
lean_inc(v_cache_2176_);
lean_inc(v_traceState_2171_);
lean_inc(v_auxDeclNGen_2175_);
lean_inc(v_ngen_2174_);
lean_inc(v_nextMacroScope_2173_);
lean_inc(v_env_2172_);
lean_dec(v___x_2170_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2202_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
uint64_t v_tid_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2200_; 
v_tid_2183_ = lean_ctor_get_uint64(v_traceState_2171_, sizeof(void*)*1);
v_isSharedCheck_2200_ = !lean_is_exclusive(v_traceState_2171_);
if (v_isSharedCheck_2200_ == 0)
{
lean_object* v_unused_2201_; 
v_unused_2201_ = lean_ctor_get(v_traceState_2171_, 0);
lean_dec(v_unused_2201_);
v___x_2185_ = v_traceState_2171_;
v_isShared_2186_ = v_isSharedCheck_2200_;
goto v_resetjp_2184_;
}
else
{
lean_dec(v_traceState_2171_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2200_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2190_; 
v___x_2187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2187_, 0, v_ref_2134_);
lean_ctor_set(v___x_2187_, 1, v_a_2166_);
v___x_2188_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2132_, v___x_2187_);
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 0, v___x_2188_);
v___x_2190_ = v___x_2185_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2188_);
lean_ctor_set_uint64(v_reuseFailAlloc_2199_, sizeof(void*)*1, v_tid_2183_);
v___x_2190_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
lean_object* v___x_2192_; 
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 4, v___x_2190_);
v___x_2192_ = v___x_2181_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_env_2172_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_nextMacroScope_2173_);
lean_ctor_set(v_reuseFailAlloc_2198_, 2, v_ngen_2174_);
lean_ctor_set(v_reuseFailAlloc_2198_, 3, v_auxDeclNGen_2175_);
lean_ctor_set(v_reuseFailAlloc_2198_, 4, v___x_2190_);
lean_ctor_set(v_reuseFailAlloc_2198_, 5, v_cache_2176_);
lean_ctor_set(v_reuseFailAlloc_2198_, 6, v_messages_2177_);
lean_ctor_set(v_reuseFailAlloc_2198_, 7, v_infoState_2178_);
lean_ctor_set(v_reuseFailAlloc_2198_, 8, v_snapshotTasks_2179_);
v___x_2192_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2193_ = lean_st_ref_set(v___y_2137_, v___x_2192_);
v___x_2194_ = lean_box(0);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 0, v___x_2194_);
v___x_2196_ = v___x_2168_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__3___boxed(lean_object* v_oldTraces_2204_, lean_object* v_data_2205_, lean_object* v_ref_2206_, lean_object* v_msg_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__3(v_oldTraces_2204_, v_data_2205_, v_ref_2206_, v_msg_2207_, v___y_2208_, v___y_2209_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
return v_res_2211_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__0));
v___x_2214_ = l_Lean_stringToMessageData(v___x_2213_);
return v___x_2214_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__2(void){
_start:
{
lean_object* v___x_2215_; double v___x_2216_; 
v___x_2215_ = lean_unsigned_to_nat(0u);
v___x_2216_ = lean_float_of_nat(v___x_2215_);
return v___x_2216_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__4(void){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2218_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__3));
v___x_2219_ = l_Lean_stringToMessageData(v___x_2218_);
return v___x_2219_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__5(void){
_start:
{
lean_object* v___x_2220_; double v___x_2221_; 
v___x_2220_ = lean_unsigned_to_nat(1000u);
v___x_2221_ = lean_float_of_nat(v___x_2220_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2(lean_object* v_cls_2222_, uint8_t v_collapsed_2223_, lean_object* v_tag_2224_, lean_object* v_opts_2225_, uint8_t v_clsEnabled_2226_, lean_object* v_oldTraces_2227_, lean_object* v_msg_2228_, lean_object* v_resStartStop_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_fst_2233_; lean_object* v_snd_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2324_; 
v_fst_2233_ = lean_ctor_get(v_resStartStop_2229_, 0);
v_snd_2234_ = lean_ctor_get(v_resStartStop_2229_, 1);
v_isSharedCheck_2324_ = !lean_is_exclusive(v_resStartStop_2229_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2236_ = v_resStartStop_2229_;
v_isShared_2237_ = v_isSharedCheck_2324_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_snd_2234_);
lean_inc(v_fst_2233_);
lean_dec(v_resStartStop_2229_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2324_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v_data_2241_; lean_object* v_fst_2244_; lean_object* v_snd_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2323_; 
v_fst_2244_ = lean_ctor_get(v_snd_2234_, 0);
v_snd_2245_ = lean_ctor_get(v_snd_2234_, 1);
v_isSharedCheck_2323_ = !lean_is_exclusive(v_snd_2234_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2247_ = v_snd_2234_;
v_isShared_2248_ = v_isSharedCheck_2323_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_snd_2245_);
lean_inc(v_fst_2244_);
lean_dec(v_snd_2234_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2323_;
goto v_resetjp_2246_;
}
v___jp_2238_:
{
lean_object* v___x_2242_; 
lean_inc(v___y_2240_);
v___x_2242_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__3(v_oldTraces_2227_, v_data_2241_, v___y_2240_, v___y_2239_, v___y_2230_, v___y_2231_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v___x_2243_; 
lean_dec_ref(v___x_2242_);
v___x_2243_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4___redArg(v_fst_2233_);
return v___x_2243_;
}
else
{
lean_dec(v_fst_2233_);
return v___x_2242_;
}
}
v_resetjp_2246_:
{
lean_object* v___x_2249_; uint8_t v___x_2250_; lean_object* v___y_2252_; lean_object* v_a_2253_; uint8_t v___y_2277_; double v___y_2308_; 
v___x_2249_ = l_Lean_trace_profiler;
v___x_2250_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2225_, v___x_2249_);
if (v___x_2250_ == 0)
{
v___y_2277_ = v___x_2250_;
goto v___jp_2276_;
}
else
{
lean_object* v___x_2313_; uint8_t v___x_2314_; 
v___x_2313_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2314_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2225_, v___x_2313_);
if (v___x_2314_ == 0)
{
lean_object* v___x_2315_; lean_object* v___x_2316_; double v___x_2317_; double v___x_2318_; double v___x_2319_; 
v___x_2315_ = l_Lean_trace_profiler_threshold;
v___x_2316_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__5(v_opts_2225_, v___x_2315_);
v___x_2317_ = lean_float_of_nat(v___x_2316_);
v___x_2318_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__5);
v___x_2319_ = lean_float_div(v___x_2317_, v___x_2318_);
v___y_2308_ = v___x_2319_;
goto v___jp_2307_;
}
else
{
lean_object* v___x_2320_; lean_object* v___x_2321_; double v___x_2322_; 
v___x_2320_ = l_Lean_trace_profiler_threshold;
v___x_2321_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__5(v_opts_2225_, v___x_2320_);
v___x_2322_ = lean_float_of_nat(v___x_2321_);
v___y_2308_ = v___x_2322_;
goto v___jp_2307_;
}
}
v___jp_2251_:
{
uint8_t v_result_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2259_; 
v_result_2254_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__2(v_fst_2233_);
v___x_2255_ = l_Lean_TraceResult_toEmoji(v_result_2254_);
v___x_2256_ = l_Lean_stringToMessageData(v___x_2255_);
v___x_2257_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__1);
if (v_isShared_2248_ == 0)
{
lean_ctor_set_tag(v___x_2247_, 7);
lean_ctor_set(v___x_2247_, 1, v___x_2257_);
lean_ctor_set(v___x_2247_, 0, v___x_2256_);
v___x_2259_ = v___x_2247_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2256_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v___x_2257_);
v___x_2259_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
lean_object* v_m_2261_; 
if (v_isShared_2237_ == 0)
{
lean_ctor_set_tag(v___x_2236_, 7);
lean_ctor_set(v___x_2236_, 1, v_a_2253_);
lean_ctor_set(v___x_2236_, 0, v___x_2259_);
v_m_2261_ = v___x_2236_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2259_);
lean_ctor_set(v_reuseFailAlloc_2269_, 1, v_a_2253_);
v_m_2261_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; double v___x_2264_; lean_object* v_data_2265_; 
v___x_2262_ = lean_box(v_result_2254_);
v___x_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
v___x_2264_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__2);
lean_inc_ref(v_tag_2224_);
lean_inc_ref(v___x_2263_);
lean_inc(v_cls_2222_);
v_data_2265_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2265_, 0, v_cls_2222_);
lean_ctor_set(v_data_2265_, 1, v___x_2263_);
lean_ctor_set(v_data_2265_, 2, v_tag_2224_);
lean_ctor_set_float(v_data_2265_, sizeof(void*)*3, v___x_2264_);
lean_ctor_set_float(v_data_2265_, sizeof(void*)*3 + 8, v___x_2264_);
lean_ctor_set_uint8(v_data_2265_, sizeof(void*)*3 + 16, v_collapsed_2223_);
if (v___x_2250_ == 0)
{
lean_dec_ref(v___x_2263_);
lean_dec(v_snd_2245_);
lean_dec(v_fst_2244_);
lean_dec_ref(v_tag_2224_);
lean_dec(v_cls_2222_);
v___y_2239_ = v_m_2261_;
v___y_2240_ = v___y_2252_;
v_data_2241_ = v_data_2265_;
goto v___jp_2238_;
}
else
{
lean_object* v_data_2266_; double v___x_2267_; double v___x_2268_; 
lean_dec_ref(v_data_2265_);
v_data_2266_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2266_, 0, v_cls_2222_);
lean_ctor_set(v_data_2266_, 1, v___x_2263_);
lean_ctor_set(v_data_2266_, 2, v_tag_2224_);
v___x_2267_ = lean_unbox_float(v_fst_2244_);
lean_dec(v_fst_2244_);
lean_ctor_set_float(v_data_2266_, sizeof(void*)*3, v___x_2267_);
v___x_2268_ = lean_unbox_float(v_snd_2245_);
lean_dec(v_snd_2245_);
lean_ctor_set_float(v_data_2266_, sizeof(void*)*3 + 8, v___x_2268_);
lean_ctor_set_uint8(v_data_2266_, sizeof(void*)*3 + 16, v_collapsed_2223_);
v___y_2239_ = v_m_2261_;
v___y_2240_ = v___y_2252_;
v_data_2241_ = v_data_2266_;
goto v___jp_2238_;
}
}
}
}
v___jp_2271_:
{
lean_object* v_ref_2272_; lean_object* v___x_2273_; 
v_ref_2272_ = lean_ctor_get(v___y_2230_, 5);
lean_inc(v___y_2231_);
lean_inc_ref(v___y_2230_);
lean_inc(v_fst_2233_);
v___x_2273_ = lean_apply_4(v_msg_2228_, v_fst_2233_, v___y_2230_, v___y_2231_, lean_box(0));
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_a_2274_);
lean_dec_ref(v___x_2273_);
v___y_2252_ = v_ref_2272_;
v_a_2253_ = v_a_2274_;
goto v___jp_2251_;
}
else
{
lean_object* v___x_2275_; 
lean_dec_ref(v___x_2273_);
v___x_2275_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__4);
v___y_2252_ = v_ref_2272_;
v_a_2253_ = v___x_2275_;
goto v___jp_2251_;
}
}
v___jp_2276_:
{
if (v_clsEnabled_2226_ == 0)
{
if (v___y_2277_ == 0)
{
lean_object* v___x_2278_; lean_object* v_traceState_2279_; lean_object* v_env_2280_; lean_object* v_nextMacroScope_2281_; lean_object* v_ngen_2282_; lean_object* v_auxDeclNGen_2283_; lean_object* v_cache_2284_; lean_object* v_messages_2285_; lean_object* v_infoState_2286_; lean_object* v_snapshotTasks_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2306_; 
lean_del_object(v___x_2247_);
lean_dec(v_snd_2245_);
lean_dec(v_fst_2244_);
lean_del_object(v___x_2236_);
lean_dec_ref(v_msg_2228_);
lean_dec_ref(v_tag_2224_);
lean_dec(v_cls_2222_);
v___x_2278_ = lean_st_ref_take(v___y_2231_);
v_traceState_2279_ = lean_ctor_get(v___x_2278_, 4);
v_env_2280_ = lean_ctor_get(v___x_2278_, 0);
v_nextMacroScope_2281_ = lean_ctor_get(v___x_2278_, 1);
v_ngen_2282_ = lean_ctor_get(v___x_2278_, 2);
v_auxDeclNGen_2283_ = lean_ctor_get(v___x_2278_, 3);
v_cache_2284_ = lean_ctor_get(v___x_2278_, 5);
v_messages_2285_ = lean_ctor_get(v___x_2278_, 6);
v_infoState_2286_ = lean_ctor_get(v___x_2278_, 7);
v_snapshotTasks_2287_ = lean_ctor_get(v___x_2278_, 8);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2289_ = v___x_2278_;
v_isShared_2290_ = v_isSharedCheck_2306_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_snapshotTasks_2287_);
lean_inc(v_infoState_2286_);
lean_inc(v_messages_2285_);
lean_inc(v_cache_2284_);
lean_inc(v_traceState_2279_);
lean_inc(v_auxDeclNGen_2283_);
lean_inc(v_ngen_2282_);
lean_inc(v_nextMacroScope_2281_);
lean_inc(v_env_2280_);
lean_dec(v___x_2278_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2306_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
uint64_t v_tid_2291_; lean_object* v_traces_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2305_; 
v_tid_2291_ = lean_ctor_get_uint64(v_traceState_2279_, sizeof(void*)*1);
v_traces_2292_ = lean_ctor_get(v_traceState_2279_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v_traceState_2279_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2294_ = v_traceState_2279_;
v_isShared_2295_ = v_isSharedCheck_2305_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_traces_2292_);
lean_dec(v_traceState_2279_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2305_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2296_; lean_object* v___x_2298_; 
v___x_2296_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2227_, v_traces_2292_);
lean_dec_ref(v_traces_2292_);
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 0, v___x_2296_);
v___x_2298_ = v___x_2294_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v___x_2296_);
lean_ctor_set_uint64(v_reuseFailAlloc_2304_, sizeof(void*)*1, v_tid_2291_);
v___x_2298_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
lean_object* v___x_2300_; 
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 4, v___x_2298_);
v___x_2300_ = v___x_2289_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_env_2280_);
lean_ctor_set(v_reuseFailAlloc_2303_, 1, v_nextMacroScope_2281_);
lean_ctor_set(v_reuseFailAlloc_2303_, 2, v_ngen_2282_);
lean_ctor_set(v_reuseFailAlloc_2303_, 3, v_auxDeclNGen_2283_);
lean_ctor_set(v_reuseFailAlloc_2303_, 4, v___x_2298_);
lean_ctor_set(v_reuseFailAlloc_2303_, 5, v_cache_2284_);
lean_ctor_set(v_reuseFailAlloc_2303_, 6, v_messages_2285_);
lean_ctor_set(v_reuseFailAlloc_2303_, 7, v_infoState_2286_);
lean_ctor_set(v_reuseFailAlloc_2303_, 8, v_snapshotTasks_2287_);
v___x_2300_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2301_ = lean_st_ref_set(v___y_2231_, v___x_2300_);
v___x_2302_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4___redArg(v_fst_2233_);
return v___x_2302_;
}
}
}
}
}
else
{
goto v___jp_2271_;
}
}
else
{
goto v___jp_2271_;
}
}
v___jp_2307_:
{
double v___x_2309_; double v___x_2310_; double v___x_2311_; uint8_t v___x_2312_; 
v___x_2309_ = lean_unbox_float(v_snd_2245_);
v___x_2310_ = lean_unbox_float(v_fst_2244_);
v___x_2311_ = lean_float_sub(v___x_2309_, v___x_2310_);
v___x_2312_ = lean_float_decLt(v___y_2308_, v___x_2311_);
v___y_2277_ = v___x_2312_;
goto v___jp_2276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___boxed(lean_object* v_cls_2325_, lean_object* v_collapsed_2326_, lean_object* v_tag_2327_, lean_object* v_opts_2328_, lean_object* v_clsEnabled_2329_, lean_object* v_oldTraces_2330_, lean_object* v_msg_2331_, lean_object* v_resStartStop_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
uint8_t v_collapsed_boxed_2336_; uint8_t v_clsEnabled_boxed_2337_; lean_object* v_res_2338_; 
v_collapsed_boxed_2336_ = lean_unbox(v_collapsed_2326_);
v_clsEnabled_boxed_2337_ = lean_unbox(v_clsEnabled_2329_);
v_res_2338_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2(v_cls_2325_, v_collapsed_boxed_2336_, v_tag_2327_, v_opts_2328_, v_clsEnabled_boxed_2337_, v_oldTraces_2330_, v_msg_2331_, v_resStartStop_2332_, v___y_2333_, v___y_2334_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec_ref(v_opts_2328_);
return v_res_2338_;
}
}
static double _init_l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2341_; double v___x_2342_; 
v___x_2341_ = lean_unsigned_to_nat(1000000000u);
v___x_2342_ = lean_float_of_nat(v___x_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1(lean_object* v_decl_2343_, lean_object* v___x_2344_, uint8_t v___x_2345_, lean_object* v___x_2346_, lean_object* v___f_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v___y_2352_; lean_object* v___y_2353_; uint8_t v___y_2354_; lean_object* v___y_2365_; lean_object* v_a_2366_; lean_object* v___y_2370_; lean_object* v___y_2371_; uint8_t v___y_2372_; lean_object* v___y_2383_; lean_object* v_a_2384_; lean_object* v_options_2387_; uint8_t v_hasTrace_2388_; 
v_options_2387_ = lean_ctor_get(v___y_2348_, 2);
v_hasTrace_2388_ = lean_ctor_get_uint8(v_options_2387_, sizeof(void*)*1);
if (v_hasTrace_2388_ == 0)
{
lean_object* v_cancelTk_x3f_2389_; lean_object* v___x_2390_; 
lean_dec_ref(v___f_2347_);
lean_dec_ref(v___x_2346_);
lean_dec(v___x_2344_);
v_cancelTk_x3f_2389_ = lean_ctor_get(v___y_2348_, 12);
lean_inc(v_decl_2343_);
v___x_2390_ = l_Lean_warnIfUsesSorry(v_decl_2343_, v___y_2348_, v___y_2349_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v___x_2391_; lean_object* v_env_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
lean_dec_ref(v___x_2390_);
v___x_2391_ = lean_st_ref_get(v___y_2349_);
v_env_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc_ref(v_env_2392_);
lean_dec(v___x_2391_);
v___x_2393_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2392_, v_options_2387_, v_decl_2343_, v_cancelTk_x3f_2389_);
v___x_2394_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_2393_, v___y_2348_, v___y_2349_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v___x_2396_; 
lean_dec(v_decl_2343_);
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_a_2395_);
lean_dec_ref(v___x_2394_);
v___x_2396_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_2395_, v___y_2349_);
return v___x_2396_;
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
v_a_2397_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2394_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2394_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
lean_inc(v_a_2397_);
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
v___y_2383_ = v___x_2402_;
v_a_2384_ = v_a_2397_;
goto v___jp_2382_;
}
}
}
}
else
{
lean_dec(v_decl_2343_);
return v___x_2390_;
}
}
else
{
lean_object* v_cancelTk_x3f_2405_; lean_object* v_inheritedTraceOptions_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; uint8_t v___x_2409_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v_a_2413_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v_a_2428_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v_a_2433_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; uint8_t v___y_2445_; lean_object* v___y_2448_; lean_object* v___y_2449_; lean_object* v_a_2450_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v_a_2456_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v_a_2468_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v_a_2473_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; uint8_t v___y_2485_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v_a_2490_; 
v_cancelTk_x3f_2405_ = lean_ctor_get(v___y_2348_, 12);
v_inheritedTraceOptions_2406_ = lean_ctor_get(v___y_2348_, 13);
v___x_2407_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v___x_2344_);
v___x_2408_ = l_Lean_Name_append(v___x_2407_, v___x_2344_);
v___x_2409_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2406_, v_options_2387_, v___x_2408_);
lean_dec(v___x_2408_);
if (v___x_2409_ == 0)
{
lean_object* v___x_2518_; uint8_t v___x_2519_; 
v___x_2518_ = l_Lean_trace_profiler;
v___x_2519_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2387_, v___x_2518_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; 
lean_dec_ref(v___f_2347_);
lean_dec_ref(v___x_2346_);
lean_dec(v___x_2344_);
lean_inc(v_decl_2343_);
v___x_2520_ = l_Lean_warnIfUsesSorry(v_decl_2343_, v___y_2348_, v___y_2349_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v___x_2521_; lean_object* v_env_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
lean_dec_ref(v___x_2520_);
v___x_2521_ = lean_st_ref_get(v___y_2349_);
v_env_2522_ = lean_ctor_get(v___x_2521_, 0);
lean_inc_ref(v_env_2522_);
lean_dec(v___x_2521_);
v___x_2523_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2522_, v_options_2387_, v_decl_2343_, v_cancelTk_x3f_2405_);
v___x_2524_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_2523_, v___y_2348_, v___y_2349_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_a_2525_; lean_object* v___x_2526_; 
lean_dec(v_decl_2343_);
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_a_2525_);
lean_dec_ref(v___x_2524_);
v___x_2526_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_2525_, v___y_2349_);
return v___x_2526_;
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
v_a_2527_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___x_2524_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2524_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
lean_inc(v_a_2527_);
if (v_isShared_2530_ == 0)
{
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
v___y_2365_ = v___x_2532_;
v_a_2366_ = v_a_2527_;
goto v___jp_2364_;
}
}
}
}
else
{
lean_dec(v_decl_2343_);
return v___x_2520_;
}
}
else
{
goto v___jp_2493_;
}
}
else
{
goto v___jp_2493_;
}
v___jp_2410_:
{
lean_object* v___x_2414_; double v___x_2415_; double v___x_2416_; double v___x_2417_; double v___x_2418_; double v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2414_ = lean_io_mono_nanos_now();
v___x_2415_ = lean_float_of_nat(v___y_2412_);
v___x_2416_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__1);
v___x_2417_ = lean_float_div(v___x_2415_, v___x_2416_);
v___x_2418_ = lean_float_of_nat(v___x_2414_);
v___x_2419_ = lean_float_div(v___x_2418_, v___x_2416_);
v___x_2420_ = lean_box_float(v___x_2417_);
v___x_2421_ = lean_box_float(v___x_2419_);
v___x_2422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2420_);
lean_ctor_set(v___x_2422_, 1, v___x_2421_);
v___x_2423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2423_, 0, v_a_2413_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
v___x_2424_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2(v___x_2344_, v___x_2345_, v___x_2346_, v_options_2387_, v___x_2409_, v___y_2411_, v___f_2347_, v___x_2423_, v___y_2348_, v___y_2349_);
return v___x_2424_;
}
v___jp_2425_:
{
lean_object* v___x_2429_; 
v___x_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2429_, 0, v_a_2428_);
v___y_2411_ = v___y_2427_;
v___y_2412_ = v___y_2426_;
v_a_2413_ = v___x_2429_;
goto v___jp_2410_;
}
v___jp_2430_:
{
lean_object* v___x_2434_; 
v___x_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2434_, 0, v_a_2433_);
v___y_2411_ = v___y_2432_;
v___y_2412_ = v___y_2431_;
v_a_2413_ = v___x_2434_;
goto v___jp_2410_;
}
v___jp_2435_:
{
if (lean_obj_tag(v___y_2438_) == 0)
{
lean_object* v_a_2439_; 
v_a_2439_ = lean_ctor_get(v___y_2438_, 0);
lean_inc(v_a_2439_);
lean_dec_ref(v___y_2438_);
v___y_2431_ = v___y_2437_;
v___y_2432_ = v___y_2436_;
v_a_2433_ = v_a_2439_;
goto v___jp_2430_;
}
else
{
lean_object* v_a_2440_; 
v_a_2440_ = lean_ctor_get(v___y_2438_, 0);
lean_inc(v_a_2440_);
lean_dec_ref(v___y_2438_);
v___y_2426_ = v___y_2437_;
v___y_2427_ = v___y_2436_;
v_a_2428_ = v_a_2440_;
goto v___jp_2425_;
}
}
v___jp_2441_:
{
if (v___y_2445_ == 0)
{
lean_object* v___x_2446_; 
v___x_2446_ = l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom(v_decl_2343_, v___y_2348_, v___y_2349_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_dec_ref(v___x_2446_);
v___y_2426_ = v___y_2444_;
v___y_2427_ = v___y_2443_;
v_a_2428_ = v___y_2442_;
goto v___jp_2425_;
}
else
{
lean_dec_ref(v___y_2442_);
v___y_2436_ = v___y_2443_;
v___y_2437_ = v___y_2444_;
v___y_2438_ = v___x_2446_;
goto v___jp_2435_;
}
}
else
{
lean_dec(v_decl_2343_);
v___y_2426_ = v___y_2444_;
v___y_2427_ = v___y_2443_;
v_a_2428_ = v___y_2442_;
goto v___jp_2425_;
}
}
v___jp_2447_:
{
uint8_t v___x_2451_; 
v___x_2451_ = l_Lean_Exception_isInterrupt(v_a_2450_);
if (v___x_2451_ == 0)
{
uint8_t v___x_2452_; 
lean_inc_ref(v_a_2450_);
v___x_2452_ = l_Lean_Exception_isRuntime(v_a_2450_);
v___y_2442_ = v_a_2450_;
v___y_2443_ = v___y_2449_;
v___y_2444_ = v___y_2448_;
v___y_2445_ = v___x_2452_;
goto v___jp_2441_;
}
else
{
v___y_2442_ = v_a_2450_;
v___y_2443_ = v___y_2449_;
v___y_2444_ = v___y_2448_;
v___y_2445_ = v___x_2451_;
goto v___jp_2441_;
}
}
v___jp_2453_:
{
lean_object* v___x_2457_; double v___x_2458_; double v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2457_ = lean_io_get_num_heartbeats();
v___x_2458_ = lean_float_of_nat(v___y_2455_);
v___x_2459_ = lean_float_of_nat(v___x_2457_);
v___x_2460_ = lean_box_float(v___x_2458_);
v___x_2461_ = lean_box_float(v___x_2459_);
v___x_2462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2460_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
v___x_2463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2463_, 0, v_a_2456_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
v___x_2464_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2(v___x_2344_, v___x_2345_, v___x_2346_, v_options_2387_, v___x_2409_, v___y_2454_, v___f_2347_, v___x_2463_, v___y_2348_, v___y_2349_);
return v___x_2464_;
}
v___jp_2465_:
{
lean_object* v___x_2469_; 
v___x_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2469_, 0, v_a_2468_);
v___y_2454_ = v___y_2466_;
v___y_2455_ = v___y_2467_;
v_a_2456_ = v___x_2469_;
goto v___jp_2453_;
}
v___jp_2470_:
{
lean_object* v___x_2474_; 
v___x_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2474_, 0, v_a_2473_);
v___y_2454_ = v___y_2471_;
v___y_2455_ = v___y_2472_;
v_a_2456_ = v___x_2474_;
goto v___jp_2453_;
}
v___jp_2475_:
{
if (lean_obj_tag(v___y_2478_) == 0)
{
lean_object* v_a_2479_; 
v_a_2479_ = lean_ctor_get(v___y_2478_, 0);
lean_inc(v_a_2479_);
lean_dec_ref(v___y_2478_);
v___y_2471_ = v___y_2476_;
v___y_2472_ = v___y_2477_;
v_a_2473_ = v_a_2479_;
goto v___jp_2470_;
}
else
{
lean_object* v_a_2480_; 
v_a_2480_ = lean_ctor_get(v___y_2478_, 0);
lean_inc(v_a_2480_);
lean_dec_ref(v___y_2478_);
v___y_2466_ = v___y_2476_;
v___y_2467_ = v___y_2477_;
v_a_2468_ = v_a_2480_;
goto v___jp_2465_;
}
}
v___jp_2481_:
{
if (v___y_2485_ == 0)
{
lean_object* v___x_2486_; 
v___x_2486_ = l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom(v_decl_2343_, v___y_2348_, v___y_2349_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_dec_ref(v___x_2486_);
v___y_2466_ = v___y_2483_;
v___y_2467_ = v___y_2484_;
v_a_2468_ = v___y_2482_;
goto v___jp_2465_;
}
else
{
lean_dec_ref(v___y_2482_);
v___y_2476_ = v___y_2483_;
v___y_2477_ = v___y_2484_;
v___y_2478_ = v___x_2486_;
goto v___jp_2475_;
}
}
else
{
lean_dec(v_decl_2343_);
v___y_2466_ = v___y_2483_;
v___y_2467_ = v___y_2484_;
v_a_2468_ = v___y_2482_;
goto v___jp_2465_;
}
}
v___jp_2487_:
{
uint8_t v___x_2491_; 
v___x_2491_ = l_Lean_Exception_isInterrupt(v_a_2490_);
if (v___x_2491_ == 0)
{
uint8_t v___x_2492_; 
lean_inc_ref(v_a_2490_);
v___x_2492_ = l_Lean_Exception_isRuntime(v_a_2490_);
v___y_2482_ = v_a_2490_;
v___y_2483_ = v___y_2488_;
v___y_2484_ = v___y_2489_;
v___y_2485_ = v___x_2492_;
goto v___jp_2481_;
}
else
{
v___y_2482_ = v_a_2490_;
v___y_2483_ = v___y_2488_;
v___y_2484_ = v___y_2489_;
v___y_2485_ = v___x_2491_;
goto v___jp_2481_;
}
}
v___jp_2493_:
{
lean_object* v___x_2494_; lean_object* v_a_2495_; lean_object* v___x_2496_; uint8_t v___x_2497_; 
v___x_2494_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v___y_2349_);
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2495_);
lean_dec_ref(v___x_2494_);
v___x_2496_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2497_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2387_, v___x_2496_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2498_ = lean_io_mono_nanos_now();
lean_inc(v_decl_2343_);
v___x_2499_ = l_Lean_warnIfUsesSorry(v_decl_2343_, v___y_2348_, v___y_2349_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v___x_2500_; lean_object* v_env_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
lean_dec_ref(v___x_2499_);
v___x_2500_ = lean_st_ref_get(v___y_2349_);
v_env_2501_ = lean_ctor_get(v___x_2500_, 0);
lean_inc_ref(v_env_2501_);
lean_dec(v___x_2500_);
v___x_2502_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2501_, v_options_2387_, v_decl_2343_, v_cancelTk_x3f_2405_);
v___x_2503_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_2502_, v___y_2348_, v___y_2349_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; lean_object* v___x_2505_; lean_object* v_a_2506_; 
lean_dec(v_decl_2343_);
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2504_);
lean_dec_ref(v___x_2503_);
v___x_2505_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_2504_, v___y_2349_);
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2506_);
lean_dec_ref(v___x_2505_);
v___y_2431_ = v___x_2498_;
v___y_2432_ = v_a_2495_;
v_a_2433_ = v_a_2506_;
goto v___jp_2430_;
}
else
{
lean_object* v_a_2507_; 
v_a_2507_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2507_);
lean_dec_ref(v___x_2503_);
v___y_2448_ = v___x_2498_;
v___y_2449_ = v_a_2495_;
v_a_2450_ = v_a_2507_;
goto v___jp_2447_;
}
}
else
{
lean_dec(v_decl_2343_);
v___y_2436_ = v_a_2495_;
v___y_2437_ = v___x_2498_;
v___y_2438_ = v___x_2499_;
goto v___jp_2435_;
}
}
else
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = lean_io_get_num_heartbeats();
lean_inc(v_decl_2343_);
v___x_2509_ = l_Lean_warnIfUsesSorry(v_decl_2343_, v___y_2348_, v___y_2349_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v___x_2510_; lean_object* v_env_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
lean_dec_ref(v___x_2509_);
v___x_2510_ = lean_st_ref_get(v___y_2349_);
v_env_2511_ = lean_ctor_get(v___x_2510_, 0);
lean_inc_ref(v_env_2511_);
lean_dec(v___x_2510_);
v___x_2512_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2511_, v_options_2387_, v_decl_2343_, v_cancelTk_x3f_2405_);
v___x_2513_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_2512_, v___y_2348_, v___y_2349_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; lean_object* v___x_2515_; lean_object* v_a_2516_; 
lean_dec(v_decl_2343_);
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
lean_inc(v_a_2514_);
lean_dec_ref(v___x_2513_);
v___x_2515_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_2514_, v___y_2349_);
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2516_);
lean_dec_ref(v___x_2515_);
v___y_2471_ = v_a_2495_;
v___y_2472_ = v___x_2508_;
v_a_2473_ = v_a_2516_;
goto v___jp_2470_;
}
else
{
lean_object* v_a_2517_; 
v_a_2517_ = lean_ctor_get(v___x_2513_, 0);
lean_inc(v_a_2517_);
lean_dec_ref(v___x_2513_);
v___y_2488_ = v_a_2495_;
v___y_2489_ = v___x_2508_;
v_a_2490_ = v_a_2517_;
goto v___jp_2487_;
}
}
else
{
lean_dec(v_decl_2343_);
v___y_2476_ = v_a_2495_;
v___y_2477_ = v___x_2508_;
v___y_2478_ = v___x_2509_;
goto v___jp_2475_;
}
}
}
}
v___jp_2351_:
{
if (v___y_2354_ == 0)
{
lean_object* v___x_2355_; 
lean_dec_ref(v___y_2353_);
v___x_2355_ = l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom(v_decl_2343_, v___y_2348_, v___y_2349_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2362_ == 0)
{
lean_object* v_unused_2363_; 
v_unused_2363_ = lean_ctor_get(v___x_2355_, 0);
lean_dec(v_unused_2363_);
v___x_2357_ = v___x_2355_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_dec(v___x_2355_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
lean_ctor_set_tag(v___x_2357_, 1);
lean_ctor_set(v___x_2357_, 0, v___y_2352_);
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___y_2352_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
else
{
lean_dec_ref(v___y_2352_);
return v___x_2355_;
}
}
else
{
lean_dec_ref(v___y_2352_);
lean_dec(v_decl_2343_);
return v___y_2353_;
}
}
v___jp_2364_:
{
uint8_t v___x_2367_; 
v___x_2367_ = l_Lean_Exception_isInterrupt(v_a_2366_);
if (v___x_2367_ == 0)
{
uint8_t v___x_2368_; 
lean_inc_ref(v_a_2366_);
v___x_2368_ = l_Lean_Exception_isRuntime(v_a_2366_);
v___y_2352_ = v_a_2366_;
v___y_2353_ = v___y_2365_;
v___y_2354_ = v___x_2368_;
goto v___jp_2351_;
}
else
{
v___y_2352_ = v_a_2366_;
v___y_2353_ = v___y_2365_;
v___y_2354_ = v___x_2367_;
goto v___jp_2351_;
}
}
v___jp_2369_:
{
if (v___y_2372_ == 0)
{
lean_object* v___x_2373_; 
lean_dec_ref(v___y_2370_);
v___x_2373_ = l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom(v_decl_2343_, v___y_2348_, v___y_2349_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2380_ == 0)
{
lean_object* v_unused_2381_; 
v_unused_2381_ = lean_ctor_get(v___x_2373_, 0);
lean_dec(v_unused_2381_);
v___x_2375_ = v___x_2373_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_dec(v___x_2373_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
lean_ctor_set_tag(v___x_2375_, 1);
lean_ctor_set(v___x_2375_, 0, v___y_2371_);
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___y_2371_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
else
{
lean_dec_ref(v___y_2371_);
return v___x_2373_;
}
}
else
{
lean_dec_ref(v___y_2371_);
lean_dec(v_decl_2343_);
return v___y_2370_;
}
}
v___jp_2382_:
{
uint8_t v___x_2385_; 
v___x_2385_ = l_Lean_Exception_isInterrupt(v_a_2384_);
if (v___x_2385_ == 0)
{
uint8_t v___x_2386_; 
lean_inc_ref(v_a_2384_);
v___x_2386_ = l_Lean_Exception_isRuntime(v_a_2384_);
v___y_2370_ = v___y_2383_;
v___y_2371_ = v_a_2384_;
v___y_2372_ = v___x_2386_;
goto v___jp_2369_;
}
else
{
v___y_2370_ = v___y_2383_;
v___y_2371_ = v_a_2384_;
v___y_2372_ = v___x_2385_;
goto v___jp_2369_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___boxed(lean_object* v_decl_2535_, lean_object* v___x_2536_, lean_object* v___x_2537_, lean_object* v___x_2538_, lean_object* v___f_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
uint8_t v___x_8044__boxed_2543_; lean_object* v_res_2544_; 
v___x_8044__boxed_2543_ = lean_unbox(v___x_2537_);
v_res_2544_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1(v_decl_2535_, v___x_2536_, v___x_8044__boxed_2543_, v___x_2538_, v___f_2539_, v___y_2540_, v___y_2541_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(lean_object* v_decl_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_){
_start:
{
lean_object* v_options_2553_; lean_object* v___f_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; uint8_t v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___f_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v_options_2553_ = lean_ctor_get(v_a_2550_, 2);
lean_inc(v_decl_2549_);
v___f_2554_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2554_, 0, v_decl_2549_);
v___x_2555_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___closed__0));
v___x_2556_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___closed__2));
v___x_2557_ = 1;
v___x_2558_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2559_ = lean_box(v___x_2557_);
v___f_2560_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___boxed), 8, 5);
lean_closure_set(v___f_2560_, 0, v_decl_2549_);
lean_closure_set(v___f_2560_, 1, v___x_2556_);
lean_closure_set(v___f_2560_, 2, v___x_2559_);
lean_closure_set(v___f_2560_, 3, v___x_2558_);
lean_closure_set(v___f_2560_, 4, v___f_2554_);
v___x_2561_ = lean_box(0);
v___x_2562_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___redArg(v___x_2555_, v_options_2553_, v___f_2560_, v___x_2561_, v_a_2550_, v_a_2551_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___boxed(lean_object* v_decl_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_2563_, v_a_2564_, v_a_2565_);
lean_dec(v_a_2565_);
lean_dec_ref(v_a_2564_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4(lean_object* v_00_u03b1_2568_, lean_object* v_x_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v___x_2573_; 
v___x_2573_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4___redArg(v_x_2569_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2574_, lean_object* v_x_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4(v_00_u03b1_2574_, v_x_2575_, v___y_2576_, v___y_2577_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__0(lean_object* v___y_2580_, lean_object* v_a_2581_, lean_object* v___y_2582_, lean_object* v_a_x3f_2583_){
_start:
{
lean_object* v___x_2585_; lean_object* v_env_2586_; lean_object* v___x_2587_; 
v___x_2585_ = lean_st_ref_get(v___y_2580_);
v_env_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc_ref(v_env_2586_);
lean_dec(v___x_2585_);
v___x_2587_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2581_, v_env_2586_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2587_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2587_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
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
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2608_; 
v_a_2596_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2598_ = v___x_2587_;
v_isShared_2599_ = v_isSharedCheck_2608_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2587_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2608_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v_ref_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2606_; 
v_ref_2600_ = lean_ctor_get(v___y_2582_, 5);
v___x_2601_ = lean_io_error_to_string(v_a_2596_);
v___x_2602_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2601_);
v___x_2603_ = l_Lean_MessageData_ofFormat(v___x_2602_);
lean_inc(v_ref_2600_);
v___x_2604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2604_, 0, v_ref_2600_);
lean_ctor_set(v___x_2604_, 1, v___x_2603_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v___x_2604_);
v___x_2606_ = v___x_2598_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2604_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__0___boxed(lean_object* v___y_2609_, lean_object* v_a_2610_, lean_object* v___y_2611_, lean_object* v_a_x3f_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l_Lean_addDecl___lam__0(v___y_2609_, v_a_2610_, v___y_2611_, v_a_x3f_2612_);
lean_dec(v_a_x3f_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2609_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__2(lean_object* v_asyncEnv_2615_, lean_object* v_a_2616_, lean_object* v_decl_2617_, lean_object* v_x_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v___x_2622_; lean_object* v_r_2623_; 
v___x_2622_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_asyncEnv_2615_, v___y_2620_);
lean_dec_ref(v___x_2622_);
v_r_2623_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_2617_, v___y_2619_, v___y_2620_);
if (lean_obj_tag(v_r_2623_) == 0)
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2640_; 
v_a_2624_ = lean_ctor_get(v_r_2623_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v_r_2623_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2626_ = v_r_2623_;
v_isShared_2627_ = v_isSharedCheck_2640_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v_r_2623_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2640_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
lean_inc(v_a_2624_);
if (v_isShared_2627_ == 0)
{
lean_ctor_set_tag(v___x_2626_, 1);
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
lean_object* v___x_2630_; 
v___x_2630_ = l_Lean_addDecl___lam__0(v___y_2620_, v_a_2616_, v___y_2619_, v___x_2629_);
lean_dec_ref(v___x_2629_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2637_ == 0)
{
lean_object* v_unused_2638_; 
v_unused_2638_ = lean_ctor_get(v___x_2630_, 0);
lean_dec(v_unused_2638_);
v___x_2632_ = v___x_2630_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_dec(v___x_2630_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
lean_ctor_set(v___x_2632_, 0, v_a_2624_);
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2624_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
else
{
lean_dec(v_a_2624_);
return v___x_2630_;
}
}
}
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v_a_2641_ = lean_ctor_get(v_r_2623_, 0);
lean_inc(v_a_2641_);
lean_dec_ref(v_r_2623_);
v___x_2642_ = lean_box(0);
v___x_2643_ = l_Lean_addDecl___lam__0(v___y_2620_, v_a_2616_, v___y_2619_, v___x_2642_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2650_ == 0)
{
lean_object* v_unused_2651_; 
v_unused_2651_ = lean_ctor_get(v___x_2643_, 0);
lean_dec(v_unused_2651_);
v___x_2645_ = v___x_2643_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_dec(v___x_2643_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
lean_ctor_set_tag(v___x_2645_, 1);
lean_ctor_set(v___x_2645_, 0, v_a_2641_);
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2641_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
else
{
lean_dec(v_a_2641_);
return v___x_2643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__2___boxed(lean_object* v_asyncEnv_2652_, lean_object* v_a_2653_, lean_object* v_decl_2654_, lean_object* v_x_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_Lean_addDecl___lam__2(v_asyncEnv_2652_, v_a_2653_, v_decl_2654_, v_x_2655_, v___y_2656_, v___y_2657_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec_ref(v_x_2655_);
return v_res_2659_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2661_ = ((lean_object*)(l_Lean_addDecl___lam__1___closed__0));
v___x_2662_ = l_Lean_stringToMessageData(v___x_2661_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__1(lean_object* v_decl_2663_, lean_object* v_x_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2668_ = lean_obj_once(&l_Lean_addDecl___lam__1___closed__1, &l_Lean_addDecl___lam__1___closed__1_once, _init_l_Lean_addDecl___lam__1___closed__1);
v___x_2669_ = l_Lean_Declaration_getNames(v_decl_2663_);
v___x_2670_ = lean_box(0);
v___x_2671_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__0(v___x_2669_, v___x_2670_);
v___x_2672_ = l_Lean_MessageData_ofList(v___x_2671_);
v___x_2673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2668_);
lean_ctor_set(v___x_2673_, 1, v___x_2672_);
v___x_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2673_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__1___boxed(lean_object* v_decl_2675_, lean_object* v_x_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l_Lean_addDecl___lam__1(v_decl_2675_, v_x_2676_, v___y_2677_, v___y_2678_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec_ref(v_x_2676_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_addDecl_spec__0(lean_object* v_cls_2683_, lean_object* v_msg_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
lean_object* v_ref_2688_; lean_object* v___x_2689_; lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2734_; 
v_ref_2688_ = lean_ctor_get(v___y_2685_, 5);
v___x_2689_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2684_, v___y_2685_, v___y_2686_);
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2692_ = v___x_2689_;
v_isShared_2693_ = v_isSharedCheck_2734_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2689_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2734_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2694_; lean_object* v_traceState_2695_; lean_object* v_env_2696_; lean_object* v_nextMacroScope_2697_; lean_object* v_ngen_2698_; lean_object* v_auxDeclNGen_2699_; lean_object* v_cache_2700_; lean_object* v_messages_2701_; lean_object* v_infoState_2702_; lean_object* v_snapshotTasks_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2733_; 
v___x_2694_ = lean_st_ref_take(v___y_2686_);
v_traceState_2695_ = lean_ctor_get(v___x_2694_, 4);
v_env_2696_ = lean_ctor_get(v___x_2694_, 0);
v_nextMacroScope_2697_ = lean_ctor_get(v___x_2694_, 1);
v_ngen_2698_ = lean_ctor_get(v___x_2694_, 2);
v_auxDeclNGen_2699_ = lean_ctor_get(v___x_2694_, 3);
v_cache_2700_ = lean_ctor_get(v___x_2694_, 5);
v_messages_2701_ = lean_ctor_get(v___x_2694_, 6);
v_infoState_2702_ = lean_ctor_get(v___x_2694_, 7);
v_snapshotTasks_2703_ = lean_ctor_get(v___x_2694_, 8);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2705_ = v___x_2694_;
v_isShared_2706_ = v_isSharedCheck_2733_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_snapshotTasks_2703_);
lean_inc(v_infoState_2702_);
lean_inc(v_messages_2701_);
lean_inc(v_cache_2700_);
lean_inc(v_traceState_2695_);
lean_inc(v_auxDeclNGen_2699_);
lean_inc(v_ngen_2698_);
lean_inc(v_nextMacroScope_2697_);
lean_inc(v_env_2696_);
lean_dec(v___x_2694_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2733_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
uint64_t v_tid_2707_; lean_object* v_traces_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2732_; 
v_tid_2707_ = lean_ctor_get_uint64(v_traceState_2695_, sizeof(void*)*1);
v_traces_2708_ = lean_ctor_get(v_traceState_2695_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v_traceState_2695_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2710_ = v_traceState_2695_;
v_isShared_2711_ = v_isSharedCheck_2732_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_traces_2708_);
lean_dec(v_traceState_2695_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2732_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2712_; double v___x_2713_; uint8_t v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2722_; 
v___x_2712_ = lean_box(0);
v___x_2713_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__2);
v___x_2714_ = 0;
v___x_2715_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2716_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2716_, 0, v_cls_2683_);
lean_ctor_set(v___x_2716_, 1, v___x_2712_);
lean_ctor_set(v___x_2716_, 2, v___x_2715_);
lean_ctor_set_float(v___x_2716_, sizeof(void*)*3, v___x_2713_);
lean_ctor_set_float(v___x_2716_, sizeof(void*)*3 + 8, v___x_2713_);
lean_ctor_set_uint8(v___x_2716_, sizeof(void*)*3 + 16, v___x_2714_);
v___x_2717_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_addDecl_spec__0___closed__0));
v___x_2718_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2716_);
lean_ctor_set(v___x_2718_, 1, v_a_2690_);
lean_ctor_set(v___x_2718_, 2, v___x_2717_);
lean_inc(v_ref_2688_);
v___x_2719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2719_, 0, v_ref_2688_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
v___x_2720_ = l_Lean_PersistentArray_push___redArg(v_traces_2708_, v___x_2719_);
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 0, v___x_2720_);
v___x_2722_ = v___x_2710_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v___x_2720_);
lean_ctor_set_uint64(v_reuseFailAlloc_2731_, sizeof(void*)*1, v_tid_2707_);
v___x_2722_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
lean_object* v___x_2724_; 
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 4, v___x_2722_);
v___x_2724_ = v___x_2705_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_env_2696_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v_nextMacroScope_2697_);
lean_ctor_set(v_reuseFailAlloc_2730_, 2, v_ngen_2698_);
lean_ctor_set(v_reuseFailAlloc_2730_, 3, v_auxDeclNGen_2699_);
lean_ctor_set(v_reuseFailAlloc_2730_, 4, v___x_2722_);
lean_ctor_set(v_reuseFailAlloc_2730_, 5, v_cache_2700_);
lean_ctor_set(v_reuseFailAlloc_2730_, 6, v_messages_2701_);
lean_ctor_set(v_reuseFailAlloc_2730_, 7, v_infoState_2702_);
lean_ctor_set(v_reuseFailAlloc_2730_, 8, v_snapshotTasks_2703_);
v___x_2724_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2728_; 
v___x_2725_ = lean_st_ref_set(v___y_2686_, v___x_2724_);
v___x_2726_ = lean_box(0);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v___x_2726_);
v___x_2728_ = v___x_2692_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2726_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_addDecl_spec__0___boxed(lean_object* v_cls_2735_, lean_object* v_msg_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_2735_, v_msg_2736_, v___y_2737_, v___y_2738_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
return v_res_2740_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2742_ = ((lean_object*)(l_Lean_addDecl___lam__3___closed__0));
v___x_2743_ = l_Lean_stringToMessageData(v___x_2742_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__3(lean_object* v_decl_2744_, lean_object* v_cls_2745_, lean_object* v_x_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v_options_2750_; uint8_t v_hasTrace_2751_; 
v_options_2750_ = lean_ctor_get(v___y_2747_, 2);
v_hasTrace_2751_ = lean_ctor_get_uint8(v_options_2750_, sizeof(void*)*1);
if (v_hasTrace_2751_ == 0)
{
lean_object* v___x_2752_; 
lean_dec(v_cls_2745_);
v___x_2752_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_2744_, v___y_2747_, v___y_2748_);
return v___x_2752_;
}
else
{
lean_object* v_inheritedTraceOptions_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; uint8_t v___x_2756_; 
v_inheritedTraceOptions_2753_ = lean_ctor_get(v___y_2747_, 13);
v___x_2754_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v_cls_2745_);
v___x_2755_ = l_Lean_Name_append(v___x_2754_, v_cls_2745_);
v___x_2756_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2753_, v_options_2750_, v___x_2755_);
lean_dec(v___x_2755_);
if (v___x_2756_ == 0)
{
lean_object* v___x_2757_; 
lean_dec(v_cls_2745_);
v___x_2757_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_2744_, v___y_2747_, v___y_2748_);
return v___x_2757_;
}
else
{
lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2758_ = lean_obj_once(&l_Lean_addDecl___lam__3___closed__1, &l_Lean_addDecl___lam__3___closed__1_once, _init_l_Lean_addDecl___lam__3___closed__1);
v___x_2759_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_2745_, v___x_2758_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v___x_2760_; 
lean_dec_ref(v___x_2759_);
v___x_2760_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_2744_, v___y_2747_, v___y_2748_);
return v___x_2760_;
}
else
{
lean_dec(v_decl_2744_);
return v___x_2759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__3___boxed(lean_object* v_decl_2761_, lean_object* v_cls_2762_, lean_object* v_x_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l_Lean_addDecl___lam__3(v_decl_2761_, v_cls_2762_, v_x_2763_, v___y_2764_, v___y_2765_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
lean_dec(v_x_2763_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_addDecl_spec__2___redArg(lean_object* v_opt_2768_, lean_object* v___y_2769_){
_start:
{
lean_object* v_options_2771_; uint8_t v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v_options_2771_ = lean_ctor_get(v___y_2769_, 2);
v___x_2772_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2771_, v_opt_2768_);
v___x_2773_ = lean_box(v___x_2772_);
v___x_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2773_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_addDecl_spec__2___redArg___boxed(lean_object* v_opt_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__2___redArg(v_opt_2775_, v___y_2776_);
lean_dec_ref(v___y_2776_);
lean_dec_ref(v_opt_2775_);
return v_res_2778_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__8___closed__2(void){
_start:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2781_ = ((lean_object*)(l_Lean_addDecl___lam__8___closed__1));
v___x_2782_ = l_Lean_stringToMessageData(v___x_2781_);
return v___x_2782_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__8___closed__4(void){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = ((lean_object*)(l_Lean_addDecl___lam__8___closed__3));
v___x_2785_ = l_Lean_stringToMessageData(v___x_2784_);
return v___x_2785_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__8___closed__6(void){
_start:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = ((lean_object*)(l_Lean_addDecl___lam__8___closed__5));
v___x_2788_ = l_Lean_stringToMessageData(v___x_2787_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__8(lean_object* v_decl_2789_, lean_object* v___x_2790_, uint8_t v_hasTrace_2791_, uint8_t v___x_2792_, lean_object* v___x_2793_, lean_object* v_cls_2794_, lean_object* v___x_2795_, lean_object* v_____x_2796_, lean_object* v_exportedInfo_x3f_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v_a_2804_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v_a_2817_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v_snd_2901_; lean_object* v_fst_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_3030_; 
v_snd_2901_ = lean_ctor_get(v_____x_2796_, 1);
v_fst_2902_ = lean_ctor_get(v_____x_2796_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v_____x_2796_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_2904_ = v_____x_2796_;
v_isShared_2905_ = v_isSharedCheck_3030_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_snd_2901_);
lean_inc(v_fst_2902_);
lean_dec(v_____x_2796_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_3030_;
goto v_resetjp_2903_;
}
v___jp_2801_:
{
lean_object* v___x_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2812_; 
v___x_2805_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_2802_, v___y_2803_);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2812_ == 0)
{
lean_object* v_unused_2813_; 
v_unused_2813_ = lean_ctor_get(v___x_2805_, 0);
lean_dec(v_unused_2813_);
v___x_2807_ = v___x_2805_;
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
else
{
lean_dec(v___x_2805_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2810_; 
if (v_isShared_2808_ == 0)
{
lean_ctor_set_tag(v___x_2807_, 1);
lean_ctor_set(v___x_2807_, 0, v_a_2804_);
v___x_2810_ = v___x_2807_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_a_2804_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
v___jp_2814_:
{
lean_object* v___x_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
v___x_2818_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_2815_, v___y_2816_);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2825_ == 0)
{
lean_object* v_unused_2826_; 
v_unused_2826_ = lean_ctor_get(v___x_2818_, 0);
lean_dec(v_unused_2826_);
v___x_2820_ = v___x_2818_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_dec(v___x_2818_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 0, v_a_2817_);
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2817_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
v___jp_2827_:
{
lean_object* v___x_2838_; 
lean_inc_ref(v___y_2829_);
v___x_2838_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_2832_, v___y_2829_, v___y_2836_, v___y_2837_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v___x_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2886_; 
lean_dec_ref(v___x_2838_);
lean_inc_ref(v___y_2831_);
v___x_2839_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_2831_, v___y_2833_);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2886_ == 0)
{
lean_object* v_unused_2887_; 
v_unused_2887_ = lean_ctor_get(v___x_2839_, 0);
lean_dec(v_unused_2887_);
v___x_2841_ = v___x_2839_;
v_isShared_2842_ = v_isSharedCheck_2886_;
goto v_resetjp_2840_;
}
else
{
lean_dec(v___x_2839_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2886_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v_options_2843_; lean_object* v___x_2844_; uint8_t v___x_2845_; 
v_options_2843_ = lean_ctor_get(v___y_2834_, 2);
v___x_2844_ = l_Lean_Elab_async;
v___x_2845_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2843_, v___x_2844_);
if (v___x_2845_ == 0)
{
lean_object* v___x_2846_; lean_object* v_r_2847_; 
lean_del_object(v___x_2841_);
lean_dec_ref(v___y_2830_);
lean_dec_ref(v___y_2828_);
lean_dec_ref(v___x_2790_);
v___x_2846_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_2829_, v___y_2833_);
lean_dec_ref(v___x_2846_);
v_r_2847_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_2789_, v___y_2834_, v___y_2833_);
if (lean_obj_tag(v_r_2847_) == 0)
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2857_; 
v_a_2848_ = lean_ctor_get(v_r_2847_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v_r_2847_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2850_ = v_r_2847_;
v_isShared_2851_ = v_isSharedCheck_2857_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v_r_2847_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2857_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
lean_inc(v_a_2848_);
if (v_isShared_2851_ == 0)
{
lean_ctor_set_tag(v___x_2850_, 1);
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
lean_object* v___x_2854_; 
v___x_2854_ = lean_apply_2(v___y_2835_, v___x_2853_, lean_box(0));
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_dec_ref(v___x_2854_);
v___y_2815_ = v___y_2831_;
v___y_2816_ = v___y_2833_;
v_a_2817_ = v_a_2848_;
goto v___jp_2814_;
}
else
{
lean_object* v_a_2855_; 
lean_dec(v_a_2848_);
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2855_);
lean_dec_ref(v___x_2854_);
v___y_2802_ = v___y_2831_;
v___y_2803_ = v___y_2833_;
v_a_2804_ = v_a_2855_;
goto v___jp_2801_;
}
}
}
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v_a_2858_ = lean_ctor_get(v_r_2847_, 0);
lean_inc(v_a_2858_);
lean_dec_ref(v_r_2847_);
v___x_2859_ = lean_box(0);
v___x_2860_ = lean_apply_2(v___y_2835_, v___x_2859_, lean_box(0));
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_dec_ref(v___x_2860_);
v___y_2802_ = v___y_2831_;
v___y_2803_ = v___y_2833_;
v_a_2804_ = v_a_2858_;
goto v___jp_2801_;
}
else
{
lean_object* v_a_2861_; 
lean_dec(v_a_2858_);
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
lean_dec_ref(v___x_2860_);
v___y_2802_ = v___y_2831_;
v___y_2803_ = v___y_2833_;
v_a_2804_ = v_a_2861_;
goto v___jp_2801_;
}
}
}
else
{
lean_object* v___x_2862_; lean_object* v___x_2864_; 
lean_dec_ref(v___y_2835_);
lean_dec_ref(v___y_2831_);
lean_dec_ref(v___y_2829_);
lean_dec(v_decl_2789_);
v___x_2862_ = l_IO_CancelToken_new();
if (v_isShared_2842_ == 0)
{
lean_ctor_set_tag(v___x_2841_, 1);
lean_ctor_set(v___x_2841_, 0, v___x_2862_);
v___x_2864_ = v___x_2841_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v___x_2862_);
v___x_2864_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2865_ = ((lean_object*)(l_Lean_initFn___closed__5_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_2866_ = l_Lean_Name_mkStr2(v___x_2865_, v___x_2790_);
v___x_2867_ = l_Lean_Name_toString(v___x_2866_, v_hasTrace_2791_);
lean_inc_ref(v___x_2864_);
v___x_2868_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_2830_, v___x_2864_, v___x_2867_, v___y_2834_, v___y_2833_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; lean_object* v_checked_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_a_2869_);
lean_dec_ref(v___x_2868_);
v_checked_2870_ = lean_ctor_get(v___y_2828_, 2);
lean_inc_ref(v_checked_2870_);
lean_dec_ref(v___y_2828_);
v___x_2871_ = lean_unsigned_to_nat(0u);
v___x_2872_ = lean_io_map_task(v_a_2869_, v_checked_2870_, v___x_2871_, v___x_2792_);
v___x_2873_ = lean_box(0);
v___x_2874_ = lean_box(2);
v___x_2875_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2873_);
lean_ctor_set(v___x_2875_, 1, v___x_2874_);
lean_ctor_set(v___x_2875_, 2, v___x_2864_);
lean_ctor_set(v___x_2875_, 3, v___x_2872_);
v___x_2876_ = l_Lean_Core_logSnapshotTask___redArg(v___x_2875_, v___y_2833_);
return v___x_2876_;
}
else
{
lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2884_; 
lean_dec_ref(v___x_2864_);
lean_dec_ref(v___y_2828_);
v_a_2877_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2879_ = v___x_2868_;
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2868_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2882_; 
if (v_isShared_2880_ == 0)
{
v___x_2882_ = v___x_2879_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2877_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2900_; 
lean_dec_ref(v___y_2835_);
lean_dec_ref(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec_ref(v___x_2790_);
lean_dec(v_decl_2789_);
v_a_2888_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2890_ = v___x_2838_;
v_isShared_2891_ = v_isSharedCheck_2900_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2838_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2900_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v_ref_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2898_; 
v_ref_2892_ = lean_ctor_get(v___y_2834_, 5);
v___x_2893_ = lean_io_error_to_string(v_a_2888_);
v___x_2894_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2893_);
v___x_2895_ = l_Lean_MessageData_ofFormat(v___x_2894_);
lean_inc(v_ref_2892_);
v___x_2896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2896_, 0, v_ref_2892_);
lean_ctor_set(v___x_2896_, 1, v___x_2895_);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 0, v___x_2896_);
v___x_2898_ = v___x_2890_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2896_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
v_resetjp_2903_:
{
lean_object* v_fst_2906_; lean_object* v_snd_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_3029_; 
v_fst_2906_ = lean_ctor_get(v_snd_2901_, 0);
v_snd_2907_ = lean_ctor_get(v_snd_2901_, 1);
v_isSharedCheck_3029_ = !lean_is_exclusive(v_snd_2901_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_2909_ = v_snd_2901_;
v_isShared_2910_ = v_isSharedCheck_3029_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_snd_2907_);
lean_inc(v_fst_2906_);
lean_dec(v_snd_2901_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_3029_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v_exportedInfo_x3f_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___x_3019_; lean_object* v_env_3020_; uint8_t v___x_3021_; 
v___x_3019_ = lean_st_ref_get(v___y_2799_);
v_env_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc_ref(v_env_3020_);
lean_dec(v___x_3019_);
v___x_3021_ = l_Lean_Environment_containsOnBranch(v_env_3020_, v_fst_2902_);
lean_dec_ref(v_env_3020_);
if (v___x_3021_ == 0)
{
lean_del_object(v___x_2904_);
v___y_2986_ = v___y_2798_;
v___y_2987_ = v___y_2799_;
goto v___jp_2985_;
}
else
{
lean_object* v___x_3022_; lean_object* v_env_3023_; lean_object* v___x_3024_; lean_object* v___x_3026_; 
lean_del_object(v___x_2909_);
lean_dec(v_snd_2907_);
lean_dec(v_fst_2906_);
lean_dec(v_exportedInfo_x3f_2797_);
lean_dec(v___x_2795_);
lean_dec(v_cls_2794_);
lean_dec_ref(v___x_2793_);
lean_dec_ref(v___x_2790_);
lean_dec(v_decl_2789_);
v___x_3022_ = lean_st_ref_get(v___y_2799_);
v_env_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc_ref(v_env_3023_);
lean_dec(v___x_3022_);
v___x_3024_ = lean_elab_environment_to_kernel_env(v_env_3023_);
if (v_isShared_2905_ == 0)
{
lean_ctor_set_tag(v___x_2904_, 1);
lean_ctor_set(v___x_2904_, 1, v_fst_2902_);
lean_ctor_set(v___x_2904_, 0, v___x_3024_);
v___x_3026_ = v___x_2904_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___x_3024_);
lean_ctor_set(v_reuseFailAlloc_3028_, 1, v_fst_2902_);
v___x_3026_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
lean_object* v___x_3027_; 
v___x_3027_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(v___x_3026_, v___y_2798_, v___y_2799_);
return v___x_3027_;
}
}
v___jp_2911_:
{
uint8_t v___x_2919_; lean_object* v___x_2920_; 
v___x_2919_ = lean_unbox(v_snd_2907_);
lean_dec(v_snd_2907_);
lean_inc_ref(v___y_2914_);
v___x_2920_ = l_Lean_Environment_addConstAsync(v___y_2914_, v_fst_2902_, v___x_2919_, v___y_2918_, v___x_2792_, v_hasTrace_2791_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; lean_object* v_mainEnv_2922_; lean_object* v_asyncEnv_2923_; lean_object* v___f_2924_; lean_object* v___f_2925_; lean_object* v___x_2926_; 
lean_del_object(v___x_2909_);
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc_n(v_a_2921_, 3);
lean_dec_ref(v___x_2920_);
v_mainEnv_2922_ = lean_ctor_get(v_a_2921_, 0);
lean_inc_ref(v_mainEnv_2922_);
v_asyncEnv_2923_ = lean_ctor_get(v_a_2921_, 1);
lean_inc_ref_n(v_asyncEnv_2923_, 2);
lean_inc_ref(v___y_2912_);
lean_inc(v___y_2913_);
v___f_2924_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2924_, 0, v___y_2913_);
lean_closure_set(v___f_2924_, 1, v_a_2921_);
lean_closure_set(v___f_2924_, 2, v___y_2912_);
lean_inc(v_decl_2789_);
v___f_2925_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__2___boxed), 7, 3);
lean_closure_set(v___f_2925_, 0, v_asyncEnv_2923_);
lean_closure_set(v___f_2925_, 1, v_a_2921_);
lean_closure_set(v___f_2925_, 2, v_decl_2789_);
v___x_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2926_, 0, v_fst_2906_);
if (lean_obj_tag(v___y_2917_) == 0)
{
lean_inc_ref(v___x_2926_);
v___y_2828_ = v___y_2914_;
v___y_2829_ = v_asyncEnv_2923_;
v___y_2830_ = v___f_2925_;
v___y_2831_ = v_mainEnv_2922_;
v___y_2832_ = v_a_2921_;
v___y_2833_ = v___y_2915_;
v___y_2834_ = v___y_2916_;
v___y_2835_ = v___f_2924_;
v___y_2836_ = v___x_2926_;
v___y_2837_ = v___x_2926_;
goto v___jp_2827_;
}
else
{
v___y_2828_ = v___y_2914_;
v___y_2829_ = v_asyncEnv_2923_;
v___y_2830_ = v___f_2925_;
v___y_2831_ = v_mainEnv_2922_;
v___y_2832_ = v_a_2921_;
v___y_2833_ = v___y_2915_;
v___y_2834_ = v___y_2916_;
v___y_2835_ = v___f_2924_;
v___y_2836_ = v___x_2926_;
v___y_2837_ = v___y_2917_;
goto v___jp_2827_;
}
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2941_; 
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2914_);
lean_dec(v_fst_2906_);
lean_dec_ref(v___x_2790_);
lean_dec(v_decl_2789_);
v_a_2927_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2929_ = v___x_2920_;
v_isShared_2930_ = v_isSharedCheck_2941_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2920_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2941_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v_ref_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2936_; 
v_ref_2931_ = lean_ctor_get(v___y_2916_, 5);
v___x_2932_ = lean_io_error_to_string(v_a_2927_);
v___x_2933_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2932_);
v___x_2934_ = l_Lean_MessageData_ofFormat(v___x_2933_);
lean_inc(v_ref_2931_);
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 1, v___x_2934_);
lean_ctor_set(v___x_2909_, 0, v_ref_2931_);
v___x_2936_ = v___x_2909_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_ref_2931_);
lean_ctor_set(v_reuseFailAlloc_2940_, 1, v___x_2934_);
v___x_2936_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
lean_object* v___x_2938_; 
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 0, v___x_2936_);
v___x_2938_ = v___x_2929_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v___x_2936_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
}
}
v___jp_2942_:
{
lean_object* v___x_2946_; 
v___x_2946_ = lean_st_ref_get(v___y_2945_);
if (lean_obj_tag(v_exportedInfo_x3f_2943_) == 0)
{
lean_object* v_env_2947_; lean_object* v___x_2948_; 
v_env_2947_ = lean_ctor_get(v___x_2946_, 0);
lean_inc_ref(v_env_2947_);
lean_dec(v___x_2946_);
v___x_2948_ = lean_box(0);
v___y_2912_ = v___y_2944_;
v___y_2913_ = v___y_2945_;
v___y_2914_ = v_env_2947_;
v___y_2915_ = v___y_2945_;
v___y_2916_ = v___y_2944_;
v___y_2917_ = v_exportedInfo_x3f_2943_;
v___y_2918_ = v___x_2948_;
goto v___jp_2911_;
}
else
{
lean_object* v_env_2949_; lean_object* v_val_2950_; uint8_t v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v_env_2949_ = lean_ctor_get(v___x_2946_, 0);
lean_inc_ref(v_env_2949_);
lean_dec(v___x_2946_);
v_val_2950_ = lean_ctor_get(v_exportedInfo_x3f_2943_, 0);
v___x_2951_ = l_Lean_ConstantKind_ofConstantInfo(v_val_2950_);
v___x_2952_ = lean_box(v___x_2951_);
v___x_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2952_);
v___y_2912_ = v___y_2944_;
v___y_2913_ = v___y_2945_;
v___y_2914_ = v_env_2949_;
v___y_2915_ = v___y_2945_;
v___y_2916_ = v___y_2944_;
v___y_2917_ = v_exportedInfo_x3f_2943_;
v___y_2918_ = v___x_2953_;
goto v___jp_2911_;
}
}
v___jp_2954_:
{
lean_object* v___x_2957_; 
lean_inc(v_fst_2906_);
v___x_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2957_, 0, v_fst_2906_);
v_exportedInfo_x3f_2943_ = v___x_2957_;
v___y_2944_ = v___y_2955_;
v___y_2945_ = v___y_2956_;
goto v___jp_2942_;
}
v___jp_2958_:
{
lean_object* v___x_2961_; 
lean_inc(v_fst_2906_);
v___x_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2961_, 0, v_fst_2906_);
v_exportedInfo_x3f_2943_ = v___x_2961_;
v___y_2944_ = v___y_2959_;
v___y_2945_ = v___y_2960_;
goto v___jp_2942_;
}
v___jp_2962_:
{
lean_object* v___x_2965_; lean_object* v_env_2966_; lean_object* v_nextMacroScope_2967_; lean_object* v_ngen_2968_; lean_object* v_auxDeclNGen_2969_; lean_object* v_traceState_2970_; lean_object* v_messages_2971_; lean_object* v_infoState_2972_; lean_object* v_snapshotTasks_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2983_; 
v___x_2965_ = lean_st_ref_take(v___y_2963_);
v_env_2966_ = lean_ctor_get(v___x_2965_, 0);
v_nextMacroScope_2967_ = lean_ctor_get(v___x_2965_, 1);
v_ngen_2968_ = lean_ctor_get(v___x_2965_, 2);
v_auxDeclNGen_2969_ = lean_ctor_get(v___x_2965_, 3);
v_traceState_2970_ = lean_ctor_get(v___x_2965_, 4);
v_messages_2971_ = lean_ctor_get(v___x_2965_, 6);
v_infoState_2972_ = lean_ctor_get(v___x_2965_, 7);
v_snapshotTasks_2973_ = lean_ctor_get(v___x_2965_, 8);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2983_ == 0)
{
lean_object* v_unused_2984_; 
v_unused_2984_ = lean_ctor_get(v___x_2965_, 5);
lean_dec(v_unused_2984_);
v___x_2975_ = v___x_2965_;
v_isShared_2976_ = v_isSharedCheck_2983_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_snapshotTasks_2973_);
lean_inc(v_infoState_2972_);
lean_inc(v_messages_2971_);
lean_inc(v_traceState_2970_);
lean_inc(v_auxDeclNGen_2969_);
lean_inc(v_ngen_2968_);
lean_inc(v_nextMacroScope_2967_);
lean_inc(v_env_2966_);
lean_dec(v___x_2965_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2983_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2980_; 
v___x_2977_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_2907_);
lean_inc(v_fst_2902_);
v___x_2978_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2977_, v_env_2966_, v_fst_2902_, v_snd_2907_);
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 5, v___x_2793_);
lean_ctor_set(v___x_2975_, 0, v___x_2978_);
v___x_2980_ = v___x_2975_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v___x_2978_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_nextMacroScope_2967_);
lean_ctor_set(v_reuseFailAlloc_2982_, 2, v_ngen_2968_);
lean_ctor_set(v_reuseFailAlloc_2982_, 3, v_auxDeclNGen_2969_);
lean_ctor_set(v_reuseFailAlloc_2982_, 4, v_traceState_2970_);
lean_ctor_set(v_reuseFailAlloc_2982_, 5, v___x_2793_);
lean_ctor_set(v_reuseFailAlloc_2982_, 6, v_messages_2971_);
lean_ctor_set(v_reuseFailAlloc_2982_, 7, v_infoState_2972_);
lean_ctor_set(v_reuseFailAlloc_2982_, 8, v_snapshotTasks_2973_);
v___x_2980_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
lean_object* v___x_2981_; 
v___x_2981_ = lean_st_ref_set(v___y_2963_, v___x_2980_);
v_exportedInfo_x3f_2943_ = v_exportedInfo_x3f_2797_;
v___y_2944_ = v___y_2964_;
v___y_2945_ = v___y_2963_;
goto v___jp_2942_;
}
}
}
v___jp_2985_:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; uint8_t v___x_2990_; 
lean_inc(v_decl_2789_);
v___x_2988_ = l_Lean_Declaration_getTopLevelNames(v_decl_2789_);
v___x_2989_ = ((lean_object*)(l_Lean_addDecl___lam__8___closed__0));
v___x_2990_ = l_List_all___redArg(v___x_2988_, v___x_2989_);
if (v___x_2990_ == 0)
{
lean_dec(v___x_2795_);
if (lean_obj_tag(v_exportedInfo_x3f_2797_) == 0)
{
if (v___x_2792_ == 0)
{
lean_object* v_options_2991_; uint8_t v_hasTrace_2992_; 
lean_dec_ref(v___x_2793_);
v_options_2991_ = lean_ctor_get(v___y_2986_, 2);
v_hasTrace_2992_ = lean_ctor_get_uint8(v_options_2991_, sizeof(void*)*1);
if (v_hasTrace_2992_ == 0)
{
lean_dec(v_cls_2794_);
v___y_2955_ = v___y_2986_;
v___y_2956_ = v___y_2987_;
goto v___jp_2954_;
}
else
{
lean_object* v_inheritedTraceOptions_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; uint8_t v___x_2996_; 
v_inheritedTraceOptions_2993_ = lean_ctor_get(v___y_2986_, 13);
v___x_2994_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v_cls_2794_);
v___x_2995_ = l_Lean_Name_append(v___x_2994_, v_cls_2794_);
v___x_2996_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2993_, v_options_2991_, v___x_2995_);
lean_dec(v___x_2995_);
if (v___x_2996_ == 0)
{
lean_dec(v_cls_2794_);
v___y_2955_ = v___y_2986_;
v___y_2956_ = v___y_2987_;
goto v___jp_2954_;
}
else
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2997_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__2, &l_Lean_addDecl___lam__8___closed__2_once, _init_l_Lean_addDecl___lam__8___closed__2);
v___x_2998_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_2794_, v___x_2997_, v___y_2986_, v___y_2987_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_dec_ref(v___x_2998_);
v___y_2955_ = v___y_2986_;
v___y_2956_ = v___y_2987_;
goto v___jp_2954_;
}
else
{
lean_del_object(v___x_2909_);
lean_dec(v_snd_2907_);
lean_dec(v_fst_2906_);
lean_dec(v_fst_2902_);
lean_dec_ref(v___x_2790_);
lean_dec(v_decl_2789_);
return v___x_2998_;
}
}
}
}
else
{
lean_dec(v_cls_2794_);
v___y_2963_ = v___y_2987_;
v___y_2964_ = v___y_2986_;
goto v___jp_2962_;
}
}
else
{
lean_dec(v_cls_2794_);
v___y_2963_ = v___y_2987_;
v___y_2964_ = v___y_2986_;
goto v___jp_2962_;
}
}
else
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v_a_3001_; uint8_t v___x_3002_; 
lean_dec(v_exportedInfo_x3f_2797_);
lean_dec_ref(v___x_2793_);
v___x_2999_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3000_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__2___redArg(v___x_2999_, v___y_2986_);
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_a_3001_);
lean_dec_ref(v___x_3000_);
v___x_3002_ = lean_unbox(v_a_3001_);
lean_dec(v_a_3001_);
if (v___x_3002_ == 0)
{
lean_object* v_options_3003_; uint8_t v_hasTrace_3004_; 
v_options_3003_ = lean_ctor_get(v___y_2986_, 2);
v_hasTrace_3004_ = lean_ctor_get_uint8(v_options_3003_, sizeof(void*)*1);
if (v_hasTrace_3004_ == 0)
{
lean_dec(v_cls_2794_);
v_exportedInfo_x3f_2943_ = v___x_2795_;
v___y_2944_ = v___y_2986_;
v___y_2945_ = v___y_2987_;
goto v___jp_2942_;
}
else
{
lean_object* v_inheritedTraceOptions_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; uint8_t v___x_3008_; 
v_inheritedTraceOptions_3005_ = lean_ctor_get(v___y_2986_, 13);
v___x_3006_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v_cls_2794_);
v___x_3007_ = l_Lean_Name_append(v___x_3006_, v_cls_2794_);
v___x_3008_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3005_, v_options_3003_, v___x_3007_);
lean_dec(v___x_3007_);
if (v___x_3008_ == 0)
{
lean_dec(v_cls_2794_);
v_exportedInfo_x3f_2943_ = v___x_2795_;
v___y_2944_ = v___y_2986_;
v___y_2945_ = v___y_2987_;
goto v___jp_2942_;
}
else
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3009_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__4, &l_Lean_addDecl___lam__8___closed__4_once, _init_l_Lean_addDecl___lam__8___closed__4);
v___x_3010_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_2794_, v___x_3009_, v___y_2986_, v___y_2987_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_dec_ref(v___x_3010_);
v_exportedInfo_x3f_2943_ = v___x_2795_;
v___y_2944_ = v___y_2986_;
v___y_2945_ = v___y_2987_;
goto v___jp_2942_;
}
else
{
lean_del_object(v___x_2909_);
lean_dec(v_snd_2907_);
lean_dec(v_fst_2906_);
lean_dec(v_fst_2902_);
lean_dec(v___x_2795_);
lean_dec_ref(v___x_2790_);
lean_dec(v_decl_2789_);
return v___x_3010_;
}
}
}
}
else
{
lean_object* v_options_3011_; uint8_t v_hasTrace_3012_; 
lean_dec(v___x_2795_);
v_options_3011_ = lean_ctor_get(v___y_2986_, 2);
v_hasTrace_3012_ = lean_ctor_get_uint8(v_options_3011_, sizeof(void*)*1);
if (v_hasTrace_3012_ == 0)
{
lean_dec(v_cls_2794_);
v___y_2959_ = v___y_2986_;
v___y_2960_ = v___y_2987_;
goto v___jp_2958_;
}
else
{
lean_object* v_inheritedTraceOptions_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; uint8_t v___x_3016_; 
v_inheritedTraceOptions_3013_ = lean_ctor_get(v___y_2986_, 13);
v___x_3014_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v_cls_2794_);
v___x_3015_ = l_Lean_Name_append(v___x_3014_, v_cls_2794_);
v___x_3016_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3013_, v_options_3011_, v___x_3015_);
lean_dec(v___x_3015_);
if (v___x_3016_ == 0)
{
lean_dec(v_cls_2794_);
v___y_2959_ = v___y_2986_;
v___y_2960_ = v___y_2987_;
goto v___jp_2958_;
}
else
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3017_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__6, &l_Lean_addDecl___lam__8___closed__6_once, _init_l_Lean_addDecl___lam__8___closed__6);
v___x_3018_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_2794_, v___x_3017_, v___y_2986_, v___y_2987_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_dec_ref(v___x_3018_);
v___y_2959_ = v___y_2986_;
v___y_2960_ = v___y_2987_;
goto v___jp_2958_;
}
else
{
lean_del_object(v___x_2909_);
lean_dec(v_snd_2907_);
lean_dec(v_fst_2906_);
lean_dec(v_fst_2902_);
lean_dec_ref(v___x_2790_);
lean_dec(v_decl_2789_);
return v___x_3018_;
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
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__8___boxed(lean_object* v_decl_3031_, lean_object* v___x_3032_, lean_object* v_hasTrace_3033_, lean_object* v___x_3034_, lean_object* v___x_3035_, lean_object* v_cls_3036_, lean_object* v___x_3037_, lean_object* v_____x_3038_, lean_object* v_exportedInfo_x3f_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_){
_start:
{
uint8_t v_hasTrace_boxed_3043_; uint8_t v___x_61816__boxed_3044_; lean_object* v_res_3045_; 
v_hasTrace_boxed_3043_ = lean_unbox(v_hasTrace_3033_);
v___x_61816__boxed_3044_ = lean_unbox(v___x_3034_);
v_res_3045_ = l_Lean_addDecl___lam__8(v_decl_3031_, v___x_3032_, v_hasTrace_boxed_3043_, v___x_61816__boxed_3044_, v___x_3035_, v_cls_3036_, v___x_3037_, v_____x_3038_, v_exportedInfo_x3f_3039_, v___y_3040_, v___y_3041_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
return v_res_3045_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__4___closed__1(void){
_start:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3047_ = ((lean_object*)(l_Lean_addDecl___lam__4___closed__0));
v___x_3048_ = l_Lean_stringToMessageData(v___x_3047_);
return v___x_3048_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__4___closed__3(void){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = ((lean_object*)(l_Lean_addDecl___lam__4___closed__2));
v___x_3051_ = l_Lean_stringToMessageData(v___x_3050_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__4(lean_object* v___f_3052_, lean_object* v_cls_3053_, lean_object* v___x_3054_, uint8_t v___x_3055_, uint8_t v_forceExpose_3056_, lean_object* v_defn_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_){
_start:
{
lean_object* v_exportedInfo_x3f_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v_env_3100_; lean_object* v_env_3101_; 
v___x_3083_ = lean_st_ref_get(v___y_3059_);
v___x_3084_ = lean_st_ref_get(v___y_3059_);
v_env_3100_ = lean_ctor_get(v___x_3083_, 0);
lean_inc_ref(v_env_3100_);
lean_dec(v___x_3083_);
v_env_3101_ = lean_ctor_get(v___x_3084_, 0);
lean_inc_ref(v_env_3101_);
lean_dec(v___x_3084_);
if (v_forceExpose_3056_ == 0)
{
goto v___jp_3102_;
}
else
{
if (v___x_3055_ == 0)
{
lean_dec_ref(v_env_3101_);
lean_dec_ref(v_env_3100_);
lean_dec(v_cls_3053_);
v_exportedInfo_x3f_3062_ = v___x_3054_;
v___y_3063_ = v___y_3058_;
v___y_3064_ = v___y_3059_;
goto v___jp_3061_;
}
else
{
goto v___jp_3102_;
}
}
v___jp_3061_:
{
lean_object* v_toConstantVal_3065_; lean_object* v_name_3066_; lean_object* v___x_3067_; uint8_t v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v_toConstantVal_3065_ = lean_ctor_get(v_defn_3057_, 0);
v_name_3066_ = lean_ctor_get(v_toConstantVal_3065_, 0);
lean_inc(v_name_3066_);
v___x_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3067_, 0, v_defn_3057_);
v___x_3068_ = 0;
v___x_3069_ = lean_box(v___x_3068_);
v___x_3070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3067_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
v___x_3071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3071_, 0, v_name_3066_);
lean_ctor_set(v___x_3071_, 1, v___x_3070_);
lean_inc(v___y_3064_);
lean_inc_ref(v___y_3063_);
v___x_3072_ = lean_apply_5(v___f_3052_, v___x_3071_, v_exportedInfo_x3f_3062_, v___y_3063_, v___y_3064_, lean_box(0));
return v___x_3072_;
}
v___jp_3073_:
{
lean_object* v_toConstantVal_3076_; uint8_t v_safety_3077_; uint8_t v___x_3078_; uint8_t v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v_toConstantVal_3076_ = lean_ctor_get(v_defn_3057_, 0);
v_safety_3077_ = lean_ctor_get_uint8(v_defn_3057_, sizeof(void*)*4);
v___x_3078_ = 0;
v___x_3079_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3077_, v___x_3078_);
lean_inc_ref(v_toConstantVal_3076_);
v___x_3080_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3080_, 0, v_toConstantVal_3076_);
lean_ctor_set_uint8(v___x_3080_, sizeof(void*)*1, v___x_3079_);
v___x_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3080_);
v___x_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
v_exportedInfo_x3f_3062_ = v___x_3082_;
v___y_3063_ = v___y_3074_;
v___y_3064_ = v___y_3075_;
goto v___jp_3061_;
}
v___jp_3085_:
{
lean_object* v_options_3086_; uint8_t v_hasTrace_3087_; 
v_options_3086_ = lean_ctor_get(v___y_3058_, 2);
v_hasTrace_3087_ = lean_ctor_get_uint8(v_options_3086_, sizeof(void*)*1);
if (v_hasTrace_3087_ == 0)
{
lean_dec(v_cls_3053_);
v___y_3074_ = v___y_3058_;
v___y_3075_ = v___y_3059_;
goto v___jp_3073_;
}
else
{
lean_object* v_inheritedTraceOptions_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; uint8_t v___x_3091_; 
v_inheritedTraceOptions_3088_ = lean_ctor_get(v___y_3058_, 13);
v___x_3089_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v_cls_3053_);
v___x_3090_ = l_Lean_Name_append(v___x_3089_, v_cls_3053_);
v___x_3091_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3088_, v_options_3086_, v___x_3090_);
lean_dec(v___x_3090_);
if (v___x_3091_ == 0)
{
lean_dec(v_cls_3053_);
v___y_3074_ = v___y_3058_;
v___y_3075_ = v___y_3059_;
goto v___jp_3073_;
}
else
{
lean_object* v_toConstantVal_3092_; lean_object* v_name_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v_toConstantVal_3092_ = lean_ctor_get(v_defn_3057_, 0);
v_name_3093_ = lean_ctor_get(v_toConstantVal_3092_, 0);
v___x_3094_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__1, &l_Lean_addDecl___lam__4___closed__1_once, _init_l_Lean_addDecl___lam__4___closed__1);
lean_inc(v_name_3093_);
v___x_3095_ = l_Lean_MessageData_ofName(v_name_3093_);
v___x_3096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3094_);
lean_ctor_set(v___x_3096_, 1, v___x_3095_);
v___x_3097_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_3098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3096_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
v___x_3099_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3053_, v___x_3098_, v___y_3058_, v___y_3059_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_dec_ref(v___x_3099_);
v___y_3074_ = v___y_3058_;
v___y_3075_ = v___y_3059_;
goto v___jp_3073_;
}
else
{
lean_dec_ref(v_defn_3057_);
lean_dec_ref(v___f_3052_);
return v___x_3099_;
}
}
}
}
v___jp_3102_:
{
lean_object* v___x_3103_; uint8_t v_isModule_3104_; 
v___x_3103_ = l_Lean_Environment_header(v_env_3100_);
lean_dec_ref(v_env_3100_);
v_isModule_3104_ = lean_ctor_get_uint8(v___x_3103_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3103_);
if (v_isModule_3104_ == 0)
{
lean_dec_ref(v_env_3101_);
lean_dec(v_cls_3053_);
v_exportedInfo_x3f_3062_ = v___x_3054_;
v___y_3063_ = v___y_3058_;
v___y_3064_ = v___y_3059_;
goto v___jp_3061_;
}
else
{
uint8_t v_isExporting_3105_; 
v_isExporting_3105_ = lean_ctor_get_uint8(v_env_3101_, sizeof(void*)*8);
lean_dec_ref(v_env_3101_);
if (v_isExporting_3105_ == 0)
{
lean_dec(v___x_3054_);
goto v___jp_3085_;
}
else
{
if (v___x_3055_ == 0)
{
lean_dec(v_cls_3053_);
v_exportedInfo_x3f_3062_ = v___x_3054_;
v___y_3063_ = v___y_3058_;
v___y_3064_ = v___y_3059_;
goto v___jp_3061_;
}
else
{
lean_dec(v___x_3054_);
goto v___jp_3085_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__4___boxed(lean_object* v___f_3106_, lean_object* v_cls_3107_, lean_object* v___x_3108_, lean_object* v___x_3109_, lean_object* v_forceExpose_3110_, lean_object* v_defn_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
uint8_t v___x_62293__boxed_3115_; uint8_t v_forceExpose_boxed_3116_; lean_object* v_res_3117_; 
v___x_62293__boxed_3115_ = lean_unbox(v___x_3109_);
v_forceExpose_boxed_3116_ = lean_unbox(v_forceExpose_3110_);
v_res_3117_ = l_Lean_addDecl___lam__4(v___f_3106_, v_cls_3107_, v___x_3108_, v___x_62293__boxed_3115_, v_forceExpose_boxed_3116_, v_defn_3111_, v___y_3112_, v___y_3113_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__5(lean_object* v_val_3118_, lean_object* v___f_3119_, lean_object* v_____r_3120_, lean_object* v_exportedInfo_x3f_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v_toConstantVal_3125_; lean_object* v_name_3126_; lean_object* v___x_3127_; uint8_t v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v_toConstantVal_3125_ = lean_ctor_get(v_val_3118_, 0);
v_name_3126_ = lean_ctor_get(v_toConstantVal_3125_, 0);
lean_inc(v_name_3126_);
v___x_3127_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3127_, 0, v_val_3118_);
v___x_3128_ = 1;
v___x_3129_ = lean_box(v___x_3128_);
v___x_3130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3127_);
lean_ctor_set(v___x_3130_, 1, v___x_3129_);
v___x_3131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3131_, 0, v_name_3126_);
lean_ctor_set(v___x_3131_, 1, v___x_3130_);
lean_inc(v___y_3123_);
lean_inc_ref(v___y_3122_);
v___x_3132_ = lean_apply_5(v___f_3119_, v___x_3131_, v_exportedInfo_x3f_3121_, v___y_3122_, v___y_3123_, lean_box(0));
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__5___boxed(lean_object* v_val_3133_, lean_object* v___f_3134_, lean_object* v_____r_3135_, lean_object* v_exportedInfo_x3f_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l_Lean_addDecl___lam__5(v_val_3133_, v___f_3134_, v_____r_3135_, v_exportedInfo_x3f_3136_, v___y_3137_, v___y_3138_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__6(lean_object* v_val_3141_, uint8_t v___x_3142_, lean_object* v___f_3143_, lean_object* v_____r_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v_toConstantVal_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v_toConstantVal_3148_ = lean_ctor_get(v_val_3141_, 0);
lean_inc_ref(v_toConstantVal_3148_);
v___x_3149_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3149_, 0, v_toConstantVal_3148_);
lean_ctor_set_uint8(v___x_3149_, sizeof(void*)*1, v___x_3142_);
v___x_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3149_);
v___x_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3150_);
v___x_3152_ = lean_box(0);
lean_inc(v___y_3146_);
lean_inc_ref(v___y_3145_);
v___x_3153_ = lean_apply_5(v___f_3143_, v___x_3152_, v___x_3151_, v___y_3145_, v___y_3146_, lean_box(0));
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__6___boxed(lean_object* v_val_3154_, lean_object* v___x_3155_, lean_object* v___f_3156_, lean_object* v_____r_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
uint8_t v___x_62412__boxed_3161_; lean_object* v_res_3162_; 
v___x_62412__boxed_3161_ = lean_unbox(v___x_3155_);
v_res_3162_ = l_Lean_addDecl___lam__6(v_val_3154_, v___x_62412__boxed_3161_, v___f_3156_, v_____r_3157_, v___y_3158_, v___y_3159_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec_ref(v_val_3154_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__7(lean_object* v_val_3163_, lean_object* v___f_3164_, lean_object* v_____r_3165_, lean_object* v_exportedInfo_x3f_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_){
_start:
{
lean_object* v_toConstantVal_3170_; lean_object* v_name_3171_; lean_object* v___x_3172_; uint8_t v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v_toConstantVal_3170_ = lean_ctor_get(v_val_3163_, 0);
v_name_3171_ = lean_ctor_get(v_toConstantVal_3170_, 0);
lean_inc(v_name_3171_);
v___x_3172_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3172_, 0, v_val_3163_);
v___x_3173_ = 3;
v___x_3174_ = lean_box(v___x_3173_);
v___x_3175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3172_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
v___x_3176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3176_, 0, v_name_3171_);
lean_ctor_set(v___x_3176_, 1, v___x_3175_);
lean_inc(v___y_3168_);
lean_inc_ref(v___y_3167_);
v___x_3177_ = lean_apply_5(v___f_3164_, v___x_3176_, v_exportedInfo_x3f_3166_, v___y_3167_, v___y_3168_, lean_box(0));
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__7___boxed(lean_object* v_val_3178_, lean_object* v___f_3179_, lean_object* v_____r_3180_, lean_object* v_exportedInfo_x3f_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
lean_object* v_res_3185_; 
v_res_3185_ = l_Lean_addDecl___lam__7(v_val_3178_, v___f_3179_, v_____r_3180_, v_exportedInfo_x3f_3181_, v___y_3182_, v___y_3183_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__9(lean_object* v_val_3186_, lean_object* v___f_3187_, lean_object* v_____r_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v_toConstantVal_3192_; uint8_t v_isUnsafe_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
v_toConstantVal_3192_ = lean_ctor_get(v_val_3186_, 0);
v_isUnsafe_3193_ = lean_ctor_get_uint8(v_val_3186_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_3192_);
v___x_3194_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3194_, 0, v_toConstantVal_3192_);
lean_ctor_set_uint8(v___x_3194_, sizeof(void*)*1, v_isUnsafe_3193_);
v___x_3195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3194_);
v___x_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3195_);
v___x_3197_ = lean_box(0);
lean_inc(v___y_3190_);
lean_inc_ref(v___y_3189_);
v___x_3198_ = lean_apply_5(v___f_3187_, v___x_3197_, v___x_3196_, v___y_3189_, v___y_3190_, lean_box(0));
return v___x_3198_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__9___boxed(lean_object* v_val_3199_, lean_object* v___f_3200_, lean_object* v_____r_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l_Lean_addDecl___lam__9(v_val_3199_, v___f_3200_, v_____r_3201_, v___y_3202_, v___y_3203_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec_ref(v_val_3199_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__13(lean_object* v_decl_3206_, lean_object* v___x_3207_, uint8_t v___x_3208_, lean_object* v_cls_3209_, lean_object* v___x_3210_, lean_object* v___x_3211_, lean_object* v_____x_3212_, lean_object* v_exportedInfo_x3f_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_){
_start:
{
lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v_a_3220_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v_a_3233_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; uint8_t v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v_snd_3318_; lean_object* v_fst_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3449_; 
v_snd_3318_ = lean_ctor_get(v_____x_3212_, 1);
v_fst_3319_ = lean_ctor_get(v_____x_3212_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v_____x_3212_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3321_ = v_____x_3212_;
v_isShared_3322_ = v_isSharedCheck_3449_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_snd_3318_);
lean_inc(v_fst_3319_);
lean_dec(v_____x_3212_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3449_;
goto v_resetjp_3320_;
}
v___jp_3217_:
{
lean_object* v___x_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3228_; 
v___x_3221_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3218_, v___y_3219_);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3228_ == 0)
{
lean_object* v_unused_3229_; 
v_unused_3229_ = lean_ctor_get(v___x_3221_, 0);
lean_dec(v_unused_3229_);
v___x_3223_ = v___x_3221_;
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
else
{
lean_dec(v___x_3221_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3226_; 
if (v_isShared_3224_ == 0)
{
lean_ctor_set_tag(v___x_3223_, 1);
lean_ctor_set(v___x_3223_, 0, v_a_3220_);
v___x_3226_ = v___x_3223_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3220_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
v___jp_3230_:
{
lean_object* v___x_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
v___x_3234_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3231_, v___y_3232_);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3241_ == 0)
{
lean_object* v_unused_3242_; 
v_unused_3242_ = lean_ctor_get(v___x_3234_, 0);
lean_dec(v_unused_3242_);
v___x_3236_ = v___x_3234_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_dec(v___x_3234_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 0, v_a_3233_);
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3233_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
v___jp_3243_:
{
lean_object* v___x_3255_; 
lean_inc_ref(v___y_3247_);
v___x_3255_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3244_, v___y_3247_, v___y_3248_, v___y_3254_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v___x_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3303_; 
lean_dec_ref(v___x_3255_);
lean_inc_ref(v___y_3250_);
v___x_3256_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3250_, v___y_3253_);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3303_ == 0)
{
lean_object* v_unused_3304_; 
v_unused_3304_ = lean_ctor_get(v___x_3256_, 0);
lean_dec(v_unused_3304_);
v___x_3258_ = v___x_3256_;
v_isShared_3259_ = v_isSharedCheck_3303_;
goto v_resetjp_3257_;
}
else
{
lean_dec(v___x_3256_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3303_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v_options_3260_; lean_object* v___x_3261_; uint8_t v___x_3262_; 
v_options_3260_ = lean_ctor_get(v___y_3251_, 2);
v___x_3261_ = l_Lean_Elab_async;
v___x_3262_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3260_, v___x_3261_);
if (v___x_3262_ == 0)
{
lean_object* v___x_3263_; lean_object* v_r_3264_; 
lean_del_object(v___x_3258_);
lean_dec_ref(v___y_3252_);
lean_dec_ref(v___y_3245_);
lean_dec_ref(v___x_3207_);
v___x_3263_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3247_, v___y_3253_);
lean_dec_ref(v___x_3263_);
v_r_3264_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3206_, v___y_3251_, v___y_3253_);
if (lean_obj_tag(v_r_3264_) == 0)
{
lean_object* v_a_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3274_; 
v_a_3265_ = lean_ctor_get(v_r_3264_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v_r_3264_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3267_ = v_r_3264_;
v_isShared_3268_ = v_isSharedCheck_3274_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_a_3265_);
lean_dec(v_r_3264_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3274_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3270_; 
lean_inc(v_a_3265_);
if (v_isShared_3268_ == 0)
{
lean_ctor_set_tag(v___x_3267_, 1);
v___x_3270_ = v___x_3267_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_a_3265_);
v___x_3270_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
lean_object* v___x_3271_; 
v___x_3271_ = lean_apply_2(v___y_3246_, v___x_3270_, lean_box(0));
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_dec_ref(v___x_3271_);
v___y_3231_ = v___y_3250_;
v___y_3232_ = v___y_3253_;
v_a_3233_ = v_a_3265_;
goto v___jp_3230_;
}
else
{
lean_object* v_a_3272_; 
lean_dec(v_a_3265_);
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_a_3272_);
lean_dec_ref(v___x_3271_);
v___y_3218_ = v___y_3250_;
v___y_3219_ = v___y_3253_;
v_a_3220_ = v_a_3272_;
goto v___jp_3217_;
}
}
}
}
else
{
lean_object* v_a_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v_a_3275_ = lean_ctor_get(v_r_3264_, 0);
lean_inc(v_a_3275_);
lean_dec_ref(v_r_3264_);
v___x_3276_ = lean_box(0);
v___x_3277_ = lean_apply_2(v___y_3246_, v___x_3276_, lean_box(0));
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_dec_ref(v___x_3277_);
v___y_3218_ = v___y_3250_;
v___y_3219_ = v___y_3253_;
v_a_3220_ = v_a_3275_;
goto v___jp_3217_;
}
else
{
lean_object* v_a_3278_; 
lean_dec(v_a_3275_);
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_a_3278_);
lean_dec_ref(v___x_3277_);
v___y_3218_ = v___y_3250_;
v___y_3219_ = v___y_3253_;
v_a_3220_ = v_a_3278_;
goto v___jp_3217_;
}
}
}
else
{
lean_object* v___x_3279_; lean_object* v___x_3281_; 
lean_dec_ref(v___y_3250_);
lean_dec_ref(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v_decl_3206_);
v___x_3279_ = l_IO_CancelToken_new();
if (v_isShared_3259_ == 0)
{
lean_ctor_set_tag(v___x_3258_, 1);
lean_ctor_set(v___x_3258_, 0, v___x_3279_);
v___x_3281_ = v___x_3258_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v___x_3279_);
v___x_3281_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3282_ = ((lean_object*)(l_Lean_initFn___closed__5_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_3283_ = l_Lean_Name_mkStr2(v___x_3282_, v___x_3207_);
v___x_3284_ = l_Lean_Name_toString(v___x_3283_, v___x_3208_);
lean_inc_ref(v___x_3281_);
v___x_3285_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3252_, v___x_3281_, v___x_3284_, v___y_3251_, v___y_3253_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_a_3286_; lean_object* v_checked_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
lean_inc(v_a_3286_);
lean_dec_ref(v___x_3285_);
v_checked_3287_ = lean_ctor_get(v___y_3245_, 2);
lean_inc_ref(v_checked_3287_);
lean_dec_ref(v___y_3245_);
v___x_3288_ = lean_unsigned_to_nat(0u);
v___x_3289_ = lean_io_map_task(v_a_3286_, v_checked_3287_, v___x_3288_, v___y_3249_);
v___x_3290_ = lean_box(0);
v___x_3291_ = lean_box(2);
v___x_3292_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3290_);
lean_ctor_set(v___x_3292_, 1, v___x_3291_);
lean_ctor_set(v___x_3292_, 2, v___x_3281_);
lean_ctor_set(v___x_3292_, 3, v___x_3289_);
v___x_3293_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3292_, v___y_3253_);
return v___x_3293_;
}
else
{
lean_object* v_a_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
lean_dec_ref(v___x_3281_);
lean_dec_ref(v___y_3245_);
v_a_3294_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3296_ = v___x_3285_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_a_3294_);
lean_dec(v___x_3285_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3299_; 
if (v_isShared_3297_ == 0)
{
v___x_3299_ = v___x_3296_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_a_3294_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3317_; 
lean_dec_ref(v___y_3252_);
lean_dec_ref(v___y_3250_);
lean_dec_ref(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec_ref(v___x_3207_);
lean_dec(v_decl_3206_);
v_a_3305_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3307_ = v___x_3255_;
v_isShared_3308_ = v_isSharedCheck_3317_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_a_3305_);
lean_dec(v___x_3255_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3317_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v_ref_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3315_; 
v_ref_3309_ = lean_ctor_get(v___y_3251_, 5);
v___x_3310_ = lean_io_error_to_string(v_a_3305_);
v___x_3311_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
v___x_3312_ = l_Lean_MessageData_ofFormat(v___x_3311_);
lean_inc(v_ref_3309_);
v___x_3313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3313_, 0, v_ref_3309_);
lean_ctor_set(v___x_3313_, 1, v___x_3312_);
if (v_isShared_3308_ == 0)
{
lean_ctor_set(v___x_3307_, 0, v___x_3313_);
v___x_3315_ = v___x_3307_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3313_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
}
v_resetjp_3320_:
{
lean_object* v_fst_3323_; lean_object* v_snd_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3448_; 
v_fst_3323_ = lean_ctor_get(v_snd_3318_, 0);
v_snd_3324_ = lean_ctor_get(v_snd_3318_, 1);
v_isSharedCheck_3448_ = !lean_is_exclusive(v_snd_3318_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3326_ = v_snd_3318_;
v_isShared_3327_ = v_isSharedCheck_3448_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_snd_3324_);
lean_inc(v_fst_3323_);
lean_dec(v_snd_3318_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3448_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v_exportedInfo_x3f_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3381_; lean_object* v___y_3382_; uint8_t v___y_3383_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___x_3438_; lean_object* v_env_3439_; uint8_t v___x_3440_; 
v___x_3438_ = lean_st_ref_get(v___y_3215_);
v_env_3439_ = lean_ctor_get(v___x_3438_, 0);
lean_inc_ref(v_env_3439_);
lean_dec(v___x_3438_);
v___x_3440_ = l_Lean_Environment_containsOnBranch(v_env_3439_, v_fst_3319_);
lean_dec_ref(v_env_3439_);
if (v___x_3440_ == 0)
{
lean_del_object(v___x_3321_);
v___y_3413_ = v___y_3214_;
v___y_3414_ = v___y_3215_;
goto v___jp_3412_;
}
else
{
lean_object* v___x_3441_; lean_object* v_env_3442_; lean_object* v___x_3443_; lean_object* v___x_3445_; 
lean_del_object(v___x_3326_);
lean_dec(v_snd_3324_);
lean_dec(v_fst_3323_);
lean_dec(v_exportedInfo_x3f_3213_);
lean_dec(v___x_3211_);
lean_dec_ref(v___x_3210_);
lean_dec(v_cls_3209_);
lean_dec_ref(v___x_3207_);
lean_dec(v_decl_3206_);
v___x_3441_ = lean_st_ref_get(v___y_3215_);
v_env_3442_ = lean_ctor_get(v___x_3441_, 0);
lean_inc_ref(v_env_3442_);
lean_dec(v___x_3441_);
v___x_3443_ = lean_elab_environment_to_kernel_env(v_env_3442_);
if (v_isShared_3322_ == 0)
{
lean_ctor_set_tag(v___x_3321_, 1);
lean_ctor_set(v___x_3321_, 1, v_fst_3319_);
lean_ctor_set(v___x_3321_, 0, v___x_3443_);
v___x_3445_ = v___x_3321_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3443_);
lean_ctor_set(v_reuseFailAlloc_3447_, 1, v_fst_3319_);
v___x_3445_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
lean_object* v___x_3446_; 
v___x_3446_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(v___x_3445_, v___y_3214_, v___y_3215_);
return v___x_3446_;
}
}
v___jp_3328_:
{
uint8_t v___x_3336_; uint8_t v___x_3337_; lean_object* v___x_3338_; 
v___x_3336_ = 0;
v___x_3337_ = lean_unbox(v_snd_3324_);
lean_dec(v_snd_3324_);
lean_inc_ref(v___y_3330_);
v___x_3338_ = l_Lean_Environment_addConstAsync(v___y_3330_, v_fst_3319_, v___x_3337_, v___y_3335_, v___x_3336_, v___x_3208_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_a_3339_; lean_object* v_mainEnv_3340_; lean_object* v_asyncEnv_3341_; lean_object* v___f_3342_; lean_object* v___f_3343_; lean_object* v___x_3344_; 
lean_del_object(v___x_3326_);
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc_n(v_a_3339_, 3);
lean_dec_ref(v___x_3338_);
v_mainEnv_3340_ = lean_ctor_get(v_a_3339_, 0);
lean_inc_ref(v_mainEnv_3340_);
v_asyncEnv_3341_ = lean_ctor_get(v_a_3339_, 1);
lean_inc_ref_n(v_asyncEnv_3341_, 2);
lean_inc_ref(v___y_3331_);
lean_inc(v___y_3329_);
v___f_3342_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3342_, 0, v___y_3329_);
lean_closure_set(v___f_3342_, 1, v_a_3339_);
lean_closure_set(v___f_3342_, 2, v___y_3331_);
lean_inc(v_decl_3206_);
v___f_3343_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3343_, 0, v_asyncEnv_3341_);
lean_closure_set(v___f_3343_, 1, v_a_3339_);
lean_closure_set(v___f_3343_, 2, v_decl_3206_);
v___x_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3344_, 0, v_fst_3323_);
if (lean_obj_tag(v___y_3332_) == 0)
{
lean_inc_ref(v___x_3344_);
v___y_3244_ = v_a_3339_;
v___y_3245_ = v___y_3330_;
v___y_3246_ = v___f_3342_;
v___y_3247_ = v_asyncEnv_3341_;
v___y_3248_ = v___x_3344_;
v___y_3249_ = v___x_3336_;
v___y_3250_ = v_mainEnv_3340_;
v___y_3251_ = v___y_3333_;
v___y_3252_ = v___f_3343_;
v___y_3253_ = v___y_3334_;
v___y_3254_ = v___x_3344_;
goto v___jp_3243_;
}
else
{
v___y_3244_ = v_a_3339_;
v___y_3245_ = v___y_3330_;
v___y_3246_ = v___f_3342_;
v___y_3247_ = v_asyncEnv_3341_;
v___y_3248_ = v___x_3344_;
v___y_3249_ = v___x_3336_;
v___y_3250_ = v_mainEnv_3340_;
v___y_3251_ = v___y_3333_;
v___y_3252_ = v___f_3343_;
v___y_3253_ = v___y_3334_;
v___y_3254_ = v___y_3332_;
goto v___jp_3243_;
}
}
else
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3359_; 
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3330_);
lean_dec(v_fst_3323_);
lean_dec_ref(v___x_3207_);
lean_dec(v_decl_3206_);
v_a_3345_ = lean_ctor_get(v___x_3338_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3347_ = v___x_3338_;
v_isShared_3348_ = v_isSharedCheck_3359_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3338_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3359_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v_ref_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3354_; 
v_ref_3349_ = lean_ctor_get(v___y_3333_, 5);
v___x_3350_ = lean_io_error_to_string(v_a_3345_);
v___x_3351_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3350_);
v___x_3352_ = l_Lean_MessageData_ofFormat(v___x_3351_);
lean_inc(v_ref_3349_);
if (v_isShared_3327_ == 0)
{
lean_ctor_set(v___x_3326_, 1, v___x_3352_);
lean_ctor_set(v___x_3326_, 0, v_ref_3349_);
v___x_3354_ = v___x_3326_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_ref_3349_);
lean_ctor_set(v_reuseFailAlloc_3358_, 1, v___x_3352_);
v___x_3354_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
lean_object* v___x_3356_; 
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 0, v___x_3354_);
v___x_3356_ = v___x_3347_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v___x_3354_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
}
}
v___jp_3360_:
{
lean_object* v___x_3364_; 
v___x_3364_ = lean_st_ref_get(v___y_3363_);
if (lean_obj_tag(v_exportedInfo_x3f_3361_) == 0)
{
lean_object* v_env_3365_; lean_object* v___x_3366_; 
v_env_3365_ = lean_ctor_get(v___x_3364_, 0);
lean_inc_ref(v_env_3365_);
lean_dec(v___x_3364_);
v___x_3366_ = lean_box(0);
v___y_3329_ = v___y_3363_;
v___y_3330_ = v_env_3365_;
v___y_3331_ = v___y_3362_;
v___y_3332_ = v_exportedInfo_x3f_3361_;
v___y_3333_ = v___y_3362_;
v___y_3334_ = v___y_3363_;
v___y_3335_ = v___x_3366_;
goto v___jp_3328_;
}
else
{
lean_object* v_env_3367_; lean_object* v_val_3368_; uint8_t v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
v_env_3367_ = lean_ctor_get(v___x_3364_, 0);
lean_inc_ref(v_env_3367_);
lean_dec(v___x_3364_);
v_val_3368_ = lean_ctor_get(v_exportedInfo_x3f_3361_, 0);
v___x_3369_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3368_);
v___x_3370_ = lean_box(v___x_3369_);
v___x_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3370_);
v___y_3329_ = v___y_3363_;
v___y_3330_ = v_env_3367_;
v___y_3331_ = v___y_3362_;
v___y_3332_ = v_exportedInfo_x3f_3361_;
v___y_3333_ = v___y_3362_;
v___y_3334_ = v___y_3363_;
v___y_3335_ = v___x_3371_;
goto v___jp_3328_;
}
}
v___jp_3372_:
{
lean_object* v___x_3375_; 
lean_inc(v_fst_3323_);
v___x_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3375_, 0, v_fst_3323_);
v_exportedInfo_x3f_3361_ = v___x_3375_;
v___y_3362_ = v___y_3373_;
v___y_3363_ = v___y_3374_;
goto v___jp_3360_;
}
v___jp_3376_:
{
lean_object* v___x_3379_; 
lean_inc(v_fst_3323_);
v___x_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3379_, 0, v_fst_3323_);
v_exportedInfo_x3f_3361_ = v___x_3379_;
v___y_3362_ = v___y_3377_;
v___y_3363_ = v___y_3378_;
goto v___jp_3360_;
}
v___jp_3380_:
{
if (v___y_3383_ == 0)
{
lean_object* v_options_3384_; uint8_t v_hasTrace_3385_; 
lean_dec(v_exportedInfo_x3f_3213_);
lean_dec_ref(v___x_3210_);
v_options_3384_ = lean_ctor_get(v___y_3381_, 2);
v_hasTrace_3385_ = lean_ctor_get_uint8(v_options_3384_, sizeof(void*)*1);
if (v_hasTrace_3385_ == 0)
{
lean_dec(v_cls_3209_);
v___y_3373_ = v___y_3381_;
v___y_3374_ = v___y_3382_;
goto v___jp_3372_;
}
else
{
lean_object* v_inheritedTraceOptions_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; uint8_t v___x_3389_; 
v_inheritedTraceOptions_3386_ = lean_ctor_get(v___y_3381_, 13);
v___x_3387_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v_cls_3209_);
v___x_3388_ = l_Lean_Name_append(v___x_3387_, v_cls_3209_);
v___x_3389_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3386_, v_options_3384_, v___x_3388_);
lean_dec(v___x_3388_);
if (v___x_3389_ == 0)
{
lean_dec(v_cls_3209_);
v___y_3373_ = v___y_3381_;
v___y_3374_ = v___y_3382_;
goto v___jp_3372_;
}
else
{
lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3390_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__2, &l_Lean_addDecl___lam__8___closed__2_once, _init_l_Lean_addDecl___lam__8___closed__2);
v___x_3391_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3209_, v___x_3390_, v___y_3381_, v___y_3382_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_dec_ref(v___x_3391_);
v___y_3373_ = v___y_3381_;
v___y_3374_ = v___y_3382_;
goto v___jp_3372_;
}
else
{
lean_del_object(v___x_3326_);
lean_dec(v_snd_3324_);
lean_dec(v_fst_3323_);
lean_dec(v_fst_3319_);
lean_dec_ref(v___x_3207_);
lean_dec(v_decl_3206_);
return v___x_3391_;
}
}
}
}
else
{
lean_object* v___x_3392_; lean_object* v_env_3393_; lean_object* v_nextMacroScope_3394_; lean_object* v_ngen_3395_; lean_object* v_auxDeclNGen_3396_; lean_object* v_traceState_3397_; lean_object* v_messages_3398_; lean_object* v_infoState_3399_; lean_object* v_snapshotTasks_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3410_; 
lean_dec(v_cls_3209_);
v___x_3392_ = lean_st_ref_take(v___y_3382_);
v_env_3393_ = lean_ctor_get(v___x_3392_, 0);
v_nextMacroScope_3394_ = lean_ctor_get(v___x_3392_, 1);
v_ngen_3395_ = lean_ctor_get(v___x_3392_, 2);
v_auxDeclNGen_3396_ = lean_ctor_get(v___x_3392_, 3);
v_traceState_3397_ = lean_ctor_get(v___x_3392_, 4);
v_messages_3398_ = lean_ctor_get(v___x_3392_, 6);
v_infoState_3399_ = lean_ctor_get(v___x_3392_, 7);
v_snapshotTasks_3400_ = lean_ctor_get(v___x_3392_, 8);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3410_ == 0)
{
lean_object* v_unused_3411_; 
v_unused_3411_ = lean_ctor_get(v___x_3392_, 5);
lean_dec(v_unused_3411_);
v___x_3402_ = v___x_3392_;
v_isShared_3403_ = v_isSharedCheck_3410_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_snapshotTasks_3400_);
lean_inc(v_infoState_3399_);
lean_inc(v_messages_3398_);
lean_inc(v_traceState_3397_);
lean_inc(v_auxDeclNGen_3396_);
lean_inc(v_ngen_3395_);
lean_inc(v_nextMacroScope_3394_);
lean_inc(v_env_3393_);
lean_dec(v___x_3392_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3410_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3407_; 
v___x_3404_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3324_);
lean_inc(v_fst_3319_);
v___x_3405_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3404_, v_env_3393_, v_fst_3319_, v_snd_3324_);
if (v_isShared_3403_ == 0)
{
lean_ctor_set(v___x_3402_, 5, v___x_3210_);
lean_ctor_set(v___x_3402_, 0, v___x_3405_);
v___x_3407_ = v___x_3402_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v___x_3405_);
lean_ctor_set(v_reuseFailAlloc_3409_, 1, v_nextMacroScope_3394_);
lean_ctor_set(v_reuseFailAlloc_3409_, 2, v_ngen_3395_);
lean_ctor_set(v_reuseFailAlloc_3409_, 3, v_auxDeclNGen_3396_);
lean_ctor_set(v_reuseFailAlloc_3409_, 4, v_traceState_3397_);
lean_ctor_set(v_reuseFailAlloc_3409_, 5, v___x_3210_);
lean_ctor_set(v_reuseFailAlloc_3409_, 6, v_messages_3398_);
lean_ctor_set(v_reuseFailAlloc_3409_, 7, v_infoState_3399_);
lean_ctor_set(v_reuseFailAlloc_3409_, 8, v_snapshotTasks_3400_);
v___x_3407_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
lean_object* v___x_3408_; 
v___x_3408_ = lean_st_ref_set(v___y_3382_, v___x_3407_);
v_exportedInfo_x3f_3361_ = v_exportedInfo_x3f_3213_;
v___y_3362_ = v___y_3381_;
v___y_3363_ = v___y_3382_;
goto v___jp_3360_;
}
}
}
}
v___jp_3412_:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; uint8_t v___x_3417_; 
lean_inc(v_decl_3206_);
v___x_3415_ = l_Lean_Declaration_getTopLevelNames(v_decl_3206_);
v___x_3416_ = ((lean_object*)(l_Lean_addDecl___lam__8___closed__0));
v___x_3417_ = l_List_all___redArg(v___x_3415_, v___x_3416_);
if (v___x_3417_ == 0)
{
lean_dec(v___x_3211_);
if (lean_obj_tag(v_exportedInfo_x3f_3213_) == 0)
{
v___y_3381_ = v___y_3413_;
v___y_3382_ = v___y_3414_;
v___y_3383_ = v___x_3417_;
goto v___jp_3380_;
}
else
{
v___y_3381_ = v___y_3413_;
v___y_3382_ = v___y_3414_;
v___y_3383_ = v___x_3208_;
goto v___jp_3380_;
}
}
else
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v_a_3420_; uint8_t v___x_3421_; 
lean_dec(v_exportedInfo_x3f_3213_);
lean_dec_ref(v___x_3210_);
v___x_3418_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3419_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__2___redArg(v___x_3418_, v___y_3413_);
v_a_3420_ = lean_ctor_get(v___x_3419_, 0);
lean_inc(v_a_3420_);
lean_dec_ref(v___x_3419_);
v___x_3421_ = lean_unbox(v_a_3420_);
lean_dec(v_a_3420_);
if (v___x_3421_ == 0)
{
lean_object* v_options_3422_; uint8_t v_hasTrace_3423_; 
v_options_3422_ = lean_ctor_get(v___y_3413_, 2);
v_hasTrace_3423_ = lean_ctor_get_uint8(v_options_3422_, sizeof(void*)*1);
if (v_hasTrace_3423_ == 0)
{
lean_dec(v_cls_3209_);
v_exportedInfo_x3f_3361_ = v___x_3211_;
v___y_3362_ = v___y_3413_;
v___y_3363_ = v___y_3414_;
goto v___jp_3360_;
}
else
{
lean_object* v_inheritedTraceOptions_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; uint8_t v___x_3427_; 
v_inheritedTraceOptions_3424_ = lean_ctor_get(v___y_3413_, 13);
v___x_3425_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v_cls_3209_);
v___x_3426_ = l_Lean_Name_append(v___x_3425_, v_cls_3209_);
v___x_3427_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3424_, v_options_3422_, v___x_3426_);
lean_dec(v___x_3426_);
if (v___x_3427_ == 0)
{
lean_dec(v_cls_3209_);
v_exportedInfo_x3f_3361_ = v___x_3211_;
v___y_3362_ = v___y_3413_;
v___y_3363_ = v___y_3414_;
goto v___jp_3360_;
}
else
{
lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3428_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__4, &l_Lean_addDecl___lam__8___closed__4_once, _init_l_Lean_addDecl___lam__8___closed__4);
v___x_3429_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3209_, v___x_3428_, v___y_3413_, v___y_3414_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_dec_ref(v___x_3429_);
v_exportedInfo_x3f_3361_ = v___x_3211_;
v___y_3362_ = v___y_3413_;
v___y_3363_ = v___y_3414_;
goto v___jp_3360_;
}
else
{
lean_del_object(v___x_3326_);
lean_dec(v_snd_3324_);
lean_dec(v_fst_3323_);
lean_dec(v_fst_3319_);
lean_dec(v___x_3211_);
lean_dec_ref(v___x_3207_);
lean_dec(v_decl_3206_);
return v___x_3429_;
}
}
}
}
else
{
lean_object* v_options_3430_; uint8_t v_hasTrace_3431_; 
lean_dec(v___x_3211_);
v_options_3430_ = lean_ctor_get(v___y_3413_, 2);
v_hasTrace_3431_ = lean_ctor_get_uint8(v_options_3430_, sizeof(void*)*1);
if (v_hasTrace_3431_ == 0)
{
lean_dec(v_cls_3209_);
v___y_3377_ = v___y_3413_;
v___y_3378_ = v___y_3414_;
goto v___jp_3376_;
}
else
{
lean_object* v_inheritedTraceOptions_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; uint8_t v___x_3435_; 
v_inheritedTraceOptions_3432_ = lean_ctor_get(v___y_3413_, 13);
v___x_3433_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v_cls_3209_);
v___x_3434_ = l_Lean_Name_append(v___x_3433_, v_cls_3209_);
v___x_3435_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3432_, v_options_3430_, v___x_3434_);
lean_dec(v___x_3434_);
if (v___x_3435_ == 0)
{
lean_dec(v_cls_3209_);
v___y_3377_ = v___y_3413_;
v___y_3378_ = v___y_3414_;
goto v___jp_3376_;
}
else
{
lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3436_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__6, &l_Lean_addDecl___lam__8___closed__6_once, _init_l_Lean_addDecl___lam__8___closed__6);
v___x_3437_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3209_, v___x_3436_, v___y_3413_, v___y_3414_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_dec_ref(v___x_3437_);
v___y_3377_ = v___y_3413_;
v___y_3378_ = v___y_3414_;
goto v___jp_3376_;
}
else
{
lean_del_object(v___x_3326_);
lean_dec(v_snd_3324_);
lean_dec(v_fst_3323_);
lean_dec(v_fst_3319_);
lean_dec_ref(v___x_3207_);
lean_dec(v_decl_3206_);
return v___x_3437_;
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
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__13___boxed(lean_object* v_decl_3450_, lean_object* v___x_3451_, lean_object* v___x_3452_, lean_object* v_cls_3453_, lean_object* v___x_3454_, lean_object* v___x_3455_, lean_object* v_____x_3456_, lean_object* v_exportedInfo_x3f_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
uint8_t v___x_62524__boxed_3461_; lean_object* v_res_3462_; 
v___x_62524__boxed_3461_ = lean_unbox(v___x_3452_);
v_res_3462_ = l_Lean_addDecl___lam__13(v_decl_3450_, v___x_3451_, v___x_62524__boxed_3461_, v_cls_3453_, v___x_3454_, v___x_3455_, v_____x_3456_, v_exportedInfo_x3f_3457_, v___y_3458_, v___y_3459_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__10(lean_object* v___f_3463_, uint8_t v_forceExpose_3464_, uint8_t v___x_3465_, lean_object* v___x_3466_, lean_object* v_cls_3467_, lean_object* v_defn_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
lean_object* v_exportedInfo_x3f_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3494_ = lean_st_ref_get(v___y_3470_);
v___x_3495_ = lean_st_ref_get(v___y_3470_);
if (v_forceExpose_3464_ == 0)
{
if (v___x_3465_ == 0)
{
lean_dec(v___x_3495_);
lean_dec(v___x_3494_);
lean_dec(v_cls_3467_);
v_exportedInfo_x3f_3473_ = v___x_3466_;
v___y_3474_ = v___y_3469_;
v___y_3475_ = v___y_3470_;
goto v___jp_3472_;
}
else
{
lean_object* v_env_3496_; lean_object* v_env_3497_; lean_object* v___x_3498_; uint8_t v_isModule_3499_; 
v_env_3496_ = lean_ctor_get(v___x_3494_, 0);
lean_inc_ref(v_env_3496_);
lean_dec(v___x_3494_);
v_env_3497_ = lean_ctor_get(v___x_3495_, 0);
lean_inc_ref(v_env_3497_);
lean_dec(v___x_3495_);
v___x_3498_ = l_Lean_Environment_header(v_env_3496_);
lean_dec_ref(v_env_3496_);
v_isModule_3499_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3498_);
if (v_isModule_3499_ == 0)
{
lean_dec_ref(v_env_3497_);
lean_dec(v_cls_3467_);
v_exportedInfo_x3f_3473_ = v___x_3466_;
v___y_3474_ = v___y_3469_;
v___y_3475_ = v___y_3470_;
goto v___jp_3472_;
}
else
{
uint8_t v_isExporting_3500_; 
v_isExporting_3500_ = lean_ctor_get_uint8(v_env_3497_, sizeof(void*)*8);
lean_dec_ref(v_env_3497_);
if (v_isExporting_3500_ == 0)
{
lean_object* v_options_3501_; uint8_t v_hasTrace_3502_; 
lean_dec(v___x_3466_);
v_options_3501_ = lean_ctor_get(v___y_3469_, 2);
v_hasTrace_3502_ = lean_ctor_get_uint8(v_options_3501_, sizeof(void*)*1);
if (v_hasTrace_3502_ == 0)
{
lean_dec(v_cls_3467_);
v___y_3485_ = v___y_3469_;
v___y_3486_ = v___y_3470_;
goto v___jp_3484_;
}
else
{
lean_object* v_inheritedTraceOptions_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; uint8_t v___x_3506_; 
v_inheritedTraceOptions_3503_ = lean_ctor_get(v___y_3469_, 13);
v___x_3504_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v_cls_3467_);
v___x_3505_ = l_Lean_Name_append(v___x_3504_, v_cls_3467_);
v___x_3506_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3503_, v_options_3501_, v___x_3505_);
lean_dec(v___x_3505_);
if (v___x_3506_ == 0)
{
lean_dec(v_cls_3467_);
v___y_3485_ = v___y_3469_;
v___y_3486_ = v___y_3470_;
goto v___jp_3484_;
}
else
{
lean_object* v_toConstantVal_3507_; lean_object* v_name_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v_toConstantVal_3507_ = lean_ctor_get(v_defn_3468_, 0);
v_name_3508_ = lean_ctor_get(v_toConstantVal_3507_, 0);
v___x_3509_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__1, &l_Lean_addDecl___lam__4___closed__1_once, _init_l_Lean_addDecl___lam__4___closed__1);
lean_inc(v_name_3508_);
v___x_3510_ = l_Lean_MessageData_ofName(v_name_3508_);
v___x_3511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3509_);
lean_ctor_set(v___x_3511_, 1, v___x_3510_);
v___x_3512_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_3513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3513_, 0, v___x_3511_);
lean_ctor_set(v___x_3513_, 1, v___x_3512_);
v___x_3514_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3467_, v___x_3513_, v___y_3469_, v___y_3470_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_dec_ref(v___x_3514_);
v___y_3485_ = v___y_3469_;
v___y_3486_ = v___y_3470_;
goto v___jp_3484_;
}
else
{
lean_dec_ref(v_defn_3468_);
lean_dec_ref(v___f_3463_);
return v___x_3514_;
}
}
}
}
else
{
lean_dec(v_cls_3467_);
v_exportedInfo_x3f_3473_ = v___x_3466_;
v___y_3474_ = v___y_3469_;
v___y_3475_ = v___y_3470_;
goto v___jp_3472_;
}
}
}
}
else
{
lean_dec(v___x_3495_);
lean_dec(v___x_3494_);
lean_dec(v_cls_3467_);
v_exportedInfo_x3f_3473_ = v___x_3466_;
v___y_3474_ = v___y_3469_;
v___y_3475_ = v___y_3470_;
goto v___jp_3472_;
}
v___jp_3472_:
{
lean_object* v_toConstantVal_3476_; lean_object* v_name_3477_; lean_object* v___x_3478_; uint8_t v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v_toConstantVal_3476_ = lean_ctor_get(v_defn_3468_, 0);
v_name_3477_ = lean_ctor_get(v_toConstantVal_3476_, 0);
lean_inc(v_name_3477_);
v___x_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3478_, 0, v_defn_3468_);
v___x_3479_ = 0;
v___x_3480_ = lean_box(v___x_3479_);
v___x_3481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3478_);
lean_ctor_set(v___x_3481_, 1, v___x_3480_);
v___x_3482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3482_, 0, v_name_3477_);
lean_ctor_set(v___x_3482_, 1, v___x_3481_);
lean_inc(v___y_3475_);
lean_inc_ref(v___y_3474_);
v___x_3483_ = lean_apply_5(v___f_3463_, v___x_3482_, v_exportedInfo_x3f_3473_, v___y_3474_, v___y_3475_, lean_box(0));
return v___x_3483_;
}
v___jp_3484_:
{
lean_object* v_toConstantVal_3487_; uint8_t v_safety_3488_; uint8_t v___x_3489_; uint8_t v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
v_toConstantVal_3487_ = lean_ctor_get(v_defn_3468_, 0);
v_safety_3488_ = lean_ctor_get_uint8(v_defn_3468_, sizeof(void*)*4);
v___x_3489_ = 0;
v___x_3490_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3488_, v___x_3489_);
lean_inc_ref(v_toConstantVal_3487_);
v___x_3491_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3491_, 0, v_toConstantVal_3487_);
lean_ctor_set_uint8(v___x_3491_, sizeof(void*)*1, v___x_3490_);
v___x_3492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3491_);
v___x_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3492_);
v_exportedInfo_x3f_3473_ = v___x_3493_;
v___y_3474_ = v___y_3485_;
v___y_3475_ = v___y_3486_;
goto v___jp_3472_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__10___boxed(lean_object* v___f_3515_, lean_object* v_forceExpose_3516_, lean_object* v___x_3517_, lean_object* v___x_3518_, lean_object* v_cls_3519_, lean_object* v_defn_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
uint8_t v_forceExpose_boxed_3524_; uint8_t v___x_62995__boxed_3525_; lean_object* v_res_3526_; 
v_forceExpose_boxed_3524_ = lean_unbox(v_forceExpose_3516_);
v___x_62995__boxed_3525_ = lean_unbox(v___x_3517_);
v_res_3526_ = l_Lean_addDecl___lam__10(v___f_3515_, v_forceExpose_boxed_3524_, v___x_62995__boxed_3525_, v___x_3518_, v_cls_3519_, v_defn_3520_, v___y_3521_, v___y_3522_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3521_);
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__12(lean_object* v_val_3527_, uint8_t v_forceExpose_3528_, lean_object* v___f_3529_, lean_object* v_____r_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v_toConstantVal_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; 
v_toConstantVal_3534_ = lean_ctor_get(v_val_3527_, 0);
lean_inc_ref(v_toConstantVal_3534_);
v___x_3535_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3535_, 0, v_toConstantVal_3534_);
lean_ctor_set_uint8(v___x_3535_, sizeof(void*)*1, v_forceExpose_3528_);
v___x_3536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3535_);
v___x_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3536_);
v___x_3538_ = lean_box(0);
lean_inc(v___y_3532_);
lean_inc_ref(v___y_3531_);
v___x_3539_ = lean_apply_5(v___f_3529_, v___x_3538_, v___x_3537_, v___y_3531_, v___y_3532_, lean_box(0));
return v___x_3539_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__12___boxed(lean_object* v_val_3540_, lean_object* v_forceExpose_3541_, lean_object* v___f_3542_, lean_object* v_____r_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
uint8_t v_forceExpose_boxed_3547_; lean_object* v_res_3548_; 
v_forceExpose_boxed_3547_ = lean_unbox(v_forceExpose_3541_);
v_res_3548_ = l_Lean_addDecl___lam__12(v_val_3540_, v_forceExpose_boxed_3547_, v___f_3542_, v_____r_3543_, v___y_3544_, v___y_3545_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
lean_dec_ref(v_val_3540_);
return v_res_3548_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_addDecl_spec__1(lean_object* v_x_3549_, lean_object* v_x_3550_){
_start:
{
if (lean_obj_tag(v_x_3550_) == 0)
{
return v_x_3549_;
}
else
{
lean_object* v_head_3551_; lean_object* v_tail_3552_; lean_object* v___x_3553_; 
v_head_3551_ = lean_ctor_get(v_x_3550_, 0);
lean_inc(v_head_3551_);
v_tail_3552_ = lean_ctor_get(v_x_3550_, 1);
lean_inc(v_tail_3552_);
lean_dec_ref(v_x_3550_);
v___x_3553_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(v_x_3549_, v_head_3551_);
v_x_3549_ = v___x_3553_;
v_x_3550_ = v_tail_3552_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_addDecl___closed__1(void){
_start:
{
lean_object* v_cls_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v_cls_3558_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_3559_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
v___x_3560_ = l_Lean_Name_append(v___x_3559_, v_cls_3558_);
return v___x_3560_;
}
}
static lean_object* _init_l_Lean_addDecl___closed__3(void){
_start:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3562_ = ((lean_object*)(l_Lean_addDecl___closed__2));
v___x_3563_ = l_Lean_stringToMessageData(v___x_3562_);
return v___x_3563_;
}
}
static lean_object* _init_l_Lean_addDecl___closed__5(void){
_start:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3565_ = ((lean_object*)(l_Lean_addDecl___closed__4));
v___x_3566_ = l_Lean_stringToMessageData(v___x_3565_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object* v_decl_3567_, uint8_t v_forceExpose_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_){
_start:
{
lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v_a_3575_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v_a_3588_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v_a_3601_; lean_object* v___y_3612_; lean_object* v___y_3613_; lean_object* v_a_3614_; lean_object* v_options_3624_; lean_object* v_inheritedTraceOptions_3625_; uint8_t v_hasTrace_3626_; lean_object* v___x_3627_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; uint8_t v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; uint8_t v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3735_; uint8_t v___y_3736_; lean_object* v___y_3737_; lean_object* v_exportedInfo_x3f_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3750_; uint8_t v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3757_; uint8_t v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v_cls_3763_; 
v_options_3624_ = lean_ctor_get(v_a_3569_, 2);
v_inheritedTraceOptions_3625_ = lean_ctor_get(v_a_3569_, 13);
v_hasTrace_3626_ = lean_ctor_get_uint8(v_options_3624_, sizeof(void*)*1);
v___x_3627_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__0_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v_cls_3763_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
if (v_hasTrace_3626_ == 0)
{
lean_object* v___x_3764_; lean_object* v_env_3765_; lean_object* v_nextMacroScope_3766_; lean_object* v_ngen_3767_; lean_object* v_auxDeclNGen_3768_; lean_object* v_traceState_3769_; lean_object* v_messages_3770_; lean_object* v_infoState_3771_; lean_object* v_snapshotTasks_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3962_; 
v___x_3764_ = lean_st_ref_take(v_a_3570_);
v_env_3765_ = lean_ctor_get(v___x_3764_, 0);
v_nextMacroScope_3766_ = lean_ctor_get(v___x_3764_, 1);
v_ngen_3767_ = lean_ctor_get(v___x_3764_, 2);
v_auxDeclNGen_3768_ = lean_ctor_get(v___x_3764_, 3);
v_traceState_3769_ = lean_ctor_get(v___x_3764_, 4);
v_messages_3770_ = lean_ctor_get(v___x_3764_, 6);
v_infoState_3771_ = lean_ctor_get(v___x_3764_, 7);
v_snapshotTasks_3772_ = lean_ctor_get(v___x_3764_, 8);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3962_ == 0)
{
lean_object* v_unused_3963_; 
v_unused_3963_ = lean_ctor_get(v___x_3764_, 5);
lean_dec(v_unused_3963_);
v___x_3774_ = v___x_3764_;
v_isShared_3775_ = v_isSharedCheck_3962_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_snapshotTasks_3772_);
lean_inc(v_infoState_3771_);
lean_inc(v_messages_3770_);
lean_inc(v_traceState_3769_);
lean_inc(v_auxDeclNGen_3768_);
lean_inc(v_ngen_3767_);
lean_inc(v_nextMacroScope_3766_);
lean_inc(v_env_3765_);
lean_dec(v___x_3764_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3962_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3780_; 
lean_inc(v_decl_3567_);
v___x_3776_ = l_Lean_Declaration_getNames(v_decl_3567_);
v___x_3777_ = l_List_foldl___at___00Lean_addDecl_spec__1(v_env_3765_, v___x_3776_);
v___x_3778_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2);
if (v_isShared_3775_ == 0)
{
lean_ctor_set(v___x_3774_, 5, v___x_3778_);
lean_ctor_set(v___x_3774_, 0, v___x_3777_);
v___x_3780_ = v___x_3774_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v___x_3777_);
lean_ctor_set(v_reuseFailAlloc_3961_, 1, v_nextMacroScope_3766_);
lean_ctor_set(v_reuseFailAlloc_3961_, 2, v_ngen_3767_);
lean_ctor_set(v_reuseFailAlloc_3961_, 3, v_auxDeclNGen_3768_);
lean_ctor_set(v_reuseFailAlloc_3961_, 4, v_traceState_3769_);
lean_ctor_set(v_reuseFailAlloc_3961_, 5, v___x_3778_);
lean_ctor_set(v_reuseFailAlloc_3961_, 6, v_messages_3770_);
lean_ctor_set(v_reuseFailAlloc_3961_, 7, v_infoState_3771_);
lean_ctor_set(v_reuseFailAlloc_3961_, 8, v_snapshotTasks_3772_);
v___x_3780_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___y_3784_; uint8_t v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v_fst_3840_; lean_object* v_fst_3841_; uint8_t v_snd_3842_; lean_object* v_exportedInfo_x3f_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3855_; lean_object* v_toConstantVal_3856_; lean_object* v_exportedInfo_x3f_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3864_; lean_object* v_exportedInfo_x3f_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3870_; lean_object* v_toConstantVal_3871_; uint8_t v_safety_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v_defn_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; 
v___x_3781_ = lean_st_ref_set(v_a_3570_, v___x_3780_);
v___x_3782_ = lean_box(0);
switch(lean_obj_tag(v_decl_3567_))
{
case 2:
{
lean_object* v_val_3911_; lean_object* v_exportedInfo_x3f_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___x_3920_; 
v_val_3911_ = lean_ctor_get(v_decl_3567_, 0);
v___x_3920_ = lean_st_ref_get(v_a_3570_);
if (v_forceExpose_3568_ == 0)
{
lean_object* v_env_3921_; lean_object* v___x_3922_; uint8_t v_isModule_3923_; 
v_env_3921_ = lean_ctor_get(v___x_3920_, 0);
lean_inc_ref(v_env_3921_);
lean_dec(v___x_3920_);
v___x_3922_ = l_Lean_Environment_header(v_env_3921_);
lean_dec_ref(v_env_3921_);
v_isModule_3923_ = lean_ctor_get_uint8(v___x_3922_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3922_);
if (v_isModule_3923_ == 0)
{
v_exportedInfo_x3f_3913_ = v___x_3782_;
v___y_3914_ = v_a_3569_;
v___y_3915_ = v_a_3570_;
goto v___jp_3912_;
}
else
{
lean_object* v_toConstantVal_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v_toConstantVal_3924_ = lean_ctor_get(v_val_3911_, 0);
lean_inc_ref(v_toConstantVal_3924_);
v___x_3925_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3925_, 0, v_toConstantVal_3924_);
lean_ctor_set_uint8(v___x_3925_, sizeof(void*)*1, v_hasTrace_3626_);
v___x_3926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3925_);
v___x_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3926_);
v_exportedInfo_x3f_3913_ = v___x_3927_;
v___y_3914_ = v_a_3569_;
v___y_3915_ = v_a_3570_;
goto v___jp_3912_;
}
}
else
{
lean_dec(v___x_3920_);
v_exportedInfo_x3f_3913_ = v___x_3782_;
v___y_3914_ = v_a_3569_;
v___y_3915_ = v_a_3570_;
goto v___jp_3912_;
}
v___jp_3912_:
{
lean_object* v_toConstantVal_3916_; lean_object* v_name_3917_; lean_object* v___x_3918_; uint8_t v___x_3919_; 
v_toConstantVal_3916_ = lean_ctor_get(v_val_3911_, 0);
v_name_3917_ = lean_ctor_get(v_toConstantVal_3916_, 0);
lean_inc_ref(v_val_3911_);
v___x_3918_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3918_, 0, v_val_3911_);
v___x_3919_ = 1;
lean_inc(v_name_3917_);
v_fst_3840_ = v_name_3917_;
v_fst_3841_ = v___x_3918_;
v_snd_3842_ = v___x_3919_;
v_exportedInfo_x3f_3843_ = v_exportedInfo_x3f_3913_;
v___y_3844_ = v___y_3914_;
v___y_3845_ = v___y_3915_;
goto v___jp_3839_;
}
}
case 1:
{
lean_object* v_val_3928_; 
v_val_3928_ = lean_ctor_get(v_decl_3567_, 0);
lean_inc_ref(v_val_3928_);
v_defn_3887_ = v_val_3928_;
v___y_3888_ = v_a_3569_;
v___y_3889_ = v_a_3570_;
goto v___jp_3886_;
}
case 5:
{
lean_object* v_defns_3929_; 
v_defns_3929_ = lean_ctor_get(v_decl_3567_, 0);
if (lean_obj_tag(v_defns_3929_) == 1)
{
lean_object* v_tail_3930_; 
v_tail_3930_ = lean_ctor_get(v_defns_3929_, 1);
if (lean_obj_tag(v_tail_3930_) == 0)
{
lean_object* v_head_3931_; 
v_head_3931_ = lean_ctor_get(v_defns_3929_, 0);
lean_inc(v_head_3931_);
v_defn_3887_ = v_head_3931_;
v___y_3888_ = v_a_3569_;
v___y_3889_ = v_a_3570_;
goto v___jp_3886_;
}
else
{
lean_object* v___x_3932_; 
v___x_3932_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3567_, v_a_3569_, v_a_3570_);
return v___x_3932_;
}
}
else
{
lean_object* v___x_3933_; 
v___x_3933_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3567_, v_a_3569_, v_a_3570_);
return v___x_3933_;
}
}
case 3:
{
lean_object* v_val_3934_; lean_object* v_exportedInfo_x3f_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v_val_3934_ = lean_ctor_get(v_decl_3567_, 0);
v___x_3943_ = lean_st_ref_get(v_a_3570_);
v___x_3944_ = lean_st_ref_get(v_a_3570_);
if (v_forceExpose_3568_ == 0)
{
lean_object* v_env_3945_; lean_object* v_env_3946_; lean_object* v___x_3947_; uint8_t v_isModule_3948_; 
v_env_3945_ = lean_ctor_get(v___x_3943_, 0);
lean_inc_ref(v_env_3945_);
lean_dec(v___x_3943_);
v_env_3946_ = lean_ctor_get(v___x_3944_, 0);
lean_inc_ref(v_env_3946_);
lean_dec(v___x_3944_);
v___x_3947_ = l_Lean_Environment_header(v_env_3945_);
lean_dec_ref(v_env_3945_);
v_isModule_3948_ = lean_ctor_get_uint8(v___x_3947_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3947_);
if (v_isModule_3948_ == 0)
{
lean_dec_ref(v_env_3946_);
v_exportedInfo_x3f_3936_ = v___x_3782_;
v___y_3937_ = v_a_3569_;
v___y_3938_ = v_a_3570_;
goto v___jp_3935_;
}
else
{
uint8_t v_isExporting_3949_; 
v_isExporting_3949_ = lean_ctor_get_uint8(v_env_3946_, sizeof(void*)*8);
lean_dec_ref(v_env_3946_);
if (v_isExporting_3949_ == 0)
{
lean_object* v_toConstantVal_3950_; uint8_t v_isUnsafe_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v_toConstantVal_3950_ = lean_ctor_get(v_val_3934_, 0);
v_isUnsafe_3951_ = lean_ctor_get_uint8(v_val_3934_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_3950_);
v___x_3952_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3952_, 0, v_toConstantVal_3950_);
lean_ctor_set_uint8(v___x_3952_, sizeof(void*)*1, v_isUnsafe_3951_);
v___x_3953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3952_);
v___x_3954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3953_);
v_exportedInfo_x3f_3936_ = v___x_3954_;
v___y_3937_ = v_a_3569_;
v___y_3938_ = v_a_3570_;
goto v___jp_3935_;
}
else
{
v_exportedInfo_x3f_3936_ = v___x_3782_;
v___y_3937_ = v_a_3569_;
v___y_3938_ = v_a_3570_;
goto v___jp_3935_;
}
}
}
else
{
lean_dec(v___x_3944_);
lean_dec(v___x_3943_);
v_exportedInfo_x3f_3936_ = v___x_3782_;
v___y_3937_ = v_a_3569_;
v___y_3938_ = v_a_3570_;
goto v___jp_3935_;
}
v___jp_3935_:
{
lean_object* v_toConstantVal_3939_; lean_object* v_name_3940_; lean_object* v___x_3941_; uint8_t v___x_3942_; 
v_toConstantVal_3939_ = lean_ctor_get(v_val_3934_, 0);
v_name_3940_ = lean_ctor_get(v_toConstantVal_3939_, 0);
lean_inc_ref(v_val_3934_);
v___x_3941_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3941_, 0, v_val_3934_);
v___x_3942_ = 3;
lean_inc(v_name_3940_);
v_fst_3840_ = v_name_3940_;
v_fst_3841_ = v___x_3941_;
v_snd_3842_ = v___x_3942_;
v_exportedInfo_x3f_3843_ = v_exportedInfo_x3f_3936_;
v___y_3844_ = v___y_3937_;
v___y_3845_ = v___y_3938_;
goto v___jp_3839_;
}
}
case 0:
{
lean_object* v_val_3955_; lean_object* v_toConstantVal_3956_; lean_object* v_name_3957_; lean_object* v___x_3958_; uint8_t v___x_3959_; 
v_val_3955_ = lean_ctor_get(v_decl_3567_, 0);
v_toConstantVal_3956_ = lean_ctor_get(v_val_3955_, 0);
v_name_3957_ = lean_ctor_get(v_toConstantVal_3956_, 0);
lean_inc_ref(v_val_3955_);
v___x_3958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3958_, 0, v_val_3955_);
v___x_3959_ = 2;
lean_inc(v_name_3957_);
v_fst_3840_ = v_name_3957_;
v_fst_3841_ = v___x_3958_;
v_snd_3842_ = v___x_3959_;
v_exportedInfo_x3f_3843_ = v___x_3782_;
v___y_3844_ = v_a_3569_;
v___y_3845_ = v_a_3570_;
goto v___jp_3839_;
}
default: 
{
lean_object* v___x_3960_; 
v___x_3960_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3567_, v_a_3569_, v_a_3570_);
return v___x_3960_;
}
}
v___jp_3783_:
{
lean_object* v___x_3790_; lean_object* v___x_3791_; uint8_t v___x_3792_; 
lean_inc(v_decl_3567_);
v___x_3790_ = l_Lean_Declaration_getTopLevelNames(v_decl_3567_);
v___x_3791_ = ((lean_object*)(l_Lean_addDecl___lam__8___closed__0));
v___x_3792_ = l_List_all___redArg(v___x_3790_, v___x_3791_);
if (v___x_3792_ == 0)
{
if (lean_obj_tag(v___y_3787_) == 0)
{
lean_object* v_options_3793_; uint8_t v_hasTrace_3794_; 
v_options_3793_ = lean_ctor_get(v___y_3788_, 2);
v_hasTrace_3794_ = lean_ctor_get_uint8(v_options_3793_, sizeof(void*)*1);
if (v_hasTrace_3794_ == 0)
{
v___y_3757_ = v___y_3784_;
v___y_3758_ = v___y_3785_;
v___y_3759_ = v___y_3786_;
v___y_3760_ = v___y_3788_;
v___y_3761_ = v___y_3789_;
goto v___jp_3756_;
}
else
{
lean_object* v_inheritedTraceOptions_3795_; lean_object* v___x_3796_; uint8_t v___x_3797_; 
v_inheritedTraceOptions_3795_ = lean_ctor_get(v___y_3788_, 13);
v___x_3796_ = lean_obj_once(&l_Lean_addDecl___closed__1, &l_Lean_addDecl___closed__1_once, _init_l_Lean_addDecl___closed__1);
v___x_3797_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3795_, v_options_3793_, v___x_3796_);
if (v___x_3797_ == 0)
{
v___y_3757_ = v___y_3784_;
v___y_3758_ = v___y_3785_;
v___y_3759_ = v___y_3786_;
v___y_3760_ = v___y_3788_;
v___y_3761_ = v___y_3789_;
goto v___jp_3756_;
}
else
{
lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3798_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__2, &l_Lean_addDecl___lam__8___closed__2_once, _init_l_Lean_addDecl___lam__8___closed__2);
v___x_3799_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3763_, v___x_3798_, v___y_3788_, v___y_3789_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_dec_ref(v___x_3799_);
v___y_3757_ = v___y_3784_;
v___y_3758_ = v___y_3785_;
v___y_3759_ = v___y_3786_;
v___y_3760_ = v___y_3788_;
v___y_3761_ = v___y_3789_;
goto v___jp_3756_;
}
else
{
lean_dec_ref(v___y_3786_);
lean_dec(v___y_3784_);
lean_dec(v_decl_3567_);
return v___x_3799_;
}
}
}
}
else
{
lean_object* v___x_3800_; lean_object* v_env_3801_; lean_object* v_nextMacroScope_3802_; lean_object* v_ngen_3803_; lean_object* v_auxDeclNGen_3804_; lean_object* v_traceState_3805_; lean_object* v_messages_3806_; lean_object* v_infoState_3807_; lean_object* v_snapshotTasks_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3819_; 
v___x_3800_ = lean_st_ref_take(v___y_3789_);
v_env_3801_ = lean_ctor_get(v___x_3800_, 0);
v_nextMacroScope_3802_ = lean_ctor_get(v___x_3800_, 1);
v_ngen_3803_ = lean_ctor_get(v___x_3800_, 2);
v_auxDeclNGen_3804_ = lean_ctor_get(v___x_3800_, 3);
v_traceState_3805_ = lean_ctor_get(v___x_3800_, 4);
v_messages_3806_ = lean_ctor_get(v___x_3800_, 6);
v_infoState_3807_ = lean_ctor_get(v___x_3800_, 7);
v_snapshotTasks_3808_ = lean_ctor_get(v___x_3800_, 8);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3800_);
if (v_isSharedCheck_3819_ == 0)
{
lean_object* v_unused_3820_; 
v_unused_3820_ = lean_ctor_get(v___x_3800_, 5);
lean_dec(v_unused_3820_);
v___x_3810_ = v___x_3800_;
v_isShared_3811_ = v_isSharedCheck_3819_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_snapshotTasks_3808_);
lean_inc(v_infoState_3807_);
lean_inc(v_messages_3806_);
lean_inc(v_traceState_3805_);
lean_inc(v_auxDeclNGen_3804_);
lean_inc(v_ngen_3803_);
lean_inc(v_nextMacroScope_3802_);
lean_inc(v_env_3801_);
lean_dec(v___x_3800_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3819_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3816_; 
v___x_3812_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_3813_ = lean_box(v___y_3785_);
lean_inc(v___y_3784_);
v___x_3814_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3812_, v_env_3801_, v___y_3784_, v___x_3813_);
if (v_isShared_3811_ == 0)
{
lean_ctor_set(v___x_3810_, 5, v___x_3778_);
lean_ctor_set(v___x_3810_, 0, v___x_3814_);
v___x_3816_ = v___x_3810_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___x_3814_);
lean_ctor_set(v_reuseFailAlloc_3818_, 1, v_nextMacroScope_3802_);
lean_ctor_set(v_reuseFailAlloc_3818_, 2, v_ngen_3803_);
lean_ctor_set(v_reuseFailAlloc_3818_, 3, v_auxDeclNGen_3804_);
lean_ctor_set(v_reuseFailAlloc_3818_, 4, v_traceState_3805_);
lean_ctor_set(v_reuseFailAlloc_3818_, 5, v___x_3778_);
lean_ctor_set(v_reuseFailAlloc_3818_, 6, v_messages_3806_);
lean_ctor_set(v_reuseFailAlloc_3818_, 7, v_infoState_3807_);
lean_ctor_set(v_reuseFailAlloc_3818_, 8, v_snapshotTasks_3808_);
v___x_3816_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
lean_object* v___x_3817_; 
v___x_3817_ = lean_st_ref_set(v___y_3789_, v___x_3816_);
v___y_3735_ = v___y_3784_;
v___y_3736_ = v___y_3785_;
v___y_3737_ = v___y_3786_;
v_exportedInfo_x3f_3738_ = v___y_3787_;
v___y_3739_ = v___y_3788_;
v___y_3740_ = v___y_3789_;
goto v___jp_3734_;
}
}
}
}
else
{
lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v_a_3823_; uint8_t v___x_3824_; 
lean_dec(v___y_3787_);
v___x_3821_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3822_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__2___redArg(v___x_3821_, v___y_3788_);
v_a_3823_ = lean_ctor_get(v___x_3822_, 0);
lean_inc(v_a_3823_);
lean_dec_ref(v___x_3822_);
v___x_3824_ = lean_unbox(v_a_3823_);
lean_dec(v_a_3823_);
if (v___x_3824_ == 0)
{
lean_object* v_options_3825_; uint8_t v_hasTrace_3826_; 
v_options_3825_ = lean_ctor_get(v___y_3788_, 2);
v_hasTrace_3826_ = lean_ctor_get_uint8(v_options_3825_, sizeof(void*)*1);
if (v_hasTrace_3826_ == 0)
{
v___y_3735_ = v___y_3784_;
v___y_3736_ = v___y_3785_;
v___y_3737_ = v___y_3786_;
v_exportedInfo_x3f_3738_ = v___x_3782_;
v___y_3739_ = v___y_3788_;
v___y_3740_ = v___y_3789_;
goto v___jp_3734_;
}
else
{
lean_object* v_inheritedTraceOptions_3827_; lean_object* v___x_3828_; uint8_t v___x_3829_; 
v_inheritedTraceOptions_3827_ = lean_ctor_get(v___y_3788_, 13);
v___x_3828_ = lean_obj_once(&l_Lean_addDecl___closed__1, &l_Lean_addDecl___closed__1_once, _init_l_Lean_addDecl___closed__1);
v___x_3829_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3827_, v_options_3825_, v___x_3828_);
if (v___x_3829_ == 0)
{
v___y_3735_ = v___y_3784_;
v___y_3736_ = v___y_3785_;
v___y_3737_ = v___y_3786_;
v_exportedInfo_x3f_3738_ = v___x_3782_;
v___y_3739_ = v___y_3788_;
v___y_3740_ = v___y_3789_;
goto v___jp_3734_;
}
else
{
lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___x_3830_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__4, &l_Lean_addDecl___lam__8___closed__4_once, _init_l_Lean_addDecl___lam__8___closed__4);
v___x_3831_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3763_, v___x_3830_, v___y_3788_, v___y_3789_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_dec_ref(v___x_3831_);
v___y_3735_ = v___y_3784_;
v___y_3736_ = v___y_3785_;
v___y_3737_ = v___y_3786_;
v_exportedInfo_x3f_3738_ = v___x_3782_;
v___y_3739_ = v___y_3788_;
v___y_3740_ = v___y_3789_;
goto v___jp_3734_;
}
else
{
lean_dec_ref(v___y_3786_);
lean_dec(v___y_3784_);
lean_dec(v_decl_3567_);
return v___x_3831_;
}
}
}
}
else
{
lean_object* v_options_3832_; uint8_t v_hasTrace_3833_; 
v_options_3832_ = lean_ctor_get(v___y_3788_, 2);
v_hasTrace_3833_ = lean_ctor_get_uint8(v_options_3832_, sizeof(void*)*1);
if (v_hasTrace_3833_ == 0)
{
v___y_3750_ = v___y_3784_;
v___y_3751_ = v___y_3785_;
v___y_3752_ = v___y_3786_;
v___y_3753_ = v___y_3788_;
v___y_3754_ = v___y_3789_;
goto v___jp_3749_;
}
else
{
lean_object* v_inheritedTraceOptions_3834_; lean_object* v___x_3835_; uint8_t v___x_3836_; 
v_inheritedTraceOptions_3834_ = lean_ctor_get(v___y_3788_, 13);
v___x_3835_ = lean_obj_once(&l_Lean_addDecl___closed__1, &l_Lean_addDecl___closed__1_once, _init_l_Lean_addDecl___closed__1);
v___x_3836_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3834_, v_options_3832_, v___x_3835_);
if (v___x_3836_ == 0)
{
v___y_3750_ = v___y_3784_;
v___y_3751_ = v___y_3785_;
v___y_3752_ = v___y_3786_;
v___y_3753_ = v___y_3788_;
v___y_3754_ = v___y_3789_;
goto v___jp_3749_;
}
else
{
lean_object* v___x_3837_; lean_object* v___x_3838_; 
v___x_3837_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__6, &l_Lean_addDecl___lam__8___closed__6_once, _init_l_Lean_addDecl___lam__8___closed__6);
v___x_3838_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3763_, v___x_3837_, v___y_3788_, v___y_3789_);
if (lean_obj_tag(v___x_3838_) == 0)
{
lean_dec_ref(v___x_3838_);
v___y_3750_ = v___y_3784_;
v___y_3751_ = v___y_3785_;
v___y_3752_ = v___y_3786_;
v___y_3753_ = v___y_3788_;
v___y_3754_ = v___y_3789_;
goto v___jp_3749_;
}
else
{
lean_dec_ref(v___y_3786_);
lean_dec(v___y_3784_);
lean_dec(v_decl_3567_);
return v___x_3838_;
}
}
}
}
}
}
v___jp_3839_:
{
lean_object* v___x_3846_; lean_object* v_env_3847_; uint8_t v___x_3848_; 
v___x_3846_ = lean_st_ref_get(v___y_3845_);
v_env_3847_ = lean_ctor_get(v___x_3846_, 0);
lean_inc_ref(v_env_3847_);
lean_dec(v___x_3846_);
v___x_3848_ = l_Lean_Environment_containsOnBranch(v_env_3847_, v_fst_3840_);
lean_dec_ref(v_env_3847_);
if (v___x_3848_ == 0)
{
v___y_3784_ = v_fst_3840_;
v___y_3785_ = v_snd_3842_;
v___y_3786_ = v_fst_3841_;
v___y_3787_ = v_exportedInfo_x3f_3843_;
v___y_3788_ = v___y_3844_;
v___y_3789_ = v___y_3845_;
goto v___jp_3783_;
}
else
{
lean_object* v___x_3849_; lean_object* v_env_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; 
lean_dec(v_exportedInfo_x3f_3843_);
lean_dec_ref(v_fst_3841_);
lean_dec(v_decl_3567_);
v___x_3849_ = lean_st_ref_get(v___y_3845_);
v_env_3850_ = lean_ctor_get(v___x_3849_, 0);
lean_inc_ref(v_env_3850_);
lean_dec(v___x_3849_);
v___x_3851_ = lean_elab_environment_to_kernel_env(v_env_3850_);
v___x_3852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3852_, 0, v___x_3851_);
lean_ctor_set(v___x_3852_, 1, v_fst_3840_);
v___x_3853_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(v___x_3852_, v___y_3844_, v___y_3845_);
return v___x_3853_;
}
}
v___jp_3854_:
{
lean_object* v_name_3860_; lean_object* v___x_3861_; uint8_t v___x_3862_; 
v_name_3860_ = lean_ctor_get(v_toConstantVal_3856_, 0);
lean_inc(v_name_3860_);
lean_dec_ref(v_toConstantVal_3856_);
v___x_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3861_, 0, v___y_3855_);
v___x_3862_ = 0;
v_fst_3840_ = v_name_3860_;
v_fst_3841_ = v___x_3861_;
v_snd_3842_ = v___x_3862_;
v_exportedInfo_x3f_3843_ = v_exportedInfo_x3f_3857_;
v___y_3844_ = v___y_3858_;
v___y_3845_ = v___y_3859_;
goto v___jp_3839_;
}
v___jp_3863_:
{
lean_object* v_toConstantVal_3868_; 
v_toConstantVal_3868_ = lean_ctor_get(v___y_3864_, 0);
lean_inc_ref(v_toConstantVal_3868_);
v___y_3855_ = v___y_3864_;
v_toConstantVal_3856_ = v_toConstantVal_3868_;
v_exportedInfo_x3f_3857_ = v_exportedInfo_x3f_3865_;
v___y_3858_ = v___y_3866_;
v___y_3859_ = v___y_3867_;
goto v___jp_3854_;
}
v___jp_3869_:
{
uint8_t v___x_3875_; uint8_t v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3875_ = 0;
v___x_3876_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3872_, v___x_3875_);
lean_inc_ref(v_toConstantVal_3871_);
v___x_3877_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3877_, 0, v_toConstantVal_3871_);
lean_ctor_set_uint8(v___x_3877_, sizeof(void*)*1, v___x_3876_);
v___x_3878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3878_, 0, v___x_3877_);
v___x_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3878_);
v___y_3855_ = v___y_3870_;
v_toConstantVal_3856_ = v_toConstantVal_3871_;
v_exportedInfo_x3f_3857_ = v___x_3879_;
v___y_3858_ = v___y_3873_;
v___y_3859_ = v___y_3874_;
goto v___jp_3854_;
}
v___jp_3880_:
{
lean_object* v_toConstantVal_3884_; uint8_t v_safety_3885_; 
v_toConstantVal_3884_ = lean_ctor_get(v___y_3881_, 0);
lean_inc_ref(v_toConstantVal_3884_);
v_safety_3885_ = lean_ctor_get_uint8(v___y_3881_, sizeof(void*)*4);
v___y_3870_ = v___y_3881_;
v_toConstantVal_3871_ = v_toConstantVal_3884_;
v_safety_3872_ = v_safety_3885_;
v___y_3873_ = v___y_3882_;
v___y_3874_ = v___y_3883_;
goto v___jp_3869_;
}
v___jp_3886_:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3890_ = lean_st_ref_get(v___y_3889_);
v___x_3891_ = lean_st_ref_get(v___y_3889_);
if (v_forceExpose_3568_ == 0)
{
lean_object* v_env_3892_; lean_object* v_env_3893_; lean_object* v___x_3894_; uint8_t v_isModule_3895_; 
v_env_3892_ = lean_ctor_get(v___x_3890_, 0);
lean_inc_ref(v_env_3892_);
lean_dec(v___x_3890_);
v_env_3893_ = lean_ctor_get(v___x_3891_, 0);
lean_inc_ref(v_env_3893_);
lean_dec(v___x_3891_);
v___x_3894_ = l_Lean_Environment_header(v_env_3892_);
lean_dec_ref(v_env_3892_);
v_isModule_3895_ = lean_ctor_get_uint8(v___x_3894_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3894_);
if (v_isModule_3895_ == 0)
{
lean_dec_ref(v_env_3893_);
v___y_3864_ = v_defn_3887_;
v_exportedInfo_x3f_3865_ = v___x_3782_;
v___y_3866_ = v___y_3888_;
v___y_3867_ = v___y_3889_;
goto v___jp_3863_;
}
else
{
uint8_t v_isExporting_3896_; 
v_isExporting_3896_ = lean_ctor_get_uint8(v_env_3893_, sizeof(void*)*8);
lean_dec_ref(v_env_3893_);
if (v_isExporting_3896_ == 0)
{
lean_object* v_options_3897_; uint8_t v_hasTrace_3898_; 
v_options_3897_ = lean_ctor_get(v___y_3888_, 2);
v_hasTrace_3898_ = lean_ctor_get_uint8(v_options_3897_, sizeof(void*)*1);
if (v_hasTrace_3898_ == 0)
{
v___y_3881_ = v_defn_3887_;
v___y_3882_ = v___y_3888_;
v___y_3883_ = v___y_3889_;
goto v___jp_3880_;
}
else
{
lean_object* v_inheritedTraceOptions_3899_; lean_object* v___x_3900_; uint8_t v___x_3901_; 
v_inheritedTraceOptions_3899_ = lean_ctor_get(v___y_3888_, 13);
v___x_3900_ = lean_obj_once(&l_Lean_addDecl___closed__1, &l_Lean_addDecl___closed__1_once, _init_l_Lean_addDecl___closed__1);
v___x_3901_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3899_, v_options_3897_, v___x_3900_);
if (v___x_3901_ == 0)
{
v___y_3881_ = v_defn_3887_;
v___y_3882_ = v___y_3888_;
v___y_3883_ = v___y_3889_;
goto v___jp_3880_;
}
else
{
lean_object* v_toConstantVal_3902_; uint8_t v_safety_3903_; lean_object* v_name_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
v_toConstantVal_3902_ = lean_ctor_get(v_defn_3887_, 0);
lean_inc_ref(v_toConstantVal_3902_);
v_safety_3903_ = lean_ctor_get_uint8(v_defn_3887_, sizeof(void*)*4);
v_name_3904_ = lean_ctor_get(v_toConstantVal_3902_, 0);
v___x_3905_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__1, &l_Lean_addDecl___lam__4___closed__1_once, _init_l_Lean_addDecl___lam__4___closed__1);
lean_inc(v_name_3904_);
v___x_3906_ = l_Lean_MessageData_ofName(v_name_3904_);
v___x_3907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3905_);
lean_ctor_set(v___x_3907_, 1, v___x_3906_);
v___x_3908_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_3909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3907_);
lean_ctor_set(v___x_3909_, 1, v___x_3908_);
v___x_3910_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3763_, v___x_3909_, v___y_3888_, v___y_3889_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_dec_ref(v___x_3910_);
v___y_3870_ = v_defn_3887_;
v_toConstantVal_3871_ = v_toConstantVal_3902_;
v_safety_3872_ = v_safety_3903_;
v___y_3873_ = v___y_3888_;
v___y_3874_ = v___y_3889_;
goto v___jp_3869_;
}
else
{
lean_dec_ref(v_toConstantVal_3902_);
lean_dec_ref(v_defn_3887_);
lean_dec(v_decl_3567_);
return v___x_3910_;
}
}
}
}
else
{
v___y_3864_ = v_defn_3887_;
v_exportedInfo_x3f_3865_ = v___x_3782_;
v___y_3866_ = v___y_3888_;
v___y_3867_ = v___y_3889_;
goto v___jp_3863_;
}
}
}
else
{
lean_dec(v___x_3891_);
lean_dec(v___x_3890_);
v___y_3864_ = v_defn_3887_;
v_exportedInfo_x3f_3865_ = v___x_3782_;
v___y_3866_ = v___y_3888_;
v___y_3867_ = v___y_3889_;
goto v___jp_3863_;
}
}
}
}
}
else
{
lean_object* v___f_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; uint8_t v___x_3967_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v_a_3971_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v_a_4017_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; uint8_t v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; 
lean_inc(v_decl_3567_);
v___f_3964_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__1___boxed), 5, 1);
lean_closure_set(v___f_3964_, 0, v_decl_3567_);
v___x_3965_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_3966_ = lean_obj_once(&l_Lean_addDecl___closed__1, &l_Lean_addDecl___closed__1_once, _init_l_Lean_addDecl___closed__1);
v___x_3967_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3625_, v_options_3624_, v___x_3966_);
if (v___x_3967_ == 0)
{
lean_object* v___x_4267_; uint8_t v___x_4268_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; uint8_t v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4374_; lean_object* v___y_4375_; uint8_t v___y_4376_; lean_object* v_exportedInfo_x3f_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4389_; lean_object* v___y_4390_; uint8_t v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4396_; lean_object* v___y_4397_; uint8_t v___y_4398_; lean_object* v___y_4399_; lean_object* v___y_4400_; 
v___x_4267_ = l_Lean_trace_profiler;
v___x_4268_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3624_, v___x_4267_);
if (v___x_4268_ == 0)
{
lean_object* v___x_4402_; lean_object* v_env_4403_; lean_object* v_nextMacroScope_4404_; lean_object* v_ngen_4405_; lean_object* v_auxDeclNGen_4406_; lean_object* v_traceState_4407_; lean_object* v_messages_4408_; lean_object* v_infoState_4409_; lean_object* v_snapshotTasks_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4647_; 
lean_dec_ref(v___f_3964_);
v___x_4402_ = lean_st_ref_take(v_a_3570_);
v_env_4403_ = lean_ctor_get(v___x_4402_, 0);
v_nextMacroScope_4404_ = lean_ctor_get(v___x_4402_, 1);
v_ngen_4405_ = lean_ctor_get(v___x_4402_, 2);
v_auxDeclNGen_4406_ = lean_ctor_get(v___x_4402_, 3);
v_traceState_4407_ = lean_ctor_get(v___x_4402_, 4);
v_messages_4408_ = lean_ctor_get(v___x_4402_, 6);
v_infoState_4409_ = lean_ctor_get(v___x_4402_, 7);
v_snapshotTasks_4410_ = lean_ctor_get(v___x_4402_, 8);
v_isSharedCheck_4647_ = !lean_is_exclusive(v___x_4402_);
if (v_isSharedCheck_4647_ == 0)
{
lean_object* v_unused_4648_; 
v_unused_4648_ = lean_ctor_get(v___x_4402_, 5);
lean_dec(v_unused_4648_);
v___x_4412_ = v___x_4402_;
v_isShared_4413_ = v_isSharedCheck_4647_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_snapshotTasks_4410_);
lean_inc(v_infoState_4409_);
lean_inc(v_messages_4408_);
lean_inc(v_traceState_4407_);
lean_inc(v_auxDeclNGen_4406_);
lean_inc(v_ngen_4405_);
lean_inc(v_nextMacroScope_4404_);
lean_inc(v_env_4403_);
lean_dec(v___x_4402_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4647_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___y_4418_; lean_object* v___y_4419_; lean_object* v___y_4420_; uint8_t v___y_4421_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v___x_4446_; 
lean_inc(v_decl_3567_);
v___x_4414_ = l_Lean_Declaration_getNames(v_decl_3567_);
v___x_4415_ = l_List_foldl___at___00Lean_addDecl_spec__1(v_env_4403_, v___x_4414_);
v___x_4416_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2);
if (v_isShared_4413_ == 0)
{
lean_ctor_set(v___x_4412_, 5, v___x_4416_);
lean_ctor_set(v___x_4412_, 0, v___x_4415_);
v___x_4446_ = v___x_4412_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v___x_4415_);
lean_ctor_set(v_reuseFailAlloc_4646_, 1, v_nextMacroScope_4404_);
lean_ctor_set(v_reuseFailAlloc_4646_, 2, v_ngen_4405_);
lean_ctor_set(v_reuseFailAlloc_4646_, 3, v_auxDeclNGen_4406_);
lean_ctor_set(v_reuseFailAlloc_4646_, 4, v_traceState_4407_);
lean_ctor_set(v_reuseFailAlloc_4646_, 5, v___x_4416_);
lean_ctor_set(v_reuseFailAlloc_4646_, 6, v_messages_4408_);
lean_ctor_set(v_reuseFailAlloc_4646_, 7, v_infoState_4409_);
lean_ctor_set(v_reuseFailAlloc_4646_, 8, v_snapshotTasks_4410_);
v___x_4446_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4445_;
}
v___jp_4417_:
{
lean_object* v___x_4424_; lean_object* v_env_4425_; lean_object* v_nextMacroScope_4426_; lean_object* v_ngen_4427_; lean_object* v_auxDeclNGen_4428_; lean_object* v_traceState_4429_; lean_object* v_messages_4430_; lean_object* v_infoState_4431_; lean_object* v_snapshotTasks_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4443_; 
v___x_4424_ = lean_st_ref_take(v___y_4423_);
v_env_4425_ = lean_ctor_get(v___x_4424_, 0);
v_nextMacroScope_4426_ = lean_ctor_get(v___x_4424_, 1);
v_ngen_4427_ = lean_ctor_get(v___x_4424_, 2);
v_auxDeclNGen_4428_ = lean_ctor_get(v___x_4424_, 3);
v_traceState_4429_ = lean_ctor_get(v___x_4424_, 4);
v_messages_4430_ = lean_ctor_get(v___x_4424_, 6);
v_infoState_4431_ = lean_ctor_get(v___x_4424_, 7);
v_snapshotTasks_4432_ = lean_ctor_get(v___x_4424_, 8);
v_isSharedCheck_4443_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4443_ == 0)
{
lean_object* v_unused_4444_; 
v_unused_4444_ = lean_ctor_get(v___x_4424_, 5);
lean_dec(v_unused_4444_);
v___x_4434_ = v___x_4424_;
v_isShared_4435_ = v_isSharedCheck_4443_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_snapshotTasks_4432_);
lean_inc(v_infoState_4431_);
lean_inc(v_messages_4430_);
lean_inc(v_traceState_4429_);
lean_inc(v_auxDeclNGen_4428_);
lean_inc(v_ngen_4427_);
lean_inc(v_nextMacroScope_4426_);
lean_inc(v_env_4425_);
lean_dec(v___x_4424_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4443_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4440_; 
v___x_4436_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4437_ = lean_box(v___y_4421_);
lean_inc(v___y_4419_);
v___x_4438_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4436_, v_env_4425_, v___y_4419_, v___x_4437_);
if (v_isShared_4435_ == 0)
{
lean_ctor_set(v___x_4434_, 5, v___x_4416_);
lean_ctor_set(v___x_4434_, 0, v___x_4438_);
v___x_4440_ = v___x_4434_;
goto v_reusejp_4439_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v___x_4438_);
lean_ctor_set(v_reuseFailAlloc_4442_, 1, v_nextMacroScope_4426_);
lean_ctor_set(v_reuseFailAlloc_4442_, 2, v_ngen_4427_);
lean_ctor_set(v_reuseFailAlloc_4442_, 3, v_auxDeclNGen_4428_);
lean_ctor_set(v_reuseFailAlloc_4442_, 4, v_traceState_4429_);
lean_ctor_set(v_reuseFailAlloc_4442_, 5, v___x_4416_);
lean_ctor_set(v_reuseFailAlloc_4442_, 6, v_messages_4430_);
lean_ctor_set(v_reuseFailAlloc_4442_, 7, v_infoState_4431_);
lean_ctor_set(v_reuseFailAlloc_4442_, 8, v_snapshotTasks_4432_);
v___x_4440_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4439_;
}
v_reusejp_4439_:
{
lean_object* v___x_4441_; 
v___x_4441_ = lean_st_ref_set(v___y_4423_, v___x_4440_);
v___y_4374_ = v___y_4419_;
v___y_4375_ = v___y_4420_;
v___y_4376_ = v___y_4421_;
v_exportedInfo_x3f_4377_ = v___y_4418_;
v___y_4378_ = v___y_4422_;
v___y_4379_ = v___y_4423_;
goto v___jp_4373_;
}
}
}
v_reusejp_4445_:
{
lean_object* v___x_4447_; lean_object* v___y_4449_; lean_object* v_options_4450_; lean_object* v_inheritedTraceOptions_4451_; lean_object* v___y_4452_; lean_object* v___x_4458_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; uint8_t v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v_fst_4492_; lean_object* v_fst_4493_; uint8_t v_snd_4494_; lean_object* v_exportedInfo_x3f_4495_; lean_object* v___y_4496_; lean_object* v___y_4497_; lean_object* v___y_4507_; lean_object* v_toConstantVal_4508_; lean_object* v_exportedInfo_x3f_4509_; lean_object* v___y_4510_; lean_object* v___y_4511_; lean_object* v___y_4516_; lean_object* v_toConstantVal_4517_; uint8_t v_safety_4518_; lean_object* v___y_4519_; lean_object* v___y_4520_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4550_; lean_object* v_exportedInfo_x3f_4551_; lean_object* v___y_4552_; lean_object* v___y_4553_; lean_object* v___y_4556_; lean_object* v___y_4557_; lean_object* v___y_4558_; lean_object* v___y_4559_; lean_object* v___y_4560_; lean_object* v_defn_4565_; lean_object* v___y_4566_; lean_object* v___y_4567_; 
v___x_4447_ = lean_st_ref_set(v_a_3570_, v___x_4446_);
v___x_4458_ = lean_box(0);
switch(lean_obj_tag(v_decl_3567_))
{
case 2:
{
lean_object* v_val_4574_; lean_object* v_exportedInfo_x3f_4576_; lean_object* v___y_4577_; lean_object* v___y_4578_; lean_object* v___y_4584_; lean_object* v___y_4585_; lean_object* v___x_4590_; lean_object* v_env_4591_; 
v_val_4574_ = lean_ctor_get(v_decl_3567_, 0);
v___x_4590_ = lean_st_ref_get(v_a_3570_);
v_env_4591_ = lean_ctor_get(v___x_4590_, 0);
lean_inc_ref(v_env_4591_);
lean_dec(v___x_4590_);
if (v_forceExpose_3568_ == 0)
{
goto v___jp_4592_;
}
else
{
if (v___x_4268_ == 0)
{
lean_dec_ref(v_env_4591_);
v_exportedInfo_x3f_4576_ = v___x_4458_;
v___y_4577_ = v_a_3569_;
v___y_4578_ = v_a_3570_;
goto v___jp_4575_;
}
else
{
goto v___jp_4592_;
}
}
v___jp_4575_:
{
lean_object* v_toConstantVal_4579_; lean_object* v_name_4580_; lean_object* v___x_4581_; uint8_t v___x_4582_; 
v_toConstantVal_4579_ = lean_ctor_get(v_val_4574_, 0);
v_name_4580_ = lean_ctor_get(v_toConstantVal_4579_, 0);
lean_inc_ref(v_val_4574_);
v___x_4581_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4581_, 0, v_val_4574_);
v___x_4582_ = 1;
lean_inc(v_name_4580_);
v_fst_4492_ = v_name_4580_;
v_fst_4493_ = v___x_4581_;
v_snd_4494_ = v___x_4582_;
v_exportedInfo_x3f_4495_ = v_exportedInfo_x3f_4576_;
v___y_4496_ = v___y_4577_;
v___y_4497_ = v___y_4578_;
goto v___jp_4491_;
}
v___jp_4583_:
{
lean_object* v_toConstantVal_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; 
v_toConstantVal_4586_ = lean_ctor_get(v_val_4574_, 0);
lean_inc_ref(v_toConstantVal_4586_);
v___x_4587_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4587_, 0, v_toConstantVal_4586_);
lean_ctor_set_uint8(v___x_4587_, sizeof(void*)*1, v___x_4268_);
v___x_4588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4588_, 0, v___x_4587_);
v___x_4589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4588_);
v_exportedInfo_x3f_4576_ = v___x_4589_;
v___y_4577_ = v___y_4584_;
v___y_4578_ = v___y_4585_;
goto v___jp_4575_;
}
v___jp_4592_:
{
lean_object* v___x_4593_; uint8_t v_isModule_4594_; 
v___x_4593_ = l_Lean_Environment_header(v_env_4591_);
lean_dec_ref(v_env_4591_);
v_isModule_4594_ = lean_ctor_get_uint8(v___x_4593_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4593_);
if (v_isModule_4594_ == 0)
{
v_exportedInfo_x3f_4576_ = v___x_4458_;
v___y_4577_ = v_a_3569_;
v___y_4578_ = v_a_3570_;
goto v___jp_4575_;
}
else
{
if (v___x_3967_ == 0)
{
v___y_4584_ = v_a_3569_;
v___y_4585_ = v_a_3570_;
goto v___jp_4583_;
}
else
{
lean_object* v_toConstantVal_4595_; lean_object* v_name_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; 
v_toConstantVal_4595_ = lean_ctor_get(v_val_4574_, 0);
v_name_4596_ = lean_ctor_get(v_toConstantVal_4595_, 0);
v___x_4597_ = lean_obj_once(&l_Lean_addDecl___closed__5, &l_Lean_addDecl___closed__5_once, _init_l_Lean_addDecl___closed__5);
lean_inc(v_name_4596_);
v___x_4598_ = l_Lean_MessageData_ofName(v_name_4596_);
v___x_4599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4599_, 0, v___x_4597_);
lean_ctor_set(v___x_4599_, 1, v___x_4598_);
v___x_4600_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_4601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4601_, 0, v___x_4599_);
lean_ctor_set(v___x_4601_, 1, v___x_4600_);
v___x_4602_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3763_, v___x_4601_, v_a_3569_, v_a_3570_);
if (lean_obj_tag(v___x_4602_) == 0)
{
lean_dec_ref(v___x_4602_);
v___y_4584_ = v_a_3569_;
v___y_4585_ = v_a_3570_;
goto v___jp_4583_;
}
else
{
lean_dec_ref(v_decl_3567_);
return v___x_4602_;
}
}
}
}
}
case 1:
{
lean_object* v_val_4603_; 
v_val_4603_ = lean_ctor_get(v_decl_3567_, 0);
lean_inc_ref(v_val_4603_);
v_defn_4565_ = v_val_4603_;
v___y_4566_ = v_a_3569_;
v___y_4567_ = v_a_3570_;
goto v___jp_4564_;
}
case 5:
{
lean_object* v_defns_4604_; 
v_defns_4604_ = lean_ctor_get(v_decl_3567_, 0);
if (lean_obj_tag(v_defns_4604_) == 1)
{
lean_object* v_tail_4605_; 
v_tail_4605_ = lean_ctor_get(v_defns_4604_, 1);
if (lean_obj_tag(v_tail_4605_) == 0)
{
lean_object* v_head_4606_; 
v_head_4606_ = lean_ctor_get(v_defns_4604_, 0);
lean_inc(v_head_4606_);
v_defn_4565_ = v_head_4606_;
v___y_4566_ = v_a_3569_;
v___y_4567_ = v_a_3570_;
goto v___jp_4564_;
}
else
{
v___y_4449_ = v_a_3569_;
v_options_4450_ = v_options_3624_;
v_inheritedTraceOptions_4451_ = v_inheritedTraceOptions_3625_;
v___y_4452_ = v_a_3570_;
goto v___jp_4448_;
}
}
else
{
v___y_4449_ = v_a_3569_;
v_options_4450_ = v_options_3624_;
v_inheritedTraceOptions_4451_ = v_inheritedTraceOptions_3625_;
v___y_4452_ = v_a_3570_;
goto v___jp_4448_;
}
}
case 3:
{
lean_object* v_val_4607_; lean_object* v_exportedInfo_x3f_4609_; lean_object* v___y_4610_; lean_object* v___y_4611_; lean_object* v___y_4617_; lean_object* v___y_4618_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v_env_4635_; lean_object* v_env_4636_; 
v_val_4607_ = lean_ctor_get(v_decl_3567_, 0);
v___x_4624_ = lean_st_ref_get(v_a_3570_);
v___x_4625_ = lean_st_ref_get(v_a_3570_);
v_env_4635_ = lean_ctor_get(v___x_4624_, 0);
lean_inc_ref(v_env_4635_);
lean_dec(v___x_4624_);
v_env_4636_ = lean_ctor_get(v___x_4625_, 0);
lean_inc_ref(v_env_4636_);
lean_dec(v___x_4625_);
if (v_forceExpose_3568_ == 0)
{
goto v___jp_4637_;
}
else
{
if (v___x_4268_ == 0)
{
lean_dec_ref(v_env_4636_);
lean_dec_ref(v_env_4635_);
v_exportedInfo_x3f_4609_ = v___x_4458_;
v___y_4610_ = v_a_3569_;
v___y_4611_ = v_a_3570_;
goto v___jp_4608_;
}
else
{
goto v___jp_4637_;
}
}
v___jp_4608_:
{
lean_object* v_toConstantVal_4612_; lean_object* v_name_4613_; lean_object* v___x_4614_; uint8_t v___x_4615_; 
v_toConstantVal_4612_ = lean_ctor_get(v_val_4607_, 0);
v_name_4613_ = lean_ctor_get(v_toConstantVal_4612_, 0);
lean_inc_ref(v_val_4607_);
v___x_4614_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4614_, 0, v_val_4607_);
v___x_4615_ = 3;
lean_inc(v_name_4613_);
v_fst_4492_ = v_name_4613_;
v_fst_4493_ = v___x_4614_;
v_snd_4494_ = v___x_4615_;
v_exportedInfo_x3f_4495_ = v_exportedInfo_x3f_4609_;
v___y_4496_ = v___y_4610_;
v___y_4497_ = v___y_4611_;
goto v___jp_4491_;
}
v___jp_4616_:
{
lean_object* v_toConstantVal_4619_; uint8_t v_isUnsafe_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; 
v_toConstantVal_4619_ = lean_ctor_get(v_val_4607_, 0);
v_isUnsafe_4620_ = lean_ctor_get_uint8(v_val_4607_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4619_);
v___x_4621_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4621_, 0, v_toConstantVal_4619_);
lean_ctor_set_uint8(v___x_4621_, sizeof(void*)*1, v_isUnsafe_4620_);
v___x_4622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4622_, 0, v___x_4621_);
v___x_4623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4623_, 0, v___x_4622_);
v_exportedInfo_x3f_4609_ = v___x_4623_;
v___y_4610_ = v___y_4617_;
v___y_4611_ = v___y_4618_;
goto v___jp_4608_;
}
v___jp_4626_:
{
if (v___x_3967_ == 0)
{
v___y_4617_ = v_a_3569_;
v___y_4618_ = v_a_3570_;
goto v___jp_4616_;
}
else
{
lean_object* v_toConstantVal_4627_; lean_object* v_name_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; 
v_toConstantVal_4627_ = lean_ctor_get(v_val_4607_, 0);
v_name_4628_ = lean_ctor_get(v_toConstantVal_4627_, 0);
v___x_4629_ = lean_obj_once(&l_Lean_addDecl___closed__3, &l_Lean_addDecl___closed__3_once, _init_l_Lean_addDecl___closed__3);
lean_inc(v_name_4628_);
v___x_4630_ = l_Lean_MessageData_ofName(v_name_4628_);
v___x_4631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4631_, 0, v___x_4629_);
lean_ctor_set(v___x_4631_, 1, v___x_4630_);
v___x_4632_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_4633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4633_, 0, v___x_4631_);
lean_ctor_set(v___x_4633_, 1, v___x_4632_);
v___x_4634_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3763_, v___x_4633_, v_a_3569_, v_a_3570_);
if (lean_obj_tag(v___x_4634_) == 0)
{
lean_dec_ref(v___x_4634_);
v___y_4617_ = v_a_3569_;
v___y_4618_ = v_a_3570_;
goto v___jp_4616_;
}
else
{
lean_dec_ref(v_decl_3567_);
return v___x_4634_;
}
}
}
v___jp_4637_:
{
lean_object* v___x_4638_; uint8_t v_isModule_4639_; 
v___x_4638_ = l_Lean_Environment_header(v_env_4635_);
lean_dec_ref(v_env_4635_);
v_isModule_4639_ = lean_ctor_get_uint8(v___x_4638_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4638_);
if (v_isModule_4639_ == 0)
{
lean_dec_ref(v_env_4636_);
v_exportedInfo_x3f_4609_ = v___x_4458_;
v___y_4610_ = v_a_3569_;
v___y_4611_ = v_a_3570_;
goto v___jp_4608_;
}
else
{
uint8_t v_isExporting_4640_; 
v_isExporting_4640_ = lean_ctor_get_uint8(v_env_4636_, sizeof(void*)*8);
lean_dec_ref(v_env_4636_);
if (v_isExporting_4640_ == 0)
{
goto v___jp_4626_;
}
else
{
if (v___x_4268_ == 0)
{
v_exportedInfo_x3f_4609_ = v___x_4458_;
v___y_4610_ = v_a_3569_;
v___y_4611_ = v_a_3570_;
goto v___jp_4608_;
}
else
{
goto v___jp_4626_;
}
}
}
}
}
case 0:
{
lean_object* v_val_4641_; lean_object* v_toConstantVal_4642_; lean_object* v_name_4643_; lean_object* v___x_4644_; uint8_t v___x_4645_; 
v_val_4641_ = lean_ctor_get(v_decl_3567_, 0);
v_toConstantVal_4642_ = lean_ctor_get(v_val_4641_, 0);
v_name_4643_ = lean_ctor_get(v_toConstantVal_4642_, 0);
lean_inc_ref(v_val_4641_);
v___x_4644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4644_, 0, v_val_4641_);
v___x_4645_ = 2;
lean_inc(v_name_4643_);
v_fst_4492_ = v_name_4643_;
v_fst_4493_ = v___x_4644_;
v_snd_4494_ = v___x_4645_;
v_exportedInfo_x3f_4495_ = v___x_4458_;
v___y_4496_ = v_a_3569_;
v___y_4497_ = v_a_3570_;
goto v___jp_4491_;
}
default: 
{
v___y_4449_ = v_a_3569_;
v_options_4450_ = v_options_3624_;
v_inheritedTraceOptions_4451_ = v_inheritedTraceOptions_3625_;
v___y_4452_ = v_a_3570_;
goto v___jp_4448_;
}
}
v___jp_4448_:
{
uint8_t v___x_4453_; 
v___x_4453_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4451_, v_options_4450_, v___x_3966_);
if (v___x_4453_ == 0)
{
lean_object* v___x_4454_; 
v___x_4454_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3567_, v___y_4449_, v___y_4452_);
return v___x_4454_;
}
else
{
lean_object* v___x_4455_; lean_object* v___x_4456_; 
v___x_4455_ = lean_obj_once(&l_Lean_addDecl___lam__3___closed__1, &l_Lean_addDecl___lam__3___closed__1_once, _init_l_Lean_addDecl___lam__3___closed__1);
v___x_4456_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3763_, v___x_4455_, v___y_4449_, v___y_4452_);
if (lean_obj_tag(v___x_4456_) == 0)
{
lean_object* v___x_4457_; 
lean_dec_ref(v___x_4456_);
v___x_4457_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3567_, v___y_4449_, v___y_4452_);
return v___x_4457_;
}
else
{
lean_dec(v_decl_3567_);
return v___x_4456_;
}
}
}
v___jp_4459_:
{
lean_object* v___x_4466_; lean_object* v___x_4467_; uint8_t v___x_4468_; 
lean_inc(v_decl_3567_);
v___x_4466_ = l_Lean_Declaration_getTopLevelNames(v_decl_3567_);
v___x_4467_ = ((lean_object*)(l_Lean_addDecl___lam__8___closed__0));
v___x_4468_ = l_List_all___redArg(v___x_4466_, v___x_4467_);
if (v___x_4468_ == 0)
{
if (lean_obj_tag(v___y_4460_) == 0)
{
if (v___x_4268_ == 0)
{
lean_object* v_options_4469_; uint8_t v_hasTrace_4470_; 
v_options_4469_ = lean_ctor_get(v___y_4464_, 2);
v_hasTrace_4470_ = lean_ctor_get_uint8(v_options_4469_, sizeof(void*)*1);
if (v_hasTrace_4470_ == 0)
{
v___y_4389_ = v___y_4461_;
v___y_4390_ = v___y_4462_;
v___y_4391_ = v___y_4463_;
v___y_4392_ = v___y_4464_;
v___y_4393_ = v___y_4465_;
goto v___jp_4388_;
}
else
{
lean_object* v_inheritedTraceOptions_4471_; uint8_t v___x_4472_; 
v_inheritedTraceOptions_4471_ = lean_ctor_get(v___y_4464_, 13);
v___x_4472_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4471_, v_options_4469_, v___x_3966_);
if (v___x_4472_ == 0)
{
v___y_4389_ = v___y_4461_;
v___y_4390_ = v___y_4462_;
v___y_4391_ = v___y_4463_;
v___y_4392_ = v___y_4464_;
v___y_4393_ = v___y_4465_;
goto v___jp_4388_;
}
else
{
lean_object* v___x_4473_; lean_object* v___x_4474_; 
v___x_4473_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__2, &l_Lean_addDecl___lam__8___closed__2_once, _init_l_Lean_addDecl___lam__8___closed__2);
v___x_4474_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3763_, v___x_4473_, v___y_4464_, v___y_4465_);
if (lean_obj_tag(v___x_4474_) == 0)
{
lean_dec_ref(v___x_4474_);
v___y_4389_ = v___y_4461_;
v___y_4390_ = v___y_4462_;
v___y_4391_ = v___y_4463_;
v___y_4392_ = v___y_4464_;
v___y_4393_ = v___y_4465_;
goto v___jp_4388_;
}
else
{
lean_dec_ref(v___y_4462_);
lean_dec(v___y_4461_);
lean_dec(v_decl_3567_);
return v___x_4474_;
}
}
}
}
else
{
v___y_4418_ = v___y_4460_;
v___y_4419_ = v___y_4461_;
v___y_4420_ = v___y_4462_;
v___y_4421_ = v___y_4463_;
v___y_4422_ = v___y_4464_;
v___y_4423_ = v___y_4465_;
goto v___jp_4417_;
}
}
else
{
v___y_4418_ = v___y_4460_;
v___y_4419_ = v___y_4461_;
v___y_4420_ = v___y_4462_;
v___y_4421_ = v___y_4463_;
v___y_4422_ = v___y_4464_;
v___y_4423_ = v___y_4465_;
goto v___jp_4417_;
}
}
else
{
lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v_a_4477_; uint8_t v___x_4478_; 
lean_dec(v___y_4460_);
v___x_4475_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4476_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__2___redArg(v___x_4475_, v___y_4464_);
v_a_4477_ = lean_ctor_get(v___x_4476_, 0);
lean_inc(v_a_4477_);
lean_dec_ref(v___x_4476_);
v___x_4478_ = lean_unbox(v_a_4477_);
lean_dec(v_a_4477_);
if (v___x_4478_ == 0)
{
lean_object* v_options_4479_; uint8_t v_hasTrace_4480_; 
v_options_4479_ = lean_ctor_get(v___y_4464_, 2);
v_hasTrace_4480_ = lean_ctor_get_uint8(v_options_4479_, sizeof(void*)*1);
if (v_hasTrace_4480_ == 0)
{
v___y_4374_ = v___y_4461_;
v___y_4375_ = v___y_4462_;
v___y_4376_ = v___y_4463_;
v_exportedInfo_x3f_4377_ = v___x_4458_;
v___y_4378_ = v___y_4464_;
v___y_4379_ = v___y_4465_;
goto v___jp_4373_;
}
else
{
lean_object* v_inheritedTraceOptions_4481_; uint8_t v___x_4482_; 
v_inheritedTraceOptions_4481_ = lean_ctor_get(v___y_4464_, 13);
v___x_4482_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4481_, v_options_4479_, v___x_3966_);
if (v___x_4482_ == 0)
{
v___y_4374_ = v___y_4461_;
v___y_4375_ = v___y_4462_;
v___y_4376_ = v___y_4463_;
v_exportedInfo_x3f_4377_ = v___x_4458_;
v___y_4378_ = v___y_4464_;
v___y_4379_ = v___y_4465_;
goto v___jp_4373_;
}
else
{
lean_object* v___x_4483_; lean_object* v___x_4484_; 
v___x_4483_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__4, &l_Lean_addDecl___lam__8___closed__4_once, _init_l_Lean_addDecl___lam__8___closed__4);
v___x_4484_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3763_, v___x_4483_, v___y_4464_, v___y_4465_);
if (lean_obj_tag(v___x_4484_) == 0)
{
lean_dec_ref(v___x_4484_);
v___y_4374_ = v___y_4461_;
v___y_4375_ = v___y_4462_;
v___y_4376_ = v___y_4463_;
v_exportedInfo_x3f_4377_ = v___x_4458_;
v___y_4378_ = v___y_4464_;
v___y_4379_ = v___y_4465_;
goto v___jp_4373_;
}
else
{
lean_dec_ref(v___y_4462_);
lean_dec(v___y_4461_);
lean_dec(v_decl_3567_);
return v___x_4484_;
}
}
}
}
else
{
lean_object* v_options_4485_; uint8_t v_hasTrace_4486_; 
v_options_4485_ = lean_ctor_get(v___y_4464_, 2);
v_hasTrace_4486_ = lean_ctor_get_uint8(v_options_4485_, sizeof(void*)*1);
if (v_hasTrace_4486_ == 0)
{
v___y_4396_ = v___y_4461_;
v___y_4397_ = v___y_4462_;
v___y_4398_ = v___y_4463_;
v___y_4399_ = v___y_4464_;
v___y_4400_ = v___y_4465_;
goto v___jp_4395_;
}
else
{
lean_object* v_inheritedTraceOptions_4487_; uint8_t v___x_4488_; 
v_inheritedTraceOptions_4487_ = lean_ctor_get(v___y_4464_, 13);
v___x_4488_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4487_, v_options_4485_, v___x_3966_);
if (v___x_4488_ == 0)
{
v___y_4396_ = v___y_4461_;
v___y_4397_ = v___y_4462_;
v___y_4398_ = v___y_4463_;
v___y_4399_ = v___y_4464_;
v___y_4400_ = v___y_4465_;
goto v___jp_4395_;
}
else
{
lean_object* v___x_4489_; lean_object* v___x_4490_; 
v___x_4489_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__6, &l_Lean_addDecl___lam__8___closed__6_once, _init_l_Lean_addDecl___lam__8___closed__6);
v___x_4490_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3763_, v___x_4489_, v___y_4464_, v___y_4465_);
if (lean_obj_tag(v___x_4490_) == 0)
{
lean_dec_ref(v___x_4490_);
v___y_4396_ = v___y_4461_;
v___y_4397_ = v___y_4462_;
v___y_4398_ = v___y_4463_;
v___y_4399_ = v___y_4464_;
v___y_4400_ = v___y_4465_;
goto v___jp_4395_;
}
else
{
lean_dec_ref(v___y_4462_);
lean_dec(v___y_4461_);
lean_dec(v_decl_3567_);
return v___x_4490_;
}
}
}
}
}
}
v___jp_4491_:
{
lean_object* v___x_4498_; lean_object* v_env_4499_; uint8_t v___x_4500_; 
v___x_4498_ = lean_st_ref_get(v___y_4497_);
v_env_4499_ = lean_ctor_get(v___x_4498_, 0);
lean_inc_ref(v_env_4499_);
lean_dec(v___x_4498_);
v___x_4500_ = l_Lean_Environment_containsOnBranch(v_env_4499_, v_fst_4492_);
lean_dec_ref(v_env_4499_);
if (v___x_4500_ == 0)
{
v___y_4460_ = v_exportedInfo_x3f_4495_;
v___y_4461_ = v_fst_4492_;
v___y_4462_ = v_fst_4493_;
v___y_4463_ = v_snd_4494_;
v___y_4464_ = v___y_4496_;
v___y_4465_ = v___y_4497_;
goto v___jp_4459_;
}
else
{
lean_object* v___x_4501_; lean_object* v_env_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; 
lean_dec(v_exportedInfo_x3f_4495_);
lean_dec_ref(v_fst_4493_);
lean_dec(v_decl_3567_);
v___x_4501_ = lean_st_ref_get(v___y_4497_);
v_env_4502_ = lean_ctor_get(v___x_4501_, 0);
lean_inc_ref(v_env_4502_);
lean_dec(v___x_4501_);
v___x_4503_ = lean_elab_environment_to_kernel_env(v_env_4502_);
v___x_4504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4504_, 0, v___x_4503_);
lean_ctor_set(v___x_4504_, 1, v_fst_4492_);
v___x_4505_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(v___x_4504_, v___y_4496_, v___y_4497_);
return v___x_4505_;
}
}
v___jp_4506_:
{
lean_object* v_name_4512_; lean_object* v___x_4513_; uint8_t v___x_4514_; 
v_name_4512_ = lean_ctor_get(v_toConstantVal_4508_, 0);
lean_inc(v_name_4512_);
lean_dec_ref(v_toConstantVal_4508_);
v___x_4513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4513_, 0, v___y_4507_);
v___x_4514_ = 0;
v_fst_4492_ = v_name_4512_;
v_fst_4493_ = v___x_4513_;
v_snd_4494_ = v___x_4514_;
v_exportedInfo_x3f_4495_ = v_exportedInfo_x3f_4509_;
v___y_4496_ = v___y_4510_;
v___y_4497_ = v___y_4511_;
goto v___jp_4491_;
}
v___jp_4515_:
{
uint8_t v___x_4521_; uint8_t v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; 
v___x_4521_ = 0;
v___x_4522_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4518_, v___x_4521_);
lean_inc_ref(v_toConstantVal_4517_);
v___x_4523_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4523_, 0, v_toConstantVal_4517_);
lean_ctor_set_uint8(v___x_4523_, sizeof(void*)*1, v___x_4522_);
v___x_4524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4524_, 0, v___x_4523_);
v___x_4525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4525_, 0, v___x_4524_);
v___y_4507_ = v___y_4516_;
v_toConstantVal_4508_ = v_toConstantVal_4517_;
v_exportedInfo_x3f_4509_ = v___x_4525_;
v___y_4510_ = v___y_4519_;
v___y_4511_ = v___y_4520_;
goto v___jp_4506_;
}
v___jp_4526_:
{
lean_object* v_toConstantVal_4530_; uint8_t v_safety_4531_; 
v_toConstantVal_4530_ = lean_ctor_get(v___y_4527_, 0);
lean_inc_ref(v_toConstantVal_4530_);
v_safety_4531_ = lean_ctor_get_uint8(v___y_4527_, sizeof(void*)*4);
v___y_4516_ = v___y_4527_;
v_toConstantVal_4517_ = v_toConstantVal_4530_;
v_safety_4518_ = v_safety_4531_;
v___y_4519_ = v___y_4528_;
v___y_4520_ = v___y_4529_;
goto v___jp_4515_;
}
v___jp_4532_:
{
lean_object* v_options_4536_; uint8_t v_hasTrace_4537_; 
v_options_4536_ = lean_ctor_get(v___y_4534_, 2);
v_hasTrace_4537_ = lean_ctor_get_uint8(v_options_4536_, sizeof(void*)*1);
if (v_hasTrace_4537_ == 0)
{
v___y_4527_ = v___y_4535_;
v___y_4528_ = v___y_4534_;
v___y_4529_ = v___y_4533_;
goto v___jp_4526_;
}
else
{
lean_object* v_inheritedTraceOptions_4538_; uint8_t v___x_4539_; 
v_inheritedTraceOptions_4538_ = lean_ctor_get(v___y_4534_, 13);
v___x_4539_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4538_, v_options_4536_, v___x_3966_);
if (v___x_4539_ == 0)
{
v___y_4527_ = v___y_4535_;
v___y_4528_ = v___y_4534_;
v___y_4529_ = v___y_4533_;
goto v___jp_4526_;
}
else
{
lean_object* v_toConstantVal_4540_; uint8_t v_safety_4541_; lean_object* v_name_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; 
v_toConstantVal_4540_ = lean_ctor_get(v___y_4535_, 0);
lean_inc_ref(v_toConstantVal_4540_);
v_safety_4541_ = lean_ctor_get_uint8(v___y_4535_, sizeof(void*)*4);
v_name_4542_ = lean_ctor_get(v_toConstantVal_4540_, 0);
v___x_4543_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__1, &l_Lean_addDecl___lam__4___closed__1_once, _init_l_Lean_addDecl___lam__4___closed__1);
lean_inc(v_name_4542_);
v___x_4544_ = l_Lean_MessageData_ofName(v_name_4542_);
v___x_4545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4545_, 0, v___x_4543_);
lean_ctor_set(v___x_4545_, 1, v___x_4544_);
v___x_4546_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_4547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4547_, 0, v___x_4545_);
lean_ctor_set(v___x_4547_, 1, v___x_4546_);
v___x_4548_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3763_, v___x_4547_, v___y_4534_, v___y_4533_);
if (lean_obj_tag(v___x_4548_) == 0)
{
lean_dec_ref(v___x_4548_);
v___y_4516_ = v___y_4535_;
v_toConstantVal_4517_ = v_toConstantVal_4540_;
v_safety_4518_ = v_safety_4541_;
v___y_4519_ = v___y_4534_;
v___y_4520_ = v___y_4533_;
goto v___jp_4515_;
}
else
{
lean_dec_ref(v_toConstantVal_4540_);
lean_dec_ref(v___y_4535_);
lean_dec(v_decl_3567_);
return v___x_4548_;
}
}
}
}
v___jp_4549_:
{
lean_object* v_toConstantVal_4554_; 
v_toConstantVal_4554_ = lean_ctor_get(v___y_4550_, 0);
lean_inc_ref(v_toConstantVal_4554_);
v___y_4507_ = v___y_4550_;
v_toConstantVal_4508_ = v_toConstantVal_4554_;
v_exportedInfo_x3f_4509_ = v_exportedInfo_x3f_4551_;
v___y_4510_ = v___y_4552_;
v___y_4511_ = v___y_4553_;
goto v___jp_4506_;
}
v___jp_4555_:
{
lean_object* v___x_4561_; uint8_t v_isModule_4562_; 
v___x_4561_ = l_Lean_Environment_header(v___y_4559_);
lean_dec_ref(v___y_4559_);
v_isModule_4562_ = lean_ctor_get_uint8(v___x_4561_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4561_);
if (v_isModule_4562_ == 0)
{
lean_dec_ref(v___y_4557_);
v___y_4550_ = v___y_4560_;
v_exportedInfo_x3f_4551_ = v___x_4458_;
v___y_4552_ = v___y_4558_;
v___y_4553_ = v___y_4556_;
goto v___jp_4549_;
}
else
{
uint8_t v_isExporting_4563_; 
v_isExporting_4563_ = lean_ctor_get_uint8(v___y_4557_, sizeof(void*)*8);
lean_dec_ref(v___y_4557_);
if (v_isExporting_4563_ == 0)
{
v___y_4533_ = v___y_4556_;
v___y_4534_ = v___y_4558_;
v___y_4535_ = v___y_4560_;
goto v___jp_4532_;
}
else
{
if (v___x_4268_ == 0)
{
v___y_4550_ = v___y_4560_;
v_exportedInfo_x3f_4551_ = v___x_4458_;
v___y_4552_ = v___y_4558_;
v___y_4553_ = v___y_4556_;
goto v___jp_4549_;
}
else
{
v___y_4533_ = v___y_4556_;
v___y_4534_ = v___y_4558_;
v___y_4535_ = v___y_4560_;
goto v___jp_4532_;
}
}
}
}
v___jp_4564_:
{
lean_object* v___x_4568_; lean_object* v___x_4569_; 
v___x_4568_ = lean_st_ref_get(v___y_4567_);
v___x_4569_ = lean_st_ref_get(v___y_4567_);
if (v_forceExpose_3568_ == 0)
{
lean_object* v_env_4570_; lean_object* v_env_4571_; 
v_env_4570_ = lean_ctor_get(v___x_4568_, 0);
lean_inc_ref(v_env_4570_);
lean_dec(v___x_4568_);
v_env_4571_ = lean_ctor_get(v___x_4569_, 0);
lean_inc_ref(v_env_4571_);
lean_dec(v___x_4569_);
v___y_4556_ = v___y_4567_;
v___y_4557_ = v_env_4571_;
v___y_4558_ = v___y_4566_;
v___y_4559_ = v_env_4570_;
v___y_4560_ = v_defn_4565_;
goto v___jp_4555_;
}
else
{
if (v___x_4268_ == 0)
{
lean_dec(v___x_4569_);
lean_dec(v___x_4568_);
v___y_4550_ = v_defn_4565_;
v_exportedInfo_x3f_4551_ = v___x_4458_;
v___y_4552_ = v___y_4566_;
v___y_4553_ = v___y_4567_;
goto v___jp_4549_;
}
else
{
lean_object* v_env_4572_; lean_object* v_env_4573_; 
v_env_4572_ = lean_ctor_get(v___x_4568_, 0);
lean_inc_ref(v_env_4572_);
lean_dec(v___x_4568_);
v_env_4573_ = lean_ctor_get(v___x_4569_, 0);
lean_inc_ref(v_env_4573_);
lean_dec(v___x_4569_);
v___y_4556_ = v___y_4567_;
v___y_4557_ = v_env_4573_;
v___y_4558_ = v___y_4566_;
v___y_4559_ = v_env_4572_;
v___y_4560_ = v_defn_4565_;
goto v___jp_4555_;
}
}
}
}
}
}
else
{
goto v___jp_4115_;
}
v___jp_4269_:
{
lean_object* v___x_4280_; 
lean_inc_ref(v___y_4273_);
v___x_4280_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_4276_, v___y_4273_, v___y_4271_, v___y_4279_);
if (lean_obj_tag(v___x_4280_) == 0)
{
lean_object* v___x_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4327_; 
lean_dec_ref(v___x_4280_);
lean_inc_ref(v___y_4278_);
v___x_4281_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_4278_, v___y_4274_);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___x_4281_);
if (v_isSharedCheck_4327_ == 0)
{
lean_object* v_unused_4328_; 
v_unused_4328_ = lean_ctor_get(v___x_4281_, 0);
lean_dec(v_unused_4328_);
v___x_4283_ = v___x_4281_;
v_isShared_4284_ = v_isSharedCheck_4327_;
goto v_resetjp_4282_;
}
else
{
lean_dec(v___x_4281_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4327_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v_options_4285_; lean_object* v___x_4286_; uint8_t v___x_4287_; 
v_options_4285_ = lean_ctor_get(v___y_4275_, 2);
v___x_4286_ = l_Lean_Elab_async;
v___x_4287_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_4285_, v___x_4286_);
if (v___x_4287_ == 0)
{
lean_object* v___x_4288_; lean_object* v_r_4289_; 
lean_del_object(v___x_4283_);
lean_dec_ref(v___y_4272_);
lean_dec_ref(v___y_4270_);
v___x_4288_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_4273_, v___y_4274_);
lean_dec_ref(v___x_4288_);
v_r_4289_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3567_, v___y_4275_, v___y_4274_);
if (lean_obj_tag(v_r_4289_) == 0)
{
lean_object* v_a_4290_; lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4299_; 
v_a_4290_ = lean_ctor_get(v_r_4289_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v_r_4289_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4292_ = v_r_4289_;
v_isShared_4293_ = v_isSharedCheck_4299_;
goto v_resetjp_4291_;
}
else
{
lean_inc(v_a_4290_);
lean_dec(v_r_4289_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4299_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
lean_object* v___x_4295_; 
lean_inc(v_a_4290_);
if (v_isShared_4293_ == 0)
{
lean_ctor_set_tag(v___x_4292_, 1);
v___x_4295_ = v___x_4292_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_a_4290_);
v___x_4295_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
lean_object* v___x_4296_; 
v___x_4296_ = lean_apply_2(v___y_4277_, v___x_4295_, lean_box(0));
if (lean_obj_tag(v___x_4296_) == 0)
{
lean_dec_ref(v___x_4296_);
v___y_3586_ = v___y_4274_;
v___y_3587_ = v___y_4278_;
v_a_3588_ = v_a_4290_;
goto v___jp_3585_;
}
else
{
lean_object* v_a_4297_; 
lean_dec(v_a_4290_);
v_a_4297_ = lean_ctor_get(v___x_4296_, 0);
lean_inc(v_a_4297_);
lean_dec_ref(v___x_4296_);
v___y_3573_ = v___y_4274_;
v___y_3574_ = v___y_4278_;
v_a_3575_ = v_a_4297_;
goto v___jp_3572_;
}
}
}
}
else
{
lean_object* v_a_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v_a_4300_ = lean_ctor_get(v_r_4289_, 0);
lean_inc(v_a_4300_);
lean_dec_ref(v_r_4289_);
v___x_4301_ = lean_box(0);
v___x_4302_ = lean_apply_2(v___y_4277_, v___x_4301_, lean_box(0));
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_dec_ref(v___x_4302_);
v___y_3573_ = v___y_4274_;
v___y_3574_ = v___y_4278_;
v_a_3575_ = v_a_4300_;
goto v___jp_3572_;
}
else
{
lean_object* v_a_4303_; 
lean_dec(v_a_4300_);
v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
lean_inc(v_a_4303_);
lean_dec_ref(v___x_4302_);
v___y_3573_ = v___y_4274_;
v___y_3574_ = v___y_4278_;
v_a_3575_ = v_a_4303_;
goto v___jp_3572_;
}
}
}
else
{
lean_object* v___x_4304_; lean_object* v___x_4306_; 
lean_dec_ref(v___y_4278_);
lean_dec_ref(v___y_4277_);
lean_dec_ref(v___y_4273_);
lean_dec(v_decl_3567_);
v___x_4304_ = l_IO_CancelToken_new();
if (v_isShared_4284_ == 0)
{
lean_ctor_set_tag(v___x_4283_, 1);
lean_ctor_set(v___x_4283_, 0, v___x_4304_);
v___x_4306_ = v___x_4283_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v___x_4304_);
v___x_4306_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4307_ = ((lean_object*)(l_Lean_addDecl___closed__0));
v___x_4308_ = l_Lean_Name_toString(v___x_4307_, v_hasTrace_3626_);
lean_inc_ref(v___x_4306_);
v___x_4309_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_4270_, v___x_4306_, v___x_4308_, v___y_4275_, v___y_4274_);
if (lean_obj_tag(v___x_4309_) == 0)
{
lean_object* v_a_4310_; lean_object* v_checked_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
v_a_4310_ = lean_ctor_get(v___x_4309_, 0);
lean_inc(v_a_4310_);
lean_dec_ref(v___x_4309_);
v_checked_4311_ = lean_ctor_get(v___y_4272_, 2);
lean_inc_ref(v_checked_4311_);
lean_dec_ref(v___y_4272_);
v___x_4312_ = lean_unsigned_to_nat(0u);
v___x_4313_ = lean_io_map_task(v_a_4310_, v_checked_4311_, v___x_4312_, v___x_4268_);
v___x_4314_ = lean_box(0);
v___x_4315_ = lean_box(2);
v___x_4316_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4316_, 0, v___x_4314_);
lean_ctor_set(v___x_4316_, 1, v___x_4315_);
lean_ctor_set(v___x_4316_, 2, v___x_4306_);
lean_ctor_set(v___x_4316_, 3, v___x_4313_);
v___x_4317_ = l_Lean_Core_logSnapshotTask___redArg(v___x_4316_, v___y_4274_);
return v___x_4317_;
}
else
{
lean_object* v_a_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4325_; 
lean_dec_ref(v___x_4306_);
lean_dec_ref(v___y_4272_);
v_a_4318_ = lean_ctor_get(v___x_4309_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___x_4309_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4320_ = v___x_4309_;
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_a_4318_);
lean_dec(v___x_4309_);
v___x_4320_ = lean_box(0);
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
v_resetjp_4319_:
{
lean_object* v___x_4323_; 
if (v_isShared_4321_ == 0)
{
v___x_4323_ = v___x_4320_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v_a_4318_);
v___x_4323_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
return v___x_4323_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4341_; 
lean_dec_ref(v___y_4278_);
lean_dec_ref(v___y_4277_);
lean_dec_ref(v___y_4273_);
lean_dec_ref(v___y_4272_);
lean_dec_ref(v___y_4270_);
lean_dec(v_decl_3567_);
v_a_4329_ = lean_ctor_get(v___x_4280_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4280_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4331_ = v___x_4280_;
v_isShared_4332_ = v_isSharedCheck_4341_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_a_4329_);
lean_dec(v___x_4280_);
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4341_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
lean_object* v_ref_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4339_; 
v_ref_4333_ = lean_ctor_get(v___y_4275_, 5);
v___x_4334_ = lean_io_error_to_string(v_a_4329_);
v___x_4335_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4335_, 0, v___x_4334_);
v___x_4336_ = l_Lean_MessageData_ofFormat(v___x_4335_);
lean_inc(v_ref_4333_);
v___x_4337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4337_, 0, v_ref_4333_);
lean_ctor_set(v___x_4337_, 1, v___x_4336_);
if (v_isShared_4332_ == 0)
{
lean_ctor_set(v___x_4331_, 0, v___x_4337_);
v___x_4339_ = v___x_4331_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v___x_4337_);
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
v___jp_4342_:
{
lean_object* v___x_4353_; 
lean_inc_ref(v___y_4343_);
v___x_4353_ = l_Lean_Environment_addConstAsync(v___y_4343_, v___y_4347_, v___y_4351_, v___y_4352_, v___x_4268_, v_hasTrace_3626_);
if (lean_obj_tag(v___x_4353_) == 0)
{
lean_object* v_a_4354_; lean_object* v_mainEnv_4355_; lean_object* v_asyncEnv_4356_; lean_object* v___f_4357_; lean_object* v___f_4358_; lean_object* v___x_4359_; 
v_a_4354_ = lean_ctor_get(v___x_4353_, 0);
lean_inc_n(v_a_4354_, 3);
lean_dec_ref(v___x_4353_);
v_mainEnv_4355_ = lean_ctor_get(v_a_4354_, 0);
lean_inc_ref(v_mainEnv_4355_);
v_asyncEnv_4356_ = lean_ctor_get(v_a_4354_, 1);
lean_inc_ref_n(v_asyncEnv_4356_, 2);
lean_inc_ref(v___y_4345_);
lean_inc(v___y_4344_);
v___f_4357_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4357_, 0, v___y_4344_);
lean_closure_set(v___f_4357_, 1, v_a_4354_);
lean_closure_set(v___f_4357_, 2, v___y_4345_);
lean_inc(v_decl_3567_);
v___f_4358_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4358_, 0, v_asyncEnv_4356_);
lean_closure_set(v___f_4358_, 1, v_a_4354_);
lean_closure_set(v___f_4358_, 2, v_decl_3567_);
v___x_4359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4359_, 0, v___y_4350_);
if (lean_obj_tag(v___y_4346_) == 0)
{
lean_inc_ref(v___x_4359_);
v___y_4270_ = v___f_4358_;
v___y_4271_ = v___x_4359_;
v___y_4272_ = v___y_4343_;
v___y_4273_ = v_asyncEnv_4356_;
v___y_4274_ = v___y_4348_;
v___y_4275_ = v___y_4349_;
v___y_4276_ = v_a_4354_;
v___y_4277_ = v___f_4357_;
v___y_4278_ = v_mainEnv_4355_;
v___y_4279_ = v___x_4359_;
goto v___jp_4269_;
}
else
{
v___y_4270_ = v___f_4358_;
v___y_4271_ = v___x_4359_;
v___y_4272_ = v___y_4343_;
v___y_4273_ = v_asyncEnv_4356_;
v___y_4274_ = v___y_4348_;
v___y_4275_ = v___y_4349_;
v___y_4276_ = v_a_4354_;
v___y_4277_ = v___f_4357_;
v___y_4278_ = v_mainEnv_4355_;
v___y_4279_ = v___y_4346_;
goto v___jp_4269_;
}
}
else
{
lean_object* v_a_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4372_; 
lean_dec_ref(v___y_4350_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4343_);
lean_dec(v_decl_3567_);
v_a_4360_ = lean_ctor_get(v___x_4353_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4353_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4362_ = v___x_4353_;
v_isShared_4363_ = v_isSharedCheck_4372_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_a_4360_);
lean_dec(v___x_4353_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4372_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v_ref_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4370_; 
v_ref_4364_ = lean_ctor_get(v___y_4349_, 5);
v___x_4365_ = lean_io_error_to_string(v_a_4360_);
v___x_4366_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4366_, 0, v___x_4365_);
v___x_4367_ = l_Lean_MessageData_ofFormat(v___x_4366_);
lean_inc(v_ref_4364_);
v___x_4368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4368_, 0, v_ref_4364_);
lean_ctor_set(v___x_4368_, 1, v___x_4367_);
if (v_isShared_4363_ == 0)
{
lean_ctor_set(v___x_4362_, 0, v___x_4368_);
v___x_4370_ = v___x_4362_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v___x_4368_);
v___x_4370_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
return v___x_4370_;
}
}
}
}
v___jp_4373_:
{
lean_object* v___x_4380_; 
v___x_4380_ = lean_st_ref_get(v___y_4379_);
if (lean_obj_tag(v_exportedInfo_x3f_4377_) == 0)
{
lean_object* v_env_4381_; lean_object* v___x_4382_; 
v_env_4381_ = lean_ctor_get(v___x_4380_, 0);
lean_inc_ref(v_env_4381_);
lean_dec(v___x_4380_);
v___x_4382_ = lean_box(0);
v___y_4343_ = v_env_4381_;
v___y_4344_ = v___y_4379_;
v___y_4345_ = v___y_4378_;
v___y_4346_ = v_exportedInfo_x3f_4377_;
v___y_4347_ = v___y_4374_;
v___y_4348_ = v___y_4379_;
v___y_4349_ = v___y_4378_;
v___y_4350_ = v___y_4375_;
v___y_4351_ = v___y_4376_;
v___y_4352_ = v___x_4382_;
goto v___jp_4342_;
}
else
{
lean_object* v_env_4383_; lean_object* v_val_4384_; uint8_t v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; 
v_env_4383_ = lean_ctor_get(v___x_4380_, 0);
lean_inc_ref(v_env_4383_);
lean_dec(v___x_4380_);
v_val_4384_ = lean_ctor_get(v_exportedInfo_x3f_4377_, 0);
v___x_4385_ = l_Lean_ConstantKind_ofConstantInfo(v_val_4384_);
v___x_4386_ = lean_box(v___x_4385_);
v___x_4387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4387_, 0, v___x_4386_);
v___y_4343_ = v_env_4383_;
v___y_4344_ = v___y_4379_;
v___y_4345_ = v___y_4378_;
v___y_4346_ = v_exportedInfo_x3f_4377_;
v___y_4347_ = v___y_4374_;
v___y_4348_ = v___y_4379_;
v___y_4349_ = v___y_4378_;
v___y_4350_ = v___y_4375_;
v___y_4351_ = v___y_4376_;
v___y_4352_ = v___x_4387_;
goto v___jp_4342_;
}
}
v___jp_4388_:
{
lean_object* v___x_4394_; 
lean_inc_ref(v___y_4390_);
v___x_4394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4394_, 0, v___y_4390_);
v___y_4374_ = v___y_4389_;
v___y_4375_ = v___y_4390_;
v___y_4376_ = v___y_4391_;
v_exportedInfo_x3f_4377_ = v___x_4394_;
v___y_4378_ = v___y_4392_;
v___y_4379_ = v___y_4393_;
goto v___jp_4373_;
}
v___jp_4395_:
{
lean_object* v___x_4401_; 
lean_inc_ref(v___y_4397_);
v___x_4401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4401_, 0, v___y_4397_);
v___y_4374_ = v___y_4396_;
v___y_4375_ = v___y_4397_;
v___y_4376_ = v___y_4398_;
v_exportedInfo_x3f_4377_ = v___x_4401_;
v___y_4378_ = v___y_4399_;
v___y_4379_ = v___y_4400_;
goto v___jp_4373_;
}
}
else
{
goto v___jp_4115_;
}
v___jp_3968_:
{
lean_object* v___x_3972_; double v___x_3973_; double v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
v___x_3972_ = lean_io_get_num_heartbeats();
v___x_3973_ = lean_float_of_nat(v___y_3970_);
v___x_3974_ = lean_float_of_nat(v___x_3972_);
v___x_3975_ = lean_box_float(v___x_3973_);
v___x_3976_ = lean_box_float(v___x_3974_);
v___x_3977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3975_);
lean_ctor_set(v___x_3977_, 1, v___x_3976_);
v___x_3978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3978_, 0, v_a_3971_);
lean_ctor_set(v___x_3978_, 1, v___x_3977_);
v___x_3979_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2(v_cls_3763_, v_hasTrace_3626_, v___x_3965_, v_options_3624_, v___x_3967_, v___y_3969_, v___f_3964_, v___x_3978_, v_a_3569_, v_a_3570_);
return v___x_3979_;
}
v___jp_3980_:
{
if (lean_obj_tag(v___y_3983_) == 0)
{
lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3991_; 
v_a_3984_ = lean_ctor_get(v___y_3983_, 0);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___y_3983_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3986_ = v___y_3983_;
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_dec(v___y_3983_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3989_; 
if (v_isShared_3987_ == 0)
{
lean_ctor_set_tag(v___x_3986_, 1);
v___x_3989_ = v___x_3986_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v_a_3984_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
v___y_3969_ = v___y_3981_;
v___y_3970_ = v___y_3982_;
v_a_3971_ = v___x_3989_;
goto v___jp_3968_;
}
}
}
else
{
lean_object* v_a_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_3999_; 
v_a_3992_ = lean_ctor_get(v___y_3983_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v___y_3983_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3994_ = v___y_3983_;
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_a_3992_);
lean_dec(v___y_3983_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v___x_3997_; 
if (v_isShared_3995_ == 0)
{
lean_ctor_set_tag(v___x_3994_, 0);
v___x_3997_ = v___x_3994_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_a_3992_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
v___y_3969_ = v___y_3981_;
v___y_3970_ = v___y_3982_;
v_a_3971_ = v___x_3997_;
goto v___jp_3968_;
}
}
}
}
v___jp_4000_:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4005_ = lean_box(0);
lean_inc(v_a_3570_);
lean_inc_ref(v_a_3569_);
v___x_4006_ = lean_apply_5(v___y_4003_, v___x_4005_, v___y_4002_, v_a_3569_, v_a_3570_, lean_box(0));
v___y_3981_ = v___y_4001_;
v___y_3982_ = v___y_4004_;
v___y_3983_ = v___x_4006_;
goto v___jp_3980_;
}
v___jp_4007_:
{
lean_object* v___x_4012_; lean_object* v___x_4013_; 
v___x_4012_ = lean_box(0);
lean_inc(v_a_3570_);
lean_inc_ref(v_a_3569_);
v___x_4013_ = lean_apply_5(v___y_4011_, v___x_4012_, v___y_4009_, v_a_3569_, v_a_3570_, lean_box(0));
v___y_3981_ = v___y_4008_;
v___y_3982_ = v___y_4010_;
v___y_3983_ = v___x_4013_;
goto v___jp_3980_;
}
v___jp_4014_:
{
lean_object* v___x_4018_; double v___x_4019_; double v___x_4020_; double v___x_4021_; double v___x_4022_; double v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4018_ = lean_io_mono_nanos_now();
v___x_4019_ = lean_float_of_nat(v___y_4016_);
v___x_4020_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__1);
v___x_4021_ = lean_float_div(v___x_4019_, v___x_4020_);
v___x_4022_ = lean_float_of_nat(v___x_4018_);
v___x_4023_ = lean_float_div(v___x_4022_, v___x_4020_);
v___x_4024_ = lean_box_float(v___x_4021_);
v___x_4025_ = lean_box_float(v___x_4023_);
v___x_4026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4026_, 0, v___x_4024_);
lean_ctor_set(v___x_4026_, 1, v___x_4025_);
v___x_4027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4027_, 0, v_a_4017_);
lean_ctor_set(v___x_4027_, 1, v___x_4026_);
v___x_4028_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2(v_cls_3763_, v_hasTrace_3626_, v___x_3965_, v_options_3624_, v___x_3967_, v___y_4015_, v___f_3964_, v___x_4027_, v_a_3569_, v_a_3570_);
return v___x_4028_;
}
v___jp_4029_:
{
if (lean_obj_tag(v___y_4032_) == 0)
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4040_; 
v_a_4033_ = lean_ctor_get(v___y_4032_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v___y_4032_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4035_ = v___y_4032_;
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___y_4032_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4038_; 
if (v_isShared_4036_ == 0)
{
lean_ctor_set_tag(v___x_4035_, 1);
v___x_4038_ = v___x_4035_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_a_4033_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
v___y_4015_ = v___y_4030_;
v___y_4016_ = v___y_4031_;
v_a_4017_ = v___x_4038_;
goto v___jp_4014_;
}
}
}
else
{
lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4048_; 
v_a_4041_ = lean_ctor_get(v___y_4032_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___y_4032_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4043_ = v___y_4032_;
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___y_4032_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4046_; 
if (v_isShared_4044_ == 0)
{
lean_ctor_set_tag(v___x_4043_, 0);
v___x_4046_ = v___x_4043_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_a_4041_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
v___y_4015_ = v___y_4030_;
v___y_4016_ = v___y_4031_;
v_a_4017_ = v___x_4046_;
goto v___jp_4014_;
}
}
}
}
v___jp_4049_:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4054_ = lean_box(0);
lean_inc(v_a_3570_);
lean_inc_ref(v_a_3569_);
v___x_4055_ = lean_apply_5(v___y_4053_, v___x_4054_, v___y_4051_, v_a_3569_, v_a_3570_, lean_box(0));
v___y_4030_ = v___y_4050_;
v___y_4031_ = v___y_4052_;
v___y_4032_ = v___x_4055_;
goto v___jp_4029_;
}
v___jp_4056_:
{
if (v___x_3967_ == 0)
{
lean_object* v___x_4061_; lean_object* v___x_4062_; 
lean_dec_ref(v___y_4059_);
v___x_4061_ = lean_box(0);
lean_inc(v_a_3570_);
lean_inc_ref(v_a_3569_);
v___x_4062_ = lean_apply_4(v___y_4060_, v___x_4061_, v_a_3569_, v_a_3570_, lean_box(0));
v___y_4030_ = v___y_4057_;
v___y_4031_ = v___y_4058_;
v___y_4032_ = v___x_4062_;
goto v___jp_4029_;
}
else
{
lean_object* v_toConstantVal_4063_; lean_object* v_name_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
v_toConstantVal_4063_ = lean_ctor_get(v___y_4059_, 0);
lean_inc_ref(v_toConstantVal_4063_);
lean_dec_ref(v___y_4059_);
v_name_4064_ = lean_ctor_get(v_toConstantVal_4063_, 0);
lean_inc(v_name_4064_);
lean_dec_ref(v_toConstantVal_4063_);
v___x_4065_ = lean_obj_once(&l_Lean_addDecl___closed__3, &l_Lean_addDecl___closed__3_once, _init_l_Lean_addDecl___closed__3);
v___x_4066_ = l_Lean_MessageData_ofName(v_name_4064_);
v___x_4067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4065_);
lean_ctor_set(v___x_4067_, 1, v___x_4066_);
v___x_4068_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_4069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4069_, 0, v___x_4067_);
lean_ctor_set(v___x_4069_, 1, v___x_4068_);
v___x_4070_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3763_, v___x_4069_, v_a_3569_, v_a_3570_);
if (lean_obj_tag(v___x_4070_) == 0)
{
lean_object* v_a_4071_; lean_object* v___x_4072_; 
v_a_4071_ = lean_ctor_get(v___x_4070_, 0);
lean_inc(v_a_4071_);
lean_dec_ref(v___x_4070_);
lean_inc(v_a_3570_);
lean_inc_ref(v_a_3569_);
v___x_4072_ = lean_apply_4(v___y_4060_, v_a_4071_, v_a_3569_, v_a_3570_, lean_box(0));
v___y_4030_ = v___y_4057_;
v___y_4031_ = v___y_4058_;
v___y_4032_ = v___x_4072_;
goto v___jp_4029_;
}
else
{
lean_dec_ref(v___y_4060_);
v___y_4030_ = v___y_4057_;
v___y_4031_ = v___y_4058_;
v___y_4032_ = v___x_4070_;
goto v___jp_4029_;
}
}
}
v___jp_4073_:
{
lean_object* v___x_4083_; uint8_t v_isModule_4084_; 
v___x_4083_ = l_Lean_Environment_header(v___y_4076_);
lean_dec_ref(v___y_4076_);
v_isModule_4084_ = lean_ctor_get_uint8(v___x_4083_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4083_);
if (v_isModule_4084_ == 0)
{
lean_dec_ref(v___y_4081_);
lean_dec_ref(v___y_4080_);
lean_dec_ref(v___y_4079_);
v___y_4050_ = v___y_4075_;
v___y_4051_ = v___y_4077_;
v___y_4052_ = v___y_4078_;
v___y_4053_ = v___y_4082_;
goto v___jp_4049_;
}
else
{
uint8_t v_isExporting_4085_; 
v_isExporting_4085_ = lean_ctor_get_uint8(v___y_4081_, sizeof(void*)*8);
lean_dec_ref(v___y_4081_);
if (v_isExporting_4085_ == 0)
{
lean_dec_ref(v___y_4082_);
lean_dec(v___y_4077_);
v___y_4057_ = v___y_4075_;
v___y_4058_ = v___y_4078_;
v___y_4059_ = v___y_4079_;
v___y_4060_ = v___y_4080_;
goto v___jp_4056_;
}
else
{
if (v___y_4074_ == 0)
{
lean_dec_ref(v___y_4080_);
lean_dec_ref(v___y_4079_);
v___y_4050_ = v___y_4075_;
v___y_4051_ = v___y_4077_;
v___y_4052_ = v___y_4078_;
v___y_4053_ = v___y_4082_;
goto v___jp_4049_;
}
else
{
lean_dec_ref(v___y_4082_);
lean_dec(v___y_4077_);
v___y_4057_ = v___y_4075_;
v___y_4058_ = v___y_4078_;
v___y_4059_ = v___y_4079_;
v___y_4060_ = v___y_4080_;
goto v___jp_4056_;
}
}
}
}
v___jp_4086_:
{
lean_object* v___x_4091_; lean_object* v___x_4092_; 
v___x_4091_ = lean_box(0);
lean_inc(v_a_3570_);
lean_inc_ref(v_a_3569_);
v___x_4092_ = lean_apply_5(v___y_4090_, v___x_4091_, v___y_4088_, v_a_3569_, v_a_3570_, lean_box(0));
v___y_4030_ = v___y_4087_;
v___y_4031_ = v___y_4089_;
v___y_4032_ = v___x_4092_;
goto v___jp_4029_;
}
v___jp_4093_:
{
lean_object* v___x_4101_; uint8_t v_isModule_4102_; 
v___x_4101_ = l_Lean_Environment_header(v___y_4100_);
lean_dec_ref(v___y_4100_);
v_isModule_4102_ = lean_ctor_get_uint8(v___x_4101_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4101_);
if (v_isModule_4102_ == 0)
{
lean_dec_ref(v___y_4095_);
lean_dec_ref(v___y_4094_);
v___y_4087_ = v___y_4096_;
v___y_4088_ = v___y_4097_;
v___y_4089_ = v___y_4098_;
v___y_4090_ = v___y_4099_;
goto v___jp_4086_;
}
else
{
lean_dec_ref(v___y_4099_);
lean_dec(v___y_4097_);
if (v___x_3967_ == 0)
{
lean_object* v___x_4103_; lean_object* v___x_4104_; 
lean_dec_ref(v___y_4095_);
v___x_4103_ = lean_box(0);
lean_inc(v_a_3570_);
lean_inc_ref(v_a_3569_);
v___x_4104_ = lean_apply_4(v___y_4094_, v___x_4103_, v_a_3569_, v_a_3570_, lean_box(0));
v___y_4030_ = v___y_4096_;
v___y_4031_ = v___y_4098_;
v___y_4032_ = v___x_4104_;
goto v___jp_4029_;
}
else
{
lean_object* v_toConstantVal_4105_; lean_object* v_name_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
v_toConstantVal_4105_ = lean_ctor_get(v___y_4095_, 0);
lean_inc_ref(v_toConstantVal_4105_);
lean_dec_ref(v___y_4095_);
v_name_4106_ = lean_ctor_get(v_toConstantVal_4105_, 0);
lean_inc(v_name_4106_);
lean_dec_ref(v_toConstantVal_4105_);
v___x_4107_ = lean_obj_once(&l_Lean_addDecl___closed__5, &l_Lean_addDecl___closed__5_once, _init_l_Lean_addDecl___closed__5);
v___x_4108_ = l_Lean_MessageData_ofName(v_name_4106_);
v___x_4109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4109_, 0, v___x_4107_);
lean_ctor_set(v___x_4109_, 1, v___x_4108_);
v___x_4110_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_4111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4111_, 0, v___x_4109_);
lean_ctor_set(v___x_4111_, 1, v___x_4110_);
v___x_4112_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3763_, v___x_4111_, v_a_3569_, v_a_3570_);
if (lean_obj_tag(v___x_4112_) == 0)
{
lean_object* v_a_4113_; lean_object* v___x_4114_; 
v_a_4113_ = lean_ctor_get(v___x_4112_, 0);
lean_inc(v_a_4113_);
lean_dec_ref(v___x_4112_);
lean_inc(v_a_3570_);
lean_inc_ref(v_a_3569_);
v___x_4114_ = lean_apply_4(v___y_4094_, v_a_4113_, v_a_3569_, v_a_3570_, lean_box(0));
v___y_4030_ = v___y_4096_;
v___y_4031_ = v___y_4098_;
v___y_4032_ = v___x_4114_;
goto v___jp_4029_;
}
else
{
lean_dec_ref(v___y_4094_);
v___y_4030_ = v___y_4096_;
v___y_4031_ = v___y_4098_;
v___y_4032_ = v___x_4112_;
goto v___jp_4029_;
}
}
}
}
v___jp_4115_:
{
lean_object* v___x_4116_; lean_object* v_a_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4266_; 
v___x_4116_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_a_3570_);
v_a_4117_ = lean_ctor_get(v___x_4116_, 0);
v_isSharedCheck_4266_ = !lean_is_exclusive(v___x_4116_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4119_ = v___x_4116_;
v_isShared_4120_ = v_isSharedCheck_4266_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_a_4117_);
lean_dec(v___x_4116_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4266_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v___x_4121_; uint8_t v___x_4122_; 
v___x_4121_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4122_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3624_, v___x_4121_);
if (v___x_4122_ == 0)
{
lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v_env_4125_; lean_object* v_nextMacroScope_4126_; lean_object* v_ngen_4127_; lean_object* v_auxDeclNGen_4128_; lean_object* v_traceState_4129_; lean_object* v_messages_4130_; lean_object* v_infoState_4131_; lean_object* v_snapshotTasks_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4180_; 
v___x_4123_ = lean_io_mono_nanos_now();
v___x_4124_ = lean_st_ref_take(v_a_3570_);
v_env_4125_ = lean_ctor_get(v___x_4124_, 0);
v_nextMacroScope_4126_ = lean_ctor_get(v___x_4124_, 1);
v_ngen_4127_ = lean_ctor_get(v___x_4124_, 2);
v_auxDeclNGen_4128_ = lean_ctor_get(v___x_4124_, 3);
v_traceState_4129_ = lean_ctor_get(v___x_4124_, 4);
v_messages_4130_ = lean_ctor_get(v___x_4124_, 6);
v_infoState_4131_ = lean_ctor_get(v___x_4124_, 7);
v_snapshotTasks_4132_ = lean_ctor_get(v___x_4124_, 8);
v_isSharedCheck_4180_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4180_ == 0)
{
lean_object* v_unused_4181_; 
v_unused_4181_ = lean_ctor_get(v___x_4124_, 5);
lean_dec(v_unused_4181_);
v___x_4134_ = v___x_4124_;
v_isShared_4135_ = v_isSharedCheck_4180_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_snapshotTasks_4132_);
lean_inc(v_infoState_4131_);
lean_inc(v_messages_4130_);
lean_inc(v_traceState_4129_);
lean_inc(v_auxDeclNGen_4128_);
lean_inc(v_ngen_4127_);
lean_inc(v_nextMacroScope_4126_);
lean_inc(v_env_4125_);
lean_dec(v___x_4124_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4180_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4140_; 
lean_inc(v_decl_3567_);
v___x_4136_ = l_Lean_Declaration_getNames(v_decl_3567_);
v___x_4137_ = l_List_foldl___at___00Lean_addDecl_spec__1(v_env_4125_, v___x_4136_);
v___x_4138_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2);
if (v_isShared_4135_ == 0)
{
lean_ctor_set(v___x_4134_, 5, v___x_4138_);
lean_ctor_set(v___x_4134_, 0, v___x_4137_);
v___x_4140_ = v___x_4134_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v___x_4137_);
lean_ctor_set(v_reuseFailAlloc_4179_, 1, v_nextMacroScope_4126_);
lean_ctor_set(v_reuseFailAlloc_4179_, 2, v_ngen_4127_);
lean_ctor_set(v_reuseFailAlloc_4179_, 3, v_auxDeclNGen_4128_);
lean_ctor_set(v_reuseFailAlloc_4179_, 4, v_traceState_4129_);
lean_ctor_set(v_reuseFailAlloc_4179_, 5, v___x_4138_);
lean_ctor_set(v_reuseFailAlloc_4179_, 6, v_messages_4130_);
lean_ctor_set(v_reuseFailAlloc_4179_, 7, v_infoState_4131_);
lean_ctor_set(v_reuseFailAlloc_4179_, 8, v_snapshotTasks_4132_);
v___x_4140_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___f_4145_; 
v___x_4141_ = lean_st_ref_set(v_a_3570_, v___x_4140_);
v___x_4142_ = lean_box(0);
v___x_4143_ = lean_box(v_hasTrace_3626_);
v___x_4144_ = lean_box(v___x_4122_);
lean_inc(v_decl_3567_);
v___f_4145_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__8___boxed), 12, 7);
lean_closure_set(v___f_4145_, 0, v_decl_3567_);
lean_closure_set(v___f_4145_, 1, v___x_3627_);
lean_closure_set(v___f_4145_, 2, v___x_4143_);
lean_closure_set(v___f_4145_, 3, v___x_4144_);
lean_closure_set(v___f_4145_, 4, v___x_4138_);
lean_closure_set(v___f_4145_, 5, v_cls_3763_);
lean_closure_set(v___f_4145_, 6, v___x_4142_);
switch(lean_obj_tag(v_decl_3567_))
{
case 2:
{
lean_object* v_val_4146_; lean_object* v___x_4147_; lean_object* v_env_4148_; lean_object* v___f_4149_; lean_object* v___x_4150_; lean_object* v___f_4151_; 
lean_del_object(v___x_4119_);
v_val_4146_ = lean_ctor_get(v_decl_3567_, 0);
lean_inc_ref_n(v_val_4146_, 3);
lean_dec_ref(v_decl_3567_);
v___x_4147_ = lean_st_ref_get(v_a_3570_);
v_env_4148_ = lean_ctor_get(v___x_4147_, 0);
lean_inc_ref(v_env_4148_);
lean_dec(v___x_4147_);
v___f_4149_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__5___boxed), 7, 2);
lean_closure_set(v___f_4149_, 0, v_val_4146_);
lean_closure_set(v___f_4149_, 1, v___f_4145_);
v___x_4150_ = lean_box(v___x_4122_);
lean_inc_ref(v___f_4149_);
v___f_4151_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__6___boxed), 7, 3);
lean_closure_set(v___f_4151_, 0, v_val_4146_);
lean_closure_set(v___f_4151_, 1, v___x_4150_);
lean_closure_set(v___f_4151_, 2, v___f_4149_);
if (v_forceExpose_3568_ == 0)
{
v___y_4094_ = v___f_4151_;
v___y_4095_ = v_val_4146_;
v___y_4096_ = v_a_4117_;
v___y_4097_ = v___x_4142_;
v___y_4098_ = v___x_4123_;
v___y_4099_ = v___f_4149_;
v___y_4100_ = v_env_4148_;
goto v___jp_4093_;
}
else
{
if (v___x_4122_ == 0)
{
lean_dec_ref(v___f_4151_);
lean_dec_ref(v_env_4148_);
lean_dec_ref(v_val_4146_);
v___y_4087_ = v_a_4117_;
v___y_4088_ = v___x_4142_;
v___y_4089_ = v___x_4123_;
v___y_4090_ = v___f_4149_;
goto v___jp_4086_;
}
else
{
v___y_4094_ = v___f_4151_;
v___y_4095_ = v_val_4146_;
v___y_4096_ = v_a_4117_;
v___y_4097_ = v___x_4142_;
v___y_4098_ = v___x_4123_;
v___y_4099_ = v___f_4149_;
v___y_4100_ = v_env_4148_;
goto v___jp_4093_;
}
}
}
case 1:
{
lean_object* v_val_4152_; lean_object* v___x_4153_; 
lean_del_object(v___x_4119_);
v_val_4152_ = lean_ctor_get(v_decl_3567_, 0);
lean_inc_ref(v_val_4152_);
lean_dec_ref(v_decl_3567_);
v___x_4153_ = l_Lean_addDecl___lam__4(v___f_4145_, v_cls_3763_, v___x_4142_, v___x_4122_, v_forceExpose_3568_, v_val_4152_, v_a_3569_, v_a_3570_);
v___y_4030_ = v_a_4117_;
v___y_4031_ = v___x_4123_;
v___y_4032_ = v___x_4153_;
goto v___jp_4029_;
}
case 5:
{
lean_object* v_defns_4154_; 
lean_del_object(v___x_4119_);
v_defns_4154_ = lean_ctor_get(v_decl_3567_, 0);
if (lean_obj_tag(v_defns_4154_) == 1)
{
lean_object* v_tail_4155_; 
v_tail_4155_ = lean_ctor_get(v_defns_4154_, 1);
if (lean_obj_tag(v_tail_4155_) == 0)
{
lean_object* v_head_4156_; lean_object* v___x_4157_; 
lean_inc_ref(v_defns_4154_);
lean_dec_ref(v_decl_3567_);
v_head_4156_ = lean_ctor_get(v_defns_4154_, 0);
lean_inc(v_head_4156_);
lean_dec_ref(v_defns_4154_);
v___x_4157_ = l_Lean_addDecl___lam__4(v___f_4145_, v_cls_3763_, v___x_4142_, v___x_4122_, v_forceExpose_3568_, v_head_4156_, v_a_3569_, v_a_3570_);
v___y_4030_ = v_a_4117_;
v___y_4031_ = v___x_4123_;
v___y_4032_ = v___x_4157_;
goto v___jp_4029_;
}
else
{
lean_object* v___x_4158_; 
lean_dec_ref(v___f_4145_);
lean_inc_ref(v_decl_3567_);
v___x_4158_ = l_Lean_addDecl___lam__3(v_decl_3567_, v_cls_3763_, v_decl_3567_, v_a_3569_, v_a_3570_);
lean_dec_ref(v_decl_3567_);
v___y_4030_ = v_a_4117_;
v___y_4031_ = v___x_4123_;
v___y_4032_ = v___x_4158_;
goto v___jp_4029_;
}
}
else
{
lean_object* v___x_4159_; 
lean_dec_ref(v___f_4145_);
lean_inc_ref(v_decl_3567_);
v___x_4159_ = l_Lean_addDecl___lam__3(v_decl_3567_, v_cls_3763_, v_decl_3567_, v_a_3569_, v_a_3570_);
lean_dec_ref(v_decl_3567_);
v___y_4030_ = v_a_4117_;
v___y_4031_ = v___x_4123_;
v___y_4032_ = v___x_4159_;
goto v___jp_4029_;
}
}
case 3:
{
lean_object* v_val_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v_env_4163_; lean_object* v_env_4164_; lean_object* v___f_4165_; lean_object* v___f_4166_; 
lean_del_object(v___x_4119_);
v_val_4160_ = lean_ctor_get(v_decl_3567_, 0);
lean_inc_ref_n(v_val_4160_, 3);
lean_dec_ref(v_decl_3567_);
v___x_4161_ = lean_st_ref_get(v_a_3570_);
v___x_4162_ = lean_st_ref_get(v_a_3570_);
v_env_4163_ = lean_ctor_get(v___x_4161_, 0);
lean_inc_ref(v_env_4163_);
lean_dec(v___x_4161_);
v_env_4164_ = lean_ctor_get(v___x_4162_, 0);
lean_inc_ref(v_env_4164_);
lean_dec(v___x_4162_);
v___f_4165_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__7___boxed), 7, 2);
lean_closure_set(v___f_4165_, 0, v_val_4160_);
lean_closure_set(v___f_4165_, 1, v___f_4145_);
lean_inc_ref(v___f_4165_);
v___f_4166_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__9___boxed), 6, 2);
lean_closure_set(v___f_4166_, 0, v_val_4160_);
lean_closure_set(v___f_4166_, 1, v___f_4165_);
if (v_forceExpose_3568_ == 0)
{
v___y_4074_ = v___x_4122_;
v___y_4075_ = v_a_4117_;
v___y_4076_ = v_env_4163_;
v___y_4077_ = v___x_4142_;
v___y_4078_ = v___x_4123_;
v___y_4079_ = v_val_4160_;
v___y_4080_ = v___f_4166_;
v___y_4081_ = v_env_4164_;
v___y_4082_ = v___f_4165_;
goto v___jp_4073_;
}
else
{
if (v___x_4122_ == 0)
{
lean_dec_ref(v___f_4166_);
lean_dec_ref(v_env_4164_);
lean_dec_ref(v_env_4163_);
lean_dec_ref(v_val_4160_);
v___y_4050_ = v_a_4117_;
v___y_4051_ = v___x_4142_;
v___y_4052_ = v___x_4123_;
v___y_4053_ = v___f_4165_;
goto v___jp_4049_;
}
else
{
v___y_4074_ = v___x_4122_;
v___y_4075_ = v_a_4117_;
v___y_4076_ = v_env_4163_;
v___y_4077_ = v___x_4142_;
v___y_4078_ = v___x_4123_;
v___y_4079_ = v_val_4160_;
v___y_4080_ = v___f_4166_;
v___y_4081_ = v_env_4164_;
v___y_4082_ = v___f_4165_;
goto v___jp_4073_;
}
}
}
case 0:
{
lean_object* v_val_4167_; lean_object* v_toConstantVal_4168_; lean_object* v_name_4169_; lean_object* v___x_4171_; 
lean_dec_ref(v___f_4145_);
v_val_4167_ = lean_ctor_get(v_decl_3567_, 0);
v_toConstantVal_4168_ = lean_ctor_get(v_val_4167_, 0);
v_name_4169_ = lean_ctor_get(v_toConstantVal_4168_, 0);
lean_inc_ref(v_val_4167_);
if (v_isShared_4120_ == 0)
{
lean_ctor_set(v___x_4119_, 0, v_val_4167_);
v___x_4171_ = v___x_4119_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v_val_4167_);
v___x_4171_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
uint8_t v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; 
v___x_4172_ = 2;
v___x_4173_ = lean_box(v___x_4172_);
v___x_4174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4171_);
lean_ctor_set(v___x_4174_, 1, v___x_4173_);
lean_inc(v_name_4169_);
v___x_4175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4175_, 0, v_name_4169_);
lean_ctor_set(v___x_4175_, 1, v___x_4174_);
v___x_4176_ = l_Lean_addDecl___lam__8(v_decl_3567_, v___x_3627_, v_hasTrace_3626_, v___x_4122_, v___x_4138_, v_cls_3763_, v___x_4142_, v___x_4175_, v___x_4142_, v_a_3569_, v_a_3570_);
v___y_4030_ = v_a_4117_;
v___y_4031_ = v___x_4123_;
v___y_4032_ = v___x_4176_;
goto v___jp_4029_;
}
}
default: 
{
lean_object* v___x_4178_; 
lean_dec_ref(v___f_4145_);
lean_del_object(v___x_4119_);
lean_inc(v_decl_3567_);
v___x_4178_ = l_Lean_addDecl___lam__3(v_decl_3567_, v_cls_3763_, v_decl_3567_, v_a_3569_, v_a_3570_);
lean_dec(v_decl_3567_);
v___y_4030_ = v_a_4117_;
v___y_4031_ = v___x_4123_;
v___y_4032_ = v___x_4178_;
goto v___jp_4029_;
}
}
}
}
}
else
{
lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v_env_4184_; lean_object* v_nextMacroScope_4185_; lean_object* v_ngen_4186_; lean_object* v_auxDeclNGen_4187_; lean_object* v_traceState_4188_; lean_object* v_messages_4189_; lean_object* v_infoState_4190_; lean_object* v_snapshotTasks_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4264_; 
v___x_4182_ = lean_io_get_num_heartbeats();
v___x_4183_ = lean_st_ref_take(v_a_3570_);
v_env_4184_ = lean_ctor_get(v___x_4183_, 0);
v_nextMacroScope_4185_ = lean_ctor_get(v___x_4183_, 1);
v_ngen_4186_ = lean_ctor_get(v___x_4183_, 2);
v_auxDeclNGen_4187_ = lean_ctor_get(v___x_4183_, 3);
v_traceState_4188_ = lean_ctor_get(v___x_4183_, 4);
v_messages_4189_ = lean_ctor_get(v___x_4183_, 6);
v_infoState_4190_ = lean_ctor_get(v___x_4183_, 7);
v_snapshotTasks_4191_ = lean_ctor_get(v___x_4183_, 8);
v_isSharedCheck_4264_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4264_ == 0)
{
lean_object* v_unused_4265_; 
v_unused_4265_ = lean_ctor_get(v___x_4183_, 5);
lean_dec(v_unused_4265_);
v___x_4193_ = v___x_4183_;
v_isShared_4194_ = v_isSharedCheck_4264_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_snapshotTasks_4191_);
lean_inc(v_infoState_4190_);
lean_inc(v_messages_4189_);
lean_inc(v_traceState_4188_);
lean_inc(v_auxDeclNGen_4187_);
lean_inc(v_ngen_4186_);
lean_inc(v_nextMacroScope_4185_);
lean_inc(v_env_4184_);
lean_dec(v___x_4183_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4264_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4199_; 
lean_inc(v_decl_3567_);
v___x_4195_ = l_Lean_Declaration_getNames(v_decl_3567_);
v___x_4196_ = l_List_foldl___at___00Lean_addDecl_spec__1(v_env_4184_, v___x_4195_);
v___x_4197_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2);
if (v_isShared_4194_ == 0)
{
lean_ctor_set(v___x_4193_, 5, v___x_4197_);
lean_ctor_set(v___x_4193_, 0, v___x_4196_);
v___x_4199_ = v___x_4193_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v___x_4196_);
lean_ctor_set(v_reuseFailAlloc_4263_, 1, v_nextMacroScope_4185_);
lean_ctor_set(v_reuseFailAlloc_4263_, 2, v_ngen_4186_);
lean_ctor_set(v_reuseFailAlloc_4263_, 3, v_auxDeclNGen_4187_);
lean_ctor_set(v_reuseFailAlloc_4263_, 4, v_traceState_4188_);
lean_ctor_set(v_reuseFailAlloc_4263_, 5, v___x_4197_);
lean_ctor_set(v_reuseFailAlloc_4263_, 6, v_messages_4189_);
lean_ctor_set(v_reuseFailAlloc_4263_, 7, v_infoState_4190_);
lean_ctor_set(v_reuseFailAlloc_4263_, 8, v_snapshotTasks_4191_);
v___x_4199_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___f_4203_; 
v___x_4200_ = lean_st_ref_set(v_a_3570_, v___x_4199_);
v___x_4201_ = lean_box(0);
v___x_4202_ = lean_box(v___x_4122_);
lean_inc(v_decl_3567_);
v___f_4203_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__13___boxed), 11, 6);
lean_closure_set(v___f_4203_, 0, v_decl_3567_);
lean_closure_set(v___f_4203_, 1, v___x_3627_);
lean_closure_set(v___f_4203_, 2, v___x_4202_);
lean_closure_set(v___f_4203_, 3, v_cls_3763_);
lean_closure_set(v___f_4203_, 4, v___x_4197_);
lean_closure_set(v___f_4203_, 5, v___x_4201_);
switch(lean_obj_tag(v_decl_3567_))
{
case 2:
{
lean_object* v_val_4204_; lean_object* v___x_4205_; lean_object* v_env_4206_; lean_object* v___f_4207_; 
lean_del_object(v___x_4119_);
v_val_4204_ = lean_ctor_get(v_decl_3567_, 0);
lean_inc_ref_n(v_val_4204_, 2);
lean_dec_ref(v_decl_3567_);
v___x_4205_ = lean_st_ref_get(v_a_3570_);
v_env_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc_ref(v_env_4206_);
lean_dec(v___x_4205_);
v___f_4207_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__5___boxed), 7, 2);
lean_closure_set(v___f_4207_, 0, v_val_4204_);
lean_closure_set(v___f_4207_, 1, v___f_4203_);
if (v_forceExpose_3568_ == 0)
{
if (v___x_4122_ == 0)
{
lean_dec_ref(v_env_4206_);
lean_dec_ref(v_val_4204_);
v___y_4001_ = v_a_4117_;
v___y_4002_ = v___x_4201_;
v___y_4003_ = v___f_4207_;
v___y_4004_ = v___x_4182_;
goto v___jp_4000_;
}
else
{
lean_object* v___x_4208_; uint8_t v_isModule_4209_; 
v___x_4208_ = l_Lean_Environment_header(v_env_4206_);
lean_dec_ref(v_env_4206_);
v_isModule_4209_ = lean_ctor_get_uint8(v___x_4208_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4208_);
if (v_isModule_4209_ == 0)
{
lean_dec_ref(v_val_4204_);
v___y_4001_ = v_a_4117_;
v___y_4002_ = v___x_4201_;
v___y_4003_ = v___f_4207_;
v___y_4004_ = v___x_4182_;
goto v___jp_4000_;
}
else
{
if (v___x_3967_ == 0)
{
lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4210_ = lean_box(0);
v___x_4211_ = l_Lean_addDecl___lam__12(v_val_4204_, v_forceExpose_3568_, v___f_4207_, v___x_4210_, v_a_3569_, v_a_3570_);
lean_dec_ref(v_val_4204_);
v___y_3981_ = v_a_4117_;
v___y_3982_ = v___x_4182_;
v___y_3983_ = v___x_4211_;
goto v___jp_3980_;
}
else
{
lean_object* v_toConstantVal_4212_; lean_object* v_name_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; 
v_toConstantVal_4212_ = lean_ctor_get(v_val_4204_, 0);
v_name_4213_ = lean_ctor_get(v_toConstantVal_4212_, 0);
v___x_4214_ = lean_obj_once(&l_Lean_addDecl___closed__5, &l_Lean_addDecl___closed__5_once, _init_l_Lean_addDecl___closed__5);
lean_inc(v_name_4213_);
v___x_4215_ = l_Lean_MessageData_ofName(v_name_4213_);
v___x_4216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4216_, 0, v___x_4214_);
lean_ctor_set(v___x_4216_, 1, v___x_4215_);
v___x_4217_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_4218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4218_, 0, v___x_4216_);
lean_ctor_set(v___x_4218_, 1, v___x_4217_);
v___x_4219_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3763_, v___x_4218_, v_a_3569_, v_a_3570_);
if (lean_obj_tag(v___x_4219_) == 0)
{
lean_object* v_a_4220_; lean_object* v___x_4221_; 
v_a_4220_ = lean_ctor_get(v___x_4219_, 0);
lean_inc(v_a_4220_);
lean_dec_ref(v___x_4219_);
v___x_4221_ = l_Lean_addDecl___lam__12(v_val_4204_, v_forceExpose_3568_, v___f_4207_, v_a_4220_, v_a_3569_, v_a_3570_);
lean_dec_ref(v_val_4204_);
v___y_3981_ = v_a_4117_;
v___y_3982_ = v___x_4182_;
v___y_3983_ = v___x_4221_;
goto v___jp_3980_;
}
else
{
lean_dec_ref(v___f_4207_);
lean_dec_ref(v_val_4204_);
v___y_3981_ = v_a_4117_;
v___y_3982_ = v___x_4182_;
v___y_3983_ = v___x_4219_;
goto v___jp_3980_;
}
}
}
}
}
else
{
lean_dec_ref(v_env_4206_);
lean_dec_ref(v_val_4204_);
v___y_4001_ = v_a_4117_;
v___y_4002_ = v___x_4201_;
v___y_4003_ = v___f_4207_;
v___y_4004_ = v___x_4182_;
goto v___jp_4000_;
}
}
case 1:
{
lean_object* v_val_4222_; lean_object* v___x_4223_; 
lean_del_object(v___x_4119_);
v_val_4222_ = lean_ctor_get(v_decl_3567_, 0);
lean_inc_ref(v_val_4222_);
lean_dec_ref(v_decl_3567_);
v___x_4223_ = l_Lean_addDecl___lam__10(v___f_4203_, v_forceExpose_3568_, v___x_4122_, v___x_4201_, v_cls_3763_, v_val_4222_, v_a_3569_, v_a_3570_);
v___y_3981_ = v_a_4117_;
v___y_3982_ = v___x_4182_;
v___y_3983_ = v___x_4223_;
goto v___jp_3980_;
}
case 5:
{
lean_object* v_defns_4224_; 
lean_del_object(v___x_4119_);
v_defns_4224_ = lean_ctor_get(v_decl_3567_, 0);
if (lean_obj_tag(v_defns_4224_) == 1)
{
lean_object* v_tail_4225_; 
v_tail_4225_ = lean_ctor_get(v_defns_4224_, 1);
if (lean_obj_tag(v_tail_4225_) == 0)
{
lean_object* v_head_4226_; lean_object* v___x_4227_; 
lean_inc_ref(v_defns_4224_);
lean_dec_ref(v_decl_3567_);
v_head_4226_ = lean_ctor_get(v_defns_4224_, 0);
lean_inc(v_head_4226_);
lean_dec_ref(v_defns_4224_);
v___x_4227_ = l_Lean_addDecl___lam__10(v___f_4203_, v_forceExpose_3568_, v___x_4122_, v___x_4201_, v_cls_3763_, v_head_4226_, v_a_3569_, v_a_3570_);
v___y_3981_ = v_a_4117_;
v___y_3982_ = v___x_4182_;
v___y_3983_ = v___x_4227_;
goto v___jp_3980_;
}
else
{
lean_object* v___x_4228_; 
lean_dec_ref(v___f_4203_);
lean_inc_ref(v_decl_3567_);
v___x_4228_ = l_Lean_addDecl___lam__3(v_decl_3567_, v_cls_3763_, v_decl_3567_, v_a_3569_, v_a_3570_);
lean_dec_ref(v_decl_3567_);
v___y_3981_ = v_a_4117_;
v___y_3982_ = v___x_4182_;
v___y_3983_ = v___x_4228_;
goto v___jp_3980_;
}
}
else
{
lean_object* v___x_4229_; 
lean_dec_ref(v___f_4203_);
lean_inc_ref(v_decl_3567_);
v___x_4229_ = l_Lean_addDecl___lam__3(v_decl_3567_, v_cls_3763_, v_decl_3567_, v_a_3569_, v_a_3570_);
lean_dec_ref(v_decl_3567_);
v___y_3981_ = v_a_4117_;
v___y_3982_ = v___x_4182_;
v___y_3983_ = v___x_4229_;
goto v___jp_3980_;
}
}
case 3:
{
lean_object* v_val_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v_env_4233_; lean_object* v_env_4234_; lean_object* v___f_4235_; 
lean_del_object(v___x_4119_);
v_val_4230_ = lean_ctor_get(v_decl_3567_, 0);
lean_inc_ref_n(v_val_4230_, 2);
lean_dec_ref(v_decl_3567_);
v___x_4231_ = lean_st_ref_get(v_a_3570_);
v___x_4232_ = lean_st_ref_get(v_a_3570_);
v_env_4233_ = lean_ctor_get(v___x_4231_, 0);
lean_inc_ref(v_env_4233_);
lean_dec(v___x_4231_);
v_env_4234_ = lean_ctor_get(v___x_4232_, 0);
lean_inc_ref(v_env_4234_);
lean_dec(v___x_4232_);
v___f_4235_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__7___boxed), 7, 2);
lean_closure_set(v___f_4235_, 0, v_val_4230_);
lean_closure_set(v___f_4235_, 1, v___f_4203_);
if (v_forceExpose_3568_ == 0)
{
if (v___x_4122_ == 0)
{
lean_dec_ref(v_env_4234_);
lean_dec_ref(v_env_4233_);
lean_dec_ref(v_val_4230_);
v___y_4008_ = v_a_4117_;
v___y_4009_ = v___x_4201_;
v___y_4010_ = v___x_4182_;
v___y_4011_ = v___f_4235_;
goto v___jp_4007_;
}
else
{
lean_object* v___x_4236_; uint8_t v_isModule_4237_; 
v___x_4236_ = l_Lean_Environment_header(v_env_4233_);
lean_dec_ref(v_env_4233_);
v_isModule_4237_ = lean_ctor_get_uint8(v___x_4236_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4236_);
if (v_isModule_4237_ == 0)
{
lean_dec_ref(v_env_4234_);
lean_dec_ref(v_val_4230_);
v___y_4008_ = v_a_4117_;
v___y_4009_ = v___x_4201_;
v___y_4010_ = v___x_4182_;
v___y_4011_ = v___f_4235_;
goto v___jp_4007_;
}
else
{
uint8_t v_isExporting_4238_; 
v_isExporting_4238_ = lean_ctor_get_uint8(v_env_4234_, sizeof(void*)*8);
lean_dec_ref(v_env_4234_);
if (v_isExporting_4238_ == 0)
{
if (v___x_3967_ == 0)
{
lean_object* v___x_4239_; lean_object* v___x_4240_; 
v___x_4239_ = lean_box(0);
v___x_4240_ = l_Lean_addDecl___lam__9(v_val_4230_, v___f_4235_, v___x_4239_, v_a_3569_, v_a_3570_);
lean_dec_ref(v_val_4230_);
v___y_3981_ = v_a_4117_;
v___y_3982_ = v___x_4182_;
v___y_3983_ = v___x_4240_;
goto v___jp_3980_;
}
else
{
lean_object* v_toConstantVal_4241_; lean_object* v_name_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; 
v_toConstantVal_4241_ = lean_ctor_get(v_val_4230_, 0);
v_name_4242_ = lean_ctor_get(v_toConstantVal_4241_, 0);
v___x_4243_ = lean_obj_once(&l_Lean_addDecl___closed__3, &l_Lean_addDecl___closed__3_once, _init_l_Lean_addDecl___closed__3);
lean_inc(v_name_4242_);
v___x_4244_ = l_Lean_MessageData_ofName(v_name_4242_);
v___x_4245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4245_, 0, v___x_4243_);
lean_ctor_set(v___x_4245_, 1, v___x_4244_);
v___x_4246_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_4247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4247_, 0, v___x_4245_);
lean_ctor_set(v___x_4247_, 1, v___x_4246_);
v___x_4248_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3763_, v___x_4247_, v_a_3569_, v_a_3570_);
if (lean_obj_tag(v___x_4248_) == 0)
{
lean_object* v_a_4249_; lean_object* v___x_4250_; 
v_a_4249_ = lean_ctor_get(v___x_4248_, 0);
lean_inc(v_a_4249_);
lean_dec_ref(v___x_4248_);
v___x_4250_ = l_Lean_addDecl___lam__9(v_val_4230_, v___f_4235_, v_a_4249_, v_a_3569_, v_a_3570_);
lean_dec_ref(v_val_4230_);
v___y_3981_ = v_a_4117_;
v___y_3982_ = v___x_4182_;
v___y_3983_ = v___x_4250_;
goto v___jp_3980_;
}
else
{
lean_dec_ref(v___f_4235_);
lean_dec_ref(v_val_4230_);
v___y_3981_ = v_a_4117_;
v___y_3982_ = v___x_4182_;
v___y_3983_ = v___x_4248_;
goto v___jp_3980_;
}
}
}
else
{
lean_dec_ref(v_val_4230_);
v___y_4008_ = v_a_4117_;
v___y_4009_ = v___x_4201_;
v___y_4010_ = v___x_4182_;
v___y_4011_ = v___f_4235_;
goto v___jp_4007_;
}
}
}
}
else
{
lean_dec_ref(v_env_4234_);
lean_dec_ref(v_env_4233_);
lean_dec_ref(v_val_4230_);
v___y_4008_ = v_a_4117_;
v___y_4009_ = v___x_4201_;
v___y_4010_ = v___x_4182_;
v___y_4011_ = v___f_4235_;
goto v___jp_4007_;
}
}
case 0:
{
lean_object* v_val_4251_; lean_object* v_toConstantVal_4252_; lean_object* v_name_4253_; lean_object* v___x_4255_; 
lean_dec_ref(v___f_4203_);
v_val_4251_ = lean_ctor_get(v_decl_3567_, 0);
v_toConstantVal_4252_ = lean_ctor_get(v_val_4251_, 0);
v_name_4253_ = lean_ctor_get(v_toConstantVal_4252_, 0);
lean_inc_ref(v_val_4251_);
if (v_isShared_4120_ == 0)
{
lean_ctor_set(v___x_4119_, 0, v_val_4251_);
v___x_4255_ = v___x_4119_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v_val_4251_);
v___x_4255_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
uint8_t v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; 
v___x_4256_ = 2;
v___x_4257_ = lean_box(v___x_4256_);
v___x_4258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4258_, 0, v___x_4255_);
lean_ctor_set(v___x_4258_, 1, v___x_4257_);
lean_inc(v_name_4253_);
v___x_4259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4259_, 0, v_name_4253_);
lean_ctor_set(v___x_4259_, 1, v___x_4258_);
v___x_4260_ = l_Lean_addDecl___lam__13(v_decl_3567_, v___x_3627_, v___x_4122_, v_cls_3763_, v___x_4197_, v___x_4201_, v___x_4259_, v___x_4201_, v_a_3569_, v_a_3570_);
v___y_3981_ = v_a_4117_;
v___y_3982_ = v___x_4182_;
v___y_3983_ = v___x_4260_;
goto v___jp_3980_;
}
}
default: 
{
lean_object* v___x_4262_; 
lean_dec_ref(v___f_4203_);
lean_del_object(v___x_4119_);
lean_inc(v_decl_3567_);
v___x_4262_ = l_Lean_addDecl___lam__3(v_decl_3567_, v_cls_3763_, v_decl_3567_, v_a_3569_, v_a_3570_);
lean_dec(v_decl_3567_);
v___y_3981_ = v_a_4117_;
v___y_3982_ = v___x_4182_;
v___y_3983_ = v___x_4262_;
goto v___jp_3980_;
}
}
}
}
}
}
}
}
v___jp_3572_:
{
lean_object* v___x_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3583_; 
v___x_3576_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3574_, v___y_3573_);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3583_ == 0)
{
lean_object* v_unused_3584_; 
v_unused_3584_ = lean_ctor_get(v___x_3576_, 0);
lean_dec(v_unused_3584_);
v___x_3578_ = v___x_3576_;
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
else
{
lean_dec(v___x_3576_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3581_; 
if (v_isShared_3579_ == 0)
{
lean_ctor_set_tag(v___x_3578_, 1);
lean_ctor_set(v___x_3578_, 0, v_a_3575_);
v___x_3581_ = v___x_3578_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_a_3575_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
v___jp_3585_:
{
lean_object* v___x_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3596_; 
v___x_3589_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3587_, v___y_3586_);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3596_ == 0)
{
lean_object* v_unused_3597_; 
v_unused_3597_ = lean_ctor_get(v___x_3589_, 0);
lean_dec(v_unused_3597_);
v___x_3591_ = v___x_3589_;
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
else
{
lean_dec(v___x_3589_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3594_; 
if (v_isShared_3592_ == 0)
{
lean_ctor_set(v___x_3591_, 0, v_a_3588_);
v___x_3594_ = v___x_3591_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_a_3588_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
v___jp_3598_:
{
lean_object* v___x_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3609_; 
v___x_3602_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3599_, v___y_3600_);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3609_ == 0)
{
lean_object* v_unused_3610_; 
v_unused_3610_ = lean_ctor_get(v___x_3602_, 0);
lean_dec(v_unused_3610_);
v___x_3604_ = v___x_3602_;
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
else
{
lean_dec(v___x_3602_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3607_; 
if (v_isShared_3605_ == 0)
{
lean_ctor_set(v___x_3604_, 0, v_a_3601_);
v___x_3607_ = v___x_3604_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_a_3601_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
v___jp_3611_:
{
lean_object* v___x_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
v___x_3615_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3612_, v___y_3613_);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3622_ == 0)
{
lean_object* v_unused_3623_; 
v_unused_3623_ = lean_ctor_get(v___x_3615_, 0);
lean_dec(v_unused_3623_);
v___x_3617_ = v___x_3615_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_dec(v___x_3615_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3620_; 
if (v_isShared_3618_ == 0)
{
lean_ctor_set_tag(v___x_3617_, 1);
lean_ctor_set(v___x_3617_, 0, v_a_3614_);
v___x_3620_ = v___x_3617_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3614_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
v___jp_3628_:
{
lean_object* v___x_3640_; 
lean_inc_ref(v___y_3638_);
v___x_3640_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3633_, v___y_3638_, v___y_3632_, v___y_3639_);
if (lean_obj_tag(v___x_3640_) == 0)
{
lean_object* v___x_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3687_; 
lean_dec_ref(v___x_3640_);
lean_inc_ref(v___y_3630_);
v___x_3641_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3630_, v___y_3631_);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3687_ == 0)
{
lean_object* v_unused_3688_; 
v_unused_3688_ = lean_ctor_get(v___x_3641_, 0);
lean_dec(v_unused_3688_);
v___x_3643_ = v___x_3641_;
v_isShared_3644_ = v_isSharedCheck_3687_;
goto v_resetjp_3642_;
}
else
{
lean_dec(v___x_3641_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3687_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v_options_3645_; lean_object* v___x_3646_; uint8_t v___x_3647_; 
v_options_3645_ = lean_ctor_get(v___y_3636_, 2);
v___x_3646_ = l_Lean_Elab_async;
v___x_3647_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3645_, v___x_3646_);
if (v___x_3647_ == 0)
{
lean_object* v___x_3648_; lean_object* v_r_3649_; 
lean_del_object(v___x_3643_);
lean_dec_ref(v___y_3637_);
lean_dec_ref(v___y_3634_);
v___x_3648_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3638_, v___y_3631_);
lean_dec_ref(v___x_3648_);
v_r_3649_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3567_, v___y_3636_, v___y_3631_);
if (lean_obj_tag(v_r_3649_) == 0)
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3659_; 
v_a_3650_ = lean_ctor_get(v_r_3649_, 0);
v_isSharedCheck_3659_ = !lean_is_exclusive(v_r_3649_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3652_ = v_r_3649_;
v_isShared_3653_ = v_isSharedCheck_3659_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v_r_3649_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3659_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3655_; 
lean_inc(v_a_3650_);
if (v_isShared_3653_ == 0)
{
lean_ctor_set_tag(v___x_3652_, 1);
v___x_3655_ = v___x_3652_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_a_3650_);
v___x_3655_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
lean_object* v___x_3656_; 
v___x_3656_ = lean_apply_2(v___y_3629_, v___x_3655_, lean_box(0));
if (lean_obj_tag(v___x_3656_) == 0)
{
lean_dec_ref(v___x_3656_);
v___y_3599_ = v___y_3630_;
v___y_3600_ = v___y_3631_;
v_a_3601_ = v_a_3650_;
goto v___jp_3598_;
}
else
{
lean_object* v_a_3657_; 
lean_dec(v_a_3650_);
v_a_3657_ = lean_ctor_get(v___x_3656_, 0);
lean_inc(v_a_3657_);
lean_dec_ref(v___x_3656_);
v___y_3612_ = v___y_3630_;
v___y_3613_ = v___y_3631_;
v_a_3614_ = v_a_3657_;
goto v___jp_3611_;
}
}
}
}
else
{
lean_object* v_a_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; 
v_a_3660_ = lean_ctor_get(v_r_3649_, 0);
lean_inc(v_a_3660_);
lean_dec_ref(v_r_3649_);
v___x_3661_ = lean_box(0);
v___x_3662_ = lean_apply_2(v___y_3629_, v___x_3661_, lean_box(0));
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_dec_ref(v___x_3662_);
v___y_3612_ = v___y_3630_;
v___y_3613_ = v___y_3631_;
v_a_3614_ = v_a_3660_;
goto v___jp_3611_;
}
else
{
lean_object* v_a_3663_; 
lean_dec(v_a_3660_);
v_a_3663_ = lean_ctor_get(v___x_3662_, 0);
lean_inc(v_a_3663_);
lean_dec_ref(v___x_3662_);
v___y_3612_ = v___y_3630_;
v___y_3613_ = v___y_3631_;
v_a_3614_ = v_a_3663_;
goto v___jp_3611_;
}
}
}
else
{
lean_object* v___x_3664_; lean_object* v___x_3666_; 
lean_dec_ref(v___y_3638_);
lean_dec_ref(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v_decl_3567_);
v___x_3664_ = l_IO_CancelToken_new();
if (v_isShared_3644_ == 0)
{
lean_ctor_set_tag(v___x_3643_, 1);
lean_ctor_set(v___x_3643_, 0, v___x_3664_);
v___x_3666_ = v___x_3643_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v___x_3664_);
v___x_3666_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3667_ = ((lean_object*)(l_Lean_addDecl___closed__0));
v___x_3668_ = l_Lean_Name_toString(v___x_3667_, v___y_3635_);
lean_inc_ref(v___x_3666_);
v___x_3669_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3634_, v___x_3666_, v___x_3668_, v___y_3636_, v___y_3631_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3670_; lean_object* v_checked_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
lean_inc(v_a_3670_);
lean_dec_ref(v___x_3669_);
v_checked_3671_ = lean_ctor_get(v___y_3637_, 2);
lean_inc_ref(v_checked_3671_);
lean_dec_ref(v___y_3637_);
v___x_3672_ = lean_unsigned_to_nat(0u);
v___x_3673_ = lean_io_map_task(v_a_3670_, v_checked_3671_, v___x_3672_, v_hasTrace_3626_);
v___x_3674_ = lean_box(0);
v___x_3675_ = lean_box(2);
v___x_3676_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3674_);
lean_ctor_set(v___x_3676_, 1, v___x_3675_);
lean_ctor_set(v___x_3676_, 2, v___x_3666_);
lean_ctor_set(v___x_3676_, 3, v___x_3673_);
v___x_3677_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3676_, v___y_3631_);
return v___x_3677_;
}
else
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3685_; 
lean_dec_ref(v___x_3666_);
lean_dec_ref(v___y_3637_);
v_a_3678_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3680_ = v___x_3669_;
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3669_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3683_; 
if (v_isShared_3681_ == 0)
{
v___x_3683_ = v___x_3680_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3701_; 
lean_dec_ref(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec_ref(v___y_3634_);
lean_dec_ref(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v_decl_3567_);
v_a_3689_ = lean_ctor_get(v___x_3640_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3640_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3691_ = v___x_3640_;
v_isShared_3692_ = v_isSharedCheck_3701_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v___x_3640_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3701_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v_ref_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3699_; 
v_ref_3693_ = lean_ctor_get(v___y_3636_, 5);
v___x_3694_ = lean_io_error_to_string(v_a_3689_);
v___x_3695_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3694_);
v___x_3696_ = l_Lean_MessageData_ofFormat(v___x_3695_);
lean_inc(v_ref_3693_);
v___x_3697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3697_, 0, v_ref_3693_);
lean_ctor_set(v___x_3697_, 1, v___x_3696_);
if (v_isShared_3692_ == 0)
{
lean_ctor_set(v___x_3691_, 0, v___x_3697_);
v___x_3699_ = v___x_3691_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v___x_3697_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
}
v___jp_3702_:
{
uint8_t v___x_3713_; lean_object* v___x_3714_; 
v___x_3713_ = 1;
lean_inc_ref(v___y_3705_);
v___x_3714_ = l_Lean_Environment_addConstAsync(v___y_3705_, v___y_3707_, v___y_3709_, v___y_3712_, v_hasTrace_3626_, v___x_3713_);
if (lean_obj_tag(v___x_3714_) == 0)
{
lean_object* v_a_3715_; lean_object* v_mainEnv_3716_; lean_object* v_asyncEnv_3717_; lean_object* v___f_3718_; lean_object* v___f_3719_; lean_object* v___x_3720_; 
v_a_3715_ = lean_ctor_get(v___x_3714_, 0);
lean_inc_n(v_a_3715_, 3);
lean_dec_ref(v___x_3714_);
v_mainEnv_3716_ = lean_ctor_get(v_a_3715_, 0);
lean_inc_ref(v_mainEnv_3716_);
v_asyncEnv_3717_ = lean_ctor_get(v_a_3715_, 1);
lean_inc_ref_n(v_asyncEnv_3717_, 2);
lean_inc_ref(v___y_3704_);
lean_inc(v___y_3703_);
v___f_3718_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3718_, 0, v___y_3703_);
lean_closure_set(v___f_3718_, 1, v_a_3715_);
lean_closure_set(v___f_3718_, 2, v___y_3704_);
lean_inc(v_decl_3567_);
v___f_3719_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3719_, 0, v_asyncEnv_3717_);
lean_closure_set(v___f_3719_, 1, v_a_3715_);
lean_closure_set(v___f_3719_, 2, v_decl_3567_);
v___x_3720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3720_, 0, v___y_3710_);
if (lean_obj_tag(v___y_3708_) == 0)
{
lean_inc_ref(v___x_3720_);
v___y_3629_ = v___f_3718_;
v___y_3630_ = v_mainEnv_3716_;
v___y_3631_ = v___y_3706_;
v___y_3632_ = v___x_3720_;
v___y_3633_ = v_a_3715_;
v___y_3634_ = v___f_3719_;
v___y_3635_ = v___x_3713_;
v___y_3636_ = v___y_3711_;
v___y_3637_ = v___y_3705_;
v___y_3638_ = v_asyncEnv_3717_;
v___y_3639_ = v___x_3720_;
goto v___jp_3628_;
}
else
{
v___y_3629_ = v___f_3718_;
v___y_3630_ = v_mainEnv_3716_;
v___y_3631_ = v___y_3706_;
v___y_3632_ = v___x_3720_;
v___y_3633_ = v_a_3715_;
v___y_3634_ = v___f_3719_;
v___y_3635_ = v___x_3713_;
v___y_3636_ = v___y_3711_;
v___y_3637_ = v___y_3705_;
v___y_3638_ = v_asyncEnv_3717_;
v___y_3639_ = v___y_3708_;
goto v___jp_3628_;
}
}
else
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3733_; 
lean_dec_ref(v___y_3710_);
lean_dec(v___y_3708_);
lean_dec_ref(v___y_3705_);
lean_dec(v_decl_3567_);
v_a_3721_ = lean_ctor_get(v___x_3714_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3714_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3723_ = v___x_3714_;
v_isShared_3724_ = v_isSharedCheck_3733_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3714_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3733_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v_ref_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3731_; 
v_ref_3725_ = lean_ctor_get(v___y_3711_, 5);
v___x_3726_ = lean_io_error_to_string(v_a_3721_);
v___x_3727_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3726_);
v___x_3728_ = l_Lean_MessageData_ofFormat(v___x_3727_);
lean_inc(v_ref_3725_);
v___x_3729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3729_, 0, v_ref_3725_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 0, v___x_3729_);
v___x_3731_ = v___x_3723_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(1, 1, 0);
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
}
v___jp_3734_:
{
lean_object* v___x_3741_; 
v___x_3741_ = lean_st_ref_get(v___y_3740_);
if (lean_obj_tag(v_exportedInfo_x3f_3738_) == 0)
{
lean_object* v_env_3742_; lean_object* v___x_3743_; 
v_env_3742_ = lean_ctor_get(v___x_3741_, 0);
lean_inc_ref(v_env_3742_);
lean_dec(v___x_3741_);
v___x_3743_ = lean_box(0);
v___y_3703_ = v___y_3740_;
v___y_3704_ = v___y_3739_;
v___y_3705_ = v_env_3742_;
v___y_3706_ = v___y_3740_;
v___y_3707_ = v___y_3735_;
v___y_3708_ = v_exportedInfo_x3f_3738_;
v___y_3709_ = v___y_3736_;
v___y_3710_ = v___y_3737_;
v___y_3711_ = v___y_3739_;
v___y_3712_ = v___x_3743_;
goto v___jp_3702_;
}
else
{
lean_object* v_env_3744_; lean_object* v_val_3745_; uint8_t v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; 
v_env_3744_ = lean_ctor_get(v___x_3741_, 0);
lean_inc_ref(v_env_3744_);
lean_dec(v___x_3741_);
v_val_3745_ = lean_ctor_get(v_exportedInfo_x3f_3738_, 0);
v___x_3746_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3745_);
v___x_3747_ = lean_box(v___x_3746_);
v___x_3748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3748_, 0, v___x_3747_);
v___y_3703_ = v___y_3740_;
v___y_3704_ = v___y_3739_;
v___y_3705_ = v_env_3744_;
v___y_3706_ = v___y_3740_;
v___y_3707_ = v___y_3735_;
v___y_3708_ = v_exportedInfo_x3f_3738_;
v___y_3709_ = v___y_3736_;
v___y_3710_ = v___y_3737_;
v___y_3711_ = v___y_3739_;
v___y_3712_ = v___x_3748_;
goto v___jp_3702_;
}
}
v___jp_3749_:
{
lean_object* v___x_3755_; 
lean_inc_ref(v___y_3752_);
v___x_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3755_, 0, v___y_3752_);
v___y_3735_ = v___y_3750_;
v___y_3736_ = v___y_3751_;
v___y_3737_ = v___y_3752_;
v_exportedInfo_x3f_3738_ = v___x_3755_;
v___y_3739_ = v___y_3753_;
v___y_3740_ = v___y_3754_;
goto v___jp_3734_;
}
v___jp_3756_:
{
lean_object* v___x_3762_; 
lean_inc_ref(v___y_3759_);
v___x_3762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3762_, 0, v___y_3759_);
v___y_3735_ = v___y_3757_;
v___y_3736_ = v___y_3758_;
v___y_3737_ = v___y_3759_;
v_exportedInfo_x3f_3738_ = v___x_3762_;
v___y_3739_ = v___y_3760_;
v___y_3740_ = v___y_3761_;
goto v___jp_3734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___boxed(lean_object* v_decl_4649_, lean_object* v_forceExpose_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_){
_start:
{
uint8_t v_forceExpose_boxed_4654_; lean_object* v_res_4655_; 
v_forceExpose_boxed_4654_ = lean_unbox(v_forceExpose_4650_);
v_res_4655_ = l_Lean_addDecl(v_decl_4649_, v_forceExpose_boxed_4654_, v_a_4651_, v_a_4652_);
lean_dec(v_a_4652_);
lean_dec_ref(v_a_4651_);
return v_res_4655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_addDecl_spec__2(lean_object* v_opt_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_){
_start:
{
lean_object* v___x_4660_; 
v___x_4660_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__2___redArg(v_opt_4656_, v___y_4657_);
return v___x_4660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_addDecl_spec__2___boxed(lean_object* v_opt_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_){
_start:
{
lean_object* v_res_4665_; 
v_res_4665_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__2(v_opt_4661_, v___y_4662_, v___y_4663_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4662_);
lean_dec_ref(v_opt_4661_);
return v_res_4665_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object* v_decl_4666_, uint8_t v_logCompileErrors_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_){
_start:
{
uint8_t v___x_4671_; lean_object* v___x_4672_; 
v___x_4671_ = 0;
lean_inc(v_decl_4666_);
v___x_4672_ = l_Lean_addDecl(v_decl_4666_, v___x_4671_, v_a_4668_, v_a_4669_);
if (lean_obj_tag(v___x_4672_) == 0)
{
lean_object* v___x_4673_; 
lean_dec_ref(v___x_4672_);
v___x_4673_ = l_Lean_compileDecl(v_decl_4666_, v_logCompileErrors_4667_, v_a_4668_, v_a_4669_);
return v___x_4673_;
}
else
{
lean_dec(v_decl_4666_);
return v___x_4672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___boxed(lean_object* v_decl_4674_, lean_object* v_logCompileErrors_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_){
_start:
{
uint8_t v_logCompileErrors_boxed_4679_; lean_object* v_res_4680_; 
v_logCompileErrors_boxed_4679_ = lean_unbox(v_logCompileErrors_4675_);
v_res_4680_ = l_Lean_addAndCompile(v_decl_4674_, v_logCompileErrors_boxed_4679_, v_a_4676_, v_a_4677_);
lean_dec(v_a_4677_);
lean_dec_ref(v_a_4676_);
return v_res_4680_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sorry(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectAxioms(uint8_t builtin);
lean_object* runtime_initialize_Lean_OriginalConstKind(uint8_t builtin);
lean_object* runtime_initialize_Lean_OriginalConstKind(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sorry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectAxioms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_OriginalConstKind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_OriginalConstKind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_warn_sorry = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_warn_sorry);
lean_dec_ref(res);
res = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_AddDecl(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sorry(uint8_t builtin);
lean_object* initialize_Lean_Util_CollectAxioms(uint8_t builtin);
lean_object* initialize_Lean_OriginalConstKind(uint8_t builtin);
lean_object* initialize_Lean_OriginalConstKind(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_AddDecl(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sorry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectAxioms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_OriginalConstKind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_OriginalConstKind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_AddDecl(builtin);
}
#ifdef __cplusplus
}
#endif
