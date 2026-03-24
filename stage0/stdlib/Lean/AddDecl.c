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
extern lean_object* l_Lean_Meta_instInhabitedConfigWithKey___private__1;
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
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "typechecking declarations "};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__0 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__4_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0;
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_addDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "exporting theorem "};
static const lean_object* l_Lean_addDecl___closed__1 = (const lean_object*)&l_Lean_addDecl___closed__1_value;
static lean_once_cell_t l_Lean_addDecl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addDecl___closed__2;
static const lean_string_object l_Lean_addDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "exporting opaque "};
static const lean_object* l_Lean_addDecl___closed__3 = (const lean_object*)&l_Lean_addDecl___closed__3_value;
static lean_once_cell_t l_Lean_addDecl___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addDecl___closed__4;
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
lean_inc(v_name_76_);
v___x_87_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_87_, 0, v_name_76_);
lean_ctor_set(v___x_87_, 1, v_ref_78_);
lean_ctor_set(v___x_87_, 2, v___x_85_);
lean_ctor_set(v___x_87_, 3, v_descr_81_);
lean_inc(v_name_76_);
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
uint8_t v___y_16390__boxed_229_; uint8_t v_suppressElabErrors_boxed_230_; uint8_t v_res_231_; lean_object* v_r_232_; 
v___y_16390__boxed_229_ = lean_unbox(v___y_226_);
v_suppressElabErrors_boxed_230_ = lean_unbox(v_suppressElabErrors_227_);
v_res_231_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(v___y_16390__boxed_229_, v_suppressElabErrors_boxed_230_, v_x_228_);
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
uint8_t v___y_278_; uint8_t v___y_279_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v___y_282_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_314_; uint8_t v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; uint8_t v___y_318_; lean_object* v___y_319_; uint8_t v___y_320_; lean_object* v___y_321_; lean_object* v___y_339_; uint8_t v___y_340_; uint8_t v___y_341_; lean_object* v___y_342_; lean_object* v___y_343_; lean_object* v___y_344_; uint8_t v___y_345_; lean_object* v___y_346_; lean_object* v___y_350_; lean_object* v___y_351_; uint8_t v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; uint8_t v___y_355_; uint8_t v___y_356_; uint8_t v___x_361_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; uint8_t v___y_367_; uint8_t v___y_368_; uint8_t v___y_369_; uint8_t v___y_371_; uint8_t v___x_386_; 
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
lean_inc(v_currNamespace_288_);
v_openDecls_289_ = lean_ctor_get(v___y_285_, 7);
lean_inc(v_openDecls_289_);
lean_dec_ref(v___y_285_);
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
v___x_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_302_, 0, v_currNamespace_288_);
lean_ctor_set(v___x_302_, 1, v_openDecls_289_);
v___x_303_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v___y_281_);
v___x_304_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_304_, 0, v___y_280_);
lean_ctor_set(v___x_304_, 1, v___y_284_);
lean_ctor_set(v___x_304_, 2, v___y_283_);
lean_ctor_set(v___x_304_, 3, v___y_282_);
lean_ctor_set(v___x_304_, 4, v___x_303_);
lean_ctor_set_uint8(v___x_304_, sizeof(void*)*5, v___y_279_);
lean_ctor_set_uint8(v___x_304_, sizeof(void*)*5 + 1, v___y_278_);
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
lean_inc_ref(v___y_319_);
v___x_328_ = l_Lean_FileMap_toPosition(v___y_319_, v___y_316_);
lean_dec(v___y_316_);
v___x_329_ = l_Lean_FileMap_toPosition(v___y_319_, v___y_321_);
lean_dec(v___y_321_);
v___x_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
v___x_331_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
if (v___y_320_ == 0)
{
lean_del_object(v___x_326_);
lean_dec_ref(v___y_314_);
v___y_278_ = v___y_315_;
v___y_279_ = v___y_318_;
v___y_280_ = v___y_317_;
v___y_281_ = v_a_324_;
v___y_282_ = v___x_331_;
v___y_283_ = v___x_330_;
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
lean_dec_ref(v___y_317_);
lean_dec_ref(v___y_274_);
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
v___y_278_ = v___y_315_;
v___y_279_ = v___y_318_;
v___y_280_ = v___y_317_;
v___y_281_ = v_a_324_;
v___y_282_ = v___x_331_;
v___y_283_ = v___x_330_;
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
v___x_347_ = l_Lean_Syntax_getTailPos_x3f(v___y_343_, v___y_341_);
lean_dec(v___y_343_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_inc(v___y_346_);
v___y_314_ = v___y_339_;
v___y_315_ = v___y_340_;
v___y_316_ = v___y_346_;
v___y_317_ = v___y_342_;
v___y_318_ = v___y_341_;
v___y_319_ = v___y_344_;
v___y_320_ = v___y_345_;
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
v___y_316_ = v___y_346_;
v___y_317_ = v___y_342_;
v___y_318_ = v___y_341_;
v___y_319_ = v___y_344_;
v___y_320_ = v___y_345_;
v___y_321_ = v_val_348_;
goto v___jp_313_;
}
}
v___jp_349_:
{
lean_object* v_ref_357_; lean_object* v___x_358_; 
v_ref_357_ = l_Lean_replaceRef(v_ref_270_, v___y_353_);
lean_dec(v___y_353_);
v___x_358_ = l_Lean_Syntax_getPos_x3f(v_ref_357_, v___y_352_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v___x_359_; 
v___x_359_ = lean_unsigned_to_nat(0u);
v___y_339_ = v___y_350_;
v___y_340_ = v___y_356_;
v___y_341_ = v___y_352_;
v___y_342_ = v___y_351_;
v___y_343_ = v_ref_357_;
v___y_344_ = v___y_354_;
v___y_345_ = v___y_355_;
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
v___y_340_ = v___y_356_;
v___y_341_ = v___y_352_;
v___y_342_ = v___y_351_;
v___y_343_ = v_ref_357_;
v___y_344_ = v___y_354_;
v___y_345_ = v___y_355_;
v___y_346_ = v_val_360_;
goto v___jp_338_;
}
}
v___jp_362_:
{
if (v___y_369_ == 0)
{
v___y_350_ = v___y_366_;
v___y_351_ = v___y_364_;
v___y_352_ = v___y_368_;
v___y_353_ = v___y_363_;
v___y_354_ = v___y_365_;
v___y_355_ = v___y_367_;
v___y_356_ = v_severity_272_;
goto v___jp_349_;
}
else
{
v___y_350_ = v___y_366_;
v___y_351_ = v___y_364_;
v___y_352_ = v___y_368_;
v___y_353_ = v___y_363_;
v___y_354_ = v___y_365_;
v___y_355_ = v___y_367_;
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
lean_inc_ref(v_fileMap_373_);
lean_inc_ref(v_fileName_372_);
lean_inc(v_ref_375_);
v___y_363_ = v_ref_375_;
v___y_364_ = v_fileName_372_;
v___y_365_ = v_fileMap_373_;
v___y_366_ = v___f_379_;
v___y_367_ = v_suppressElabErrors_376_;
v___y_368_ = v___y_371_;
v___y_369_ = v___x_381_;
goto v___jp_362_;
}
else
{
lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_382_ = l_Lean_warningAsError;
v___x_383_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_374_, v___x_382_);
lean_inc_ref(v_fileMap_373_);
lean_inc_ref(v_fileName_372_);
lean_inc(v_ref_375_);
v___y_363_ = v_ref_375_;
v___y_364_ = v_fileName_372_;
v___y_365_ = v_fileMap_373_;
v___y_366_ = v___f_379_;
v___y_367_ = v_suppressElabErrors_376_;
v___y_368_ = v___y_371_;
v___y_369_ = v___x_383_;
goto v___jp_362_;
}
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; 
lean_dec_ref(v___y_274_);
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
lean_dec(v_ref_388_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(lean_object* v_msgData_398_, uint8_t v_severity_399_, uint8_t v_isSilent_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_ref_404_; lean_object* v___x_405_; 
v_ref_404_ = lean_ctor_get(v___y_401_, 5);
lean_inc(v_ref_404_);
v___x_405_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_404_, v_msgData_398_, v_severity_399_, v_isSilent_400_, v___y_401_, v___y_402_);
lean_dec(v_ref_404_);
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
return v_b_433_;
}
else
{
lean_object* v_a_435_; lean_object* v_fst_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
lean_dec_ref(v_b_433_);
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
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
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
v___x_522_ = lean_apply_8(v_k_513_, v_b_516_, v___y_514_, v___y_515_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, lean_box(0));
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed(lean_object* v_k_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v_b_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(v_k_523_, v___y_524_, v___y_525_, v_b_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(lean_object* v_name_533_, lean_object* v_type_534_, lean_object* v_val_535_, lean_object* v_k_536_, uint8_t v_nondep_537_, uint8_t v_kind_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v___f_546_; lean_object* v___x_547_; 
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
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed(lean_object* v_fvars_572_, lean_object* v_f_573_, lean_object* v_body_574_, lean_object* v_x_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(v_fvars_572_, v_f_573_, v_body_574_, v_x_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
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
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec(v___y_587_);
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
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec(v___y_587_);
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
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(lean_object* v_name_655_, uint8_t v_bi_656_, lean_object* v_type_657_, lean_object* v_k_658_, uint8_t v_kind_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v___f_667_; lean_object* v___x_668_; 
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
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed(lean_object* v_fvars_692_, lean_object* v_f_693_, lean_object* v_body_694_, lean_object* v_x_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(v_fvars_692_, v_f_693_, v_body_694_, v_x_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
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
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
lean_dec(v___y_707_);
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
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed(lean_object* v_fvars_770_, lean_object* v_f_771_, lean_object* v_body_772_, lean_object* v_x_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(v_fvars_770_, v_f_771_, v_body_772_, v_x_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
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
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec(v___y_785_);
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
lean_inc(v___y_1055_);
lean_inc_ref(v___y_1054_);
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
lean_inc(v___y_1051_);
lean_inc(v_a_1050_);
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
lean_inc(v___y_1055_);
lean_inc_ref(v___y_1054_);
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
lean_inc(v___y_1051_);
lean_inc(v_a_1050_);
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
lean_inc(v___y_1055_);
lean_inc_ref(v___y_1054_);
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
lean_inc(v___y_1051_);
lean_inc(v_a_1050_);
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
lean_inc(v___y_1055_);
lean_inc_ref(v___y_1054_);
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
lean_inc(v___y_1051_);
lean_inc(v_a_1050_);
lean_inc_ref(v_fn_1089_);
lean_inc_ref(v_fn_1048_);
v___x_1091_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1048_, v_fn_1089_, v_a_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v___x_1092_; 
lean_dec_ref(v___x_1091_);
lean_inc(v___y_1055_);
lean_inc_ref(v___y_1054_);
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
lean_inc(v___y_1051_);
lean_inc(v_a_1050_);
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
lean_inc(v___y_1055_);
lean_inc_ref(v___y_1054_);
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
lean_inc(v___y_1051_);
lean_inc(v_a_1050_);
lean_inc_ref(v_expr_1093_);
v___x_1094_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1048_, v_expr_1093_, v_a_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
v___y_1070_ = v___x_1094_;
goto v___jp_1069_;
}
case 11:
{
lean_object* v_struct_1095_; lean_object* v___x_1096_; 
v_struct_1095_ = lean_ctor_get(v_e_1049_, 2);
lean_inc(v___y_1055_);
lean_inc_ref(v___y_1054_);
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
lean_inc(v___y_1051_);
lean_inc(v_a_1050_);
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
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec(v_a_1050_);
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
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec(v_a_1050_);
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
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec(v_a_1050_);
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
v___f_1059_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1059_, 0, v_a_1050_);
lean_closure_set(v___f_1059_, 1, v_e_1049_);
lean_closure_set(v___f_1059_, 2, v_a_1058_);
v___x_1060_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___f_1059_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
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
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec(v_a_1050_);
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
lean_inc(v___y_1133_);
lean_inc_ref(v___y_1132_);
lean_inc(v___y_1131_);
lean_inc_ref(v___y_1130_);
lean_inc(v___y_1129_);
lean_inc(v_a_1137_);
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
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
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
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
return v___x_1138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___boxed(lean_object* v_input_1150_, lean_object* v_fn_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1150_, v_fn_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
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
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(lean_object* v_fn_1178_, lean_object* v_x_1179_, lean_object* v_x_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
if (lean_obj_tag(v_x_1180_) == 0)
{
lean_object* v___x_1187_; 
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
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
lean_inc(v___y_1185_);
lean_inc_ref(v___y_1184_);
lean_inc(v___y_1183_);
lean_inc_ref(v___y_1182_);
lean_inc(v___y_1181_);
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
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
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
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(lean_object* v_fn_1204_, lean_object* v_x_1205_, lean_object* v_x_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
if (lean_obj_tag(v_x_1206_) == 0)
{
lean_object* v___x_1213_; 
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
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
lean_inc(v___y_1211_);
lean_inc_ref(v___y_1210_);
lean_inc(v___y_1209_);
lean_inc_ref(v___y_1208_);
lean_inc(v___y_1207_);
lean_inc_ref(v_fn_1204_);
v___x_1222_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1220_, v_fn_1204_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v___x_1224_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_a_1223_);
lean_dec_ref(v___x_1222_);
lean_inc(v___y_1211_);
lean_inc_ref(v___y_1210_);
lean_inc(v___y_1209_);
lean_inc_ref(v___y_1208_);
lean_inc(v___y_1207_);
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
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
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
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(lean_object* v_fn_1235_, lean_object* v_x_1236_, lean_object* v_x_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
if (lean_obj_tag(v_x_1237_) == 0)
{
lean_object* v___x_1244_; 
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
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
lean_inc(v___y_1242_);
lean_inc_ref(v___y_1241_);
lean_inc(v___y_1240_);
lean_inc_ref(v___y_1239_);
lean_inc(v___y_1238_);
lean_inc_ref(v_fn_1235_);
v___x_1254_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1253_, v_fn_1235_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v___x_1255_; 
lean_dec_ref(v___x_1254_);
lean_inc(v___y_1242_);
lean_inc_ref(v___y_1241_);
lean_inc(v___y_1240_);
lean_inc_ref(v___y_1239_);
lean_inc(v___y_1238_);
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
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
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
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
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
lean_inc(v___y_1273_);
lean_inc_ref(v___y_1272_);
lean_inc(v___y_1271_);
lean_inc_ref(v___y_1270_);
lean_inc(v___y_1269_);
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
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
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
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
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
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
lean_dec(v_decl_1360_);
goto v___jp_1370_;
}
else
{
uint8_t v___x_1375_; 
v___x_1375_ = l_Lean_Declaration_hasSorry(v_decl_1360_);
if (v___x_1375_ == 0)
{
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
lean_dec(v_decl_1360_);
goto v___jp_1370_;
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___f_1386_; lean_object* v___x_1387_; 
v___x_1376_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_1377_ = lean_box(1);
v___x_1378_ = lean_unsigned_to_nat(0u);
v___x_1379_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1380_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__3));
v___x_1381_ = lean_box(0);
v___x_1382_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1382_, 0, v___x_1376_);
lean_ctor_set(v___x_1382_, 1, v___x_1377_);
lean_ctor_set(v___x_1382_, 2, v___x_1379_);
lean_ctor_set(v___x_1382_, 3, v___x_1380_);
lean_ctor_set(v___x_1382_, 4, v___x_1381_);
lean_ctor_set(v___x_1382_, 5, v___x_1378_);
lean_ctor_set(v___x_1382_, 6, v___x_1381_);
lean_ctor_set_uint8(v___x_1382_, sizeof(void*)*7, v___x_1374_);
lean_ctor_set_uint8(v___x_1382_, sizeof(void*)*7 + 1, v___x_1374_);
lean_ctor_set_uint8(v___x_1382_, sizeof(void*)*7 + 2, v___x_1374_);
lean_ctor_set_uint8(v___x_1382_, sizeof(void*)*7 + 3, v___x_1366_);
v___x_1383_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__7, &l_Lean_warnIfUsesSorry___closed__7_once, _init_l_Lean_warnIfUsesSorry___closed__7);
v___x_1384_ = lean_st_mk_ref(v___x_1383_);
v___x_1385_ = lean_st_mk_ref(v___x_1380_);
v___f_1386_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__8));
lean_inc(v_a_1362_);
lean_inc_ref(v_a_1361_);
lean_inc(v___x_1384_);
lean_inc(v___x_1385_);
v___x_1387_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1360_, v___f_1386_, v___x_1385_, v___x_1382_, v___x_1384_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v_val_1391_; lean_object* v___x_1413_; size_t v_sz_1414_; size_t v___x_1415_; lean_object* v___x_1416_; lean_object* v_fst_1417_; 
lean_dec_ref(v___x_1387_);
v___x_1388_ = lean_st_ref_get(v___x_1385_);
lean_dec(v___x_1385_);
v___x_1389_ = lean_st_ref_get(v___x_1384_);
lean_dec(v___x_1384_);
lean_dec(v___x_1389_);
v___x_1413_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__18));
v_sz_1414_ = lean_array_size(v___x_1388_);
v___x_1415_ = ((size_t)0ULL);
v___x_1416_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v___x_1388_, v_sz_1414_, v___x_1415_, v___x_1413_);
v_fst_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_fst_1417_);
lean_dec_ref(v___x_1416_);
if (lean_obj_tag(v_fst_1417_) == 0)
{
goto v___jp_1407_;
}
else
{
lean_object* v_val_1418_; 
v_val_1418_ = lean_ctor_get(v_fst_1417_, 0);
lean_inc(v_val_1418_);
lean_dec_ref(v_fst_1417_);
if (lean_obj_tag(v_val_1418_) == 0)
{
goto v___jp_1407_;
}
else
{
lean_object* v_val_1419_; 
lean_dec(v___x_1388_);
v_val_1419_ = lean_ctor_get(v_val_1418_, 0);
lean_inc(v_val_1419_);
lean_dec_ref(v_val_1418_);
v_val_1391_ = v_val_1419_;
goto v___jp_1390_;
}
}
v___jp_1390_:
{
lean_object* v_snd_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1405_; 
v_snd_1392_ = lean_ctor_get(v_val_1391_, 1);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_val_1391_);
if (v_isSharedCheck_1405_ == 0)
{
lean_object* v_unused_1406_; 
v_unused_1406_ = lean_ctor_get(v_val_1391_, 0);
lean_dec(v_unused_1406_);
v___x_1394_ = v_val_1391_;
v_isShared_1395_ = v_isSharedCheck_1405_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_snd_1392_);
lean_dec(v_val_1391_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1405_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1399_; 
v___x_1396_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__10));
v___x_1397_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__12, &l_Lean_warnIfUsesSorry___closed__12_once, _init_l_Lean_warnIfUsesSorry___closed__12);
if (v_isShared_1395_ == 0)
{
lean_ctor_set_tag(v___x_1394_, 7);
lean_ctor_set(v___x_1394_, 0, v___x_1397_);
v___x_1399_ = v___x_1394_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_snd_1392_);
v___x_1399_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1400_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__14, &l_Lean_warnIfUsesSorry___closed__14_once, _init_l_Lean_warnIfUsesSorry___closed__14);
v___x_1401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1399_);
lean_ctor_set(v___x_1401_, 1, v___x_1400_);
v___x_1402_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1396_);
lean_ctor_set(v___x_1402_, 1, v___x_1401_);
v___x_1403_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1402_, v_a_1361_, v_a_1362_);
lean_dec(v_a_1362_);
return v___x_1403_;
}
}
}
v___jp_1407_:
{
lean_object* v___x_1408_; uint8_t v___x_1409_; 
v___x_1408_ = lean_array_get_size(v___x_1388_);
v___x_1409_ = lean_nat_dec_lt(v___x_1378_, v___x_1408_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
lean_dec(v___x_1388_);
v___x_1410_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__17, &l_Lean_warnIfUsesSorry___closed__17_once, _init_l_Lean_warnIfUsesSorry___closed__17);
v___x_1411_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1410_, v_a_1361_, v_a_1362_);
lean_dec(v_a_1362_);
return v___x_1411_;
}
else
{
lean_object* v___x_1412_; 
v___x_1412_ = lean_array_fget(v___x_1388_, v___x_1378_);
lean_dec(v___x_1388_);
v_val_1391_ = v___x_1412_;
goto v___jp_1390_;
}
}
}
else
{
lean_dec(v___x_1385_);
lean_dec(v___x_1384_);
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
return v___x_1387_;
}
}
}
}
else
{
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
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
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___boxed(lean_object* v_decl_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_warnIfUsesSorry(v_decl_1420_, v_a_1421_, v_a_1422_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1425_, lean_object* v_m_1426_, lean_object* v_a_1427_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1426_, v_a_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1429_, lean_object* v_m_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(v_00_u03b2_1429_, v_m_1430_, v_a_1431_);
lean_dec_ref(v_a_1431_);
lean_dec_ref(v_m_1430_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_1433_, lean_object* v_m_1434_, lean_object* v_a_1435_, lean_object* v_b_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_m_1434_, v_a_1435_, v_b_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_1438_, lean_object* v_a_1439_, lean_object* v_x_1440_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1439_, v_x_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1442_, lean_object* v_a_1443_, lean_object* v_x_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(v_00_u03b2_1442_, v_a_1443_, v_x_1444_);
lean_dec(v_x_1444_);
lean_dec_ref(v_a_1443_);
return v_res_1445_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(lean_object* v_00_u03b2_1446_, lean_object* v_a_1447_, lean_object* v_x_1448_){
_start:
{
uint8_t v___x_1449_; 
v___x_1449_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1447_, v_x_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___boxed(lean_object* v_00_u03b2_1450_, lean_object* v_a_1451_, lean_object* v_x_1452_){
_start:
{
uint8_t v_res_1453_; lean_object* v_r_1454_; 
v_res_1453_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(v_00_u03b2_1450_, v_a_1451_, v_x_1452_);
lean_dec(v_x_1452_);
lean_dec_ref(v_a_1451_);
v_r_1454_ = lean_box(v_res_1453_);
return v_r_1454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17(lean_object* v_00_u03b2_1455_, lean_object* v_data_1456_){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_data_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18(lean_object* v_00_u03b2_1458_, lean_object* v_a_1459_, lean_object* v_b_1460_, lean_object* v_x_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1459_, v_b_1460_, v_x_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(lean_object* v_00_u03b1_1463_, lean_object* v_name_1464_, uint8_t v_bi_1465_, lean_object* v_type_1466_, lean_object* v_k_1467_, uint8_t v_kind_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_1464_, v_bi_1465_, v_type_1466_, v_k_1467_, v_kind_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___boxed(lean_object* v_00_u03b1_1477_, lean_object* v_name_1478_, lean_object* v_bi_1479_, lean_object* v_type_1480_, lean_object* v_k_1481_, lean_object* v_kind_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
uint8_t v_bi_boxed_1490_; uint8_t v_kind_boxed_1491_; lean_object* v_res_1492_; 
v_bi_boxed_1490_ = lean_unbox(v_bi_1479_);
v_kind_boxed_1491_ = lean_unbox(v_kind_1482_);
v_res_1492_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(v_00_u03b1_1477_, v_name_1478_, v_bi_boxed_1490_, v_type_1480_, v_k_1481_, v_kind_boxed_1491_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(lean_object* v_00_u03b1_1493_, lean_object* v_name_1494_, lean_object* v_type_1495_, lean_object* v_val_1496_, lean_object* v_k_1497_, uint8_t v_nondep_1498_, uint8_t v_kind_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_1494_, v_type_1495_, v_val_1496_, v_k_1497_, v_nondep_1498_, v_kind_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___boxed(lean_object* v_00_u03b1_1508_, lean_object* v_name_1509_, lean_object* v_type_1510_, lean_object* v_val_1511_, lean_object* v_k_1512_, lean_object* v_nondep_1513_, lean_object* v_kind_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
uint8_t v_nondep_boxed_1522_; uint8_t v_kind_boxed_1523_; lean_object* v_res_1524_; 
v_nondep_boxed_1522_ = lean_unbox(v_nondep_1513_);
v_kind_boxed_1523_ = lean_unbox(v_kind_1514_);
v_res_1524_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(v_00_u03b1_1508_, v_name_1509_, v_type_1510_, v_val_1511_, v_k_1512_, v_nondep_boxed_1522_, v_kind_boxed_1523_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18(lean_object* v_00_u03b2_1525_, lean_object* v_i_1526_, lean_object* v_source_1527_, lean_object* v_target_1528_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v_i_1526_, v_source_1527_, v_target_1528_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22(lean_object* v_00_u03b2_1530_, lean_object* v_x_1531_, lean_object* v_x_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_x_1531_, v_x_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1583_; uint8_t v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1583_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1584_ = 0;
v___x_1585_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__20_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1586_ = l_Lean_registerTraceClass(v___x_1583_, v___x_1584_, v___x_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2____boxed(lean_object* v_a_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_();
return v_res_1588_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1589_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__0);
v___x_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
return v___x_1591_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__1);
v___x_1593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1592_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(lean_object* v_env_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v___x_1597_; lean_object* v_nextMacroScope_1598_; lean_object* v_ngen_1599_; lean_object* v_auxDeclNGen_1600_; lean_object* v_traceState_1601_; lean_object* v_messages_1602_; lean_object* v_infoState_1603_; lean_object* v_snapshotTasks_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1615_; 
v___x_1597_ = lean_st_ref_take(v___y_1595_);
v_nextMacroScope_1598_ = lean_ctor_get(v___x_1597_, 1);
v_ngen_1599_ = lean_ctor_get(v___x_1597_, 2);
v_auxDeclNGen_1600_ = lean_ctor_get(v___x_1597_, 3);
v_traceState_1601_ = lean_ctor_get(v___x_1597_, 4);
v_messages_1602_ = lean_ctor_get(v___x_1597_, 6);
v_infoState_1603_ = lean_ctor_get(v___x_1597_, 7);
v_snapshotTasks_1604_ = lean_ctor_get(v___x_1597_, 8);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1615_ == 0)
{
lean_object* v_unused_1616_; lean_object* v_unused_1617_; 
v_unused_1616_ = lean_ctor_get(v___x_1597_, 5);
lean_dec(v_unused_1616_);
v_unused_1617_ = lean_ctor_get(v___x_1597_, 0);
lean_dec(v_unused_1617_);
v___x_1606_ = v___x_1597_;
v_isShared_1607_ = v_isSharedCheck_1615_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_snapshotTasks_1604_);
lean_inc(v_infoState_1603_);
lean_inc(v_messages_1602_);
lean_inc(v_traceState_1601_);
lean_inc(v_auxDeclNGen_1600_);
lean_inc(v_ngen_1599_);
lean_inc(v_nextMacroScope_1598_);
lean_dec(v___x_1597_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1615_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1608_; lean_object* v___x_1610_; 
v___x_1608_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 5, v___x_1608_);
lean_ctor_set(v___x_1606_, 0, v_env_1594_);
v___x_1610_ = v___x_1606_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_env_1594_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_nextMacroScope_1598_);
lean_ctor_set(v_reuseFailAlloc_1614_, 2, v_ngen_1599_);
lean_ctor_set(v_reuseFailAlloc_1614_, 3, v_auxDeclNGen_1600_);
lean_ctor_set(v_reuseFailAlloc_1614_, 4, v_traceState_1601_);
lean_ctor_set(v_reuseFailAlloc_1614_, 5, v___x_1608_);
lean_ctor_set(v_reuseFailAlloc_1614_, 6, v_messages_1602_);
lean_ctor_set(v_reuseFailAlloc_1614_, 7, v_infoState_1603_);
lean_ctor_set(v_reuseFailAlloc_1614_, 8, v_snapshotTasks_1604_);
v___x_1610_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1611_ = lean_st_ref_set(v___y_1595_, v___x_1610_);
v___x_1612_ = lean_box(0);
v___x_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
return v___x_1613_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___boxed(lean_object* v_env_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_env_1618_, v___y_1619_);
lean_dec(v___y_1619_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1(lean_object* v_env_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_env_1622_, v___y_1624_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___boxed(lean_object* v_env_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1(v_env_1627_, v___y_1628_, v___y_1629_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2___redArg(lean_object* v_msg_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v_ref_1636_; lean_object* v___x_1637_; lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1646_; 
v_ref_1636_ = lean_ctor_get(v___y_1633_, 5);
v___x_1637_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_1632_, v___y_1633_, v___y_1634_);
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1640_ = v___x_1637_;
v_isShared_1641_ = v_isSharedCheck_1646_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1637_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1646_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; lean_object* v___x_1644_; 
lean_inc(v_ref_1636_);
v___x_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1642_, 0, v_ref_1636_);
lean_ctor_set(v___x_1642_, 1, v_a_1638_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set_tag(v___x_1640_, 1);
lean_ctor_set(v___x_1640_, 0, v___x_1642_);
v___x_1644_ = v___x_1640_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msg_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_1647_, v___y_1648_, v___y_1649_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
return v_res_1651_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1652_ = lean_box(0);
v___x_1653_ = l_Lean_interruptExceptionId;
v___x_1654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
lean_ctor_set(v___x_1654_, 1, v___x_1652_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg(){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v___y_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(lean_object* v_ex_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v___y_1665_; lean_object* v___y_1666_; 
if (lean_obj_tag(v_ex_1660_) == 16)
{
lean_object* v___x_1670_; lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_dec_ref(v___y_1661_);
v___x_1670_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg();
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1670_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1670_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
else
{
v___y_1665_ = v___y_1661_;
v___y_1666_ = v___y_1662_;
goto v___jp_1664_;
}
v___jp_1664_:
{
lean_object* v_options_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v_options_1667_ = lean_ctor_get(v___y_1665_, 2);
lean_inc_ref(v_options_1667_);
v___x_1668_ = l_Lean_Kernel_Exception_toMessageData(v_ex_1660_, v_options_1667_);
v___x_1669_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2___redArg(v___x_1668_, v___y_1665_, v___y_1666_);
lean_dec_ref(v___y_1665_);
return v___x_1669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg___boxed(lean_object* v_ex_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(v_ex_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(lean_object* v_x_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
if (lean_obj_tag(v_x_1684_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1689_; 
v_a_1688_ = lean_ctor_get(v_x_1684_, 0);
lean_inc(v_a_1688_);
lean_dec_ref(v_x_1684_);
v___x_1689_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(v_a_1688_, v___y_1685_, v___y_1686_);
return v___x_1689_;
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
lean_dec_ref(v___y_1685_);
v_a_1690_ = lean_ctor_get(v_x_1684_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_x_1684_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v_x_1684_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v_x_1684_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
lean_ctor_set_tag(v___x_1692_, 0);
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg___boxed(lean_object* v_x_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v_x_1698_, v___y_1699_, v___y_1700_);
lean_dec(v___y_1700_);
return v_res_1702_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = lean_unsigned_to_nat(1u);
v___x_1704_ = l_Lean_Level_ofNat(v___x_1703_);
return v___x_1704_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1705_ = lean_box(0);
v___x_1706_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__0);
v___x_1707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1706_);
lean_ctor_set(v___x_1707_, 1, v___x_1705_);
return v___x_1707_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1714_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__1);
v___x_1715_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__4));
v___x_1716_ = l_Lean_mkConst(v___x_1715_, v___x_1714_);
return v___x_1716_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1717_ = lean_unsigned_to_nat(0u);
v___x_1718_ = l_Lean_Level_ofNat(v___x_1717_);
return v___x_1718_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__6);
v___x_1720_ = l_Lean_mkSort(v___x_1719_);
return v___x_1720_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__11(void){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1726_ = lean_box(0);
v___x_1727_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__10));
v___x_1728_ = l_Lean_mkConst(v___x_1727_, v___x_1726_);
return v___x_1728_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__12(void){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1729_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__11);
v___x_1730_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__7);
v___x_1731_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__5);
v___x_1732_ = l_Lean_mkAppB(v___x_1731_, v___x_1730_, v___x_1729_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg(lean_object* v_as_x27_1738_, lean_object* v_b_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
if (lean_obj_tag(v_as_x27_1738_) == 0)
{
lean_object* v___x_1743_; 
lean_dec_ref(v___y_1740_);
v___x_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1743_, 0, v_b_1739_);
return v___x_1743_;
}
else
{
lean_object* v_head_1744_; lean_object* v_tail_1745_; lean_object* v___x_1746_; lean_object* v_env_1747_; lean_object* v_options_1748_; lean_object* v_cancelTk_x3f_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___y_1753_; uint8_t v___y_1754_; lean_object* v_a_1758_; lean_object* v___x_1761_; lean_object* v___x_1762_; uint8_t v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
lean_dec_ref(v_b_1739_);
v_head_1744_ = lean_ctor_get(v_as_x27_1738_, 0);
v_tail_1745_ = lean_ctor_get(v_as_x27_1738_, 1);
v___x_1746_ = lean_st_ref_get(v___y_1741_);
v_env_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc_ref(v_env_1747_);
lean_dec(v___x_1746_);
v_options_1748_ = lean_ctor_get(v___y_1740_, 2);
v_cancelTk_x3f_1749_ = lean_ctor_get(v___y_1740_, 12);
v___x_1750_ = lean_box(0);
v___x_1751_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__2));
v___x_1761_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__12, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__12_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__12);
lean_inc(v_head_1744_);
v___x_1762_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1762_, 0, v_head_1744_);
lean_ctor_set(v___x_1762_, 1, v___x_1750_);
lean_ctor_set(v___x_1762_, 2, v___x_1761_);
v___x_1763_ = 0;
v___x_1764_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1764_, 0, v___x_1762_);
lean_ctor_set_uint8(v___x_1764_, sizeof(void*)*1, v___x_1763_);
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
v___x_1766_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_1747_, v_options_1748_, v___x_1765_, v_cancelTk_x3f_1749_);
lean_inc_ref(v___y_1740_);
v___x_1767_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_1766_, v___y_1740_, v___y_1741_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v_a_1768_; lean_object* v___x_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1777_; 
lean_dec_ref(v___y_1740_);
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_a_1768_);
lean_dec_ref(v___x_1767_);
v___x_1769_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_1768_, v___y_1741_);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1777_ == 0)
{
lean_object* v_unused_1778_; 
v_unused_1778_ = lean_ctor_get(v___x_1769_, 0);
lean_dec(v_unused_1778_);
v___x_1771_ = v___x_1769_;
v_isShared_1772_ = v_isSharedCheck_1777_;
goto v_resetjp_1770_;
}
else
{
lean_dec(v___x_1769_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1777_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1773_; lean_object* v___x_1775_; 
v___x_1773_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__14));
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1773_);
v___x_1775_ = v___x_1771_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1773_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
else
{
lean_object* v_a_1779_; 
v_a_1779_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_a_1779_);
lean_dec_ref(v___x_1767_);
v_a_1758_ = v_a_1779_;
goto v___jp_1757_;
}
v___jp_1752_:
{
if (v___y_1754_ == 0)
{
lean_dec_ref(v___y_1753_);
v_as_x27_1738_ = v_tail_1745_;
v_b_1739_ = v___x_1751_;
goto _start;
}
else
{
lean_object* v___x_1756_; 
lean_dec_ref(v___y_1740_);
v___x_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1756_, 0, v___y_1753_);
return v___x_1756_;
}
}
v___jp_1757_:
{
uint8_t v___x_1759_; 
v___x_1759_ = l_Lean_Exception_isInterrupt(v_a_1758_);
if (v___x_1759_ == 0)
{
uint8_t v___x_1760_; 
lean_inc_ref(v_a_1758_);
v___x_1760_ = l_Lean_Exception_isRuntime(v_a_1758_);
v___y_1753_ = v_a_1758_;
v___y_1754_ = v___x_1760_;
goto v___jp_1752_;
}
else
{
v___y_1753_ = v_a_1758_;
v___y_1754_ = v___x_1759_;
goto v___jp_1752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___boxed(lean_object* v_as_x27_1780_, lean_object* v_b_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg(v_as_x27_1780_, v_b_1781_, v___y_1782_, v___y_1783_);
lean_dec(v___y_1783_);
lean_dec(v_as_x27_1780_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom(lean_object* v_decl_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1819_; uint8_t v___y_1820_; lean_object* v_a_1823_; lean_object* v___y_1827_; uint8_t v___y_1828_; lean_object* v_a_1831_; 
switch(lean_obj_tag(v_decl_1786_))
{
case 1:
{
lean_object* v_val_1834_; lean_object* v___x_1835_; lean_object* v_toConstantVal_1836_; lean_object* v_env_1837_; lean_object* v_options_1838_; lean_object* v_cancelTk_x3f_1839_; uint8_t v___x_1840_; lean_object* v___x_1841_; lean_object* v_fallbackDecl_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v_val_1834_ = lean_ctor_get(v_decl_1786_, 0);
v___x_1835_ = lean_st_ref_get(v_a_1788_);
v_toConstantVal_1836_ = lean_ctor_get(v_val_1834_, 0);
v_env_1837_ = lean_ctor_get(v___x_1835_, 0);
lean_inc_ref(v_env_1837_);
lean_dec(v___x_1835_);
v_options_1838_ = lean_ctor_get(v_a_1787_, 2);
v_cancelTk_x3f_1839_ = lean_ctor_get(v_a_1787_, 12);
v___x_1840_ = 0;
lean_inc_ref(v_toConstantVal_1836_);
v___x_1841_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1841_, 0, v_toConstantVal_1836_);
lean_ctor_set_uint8(v___x_1841_, sizeof(void*)*1, v___x_1840_);
v_fallbackDecl_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_1842_, 0, v___x_1841_);
v___x_1843_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_1837_, v_options_1838_, v_fallbackDecl_1842_, v_cancelTk_x3f_1839_);
lean_inc_ref(v_a_1787_);
v___x_1844_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_1843_, v_a_1787_, v_a_1788_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; lean_object* v___x_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1854_; 
lean_dec_ref(v_decl_1786_);
lean_dec_ref(v_a_1787_);
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1845_);
lean_dec_ref(v___x_1844_);
v___x_1846_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_1845_, v_a_1788_);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1854_ == 0)
{
lean_object* v_unused_1855_; 
v_unused_1855_ = lean_ctor_get(v___x_1846_, 0);
lean_dec(v_unused_1855_);
v___x_1848_ = v___x_1846_;
v_isShared_1849_ = v_isSharedCheck_1854_;
goto v_resetjp_1847_;
}
else
{
lean_dec(v___x_1846_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1854_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1850_; lean_object* v___x_1852_; 
v___x_1850_ = lean_box(0);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 0, v___x_1850_);
v___x_1852_ = v___x_1848_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
else
{
lean_object* v_a_1856_; 
v_a_1856_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1856_);
lean_dec_ref(v___x_1844_);
v_a_1823_ = v_a_1856_;
goto v___jp_1822_;
}
}
case 2:
{
lean_object* v_val_1857_; lean_object* v___x_1858_; lean_object* v_toConstantVal_1859_; lean_object* v_env_1860_; lean_object* v_options_1861_; lean_object* v_cancelTk_x3f_1862_; uint8_t v___x_1863_; lean_object* v___x_1864_; lean_object* v_fallbackDecl_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v_val_1857_ = lean_ctor_get(v_decl_1786_, 0);
v___x_1858_ = lean_st_ref_get(v_a_1788_);
v_toConstantVal_1859_ = lean_ctor_get(v_val_1857_, 0);
v_env_1860_ = lean_ctor_get(v___x_1858_, 0);
lean_inc_ref(v_env_1860_);
lean_dec(v___x_1858_);
v_options_1861_ = lean_ctor_get(v_a_1787_, 2);
v_cancelTk_x3f_1862_ = lean_ctor_get(v_a_1787_, 12);
v___x_1863_ = 0;
lean_inc_ref(v_toConstantVal_1859_);
v___x_1864_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1864_, 0, v_toConstantVal_1859_);
lean_ctor_set_uint8(v___x_1864_, sizeof(void*)*1, v___x_1863_);
v_fallbackDecl_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_1865_, 0, v___x_1864_);
v___x_1866_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_1860_, v_options_1861_, v_fallbackDecl_1865_, v_cancelTk_x3f_1862_);
lean_inc_ref(v_a_1787_);
v___x_1867_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_1866_, v_a_1787_, v_a_1788_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; lean_object* v___x_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1877_; 
lean_dec_ref(v_decl_1786_);
lean_dec_ref(v_a_1787_);
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_a_1868_);
lean_dec_ref(v___x_1867_);
v___x_1869_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_1868_, v_a_1788_);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1877_ == 0)
{
lean_object* v_unused_1878_; 
v_unused_1878_ = lean_ctor_get(v___x_1869_, 0);
lean_dec(v_unused_1878_);
v___x_1871_ = v___x_1869_;
v_isShared_1872_ = v_isSharedCheck_1877_;
goto v_resetjp_1870_;
}
else
{
lean_dec(v___x_1869_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1877_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; lean_object* v___x_1875_; 
v___x_1873_ = lean_box(0);
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v___x_1873_);
v___x_1875_ = v___x_1871_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1873_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
else
{
lean_object* v_a_1879_; 
v_a_1879_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_a_1879_);
lean_dec_ref(v___x_1867_);
v_a_1831_ = v_a_1879_;
goto v___jp_1830_;
}
}
default: 
{
v___y_1791_ = v_a_1787_;
v___y_1792_ = v_a_1788_;
goto v___jp_1790_;
}
}
v___jp_1790_:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1793_ = l_Lean_Declaration_getNames(v_decl_1786_);
v___x_1794_ = lean_box(0);
v___x_1795_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__2));
v___x_1796_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg(v___x_1793_, v___x_1795_, v___y_1791_, v___y_1792_);
lean_dec(v___x_1793_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1809_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1799_ = v___x_1796_;
v_isShared_1800_ = v_isSharedCheck_1809_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1809_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v_fst_1801_; 
v_fst_1801_ = lean_ctor_get(v_a_1797_, 0);
lean_inc(v_fst_1801_);
lean_dec(v_a_1797_);
if (lean_obj_tag(v_fst_1801_) == 0)
{
lean_object* v___x_1803_; 
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 0, v___x_1794_);
v___x_1803_ = v___x_1799_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1794_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
else
{
lean_object* v_val_1805_; lean_object* v___x_1807_; 
v_val_1805_ = lean_ctor_get(v_fst_1801_, 0);
lean_inc(v_val_1805_);
lean_dec_ref(v_fst_1801_);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 0, v_val_1805_);
v___x_1807_ = v___x_1799_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_val_1805_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
else
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1817_; 
v_a_1810_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1812_ = v___x_1796_;
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1796_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1810_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
v___jp_1818_:
{
if (v___y_1820_ == 0)
{
lean_dec_ref(v___y_1819_);
v___y_1791_ = v_a_1787_;
v___y_1792_ = v_a_1788_;
goto v___jp_1790_;
}
else
{
lean_object* v___x_1821_; 
lean_dec_ref(v_a_1787_);
lean_dec(v_decl_1786_);
v___x_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1821_, 0, v___y_1819_);
return v___x_1821_;
}
}
v___jp_1822_:
{
uint8_t v___x_1824_; 
v___x_1824_ = l_Lean_Exception_isInterrupt(v_a_1823_);
if (v___x_1824_ == 0)
{
uint8_t v___x_1825_; 
lean_inc_ref(v_a_1823_);
v___x_1825_ = l_Lean_Exception_isRuntime(v_a_1823_);
v___y_1819_ = v_a_1823_;
v___y_1820_ = v___x_1825_;
goto v___jp_1818_;
}
else
{
v___y_1819_ = v_a_1823_;
v___y_1820_ = v___x_1824_;
goto v___jp_1818_;
}
}
v___jp_1826_:
{
if (v___y_1828_ == 0)
{
lean_dec_ref(v___y_1827_);
v___y_1791_ = v_a_1787_;
v___y_1792_ = v_a_1788_;
goto v___jp_1790_;
}
else
{
lean_object* v___x_1829_; 
lean_dec_ref(v_a_1787_);
lean_dec(v_decl_1786_);
v___x_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___y_1827_);
return v___x_1829_;
}
}
v___jp_1830_:
{
uint8_t v___x_1832_; 
v___x_1832_ = l_Lean_Exception_isInterrupt(v_a_1831_);
if (v___x_1832_ == 0)
{
uint8_t v___x_1833_; 
lean_inc_ref(v_a_1831_);
v___x_1833_ = l_Lean_Exception_isRuntime(v_a_1831_);
v___y_1827_ = v_a_1831_;
v___y_1828_ = v___x_1833_;
goto v___jp_1826_;
}
else
{
v___y_1827_ = v_a_1831_;
v___y_1828_ = v___x_1832_;
goto v___jp_1826_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom___boxed(lean_object* v_decl_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom(v_decl_1880_, v_a_1881_, v_a_1882_);
lean_dec(v_a_1882_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0(lean_object* v_00_u03b1_1885_, lean_object* v_x_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v_x_1886_, v___y_1887_, v___y_1888_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___boxed(lean_object* v_00_u03b1_1891_, lean_object* v_x_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0(v_00_u03b1_1891_, v_x_1892_, v___y_1893_, v___y_1894_);
lean_dec(v___y_1894_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2(lean_object* v_as_1897_, lean_object* v_as_x27_1898_, lean_object* v_b_1899_, lean_object* v_a_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg(v_as_x27_1898_, v_b_1899_, v___y_1901_, v___y_1902_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___boxed(lean_object* v_as_1905_, lean_object* v_as_x27_1906_, lean_object* v_b_1907_, lean_object* v_a_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2(v_as_1905_, v_as_x27_1906_, v_b_1907_, v_a_1908_, v___y_1909_, v___y_1910_);
lean_dec(v___y_1910_);
lean_dec(v_as_x27_1906_);
lean_dec(v_as_1905_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3(v_00_u03b1_1918_, v___y_1919_, v___y_1920_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0(lean_object* v_00_u03b1_1923_, lean_object* v_ex_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v___x_1928_; 
v___x_1928_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(v_ex_1924_, v___y_1925_, v___y_1926_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1929_, lean_object* v_ex_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0(v_00_u03b1_1929_, v_ex_1930_, v___y_1931_, v___y_1932_);
lean_dec(v___y_1932_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1935_, lean_object* v_msg_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_1936_, v___y_1937_, v___y_1938_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1941_, lean_object* v_msg_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2(v_00_u03b1_1941_, v_msg_1942_, v___y_1943_, v___y_1944_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(lean_object* v_cls_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v_options_1952_; uint8_t v_hasTrace_1953_; 
v_options_1952_ = lean_ctor_get(v___y_1950_, 2);
v_hasTrace_1953_ = lean_ctor_get_uint8(v_options_1952_, sizeof(void*)*1);
if (v_hasTrace_1953_ == 0)
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
lean_dec(v_cls_1949_);
v___x_1954_ = lean_box(v_hasTrace_1953_);
v___x_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
return v___x_1955_;
}
else
{
lean_object* v_inheritedTraceOptions_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v_inheritedTraceOptions_1956_ = lean_ctor_get(v___y_1950_, 13);
v___x_1957_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__0));
v___x_1958_ = l_Lean_Name_append(v___x_1957_, v_cls_1949_);
v___x_1959_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1956_, v_options_1952_, v___x_1958_);
lean_dec(v___x_1958_);
v___x_1960_ = lean_box(v___x_1959_);
v___x_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
return v___x_1961_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___boxed(lean_object* v_cls_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_1962_, v___y_1963_);
lean_dec_ref(v___y_1963_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1(lean_object* v_cls_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v___x_1970_; 
v___x_1970_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_1966_, v___y_1967_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___boxed(lean_object* v_cls_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1(v_cls_1971_, v___y_1972_, v___y_1973_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
return v_res_1975_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1976_ = lean_unsigned_to_nat(32u);
v___x_1977_ = lean_mk_empty_array_with_capacity(v___x_1976_);
v___x_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
return v___x_1978_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1979_ = ((size_t)5ULL);
v___x_1980_ = lean_unsigned_to_nat(0u);
v___x_1981_ = lean_unsigned_to_nat(32u);
v___x_1982_ = lean_mk_empty_array_with_capacity(v___x_1981_);
v___x_1983_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___redArg___closed__0);
v___x_1984_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
lean_ctor_set(v___x_1984_, 1, v___x_1982_);
lean_ctor_set(v___x_1984_, 2, v___x_1980_);
lean_ctor_set(v___x_1984_, 3, v___x_1980_);
lean_ctor_set_usize(v___x_1984_, 4, v___x_1979_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___redArg(lean_object* v___y_1985_){
_start:
{
lean_object* v___x_1987_; lean_object* v_traceState_1988_; lean_object* v_traces_1989_; lean_object* v___x_1990_; lean_object* v_traceState_1991_; lean_object* v_env_1992_; lean_object* v_nextMacroScope_1993_; lean_object* v_ngen_1994_; lean_object* v_auxDeclNGen_1995_; lean_object* v_cache_1996_; lean_object* v_messages_1997_; lean_object* v_infoState_1998_; lean_object* v_snapshotTasks_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2018_; 
v___x_1987_ = lean_st_ref_get(v___y_1985_);
v_traceState_1988_ = lean_ctor_get(v___x_1987_, 4);
lean_inc_ref(v_traceState_1988_);
lean_dec(v___x_1987_);
v_traces_1989_ = lean_ctor_get(v_traceState_1988_, 0);
lean_inc_ref(v_traces_1989_);
lean_dec_ref(v_traceState_1988_);
v___x_1990_ = lean_st_ref_take(v___y_1985_);
v_traceState_1991_ = lean_ctor_get(v___x_1990_, 4);
v_env_1992_ = lean_ctor_get(v___x_1990_, 0);
v_nextMacroScope_1993_ = lean_ctor_get(v___x_1990_, 1);
v_ngen_1994_ = lean_ctor_get(v___x_1990_, 2);
v_auxDeclNGen_1995_ = lean_ctor_get(v___x_1990_, 3);
v_cache_1996_ = lean_ctor_get(v___x_1990_, 5);
v_messages_1997_ = lean_ctor_get(v___x_1990_, 6);
v_infoState_1998_ = lean_ctor_get(v___x_1990_, 7);
v_snapshotTasks_1999_ = lean_ctor_get(v___x_1990_, 8);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2001_ = v___x_1990_;
v_isShared_2002_ = v_isSharedCheck_2018_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_snapshotTasks_1999_);
lean_inc(v_infoState_1998_);
lean_inc(v_messages_1997_);
lean_inc(v_cache_1996_);
lean_inc(v_traceState_1991_);
lean_inc(v_auxDeclNGen_1995_);
lean_inc(v_ngen_1994_);
lean_inc(v_nextMacroScope_1993_);
lean_inc(v_env_1992_);
lean_dec(v___x_1990_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2018_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
uint64_t v_tid_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2016_; 
v_tid_2003_ = lean_ctor_get_uint64(v_traceState_1991_, sizeof(void*)*1);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_traceState_1991_);
if (v_isSharedCheck_2016_ == 0)
{
lean_object* v_unused_2017_; 
v_unused_2017_ = lean_ctor_get(v_traceState_1991_, 0);
lean_dec(v_unused_2017_);
v___x_2005_ = v_traceState_1991_;
v_isShared_2006_ = v_isSharedCheck_2016_;
goto v_resetjp_2004_;
}
else
{
lean_dec(v_traceState_1991_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2016_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2007_; lean_object* v___x_2009_; 
v___x_2007_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___redArg___closed__1);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 0, v___x_2007_);
v___x_2009_ = v___x_2005_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2007_);
lean_ctor_set_uint64(v_reuseFailAlloc_2015_, sizeof(void*)*1, v_tid_2003_);
v___x_2009_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
lean_object* v___x_2011_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 4, v___x_2009_);
v___x_2011_ = v___x_2001_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_env_1992_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_nextMacroScope_1993_);
lean_ctor_set(v_reuseFailAlloc_2014_, 2, v_ngen_1994_);
lean_ctor_set(v_reuseFailAlloc_2014_, 3, v_auxDeclNGen_1995_);
lean_ctor_set(v_reuseFailAlloc_2014_, 4, v___x_2009_);
lean_ctor_set(v_reuseFailAlloc_2014_, 5, v_cache_1996_);
lean_ctor_set(v_reuseFailAlloc_2014_, 6, v_messages_1997_);
lean_ctor_set(v_reuseFailAlloc_2014_, 7, v_infoState_1998_);
lean_ctor_set(v_reuseFailAlloc_2014_, 8, v_snapshotTasks_1999_);
v___x_2011_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = lean_st_ref_set(v___y_1985_, v___x_2011_);
v___x_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2013_, 0, v_traces_1989_);
return v___x_2013_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___redArg___boxed(lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___redArg(v___y_2019_);
lean_dec(v___y_2019_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2(lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
lean_object* v___x_2025_; 
v___x_2025_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___redArg(v___y_2023_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___boxed(lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2(v___y_2026_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__4___redArg(lean_object* v_category_2030_, lean_object* v_opts_2031_, lean_object* v_act_2032_, lean_object* v_decl_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = lean_apply_2(v_act_2032_, v___y_2034_, v___y_2035_);
v___x_2038_ = l_Lean_profileitIOUnsafe___redArg(v_category_2030_, v_opts_2031_, v___x_2037_, v_decl_2033_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__4___redArg___boxed(lean_object* v_category_2039_, lean_object* v_opts_2040_, lean_object* v_act_2041_, lean_object* v_decl_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__4___redArg(v_category_2039_, v_opts_2040_, v_act_2041_, v_decl_2042_, v___y_2043_, v___y_2044_);
lean_dec_ref(v_opts_2040_);
lean_dec_ref(v_category_2039_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__4(lean_object* v_00_u03b1_2047_, lean_object* v_category_2048_, lean_object* v_opts_2049_, lean_object* v_act_2050_, lean_object* v_decl_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v___x_2055_; 
v___x_2055_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__4___redArg(v_category_2048_, v_opts_2049_, v_act_2050_, v_decl_2051_, v___y_2052_, v___y_2053_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__4___boxed(lean_object* v_00_u03b1_2056_, lean_object* v_category_2057_, lean_object* v_opts_2058_, lean_object* v_act_2059_, lean_object* v_decl_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__4(v_00_u03b1_2056_, v_category_2057_, v_opts_2058_, v_act_2059_, v_decl_2060_, v___y_2061_, v___y_2062_);
lean_dec_ref(v_opts_2058_);
lean_dec_ref(v_category_2057_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__0(lean_object* v_a_2065_, lean_object* v_a_2066_){
_start:
{
if (lean_obj_tag(v_a_2065_) == 0)
{
lean_object* v___x_2067_; 
v___x_2067_ = l_List_reverse___redArg(v_a_2066_);
return v___x_2067_;
}
else
{
lean_object* v_head_2068_; lean_object* v_tail_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2078_; 
v_head_2068_ = lean_ctor_get(v_a_2065_, 0);
v_tail_2069_ = lean_ctor_get(v_a_2065_, 1);
v_isSharedCheck_2078_ = !lean_is_exclusive(v_a_2065_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2071_ = v_a_2065_;
v_isShared_2072_ = v_isSharedCheck_2078_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_tail_2069_);
lean_inc(v_head_2068_);
lean_dec(v_a_2065_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2078_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2073_; lean_object* v___x_2075_; 
v___x_2073_ = l_Lean_MessageData_ofName(v_head_2068_);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 1, v_a_2066_);
lean_ctor_set(v___x_2071_, 0, v___x_2073_);
v___x_2075_ = v___x_2071_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2073_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_a_2066_);
v___x_2075_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
v_a_2065_ = v_tail_2069_;
v_a_2066_ = v___x_2075_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2080_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__0));
v___x_2081_ = l_Lean_stringToMessageData(v___x_2080_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0(lean_object* v_decl_2082_, lean_object* v_x_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2087_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__1, &l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__1);
v___x_2088_ = l_Lean_Declaration_getTopLevelNames(v_decl_2082_);
v___x_2089_ = lean_box(0);
v___x_2090_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__0(v___x_2088_, v___x_2089_);
v___x_2091_ = l_Lean_MessageData_ofList(v___x_2090_);
v___x_2092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2087_);
lean_ctor_set(v___x_2092_, 1, v___x_2091_);
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___boxed(lean_object* v_decl_2094_, lean_object* v_x_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0(v_decl_2094_, v_x_2095_, v___y_2096_, v___y_2097_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec_ref(v_x_2095_);
return v_res_2099_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__3(lean_object* v_e_2100_){
_start:
{
if (lean_obj_tag(v_e_2100_) == 0)
{
uint8_t v___x_2101_; 
v___x_2101_ = 2;
return v___x_2101_;
}
else
{
uint8_t v___x_2102_; 
v___x_2102_ = 0;
return v___x_2102_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__3___boxed(lean_object* v_e_2103_){
_start:
{
uint8_t v_res_2104_; lean_object* v_r_2105_; 
v_res_2104_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__3(v_e_2103_);
lean_dec_ref(v_e_2103_);
v_r_2105_ = lean_box(v_res_2104_);
return v_r_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__6(lean_object* v_opts_2106_, lean_object* v_opt_2107_){
_start:
{
lean_object* v_name_2108_; lean_object* v_defValue_2109_; lean_object* v_map_2110_; lean_object* v___x_2111_; 
v_name_2108_ = lean_ctor_get(v_opt_2107_, 0);
v_defValue_2109_ = lean_ctor_get(v_opt_2107_, 1);
v_map_2110_ = lean_ctor_get(v_opts_2106_, 0);
v___x_2111_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2110_, v_name_2108_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_inc(v_defValue_2109_);
return v_defValue_2109_;
}
else
{
lean_object* v_val_2112_; 
v_val_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_val_2112_);
lean_dec_ref(v___x_2111_);
if (lean_obj_tag(v_val_2112_) == 3)
{
lean_object* v_v_2113_; 
v_v_2113_ = lean_ctor_get(v_val_2112_, 0);
lean_inc(v_v_2113_);
lean_dec_ref(v_val_2112_);
return v_v_2113_;
}
else
{
lean_dec(v_val_2112_);
lean_inc(v_defValue_2109_);
return v_defValue_2109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__6___boxed(lean_object* v_opts_2114_, lean_object* v_opt_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__6(v_opts_2114_, v_opt_2115_);
lean_dec_ref(v_opt_2115_);
lean_dec_ref(v_opts_2114_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__4_spec__6(size_t v_sz_2117_, size_t v_i_2118_, lean_object* v_bs_2119_){
_start:
{
uint8_t v___x_2120_; 
v___x_2120_ = lean_usize_dec_lt(v_i_2118_, v_sz_2117_);
if (v___x_2120_ == 0)
{
return v_bs_2119_;
}
else
{
lean_object* v_v_2121_; lean_object* v_msg_2122_; lean_object* v___x_2123_; lean_object* v_bs_x27_2124_; size_t v___x_2125_; size_t v___x_2126_; lean_object* v___x_2127_; 
v_v_2121_ = lean_array_uget_borrowed(v_bs_2119_, v_i_2118_);
v_msg_2122_ = lean_ctor_get(v_v_2121_, 1);
lean_inc_ref(v_msg_2122_);
v___x_2123_ = lean_unsigned_to_nat(0u);
v_bs_x27_2124_ = lean_array_uset(v_bs_2119_, v_i_2118_, v___x_2123_);
v___x_2125_ = ((size_t)1ULL);
v___x_2126_ = lean_usize_add(v_i_2118_, v___x_2125_);
v___x_2127_ = lean_array_uset(v_bs_x27_2124_, v_i_2118_, v_msg_2122_);
v_i_2118_ = v___x_2126_;
v_bs_2119_ = v___x_2127_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__4_spec__6___boxed(lean_object* v_sz_2129_, lean_object* v_i_2130_, lean_object* v_bs_2131_){
_start:
{
size_t v_sz_boxed_2132_; size_t v_i_boxed_2133_; lean_object* v_res_2134_; 
v_sz_boxed_2132_ = lean_unbox_usize(v_sz_2129_);
lean_dec(v_sz_2129_);
v_i_boxed_2133_ = lean_unbox_usize(v_i_2130_);
lean_dec(v_i_2130_);
v_res_2134_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__4_spec__6(v_sz_boxed_2132_, v_i_boxed_2133_, v_bs_2131_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__4(lean_object* v_oldTraces_2135_, lean_object* v_data_2136_, lean_object* v_ref_2137_, lean_object* v_msg_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
lean_object* v_fileName_2142_; lean_object* v_fileMap_2143_; lean_object* v_options_2144_; lean_object* v_currRecDepth_2145_; lean_object* v_maxRecDepth_2146_; lean_object* v_ref_2147_; lean_object* v_currNamespace_2148_; lean_object* v_openDecls_2149_; lean_object* v_initHeartbeats_2150_; lean_object* v_maxHeartbeats_2151_; lean_object* v_quotContext_2152_; lean_object* v_currMacroScope_2153_; uint8_t v_diag_2154_; lean_object* v_cancelTk_x3f_2155_; uint8_t v_suppressElabErrors_2156_; lean_object* v_inheritedTraceOptions_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2212_; 
v_fileName_2142_ = lean_ctor_get(v___y_2139_, 0);
v_fileMap_2143_ = lean_ctor_get(v___y_2139_, 1);
v_options_2144_ = lean_ctor_get(v___y_2139_, 2);
v_currRecDepth_2145_ = lean_ctor_get(v___y_2139_, 3);
v_maxRecDepth_2146_ = lean_ctor_get(v___y_2139_, 4);
v_ref_2147_ = lean_ctor_get(v___y_2139_, 5);
v_currNamespace_2148_ = lean_ctor_get(v___y_2139_, 6);
v_openDecls_2149_ = lean_ctor_get(v___y_2139_, 7);
v_initHeartbeats_2150_ = lean_ctor_get(v___y_2139_, 8);
v_maxHeartbeats_2151_ = lean_ctor_get(v___y_2139_, 9);
v_quotContext_2152_ = lean_ctor_get(v___y_2139_, 10);
v_currMacroScope_2153_ = lean_ctor_get(v___y_2139_, 11);
v_diag_2154_ = lean_ctor_get_uint8(v___y_2139_, sizeof(void*)*14);
v_cancelTk_x3f_2155_ = lean_ctor_get(v___y_2139_, 12);
v_suppressElabErrors_2156_ = lean_ctor_get_uint8(v___y_2139_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2157_ = lean_ctor_get(v___y_2139_, 13);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___y_2139_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2159_ = v___y_2139_;
v_isShared_2160_ = v_isSharedCheck_2212_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_inheritedTraceOptions_2157_);
lean_inc(v_cancelTk_x3f_2155_);
lean_inc(v_currMacroScope_2153_);
lean_inc(v_quotContext_2152_);
lean_inc(v_maxHeartbeats_2151_);
lean_inc(v_initHeartbeats_2150_);
lean_inc(v_openDecls_2149_);
lean_inc(v_currNamespace_2148_);
lean_inc(v_ref_2147_);
lean_inc(v_maxRecDepth_2146_);
lean_inc(v_currRecDepth_2145_);
lean_inc(v_options_2144_);
lean_inc(v_fileMap_2143_);
lean_inc(v_fileName_2142_);
lean_dec(v___y_2139_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2212_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2161_; lean_object* v_traceState_2162_; lean_object* v_traces_2163_; lean_object* v_ref_2164_; lean_object* v___x_2166_; 
v___x_2161_ = lean_st_ref_get(v___y_2140_);
v_traceState_2162_ = lean_ctor_get(v___x_2161_, 4);
lean_inc_ref(v_traceState_2162_);
lean_dec(v___x_2161_);
v_traces_2163_ = lean_ctor_get(v_traceState_2162_, 0);
lean_inc_ref(v_traces_2163_);
lean_dec_ref(v_traceState_2162_);
v_ref_2164_ = l_Lean_replaceRef(v_ref_2137_, v_ref_2147_);
lean_dec(v_ref_2147_);
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 5, v_ref_2164_);
v___x_2166_ = v___x_2159_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_fileName_2142_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_fileMap_2143_);
lean_ctor_set(v_reuseFailAlloc_2211_, 2, v_options_2144_);
lean_ctor_set(v_reuseFailAlloc_2211_, 3, v_currRecDepth_2145_);
lean_ctor_set(v_reuseFailAlloc_2211_, 4, v_maxRecDepth_2146_);
lean_ctor_set(v_reuseFailAlloc_2211_, 5, v_ref_2164_);
lean_ctor_set(v_reuseFailAlloc_2211_, 6, v_currNamespace_2148_);
lean_ctor_set(v_reuseFailAlloc_2211_, 7, v_openDecls_2149_);
lean_ctor_set(v_reuseFailAlloc_2211_, 8, v_initHeartbeats_2150_);
lean_ctor_set(v_reuseFailAlloc_2211_, 9, v_maxHeartbeats_2151_);
lean_ctor_set(v_reuseFailAlloc_2211_, 10, v_quotContext_2152_);
lean_ctor_set(v_reuseFailAlloc_2211_, 11, v_currMacroScope_2153_);
lean_ctor_set(v_reuseFailAlloc_2211_, 12, v_cancelTk_x3f_2155_);
lean_ctor_set(v_reuseFailAlloc_2211_, 13, v_inheritedTraceOptions_2157_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, sizeof(void*)*14, v_diag_2154_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, sizeof(void*)*14 + 1, v_suppressElabErrors_2156_);
v___x_2166_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
lean_object* v___x_2167_; size_t v_sz_2168_; size_t v___x_2169_; lean_object* v___x_2170_; lean_object* v_msg_2171_; lean_object* v___x_2172_; lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2210_; 
v___x_2167_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2163_);
lean_dec_ref(v_traces_2163_);
v_sz_2168_ = lean_array_size(v___x_2167_);
v___x_2169_ = ((size_t)0ULL);
v___x_2170_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__4_spec__6(v_sz_2168_, v___x_2169_, v___x_2167_);
v_msg_2171_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2171_, 0, v_data_2136_);
lean_ctor_set(v_msg_2171_, 1, v_msg_2138_);
lean_ctor_set(v_msg_2171_, 2, v___x_2170_);
v___x_2172_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2171_, v___x_2166_, v___y_2140_);
lean_dec_ref(v___x_2166_);
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2175_ = v___x_2172_;
v_isShared_2176_ = v_isSharedCheck_2210_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2172_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2210_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2177_; lean_object* v_traceState_2178_; lean_object* v_env_2179_; lean_object* v_nextMacroScope_2180_; lean_object* v_ngen_2181_; lean_object* v_auxDeclNGen_2182_; lean_object* v_cache_2183_; lean_object* v_messages_2184_; lean_object* v_infoState_2185_; lean_object* v_snapshotTasks_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2209_; 
v___x_2177_ = lean_st_ref_take(v___y_2140_);
v_traceState_2178_ = lean_ctor_get(v___x_2177_, 4);
v_env_2179_ = lean_ctor_get(v___x_2177_, 0);
v_nextMacroScope_2180_ = lean_ctor_get(v___x_2177_, 1);
v_ngen_2181_ = lean_ctor_get(v___x_2177_, 2);
v_auxDeclNGen_2182_ = lean_ctor_get(v___x_2177_, 3);
v_cache_2183_ = lean_ctor_get(v___x_2177_, 5);
v_messages_2184_ = lean_ctor_get(v___x_2177_, 6);
v_infoState_2185_ = lean_ctor_get(v___x_2177_, 7);
v_snapshotTasks_2186_ = lean_ctor_get(v___x_2177_, 8);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2188_ = v___x_2177_;
v_isShared_2189_ = v_isSharedCheck_2209_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_snapshotTasks_2186_);
lean_inc(v_infoState_2185_);
lean_inc(v_messages_2184_);
lean_inc(v_cache_2183_);
lean_inc(v_traceState_2178_);
lean_inc(v_auxDeclNGen_2182_);
lean_inc(v_ngen_2181_);
lean_inc(v_nextMacroScope_2180_);
lean_inc(v_env_2179_);
lean_dec(v___x_2177_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2209_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
uint64_t v_tid_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2207_; 
v_tid_2190_ = lean_ctor_get_uint64(v_traceState_2178_, sizeof(void*)*1);
v_isSharedCheck_2207_ = !lean_is_exclusive(v_traceState_2178_);
if (v_isSharedCheck_2207_ == 0)
{
lean_object* v_unused_2208_; 
v_unused_2208_ = lean_ctor_get(v_traceState_2178_, 0);
lean_dec(v_unused_2208_);
v___x_2192_ = v_traceState_2178_;
v_isShared_2193_ = v_isSharedCheck_2207_;
goto v_resetjp_2191_;
}
else
{
lean_dec(v_traceState_2178_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2207_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2197_; 
v___x_2194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2194_, 0, v_ref_2137_);
lean_ctor_set(v___x_2194_, 1, v_a_2173_);
v___x_2195_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2135_, v___x_2194_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 0, v___x_2195_);
v___x_2197_ = v___x_2192_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2195_);
lean_ctor_set_uint64(v_reuseFailAlloc_2206_, sizeof(void*)*1, v_tid_2190_);
v___x_2197_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
lean_object* v___x_2199_; 
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 4, v___x_2197_);
v___x_2199_ = v___x_2188_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_env_2179_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v_nextMacroScope_2180_);
lean_ctor_set(v_reuseFailAlloc_2205_, 2, v_ngen_2181_);
lean_ctor_set(v_reuseFailAlloc_2205_, 3, v_auxDeclNGen_2182_);
lean_ctor_set(v_reuseFailAlloc_2205_, 4, v___x_2197_);
lean_ctor_set(v_reuseFailAlloc_2205_, 5, v_cache_2183_);
lean_ctor_set(v_reuseFailAlloc_2205_, 6, v_messages_2184_);
lean_ctor_set(v_reuseFailAlloc_2205_, 7, v_infoState_2185_);
lean_ctor_set(v_reuseFailAlloc_2205_, 8, v_snapshotTasks_2186_);
v___x_2199_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2203_; 
v___x_2200_ = lean_st_ref_set(v___y_2140_, v___x_2199_);
v___x_2201_ = lean_box(0);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 0, v___x_2201_);
v___x_2203_ = v___x_2175_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2201_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__4___boxed(lean_object* v_oldTraces_2213_, lean_object* v_data_2214_, lean_object* v_ref_2215_, lean_object* v_msg_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__4(v_oldTraces_2213_, v_data_2214_, v_ref_2215_, v_msg_2216_, v___y_2217_, v___y_2218_);
lean_dec(v___y_2218_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__5___redArg(lean_object* v_x_2221_){
_start:
{
if (lean_obj_tag(v_x_2221_) == 0)
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
v_a_2223_ = lean_ctor_get(v_x_2221_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_x_2221_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v_x_2221_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v_x_2221_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
lean_ctor_set_tag(v___x_2225_, 1);
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
v_a_2231_ = lean_ctor_get(v_x_2221_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v_x_2221_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v_x_2221_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v_x_2221_);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__5___redArg___boxed(lean_object* v_x_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__5___redArg(v_x_2239_);
return v_res_2241_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__0));
v___x_2244_ = l_Lean_stringToMessageData(v___x_2243_);
return v___x_2244_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2245_; double v___x_2246_; 
v___x_2245_ = lean_unsigned_to_nat(0u);
v___x_2246_ = lean_float_of_nat(v___x_2245_);
return v___x_2246_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__4(void){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__3));
v___x_2249_ = l_Lean_stringToMessageData(v___x_2248_);
return v___x_2249_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__5(void){
_start:
{
lean_object* v___x_2250_; double v___x_2251_; 
v___x_2250_ = lean_unsigned_to_nat(1000u);
v___x_2251_ = lean_float_of_nat(v___x_2250_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3(lean_object* v_cls_2252_, uint8_t v_collapsed_2253_, lean_object* v_tag_2254_, lean_object* v_opts_2255_, uint8_t v_clsEnabled_2256_, lean_object* v_oldTraces_2257_, lean_object* v_msg_2258_, lean_object* v_resStartStop_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v_fst_2263_; lean_object* v_snd_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2354_; 
v_fst_2263_ = lean_ctor_get(v_resStartStop_2259_, 0);
v_snd_2264_ = lean_ctor_get(v_resStartStop_2259_, 1);
v_isSharedCheck_2354_ = !lean_is_exclusive(v_resStartStop_2259_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2266_ = v_resStartStop_2259_;
v_isShared_2267_ = v_isSharedCheck_2354_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_snd_2264_);
lean_inc(v_fst_2263_);
lean_dec(v_resStartStop_2259_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2354_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v_data_2271_; lean_object* v_fst_2274_; lean_object* v_snd_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2353_; 
v_fst_2274_ = lean_ctor_get(v_snd_2264_, 0);
v_snd_2275_ = lean_ctor_get(v_snd_2264_, 1);
v_isSharedCheck_2353_ = !lean_is_exclusive(v_snd_2264_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2277_ = v_snd_2264_;
v_isShared_2278_ = v_isSharedCheck_2353_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_snd_2275_);
lean_inc(v_fst_2274_);
lean_dec(v_snd_2264_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2353_;
goto v_resetjp_2276_;
}
v___jp_2268_:
{
lean_object* v___x_2272_; 
v___x_2272_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__4(v_oldTraces_2257_, v_data_2271_, v___y_2270_, v___y_2269_, v___y_2260_, v___y_2261_);
lean_dec(v___y_2261_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v___x_2273_; 
lean_dec_ref(v___x_2272_);
v___x_2273_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__5___redArg(v_fst_2263_);
return v___x_2273_;
}
else
{
lean_dec(v_fst_2263_);
return v___x_2272_;
}
}
v_resetjp_2276_:
{
lean_object* v___x_2279_; uint8_t v___x_2280_; lean_object* v___y_2282_; lean_object* v_a_2283_; uint8_t v___y_2307_; double v___y_2338_; 
v___x_2279_ = l_Lean_trace_profiler;
v___x_2280_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2255_, v___x_2279_);
if (v___x_2280_ == 0)
{
v___y_2307_ = v___x_2280_;
goto v___jp_2306_;
}
else
{
lean_object* v___x_2343_; uint8_t v___x_2344_; 
v___x_2343_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2344_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2255_, v___x_2343_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; lean_object* v___x_2346_; double v___x_2347_; double v___x_2348_; double v___x_2349_; 
v___x_2345_ = l_Lean_trace_profiler_threshold;
v___x_2346_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__6(v_opts_2255_, v___x_2345_);
v___x_2347_ = lean_float_of_nat(v___x_2346_);
v___x_2348_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__5);
v___x_2349_ = lean_float_div(v___x_2347_, v___x_2348_);
v___y_2338_ = v___x_2349_;
goto v___jp_2337_;
}
else
{
lean_object* v___x_2350_; lean_object* v___x_2351_; double v___x_2352_; 
v___x_2350_ = l_Lean_trace_profiler_threshold;
v___x_2351_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__6(v_opts_2255_, v___x_2350_);
v___x_2352_ = lean_float_of_nat(v___x_2351_);
v___y_2338_ = v___x_2352_;
goto v___jp_2337_;
}
}
v___jp_2281_:
{
uint8_t v_result_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2289_; 
v_result_2284_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__3(v_fst_2263_);
v___x_2285_ = l_Lean_TraceResult_toEmoji(v_result_2284_);
v___x_2286_ = l_Lean_stringToMessageData(v___x_2285_);
v___x_2287_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__1);
if (v_isShared_2278_ == 0)
{
lean_ctor_set_tag(v___x_2277_, 7);
lean_ctor_set(v___x_2277_, 1, v___x_2287_);
lean_ctor_set(v___x_2277_, 0, v___x_2286_);
v___x_2289_ = v___x_2277_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2286_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v___x_2287_);
v___x_2289_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
lean_object* v_m_2291_; 
if (v_isShared_2267_ == 0)
{
lean_ctor_set_tag(v___x_2266_, 7);
lean_ctor_set(v___x_2266_, 1, v_a_2283_);
lean_ctor_set(v___x_2266_, 0, v___x_2289_);
v_m_2291_ = v___x_2266_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2289_);
lean_ctor_set(v_reuseFailAlloc_2299_, 1, v_a_2283_);
v_m_2291_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; double v___x_2294_; lean_object* v_data_2295_; 
v___x_2292_ = lean_box(v_result_2284_);
v___x_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
v___x_2294_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__2);
lean_inc_ref(v_tag_2254_);
lean_inc_ref(v___x_2293_);
lean_inc(v_cls_2252_);
v_data_2295_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2295_, 0, v_cls_2252_);
lean_ctor_set(v_data_2295_, 1, v___x_2293_);
lean_ctor_set(v_data_2295_, 2, v_tag_2254_);
lean_ctor_set_float(v_data_2295_, sizeof(void*)*3, v___x_2294_);
lean_ctor_set_float(v_data_2295_, sizeof(void*)*3 + 8, v___x_2294_);
lean_ctor_set_uint8(v_data_2295_, sizeof(void*)*3 + 16, v_collapsed_2253_);
if (v___x_2280_ == 0)
{
lean_dec_ref(v___x_2293_);
lean_dec(v_snd_2275_);
lean_dec(v_fst_2274_);
lean_dec_ref(v_tag_2254_);
lean_dec(v_cls_2252_);
v___y_2269_ = v_m_2291_;
v___y_2270_ = v___y_2282_;
v_data_2271_ = v_data_2295_;
goto v___jp_2268_;
}
else
{
lean_object* v_data_2296_; double v___x_2297_; double v___x_2298_; 
lean_dec_ref(v_data_2295_);
v_data_2296_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2296_, 0, v_cls_2252_);
lean_ctor_set(v_data_2296_, 1, v___x_2293_);
lean_ctor_set(v_data_2296_, 2, v_tag_2254_);
v___x_2297_ = lean_unbox_float(v_fst_2274_);
lean_dec(v_fst_2274_);
lean_ctor_set_float(v_data_2296_, sizeof(void*)*3, v___x_2297_);
v___x_2298_ = lean_unbox_float(v_snd_2275_);
lean_dec(v_snd_2275_);
lean_ctor_set_float(v_data_2296_, sizeof(void*)*3 + 8, v___x_2298_);
lean_ctor_set_uint8(v_data_2296_, sizeof(void*)*3 + 16, v_collapsed_2253_);
v___y_2269_ = v_m_2291_;
v___y_2270_ = v___y_2282_;
v_data_2271_ = v_data_2296_;
goto v___jp_2268_;
}
}
}
}
v___jp_2301_:
{
lean_object* v_ref_2302_; lean_object* v___x_2303_; 
v_ref_2302_ = lean_ctor_get(v___y_2260_, 5);
lean_inc(v___y_2261_);
lean_inc_ref(v___y_2260_);
lean_inc(v_fst_2263_);
v___x_2303_ = lean_apply_4(v_msg_2258_, v_fst_2263_, v___y_2260_, v___y_2261_, lean_box(0));
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref(v___x_2303_);
lean_inc(v_ref_2302_);
v___y_2282_ = v_ref_2302_;
v_a_2283_ = v_a_2304_;
goto v___jp_2281_;
}
else
{
lean_object* v___x_2305_; 
lean_dec_ref(v___x_2303_);
v___x_2305_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__4);
lean_inc(v_ref_2302_);
v___y_2282_ = v_ref_2302_;
v_a_2283_ = v___x_2305_;
goto v___jp_2281_;
}
}
v___jp_2306_:
{
if (v_clsEnabled_2256_ == 0)
{
if (v___y_2307_ == 0)
{
lean_object* v___x_2308_; lean_object* v_traceState_2309_; lean_object* v_env_2310_; lean_object* v_nextMacroScope_2311_; lean_object* v_ngen_2312_; lean_object* v_auxDeclNGen_2313_; lean_object* v_cache_2314_; lean_object* v_messages_2315_; lean_object* v_infoState_2316_; lean_object* v_snapshotTasks_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2336_; 
lean_del_object(v___x_2277_);
lean_dec(v_snd_2275_);
lean_dec(v_fst_2274_);
lean_del_object(v___x_2266_);
lean_dec_ref(v___y_2260_);
lean_dec_ref(v_msg_2258_);
lean_dec_ref(v_tag_2254_);
lean_dec(v_cls_2252_);
v___x_2308_ = lean_st_ref_take(v___y_2261_);
v_traceState_2309_ = lean_ctor_get(v___x_2308_, 4);
v_env_2310_ = lean_ctor_get(v___x_2308_, 0);
v_nextMacroScope_2311_ = lean_ctor_get(v___x_2308_, 1);
v_ngen_2312_ = lean_ctor_get(v___x_2308_, 2);
v_auxDeclNGen_2313_ = lean_ctor_get(v___x_2308_, 3);
v_cache_2314_ = lean_ctor_get(v___x_2308_, 5);
v_messages_2315_ = lean_ctor_get(v___x_2308_, 6);
v_infoState_2316_ = lean_ctor_get(v___x_2308_, 7);
v_snapshotTasks_2317_ = lean_ctor_get(v___x_2308_, 8);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2319_ = v___x_2308_;
v_isShared_2320_ = v_isSharedCheck_2336_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_snapshotTasks_2317_);
lean_inc(v_infoState_2316_);
lean_inc(v_messages_2315_);
lean_inc(v_cache_2314_);
lean_inc(v_traceState_2309_);
lean_inc(v_auxDeclNGen_2313_);
lean_inc(v_ngen_2312_);
lean_inc(v_nextMacroScope_2311_);
lean_inc(v_env_2310_);
lean_dec(v___x_2308_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2336_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
uint64_t v_tid_2321_; lean_object* v_traces_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2335_; 
v_tid_2321_ = lean_ctor_get_uint64(v_traceState_2309_, sizeof(void*)*1);
v_traces_2322_ = lean_ctor_get(v_traceState_2309_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v_traceState_2309_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2324_ = v_traceState_2309_;
v_isShared_2325_ = v_isSharedCheck_2335_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_traces_2322_);
lean_dec(v_traceState_2309_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2335_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2326_; lean_object* v___x_2328_; 
v___x_2326_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2257_, v_traces_2322_);
lean_dec_ref(v_traces_2322_);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v___x_2326_);
v___x_2328_ = v___x_2324_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2326_);
lean_ctor_set_uint64(v_reuseFailAlloc_2334_, sizeof(void*)*1, v_tid_2321_);
v___x_2328_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
lean_object* v___x_2330_; 
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 4, v___x_2328_);
v___x_2330_ = v___x_2319_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_env_2310_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_nextMacroScope_2311_);
lean_ctor_set(v_reuseFailAlloc_2333_, 2, v_ngen_2312_);
lean_ctor_set(v_reuseFailAlloc_2333_, 3, v_auxDeclNGen_2313_);
lean_ctor_set(v_reuseFailAlloc_2333_, 4, v___x_2328_);
lean_ctor_set(v_reuseFailAlloc_2333_, 5, v_cache_2314_);
lean_ctor_set(v_reuseFailAlloc_2333_, 6, v_messages_2315_);
lean_ctor_set(v_reuseFailAlloc_2333_, 7, v_infoState_2316_);
lean_ctor_set(v_reuseFailAlloc_2333_, 8, v_snapshotTasks_2317_);
v___x_2330_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2331_ = lean_st_ref_set(v___y_2261_, v___x_2330_);
lean_dec(v___y_2261_);
v___x_2332_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__5___redArg(v_fst_2263_);
return v___x_2332_;
}
}
}
}
}
else
{
goto v___jp_2301_;
}
}
else
{
goto v___jp_2301_;
}
}
v___jp_2337_:
{
double v___x_2339_; double v___x_2340_; double v___x_2341_; uint8_t v___x_2342_; 
v___x_2339_ = lean_unbox_float(v_snd_2275_);
v___x_2340_ = lean_unbox_float(v_fst_2274_);
v___x_2341_ = lean_float_sub(v___x_2339_, v___x_2340_);
v___x_2342_ = lean_float_decLt(v___y_2338_, v___x_2341_);
v___y_2307_ = v___x_2342_;
goto v___jp_2306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___boxed(lean_object* v_cls_2355_, lean_object* v_collapsed_2356_, lean_object* v_tag_2357_, lean_object* v_opts_2358_, lean_object* v_clsEnabled_2359_, lean_object* v_oldTraces_2360_, lean_object* v_msg_2361_, lean_object* v_resStartStop_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
uint8_t v_collapsed_boxed_2366_; uint8_t v_clsEnabled_boxed_2367_; lean_object* v_res_2368_; 
v_collapsed_boxed_2366_ = lean_unbox(v_collapsed_2356_);
v_clsEnabled_boxed_2367_ = lean_unbox(v_clsEnabled_2359_);
v_res_2368_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3(v_cls_2355_, v_collapsed_boxed_2366_, v_tag_2357_, v_opts_2358_, v_clsEnabled_boxed_2367_, v_oldTraces_2360_, v_msg_2361_, v_resStartStop_2362_, v___y_2363_, v___y_2364_);
lean_dec_ref(v_opts_2358_);
return v_res_2368_;
}
}
static double _init_l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2369_; double v___x_2370_; 
v___x_2369_ = lean_unsigned_to_nat(1000000000u);
v___x_2370_ = lean_float_of_nat(v___x_2369_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1(lean_object* v_decl_2371_, lean_object* v___x_2372_, uint8_t v___x_2373_, lean_object* v___x_2374_, lean_object* v___f_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v___y_2380_; lean_object* v___y_2381_; uint8_t v___y_2382_; lean_object* v___y_2393_; lean_object* v_a_2394_; lean_object* v___y_2398_; lean_object* v___y_2399_; uint8_t v___y_2400_; lean_object* v___y_2411_; lean_object* v_a_2412_; lean_object* v_options_2415_; uint8_t v_hasTrace_2416_; 
v_options_2415_ = lean_ctor_get(v___y_2376_, 2);
v_hasTrace_2416_ = lean_ctor_get_uint8(v_options_2415_, sizeof(void*)*1);
if (v_hasTrace_2416_ == 0)
{
lean_object* v_cancelTk_x3f_2417_; lean_object* v___x_2418_; 
lean_dec_ref(v___f_2375_);
lean_dec_ref(v___x_2374_);
lean_dec(v___x_2372_);
v_cancelTk_x3f_2417_ = lean_ctor_get(v___y_2376_, 12);
lean_inc(v___y_2377_);
lean_inc_ref(v___y_2376_);
lean_inc(v_decl_2371_);
v___x_2418_ = l_Lean_warnIfUsesSorry(v_decl_2371_, v___y_2376_, v___y_2377_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v___x_2419_; lean_object* v_env_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
lean_dec_ref(v___x_2418_);
v___x_2419_ = lean_st_ref_get(v___y_2377_);
v_env_2420_ = lean_ctor_get(v___x_2419_, 0);
lean_inc_ref(v_env_2420_);
lean_dec(v___x_2419_);
lean_inc(v_decl_2371_);
v___x_2421_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2420_, v_options_2415_, v_decl_2371_, v_cancelTk_x3f_2417_);
lean_inc_ref(v___y_2376_);
v___x_2422_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_2421_, v___y_2376_, v___y_2377_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2423_; lean_object* v___x_2424_; 
lean_dec_ref(v___y_2376_);
lean_dec(v_decl_2371_);
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_a_2423_);
lean_dec_ref(v___x_2422_);
v___x_2424_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_2423_, v___y_2377_);
lean_dec(v___y_2377_);
return v___x_2424_;
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
v_a_2425_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___x_2422_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2422_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
lean_inc(v_a_2425_);
if (v_isShared_2428_ == 0)
{
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
v___y_2411_ = v___x_2430_;
v_a_2412_ = v_a_2425_;
goto v___jp_2410_;
}
}
}
}
else
{
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v_decl_2371_);
return v___x_2418_;
}
}
else
{
lean_object* v_cancelTk_x3f_2433_; lean_object* v___x_2434_; lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2569_; 
v_cancelTk_x3f_2433_ = lean_ctor_get(v___y_2376_, 12);
lean_inc(v___x_2372_);
v___x_2434_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v___x_2372_, v___y_2376_);
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2437_ = v___x_2434_;
v_isShared_2438_ = v_isSharedCheck_2569_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2434_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2569_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v_a_2442_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v_a_2458_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v_a_2465_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; uint8_t v___y_2477_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v_a_2482_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v_a_2488_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v_a_2501_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v_a_2506_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; uint8_t v___y_2518_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v_a_2523_; uint8_t v___x_2551_; 
v___x_2551_ = lean_unbox(v_a_2435_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2552_; uint8_t v___x_2553_; 
v___x_2552_ = l_Lean_trace_profiler;
v___x_2553_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2415_, v___x_2552_);
if (v___x_2553_ == 0)
{
lean_object* v___x_2554_; 
lean_del_object(v___x_2437_);
lean_dec(v_a_2435_);
lean_dec_ref(v___f_2375_);
lean_dec_ref(v___x_2374_);
lean_dec(v___x_2372_);
lean_inc(v___y_2377_);
lean_inc_ref(v___y_2376_);
lean_inc(v_decl_2371_);
v___x_2554_ = l_Lean_warnIfUsesSorry(v_decl_2371_, v___y_2376_, v___y_2377_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v___x_2555_; lean_object* v_env_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
lean_dec_ref(v___x_2554_);
v___x_2555_ = lean_st_ref_get(v___y_2377_);
v_env_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc_ref(v_env_2556_);
lean_dec(v___x_2555_);
lean_inc(v_decl_2371_);
v___x_2557_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2556_, v_options_2415_, v_decl_2371_, v_cancelTk_x3f_2433_);
lean_inc_ref(v___y_2376_);
v___x_2558_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_2557_, v___y_2376_, v___y_2377_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2560_; 
lean_dec_ref(v___y_2376_);
lean_dec(v_decl_2371_);
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_a_2559_);
lean_dec_ref(v___x_2558_);
v___x_2560_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_2559_, v___y_2377_);
lean_dec(v___y_2377_);
return v___x_2560_;
}
else
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
v_a_2561_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2563_ = v___x_2558_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2558_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
lean_inc(v_a_2561_);
if (v_isShared_2564_ == 0)
{
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
v___y_2393_ = v___x_2566_;
v_a_2394_ = v_a_2561_;
goto v___jp_2392_;
}
}
}
}
else
{
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v_decl_2371_);
return v___x_2554_;
}
}
else
{
lean_inc_ref(v_options_2415_);
goto v___jp_2526_;
}
}
else
{
lean_inc_ref(v_options_2415_);
goto v___jp_2526_;
}
v___jp_2439_:
{
lean_object* v___x_2443_; double v___x_2444_; double v___x_2445_; double v___x_2446_; double v___x_2447_; double v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; uint8_t v___x_2453_; lean_object* v___x_2454_; 
v___x_2443_ = lean_io_mono_nanos_now();
v___x_2444_ = lean_float_of_nat(v___y_2441_);
v___x_2445_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0, &l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0);
v___x_2446_ = lean_float_div(v___x_2444_, v___x_2445_);
v___x_2447_ = lean_float_of_nat(v___x_2443_);
v___x_2448_ = lean_float_div(v___x_2447_, v___x_2445_);
v___x_2449_ = lean_box_float(v___x_2446_);
v___x_2450_ = lean_box_float(v___x_2448_);
v___x_2451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2449_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
v___x_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2452_, 0, v_a_2442_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
v___x_2453_ = lean_unbox(v_a_2435_);
lean_dec(v_a_2435_);
v___x_2454_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3(v___x_2372_, v___x_2373_, v___x_2374_, v_options_2415_, v___x_2453_, v___y_2440_, v___f_2375_, v___x_2452_, v___y_2376_, v___y_2377_);
lean_dec_ref(v_options_2415_);
return v___x_2454_;
}
v___jp_2455_:
{
lean_object* v___x_2460_; 
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 0, v_a_2458_);
v___x_2460_ = v___x_2437_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2458_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
v___y_2440_ = v___y_2456_;
v___y_2441_ = v___y_2457_;
v_a_2442_ = v___x_2460_;
goto v___jp_2439_;
}
}
v___jp_2462_:
{
lean_object* v___x_2466_; 
v___x_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2466_, 0, v_a_2465_);
v___y_2440_ = v___y_2463_;
v___y_2441_ = v___y_2464_;
v_a_2442_ = v___x_2466_;
goto v___jp_2439_;
}
v___jp_2467_:
{
if (lean_obj_tag(v___y_2470_) == 0)
{
lean_object* v_a_2471_; 
lean_del_object(v___x_2437_);
v_a_2471_ = lean_ctor_get(v___y_2470_, 0);
lean_inc(v_a_2471_);
lean_dec_ref(v___y_2470_);
v___y_2463_ = v___y_2468_;
v___y_2464_ = v___y_2469_;
v_a_2465_ = v_a_2471_;
goto v___jp_2462_;
}
else
{
lean_object* v_a_2472_; 
v_a_2472_ = lean_ctor_get(v___y_2470_, 0);
lean_inc(v_a_2472_);
lean_dec_ref(v___y_2470_);
v___y_2456_ = v___y_2468_;
v___y_2457_ = v___y_2469_;
v_a_2458_ = v_a_2472_;
goto v___jp_2455_;
}
}
v___jp_2473_:
{
if (v___y_2477_ == 0)
{
lean_object* v___x_2478_; 
lean_inc_ref(v___y_2376_);
v___x_2478_ = l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom(v_decl_2371_, v___y_2376_, v___y_2377_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_dec_ref(v___x_2478_);
v___y_2456_ = v___y_2474_;
v___y_2457_ = v___y_2475_;
v_a_2458_ = v___y_2476_;
goto v___jp_2455_;
}
else
{
lean_dec_ref(v___y_2476_);
v___y_2468_ = v___y_2474_;
v___y_2469_ = v___y_2475_;
v___y_2470_ = v___x_2478_;
goto v___jp_2467_;
}
}
else
{
lean_dec(v_decl_2371_);
v___y_2456_ = v___y_2474_;
v___y_2457_ = v___y_2475_;
v_a_2458_ = v___y_2476_;
goto v___jp_2455_;
}
}
v___jp_2479_:
{
uint8_t v___x_2483_; 
v___x_2483_ = l_Lean_Exception_isInterrupt(v_a_2482_);
if (v___x_2483_ == 0)
{
uint8_t v___x_2484_; 
lean_inc_ref(v_a_2482_);
v___x_2484_ = l_Lean_Exception_isRuntime(v_a_2482_);
v___y_2474_ = v___y_2480_;
v___y_2475_ = v___y_2481_;
v___y_2476_ = v_a_2482_;
v___y_2477_ = v___x_2484_;
goto v___jp_2473_;
}
else
{
v___y_2474_ = v___y_2480_;
v___y_2475_ = v___y_2481_;
v___y_2476_ = v_a_2482_;
v___y_2477_ = v___x_2483_;
goto v___jp_2473_;
}
}
v___jp_2485_:
{
lean_object* v___x_2489_; double v___x_2490_; double v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; uint8_t v___x_2496_; lean_object* v___x_2497_; 
v___x_2489_ = lean_io_get_num_heartbeats();
v___x_2490_ = lean_float_of_nat(v___y_2487_);
v___x_2491_ = lean_float_of_nat(v___x_2489_);
v___x_2492_ = lean_box_float(v___x_2490_);
v___x_2493_ = lean_box_float(v___x_2491_);
v___x_2494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2492_);
lean_ctor_set(v___x_2494_, 1, v___x_2493_);
v___x_2495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2495_, 0, v_a_2488_);
lean_ctor_set(v___x_2495_, 1, v___x_2494_);
v___x_2496_ = lean_unbox(v_a_2435_);
lean_dec(v_a_2435_);
v___x_2497_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3(v___x_2372_, v___x_2373_, v___x_2374_, v_options_2415_, v___x_2496_, v___y_2486_, v___f_2375_, v___x_2495_, v___y_2376_, v___y_2377_);
lean_dec_ref(v_options_2415_);
return v___x_2497_;
}
v___jp_2498_:
{
lean_object* v___x_2502_; 
v___x_2502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2502_, 0, v_a_2501_);
v___y_2486_ = v___y_2499_;
v___y_2487_ = v___y_2500_;
v_a_2488_ = v___x_2502_;
goto v___jp_2485_;
}
v___jp_2503_:
{
lean_object* v___x_2507_; 
v___x_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2507_, 0, v_a_2506_);
v___y_2486_ = v___y_2504_;
v___y_2487_ = v___y_2505_;
v_a_2488_ = v___x_2507_;
goto v___jp_2485_;
}
v___jp_2508_:
{
if (lean_obj_tag(v___y_2511_) == 0)
{
lean_object* v_a_2512_; 
v_a_2512_ = lean_ctor_get(v___y_2511_, 0);
lean_inc(v_a_2512_);
lean_dec_ref(v___y_2511_);
v___y_2504_ = v___y_2509_;
v___y_2505_ = v___y_2510_;
v_a_2506_ = v_a_2512_;
goto v___jp_2503_;
}
else
{
lean_object* v_a_2513_; 
v_a_2513_ = lean_ctor_get(v___y_2511_, 0);
lean_inc(v_a_2513_);
lean_dec_ref(v___y_2511_);
v___y_2499_ = v___y_2509_;
v___y_2500_ = v___y_2510_;
v_a_2501_ = v_a_2513_;
goto v___jp_2498_;
}
}
v___jp_2514_:
{
if (v___y_2518_ == 0)
{
lean_object* v___x_2519_; 
lean_inc_ref(v___y_2376_);
v___x_2519_ = l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom(v_decl_2371_, v___y_2376_, v___y_2377_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_dec_ref(v___x_2519_);
v___y_2499_ = v___y_2515_;
v___y_2500_ = v___y_2516_;
v_a_2501_ = v___y_2517_;
goto v___jp_2498_;
}
else
{
lean_dec_ref(v___y_2517_);
v___y_2509_ = v___y_2515_;
v___y_2510_ = v___y_2516_;
v___y_2511_ = v___x_2519_;
goto v___jp_2508_;
}
}
else
{
lean_dec(v_decl_2371_);
v___y_2499_ = v___y_2515_;
v___y_2500_ = v___y_2516_;
v_a_2501_ = v___y_2517_;
goto v___jp_2498_;
}
}
v___jp_2520_:
{
uint8_t v___x_2524_; 
v___x_2524_ = l_Lean_Exception_isInterrupt(v_a_2523_);
if (v___x_2524_ == 0)
{
uint8_t v___x_2525_; 
lean_inc_ref(v_a_2523_);
v___x_2525_ = l_Lean_Exception_isRuntime(v_a_2523_);
v___y_2515_ = v___y_2521_;
v___y_2516_ = v___y_2522_;
v___y_2517_ = v_a_2523_;
v___y_2518_ = v___x_2525_;
goto v___jp_2514_;
}
else
{
v___y_2515_ = v___y_2521_;
v___y_2516_ = v___y_2522_;
v___y_2517_ = v_a_2523_;
v___y_2518_ = v___x_2524_;
goto v___jp_2514_;
}
}
v___jp_2526_:
{
lean_object* v___x_2527_; lean_object* v_a_2528_; lean_object* v___x_2529_; uint8_t v___x_2530_; 
v___x_2527_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___redArg(v___y_2377_);
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_a_2528_);
lean_dec_ref(v___x_2527_);
v___x_2529_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2530_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2415_, v___x_2529_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2531_ = lean_io_mono_nanos_now();
lean_inc(v___y_2377_);
lean_inc_ref(v___y_2376_);
lean_inc(v_decl_2371_);
v___x_2532_ = l_Lean_warnIfUsesSorry(v_decl_2371_, v___y_2376_, v___y_2377_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v___x_2533_; lean_object* v_env_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
lean_dec_ref(v___x_2532_);
v___x_2533_ = lean_st_ref_get(v___y_2377_);
v_env_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc_ref(v_env_2534_);
lean_dec(v___x_2533_);
lean_inc(v_decl_2371_);
v___x_2535_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2534_, v_options_2415_, v_decl_2371_, v_cancelTk_x3f_2433_);
lean_inc_ref(v___y_2376_);
v___x_2536_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_2535_, v___y_2376_, v___y_2377_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; lean_object* v___x_2538_; lean_object* v_a_2539_; 
lean_del_object(v___x_2437_);
lean_dec(v_decl_2371_);
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_a_2537_);
lean_dec_ref(v___x_2536_);
v___x_2538_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_2537_, v___y_2377_);
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2539_);
lean_dec_ref(v___x_2538_);
v___y_2463_ = v_a_2528_;
v___y_2464_ = v___x_2531_;
v_a_2465_ = v_a_2539_;
goto v___jp_2462_;
}
else
{
lean_object* v_a_2540_; 
v_a_2540_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_a_2540_);
lean_dec_ref(v___x_2536_);
v___y_2480_ = v_a_2528_;
v___y_2481_ = v___x_2531_;
v_a_2482_ = v_a_2540_;
goto v___jp_2479_;
}
}
else
{
lean_dec(v_decl_2371_);
v___y_2468_ = v_a_2528_;
v___y_2469_ = v___x_2531_;
v___y_2470_ = v___x_2532_;
goto v___jp_2467_;
}
}
else
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
lean_del_object(v___x_2437_);
v___x_2541_ = lean_io_get_num_heartbeats();
lean_inc(v___y_2377_);
lean_inc_ref(v___y_2376_);
lean_inc(v_decl_2371_);
v___x_2542_ = l_Lean_warnIfUsesSorry(v_decl_2371_, v___y_2376_, v___y_2377_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v___x_2543_; lean_object* v_env_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
lean_dec_ref(v___x_2542_);
v___x_2543_ = lean_st_ref_get(v___y_2377_);
v_env_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc_ref(v_env_2544_);
lean_dec(v___x_2543_);
lean_inc(v_decl_2371_);
v___x_2545_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2544_, v_options_2415_, v_decl_2371_, v_cancelTk_x3f_2433_);
lean_inc_ref(v___y_2376_);
v___x_2546_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_2545_, v___y_2376_, v___y_2377_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; lean_object* v___x_2548_; lean_object* v_a_2549_; 
lean_dec(v_decl_2371_);
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_a_2547_);
lean_dec_ref(v___x_2546_);
v___x_2548_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_2547_, v___y_2377_);
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref(v___x_2548_);
v___y_2504_ = v_a_2528_;
v___y_2505_ = v___x_2541_;
v_a_2506_ = v_a_2549_;
goto v___jp_2503_;
}
else
{
lean_object* v_a_2550_; 
v_a_2550_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_a_2550_);
lean_dec_ref(v___x_2546_);
v___y_2521_ = v_a_2528_;
v___y_2522_ = v___x_2541_;
v_a_2523_ = v_a_2550_;
goto v___jp_2520_;
}
}
else
{
lean_dec(v_decl_2371_);
v___y_2509_ = v_a_2528_;
v___y_2510_ = v___x_2541_;
v___y_2511_ = v___x_2542_;
goto v___jp_2508_;
}
}
}
}
}
v___jp_2379_:
{
if (v___y_2382_ == 0)
{
lean_object* v___x_2383_; 
lean_dec_ref(v___y_2381_);
v___x_2383_ = l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom(v_decl_2371_, v___y_2376_, v___y_2377_);
lean_dec(v___y_2377_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2390_; 
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2390_ == 0)
{
lean_object* v_unused_2391_; 
v_unused_2391_ = lean_ctor_get(v___x_2383_, 0);
lean_dec(v_unused_2391_);
v___x_2385_ = v___x_2383_;
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
else
{
lean_dec(v___x_2383_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2388_; 
if (v_isShared_2386_ == 0)
{
lean_ctor_set_tag(v___x_2385_, 1);
lean_ctor_set(v___x_2385_, 0, v___y_2380_);
v___x_2388_ = v___x_2385_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___y_2380_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
else
{
lean_dec_ref(v___y_2380_);
return v___x_2383_;
}
}
else
{
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v_decl_2371_);
return v___y_2381_;
}
}
v___jp_2392_:
{
uint8_t v___x_2395_; 
v___x_2395_ = l_Lean_Exception_isInterrupt(v_a_2394_);
if (v___x_2395_ == 0)
{
uint8_t v___x_2396_; 
lean_inc_ref(v_a_2394_);
v___x_2396_ = l_Lean_Exception_isRuntime(v_a_2394_);
v___y_2380_ = v_a_2394_;
v___y_2381_ = v___y_2393_;
v___y_2382_ = v___x_2396_;
goto v___jp_2379_;
}
else
{
v___y_2380_ = v_a_2394_;
v___y_2381_ = v___y_2393_;
v___y_2382_ = v___x_2395_;
goto v___jp_2379_;
}
}
v___jp_2397_:
{
if (v___y_2400_ == 0)
{
lean_object* v___x_2401_; 
lean_dec_ref(v___y_2399_);
v___x_2401_ = l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom(v_decl_2371_, v___y_2376_, v___y_2377_);
lean_dec(v___y_2377_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2408_; 
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2408_ == 0)
{
lean_object* v_unused_2409_; 
v_unused_2409_ = lean_ctor_get(v___x_2401_, 0);
lean_dec(v_unused_2409_);
v___x_2403_ = v___x_2401_;
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
else
{
lean_dec(v___x_2401_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
lean_ctor_set_tag(v___x_2403_, 1);
lean_ctor_set(v___x_2403_, 0, v___y_2398_);
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___y_2398_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
else
{
lean_dec_ref(v___y_2398_);
return v___x_2401_;
}
}
else
{
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v_decl_2371_);
return v___y_2399_;
}
}
v___jp_2410_:
{
uint8_t v___x_2413_; 
v___x_2413_ = l_Lean_Exception_isInterrupt(v_a_2412_);
if (v___x_2413_ == 0)
{
uint8_t v___x_2414_; 
lean_inc_ref(v_a_2412_);
v___x_2414_ = l_Lean_Exception_isRuntime(v_a_2412_);
v___y_2398_ = v_a_2412_;
v___y_2399_ = v___y_2411_;
v___y_2400_ = v___x_2414_;
goto v___jp_2397_;
}
else
{
v___y_2398_ = v_a_2412_;
v___y_2399_ = v___y_2411_;
v___y_2400_ = v___x_2413_;
goto v___jp_2397_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___boxed(lean_object* v_decl_2570_, lean_object* v___x_2571_, lean_object* v___x_2572_, lean_object* v___x_2573_, lean_object* v___f_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
uint8_t v___x_7934__boxed_2578_; lean_object* v_res_2579_; 
v___x_7934__boxed_2578_ = lean_unbox(v___x_2572_);
v_res_2579_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1(v_decl_2570_, v___x_2571_, v___x_7934__boxed_2578_, v___x_2573_, v___f_2574_, v___y_2575_, v___y_2576_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(lean_object* v_decl_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_){
_start:
{
lean_object* v_options_2588_; lean_object* v___f_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; uint8_t v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___f_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v_options_2588_ = lean_ctor_get(v_a_2585_, 2);
lean_inc_ref(v_options_2588_);
lean_inc(v_decl_2584_);
v___f_2589_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2589_, 0, v_decl_2584_);
v___x_2590_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___closed__0));
v___x_2591_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___closed__2));
v___x_2592_ = 1;
v___x_2593_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2594_ = lean_box(v___x_2592_);
v___f_2595_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___boxed), 8, 5);
lean_closure_set(v___f_2595_, 0, v_decl_2584_);
lean_closure_set(v___f_2595_, 1, v___x_2591_);
lean_closure_set(v___f_2595_, 2, v___x_2594_);
lean_closure_set(v___f_2595_, 3, v___x_2593_);
lean_closure_set(v___f_2595_, 4, v___f_2589_);
v___x_2596_ = lean_box(0);
v___x_2597_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__4___redArg(v___x_2590_, v_options_2588_, v___f_2595_, v___x_2596_, v_a_2585_, v_a_2586_);
lean_dec_ref(v_options_2588_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___boxed(lean_object* v_decl_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_2598_, v_a_2599_, v_a_2600_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__5(lean_object* v_00_u03b1_2603_, lean_object* v_x_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v___x_2608_; 
v___x_2608_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__5___redArg(v_x_2604_);
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2609_, lean_object* v_x_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3_spec__5(v_00_u03b1_2609_, v_x_2610_, v___y_2611_, v___y_2612_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__0(lean_object* v___y_2615_, lean_object* v_a_2616_, lean_object* v___y_2617_, lean_object* v_a_x3f_2618_){
_start:
{
lean_object* v___x_2620_; lean_object* v_env_2621_; lean_object* v___x_2622_; 
v___x_2620_ = lean_st_ref_get(v___y_2615_);
v_env_2621_ = lean_ctor_get(v___x_2620_, 0);
lean_inc_ref(v_env_2621_);
lean_dec(v___x_2620_);
v___x_2622_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2616_, v_env_2621_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___x_2622_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2622_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2623_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
else
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2643_; 
v_a_2631_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2633_ = v___x_2622_;
v_isShared_2634_ = v_isSharedCheck_2643_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2622_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2643_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v_ref_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2641_; 
v_ref_2635_ = lean_ctor_get(v___y_2617_, 5);
v___x_2636_ = lean_io_error_to_string(v_a_2631_);
v___x_2637_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2636_);
v___x_2638_ = l_Lean_MessageData_ofFormat(v___x_2637_);
lean_inc(v_ref_2635_);
v___x_2639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2639_, 0, v_ref_2635_);
lean_ctor_set(v___x_2639_, 1, v___x_2638_);
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 0, v___x_2639_);
v___x_2641_ = v___x_2633_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2639_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__0___boxed(lean_object* v___y_2644_, lean_object* v_a_2645_, lean_object* v___y_2646_, lean_object* v_a_x3f_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l_Lean_addDecl___lam__0(v___y_2644_, v_a_2645_, v___y_2646_, v_a_x3f_2647_);
lean_dec(v_a_x3f_2647_);
lean_dec_ref(v___y_2646_);
lean_dec(v___y_2644_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__2(lean_object* v_asyncEnv_2650_, lean_object* v_a_2651_, lean_object* v_decl_2652_, lean_object* v_x_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v___x_2657_; lean_object* v_r_2658_; 
v___x_2657_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_asyncEnv_2650_, v___y_2655_);
lean_dec_ref(v___x_2657_);
lean_inc(v___y_2655_);
lean_inc_ref(v___y_2654_);
v_r_2658_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_2652_, v___y_2654_, v___y_2655_);
if (lean_obj_tag(v_r_2658_) == 0)
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2675_; 
v_a_2659_ = lean_ctor_get(v_r_2658_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v_r_2658_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2661_ = v_r_2658_;
v_isShared_2662_ = v_isSharedCheck_2675_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v_r_2658_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2675_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
lean_inc(v_a_2659_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set_tag(v___x_2661_, 1);
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2659_);
v___x_2664_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
lean_object* v___x_2665_; 
v___x_2665_ = l_Lean_addDecl___lam__0(v___y_2655_, v_a_2651_, v___y_2654_, v___x_2664_);
lean_dec_ref(v___x_2664_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2655_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2672_ == 0)
{
lean_object* v_unused_2673_; 
v_unused_2673_ = lean_ctor_get(v___x_2665_, 0);
lean_dec(v_unused_2673_);
v___x_2667_ = v___x_2665_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_dec(v___x_2665_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 0, v_a_2659_);
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2659_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
else
{
lean_dec(v_a_2659_);
return v___x_2665_;
}
}
}
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v_a_2676_ = lean_ctor_get(v_r_2658_, 0);
lean_inc(v_a_2676_);
lean_dec_ref(v_r_2658_);
v___x_2677_ = lean_box(0);
v___x_2678_ = l_Lean_addDecl___lam__0(v___y_2655_, v_a_2651_, v___y_2654_, v___x_2677_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2655_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2685_ == 0)
{
lean_object* v_unused_2686_; 
v_unused_2686_ = lean_ctor_get(v___x_2678_, 0);
lean_dec(v_unused_2686_);
v___x_2680_ = v___x_2678_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_dec(v___x_2678_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
lean_ctor_set_tag(v___x_2680_, 1);
lean_ctor_set(v___x_2680_, 0, v_a_2676_);
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2676_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
else
{
lean_dec(v_a_2676_);
return v___x_2678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__2___boxed(lean_object* v_asyncEnv_2687_, lean_object* v_a_2688_, lean_object* v_decl_2689_, lean_object* v_x_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l_Lean_addDecl___lam__2(v_asyncEnv_2687_, v_a_2688_, v_decl_2689_, v_x_2690_, v___y_2691_, v___y_2692_);
lean_dec_ref(v_x_2690_);
return v_res_2694_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2696_ = ((lean_object*)(l_Lean_addDecl___lam__1___closed__0));
v___x_2697_ = l_Lean_stringToMessageData(v___x_2696_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__1(lean_object* v_decl_2698_, lean_object* v_x_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2703_ = lean_obj_once(&l_Lean_addDecl___lam__1___closed__1, &l_Lean_addDecl___lam__1___closed__1_once, _init_l_Lean_addDecl___lam__1___closed__1);
v___x_2704_ = l_Lean_Declaration_getNames(v_decl_2698_);
v___x_2705_ = lean_box(0);
v___x_2706_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__0(v___x_2704_, v___x_2705_);
v___x_2707_ = l_Lean_MessageData_ofList(v___x_2706_);
v___x_2708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2703_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v___x_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__1___boxed(lean_object* v_decl_2710_, lean_object* v_x_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_Lean_addDecl___lam__1(v_decl_2710_, v_x_2711_, v___y_2712_, v___y_2713_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec_ref(v_x_2711_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_addDecl_spec__0(lean_object* v_cls_2718_, lean_object* v_msg_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
lean_object* v_ref_2723_; lean_object* v___x_2724_; lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2769_; 
v_ref_2723_ = lean_ctor_get(v___y_2720_, 5);
v___x_2724_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2719_, v___y_2720_, v___y_2721_);
v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2727_ = v___x_2724_;
v_isShared_2728_ = v_isSharedCheck_2769_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2724_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2769_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2729_; lean_object* v_traceState_2730_; lean_object* v_env_2731_; lean_object* v_nextMacroScope_2732_; lean_object* v_ngen_2733_; lean_object* v_auxDeclNGen_2734_; lean_object* v_cache_2735_; lean_object* v_messages_2736_; lean_object* v_infoState_2737_; lean_object* v_snapshotTasks_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2768_; 
v___x_2729_ = lean_st_ref_take(v___y_2721_);
v_traceState_2730_ = lean_ctor_get(v___x_2729_, 4);
v_env_2731_ = lean_ctor_get(v___x_2729_, 0);
v_nextMacroScope_2732_ = lean_ctor_get(v___x_2729_, 1);
v_ngen_2733_ = lean_ctor_get(v___x_2729_, 2);
v_auxDeclNGen_2734_ = lean_ctor_get(v___x_2729_, 3);
v_cache_2735_ = lean_ctor_get(v___x_2729_, 5);
v_messages_2736_ = lean_ctor_get(v___x_2729_, 6);
v_infoState_2737_ = lean_ctor_get(v___x_2729_, 7);
v_snapshotTasks_2738_ = lean_ctor_get(v___x_2729_, 8);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2740_ = v___x_2729_;
v_isShared_2741_ = v_isSharedCheck_2768_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_snapshotTasks_2738_);
lean_inc(v_infoState_2737_);
lean_inc(v_messages_2736_);
lean_inc(v_cache_2735_);
lean_inc(v_traceState_2730_);
lean_inc(v_auxDeclNGen_2734_);
lean_inc(v_ngen_2733_);
lean_inc(v_nextMacroScope_2732_);
lean_inc(v_env_2731_);
lean_dec(v___x_2729_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2768_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
uint64_t v_tid_2742_; lean_object* v_traces_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2767_; 
v_tid_2742_ = lean_ctor_get_uint64(v_traceState_2730_, sizeof(void*)*1);
v_traces_2743_ = lean_ctor_get(v_traceState_2730_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v_traceState_2730_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2745_ = v_traceState_2730_;
v_isShared_2746_ = v_isSharedCheck_2767_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_traces_2743_);
lean_dec(v_traceState_2730_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2767_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2747_; double v___x_2748_; uint8_t v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2757_; 
v___x_2747_ = lean_box(0);
v___x_2748_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___closed__2);
v___x_2749_ = 0;
v___x_2750_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2751_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2751_, 0, v_cls_2718_);
lean_ctor_set(v___x_2751_, 1, v___x_2747_);
lean_ctor_set(v___x_2751_, 2, v___x_2750_);
lean_ctor_set_float(v___x_2751_, sizeof(void*)*3, v___x_2748_);
lean_ctor_set_float(v___x_2751_, sizeof(void*)*3 + 8, v___x_2748_);
lean_ctor_set_uint8(v___x_2751_, sizeof(void*)*3 + 16, v___x_2749_);
v___x_2752_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_addDecl_spec__0___closed__0));
v___x_2753_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2751_);
lean_ctor_set(v___x_2753_, 1, v_a_2725_);
lean_ctor_set(v___x_2753_, 2, v___x_2752_);
lean_inc(v_ref_2723_);
v___x_2754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2754_, 0, v_ref_2723_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
v___x_2755_ = l_Lean_PersistentArray_push___redArg(v_traces_2743_, v___x_2754_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v___x_2755_);
v___x_2757_ = v___x_2745_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2755_);
lean_ctor_set_uint64(v_reuseFailAlloc_2766_, sizeof(void*)*1, v_tid_2742_);
v___x_2757_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
lean_object* v___x_2759_; 
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 4, v___x_2757_);
v___x_2759_ = v___x_2740_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_env_2731_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v_nextMacroScope_2732_);
lean_ctor_set(v_reuseFailAlloc_2765_, 2, v_ngen_2733_);
lean_ctor_set(v_reuseFailAlloc_2765_, 3, v_auxDeclNGen_2734_);
lean_ctor_set(v_reuseFailAlloc_2765_, 4, v___x_2757_);
lean_ctor_set(v_reuseFailAlloc_2765_, 5, v_cache_2735_);
lean_ctor_set(v_reuseFailAlloc_2765_, 6, v_messages_2736_);
lean_ctor_set(v_reuseFailAlloc_2765_, 7, v_infoState_2737_);
lean_ctor_set(v_reuseFailAlloc_2765_, 8, v_snapshotTasks_2738_);
v___x_2759_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2763_; 
v___x_2760_ = lean_st_ref_set(v___y_2721_, v___x_2759_);
v___x_2761_ = lean_box(0);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 0, v___x_2761_);
v___x_2763_ = v___x_2727_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2761_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_addDecl_spec__0___boxed(lean_object* v_cls_2770_, lean_object* v_msg_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_2770_, v_msg_2771_, v___y_2772_, v___y_2773_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
return v_res_2775_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2777_ = ((lean_object*)(l_Lean_addDecl___lam__3___closed__0));
v___x_2778_ = l_Lean_stringToMessageData(v___x_2777_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__3(lean_object* v_cls_2779_, lean_object* v_decl_2780_, lean_object* v_x_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
lean_object* v___x_2785_; lean_object* v_a_2786_; uint8_t v___x_2787_; 
lean_inc(v_cls_2779_);
v___x_2785_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_2779_, v___y_2782_);
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_a_2786_);
lean_dec_ref(v___x_2785_);
v___x_2787_ = lean_unbox(v_a_2786_);
lean_dec(v_a_2786_);
if (v___x_2787_ == 0)
{
lean_object* v___x_2788_; 
lean_dec(v_cls_2779_);
v___x_2788_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_2780_, v___y_2782_, v___y_2783_);
return v___x_2788_;
}
else
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = lean_obj_once(&l_Lean_addDecl___lam__3___closed__1, &l_Lean_addDecl___lam__3___closed__1_once, _init_l_Lean_addDecl___lam__3___closed__1);
v___x_2790_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_2779_, v___x_2789_, v___y_2782_, v___y_2783_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v___x_2791_; 
lean_dec_ref(v___x_2790_);
v___x_2791_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_2780_, v___y_2782_, v___y_2783_);
return v___x_2791_;
}
else
{
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
lean_dec(v_decl_2780_);
return v___x_2790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__3___boxed(lean_object* v_cls_2792_, lean_object* v_decl_2793_, lean_object* v_x_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l_Lean_addDecl___lam__3(v_cls_2792_, v_decl_2793_, v_x_2794_, v___y_2795_, v___y_2796_);
lean_dec(v_x_2794_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_addDecl_spec__2___redArg(lean_object* v_opt_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v_options_2802_; uint8_t v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v_options_2802_ = lean_ctor_get(v___y_2800_, 2);
v___x_2803_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2802_, v_opt_2799_);
v___x_2804_ = lean_box(v___x_2803_);
v___x_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_addDecl_spec__2___redArg___boxed(lean_object* v_opt_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__2___redArg(v_opt_2806_, v___y_2807_);
lean_dec_ref(v___y_2807_);
lean_dec_ref(v_opt_2806_);
return v_res_2809_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__8___closed__2(void){
_start:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2812_ = ((lean_object*)(l_Lean_addDecl___lam__8___closed__1));
v___x_2813_ = l_Lean_stringToMessageData(v___x_2812_);
return v___x_2813_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__8___closed__4(void){
_start:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2815_ = ((lean_object*)(l_Lean_addDecl___lam__8___closed__3));
v___x_2816_ = l_Lean_stringToMessageData(v___x_2815_);
return v___x_2816_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__8___closed__6(void){
_start:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2818_ = ((lean_object*)(l_Lean_addDecl___lam__8___closed__5));
v___x_2819_ = l_Lean_stringToMessageData(v___x_2818_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__8(lean_object* v_decl_2820_, lean_object* v___x_2821_, uint8_t v_hasTrace_2822_, uint8_t v___x_2823_, lean_object* v___x_2824_, lean_object* v_cls_2825_, lean_object* v___x_2826_, lean_object* v_____x_2827_, lean_object* v_exportedInfo_x3f_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_){
_start:
{
lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v_a_2835_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v_a_2848_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v_snd_2932_; lean_object* v_fst_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_3052_; 
v_snd_2932_ = lean_ctor_get(v_____x_2827_, 1);
v_fst_2933_ = lean_ctor_get(v_____x_2827_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v_____x_2827_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_2935_ = v_____x_2827_;
v_isShared_2936_ = v_isSharedCheck_3052_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_snd_2932_);
lean_inc(v_fst_2933_);
lean_dec(v_____x_2827_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_3052_;
goto v_resetjp_2934_;
}
v___jp_2832_:
{
lean_object* v___x_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
v___x_2836_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_2833_, v___y_2834_);
lean_dec(v___y_2834_);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2843_ == 0)
{
lean_object* v_unused_2844_; 
v_unused_2844_ = lean_ctor_get(v___x_2836_, 0);
lean_dec(v_unused_2844_);
v___x_2838_ = v___x_2836_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_dec(v___x_2836_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
if (v_isShared_2839_ == 0)
{
lean_ctor_set_tag(v___x_2838_, 1);
lean_ctor_set(v___x_2838_, 0, v_a_2835_);
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_a_2835_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
v___jp_2845_:
{
lean_object* v___x_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
v___x_2849_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_2846_, v___y_2847_);
lean_dec(v___y_2847_);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2856_ == 0)
{
lean_object* v_unused_2857_; 
v_unused_2857_ = lean_ctor_get(v___x_2849_, 0);
lean_dec(v_unused_2857_);
v___x_2851_ = v___x_2849_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_dec(v___x_2849_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 0, v_a_2848_);
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2848_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
v___jp_2858_:
{
lean_object* v___x_2869_; 
lean_inc_ref(v___y_2863_);
v___x_2869_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_2864_, v___y_2863_, v___y_2867_, v___y_2868_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v___x_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2917_; 
lean_dec_ref(v___x_2869_);
lean_inc_ref(v___y_2859_);
v___x_2870_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_2859_, v___y_2861_);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2917_ == 0)
{
lean_object* v_unused_2918_; 
v_unused_2918_ = lean_ctor_get(v___x_2870_, 0);
lean_dec(v_unused_2918_);
v___x_2872_ = v___x_2870_;
v_isShared_2873_ = v_isSharedCheck_2917_;
goto v_resetjp_2871_;
}
else
{
lean_dec(v___x_2870_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2917_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v_options_2874_; lean_object* v___x_2875_; uint8_t v___x_2876_; 
v_options_2874_ = lean_ctor_get(v___y_2862_, 2);
v___x_2875_ = l_Lean_Elab_async;
v___x_2876_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2874_, v___x_2875_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2877_; lean_object* v_r_2878_; 
lean_del_object(v___x_2872_);
lean_dec_ref(v___y_2865_);
lean_dec_ref(v___y_2860_);
lean_dec_ref(v___x_2821_);
v___x_2877_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_2863_, v___y_2861_);
lean_dec_ref(v___x_2877_);
lean_inc(v___y_2861_);
v_r_2878_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_2820_, v___y_2862_, v___y_2861_);
if (lean_obj_tag(v_r_2878_) == 0)
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2888_; 
v_a_2879_ = lean_ctor_get(v_r_2878_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v_r_2878_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2881_ = v_r_2878_;
v_isShared_2882_ = v_isSharedCheck_2888_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v_r_2878_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2888_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
lean_inc(v_a_2879_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set_tag(v___x_2881_, 1);
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
lean_object* v___x_2885_; 
v___x_2885_ = lean_apply_2(v___y_2866_, v___x_2884_, lean_box(0));
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_dec_ref(v___x_2885_);
v___y_2846_ = v___y_2859_;
v___y_2847_ = v___y_2861_;
v_a_2848_ = v_a_2879_;
goto v___jp_2845_;
}
else
{
lean_object* v_a_2886_; 
lean_dec(v_a_2879_);
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_a_2886_);
lean_dec_ref(v___x_2885_);
v___y_2833_ = v___y_2859_;
v___y_2834_ = v___y_2861_;
v_a_2835_ = v_a_2886_;
goto v___jp_2832_;
}
}
}
}
else
{
lean_object* v_a_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v_a_2889_ = lean_ctor_get(v_r_2878_, 0);
lean_inc(v_a_2889_);
lean_dec_ref(v_r_2878_);
v___x_2890_ = lean_box(0);
v___x_2891_ = lean_apply_2(v___y_2866_, v___x_2890_, lean_box(0));
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_dec_ref(v___x_2891_);
v___y_2833_ = v___y_2859_;
v___y_2834_ = v___y_2861_;
v_a_2835_ = v_a_2889_;
goto v___jp_2832_;
}
else
{
lean_object* v_a_2892_; 
lean_dec(v_a_2889_);
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2892_);
lean_dec_ref(v___x_2891_);
v___y_2833_ = v___y_2859_;
v___y_2834_ = v___y_2861_;
v_a_2835_ = v_a_2892_;
goto v___jp_2832_;
}
}
}
else
{
lean_object* v___x_2893_; lean_object* v___x_2895_; 
lean_dec_ref(v___y_2866_);
lean_dec_ref(v___y_2863_);
lean_dec_ref(v___y_2859_);
lean_dec(v_decl_2820_);
v___x_2893_ = l_IO_CancelToken_new();
if (v_isShared_2873_ == 0)
{
lean_ctor_set_tag(v___x_2872_, 1);
lean_ctor_set(v___x_2872_, 0, v___x_2893_);
v___x_2895_ = v___x_2872_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v___x_2893_);
v___x_2895_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2896_ = ((lean_object*)(l_Lean_initFn___closed__5_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_2897_ = l_Lean_Name_mkStr2(v___x_2896_, v___x_2821_);
v___x_2898_ = l_Lean_Name_toString(v___x_2897_, v_hasTrace_2822_);
lean_inc_ref(v___x_2895_);
v___x_2899_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_2860_, v___x_2895_, v___x_2898_, v___y_2862_, v___y_2861_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; lean_object* v_checked_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
lean_inc(v_a_2900_);
lean_dec_ref(v___x_2899_);
v_checked_2901_ = lean_ctor_get(v___y_2865_, 2);
lean_inc_ref(v_checked_2901_);
lean_dec_ref(v___y_2865_);
v___x_2902_ = lean_unsigned_to_nat(0u);
v___x_2903_ = lean_io_map_task(v_a_2900_, v_checked_2901_, v___x_2902_, v___x_2823_);
v___x_2904_ = lean_box(0);
v___x_2905_ = lean_box(2);
v___x_2906_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2904_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
lean_ctor_set(v___x_2906_, 2, v___x_2895_);
lean_ctor_set(v___x_2906_, 3, v___x_2903_);
v___x_2907_ = l_Lean_Core_logSnapshotTask___redArg(v___x_2906_, v___y_2861_);
lean_dec(v___y_2861_);
return v___x_2907_;
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___y_2865_);
lean_dec(v___y_2861_);
v_a_2908_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2899_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2899_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2931_; 
lean_dec_ref(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec_ref(v___x_2821_);
lean_dec(v_decl_2820_);
v_a_2919_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2921_ = v___x_2869_;
v_isShared_2922_ = v_isSharedCheck_2931_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2869_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2931_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v_ref_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2929_; 
v_ref_2923_ = lean_ctor_get(v___y_2862_, 5);
lean_inc(v_ref_2923_);
lean_dec_ref(v___y_2862_);
v___x_2924_ = lean_io_error_to_string(v_a_2919_);
v___x_2925_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2924_);
v___x_2926_ = l_Lean_MessageData_ofFormat(v___x_2925_);
v___x_2927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2927_, 0, v_ref_2923_);
lean_ctor_set(v___x_2927_, 1, v___x_2926_);
if (v_isShared_2922_ == 0)
{
lean_ctor_set(v___x_2921_, 0, v___x_2927_);
v___x_2929_ = v___x_2921_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v___x_2927_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
}
v_resetjp_2934_:
{
lean_object* v_fst_2937_; lean_object* v_snd_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_3051_; 
v_fst_2937_ = lean_ctor_get(v_snd_2932_, 0);
v_snd_2938_ = lean_ctor_get(v_snd_2932_, 1);
v_isSharedCheck_3051_ = !lean_is_exclusive(v_snd_2932_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_2940_ = v_snd_2932_;
v_isShared_2941_ = v_isSharedCheck_3051_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_snd_2938_);
lean_inc(v_fst_2937_);
lean_dec(v_snd_2932_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_3051_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v_exportedInfo_x3f_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___x_3041_; lean_object* v_env_3042_; uint8_t v___x_3043_; 
v___x_3041_ = lean_st_ref_get(v___y_2830_);
v_env_3042_ = lean_ctor_get(v___x_3041_, 0);
lean_inc_ref(v_env_3042_);
lean_dec(v___x_3041_);
v___x_3043_ = l_Lean_Environment_containsOnBranch(v_env_3042_, v_fst_2933_);
if (v___x_3043_ == 0)
{
lean_del_object(v___x_2935_);
v___y_3017_ = v___y_2829_;
v___y_3018_ = v___y_2830_;
goto v___jp_3016_;
}
else
{
lean_object* v___x_3044_; lean_object* v_env_3045_; lean_object* v___x_3046_; lean_object* v___x_3048_; 
lean_del_object(v___x_2940_);
lean_dec(v_snd_2938_);
lean_dec(v_fst_2937_);
lean_dec(v_exportedInfo_x3f_2828_);
lean_dec(v___x_2826_);
lean_dec(v_cls_2825_);
lean_dec_ref(v___x_2824_);
lean_dec_ref(v___x_2821_);
lean_dec(v_decl_2820_);
v___x_3044_ = lean_st_ref_get(v___y_2830_);
v_env_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc_ref(v_env_3045_);
lean_dec(v___x_3044_);
v___x_3046_ = lean_elab_environment_to_kernel_env(v_env_3045_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set_tag(v___x_2935_, 1);
lean_ctor_set(v___x_2935_, 1, v_fst_2933_);
lean_ctor_set(v___x_2935_, 0, v___x_3046_);
v___x_3048_ = v___x_2935_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3046_);
lean_ctor_set(v_reuseFailAlloc_3050_, 1, v_fst_2933_);
v___x_3048_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
lean_object* v___x_3049_; 
v___x_3049_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(v___x_3048_, v___y_2829_, v___y_2830_);
lean_dec(v___y_2830_);
return v___x_3049_;
}
}
v___jp_2942_:
{
uint8_t v___x_2950_; lean_object* v___x_2951_; 
v___x_2950_ = lean_unbox(v_snd_2938_);
lean_dec(v_snd_2938_);
lean_inc_ref(v___y_2944_);
v___x_2951_ = l_Lean_Environment_addConstAsync(v___y_2944_, v_fst_2933_, v___x_2950_, v___y_2949_, v___x_2823_, v_hasTrace_2822_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v_mainEnv_2953_; lean_object* v_asyncEnv_2954_; lean_object* v___f_2955_; lean_object* v___f_2956_; lean_object* v___x_2957_; 
lean_del_object(v___x_2940_);
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref(v___x_2951_);
v_mainEnv_2953_ = lean_ctor_get(v_a_2952_, 0);
lean_inc_ref(v_mainEnv_2953_);
v_asyncEnv_2954_ = lean_ctor_get(v_a_2952_, 1);
lean_inc_ref(v_asyncEnv_2954_);
lean_inc(v_a_2952_);
v___f_2955_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2955_, 0, v___y_2943_);
lean_closure_set(v___f_2955_, 1, v_a_2952_);
lean_closure_set(v___f_2955_, 2, v___y_2945_);
lean_inc(v_decl_2820_);
lean_inc(v_a_2952_);
lean_inc_ref(v_asyncEnv_2954_);
v___f_2956_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__2___boxed), 7, 3);
lean_closure_set(v___f_2956_, 0, v_asyncEnv_2954_);
lean_closure_set(v___f_2956_, 1, v_a_2952_);
lean_closure_set(v___f_2956_, 2, v_decl_2820_);
v___x_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2957_, 0, v_fst_2937_);
if (lean_obj_tag(v___y_2946_) == 0)
{
lean_inc_ref(v___x_2957_);
v___y_2859_ = v_mainEnv_2953_;
v___y_2860_ = v___f_2956_;
v___y_2861_ = v___y_2947_;
v___y_2862_ = v___y_2948_;
v___y_2863_ = v_asyncEnv_2954_;
v___y_2864_ = v_a_2952_;
v___y_2865_ = v___y_2944_;
v___y_2866_ = v___f_2955_;
v___y_2867_ = v___x_2957_;
v___y_2868_ = v___x_2957_;
goto v___jp_2858_;
}
else
{
v___y_2859_ = v_mainEnv_2953_;
v___y_2860_ = v___f_2956_;
v___y_2861_ = v___y_2947_;
v___y_2862_ = v___y_2948_;
v___y_2863_ = v_asyncEnv_2954_;
v___y_2864_ = v_a_2952_;
v___y_2865_ = v___y_2944_;
v___y_2866_ = v___f_2955_;
v___y_2867_ = v___x_2957_;
v___y_2868_ = v___y_2946_;
goto v___jp_2858_;
}
}
else
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2972_; 
lean_dec(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec_ref(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec(v_fst_2937_);
lean_dec_ref(v___x_2821_);
lean_dec(v_decl_2820_);
v_a_2958_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2960_ = v___x_2951_;
v_isShared_2961_ = v_isSharedCheck_2972_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2951_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2972_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v_ref_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2967_; 
v_ref_2962_ = lean_ctor_get(v___y_2948_, 5);
lean_inc(v_ref_2962_);
lean_dec_ref(v___y_2948_);
v___x_2963_ = lean_io_error_to_string(v_a_2958_);
v___x_2964_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2963_);
v___x_2965_ = l_Lean_MessageData_ofFormat(v___x_2964_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 1, v___x_2965_);
lean_ctor_set(v___x_2940_, 0, v_ref_2962_);
v___x_2967_ = v___x_2940_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_ref_2962_);
lean_ctor_set(v_reuseFailAlloc_2971_, 1, v___x_2965_);
v___x_2967_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
lean_object* v___x_2969_; 
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 0, v___x_2967_);
v___x_2969_ = v___x_2960_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2967_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
}
v___jp_2973_:
{
lean_object* v___x_2977_; 
v___x_2977_ = lean_st_ref_get(v___y_2976_);
if (lean_obj_tag(v_exportedInfo_x3f_2974_) == 0)
{
lean_object* v_env_2978_; lean_object* v___x_2979_; 
v_env_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc_ref(v_env_2978_);
lean_dec(v___x_2977_);
v___x_2979_ = lean_box(0);
lean_inc_ref(v___y_2975_);
lean_inc(v___y_2976_);
v___y_2943_ = v___y_2976_;
v___y_2944_ = v_env_2978_;
v___y_2945_ = v___y_2975_;
v___y_2946_ = v_exportedInfo_x3f_2974_;
v___y_2947_ = v___y_2976_;
v___y_2948_ = v___y_2975_;
v___y_2949_ = v___x_2979_;
goto v___jp_2942_;
}
else
{
lean_object* v_env_2980_; lean_object* v_val_2981_; uint8_t v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
v_env_2980_ = lean_ctor_get(v___x_2977_, 0);
lean_inc_ref(v_env_2980_);
lean_dec(v___x_2977_);
v_val_2981_ = lean_ctor_get(v_exportedInfo_x3f_2974_, 0);
v___x_2982_ = l_Lean_ConstantKind_ofConstantInfo(v_val_2981_);
v___x_2983_ = lean_box(v___x_2982_);
v___x_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2983_);
lean_inc_ref(v___y_2975_);
lean_inc(v___y_2976_);
v___y_2943_ = v___y_2976_;
v___y_2944_ = v_env_2980_;
v___y_2945_ = v___y_2975_;
v___y_2946_ = v_exportedInfo_x3f_2974_;
v___y_2947_ = v___y_2976_;
v___y_2948_ = v___y_2975_;
v___y_2949_ = v___x_2984_;
goto v___jp_2942_;
}
}
v___jp_2985_:
{
lean_object* v___x_2988_; 
lean_inc(v_fst_2937_);
v___x_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2988_, 0, v_fst_2937_);
v_exportedInfo_x3f_2974_ = v___x_2988_;
v___y_2975_ = v___y_2986_;
v___y_2976_ = v___y_2987_;
goto v___jp_2973_;
}
v___jp_2989_:
{
lean_object* v___x_2992_; 
lean_inc(v_fst_2937_);
v___x_2992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2992_, 0, v_fst_2937_);
v_exportedInfo_x3f_2974_ = v___x_2992_;
v___y_2975_ = v___y_2990_;
v___y_2976_ = v___y_2991_;
goto v___jp_2973_;
}
v___jp_2993_:
{
lean_object* v___x_2996_; lean_object* v_env_2997_; lean_object* v_nextMacroScope_2998_; lean_object* v_ngen_2999_; lean_object* v_auxDeclNGen_3000_; lean_object* v_traceState_3001_; lean_object* v_messages_3002_; lean_object* v_infoState_3003_; lean_object* v_snapshotTasks_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3014_; 
v___x_2996_ = lean_st_ref_take(v___y_2994_);
v_env_2997_ = lean_ctor_get(v___x_2996_, 0);
v_nextMacroScope_2998_ = lean_ctor_get(v___x_2996_, 1);
v_ngen_2999_ = lean_ctor_get(v___x_2996_, 2);
v_auxDeclNGen_3000_ = lean_ctor_get(v___x_2996_, 3);
v_traceState_3001_ = lean_ctor_get(v___x_2996_, 4);
v_messages_3002_ = lean_ctor_get(v___x_2996_, 6);
v_infoState_3003_ = lean_ctor_get(v___x_2996_, 7);
v_snapshotTasks_3004_ = lean_ctor_get(v___x_2996_, 8);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3014_ == 0)
{
lean_object* v_unused_3015_; 
v_unused_3015_ = lean_ctor_get(v___x_2996_, 5);
lean_dec(v_unused_3015_);
v___x_3006_ = v___x_2996_;
v_isShared_3007_ = v_isSharedCheck_3014_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_snapshotTasks_3004_);
lean_inc(v_infoState_3003_);
lean_inc(v_messages_3002_);
lean_inc(v_traceState_3001_);
lean_inc(v_auxDeclNGen_3000_);
lean_inc(v_ngen_2999_);
lean_inc(v_nextMacroScope_2998_);
lean_inc(v_env_2997_);
lean_dec(v___x_2996_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3014_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3011_; 
v___x_3008_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_2938_);
lean_inc(v_fst_2933_);
v___x_3009_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3008_, v_env_2997_, v_fst_2933_, v_snd_2938_);
if (v_isShared_3007_ == 0)
{
lean_ctor_set(v___x_3006_, 5, v___x_2824_);
lean_ctor_set(v___x_3006_, 0, v___x_3009_);
v___x_3011_ = v___x_3006_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v___x_3009_);
lean_ctor_set(v_reuseFailAlloc_3013_, 1, v_nextMacroScope_2998_);
lean_ctor_set(v_reuseFailAlloc_3013_, 2, v_ngen_2999_);
lean_ctor_set(v_reuseFailAlloc_3013_, 3, v_auxDeclNGen_3000_);
lean_ctor_set(v_reuseFailAlloc_3013_, 4, v_traceState_3001_);
lean_ctor_set(v_reuseFailAlloc_3013_, 5, v___x_2824_);
lean_ctor_set(v_reuseFailAlloc_3013_, 6, v_messages_3002_);
lean_ctor_set(v_reuseFailAlloc_3013_, 7, v_infoState_3003_);
lean_ctor_set(v_reuseFailAlloc_3013_, 8, v_snapshotTasks_3004_);
v___x_3011_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
lean_object* v___x_3012_; 
v___x_3012_ = lean_st_ref_set(v___y_2994_, v___x_3011_);
v_exportedInfo_x3f_2974_ = v_exportedInfo_x3f_2828_;
v___y_2975_ = v___y_2995_;
v___y_2976_ = v___y_2994_;
goto v___jp_2973_;
}
}
}
v___jp_3016_:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; uint8_t v___x_3021_; 
lean_inc(v_decl_2820_);
v___x_3019_ = l_Lean_Declaration_getTopLevelNames(v_decl_2820_);
v___x_3020_ = ((lean_object*)(l_Lean_addDecl___lam__8___closed__0));
v___x_3021_ = l_List_all___redArg(v___x_3019_, v___x_3020_);
if (v___x_3021_ == 0)
{
lean_dec(v___x_2826_);
if (lean_obj_tag(v_exportedInfo_x3f_2828_) == 0)
{
if (v___x_2823_ == 0)
{
lean_object* v___x_3022_; lean_object* v_a_3023_; uint8_t v___x_3024_; 
lean_dec_ref(v___x_2824_);
lean_inc(v_cls_2825_);
v___x_3022_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_2825_, v___y_3017_);
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_a_3023_);
lean_dec_ref(v___x_3022_);
v___x_3024_ = lean_unbox(v_a_3023_);
lean_dec(v_a_3023_);
if (v___x_3024_ == 0)
{
lean_dec(v_cls_2825_);
v___y_2986_ = v___y_3017_;
v___y_2987_ = v___y_3018_;
goto v___jp_2985_;
}
else
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3025_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__2, &l_Lean_addDecl___lam__8___closed__2_once, _init_l_Lean_addDecl___lam__8___closed__2);
v___x_3026_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_2825_, v___x_3025_, v___y_3017_, v___y_3018_);
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_dec_ref(v___x_3026_);
v___y_2986_ = v___y_3017_;
v___y_2987_ = v___y_3018_;
goto v___jp_2985_;
}
else
{
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_del_object(v___x_2940_);
lean_dec(v_snd_2938_);
lean_dec(v_fst_2937_);
lean_dec(v_fst_2933_);
lean_dec_ref(v___x_2821_);
lean_dec(v_decl_2820_);
return v___x_3026_;
}
}
}
else
{
lean_dec(v_cls_2825_);
v___y_2994_ = v___y_3018_;
v___y_2995_ = v___y_3017_;
goto v___jp_2993_;
}
}
else
{
lean_dec(v_cls_2825_);
v___y_2994_ = v___y_3018_;
v___y_2995_ = v___y_3017_;
goto v___jp_2993_;
}
}
else
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v_a_3029_; uint8_t v___x_3030_; 
lean_dec(v_exportedInfo_x3f_2828_);
lean_dec_ref(v___x_2824_);
v___x_3027_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3028_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__2___redArg(v___x_3027_, v___y_3017_);
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_a_3029_);
lean_dec_ref(v___x_3028_);
v___x_3030_ = lean_unbox(v_a_3029_);
lean_dec(v_a_3029_);
if (v___x_3030_ == 0)
{
lean_object* v___x_3031_; lean_object* v_a_3032_; uint8_t v___x_3033_; 
lean_inc(v_cls_2825_);
v___x_3031_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_2825_, v___y_3017_);
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc(v_a_3032_);
lean_dec_ref(v___x_3031_);
v___x_3033_ = lean_unbox(v_a_3032_);
lean_dec(v_a_3032_);
if (v___x_3033_ == 0)
{
lean_dec(v_cls_2825_);
v_exportedInfo_x3f_2974_ = v___x_2826_;
v___y_2975_ = v___y_3017_;
v___y_2976_ = v___y_3018_;
goto v___jp_2973_;
}
else
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3034_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__4, &l_Lean_addDecl___lam__8___closed__4_once, _init_l_Lean_addDecl___lam__8___closed__4);
v___x_3035_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_2825_, v___x_3034_, v___y_3017_, v___y_3018_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_dec_ref(v___x_3035_);
v_exportedInfo_x3f_2974_ = v___x_2826_;
v___y_2975_ = v___y_3017_;
v___y_2976_ = v___y_3018_;
goto v___jp_2973_;
}
else
{
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_del_object(v___x_2940_);
lean_dec(v_snd_2938_);
lean_dec(v_fst_2937_);
lean_dec(v_fst_2933_);
lean_dec(v___x_2826_);
lean_dec_ref(v___x_2821_);
lean_dec(v_decl_2820_);
return v___x_3035_;
}
}
}
else
{
lean_object* v___x_3036_; lean_object* v_a_3037_; uint8_t v___x_3038_; 
lean_dec(v___x_2826_);
lean_inc(v_cls_2825_);
v___x_3036_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_2825_, v___y_3017_);
v_a_3037_ = lean_ctor_get(v___x_3036_, 0);
lean_inc(v_a_3037_);
lean_dec_ref(v___x_3036_);
v___x_3038_ = lean_unbox(v_a_3037_);
lean_dec(v_a_3037_);
if (v___x_3038_ == 0)
{
lean_dec(v_cls_2825_);
v___y_2990_ = v___y_3017_;
v___y_2991_ = v___y_3018_;
goto v___jp_2989_;
}
else
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3039_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__6, &l_Lean_addDecl___lam__8___closed__6_once, _init_l_Lean_addDecl___lam__8___closed__6);
v___x_3040_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_2825_, v___x_3039_, v___y_3017_, v___y_3018_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_dec_ref(v___x_3040_);
v___y_2990_ = v___y_3017_;
v___y_2991_ = v___y_3018_;
goto v___jp_2989_;
}
else
{
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_del_object(v___x_2940_);
lean_dec(v_snd_2938_);
lean_dec(v_fst_2937_);
lean_dec(v_fst_2933_);
lean_dec_ref(v___x_2821_);
lean_dec(v_decl_2820_);
return v___x_3040_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__8___boxed(lean_object* v_decl_3053_, lean_object* v___x_3054_, lean_object* v_hasTrace_3055_, lean_object* v___x_3056_, lean_object* v___x_3057_, lean_object* v_cls_3058_, lean_object* v___x_3059_, lean_object* v_____x_3060_, lean_object* v_exportedInfo_x3f_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_){
_start:
{
uint8_t v_hasTrace_boxed_3065_; uint8_t v___x_51741__boxed_3066_; lean_object* v_res_3067_; 
v_hasTrace_boxed_3065_ = lean_unbox(v_hasTrace_3055_);
v___x_51741__boxed_3066_ = lean_unbox(v___x_3056_);
v_res_3067_ = l_Lean_addDecl___lam__8(v_decl_3053_, v___x_3054_, v_hasTrace_boxed_3065_, v___x_51741__boxed_3066_, v___x_3057_, v_cls_3058_, v___x_3059_, v_____x_3060_, v_exportedInfo_x3f_3061_, v___y_3062_, v___y_3063_);
return v_res_3067_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__4___closed__1(void){
_start:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3069_ = ((lean_object*)(l_Lean_addDecl___lam__4___closed__0));
v___x_3070_ = l_Lean_stringToMessageData(v___x_3069_);
return v___x_3070_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__4___closed__3(void){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3072_ = ((lean_object*)(l_Lean_addDecl___lam__4___closed__2));
v___x_3073_ = l_Lean_stringToMessageData(v___x_3072_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__4(lean_object* v___f_3074_, lean_object* v_cls_3075_, lean_object* v___x_3076_, uint8_t v___x_3077_, uint8_t v_forceExpose_3078_, lean_object* v_defn_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
lean_object* v_exportedInfo_x3f_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v_env_3119_; lean_object* v_env_3120_; 
v___x_3105_ = lean_st_ref_get(v___y_3081_);
v___x_3106_ = lean_st_ref_get(v___y_3081_);
v_env_3119_ = lean_ctor_get(v___x_3105_, 0);
lean_inc_ref(v_env_3119_);
lean_dec(v___x_3105_);
v_env_3120_ = lean_ctor_get(v___x_3106_, 0);
lean_inc_ref(v_env_3120_);
lean_dec(v___x_3106_);
if (v_forceExpose_3078_ == 0)
{
goto v___jp_3121_;
}
else
{
if (v___x_3077_ == 0)
{
lean_dec_ref(v_env_3120_);
lean_dec_ref(v_env_3119_);
lean_dec(v_cls_3075_);
v_exportedInfo_x3f_3084_ = v___x_3076_;
v___y_3085_ = v___y_3080_;
v___y_3086_ = v___y_3081_;
goto v___jp_3083_;
}
else
{
goto v___jp_3121_;
}
}
v___jp_3083_:
{
lean_object* v_toConstantVal_3087_; lean_object* v_name_3088_; lean_object* v___x_3089_; uint8_t v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v_toConstantVal_3087_ = lean_ctor_get(v_defn_3079_, 0);
v_name_3088_ = lean_ctor_get(v_toConstantVal_3087_, 0);
lean_inc(v_name_3088_);
v___x_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3089_, 0, v_defn_3079_);
v___x_3090_ = 0;
v___x_3091_ = lean_box(v___x_3090_);
v___x_3092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3089_);
lean_ctor_set(v___x_3092_, 1, v___x_3091_);
v___x_3093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3093_, 0, v_name_3088_);
lean_ctor_set(v___x_3093_, 1, v___x_3092_);
v___x_3094_ = lean_apply_5(v___f_3074_, v___x_3093_, v_exportedInfo_x3f_3084_, v___y_3085_, v___y_3086_, lean_box(0));
return v___x_3094_;
}
v___jp_3095_:
{
lean_object* v_toConstantVal_3098_; uint8_t v_safety_3099_; uint8_t v___x_3100_; uint8_t v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v_toConstantVal_3098_ = lean_ctor_get(v_defn_3079_, 0);
v_safety_3099_ = lean_ctor_get_uint8(v_defn_3079_, sizeof(void*)*4);
v___x_3100_ = 0;
v___x_3101_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3099_, v___x_3100_);
lean_inc_ref(v_toConstantVal_3098_);
v___x_3102_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3102_, 0, v_toConstantVal_3098_);
lean_ctor_set_uint8(v___x_3102_, sizeof(void*)*1, v___x_3101_);
v___x_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
v___x_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3103_);
v_exportedInfo_x3f_3084_ = v___x_3104_;
v___y_3085_ = v___y_3096_;
v___y_3086_ = v___y_3097_;
goto v___jp_3083_;
}
v___jp_3107_:
{
lean_object* v___x_3108_; lean_object* v_a_3109_; uint8_t v___x_3110_; 
lean_inc(v_cls_3075_);
v___x_3108_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_3075_, v___y_3080_);
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
lean_inc(v_a_3109_);
lean_dec_ref(v___x_3108_);
v___x_3110_ = lean_unbox(v_a_3109_);
lean_dec(v_a_3109_);
if (v___x_3110_ == 0)
{
lean_dec(v_cls_3075_);
v___y_3096_ = v___y_3080_;
v___y_3097_ = v___y_3081_;
goto v___jp_3095_;
}
else
{
lean_object* v_toConstantVal_3111_; lean_object* v_name_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v_toConstantVal_3111_ = lean_ctor_get(v_defn_3079_, 0);
v_name_3112_ = lean_ctor_get(v_toConstantVal_3111_, 0);
v___x_3113_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__1, &l_Lean_addDecl___lam__4___closed__1_once, _init_l_Lean_addDecl___lam__4___closed__1);
lean_inc(v_name_3112_);
v___x_3114_ = l_Lean_MessageData_ofName(v_name_3112_);
v___x_3115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3113_);
lean_ctor_set(v___x_3115_, 1, v___x_3114_);
v___x_3116_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_3117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3115_);
lean_ctor_set(v___x_3117_, 1, v___x_3116_);
v___x_3118_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3075_, v___x_3117_, v___y_3080_, v___y_3081_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_dec_ref(v___x_3118_);
v___y_3096_ = v___y_3080_;
v___y_3097_ = v___y_3081_;
goto v___jp_3095_;
}
else
{
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec_ref(v_defn_3079_);
lean_dec_ref(v___f_3074_);
return v___x_3118_;
}
}
}
v___jp_3121_:
{
lean_object* v___x_3122_; uint8_t v_isModule_3123_; 
v___x_3122_ = l_Lean_Environment_header(v_env_3119_);
lean_dec_ref(v_env_3119_);
v_isModule_3123_ = lean_ctor_get_uint8(v___x_3122_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3122_);
if (v_isModule_3123_ == 0)
{
lean_dec_ref(v_env_3120_);
lean_dec(v_cls_3075_);
v_exportedInfo_x3f_3084_ = v___x_3076_;
v___y_3085_ = v___y_3080_;
v___y_3086_ = v___y_3081_;
goto v___jp_3083_;
}
else
{
uint8_t v_isExporting_3124_; 
v_isExporting_3124_ = lean_ctor_get_uint8(v_env_3120_, sizeof(void*)*8);
lean_dec_ref(v_env_3120_);
if (v_isExporting_3124_ == 0)
{
lean_dec(v___x_3076_);
goto v___jp_3107_;
}
else
{
if (v___x_3077_ == 0)
{
lean_dec(v_cls_3075_);
v_exportedInfo_x3f_3084_ = v___x_3076_;
v___y_3085_ = v___y_3080_;
v___y_3086_ = v___y_3081_;
goto v___jp_3083_;
}
else
{
lean_dec(v___x_3076_);
goto v___jp_3107_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__4___boxed(lean_object* v___f_3125_, lean_object* v_cls_3126_, lean_object* v___x_3127_, lean_object* v___x_3128_, lean_object* v_forceExpose_3129_, lean_object* v_defn_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
uint8_t v___x_52218__boxed_3134_; uint8_t v_forceExpose_boxed_3135_; lean_object* v_res_3136_; 
v___x_52218__boxed_3134_ = lean_unbox(v___x_3128_);
v_forceExpose_boxed_3135_ = lean_unbox(v_forceExpose_3129_);
v_res_3136_ = l_Lean_addDecl___lam__4(v___f_3125_, v_cls_3126_, v___x_3127_, v___x_52218__boxed_3134_, v_forceExpose_boxed_3135_, v_defn_3130_, v___y_3131_, v___y_3132_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__5(lean_object* v_val_3137_, lean_object* v___f_3138_, lean_object* v_____r_3139_, lean_object* v_exportedInfo_x3f_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_){
_start:
{
lean_object* v_toConstantVal_3144_; lean_object* v_name_3145_; lean_object* v___x_3146_; uint8_t v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v_toConstantVal_3144_ = lean_ctor_get(v_val_3137_, 0);
v_name_3145_ = lean_ctor_get(v_toConstantVal_3144_, 0);
lean_inc(v_name_3145_);
v___x_3146_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3146_, 0, v_val_3137_);
v___x_3147_ = 1;
v___x_3148_ = lean_box(v___x_3147_);
v___x_3149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3146_);
lean_ctor_set(v___x_3149_, 1, v___x_3148_);
v___x_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3150_, 0, v_name_3145_);
lean_ctor_set(v___x_3150_, 1, v___x_3149_);
v___x_3151_ = lean_apply_5(v___f_3138_, v___x_3150_, v_exportedInfo_x3f_3140_, v___y_3141_, v___y_3142_, lean_box(0));
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__5___boxed(lean_object* v_val_3152_, lean_object* v___f_3153_, lean_object* v_____r_3154_, lean_object* v_exportedInfo_x3f_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_){
_start:
{
lean_object* v_res_3159_; 
v_res_3159_ = l_Lean_addDecl___lam__5(v_val_3152_, v___f_3153_, v_____r_3154_, v_exportedInfo_x3f_3155_, v___y_3156_, v___y_3157_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__6(lean_object* v_val_3160_, uint8_t v___x_3161_, lean_object* v___f_3162_, lean_object* v_____r_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
lean_object* v_toConstantVal_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v_toConstantVal_3167_ = lean_ctor_get(v_val_3160_, 0);
lean_inc_ref(v_toConstantVal_3167_);
v___x_3168_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3168_, 0, v_toConstantVal_3167_);
lean_ctor_set_uint8(v___x_3168_, sizeof(void*)*1, v___x_3161_);
v___x_3169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3168_);
v___x_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3169_);
v___x_3171_ = lean_box(0);
v___x_3172_ = lean_apply_5(v___f_3162_, v___x_3171_, v___x_3170_, v___y_3164_, v___y_3165_, lean_box(0));
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__6___boxed(lean_object* v_val_3173_, lean_object* v___x_3174_, lean_object* v___f_3175_, lean_object* v_____r_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
uint8_t v___x_52338__boxed_3180_; lean_object* v_res_3181_; 
v___x_52338__boxed_3180_ = lean_unbox(v___x_3174_);
v_res_3181_ = l_Lean_addDecl___lam__6(v_val_3173_, v___x_52338__boxed_3180_, v___f_3175_, v_____r_3176_, v___y_3177_, v___y_3178_);
lean_dec_ref(v_val_3173_);
return v_res_3181_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__7(lean_object* v_val_3182_, lean_object* v___f_3183_, lean_object* v_____r_3184_, lean_object* v_exportedInfo_x3f_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v_toConstantVal_3189_; lean_object* v_name_3190_; lean_object* v___x_3191_; uint8_t v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v_toConstantVal_3189_ = lean_ctor_get(v_val_3182_, 0);
v_name_3190_ = lean_ctor_get(v_toConstantVal_3189_, 0);
lean_inc(v_name_3190_);
v___x_3191_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3191_, 0, v_val_3182_);
v___x_3192_ = 3;
v___x_3193_ = lean_box(v___x_3192_);
v___x_3194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3191_);
lean_ctor_set(v___x_3194_, 1, v___x_3193_);
v___x_3195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3195_, 0, v_name_3190_);
lean_ctor_set(v___x_3195_, 1, v___x_3194_);
v___x_3196_ = lean_apply_5(v___f_3183_, v___x_3195_, v_exportedInfo_x3f_3185_, v___y_3186_, v___y_3187_, lean_box(0));
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__7___boxed(lean_object* v_val_3197_, lean_object* v___f_3198_, lean_object* v_____r_3199_, lean_object* v_exportedInfo_x3f_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
lean_object* v_res_3204_; 
v_res_3204_ = l_Lean_addDecl___lam__7(v_val_3197_, v___f_3198_, v_____r_3199_, v_exportedInfo_x3f_3200_, v___y_3201_, v___y_3202_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__9(lean_object* v_val_3205_, lean_object* v___f_3206_, lean_object* v_____r_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_){
_start:
{
lean_object* v_toConstantVal_3211_; uint8_t v_isUnsafe_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
v_toConstantVal_3211_ = lean_ctor_get(v_val_3205_, 0);
v_isUnsafe_3212_ = lean_ctor_get_uint8(v_val_3205_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_3211_);
v___x_3213_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3213_, 0, v_toConstantVal_3211_);
lean_ctor_set_uint8(v___x_3213_, sizeof(void*)*1, v_isUnsafe_3212_);
v___x_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
v___x_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3214_);
v___x_3216_ = lean_box(0);
v___x_3217_ = lean_apply_5(v___f_3206_, v___x_3216_, v___x_3215_, v___y_3208_, v___y_3209_, lean_box(0));
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__9___boxed(lean_object* v_val_3218_, lean_object* v___f_3219_, lean_object* v_____r_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_){
_start:
{
lean_object* v_res_3224_; 
v_res_3224_ = l_Lean_addDecl___lam__9(v_val_3218_, v___f_3219_, v_____r_3220_, v___y_3221_, v___y_3222_);
lean_dec_ref(v_val_3218_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__13(lean_object* v_decl_3225_, lean_object* v___x_3226_, uint8_t v___x_3227_, lean_object* v_cls_3228_, lean_object* v___x_3229_, lean_object* v___x_3230_, lean_object* v_____x_3231_, lean_object* v_exportedInfo_x3f_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_){
_start:
{
lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v_a_3239_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v_a_3252_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; uint8_t v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v_snd_3337_; lean_object* v_fst_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3459_; 
v_snd_3337_ = lean_ctor_get(v_____x_3231_, 1);
v_fst_3338_ = lean_ctor_get(v_____x_3231_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v_____x_3231_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3340_ = v_____x_3231_;
v_isShared_3341_ = v_isSharedCheck_3459_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_snd_3337_);
lean_inc(v_fst_3338_);
lean_dec(v_____x_3231_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3459_;
goto v_resetjp_3339_;
}
v___jp_3236_:
{
lean_object* v___x_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
v___x_3240_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3238_, v___y_3237_);
lean_dec(v___y_3237_);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3247_ == 0)
{
lean_object* v_unused_3248_; 
v_unused_3248_ = lean_ctor_get(v___x_3240_, 0);
lean_dec(v_unused_3248_);
v___x_3242_ = v___x_3240_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_dec(v___x_3240_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3243_ == 0)
{
lean_ctor_set_tag(v___x_3242_, 1);
lean_ctor_set(v___x_3242_, 0, v_a_3239_);
v___x_3245_ = v___x_3242_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3239_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
v___jp_3249_:
{
lean_object* v___x_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
v___x_3253_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3251_, v___y_3250_);
lean_dec(v___y_3250_);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3260_ == 0)
{
lean_object* v_unused_3261_; 
v_unused_3261_ = lean_ctor_get(v___x_3253_, 0);
lean_dec(v_unused_3261_);
v___x_3255_ = v___x_3253_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_dec(v___x_3253_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
lean_ctor_set(v___x_3255_, 0, v_a_3252_);
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3252_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
v___jp_3262_:
{
lean_object* v___x_3274_; 
lean_inc_ref(v___y_3270_);
v___x_3274_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3267_, v___y_3270_, v___y_3264_, v___y_3273_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v___x_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3322_; 
lean_dec_ref(v___x_3274_);
lean_inc_ref(v___y_3271_);
v___x_3275_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3271_, v___y_3263_);
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3322_ == 0)
{
lean_object* v_unused_3323_; 
v_unused_3323_ = lean_ctor_get(v___x_3275_, 0);
lean_dec(v_unused_3323_);
v___x_3277_ = v___x_3275_;
v_isShared_3278_ = v_isSharedCheck_3322_;
goto v_resetjp_3276_;
}
else
{
lean_dec(v___x_3275_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3322_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v_options_3279_; lean_object* v___x_3280_; uint8_t v___x_3281_; 
v_options_3279_ = lean_ctor_get(v___y_3268_, 2);
v___x_3280_ = l_Lean_Elab_async;
v___x_3281_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3279_, v___x_3280_);
if (v___x_3281_ == 0)
{
lean_object* v___x_3282_; lean_object* v_r_3283_; 
lean_del_object(v___x_3277_);
lean_dec_ref(v___y_3269_);
lean_dec_ref(v___y_3265_);
lean_dec_ref(v___x_3226_);
v___x_3282_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3270_, v___y_3263_);
lean_dec_ref(v___x_3282_);
lean_inc(v___y_3263_);
v_r_3283_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3225_, v___y_3268_, v___y_3263_);
if (lean_obj_tag(v_r_3283_) == 0)
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3293_; 
v_a_3284_ = lean_ctor_get(v_r_3283_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v_r_3283_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3286_ = v_r_3283_;
v_isShared_3287_ = v_isSharedCheck_3293_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v_r_3283_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3293_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3289_; 
lean_inc(v_a_3284_);
if (v_isShared_3287_ == 0)
{
lean_ctor_set_tag(v___x_3286_, 1);
v___x_3289_ = v___x_3286_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_a_3284_);
v___x_3289_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
lean_object* v___x_3290_; 
v___x_3290_ = lean_apply_2(v___y_3272_, v___x_3289_, lean_box(0));
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_dec_ref(v___x_3290_);
v___y_3250_ = v___y_3263_;
v___y_3251_ = v___y_3271_;
v_a_3252_ = v_a_3284_;
goto v___jp_3249_;
}
else
{
lean_object* v_a_3291_; 
lean_dec(v_a_3284_);
v_a_3291_ = lean_ctor_get(v___x_3290_, 0);
lean_inc(v_a_3291_);
lean_dec_ref(v___x_3290_);
v___y_3237_ = v___y_3263_;
v___y_3238_ = v___y_3271_;
v_a_3239_ = v_a_3291_;
goto v___jp_3236_;
}
}
}
}
else
{
lean_object* v_a_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v_a_3294_ = lean_ctor_get(v_r_3283_, 0);
lean_inc(v_a_3294_);
lean_dec_ref(v_r_3283_);
v___x_3295_ = lean_box(0);
v___x_3296_ = lean_apply_2(v___y_3272_, v___x_3295_, lean_box(0));
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_dec_ref(v___x_3296_);
v___y_3237_ = v___y_3263_;
v___y_3238_ = v___y_3271_;
v_a_3239_ = v_a_3294_;
goto v___jp_3236_;
}
else
{
lean_object* v_a_3297_; 
lean_dec(v_a_3294_);
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_a_3297_);
lean_dec_ref(v___x_3296_);
v___y_3237_ = v___y_3263_;
v___y_3238_ = v___y_3271_;
v_a_3239_ = v_a_3297_;
goto v___jp_3236_;
}
}
}
else
{
lean_object* v___x_3298_; lean_object* v___x_3300_; 
lean_dec_ref(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v_decl_3225_);
v___x_3298_ = l_IO_CancelToken_new();
if (v_isShared_3278_ == 0)
{
lean_ctor_set_tag(v___x_3277_, 1);
lean_ctor_set(v___x_3277_, 0, v___x_3298_);
v___x_3300_ = v___x_3277_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v___x_3298_);
v___x_3300_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3301_ = ((lean_object*)(l_Lean_initFn___closed__5_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_3302_ = l_Lean_Name_mkStr2(v___x_3301_, v___x_3226_);
v___x_3303_ = l_Lean_Name_toString(v___x_3302_, v___x_3227_);
lean_inc_ref(v___x_3300_);
v___x_3304_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3265_, v___x_3300_, v___x_3303_, v___y_3268_, v___y_3263_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v_a_3305_; lean_object* v_checked_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v_a_3305_ = lean_ctor_get(v___x_3304_, 0);
lean_inc(v_a_3305_);
lean_dec_ref(v___x_3304_);
v_checked_3306_ = lean_ctor_get(v___y_3269_, 2);
lean_inc_ref(v_checked_3306_);
lean_dec_ref(v___y_3269_);
v___x_3307_ = lean_unsigned_to_nat(0u);
v___x_3308_ = lean_io_map_task(v_a_3305_, v_checked_3306_, v___x_3307_, v___y_3266_);
v___x_3309_ = lean_box(0);
v___x_3310_ = lean_box(2);
v___x_3311_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3309_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
lean_ctor_set(v___x_3311_, 2, v___x_3300_);
lean_ctor_set(v___x_3311_, 3, v___x_3308_);
v___x_3312_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3311_, v___y_3263_);
lean_dec(v___y_3263_);
return v___x_3312_;
}
else
{
lean_object* v_a_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3320_; 
lean_dec_ref(v___x_3300_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3263_);
v_a_3313_ = lean_ctor_get(v___x_3304_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3315_ = v___x_3304_;
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_a_3313_);
lean_dec(v___x_3304_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3318_; 
if (v_isShared_3316_ == 0)
{
v___x_3318_ = v___x_3315_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v_a_3313_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3336_; 
lean_dec_ref(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec_ref(v___y_3265_);
lean_dec(v___y_3263_);
lean_dec_ref(v___x_3226_);
lean_dec(v_decl_3225_);
v_a_3324_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3326_ = v___x_3274_;
v_isShared_3327_ = v_isSharedCheck_3336_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_dec(v___x_3274_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3336_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v_ref_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3334_; 
v_ref_3328_ = lean_ctor_get(v___y_3268_, 5);
lean_inc(v_ref_3328_);
lean_dec_ref(v___y_3268_);
v___x_3329_ = lean_io_error_to_string(v_a_3324_);
v___x_3330_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3329_);
v___x_3331_ = l_Lean_MessageData_ofFormat(v___x_3330_);
v___x_3332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3332_, 0, v_ref_3328_);
lean_ctor_set(v___x_3332_, 1, v___x_3331_);
if (v_isShared_3327_ == 0)
{
lean_ctor_set(v___x_3326_, 0, v___x_3332_);
v___x_3334_ = v___x_3326_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v___x_3332_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
}
v_resetjp_3339_:
{
lean_object* v_fst_3342_; lean_object* v_snd_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3458_; 
v_fst_3342_ = lean_ctor_get(v_snd_3337_, 0);
v_snd_3343_ = lean_ctor_get(v_snd_3337_, 1);
v_isSharedCheck_3458_ = !lean_is_exclusive(v_snd_3337_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3345_ = v_snd_3337_;
v_isShared_3346_ = v_isSharedCheck_3458_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_snd_3343_);
lean_inc(v_fst_3342_);
lean_dec(v_snd_3337_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3458_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v_exportedInfo_x3f_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3400_; lean_object* v___y_3401_; uint8_t v___y_3402_; lean_object* v___y_3429_; lean_object* v___y_3430_; lean_object* v___x_3448_; lean_object* v_env_3449_; uint8_t v___x_3450_; 
v___x_3448_ = lean_st_ref_get(v___y_3234_);
v_env_3449_ = lean_ctor_get(v___x_3448_, 0);
lean_inc_ref(v_env_3449_);
lean_dec(v___x_3448_);
v___x_3450_ = l_Lean_Environment_containsOnBranch(v_env_3449_, v_fst_3338_);
if (v___x_3450_ == 0)
{
lean_del_object(v___x_3340_);
v___y_3429_ = v___y_3233_;
v___y_3430_ = v___y_3234_;
goto v___jp_3428_;
}
else
{
lean_object* v___x_3451_; lean_object* v_env_3452_; lean_object* v___x_3453_; lean_object* v___x_3455_; 
lean_del_object(v___x_3345_);
lean_dec(v_snd_3343_);
lean_dec(v_fst_3342_);
lean_dec(v_exportedInfo_x3f_3232_);
lean_dec(v___x_3230_);
lean_dec_ref(v___x_3229_);
lean_dec(v_cls_3228_);
lean_dec_ref(v___x_3226_);
lean_dec(v_decl_3225_);
v___x_3451_ = lean_st_ref_get(v___y_3234_);
v_env_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc_ref(v_env_3452_);
lean_dec(v___x_3451_);
v___x_3453_ = lean_elab_environment_to_kernel_env(v_env_3452_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set_tag(v___x_3340_, 1);
lean_ctor_set(v___x_3340_, 1, v_fst_3338_);
lean_ctor_set(v___x_3340_, 0, v___x_3453_);
v___x_3455_ = v___x_3340_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v___x_3453_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v_fst_3338_);
v___x_3455_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
lean_object* v___x_3456_; 
v___x_3456_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(v___x_3455_, v___y_3233_, v___y_3234_);
lean_dec(v___y_3234_);
return v___x_3456_;
}
}
v___jp_3347_:
{
uint8_t v___x_3355_; uint8_t v___x_3356_; lean_object* v___x_3357_; 
v___x_3355_ = 0;
v___x_3356_ = lean_unbox(v_snd_3343_);
lean_dec(v_snd_3343_);
lean_inc_ref(v___y_3350_);
v___x_3357_ = l_Lean_Environment_addConstAsync(v___y_3350_, v_fst_3338_, v___x_3356_, v___y_3354_, v___x_3355_, v___x_3227_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_a_3358_; lean_object* v_mainEnv_3359_; lean_object* v_asyncEnv_3360_; lean_object* v___f_3361_; lean_object* v___f_3362_; lean_object* v___x_3363_; 
lean_del_object(v___x_3345_);
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_a_3358_);
lean_dec_ref(v___x_3357_);
v_mainEnv_3359_ = lean_ctor_get(v_a_3358_, 0);
lean_inc_ref(v_mainEnv_3359_);
v_asyncEnv_3360_ = lean_ctor_get(v_a_3358_, 1);
lean_inc_ref(v_asyncEnv_3360_);
lean_inc(v_a_3358_);
v___f_3361_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3361_, 0, v___y_3348_);
lean_closure_set(v___f_3361_, 1, v_a_3358_);
lean_closure_set(v___f_3361_, 2, v___y_3349_);
lean_inc(v_decl_3225_);
lean_inc(v_a_3358_);
lean_inc_ref(v_asyncEnv_3360_);
v___f_3362_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3362_, 0, v_asyncEnv_3360_);
lean_closure_set(v___f_3362_, 1, v_a_3358_);
lean_closure_set(v___f_3362_, 2, v_decl_3225_);
v___x_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3363_, 0, v_fst_3342_);
if (lean_obj_tag(v___y_3353_) == 0)
{
lean_inc_ref(v___x_3363_);
v___y_3263_ = v___y_3351_;
v___y_3264_ = v___x_3363_;
v___y_3265_ = v___f_3362_;
v___y_3266_ = v___x_3355_;
v___y_3267_ = v_a_3358_;
v___y_3268_ = v___y_3352_;
v___y_3269_ = v___y_3350_;
v___y_3270_ = v_asyncEnv_3360_;
v___y_3271_ = v_mainEnv_3359_;
v___y_3272_ = v___f_3361_;
v___y_3273_ = v___x_3363_;
goto v___jp_3262_;
}
else
{
v___y_3263_ = v___y_3351_;
v___y_3264_ = v___x_3363_;
v___y_3265_ = v___f_3362_;
v___y_3266_ = v___x_3355_;
v___y_3267_ = v_a_3358_;
v___y_3268_ = v___y_3352_;
v___y_3269_ = v___y_3350_;
v___y_3270_ = v_asyncEnv_3360_;
v___y_3271_ = v_mainEnv_3359_;
v___y_3272_ = v___f_3361_;
v___y_3273_ = v___y_3353_;
goto v___jp_3262_;
}
}
else
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3378_; 
lean_dec(v___y_3353_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
lean_dec_ref(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec(v_fst_3342_);
lean_dec_ref(v___x_3226_);
lean_dec(v_decl_3225_);
v_a_3364_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3366_ = v___x_3357_;
v_isShared_3367_ = v_isSharedCheck_3378_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___x_3357_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3378_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v_ref_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3373_; 
v_ref_3368_ = lean_ctor_get(v___y_3352_, 5);
lean_inc(v_ref_3368_);
lean_dec_ref(v___y_3352_);
v___x_3369_ = lean_io_error_to_string(v_a_3364_);
v___x_3370_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3369_);
v___x_3371_ = l_Lean_MessageData_ofFormat(v___x_3370_);
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 1, v___x_3371_);
lean_ctor_set(v___x_3345_, 0, v_ref_3368_);
v___x_3373_ = v___x_3345_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_ref_3368_);
lean_ctor_set(v_reuseFailAlloc_3377_, 1, v___x_3371_);
v___x_3373_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
lean_object* v___x_3375_; 
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 0, v___x_3373_);
v___x_3375_ = v___x_3366_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3373_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
}
}
v___jp_3379_:
{
lean_object* v___x_3383_; 
v___x_3383_ = lean_st_ref_get(v___y_3382_);
if (lean_obj_tag(v_exportedInfo_x3f_3380_) == 0)
{
lean_object* v_env_3384_; lean_object* v___x_3385_; 
v_env_3384_ = lean_ctor_get(v___x_3383_, 0);
lean_inc_ref(v_env_3384_);
lean_dec(v___x_3383_);
v___x_3385_ = lean_box(0);
lean_inc_ref(v___y_3381_);
lean_inc(v___y_3382_);
v___y_3348_ = v___y_3382_;
v___y_3349_ = v___y_3381_;
v___y_3350_ = v_env_3384_;
v___y_3351_ = v___y_3382_;
v___y_3352_ = v___y_3381_;
v___y_3353_ = v_exportedInfo_x3f_3380_;
v___y_3354_ = v___x_3385_;
goto v___jp_3347_;
}
else
{
lean_object* v_env_3386_; lean_object* v_val_3387_; uint8_t v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v_env_3386_ = lean_ctor_get(v___x_3383_, 0);
lean_inc_ref(v_env_3386_);
lean_dec(v___x_3383_);
v_val_3387_ = lean_ctor_get(v_exportedInfo_x3f_3380_, 0);
v___x_3388_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3387_);
v___x_3389_ = lean_box(v___x_3388_);
v___x_3390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3389_);
lean_inc_ref(v___y_3381_);
lean_inc(v___y_3382_);
v___y_3348_ = v___y_3382_;
v___y_3349_ = v___y_3381_;
v___y_3350_ = v_env_3386_;
v___y_3351_ = v___y_3382_;
v___y_3352_ = v___y_3381_;
v___y_3353_ = v_exportedInfo_x3f_3380_;
v___y_3354_ = v___x_3390_;
goto v___jp_3347_;
}
}
v___jp_3391_:
{
lean_object* v___x_3394_; 
lean_inc(v_fst_3342_);
v___x_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3394_, 0, v_fst_3342_);
v_exportedInfo_x3f_3380_ = v___x_3394_;
v___y_3381_ = v___y_3392_;
v___y_3382_ = v___y_3393_;
goto v___jp_3379_;
}
v___jp_3395_:
{
lean_object* v___x_3398_; 
lean_inc(v_fst_3342_);
v___x_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3398_, 0, v_fst_3342_);
v_exportedInfo_x3f_3380_ = v___x_3398_;
v___y_3381_ = v___y_3396_;
v___y_3382_ = v___y_3397_;
goto v___jp_3379_;
}
v___jp_3399_:
{
if (v___y_3402_ == 0)
{
lean_object* v___x_3403_; lean_object* v_a_3404_; uint8_t v___x_3405_; 
lean_dec(v_exportedInfo_x3f_3232_);
lean_dec_ref(v___x_3229_);
lean_inc(v_cls_3228_);
v___x_3403_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_3228_, v___y_3400_);
v_a_3404_ = lean_ctor_get(v___x_3403_, 0);
lean_inc(v_a_3404_);
lean_dec_ref(v___x_3403_);
v___x_3405_ = lean_unbox(v_a_3404_);
lean_dec(v_a_3404_);
if (v___x_3405_ == 0)
{
lean_dec(v_cls_3228_);
v___y_3392_ = v___y_3400_;
v___y_3393_ = v___y_3401_;
goto v___jp_3391_;
}
else
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3406_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__2, &l_Lean_addDecl___lam__8___closed__2_once, _init_l_Lean_addDecl___lam__8___closed__2);
v___x_3407_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3228_, v___x_3406_, v___y_3400_, v___y_3401_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_dec_ref(v___x_3407_);
v___y_3392_ = v___y_3400_;
v___y_3393_ = v___y_3401_;
goto v___jp_3391_;
}
else
{
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_del_object(v___x_3345_);
lean_dec(v_snd_3343_);
lean_dec(v_fst_3342_);
lean_dec(v_fst_3338_);
lean_dec_ref(v___x_3226_);
lean_dec(v_decl_3225_);
return v___x_3407_;
}
}
}
else
{
lean_object* v___x_3408_; lean_object* v_env_3409_; lean_object* v_nextMacroScope_3410_; lean_object* v_ngen_3411_; lean_object* v_auxDeclNGen_3412_; lean_object* v_traceState_3413_; lean_object* v_messages_3414_; lean_object* v_infoState_3415_; lean_object* v_snapshotTasks_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3426_; 
lean_dec(v_cls_3228_);
v___x_3408_ = lean_st_ref_take(v___y_3401_);
v_env_3409_ = lean_ctor_get(v___x_3408_, 0);
v_nextMacroScope_3410_ = lean_ctor_get(v___x_3408_, 1);
v_ngen_3411_ = lean_ctor_get(v___x_3408_, 2);
v_auxDeclNGen_3412_ = lean_ctor_get(v___x_3408_, 3);
v_traceState_3413_ = lean_ctor_get(v___x_3408_, 4);
v_messages_3414_ = lean_ctor_get(v___x_3408_, 6);
v_infoState_3415_ = lean_ctor_get(v___x_3408_, 7);
v_snapshotTasks_3416_ = lean_ctor_get(v___x_3408_, 8);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3426_ == 0)
{
lean_object* v_unused_3427_; 
v_unused_3427_ = lean_ctor_get(v___x_3408_, 5);
lean_dec(v_unused_3427_);
v___x_3418_ = v___x_3408_;
v_isShared_3419_ = v_isSharedCheck_3426_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_snapshotTasks_3416_);
lean_inc(v_infoState_3415_);
lean_inc(v_messages_3414_);
lean_inc(v_traceState_3413_);
lean_inc(v_auxDeclNGen_3412_);
lean_inc(v_ngen_3411_);
lean_inc(v_nextMacroScope_3410_);
lean_inc(v_env_3409_);
lean_dec(v___x_3408_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3426_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3423_; 
v___x_3420_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3343_);
lean_inc(v_fst_3338_);
v___x_3421_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3420_, v_env_3409_, v_fst_3338_, v_snd_3343_);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 5, v___x_3229_);
lean_ctor_set(v___x_3418_, 0, v___x_3421_);
v___x_3423_ = v___x_3418_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v___x_3421_);
lean_ctor_set(v_reuseFailAlloc_3425_, 1, v_nextMacroScope_3410_);
lean_ctor_set(v_reuseFailAlloc_3425_, 2, v_ngen_3411_);
lean_ctor_set(v_reuseFailAlloc_3425_, 3, v_auxDeclNGen_3412_);
lean_ctor_set(v_reuseFailAlloc_3425_, 4, v_traceState_3413_);
lean_ctor_set(v_reuseFailAlloc_3425_, 5, v___x_3229_);
lean_ctor_set(v_reuseFailAlloc_3425_, 6, v_messages_3414_);
lean_ctor_set(v_reuseFailAlloc_3425_, 7, v_infoState_3415_);
lean_ctor_set(v_reuseFailAlloc_3425_, 8, v_snapshotTasks_3416_);
v___x_3423_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
lean_object* v___x_3424_; 
v___x_3424_ = lean_st_ref_set(v___y_3401_, v___x_3423_);
v_exportedInfo_x3f_3380_ = v_exportedInfo_x3f_3232_;
v___y_3381_ = v___y_3400_;
v___y_3382_ = v___y_3401_;
goto v___jp_3379_;
}
}
}
}
v___jp_3428_:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; uint8_t v___x_3433_; 
lean_inc(v_decl_3225_);
v___x_3431_ = l_Lean_Declaration_getTopLevelNames(v_decl_3225_);
v___x_3432_ = ((lean_object*)(l_Lean_addDecl___lam__8___closed__0));
v___x_3433_ = l_List_all___redArg(v___x_3431_, v___x_3432_);
if (v___x_3433_ == 0)
{
lean_dec(v___x_3230_);
if (lean_obj_tag(v_exportedInfo_x3f_3232_) == 0)
{
v___y_3400_ = v___y_3429_;
v___y_3401_ = v___y_3430_;
v___y_3402_ = v___x_3433_;
goto v___jp_3399_;
}
else
{
v___y_3400_ = v___y_3429_;
v___y_3401_ = v___y_3430_;
v___y_3402_ = v___x_3227_;
goto v___jp_3399_;
}
}
else
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v_a_3436_; uint8_t v___x_3437_; 
lean_dec(v_exportedInfo_x3f_3232_);
lean_dec_ref(v___x_3229_);
v___x_3434_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3435_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__2___redArg(v___x_3434_, v___y_3429_);
v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
lean_inc(v_a_3436_);
lean_dec_ref(v___x_3435_);
v___x_3437_ = lean_unbox(v_a_3436_);
lean_dec(v_a_3436_);
if (v___x_3437_ == 0)
{
lean_object* v___x_3438_; lean_object* v_a_3439_; uint8_t v___x_3440_; 
lean_inc(v_cls_3228_);
v___x_3438_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_3228_, v___y_3429_);
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
lean_inc(v_a_3439_);
lean_dec_ref(v___x_3438_);
v___x_3440_ = lean_unbox(v_a_3439_);
lean_dec(v_a_3439_);
if (v___x_3440_ == 0)
{
lean_dec(v_cls_3228_);
v_exportedInfo_x3f_3380_ = v___x_3230_;
v___y_3381_ = v___y_3429_;
v___y_3382_ = v___y_3430_;
goto v___jp_3379_;
}
else
{
lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3441_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__4, &l_Lean_addDecl___lam__8___closed__4_once, _init_l_Lean_addDecl___lam__8___closed__4);
v___x_3442_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3228_, v___x_3441_, v___y_3429_, v___y_3430_);
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_dec_ref(v___x_3442_);
v_exportedInfo_x3f_3380_ = v___x_3230_;
v___y_3381_ = v___y_3429_;
v___y_3382_ = v___y_3430_;
goto v___jp_3379_;
}
else
{
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_del_object(v___x_3345_);
lean_dec(v_snd_3343_);
lean_dec(v_fst_3342_);
lean_dec(v_fst_3338_);
lean_dec(v___x_3230_);
lean_dec_ref(v___x_3226_);
lean_dec(v_decl_3225_);
return v___x_3442_;
}
}
}
else
{
lean_object* v___x_3443_; lean_object* v_a_3444_; uint8_t v___x_3445_; 
lean_dec(v___x_3230_);
lean_inc(v_cls_3228_);
v___x_3443_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_3228_, v___y_3429_);
v_a_3444_ = lean_ctor_get(v___x_3443_, 0);
lean_inc(v_a_3444_);
lean_dec_ref(v___x_3443_);
v___x_3445_ = lean_unbox(v_a_3444_);
lean_dec(v_a_3444_);
if (v___x_3445_ == 0)
{
lean_dec(v_cls_3228_);
v___y_3396_ = v___y_3429_;
v___y_3397_ = v___y_3430_;
goto v___jp_3395_;
}
else
{
lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3446_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__6, &l_Lean_addDecl___lam__8___closed__6_once, _init_l_Lean_addDecl___lam__8___closed__6);
v___x_3447_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3228_, v___x_3446_, v___y_3429_, v___y_3430_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_dec_ref(v___x_3447_);
v___y_3396_ = v___y_3429_;
v___y_3397_ = v___y_3430_;
goto v___jp_3395_;
}
else
{
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_del_object(v___x_3345_);
lean_dec(v_snd_3343_);
lean_dec(v_fst_3342_);
lean_dec(v_fst_3338_);
lean_dec_ref(v___x_3226_);
lean_dec(v_decl_3225_);
return v___x_3447_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__13___boxed(lean_object* v_decl_3460_, lean_object* v___x_3461_, lean_object* v___x_3462_, lean_object* v_cls_3463_, lean_object* v___x_3464_, lean_object* v___x_3465_, lean_object* v_____x_3466_, lean_object* v_exportedInfo_x3f_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
uint8_t v___x_52441__boxed_3471_; lean_object* v_res_3472_; 
v___x_52441__boxed_3471_ = lean_unbox(v___x_3462_);
v_res_3472_ = l_Lean_addDecl___lam__13(v_decl_3460_, v___x_3461_, v___x_52441__boxed_3471_, v_cls_3463_, v___x_3464_, v___x_3465_, v_____x_3466_, v_exportedInfo_x3f_3467_, v___y_3468_, v___y_3469_);
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__10(lean_object* v___f_3473_, uint8_t v_forceExpose_3474_, uint8_t v___x_3475_, lean_object* v___x_3476_, lean_object* v_cls_3477_, lean_object* v_defn_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_){
_start:
{
lean_object* v_exportedInfo_x3f_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3504_ = lean_st_ref_get(v___y_3480_);
v___x_3505_ = lean_st_ref_get(v___y_3480_);
if (v_forceExpose_3474_ == 0)
{
if (v___x_3475_ == 0)
{
lean_dec(v___x_3505_);
lean_dec(v___x_3504_);
lean_dec(v_cls_3477_);
v_exportedInfo_x3f_3483_ = v___x_3476_;
v___y_3484_ = v___y_3479_;
v___y_3485_ = v___y_3480_;
goto v___jp_3482_;
}
else
{
lean_object* v_env_3506_; lean_object* v_env_3507_; lean_object* v___x_3508_; uint8_t v_isModule_3509_; 
v_env_3506_ = lean_ctor_get(v___x_3504_, 0);
lean_inc_ref(v_env_3506_);
lean_dec(v___x_3504_);
v_env_3507_ = lean_ctor_get(v___x_3505_, 0);
lean_inc_ref(v_env_3507_);
lean_dec(v___x_3505_);
v___x_3508_ = l_Lean_Environment_header(v_env_3506_);
lean_dec_ref(v_env_3506_);
v_isModule_3509_ = lean_ctor_get_uint8(v___x_3508_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3508_);
if (v_isModule_3509_ == 0)
{
lean_dec_ref(v_env_3507_);
lean_dec(v_cls_3477_);
v_exportedInfo_x3f_3483_ = v___x_3476_;
v___y_3484_ = v___y_3479_;
v___y_3485_ = v___y_3480_;
goto v___jp_3482_;
}
else
{
uint8_t v_isExporting_3510_; 
v_isExporting_3510_ = lean_ctor_get_uint8(v_env_3507_, sizeof(void*)*8);
lean_dec_ref(v_env_3507_);
if (v_isExporting_3510_ == 0)
{
lean_object* v___x_3511_; lean_object* v_a_3512_; uint8_t v___x_3513_; 
lean_dec(v___x_3476_);
lean_inc(v_cls_3477_);
v___x_3511_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_3477_, v___y_3479_);
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_a_3512_);
lean_dec_ref(v___x_3511_);
v___x_3513_ = lean_unbox(v_a_3512_);
lean_dec(v_a_3512_);
if (v___x_3513_ == 0)
{
lean_dec(v_cls_3477_);
v___y_3495_ = v___y_3479_;
v___y_3496_ = v___y_3480_;
goto v___jp_3494_;
}
else
{
lean_object* v_toConstantVal_3514_; lean_object* v_name_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v_toConstantVal_3514_ = lean_ctor_get(v_defn_3478_, 0);
v_name_3515_ = lean_ctor_get(v_toConstantVal_3514_, 0);
v___x_3516_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__1, &l_Lean_addDecl___lam__4___closed__1_once, _init_l_Lean_addDecl___lam__4___closed__1);
lean_inc(v_name_3515_);
v___x_3517_ = l_Lean_MessageData_ofName(v_name_3515_);
v___x_3518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3516_);
lean_ctor_set(v___x_3518_, 1, v___x_3517_);
v___x_3519_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_3520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3518_);
lean_ctor_set(v___x_3520_, 1, v___x_3519_);
v___x_3521_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3477_, v___x_3520_, v___y_3479_, v___y_3480_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_dec_ref(v___x_3521_);
v___y_3495_ = v___y_3479_;
v___y_3496_ = v___y_3480_;
goto v___jp_3494_;
}
else
{
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
lean_dec_ref(v_defn_3478_);
lean_dec_ref(v___f_3473_);
return v___x_3521_;
}
}
}
else
{
lean_dec(v_cls_3477_);
v_exportedInfo_x3f_3483_ = v___x_3476_;
v___y_3484_ = v___y_3479_;
v___y_3485_ = v___y_3480_;
goto v___jp_3482_;
}
}
}
}
else
{
lean_dec(v___x_3505_);
lean_dec(v___x_3504_);
lean_dec(v_cls_3477_);
v_exportedInfo_x3f_3483_ = v___x_3476_;
v___y_3484_ = v___y_3479_;
v___y_3485_ = v___y_3480_;
goto v___jp_3482_;
}
v___jp_3482_:
{
lean_object* v_toConstantVal_3486_; lean_object* v_name_3487_; lean_object* v___x_3488_; uint8_t v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
v_toConstantVal_3486_ = lean_ctor_get(v_defn_3478_, 0);
v_name_3487_ = lean_ctor_get(v_toConstantVal_3486_, 0);
lean_inc(v_name_3487_);
v___x_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3488_, 0, v_defn_3478_);
v___x_3489_ = 0;
v___x_3490_ = lean_box(v___x_3489_);
v___x_3491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3488_);
lean_ctor_set(v___x_3491_, 1, v___x_3490_);
v___x_3492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3492_, 0, v_name_3487_);
lean_ctor_set(v___x_3492_, 1, v___x_3491_);
v___x_3493_ = lean_apply_5(v___f_3473_, v___x_3492_, v_exportedInfo_x3f_3483_, v___y_3484_, v___y_3485_, lean_box(0));
return v___x_3493_;
}
v___jp_3494_:
{
lean_object* v_toConstantVal_3497_; uint8_t v_safety_3498_; uint8_t v___x_3499_; uint8_t v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v_toConstantVal_3497_ = lean_ctor_get(v_defn_3478_, 0);
v_safety_3498_ = lean_ctor_get_uint8(v_defn_3478_, sizeof(void*)*4);
v___x_3499_ = 0;
v___x_3500_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3498_, v___x_3499_);
lean_inc_ref(v_toConstantVal_3497_);
v___x_3501_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3501_, 0, v_toConstantVal_3497_);
lean_ctor_set_uint8(v___x_3501_, sizeof(void*)*1, v___x_3500_);
v___x_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
v___x_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3502_);
v_exportedInfo_x3f_3483_ = v___x_3503_;
v___y_3484_ = v___y_3495_;
v___y_3485_ = v___y_3496_;
goto v___jp_3482_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__10___boxed(lean_object* v___f_3522_, lean_object* v_forceExpose_3523_, lean_object* v___x_3524_, lean_object* v___x_3525_, lean_object* v_cls_3526_, lean_object* v_defn_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_){
_start:
{
uint8_t v_forceExpose_boxed_3531_; uint8_t v___x_52909__boxed_3532_; lean_object* v_res_3533_; 
v_forceExpose_boxed_3531_ = lean_unbox(v_forceExpose_3523_);
v___x_52909__boxed_3532_ = lean_unbox(v___x_3524_);
v_res_3533_ = l_Lean_addDecl___lam__10(v___f_3522_, v_forceExpose_boxed_3531_, v___x_52909__boxed_3532_, v___x_3525_, v_cls_3526_, v_defn_3527_, v___y_3528_, v___y_3529_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__12(lean_object* v_val_3534_, uint8_t v_forceExpose_3535_, lean_object* v___f_3536_, lean_object* v_____r_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
lean_object* v_toConstantVal_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
v_toConstantVal_3541_ = lean_ctor_get(v_val_3534_, 0);
lean_inc_ref(v_toConstantVal_3541_);
v___x_3542_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3542_, 0, v_toConstantVal_3541_);
lean_ctor_set_uint8(v___x_3542_, sizeof(void*)*1, v_forceExpose_3535_);
v___x_3543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3542_);
v___x_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3543_);
v___x_3545_ = lean_box(0);
v___x_3546_ = lean_apply_5(v___f_3536_, v___x_3545_, v___x_3544_, v___y_3538_, v___y_3539_, lean_box(0));
return v___x_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__12___boxed(lean_object* v_val_3547_, lean_object* v_forceExpose_3548_, lean_object* v___f_3549_, lean_object* v_____r_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
uint8_t v_forceExpose_boxed_3554_; lean_object* v_res_3555_; 
v_forceExpose_boxed_3554_ = lean_unbox(v_forceExpose_3548_);
v_res_3555_ = l_Lean_addDecl___lam__12(v_val_3547_, v_forceExpose_boxed_3554_, v___f_3549_, v_____r_3550_, v___y_3551_, v___y_3552_);
lean_dec_ref(v_val_3547_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_addDecl_spec__1(lean_object* v_x_3556_, lean_object* v_x_3557_){
_start:
{
if (lean_obj_tag(v_x_3557_) == 0)
{
return v_x_3556_;
}
else
{
lean_object* v_head_3558_; lean_object* v_tail_3559_; lean_object* v___x_3560_; 
v_head_3558_ = lean_ctor_get(v_x_3557_, 0);
lean_inc(v_head_3558_);
v_tail_3559_ = lean_ctor_get(v_x_3557_, 1);
lean_inc(v_tail_3559_);
lean_dec_ref(v_x_3557_);
v___x_3560_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(v_x_3556_, v_head_3558_);
v_x_3556_ = v___x_3560_;
v_x_3557_ = v_tail_3559_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_addDecl___closed__2(void){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3566_ = ((lean_object*)(l_Lean_addDecl___closed__1));
v___x_3567_ = l_Lean_stringToMessageData(v___x_3566_);
return v___x_3567_;
}
}
static lean_object* _init_l_Lean_addDecl___closed__4(void){
_start:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3569_ = ((lean_object*)(l_Lean_addDecl___closed__3));
v___x_3570_ = l_Lean_stringToMessageData(v___x_3569_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object* v_decl_3571_, uint8_t v_forceExpose_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_){
_start:
{
lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v_a_3579_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v_a_3592_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v_a_3605_; lean_object* v___y_3616_; lean_object* v___y_3617_; lean_object* v_a_3618_; lean_object* v_options_3628_; uint8_t v_hasTrace_3629_; lean_object* v___x_3630_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; uint8_t v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3709_; uint8_t v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3738_; uint8_t v___y_3739_; lean_object* v___y_3740_; lean_object* v_exportedInfo_x3f_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3753_; uint8_t v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3760_; uint8_t v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v_cls_3766_; 
v_options_3628_ = lean_ctor_get(v_a_3573_, 2);
lean_inc_ref(v_options_3628_);
v_hasTrace_3629_ = lean_ctor_get_uint8(v_options_3628_, sizeof(void*)*1);
v___x_3630_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__0_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v_cls_3766_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
if (v_hasTrace_3629_ == 0)
{
lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3995_; 
v_isSharedCheck_3995_ = !lean_is_exclusive(v_options_3628_);
if (v_isSharedCheck_3995_ == 0)
{
lean_object* v_unused_3996_; 
v_unused_3996_ = lean_ctor_get(v_options_3628_, 0);
lean_dec(v_unused_3996_);
v___x_3768_ = v_options_3628_;
v_isShared_3769_ = v_isSharedCheck_3995_;
goto v_resetjp_3767_;
}
else
{
lean_dec(v_options_3628_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3995_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3770_; lean_object* v_env_3771_; lean_object* v_nextMacroScope_3772_; lean_object* v_ngen_3773_; lean_object* v_auxDeclNGen_3774_; lean_object* v_traceState_3775_; lean_object* v_messages_3776_; lean_object* v_infoState_3777_; lean_object* v_snapshotTasks_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3993_; 
v___x_3770_ = lean_st_ref_take(v_a_3574_);
v_env_3771_ = lean_ctor_get(v___x_3770_, 0);
v_nextMacroScope_3772_ = lean_ctor_get(v___x_3770_, 1);
v_ngen_3773_ = lean_ctor_get(v___x_3770_, 2);
v_auxDeclNGen_3774_ = lean_ctor_get(v___x_3770_, 3);
v_traceState_3775_ = lean_ctor_get(v___x_3770_, 4);
v_messages_3776_ = lean_ctor_get(v___x_3770_, 6);
v_infoState_3777_ = lean_ctor_get(v___x_3770_, 7);
v_snapshotTasks_3778_ = lean_ctor_get(v___x_3770_, 8);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___x_3770_);
if (v_isSharedCheck_3993_ == 0)
{
lean_object* v_unused_3994_; 
v_unused_3994_ = lean_ctor_get(v___x_3770_, 5);
lean_dec(v_unused_3994_);
v___x_3780_ = v___x_3770_;
v_isShared_3781_ = v_isSharedCheck_3993_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_snapshotTasks_3778_);
lean_inc(v_infoState_3777_);
lean_inc(v_messages_3776_);
lean_inc(v_traceState_3775_);
lean_inc(v_auxDeclNGen_3774_);
lean_inc(v_ngen_3773_);
lean_inc(v_nextMacroScope_3772_);
lean_inc(v_env_3771_);
lean_dec(v___x_3770_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3993_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3786_; 
lean_inc(v_decl_3571_);
v___x_3782_ = l_Lean_Declaration_getNames(v_decl_3571_);
v___x_3783_ = l_List_foldl___at___00Lean_addDecl_spec__1(v_env_3771_, v___x_3782_);
v___x_3784_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2);
if (v_isShared_3781_ == 0)
{
lean_ctor_set(v___x_3780_, 5, v___x_3784_);
lean_ctor_set(v___x_3780_, 0, v___x_3783_);
v___x_3786_ = v___x_3780_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v___x_3783_);
lean_ctor_set(v_reuseFailAlloc_3992_, 1, v_nextMacroScope_3772_);
lean_ctor_set(v_reuseFailAlloc_3992_, 2, v_ngen_3773_);
lean_ctor_set(v_reuseFailAlloc_3992_, 3, v_auxDeclNGen_3774_);
lean_ctor_set(v_reuseFailAlloc_3992_, 4, v_traceState_3775_);
lean_ctor_set(v_reuseFailAlloc_3992_, 5, v___x_3784_);
lean_ctor_set(v_reuseFailAlloc_3992_, 6, v_messages_3776_);
lean_ctor_set(v_reuseFailAlloc_3992_, 7, v_infoState_3777_);
lean_ctor_set(v_reuseFailAlloc_3992_, 8, v_snapshotTasks_3778_);
v___x_3786_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
lean_object* v___x_3787_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___x_3798_; lean_object* v___y_3800_; uint8_t v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v_fst_3850_; lean_object* v_fst_3851_; uint8_t v_snd_3852_; lean_object* v_exportedInfo_x3f_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3865_; lean_object* v_toConstantVal_3866_; lean_object* v_exportedInfo_x3f_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___y_3874_; lean_object* v_exportedInfo_x3f_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3880_; lean_object* v_toConstantVal_3881_; uint8_t v_safety_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v_defn_3893_; lean_object* v___y_3894_; lean_object* v___y_3895_; 
v___x_3787_ = lean_st_ref_set(v_a_3574_, v___x_3786_);
v___x_3798_ = lean_box(0);
switch(lean_obj_tag(v_decl_3571_))
{
case 2:
{
lean_object* v_val_3917_; lean_object* v_exportedInfo_x3f_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3927_; lean_object* v___y_3928_; lean_object* v___x_3933_; 
lean_del_object(v___x_3768_);
v_val_3917_ = lean_ctor_get(v_decl_3571_, 0);
v___x_3933_ = lean_st_ref_get(v_a_3574_);
if (v_forceExpose_3572_ == 0)
{
lean_object* v_env_3934_; lean_object* v___x_3935_; uint8_t v_isModule_3936_; 
v_env_3934_ = lean_ctor_get(v___x_3933_, 0);
lean_inc_ref(v_env_3934_);
lean_dec(v___x_3933_);
v___x_3935_ = l_Lean_Environment_header(v_env_3934_);
lean_dec_ref(v_env_3934_);
v_isModule_3936_ = lean_ctor_get_uint8(v___x_3935_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3935_);
if (v_isModule_3936_ == 0)
{
v_exportedInfo_x3f_3919_ = v___x_3798_;
v___y_3920_ = v_a_3573_;
v___y_3921_ = v_a_3574_;
goto v___jp_3918_;
}
else
{
lean_object* v___x_3937_; lean_object* v_a_3938_; uint8_t v___x_3939_; 
v___x_3937_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_3766_, v_a_3573_);
v_a_3938_ = lean_ctor_get(v___x_3937_, 0);
lean_inc(v_a_3938_);
lean_dec_ref(v___x_3937_);
v___x_3939_ = lean_unbox(v_a_3938_);
lean_dec(v_a_3938_);
if (v___x_3939_ == 0)
{
v___y_3927_ = v_a_3573_;
v___y_3928_ = v_a_3574_;
goto v___jp_3926_;
}
else
{
lean_object* v_toConstantVal_3940_; lean_object* v_name_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
v_toConstantVal_3940_ = lean_ctor_get(v_val_3917_, 0);
v_name_3941_ = lean_ctor_get(v_toConstantVal_3940_, 0);
v___x_3942_ = lean_obj_once(&l_Lean_addDecl___closed__2, &l_Lean_addDecl___closed__2_once, _init_l_Lean_addDecl___closed__2);
lean_inc(v_name_3941_);
v___x_3943_ = l_Lean_MessageData_ofName(v_name_3941_);
v___x_3944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3942_);
lean_ctor_set(v___x_3944_, 1, v___x_3943_);
v___x_3945_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_3946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3944_);
lean_ctor_set(v___x_3946_, 1, v___x_3945_);
v___x_3947_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3766_, v___x_3946_, v_a_3573_, v_a_3574_);
if (lean_obj_tag(v___x_3947_) == 0)
{
lean_dec_ref(v___x_3947_);
v___y_3927_ = v_a_3573_;
v___y_3928_ = v_a_3574_;
goto v___jp_3926_;
}
else
{
lean_dec_ref(v_decl_3571_);
lean_dec(v_a_3574_);
lean_dec_ref(v_a_3573_);
return v___x_3947_;
}
}
}
}
else
{
lean_dec(v___x_3933_);
v_exportedInfo_x3f_3919_ = v___x_3798_;
v___y_3920_ = v_a_3573_;
v___y_3921_ = v_a_3574_;
goto v___jp_3918_;
}
v___jp_3918_:
{
lean_object* v_toConstantVal_3922_; lean_object* v_name_3923_; lean_object* v___x_3924_; uint8_t v___x_3925_; 
v_toConstantVal_3922_ = lean_ctor_get(v_val_3917_, 0);
v_name_3923_ = lean_ctor_get(v_toConstantVal_3922_, 0);
lean_inc_ref(v_val_3917_);
v___x_3924_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3924_, 0, v_val_3917_);
v___x_3925_ = 1;
lean_inc(v_name_3923_);
v_fst_3850_ = v_name_3923_;
v_fst_3851_ = v___x_3924_;
v_snd_3852_ = v___x_3925_;
v_exportedInfo_x3f_3853_ = v_exportedInfo_x3f_3919_;
v___y_3854_ = v___y_3920_;
v___y_3855_ = v___y_3921_;
goto v___jp_3849_;
}
v___jp_3926_:
{
lean_object* v_toConstantVal_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; 
v_toConstantVal_3929_ = lean_ctor_get(v_val_3917_, 0);
lean_inc_ref(v_toConstantVal_3929_);
v___x_3930_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3930_, 0, v_toConstantVal_3929_);
lean_ctor_set_uint8(v___x_3930_, sizeof(void*)*1, v_hasTrace_3629_);
v___x_3931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3930_);
v___x_3932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3931_);
v_exportedInfo_x3f_3919_ = v___x_3932_;
v___y_3920_ = v___y_3927_;
v___y_3921_ = v___y_3928_;
goto v___jp_3918_;
}
}
case 1:
{
lean_object* v_val_3948_; 
v_val_3948_ = lean_ctor_get(v_decl_3571_, 0);
lean_inc_ref(v_val_3948_);
v_defn_3893_ = v_val_3948_;
v___y_3894_ = v_a_3573_;
v___y_3895_ = v_a_3574_;
goto v___jp_3892_;
}
case 5:
{
lean_object* v_defns_3949_; 
v_defns_3949_ = lean_ctor_get(v_decl_3571_, 0);
if (lean_obj_tag(v_defns_3949_) == 1)
{
lean_object* v_tail_3950_; 
v_tail_3950_ = lean_ctor_get(v_defns_3949_, 1);
if (lean_obj_tag(v_tail_3950_) == 0)
{
lean_object* v_head_3951_; 
v_head_3951_ = lean_ctor_get(v_defns_3949_, 0);
lean_inc(v_head_3951_);
v_defn_3893_ = v_head_3951_;
v___y_3894_ = v_a_3573_;
v___y_3895_ = v_a_3574_;
goto v___jp_3892_;
}
else
{
lean_del_object(v___x_3768_);
v___y_3789_ = v_a_3573_;
v___y_3790_ = v_a_3574_;
goto v___jp_3788_;
}
}
else
{
lean_del_object(v___x_3768_);
v___y_3789_ = v_a_3573_;
v___y_3790_ = v_a_3574_;
goto v___jp_3788_;
}
}
case 3:
{
lean_object* v_val_3952_; lean_object* v_exportedInfo_x3f_3954_; lean_object* v___y_3955_; lean_object* v___y_3956_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
lean_del_object(v___x_3768_);
v_val_3952_ = lean_ctor_get(v_decl_3571_, 0);
v___x_3969_ = lean_st_ref_get(v_a_3574_);
v___x_3970_ = lean_st_ref_get(v_a_3574_);
if (v_forceExpose_3572_ == 0)
{
lean_object* v_env_3971_; lean_object* v_env_3972_; lean_object* v___x_3973_; uint8_t v_isModule_3974_; 
v_env_3971_ = lean_ctor_get(v___x_3969_, 0);
lean_inc_ref(v_env_3971_);
lean_dec(v___x_3969_);
v_env_3972_ = lean_ctor_get(v___x_3970_, 0);
lean_inc_ref(v_env_3972_);
lean_dec(v___x_3970_);
v___x_3973_ = l_Lean_Environment_header(v_env_3971_);
lean_dec_ref(v_env_3971_);
v_isModule_3974_ = lean_ctor_get_uint8(v___x_3973_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3973_);
if (v_isModule_3974_ == 0)
{
lean_dec_ref(v_env_3972_);
v_exportedInfo_x3f_3954_ = v___x_3798_;
v___y_3955_ = v_a_3573_;
v___y_3956_ = v_a_3574_;
goto v___jp_3953_;
}
else
{
uint8_t v_isExporting_3975_; 
v_isExporting_3975_ = lean_ctor_get_uint8(v_env_3972_, sizeof(void*)*8);
lean_dec_ref(v_env_3972_);
if (v_isExporting_3975_ == 0)
{
lean_object* v___x_3976_; lean_object* v_a_3977_; uint8_t v___x_3978_; 
v___x_3976_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_3766_, v_a_3573_);
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
lean_inc(v_a_3977_);
lean_dec_ref(v___x_3976_);
v___x_3978_ = lean_unbox(v_a_3977_);
lean_dec(v_a_3977_);
if (v___x_3978_ == 0)
{
v___y_3962_ = v_a_3573_;
v___y_3963_ = v_a_3574_;
goto v___jp_3961_;
}
else
{
lean_object* v_toConstantVal_3979_; lean_object* v_name_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
v_toConstantVal_3979_ = lean_ctor_get(v_val_3952_, 0);
v_name_3980_ = lean_ctor_get(v_toConstantVal_3979_, 0);
v___x_3981_ = lean_obj_once(&l_Lean_addDecl___closed__4, &l_Lean_addDecl___closed__4_once, _init_l_Lean_addDecl___closed__4);
lean_inc(v_name_3980_);
v___x_3982_ = l_Lean_MessageData_ofName(v_name_3980_);
v___x_3983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3981_);
lean_ctor_set(v___x_3983_, 1, v___x_3982_);
v___x_3984_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_3985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3983_);
lean_ctor_set(v___x_3985_, 1, v___x_3984_);
v___x_3986_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3766_, v___x_3985_, v_a_3573_, v_a_3574_);
if (lean_obj_tag(v___x_3986_) == 0)
{
lean_dec_ref(v___x_3986_);
v___y_3962_ = v_a_3573_;
v___y_3963_ = v_a_3574_;
goto v___jp_3961_;
}
else
{
lean_dec_ref(v_decl_3571_);
lean_dec(v_a_3574_);
lean_dec_ref(v_a_3573_);
return v___x_3986_;
}
}
}
else
{
v_exportedInfo_x3f_3954_ = v___x_3798_;
v___y_3955_ = v_a_3573_;
v___y_3956_ = v_a_3574_;
goto v___jp_3953_;
}
}
}
else
{
lean_dec(v___x_3970_);
lean_dec(v___x_3969_);
v_exportedInfo_x3f_3954_ = v___x_3798_;
v___y_3955_ = v_a_3573_;
v___y_3956_ = v_a_3574_;
goto v___jp_3953_;
}
v___jp_3953_:
{
lean_object* v_toConstantVal_3957_; lean_object* v_name_3958_; lean_object* v___x_3959_; uint8_t v___x_3960_; 
v_toConstantVal_3957_ = lean_ctor_get(v_val_3952_, 0);
v_name_3958_ = lean_ctor_get(v_toConstantVal_3957_, 0);
lean_inc_ref(v_val_3952_);
v___x_3959_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3959_, 0, v_val_3952_);
v___x_3960_ = 3;
lean_inc(v_name_3958_);
v_fst_3850_ = v_name_3958_;
v_fst_3851_ = v___x_3959_;
v_snd_3852_ = v___x_3960_;
v_exportedInfo_x3f_3853_ = v_exportedInfo_x3f_3954_;
v___y_3854_ = v___y_3955_;
v___y_3855_ = v___y_3956_;
goto v___jp_3849_;
}
v___jp_3961_:
{
lean_object* v_toConstantVal_3964_; uint8_t v_isUnsafe_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; 
v_toConstantVal_3964_ = lean_ctor_get(v_val_3952_, 0);
v_isUnsafe_3965_ = lean_ctor_get_uint8(v_val_3952_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_3964_);
v___x_3966_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3966_, 0, v_toConstantVal_3964_);
lean_ctor_set_uint8(v___x_3966_, sizeof(void*)*1, v_isUnsafe_3965_);
v___x_3967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3966_);
v___x_3968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3967_);
v_exportedInfo_x3f_3954_ = v___x_3968_;
v___y_3955_ = v___y_3962_;
v___y_3956_ = v___y_3963_;
goto v___jp_3953_;
}
}
case 0:
{
lean_object* v_val_3987_; lean_object* v_toConstantVal_3988_; lean_object* v_name_3989_; lean_object* v___x_3990_; uint8_t v___x_3991_; 
lean_del_object(v___x_3768_);
v_val_3987_ = lean_ctor_get(v_decl_3571_, 0);
v_toConstantVal_3988_ = lean_ctor_get(v_val_3987_, 0);
v_name_3989_ = lean_ctor_get(v_toConstantVal_3988_, 0);
lean_inc_ref(v_val_3987_);
v___x_3990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3990_, 0, v_val_3987_);
v___x_3991_ = 2;
lean_inc(v_name_3989_);
v_fst_3850_ = v_name_3989_;
v_fst_3851_ = v___x_3990_;
v_snd_3852_ = v___x_3991_;
v_exportedInfo_x3f_3853_ = v___x_3798_;
v___y_3854_ = v_a_3573_;
v___y_3855_ = v_a_3574_;
goto v___jp_3849_;
}
default: 
{
lean_del_object(v___x_3768_);
v___y_3789_ = v_a_3573_;
v___y_3790_ = v_a_3574_;
goto v___jp_3788_;
}
}
v___jp_3788_:
{
lean_object* v___x_3791_; lean_object* v_a_3792_; uint8_t v___x_3793_; 
v___x_3791_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_3766_, v___y_3789_);
v_a_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_a_3792_);
lean_dec_ref(v___x_3791_);
v___x_3793_ = lean_unbox(v_a_3792_);
lean_dec(v_a_3792_);
if (v___x_3793_ == 0)
{
lean_object* v___x_3794_; 
v___x_3794_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3571_, v___y_3789_, v___y_3790_);
return v___x_3794_;
}
else
{
lean_object* v___x_3795_; lean_object* v___x_3796_; 
v___x_3795_ = lean_obj_once(&l_Lean_addDecl___lam__3___closed__1, &l_Lean_addDecl___lam__3___closed__1_once, _init_l_Lean_addDecl___lam__3___closed__1);
v___x_3796_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3766_, v___x_3795_, v___y_3789_, v___y_3790_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_object* v___x_3797_; 
lean_dec_ref(v___x_3796_);
v___x_3797_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3571_, v___y_3789_, v___y_3790_);
return v___x_3797_;
}
else
{
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v_decl_3571_);
return v___x_3796_;
}
}
}
v___jp_3799_:
{
lean_object* v___x_3806_; lean_object* v___x_3807_; uint8_t v___x_3808_; 
lean_inc(v_decl_3571_);
v___x_3806_ = l_Lean_Declaration_getTopLevelNames(v_decl_3571_);
v___x_3807_ = ((lean_object*)(l_Lean_addDecl___lam__8___closed__0));
v___x_3808_ = l_List_all___redArg(v___x_3806_, v___x_3807_);
if (v___x_3808_ == 0)
{
if (lean_obj_tag(v___y_3803_) == 0)
{
lean_object* v___x_3809_; lean_object* v_a_3810_; uint8_t v___x_3811_; 
v___x_3809_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_3766_, v___y_3804_);
v_a_3810_ = lean_ctor_get(v___x_3809_, 0);
lean_inc(v_a_3810_);
lean_dec_ref(v___x_3809_);
v___x_3811_ = lean_unbox(v_a_3810_);
lean_dec(v_a_3810_);
if (v___x_3811_ == 0)
{
v___y_3753_ = v___y_3800_;
v___y_3754_ = v___y_3801_;
v___y_3755_ = v___y_3802_;
v___y_3756_ = v___y_3804_;
v___y_3757_ = v___y_3805_;
goto v___jp_3752_;
}
else
{
lean_object* v___x_3812_; lean_object* v___x_3813_; 
v___x_3812_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__2, &l_Lean_addDecl___lam__8___closed__2_once, _init_l_Lean_addDecl___lam__8___closed__2);
v___x_3813_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3766_, v___x_3812_, v___y_3804_, v___y_3805_);
if (lean_obj_tag(v___x_3813_) == 0)
{
lean_dec_ref(v___x_3813_);
v___y_3753_ = v___y_3800_;
v___y_3754_ = v___y_3801_;
v___y_3755_ = v___y_3802_;
v___y_3756_ = v___y_3804_;
v___y_3757_ = v___y_3805_;
goto v___jp_3752_;
}
else
{
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec_ref(v___y_3802_);
lean_dec(v___y_3800_);
lean_dec(v_decl_3571_);
return v___x_3813_;
}
}
}
else
{
lean_object* v___x_3814_; lean_object* v_env_3815_; lean_object* v_nextMacroScope_3816_; lean_object* v_ngen_3817_; lean_object* v_auxDeclNGen_3818_; lean_object* v_traceState_3819_; lean_object* v_messages_3820_; lean_object* v_infoState_3821_; lean_object* v_snapshotTasks_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3833_; 
v___x_3814_ = lean_st_ref_take(v___y_3805_);
v_env_3815_ = lean_ctor_get(v___x_3814_, 0);
v_nextMacroScope_3816_ = lean_ctor_get(v___x_3814_, 1);
v_ngen_3817_ = lean_ctor_get(v___x_3814_, 2);
v_auxDeclNGen_3818_ = lean_ctor_get(v___x_3814_, 3);
v_traceState_3819_ = lean_ctor_get(v___x_3814_, 4);
v_messages_3820_ = lean_ctor_get(v___x_3814_, 6);
v_infoState_3821_ = lean_ctor_get(v___x_3814_, 7);
v_snapshotTasks_3822_ = lean_ctor_get(v___x_3814_, 8);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3833_ == 0)
{
lean_object* v_unused_3834_; 
v_unused_3834_ = lean_ctor_get(v___x_3814_, 5);
lean_dec(v_unused_3834_);
v___x_3824_ = v___x_3814_;
v_isShared_3825_ = v_isSharedCheck_3833_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_snapshotTasks_3822_);
lean_inc(v_infoState_3821_);
lean_inc(v_messages_3820_);
lean_inc(v_traceState_3819_);
lean_inc(v_auxDeclNGen_3818_);
lean_inc(v_ngen_3817_);
lean_inc(v_nextMacroScope_3816_);
lean_inc(v_env_3815_);
lean_dec(v___x_3814_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3833_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3830_; 
v___x_3826_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_3827_ = lean_box(v___y_3801_);
lean_inc(v___y_3800_);
v___x_3828_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3826_, v_env_3815_, v___y_3800_, v___x_3827_);
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 5, v___x_3784_);
lean_ctor_set(v___x_3824_, 0, v___x_3828_);
v___x_3830_ = v___x_3824_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v___x_3828_);
lean_ctor_set(v_reuseFailAlloc_3832_, 1, v_nextMacroScope_3816_);
lean_ctor_set(v_reuseFailAlloc_3832_, 2, v_ngen_3817_);
lean_ctor_set(v_reuseFailAlloc_3832_, 3, v_auxDeclNGen_3818_);
lean_ctor_set(v_reuseFailAlloc_3832_, 4, v_traceState_3819_);
lean_ctor_set(v_reuseFailAlloc_3832_, 5, v___x_3784_);
lean_ctor_set(v_reuseFailAlloc_3832_, 6, v_messages_3820_);
lean_ctor_set(v_reuseFailAlloc_3832_, 7, v_infoState_3821_);
lean_ctor_set(v_reuseFailAlloc_3832_, 8, v_snapshotTasks_3822_);
v___x_3830_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
lean_object* v___x_3831_; 
v___x_3831_ = lean_st_ref_set(v___y_3805_, v___x_3830_);
v___y_3738_ = v___y_3800_;
v___y_3739_ = v___y_3801_;
v___y_3740_ = v___y_3802_;
v_exportedInfo_x3f_3741_ = v___y_3803_;
v___y_3742_ = v___y_3804_;
v___y_3743_ = v___y_3805_;
goto v___jp_3737_;
}
}
}
}
else
{
lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v_a_3837_; uint8_t v___x_3838_; 
lean_dec(v___y_3803_);
v___x_3835_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3836_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__2___redArg(v___x_3835_, v___y_3804_);
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
lean_inc(v_a_3837_);
lean_dec_ref(v___x_3836_);
v___x_3838_ = lean_unbox(v_a_3837_);
lean_dec(v_a_3837_);
if (v___x_3838_ == 0)
{
lean_object* v___x_3839_; lean_object* v_a_3840_; uint8_t v___x_3841_; 
v___x_3839_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_3766_, v___y_3804_);
v_a_3840_ = lean_ctor_get(v___x_3839_, 0);
lean_inc(v_a_3840_);
lean_dec_ref(v___x_3839_);
v___x_3841_ = lean_unbox(v_a_3840_);
lean_dec(v_a_3840_);
if (v___x_3841_ == 0)
{
v___y_3738_ = v___y_3800_;
v___y_3739_ = v___y_3801_;
v___y_3740_ = v___y_3802_;
v_exportedInfo_x3f_3741_ = v___x_3798_;
v___y_3742_ = v___y_3804_;
v___y_3743_ = v___y_3805_;
goto v___jp_3737_;
}
else
{
lean_object* v___x_3842_; lean_object* v___x_3843_; 
v___x_3842_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__4, &l_Lean_addDecl___lam__8___closed__4_once, _init_l_Lean_addDecl___lam__8___closed__4);
v___x_3843_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3766_, v___x_3842_, v___y_3804_, v___y_3805_);
if (lean_obj_tag(v___x_3843_) == 0)
{
lean_dec_ref(v___x_3843_);
v___y_3738_ = v___y_3800_;
v___y_3739_ = v___y_3801_;
v___y_3740_ = v___y_3802_;
v_exportedInfo_x3f_3741_ = v___x_3798_;
v___y_3742_ = v___y_3804_;
v___y_3743_ = v___y_3805_;
goto v___jp_3737_;
}
else
{
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec_ref(v___y_3802_);
lean_dec(v___y_3800_);
lean_dec(v_decl_3571_);
return v___x_3843_;
}
}
}
else
{
lean_object* v___x_3844_; lean_object* v_a_3845_; uint8_t v___x_3846_; 
v___x_3844_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_3766_, v___y_3804_);
v_a_3845_ = lean_ctor_get(v___x_3844_, 0);
lean_inc(v_a_3845_);
lean_dec_ref(v___x_3844_);
v___x_3846_ = lean_unbox(v_a_3845_);
lean_dec(v_a_3845_);
if (v___x_3846_ == 0)
{
v___y_3760_ = v___y_3800_;
v___y_3761_ = v___y_3801_;
v___y_3762_ = v___y_3802_;
v___y_3763_ = v___y_3804_;
v___y_3764_ = v___y_3805_;
goto v___jp_3759_;
}
else
{
lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___x_3847_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__6, &l_Lean_addDecl___lam__8___closed__6_once, _init_l_Lean_addDecl___lam__8___closed__6);
v___x_3848_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3766_, v___x_3847_, v___y_3804_, v___y_3805_);
if (lean_obj_tag(v___x_3848_) == 0)
{
lean_dec_ref(v___x_3848_);
v___y_3760_ = v___y_3800_;
v___y_3761_ = v___y_3801_;
v___y_3762_ = v___y_3802_;
v___y_3763_ = v___y_3804_;
v___y_3764_ = v___y_3805_;
goto v___jp_3759_;
}
else
{
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec_ref(v___y_3802_);
lean_dec(v___y_3800_);
lean_dec(v_decl_3571_);
return v___x_3848_;
}
}
}
}
}
v___jp_3849_:
{
lean_object* v___x_3856_; lean_object* v_env_3857_; uint8_t v___x_3858_; 
v___x_3856_ = lean_st_ref_get(v___y_3855_);
v_env_3857_ = lean_ctor_get(v___x_3856_, 0);
lean_inc_ref(v_env_3857_);
lean_dec(v___x_3856_);
v___x_3858_ = l_Lean_Environment_containsOnBranch(v_env_3857_, v_fst_3850_);
if (v___x_3858_ == 0)
{
v___y_3800_ = v_fst_3850_;
v___y_3801_ = v_snd_3852_;
v___y_3802_ = v_fst_3851_;
v___y_3803_ = v_exportedInfo_x3f_3853_;
v___y_3804_ = v___y_3854_;
v___y_3805_ = v___y_3855_;
goto v___jp_3799_;
}
else
{
lean_object* v___x_3859_; lean_object* v_env_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; 
lean_dec(v_exportedInfo_x3f_3853_);
lean_dec_ref(v_fst_3851_);
lean_dec(v_decl_3571_);
v___x_3859_ = lean_st_ref_get(v___y_3855_);
v_env_3860_ = lean_ctor_get(v___x_3859_, 0);
lean_inc_ref(v_env_3860_);
lean_dec(v___x_3859_);
v___x_3861_ = lean_elab_environment_to_kernel_env(v_env_3860_);
v___x_3862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3861_);
lean_ctor_set(v___x_3862_, 1, v_fst_3850_);
v___x_3863_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(v___x_3862_, v___y_3854_, v___y_3855_);
lean_dec(v___y_3855_);
return v___x_3863_;
}
}
v___jp_3864_:
{
lean_object* v_name_3870_; lean_object* v___x_3871_; uint8_t v___x_3872_; 
v_name_3870_ = lean_ctor_get(v_toConstantVal_3866_, 0);
lean_inc(v_name_3870_);
lean_dec_ref(v_toConstantVal_3866_);
v___x_3871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3871_, 0, v___y_3865_);
v___x_3872_ = 0;
v_fst_3850_ = v_name_3870_;
v_fst_3851_ = v___x_3871_;
v_snd_3852_ = v___x_3872_;
v_exportedInfo_x3f_3853_ = v_exportedInfo_x3f_3867_;
v___y_3854_ = v___y_3868_;
v___y_3855_ = v___y_3869_;
goto v___jp_3849_;
}
v___jp_3873_:
{
lean_object* v_toConstantVal_3878_; 
v_toConstantVal_3878_ = lean_ctor_get(v___y_3874_, 0);
lean_inc_ref(v_toConstantVal_3878_);
v___y_3865_ = v___y_3874_;
v_toConstantVal_3866_ = v_toConstantVal_3878_;
v_exportedInfo_x3f_3867_ = v_exportedInfo_x3f_3875_;
v___y_3868_ = v___y_3876_;
v___y_3869_ = v___y_3877_;
goto v___jp_3864_;
}
v___jp_3879_:
{
uint8_t v___x_3885_; uint8_t v___x_3886_; lean_object* v___x_3888_; 
v___x_3885_ = 0;
v___x_3886_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3882_, v___x_3885_);
lean_inc_ref(v_toConstantVal_3881_);
if (v_isShared_3769_ == 0)
{
lean_ctor_set(v___x_3768_, 0, v_toConstantVal_3881_);
v___x_3888_ = v___x_3768_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_toConstantVal_3881_);
v___x_3888_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; 
lean_ctor_set_uint8(v___x_3888_, sizeof(void*)*1, v___x_3886_);
v___x_3889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3888_);
v___x_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3889_);
v___y_3865_ = v___y_3880_;
v_toConstantVal_3866_ = v_toConstantVal_3881_;
v_exportedInfo_x3f_3867_ = v___x_3890_;
v___y_3868_ = v___y_3883_;
v___y_3869_ = v___y_3884_;
goto v___jp_3864_;
}
}
v___jp_3892_:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3896_ = lean_st_ref_get(v___y_3895_);
v___x_3897_ = lean_st_ref_get(v___y_3895_);
if (v_forceExpose_3572_ == 0)
{
lean_object* v_env_3898_; lean_object* v_env_3899_; lean_object* v___x_3900_; uint8_t v_isModule_3901_; 
v_env_3898_ = lean_ctor_get(v___x_3896_, 0);
lean_inc_ref(v_env_3898_);
lean_dec(v___x_3896_);
v_env_3899_ = lean_ctor_get(v___x_3897_, 0);
lean_inc_ref(v_env_3899_);
lean_dec(v___x_3897_);
v___x_3900_ = l_Lean_Environment_header(v_env_3898_);
lean_dec_ref(v_env_3898_);
v_isModule_3901_ = lean_ctor_get_uint8(v___x_3900_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3900_);
if (v_isModule_3901_ == 0)
{
lean_dec_ref(v_env_3899_);
lean_del_object(v___x_3768_);
v___y_3874_ = v_defn_3893_;
v_exportedInfo_x3f_3875_ = v___x_3798_;
v___y_3876_ = v___y_3894_;
v___y_3877_ = v___y_3895_;
goto v___jp_3873_;
}
else
{
uint8_t v_isExporting_3902_; 
v_isExporting_3902_ = lean_ctor_get_uint8(v_env_3899_, sizeof(void*)*8);
lean_dec_ref(v_env_3899_);
if (v_isExporting_3902_ == 0)
{
lean_object* v___x_3903_; lean_object* v_a_3904_; uint8_t v___x_3905_; 
v___x_3903_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_3766_, v___y_3894_);
v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
lean_inc(v_a_3904_);
lean_dec_ref(v___x_3903_);
v___x_3905_ = lean_unbox(v_a_3904_);
lean_dec(v_a_3904_);
if (v___x_3905_ == 0)
{
lean_object* v_toConstantVal_3906_; uint8_t v_safety_3907_; 
v_toConstantVal_3906_ = lean_ctor_get(v_defn_3893_, 0);
lean_inc_ref(v_toConstantVal_3906_);
v_safety_3907_ = lean_ctor_get_uint8(v_defn_3893_, sizeof(void*)*4);
v___y_3880_ = v_defn_3893_;
v_toConstantVal_3881_ = v_toConstantVal_3906_;
v_safety_3882_ = v_safety_3907_;
v___y_3883_ = v___y_3894_;
v___y_3884_ = v___y_3895_;
goto v___jp_3879_;
}
else
{
lean_object* v_toConstantVal_3908_; uint8_t v_safety_3909_; lean_object* v_name_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v_toConstantVal_3908_ = lean_ctor_get(v_defn_3893_, 0);
lean_inc_ref(v_toConstantVal_3908_);
v_safety_3909_ = lean_ctor_get_uint8(v_defn_3893_, sizeof(void*)*4);
v_name_3910_ = lean_ctor_get(v_toConstantVal_3908_, 0);
v___x_3911_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__1, &l_Lean_addDecl___lam__4___closed__1_once, _init_l_Lean_addDecl___lam__4___closed__1);
lean_inc(v_name_3910_);
v___x_3912_ = l_Lean_MessageData_ofName(v_name_3910_);
v___x_3913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3911_);
lean_ctor_set(v___x_3913_, 1, v___x_3912_);
v___x_3914_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_3915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3913_);
lean_ctor_set(v___x_3915_, 1, v___x_3914_);
v___x_3916_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3766_, v___x_3915_, v___y_3894_, v___y_3895_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_dec_ref(v___x_3916_);
v___y_3880_ = v_defn_3893_;
v_toConstantVal_3881_ = v_toConstantVal_3908_;
v_safety_3882_ = v_safety_3909_;
v___y_3883_ = v___y_3894_;
v___y_3884_ = v___y_3895_;
goto v___jp_3879_;
}
else
{
lean_dec_ref(v_toConstantVal_3908_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec_ref(v_defn_3893_);
lean_del_object(v___x_3768_);
lean_dec(v_decl_3571_);
return v___x_3916_;
}
}
}
else
{
lean_del_object(v___x_3768_);
v___y_3874_ = v_defn_3893_;
v_exportedInfo_x3f_3875_ = v___x_3798_;
v___y_3876_ = v___y_3894_;
v___y_3877_ = v___y_3895_;
goto v___jp_3873_;
}
}
}
else
{
lean_dec(v___x_3897_);
lean_dec(v___x_3896_);
lean_del_object(v___x_3768_);
v___y_3874_ = v_defn_3893_;
v_exportedInfo_x3f_3875_ = v___x_3798_;
v___y_3876_ = v___y_3894_;
v___y_3877_ = v___y_3895_;
goto v___jp_3873_;
}
}
}
}
}
}
else
{
lean_object* v___x_3997_; lean_object* v_a_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4703_; 
v___x_3997_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_3766_, v_a_3573_);
v_a_3998_ = lean_ctor_get(v___x_3997_, 0);
v_isSharedCheck_4703_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4703_ == 0)
{
v___x_4000_ = v___x_3997_;
v_isShared_4001_ = v_isSharedCheck_4703_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_a_3998_);
lean_dec(v___x_3997_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4703_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___f_4002_; lean_object* v___x_4003_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v_a_4007_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v_a_4020_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v_a_4054_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v_a_4070_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; uint8_t v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; uint8_t v___x_4315_; 
lean_inc(v_decl_3571_);
v___f_4002_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__1___boxed), 5, 1);
lean_closure_set(v___f_4002_, 0, v_decl_3571_);
v___x_4003_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_4315_ = lean_unbox(v_a_3998_);
if (v___x_4315_ == 0)
{
lean_object* v___x_4316_; uint8_t v___x_4317_; lean_object* v___y_4319_; lean_object* v___y_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; uint8_t v___y_4398_; lean_object* v___y_4399_; lean_object* v___y_4400_; lean_object* v___y_4401_; lean_object* v___y_4423_; uint8_t v___y_4424_; lean_object* v___y_4425_; lean_object* v_exportedInfo_x3f_4426_; lean_object* v___y_4427_; lean_object* v___y_4428_; uint8_t v___y_4438_; lean_object* v___y_4439_; lean_object* v___y_4440_; lean_object* v___y_4441_; lean_object* v___y_4442_; uint8_t v___y_4445_; lean_object* v___y_4446_; lean_object* v___y_4447_; lean_object* v___y_4448_; lean_object* v___y_4449_; 
v___x_4316_ = l_Lean_trace_profiler;
v___x_4317_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3628_, v___x_4316_);
if (v___x_4317_ == 0)
{
lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4701_; 
lean_dec_ref(v___f_4002_);
lean_del_object(v___x_4000_);
lean_dec(v_a_3998_);
v_isSharedCheck_4701_ = !lean_is_exclusive(v_options_3628_);
if (v_isSharedCheck_4701_ == 0)
{
lean_object* v_unused_4702_; 
v_unused_4702_ = lean_ctor_get(v_options_3628_, 0);
lean_dec(v_unused_4702_);
v___x_4452_ = v_options_3628_;
v_isShared_4453_ = v_isSharedCheck_4701_;
goto v_resetjp_4451_;
}
else
{
lean_dec(v_options_3628_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4701_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v___x_4454_; lean_object* v_env_4455_; lean_object* v_nextMacroScope_4456_; lean_object* v_ngen_4457_; lean_object* v_auxDeclNGen_4458_; lean_object* v_traceState_4459_; lean_object* v_messages_4460_; lean_object* v_infoState_4461_; lean_object* v_snapshotTasks_4462_; lean_object* v___x_4464_; uint8_t v_isShared_4465_; uint8_t v_isSharedCheck_4699_; 
v___x_4454_ = lean_st_ref_take(v_a_3574_);
v_env_4455_ = lean_ctor_get(v___x_4454_, 0);
v_nextMacroScope_4456_ = lean_ctor_get(v___x_4454_, 1);
v_ngen_4457_ = lean_ctor_get(v___x_4454_, 2);
v_auxDeclNGen_4458_ = lean_ctor_get(v___x_4454_, 3);
v_traceState_4459_ = lean_ctor_get(v___x_4454_, 4);
v_messages_4460_ = lean_ctor_get(v___x_4454_, 6);
v_infoState_4461_ = lean_ctor_get(v___x_4454_, 7);
v_snapshotTasks_4462_ = lean_ctor_get(v___x_4454_, 8);
v_isSharedCheck_4699_ = !lean_is_exclusive(v___x_4454_);
if (v_isSharedCheck_4699_ == 0)
{
lean_object* v_unused_4700_; 
v_unused_4700_ = lean_ctor_get(v___x_4454_, 5);
lean_dec(v_unused_4700_);
v___x_4464_ = v___x_4454_;
v_isShared_4465_ = v_isSharedCheck_4699_;
goto v_resetjp_4463_;
}
else
{
lean_inc(v_snapshotTasks_4462_);
lean_inc(v_infoState_4461_);
lean_inc(v_messages_4460_);
lean_inc(v_traceState_4459_);
lean_inc(v_auxDeclNGen_4458_);
lean_inc(v_ngen_4457_);
lean_inc(v_nextMacroScope_4456_);
lean_inc(v_env_4455_);
lean_dec(v___x_4454_);
v___x_4464_ = lean_box(0);
v_isShared_4465_ = v_isSharedCheck_4699_;
goto v_resetjp_4463_;
}
v_resetjp_4463_:
{
lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___y_4470_; lean_object* v___y_4471_; lean_object* v___y_4472_; uint8_t v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___x_4498_; 
lean_inc(v_decl_3571_);
v___x_4466_ = l_Lean_Declaration_getNames(v_decl_3571_);
v___x_4467_ = l_List_foldl___at___00Lean_addDecl_spec__1(v_env_4455_, v___x_4466_);
v___x_4468_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2);
if (v_isShared_4465_ == 0)
{
lean_ctor_set(v___x_4464_, 5, v___x_4468_);
lean_ctor_set(v___x_4464_, 0, v___x_4467_);
v___x_4498_ = v___x_4464_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v___x_4467_);
lean_ctor_set(v_reuseFailAlloc_4698_, 1, v_nextMacroScope_4456_);
lean_ctor_set(v_reuseFailAlloc_4698_, 2, v_ngen_4457_);
lean_ctor_set(v_reuseFailAlloc_4698_, 3, v_auxDeclNGen_4458_);
lean_ctor_set(v_reuseFailAlloc_4698_, 4, v_traceState_4459_);
lean_ctor_set(v_reuseFailAlloc_4698_, 5, v___x_4468_);
lean_ctor_set(v_reuseFailAlloc_4698_, 6, v_messages_4460_);
lean_ctor_set(v_reuseFailAlloc_4698_, 7, v_infoState_4461_);
lean_ctor_set(v_reuseFailAlloc_4698_, 8, v_snapshotTasks_4462_);
v___x_4498_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4497_;
}
v___jp_4469_:
{
lean_object* v___x_4476_; lean_object* v_env_4477_; lean_object* v_nextMacroScope_4478_; lean_object* v_ngen_4479_; lean_object* v_auxDeclNGen_4480_; lean_object* v_traceState_4481_; lean_object* v_messages_4482_; lean_object* v_infoState_4483_; lean_object* v_snapshotTasks_4484_; lean_object* v___x_4486_; uint8_t v_isShared_4487_; uint8_t v_isSharedCheck_4495_; 
v___x_4476_ = lean_st_ref_take(v___y_4470_);
v_env_4477_ = lean_ctor_get(v___x_4476_, 0);
v_nextMacroScope_4478_ = lean_ctor_get(v___x_4476_, 1);
v_ngen_4479_ = lean_ctor_get(v___x_4476_, 2);
v_auxDeclNGen_4480_ = lean_ctor_get(v___x_4476_, 3);
v_traceState_4481_ = lean_ctor_get(v___x_4476_, 4);
v_messages_4482_ = lean_ctor_get(v___x_4476_, 6);
v_infoState_4483_ = lean_ctor_get(v___x_4476_, 7);
v_snapshotTasks_4484_ = lean_ctor_get(v___x_4476_, 8);
v_isSharedCheck_4495_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4495_ == 0)
{
lean_object* v_unused_4496_; 
v_unused_4496_ = lean_ctor_get(v___x_4476_, 5);
lean_dec(v_unused_4496_);
v___x_4486_ = v___x_4476_;
v_isShared_4487_ = v_isSharedCheck_4495_;
goto v_resetjp_4485_;
}
else
{
lean_inc(v_snapshotTasks_4484_);
lean_inc(v_infoState_4483_);
lean_inc(v_messages_4482_);
lean_inc(v_traceState_4481_);
lean_inc(v_auxDeclNGen_4480_);
lean_inc(v_ngen_4479_);
lean_inc(v_nextMacroScope_4478_);
lean_inc(v_env_4477_);
lean_dec(v___x_4476_);
v___x_4486_ = lean_box(0);
v_isShared_4487_ = v_isSharedCheck_4495_;
goto v_resetjp_4485_;
}
v_resetjp_4485_:
{
lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4492_; 
v___x_4488_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4489_ = lean_box(v___y_4473_);
lean_inc(v___y_4474_);
v___x_4490_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4488_, v_env_4477_, v___y_4474_, v___x_4489_);
if (v_isShared_4487_ == 0)
{
lean_ctor_set(v___x_4486_, 5, v___x_4468_);
lean_ctor_set(v___x_4486_, 0, v___x_4490_);
v___x_4492_ = v___x_4486_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v___x_4490_);
lean_ctor_set(v_reuseFailAlloc_4494_, 1, v_nextMacroScope_4478_);
lean_ctor_set(v_reuseFailAlloc_4494_, 2, v_ngen_4479_);
lean_ctor_set(v_reuseFailAlloc_4494_, 3, v_auxDeclNGen_4480_);
lean_ctor_set(v_reuseFailAlloc_4494_, 4, v_traceState_4481_);
lean_ctor_set(v_reuseFailAlloc_4494_, 5, v___x_4468_);
lean_ctor_set(v_reuseFailAlloc_4494_, 6, v_messages_4482_);
lean_ctor_set(v_reuseFailAlloc_4494_, 7, v_infoState_4483_);
lean_ctor_set(v_reuseFailAlloc_4494_, 8, v_snapshotTasks_4484_);
v___x_4492_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
lean_object* v___x_4493_; 
v___x_4493_ = lean_st_ref_set(v___y_4470_, v___x_4492_);
v___y_4423_ = v___y_4474_;
v___y_4424_ = v___y_4473_;
v___y_4425_ = v___y_4475_;
v_exportedInfo_x3f_4426_ = v___y_4472_;
v___y_4427_ = v___y_4471_;
v___y_4428_ = v___y_4470_;
goto v___jp_4422_;
}
}
}
v_reusejp_4497_:
{
lean_object* v___x_4499_; lean_object* v___y_4501_; lean_object* v___y_4502_; lean_object* v___x_4510_; lean_object* v___y_4512_; lean_object* v___y_4513_; uint8_t v___y_4514_; lean_object* v___y_4515_; lean_object* v___y_4516_; lean_object* v___y_4517_; lean_object* v_fst_4541_; lean_object* v_fst_4542_; uint8_t v_snd_4543_; lean_object* v_exportedInfo_x3f_4544_; lean_object* v___y_4545_; lean_object* v___y_4546_; lean_object* v___y_4556_; lean_object* v_toConstantVal_4557_; lean_object* v_exportedInfo_x3f_4558_; lean_object* v___y_4559_; lean_object* v___y_4560_; lean_object* v___y_4565_; lean_object* v_toConstantVal_4566_; uint8_t v_safety_4567_; lean_object* v___y_4568_; lean_object* v___y_4569_; lean_object* v___y_4578_; lean_object* v___y_4579_; lean_object* v___y_4580_; lean_object* v___y_4596_; lean_object* v_exportedInfo_x3f_4597_; lean_object* v___y_4598_; lean_object* v___y_4599_; lean_object* v___y_4602_; lean_object* v___y_4603_; lean_object* v___y_4604_; lean_object* v___y_4605_; lean_object* v___y_4606_; lean_object* v_defn_4611_; lean_object* v___y_4612_; lean_object* v___y_4613_; 
v___x_4499_ = lean_st_ref_set(v_a_3574_, v___x_4498_);
v___x_4510_ = lean_box(0);
switch(lean_obj_tag(v_decl_3571_))
{
case 2:
{
lean_object* v_val_4620_; lean_object* v_exportedInfo_x3f_4622_; lean_object* v___y_4623_; lean_object* v___y_4624_; lean_object* v___y_4630_; lean_object* v___y_4631_; lean_object* v___x_4636_; lean_object* v_env_4637_; 
lean_del_object(v___x_4452_);
v_val_4620_ = lean_ctor_get(v_decl_3571_, 0);
v___x_4636_ = lean_st_ref_get(v_a_3574_);
v_env_4637_ = lean_ctor_get(v___x_4636_, 0);
lean_inc_ref(v_env_4637_);
lean_dec(v___x_4636_);
if (v_forceExpose_3572_ == 0)
{
goto v___jp_4638_;
}
else
{
if (v___x_4317_ == 0)
{
lean_dec_ref(v_env_4637_);
v_exportedInfo_x3f_4622_ = v___x_4510_;
v___y_4623_ = v_a_3573_;
v___y_4624_ = v_a_3574_;
goto v___jp_4621_;
}
else
{
goto v___jp_4638_;
}
}
v___jp_4621_:
{
lean_object* v_toConstantVal_4625_; lean_object* v_name_4626_; lean_object* v___x_4627_; uint8_t v___x_4628_; 
v_toConstantVal_4625_ = lean_ctor_get(v_val_4620_, 0);
v_name_4626_ = lean_ctor_get(v_toConstantVal_4625_, 0);
lean_inc_ref(v_val_4620_);
v___x_4627_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4627_, 0, v_val_4620_);
v___x_4628_ = 1;
lean_inc(v_name_4626_);
v_fst_4541_ = v_name_4626_;
v_fst_4542_ = v___x_4627_;
v_snd_4543_ = v___x_4628_;
v_exportedInfo_x3f_4544_ = v_exportedInfo_x3f_4622_;
v___y_4545_ = v___y_4623_;
v___y_4546_ = v___y_4624_;
goto v___jp_4540_;
}
v___jp_4629_:
{
lean_object* v_toConstantVal_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; 
v_toConstantVal_4632_ = lean_ctor_get(v_val_4620_, 0);
lean_inc_ref(v_toConstantVal_4632_);
v___x_4633_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4633_, 0, v_toConstantVal_4632_);
lean_ctor_set_uint8(v___x_4633_, sizeof(void*)*1, v___x_4317_);
v___x_4634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4634_, 0, v___x_4633_);
v___x_4635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4635_, 0, v___x_4634_);
v_exportedInfo_x3f_4622_ = v___x_4635_;
v___y_4623_ = v___y_4630_;
v___y_4624_ = v___y_4631_;
goto v___jp_4621_;
}
v___jp_4638_:
{
lean_object* v___x_4639_; uint8_t v_isModule_4640_; 
v___x_4639_ = l_Lean_Environment_header(v_env_4637_);
lean_dec_ref(v_env_4637_);
v_isModule_4640_ = lean_ctor_get_uint8(v___x_4639_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4639_);
if (v_isModule_4640_ == 0)
{
v_exportedInfo_x3f_4622_ = v___x_4510_;
v___y_4623_ = v_a_3573_;
v___y_4624_ = v_a_3574_;
goto v___jp_4621_;
}
else
{
lean_object* v___x_4641_; lean_object* v_a_4642_; uint8_t v___x_4643_; 
v___x_4641_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_3766_, v_a_3573_);
v_a_4642_ = lean_ctor_get(v___x_4641_, 0);
lean_inc(v_a_4642_);
lean_dec_ref(v___x_4641_);
v___x_4643_ = lean_unbox(v_a_4642_);
lean_dec(v_a_4642_);
if (v___x_4643_ == 0)
{
v___y_4630_ = v_a_3573_;
v___y_4631_ = v_a_3574_;
goto v___jp_4629_;
}
else
{
lean_object* v_toConstantVal_4644_; lean_object* v_name_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; 
v_toConstantVal_4644_ = lean_ctor_get(v_val_4620_, 0);
v_name_4645_ = lean_ctor_get(v_toConstantVal_4644_, 0);
v___x_4646_ = lean_obj_once(&l_Lean_addDecl___closed__2, &l_Lean_addDecl___closed__2_once, _init_l_Lean_addDecl___closed__2);
lean_inc(v_name_4645_);
v___x_4647_ = l_Lean_MessageData_ofName(v_name_4645_);
v___x_4648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4648_, 0, v___x_4646_);
lean_ctor_set(v___x_4648_, 1, v___x_4647_);
v___x_4649_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_4650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4650_, 0, v___x_4648_);
lean_ctor_set(v___x_4650_, 1, v___x_4649_);
v___x_4651_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3766_, v___x_4650_, v_a_3573_, v_a_3574_);
if (lean_obj_tag(v___x_4651_) == 0)
{
lean_dec_ref(v___x_4651_);
v___y_4630_ = v_a_3573_;
v___y_4631_ = v_a_3574_;
goto v___jp_4629_;
}
else
{
lean_dec_ref(v_decl_3571_);
lean_dec(v_a_3574_);
lean_dec_ref(v_a_3573_);
return v___x_4651_;
}
}
}
}
}
case 1:
{
lean_object* v_val_4652_; 
v_val_4652_ = lean_ctor_get(v_decl_3571_, 0);
lean_inc_ref(v_val_4652_);
v_defn_4611_ = v_val_4652_;
v___y_4612_ = v_a_3573_;
v___y_4613_ = v_a_3574_;
goto v___jp_4610_;
}
case 5:
{
lean_object* v_defns_4653_; 
v_defns_4653_ = lean_ctor_get(v_decl_3571_, 0);
if (lean_obj_tag(v_defns_4653_) == 1)
{
lean_object* v_tail_4654_; 
v_tail_4654_ = lean_ctor_get(v_defns_4653_, 1);
if (lean_obj_tag(v_tail_4654_) == 0)
{
lean_object* v_head_4655_; 
v_head_4655_ = lean_ctor_get(v_defns_4653_, 0);
lean_inc(v_head_4655_);
v_defn_4611_ = v_head_4655_;
v___y_4612_ = v_a_3573_;
v___y_4613_ = v_a_3574_;
goto v___jp_4610_;
}
else
{
lean_del_object(v___x_4452_);
v___y_4501_ = v_a_3573_;
v___y_4502_ = v_a_3574_;
goto v___jp_4500_;
}
}
else
{
lean_del_object(v___x_4452_);
v___y_4501_ = v_a_3573_;
v___y_4502_ = v_a_3574_;
goto v___jp_4500_;
}
}
case 3:
{
lean_object* v_val_4656_; lean_object* v_exportedInfo_x3f_4658_; lean_object* v___y_4659_; lean_object* v___y_4660_; lean_object* v___y_4666_; lean_object* v___y_4667_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v_env_4687_; lean_object* v_env_4688_; 
lean_del_object(v___x_4452_);
v_val_4656_ = lean_ctor_get(v_decl_3571_, 0);
v___x_4673_ = lean_st_ref_get(v_a_3574_);
v___x_4674_ = lean_st_ref_get(v_a_3574_);
v_env_4687_ = lean_ctor_get(v___x_4673_, 0);
lean_inc_ref(v_env_4687_);
lean_dec(v___x_4673_);
v_env_4688_ = lean_ctor_get(v___x_4674_, 0);
lean_inc_ref(v_env_4688_);
lean_dec(v___x_4674_);
if (v_forceExpose_3572_ == 0)
{
goto v___jp_4689_;
}
else
{
if (v___x_4317_ == 0)
{
lean_dec_ref(v_env_4688_);
lean_dec_ref(v_env_4687_);
v_exportedInfo_x3f_4658_ = v___x_4510_;
v___y_4659_ = v_a_3573_;
v___y_4660_ = v_a_3574_;
goto v___jp_4657_;
}
else
{
goto v___jp_4689_;
}
}
v___jp_4657_:
{
lean_object* v_toConstantVal_4661_; lean_object* v_name_4662_; lean_object* v___x_4663_; uint8_t v___x_4664_; 
v_toConstantVal_4661_ = lean_ctor_get(v_val_4656_, 0);
v_name_4662_ = lean_ctor_get(v_toConstantVal_4661_, 0);
lean_inc_ref(v_val_4656_);
v___x_4663_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4663_, 0, v_val_4656_);
v___x_4664_ = 3;
lean_inc(v_name_4662_);
v_fst_4541_ = v_name_4662_;
v_fst_4542_ = v___x_4663_;
v_snd_4543_ = v___x_4664_;
v_exportedInfo_x3f_4544_ = v_exportedInfo_x3f_4658_;
v___y_4545_ = v___y_4659_;
v___y_4546_ = v___y_4660_;
goto v___jp_4540_;
}
v___jp_4665_:
{
lean_object* v_toConstantVal_4668_; uint8_t v_isUnsafe_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; 
v_toConstantVal_4668_ = lean_ctor_get(v_val_4656_, 0);
v_isUnsafe_4669_ = lean_ctor_get_uint8(v_val_4656_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4668_);
v___x_4670_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4670_, 0, v_toConstantVal_4668_);
lean_ctor_set_uint8(v___x_4670_, sizeof(void*)*1, v_isUnsafe_4669_);
v___x_4671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4671_, 0, v___x_4670_);
v___x_4672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4672_, 0, v___x_4671_);
v_exportedInfo_x3f_4658_ = v___x_4672_;
v___y_4659_ = v___y_4666_;
v___y_4660_ = v___y_4667_;
goto v___jp_4657_;
}
v___jp_4675_:
{
lean_object* v___x_4676_; lean_object* v_a_4677_; uint8_t v___x_4678_; 
v___x_4676_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_3766_, v_a_3573_);
v_a_4677_ = lean_ctor_get(v___x_4676_, 0);
lean_inc(v_a_4677_);
lean_dec_ref(v___x_4676_);
v___x_4678_ = lean_unbox(v_a_4677_);
lean_dec(v_a_4677_);
if (v___x_4678_ == 0)
{
v___y_4666_ = v_a_3573_;
v___y_4667_ = v_a_3574_;
goto v___jp_4665_;
}
else
{
lean_object* v_toConstantVal_4679_; lean_object* v_name_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; 
v_toConstantVal_4679_ = lean_ctor_get(v_val_4656_, 0);
v_name_4680_ = lean_ctor_get(v_toConstantVal_4679_, 0);
v___x_4681_ = lean_obj_once(&l_Lean_addDecl___closed__4, &l_Lean_addDecl___closed__4_once, _init_l_Lean_addDecl___closed__4);
lean_inc(v_name_4680_);
v___x_4682_ = l_Lean_MessageData_ofName(v_name_4680_);
v___x_4683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4683_, 0, v___x_4681_);
lean_ctor_set(v___x_4683_, 1, v___x_4682_);
v___x_4684_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_4685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4685_, 0, v___x_4683_);
lean_ctor_set(v___x_4685_, 1, v___x_4684_);
v___x_4686_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3766_, v___x_4685_, v_a_3573_, v_a_3574_);
if (lean_obj_tag(v___x_4686_) == 0)
{
lean_dec_ref(v___x_4686_);
v___y_4666_ = v_a_3573_;
v___y_4667_ = v_a_3574_;
goto v___jp_4665_;
}
else
{
lean_dec_ref(v_decl_3571_);
lean_dec(v_a_3574_);
lean_dec_ref(v_a_3573_);
return v___x_4686_;
}
}
}
v___jp_4689_:
{
lean_object* v___x_4690_; uint8_t v_isModule_4691_; 
v___x_4690_ = l_Lean_Environment_header(v_env_4687_);
lean_dec_ref(v_env_4687_);
v_isModule_4691_ = lean_ctor_get_uint8(v___x_4690_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4690_);
if (v_isModule_4691_ == 0)
{
lean_dec_ref(v_env_4688_);
v_exportedInfo_x3f_4658_ = v___x_4510_;
v___y_4659_ = v_a_3573_;
v___y_4660_ = v_a_3574_;
goto v___jp_4657_;
}
else
{
uint8_t v_isExporting_4692_; 
v_isExporting_4692_ = lean_ctor_get_uint8(v_env_4688_, sizeof(void*)*8);
lean_dec_ref(v_env_4688_);
if (v_isExporting_4692_ == 0)
{
goto v___jp_4675_;
}
else
{
if (v___x_4317_ == 0)
{
v_exportedInfo_x3f_4658_ = v___x_4510_;
v___y_4659_ = v_a_3573_;
v___y_4660_ = v_a_3574_;
goto v___jp_4657_;
}
else
{
goto v___jp_4675_;
}
}
}
}
}
case 0:
{
lean_object* v_val_4693_; lean_object* v_toConstantVal_4694_; lean_object* v_name_4695_; lean_object* v___x_4696_; uint8_t v___x_4697_; 
lean_del_object(v___x_4452_);
v_val_4693_ = lean_ctor_get(v_decl_3571_, 0);
v_toConstantVal_4694_ = lean_ctor_get(v_val_4693_, 0);
v_name_4695_ = lean_ctor_get(v_toConstantVal_4694_, 0);
lean_inc_ref(v_val_4693_);
v___x_4696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4696_, 0, v_val_4693_);
v___x_4697_ = 2;
lean_inc(v_name_4695_);
v_fst_4541_ = v_name_4695_;
v_fst_4542_ = v___x_4696_;
v_snd_4543_ = v___x_4697_;
v_exportedInfo_x3f_4544_ = v___x_4510_;
v___y_4545_ = v_a_3573_;
v___y_4546_ = v_a_3574_;
goto v___jp_4540_;
}
default: 
{
lean_del_object(v___x_4452_);
v___y_4501_ = v_a_3573_;
v___y_4502_ = v_a_3574_;
goto v___jp_4500_;
}
}
v___jp_4500_:
{
lean_object* v___x_4503_; lean_object* v_a_4504_; uint8_t v___x_4505_; 
v___x_4503_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_3766_, v___y_4501_);
v_a_4504_ = lean_ctor_get(v___x_4503_, 0);
lean_inc(v_a_4504_);
lean_dec_ref(v___x_4503_);
v___x_4505_ = lean_unbox(v_a_4504_);
lean_dec(v_a_4504_);
if (v___x_4505_ == 0)
{
lean_object* v___x_4506_; 
v___x_4506_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3571_, v___y_4501_, v___y_4502_);
return v___x_4506_;
}
else
{
lean_object* v___x_4507_; lean_object* v___x_4508_; 
v___x_4507_ = lean_obj_once(&l_Lean_addDecl___lam__3___closed__1, &l_Lean_addDecl___lam__3___closed__1_once, _init_l_Lean_addDecl___lam__3___closed__1);
v___x_4508_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3766_, v___x_4507_, v___y_4501_, v___y_4502_);
if (lean_obj_tag(v___x_4508_) == 0)
{
lean_object* v___x_4509_; 
lean_dec_ref(v___x_4508_);
v___x_4509_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3571_, v___y_4501_, v___y_4502_);
return v___x_4509_;
}
else
{
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
lean_dec(v_decl_3571_);
return v___x_4508_;
}
}
}
v___jp_4511_:
{
lean_object* v___x_4518_; lean_object* v___x_4519_; uint8_t v___x_4520_; 
lean_inc(v_decl_3571_);
v___x_4518_ = l_Lean_Declaration_getTopLevelNames(v_decl_3571_);
v___x_4519_ = ((lean_object*)(l_Lean_addDecl___lam__8___closed__0));
v___x_4520_ = l_List_all___redArg(v___x_4518_, v___x_4519_);
if (v___x_4520_ == 0)
{
if (lean_obj_tag(v___y_4512_) == 0)
{
if (v___x_4317_ == 0)
{
lean_object* v___x_4521_; lean_object* v_a_4522_; uint8_t v___x_4523_; 
v___x_4521_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_3766_, v___y_4516_);
v_a_4522_ = lean_ctor_get(v___x_4521_, 0);
lean_inc(v_a_4522_);
lean_dec_ref(v___x_4521_);
v___x_4523_ = lean_unbox(v_a_4522_);
lean_dec(v_a_4522_);
if (v___x_4523_ == 0)
{
v___y_4438_ = v___y_4514_;
v___y_4439_ = v___y_4513_;
v___y_4440_ = v___y_4515_;
v___y_4441_ = v___y_4516_;
v___y_4442_ = v___y_4517_;
goto v___jp_4437_;
}
else
{
lean_object* v___x_4524_; lean_object* v___x_4525_; 
v___x_4524_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__2, &l_Lean_addDecl___lam__8___closed__2_once, _init_l_Lean_addDecl___lam__8___closed__2);
v___x_4525_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3766_, v___x_4524_, v___y_4516_, v___y_4517_);
if (lean_obj_tag(v___x_4525_) == 0)
{
lean_dec_ref(v___x_4525_);
v___y_4438_ = v___y_4514_;
v___y_4439_ = v___y_4513_;
v___y_4440_ = v___y_4515_;
v___y_4441_ = v___y_4516_;
v___y_4442_ = v___y_4517_;
goto v___jp_4437_;
}
else
{
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
lean_dec_ref(v___y_4515_);
lean_dec(v___y_4513_);
lean_dec(v_decl_3571_);
return v___x_4525_;
}
}
}
else
{
v___y_4470_ = v___y_4517_;
v___y_4471_ = v___y_4516_;
v___y_4472_ = v___y_4512_;
v___y_4473_ = v___y_4514_;
v___y_4474_ = v___y_4513_;
v___y_4475_ = v___y_4515_;
goto v___jp_4469_;
}
}
else
{
v___y_4470_ = v___y_4517_;
v___y_4471_ = v___y_4516_;
v___y_4472_ = v___y_4512_;
v___y_4473_ = v___y_4514_;
v___y_4474_ = v___y_4513_;
v___y_4475_ = v___y_4515_;
goto v___jp_4469_;
}
}
else
{
lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v_a_4528_; uint8_t v___x_4529_; 
lean_dec(v___y_4512_);
v___x_4526_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4527_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__2___redArg(v___x_4526_, v___y_4516_);
v_a_4528_ = lean_ctor_get(v___x_4527_, 0);
lean_inc(v_a_4528_);
lean_dec_ref(v___x_4527_);
v___x_4529_ = lean_unbox(v_a_4528_);
lean_dec(v_a_4528_);
if (v___x_4529_ == 0)
{
lean_object* v___x_4530_; lean_object* v_a_4531_; uint8_t v___x_4532_; 
v___x_4530_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_3766_, v___y_4516_);
v_a_4531_ = lean_ctor_get(v___x_4530_, 0);
lean_inc(v_a_4531_);
lean_dec_ref(v___x_4530_);
v___x_4532_ = lean_unbox(v_a_4531_);
lean_dec(v_a_4531_);
if (v___x_4532_ == 0)
{
v___y_4423_ = v___y_4513_;
v___y_4424_ = v___y_4514_;
v___y_4425_ = v___y_4515_;
v_exportedInfo_x3f_4426_ = v___x_4510_;
v___y_4427_ = v___y_4516_;
v___y_4428_ = v___y_4517_;
goto v___jp_4422_;
}
else
{
lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4533_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__4, &l_Lean_addDecl___lam__8___closed__4_once, _init_l_Lean_addDecl___lam__8___closed__4);
v___x_4534_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3766_, v___x_4533_, v___y_4516_, v___y_4517_);
if (lean_obj_tag(v___x_4534_) == 0)
{
lean_dec_ref(v___x_4534_);
v___y_4423_ = v___y_4513_;
v___y_4424_ = v___y_4514_;
v___y_4425_ = v___y_4515_;
v_exportedInfo_x3f_4426_ = v___x_4510_;
v___y_4427_ = v___y_4516_;
v___y_4428_ = v___y_4517_;
goto v___jp_4422_;
}
else
{
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
lean_dec_ref(v___y_4515_);
lean_dec(v___y_4513_);
lean_dec(v_decl_3571_);
return v___x_4534_;
}
}
}
else
{
lean_object* v___x_4535_; lean_object* v_a_4536_; uint8_t v___x_4537_; 
v___x_4535_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_3766_, v___y_4516_);
v_a_4536_ = lean_ctor_get(v___x_4535_, 0);
lean_inc(v_a_4536_);
lean_dec_ref(v___x_4535_);
v___x_4537_ = lean_unbox(v_a_4536_);
lean_dec(v_a_4536_);
if (v___x_4537_ == 0)
{
v___y_4445_ = v___y_4514_;
v___y_4446_ = v___y_4513_;
v___y_4447_ = v___y_4515_;
v___y_4448_ = v___y_4516_;
v___y_4449_ = v___y_4517_;
goto v___jp_4444_;
}
else
{
lean_object* v___x_4538_; lean_object* v___x_4539_; 
v___x_4538_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__6, &l_Lean_addDecl___lam__8___closed__6_once, _init_l_Lean_addDecl___lam__8___closed__6);
v___x_4539_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3766_, v___x_4538_, v___y_4516_, v___y_4517_);
if (lean_obj_tag(v___x_4539_) == 0)
{
lean_dec_ref(v___x_4539_);
v___y_4445_ = v___y_4514_;
v___y_4446_ = v___y_4513_;
v___y_4447_ = v___y_4515_;
v___y_4448_ = v___y_4516_;
v___y_4449_ = v___y_4517_;
goto v___jp_4444_;
}
else
{
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
lean_dec_ref(v___y_4515_);
lean_dec(v___y_4513_);
lean_dec(v_decl_3571_);
return v___x_4539_;
}
}
}
}
}
v___jp_4540_:
{
lean_object* v___x_4547_; lean_object* v_env_4548_; uint8_t v___x_4549_; 
v___x_4547_ = lean_st_ref_get(v___y_4546_);
v_env_4548_ = lean_ctor_get(v___x_4547_, 0);
lean_inc_ref(v_env_4548_);
lean_dec(v___x_4547_);
v___x_4549_ = l_Lean_Environment_containsOnBranch(v_env_4548_, v_fst_4541_);
if (v___x_4549_ == 0)
{
v___y_4512_ = v_exportedInfo_x3f_4544_;
v___y_4513_ = v_fst_4541_;
v___y_4514_ = v_snd_4543_;
v___y_4515_ = v_fst_4542_;
v___y_4516_ = v___y_4545_;
v___y_4517_ = v___y_4546_;
goto v___jp_4511_;
}
else
{
lean_object* v___x_4550_; lean_object* v_env_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; 
lean_dec(v_exportedInfo_x3f_4544_);
lean_dec_ref(v_fst_4542_);
lean_dec(v_decl_3571_);
v___x_4550_ = lean_st_ref_get(v___y_4546_);
v_env_4551_ = lean_ctor_get(v___x_4550_, 0);
lean_inc_ref(v_env_4551_);
lean_dec(v___x_4550_);
v___x_4552_ = lean_elab_environment_to_kernel_env(v_env_4551_);
v___x_4553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4553_, 0, v___x_4552_);
lean_ctor_set(v___x_4553_, 1, v_fst_4541_);
v___x_4554_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(v___x_4553_, v___y_4545_, v___y_4546_);
lean_dec(v___y_4546_);
return v___x_4554_;
}
}
v___jp_4555_:
{
lean_object* v_name_4561_; lean_object* v___x_4562_; uint8_t v___x_4563_; 
v_name_4561_ = lean_ctor_get(v_toConstantVal_4557_, 0);
lean_inc(v_name_4561_);
lean_dec_ref(v_toConstantVal_4557_);
v___x_4562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4562_, 0, v___y_4556_);
v___x_4563_ = 0;
v_fst_4541_ = v_name_4561_;
v_fst_4542_ = v___x_4562_;
v_snd_4543_ = v___x_4563_;
v_exportedInfo_x3f_4544_ = v_exportedInfo_x3f_4558_;
v___y_4545_ = v___y_4559_;
v___y_4546_ = v___y_4560_;
goto v___jp_4540_;
}
v___jp_4564_:
{
uint8_t v___x_4570_; uint8_t v___x_4571_; lean_object* v___x_4573_; 
v___x_4570_ = 0;
v___x_4571_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4567_, v___x_4570_);
lean_inc_ref(v_toConstantVal_4566_);
if (v_isShared_4453_ == 0)
{
lean_ctor_set(v___x_4452_, 0, v_toConstantVal_4566_);
v___x_4573_ = v___x_4452_;
goto v_reusejp_4572_;
}
else
{
lean_object* v_reuseFailAlloc_4576_; 
v_reuseFailAlloc_4576_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4576_, 0, v_toConstantVal_4566_);
v___x_4573_ = v_reuseFailAlloc_4576_;
goto v_reusejp_4572_;
}
v_reusejp_4572_:
{
lean_object* v___x_4574_; lean_object* v___x_4575_; 
lean_ctor_set_uint8(v___x_4573_, sizeof(void*)*1, v___x_4571_);
v___x_4574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4574_, 0, v___x_4573_);
v___x_4575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4575_, 0, v___x_4574_);
v___y_4556_ = v___y_4565_;
v_toConstantVal_4557_ = v_toConstantVal_4566_;
v_exportedInfo_x3f_4558_ = v___x_4575_;
v___y_4559_ = v___y_4568_;
v___y_4560_ = v___y_4569_;
goto v___jp_4555_;
}
}
v___jp_4577_:
{
lean_object* v___x_4581_; lean_object* v_a_4582_; uint8_t v___x_4583_; 
v___x_4581_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_3766_, v___y_4579_);
v_a_4582_ = lean_ctor_get(v___x_4581_, 0);
lean_inc(v_a_4582_);
lean_dec_ref(v___x_4581_);
v___x_4583_ = lean_unbox(v_a_4582_);
lean_dec(v_a_4582_);
if (v___x_4583_ == 0)
{
lean_object* v_toConstantVal_4584_; uint8_t v_safety_4585_; 
v_toConstantVal_4584_ = lean_ctor_get(v___y_4578_, 0);
lean_inc_ref(v_toConstantVal_4584_);
v_safety_4585_ = lean_ctor_get_uint8(v___y_4578_, sizeof(void*)*4);
v___y_4565_ = v___y_4578_;
v_toConstantVal_4566_ = v_toConstantVal_4584_;
v_safety_4567_ = v_safety_4585_;
v___y_4568_ = v___y_4579_;
v___y_4569_ = v___y_4580_;
goto v___jp_4564_;
}
else
{
lean_object* v_toConstantVal_4586_; uint8_t v_safety_4587_; lean_object* v_name_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; 
v_toConstantVal_4586_ = lean_ctor_get(v___y_4578_, 0);
lean_inc_ref(v_toConstantVal_4586_);
v_safety_4587_ = lean_ctor_get_uint8(v___y_4578_, sizeof(void*)*4);
v_name_4588_ = lean_ctor_get(v_toConstantVal_4586_, 0);
v___x_4589_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__1, &l_Lean_addDecl___lam__4___closed__1_once, _init_l_Lean_addDecl___lam__4___closed__1);
lean_inc(v_name_4588_);
v___x_4590_ = l_Lean_MessageData_ofName(v_name_4588_);
v___x_4591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4591_, 0, v___x_4589_);
lean_ctor_set(v___x_4591_, 1, v___x_4590_);
v___x_4592_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_4593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4593_, 0, v___x_4591_);
lean_ctor_set(v___x_4593_, 1, v___x_4592_);
v___x_4594_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3766_, v___x_4593_, v___y_4579_, v___y_4580_);
if (lean_obj_tag(v___x_4594_) == 0)
{
lean_dec_ref(v___x_4594_);
v___y_4565_ = v___y_4578_;
v_toConstantVal_4566_ = v_toConstantVal_4586_;
v_safety_4567_ = v_safety_4587_;
v___y_4568_ = v___y_4579_;
v___y_4569_ = v___y_4580_;
goto v___jp_4564_;
}
else
{
lean_dec_ref(v_toConstantVal_4586_);
lean_dec(v___y_4580_);
lean_dec_ref(v___y_4579_);
lean_dec_ref(v___y_4578_);
lean_del_object(v___x_4452_);
lean_dec(v_decl_3571_);
return v___x_4594_;
}
}
}
v___jp_4595_:
{
lean_object* v_toConstantVal_4600_; 
v_toConstantVal_4600_ = lean_ctor_get(v___y_4596_, 0);
lean_inc_ref(v_toConstantVal_4600_);
v___y_4556_ = v___y_4596_;
v_toConstantVal_4557_ = v_toConstantVal_4600_;
v_exportedInfo_x3f_4558_ = v_exportedInfo_x3f_4597_;
v___y_4559_ = v___y_4598_;
v___y_4560_ = v___y_4599_;
goto v___jp_4555_;
}
v___jp_4601_:
{
lean_object* v___x_4607_; uint8_t v_isModule_4608_; 
v___x_4607_ = l_Lean_Environment_header(v___y_4606_);
lean_dec_ref(v___y_4606_);
v_isModule_4608_ = lean_ctor_get_uint8(v___x_4607_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4607_);
if (v_isModule_4608_ == 0)
{
lean_dec_ref(v___y_4605_);
lean_del_object(v___x_4452_);
v___y_4596_ = v___y_4602_;
v_exportedInfo_x3f_4597_ = v___x_4510_;
v___y_4598_ = v___y_4603_;
v___y_4599_ = v___y_4604_;
goto v___jp_4595_;
}
else
{
uint8_t v_isExporting_4609_; 
v_isExporting_4609_ = lean_ctor_get_uint8(v___y_4605_, sizeof(void*)*8);
lean_dec_ref(v___y_4605_);
if (v_isExporting_4609_ == 0)
{
v___y_4578_ = v___y_4602_;
v___y_4579_ = v___y_4603_;
v___y_4580_ = v___y_4604_;
goto v___jp_4577_;
}
else
{
if (v___x_4317_ == 0)
{
lean_del_object(v___x_4452_);
v___y_4596_ = v___y_4602_;
v_exportedInfo_x3f_4597_ = v___x_4510_;
v___y_4598_ = v___y_4603_;
v___y_4599_ = v___y_4604_;
goto v___jp_4595_;
}
else
{
v___y_4578_ = v___y_4602_;
v___y_4579_ = v___y_4603_;
v___y_4580_ = v___y_4604_;
goto v___jp_4577_;
}
}
}
}
v___jp_4610_:
{
lean_object* v___x_4614_; lean_object* v___x_4615_; 
v___x_4614_ = lean_st_ref_get(v___y_4613_);
v___x_4615_ = lean_st_ref_get(v___y_4613_);
if (v_forceExpose_3572_ == 0)
{
lean_object* v_env_4616_; lean_object* v_env_4617_; 
v_env_4616_ = lean_ctor_get(v___x_4614_, 0);
lean_inc_ref(v_env_4616_);
lean_dec(v___x_4614_);
v_env_4617_ = lean_ctor_get(v___x_4615_, 0);
lean_inc_ref(v_env_4617_);
lean_dec(v___x_4615_);
v___y_4602_ = v_defn_4611_;
v___y_4603_ = v___y_4612_;
v___y_4604_ = v___y_4613_;
v___y_4605_ = v_env_4617_;
v___y_4606_ = v_env_4616_;
goto v___jp_4601_;
}
else
{
if (v___x_4317_ == 0)
{
lean_dec(v___x_4615_);
lean_dec(v___x_4614_);
lean_del_object(v___x_4452_);
v___y_4596_ = v_defn_4611_;
v_exportedInfo_x3f_4597_ = v___x_4510_;
v___y_4598_ = v___y_4612_;
v___y_4599_ = v___y_4613_;
goto v___jp_4595_;
}
else
{
lean_object* v_env_4618_; lean_object* v_env_4619_; 
v_env_4618_ = lean_ctor_get(v___x_4614_, 0);
lean_inc_ref(v_env_4618_);
lean_dec(v___x_4614_);
v_env_4619_ = lean_ctor_get(v___x_4615_, 0);
lean_inc_ref(v_env_4619_);
lean_dec(v___x_4615_);
v___y_4602_ = v_defn_4611_;
v___y_4603_ = v___y_4612_;
v___y_4604_ = v___y_4613_;
v___y_4605_ = v_env_4619_;
v___y_4606_ = v_env_4618_;
goto v___jp_4601_;
}
}
}
}
}
}
}
else
{
goto v___jp_4157_;
}
v___jp_4318_:
{
lean_object* v___x_4329_; 
lean_inc_ref(v___y_4324_);
v___x_4329_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_4320_, v___y_4324_, v___y_4327_, v___y_4328_);
if (lean_obj_tag(v___x_4329_) == 0)
{
lean_object* v___x_4330_; lean_object* v___x_4332_; uint8_t v_isShared_4333_; uint8_t v_isSharedCheck_4376_; 
lean_dec_ref(v___x_4329_);
lean_inc_ref(v___y_4326_);
v___x_4330_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_4326_, v___y_4322_);
v_isSharedCheck_4376_ = !lean_is_exclusive(v___x_4330_);
if (v_isSharedCheck_4376_ == 0)
{
lean_object* v_unused_4377_; 
v_unused_4377_ = lean_ctor_get(v___x_4330_, 0);
lean_dec(v_unused_4377_);
v___x_4332_ = v___x_4330_;
v_isShared_4333_ = v_isSharedCheck_4376_;
goto v_resetjp_4331_;
}
else
{
lean_dec(v___x_4330_);
v___x_4332_ = lean_box(0);
v_isShared_4333_ = v_isSharedCheck_4376_;
goto v_resetjp_4331_;
}
v_resetjp_4331_:
{
lean_object* v_options_4334_; lean_object* v___x_4335_; uint8_t v___x_4336_; 
v_options_4334_ = lean_ctor_get(v___y_4321_, 2);
v___x_4335_ = l_Lean_Elab_async;
v___x_4336_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_4334_, v___x_4335_);
if (v___x_4336_ == 0)
{
lean_object* v___x_4337_; lean_object* v_r_4338_; 
lean_del_object(v___x_4332_);
lean_dec_ref(v___y_4325_);
lean_dec_ref(v___y_4319_);
v___x_4337_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_4324_, v___y_4322_);
lean_dec_ref(v___x_4337_);
lean_inc(v___y_4322_);
v_r_4338_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3571_, v___y_4321_, v___y_4322_);
if (lean_obj_tag(v_r_4338_) == 0)
{
lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4348_; 
v_a_4339_ = lean_ctor_get(v_r_4338_, 0);
v_isSharedCheck_4348_ = !lean_is_exclusive(v_r_4338_);
if (v_isSharedCheck_4348_ == 0)
{
v___x_4341_ = v_r_4338_;
v_isShared_4342_ = v_isSharedCheck_4348_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v_r_4338_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4348_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4344_; 
lean_inc(v_a_4339_);
if (v_isShared_4342_ == 0)
{
lean_ctor_set_tag(v___x_4341_, 1);
v___x_4344_ = v___x_4341_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4347_; 
v_reuseFailAlloc_4347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4347_, 0, v_a_4339_);
v___x_4344_ = v_reuseFailAlloc_4347_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
lean_object* v___x_4345_; 
v___x_4345_ = lean_apply_2(v___y_4323_, v___x_4344_, lean_box(0));
if (lean_obj_tag(v___x_4345_) == 0)
{
lean_dec_ref(v___x_4345_);
v___y_3590_ = v___y_4322_;
v___y_3591_ = v___y_4326_;
v_a_3592_ = v_a_4339_;
goto v___jp_3589_;
}
else
{
lean_object* v_a_4346_; 
lean_dec(v_a_4339_);
v_a_4346_ = lean_ctor_get(v___x_4345_, 0);
lean_inc(v_a_4346_);
lean_dec_ref(v___x_4345_);
v___y_3577_ = v___y_4322_;
v___y_3578_ = v___y_4326_;
v_a_3579_ = v_a_4346_;
goto v___jp_3576_;
}
}
}
}
else
{
lean_object* v_a_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; 
v_a_4349_ = lean_ctor_get(v_r_4338_, 0);
lean_inc(v_a_4349_);
lean_dec_ref(v_r_4338_);
v___x_4350_ = lean_box(0);
v___x_4351_ = lean_apply_2(v___y_4323_, v___x_4350_, lean_box(0));
if (lean_obj_tag(v___x_4351_) == 0)
{
lean_dec_ref(v___x_4351_);
v___y_3577_ = v___y_4322_;
v___y_3578_ = v___y_4326_;
v_a_3579_ = v_a_4349_;
goto v___jp_3576_;
}
else
{
lean_object* v_a_4352_; 
lean_dec(v_a_4349_);
v_a_4352_ = lean_ctor_get(v___x_4351_, 0);
lean_inc(v_a_4352_);
lean_dec_ref(v___x_4351_);
v___y_3577_ = v___y_4322_;
v___y_3578_ = v___y_4326_;
v_a_3579_ = v_a_4352_;
goto v___jp_3576_;
}
}
}
else
{
lean_object* v___x_4353_; lean_object* v___x_4355_; 
lean_dec_ref(v___y_4326_);
lean_dec_ref(v___y_4324_);
lean_dec_ref(v___y_4323_);
lean_dec(v_decl_3571_);
v___x_4353_ = l_IO_CancelToken_new();
if (v_isShared_4333_ == 0)
{
lean_ctor_set_tag(v___x_4332_, 1);
lean_ctor_set(v___x_4332_, 0, v___x_4353_);
v___x_4355_ = v___x_4332_;
goto v_reusejp_4354_;
}
else
{
lean_object* v_reuseFailAlloc_4375_; 
v_reuseFailAlloc_4375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4375_, 0, v___x_4353_);
v___x_4355_ = v_reuseFailAlloc_4375_;
goto v_reusejp_4354_;
}
v_reusejp_4354_:
{
lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; 
v___x_4356_ = ((lean_object*)(l_Lean_addDecl___closed__0));
v___x_4357_ = l_Lean_Name_toString(v___x_4356_, v_hasTrace_3629_);
lean_inc_ref(v___x_4355_);
v___x_4358_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_4319_, v___x_4355_, v___x_4357_, v___y_4321_, v___y_4322_);
if (lean_obj_tag(v___x_4358_) == 0)
{
lean_object* v_a_4359_; lean_object* v_checked_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; 
v_a_4359_ = lean_ctor_get(v___x_4358_, 0);
lean_inc(v_a_4359_);
lean_dec_ref(v___x_4358_);
v_checked_4360_ = lean_ctor_get(v___y_4325_, 2);
lean_inc_ref(v_checked_4360_);
lean_dec_ref(v___y_4325_);
v___x_4361_ = lean_unsigned_to_nat(0u);
v___x_4362_ = lean_io_map_task(v_a_4359_, v_checked_4360_, v___x_4361_, v___x_4317_);
v___x_4363_ = lean_box(0);
v___x_4364_ = lean_box(2);
v___x_4365_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4365_, 0, v___x_4363_);
lean_ctor_set(v___x_4365_, 1, v___x_4364_);
lean_ctor_set(v___x_4365_, 2, v___x_4355_);
lean_ctor_set(v___x_4365_, 3, v___x_4362_);
v___x_4366_ = l_Lean_Core_logSnapshotTask___redArg(v___x_4365_, v___y_4322_);
lean_dec(v___y_4322_);
return v___x_4366_;
}
else
{
lean_object* v_a_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4374_; 
lean_dec_ref(v___x_4355_);
lean_dec_ref(v___y_4325_);
lean_dec(v___y_4322_);
v_a_4367_ = lean_ctor_get(v___x_4358_, 0);
v_isSharedCheck_4374_ = !lean_is_exclusive(v___x_4358_);
if (v_isSharedCheck_4374_ == 0)
{
v___x_4369_ = v___x_4358_;
v_isShared_4370_ = v_isSharedCheck_4374_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_a_4367_);
lean_dec(v___x_4358_);
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
}
}
}
else
{
lean_object* v_a_4378_; lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4390_; 
lean_dec_ref(v___y_4326_);
lean_dec_ref(v___y_4325_);
lean_dec_ref(v___y_4324_);
lean_dec_ref(v___y_4323_);
lean_dec(v___y_4322_);
lean_dec_ref(v___y_4319_);
lean_dec(v_decl_3571_);
v_a_4378_ = lean_ctor_get(v___x_4329_, 0);
v_isSharedCheck_4390_ = !lean_is_exclusive(v___x_4329_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4380_ = v___x_4329_;
v_isShared_4381_ = v_isSharedCheck_4390_;
goto v_resetjp_4379_;
}
else
{
lean_inc(v_a_4378_);
lean_dec(v___x_4329_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4390_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
lean_object* v_ref_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4388_; 
v_ref_4382_ = lean_ctor_get(v___y_4321_, 5);
lean_inc(v_ref_4382_);
lean_dec_ref(v___y_4321_);
v___x_4383_ = lean_io_error_to_string(v_a_4378_);
v___x_4384_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4384_, 0, v___x_4383_);
v___x_4385_ = l_Lean_MessageData_ofFormat(v___x_4384_);
v___x_4386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4386_, 0, v_ref_4382_);
lean_ctor_set(v___x_4386_, 1, v___x_4385_);
if (v_isShared_4381_ == 0)
{
lean_ctor_set(v___x_4380_, 0, v___x_4386_);
v___x_4388_ = v___x_4380_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v___x_4386_);
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
v___jp_4391_:
{
lean_object* v___x_4402_; 
lean_inc_ref(v___y_4394_);
v___x_4402_ = l_Lean_Environment_addConstAsync(v___y_4394_, v___y_4399_, v___y_4398_, v___y_4401_, v___x_4317_, v_hasTrace_3629_);
if (lean_obj_tag(v___x_4402_) == 0)
{
lean_object* v_a_4403_; lean_object* v_mainEnv_4404_; lean_object* v_asyncEnv_4405_; lean_object* v___f_4406_; lean_object* v___f_4407_; lean_object* v___x_4408_; 
v_a_4403_ = lean_ctor_get(v___x_4402_, 0);
lean_inc(v_a_4403_);
lean_dec_ref(v___x_4402_);
v_mainEnv_4404_ = lean_ctor_get(v_a_4403_, 0);
lean_inc_ref(v_mainEnv_4404_);
v_asyncEnv_4405_ = lean_ctor_get(v_a_4403_, 1);
lean_inc_ref(v_asyncEnv_4405_);
lean_inc(v_a_4403_);
v___f_4406_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4406_, 0, v___y_4393_);
lean_closure_set(v___f_4406_, 1, v_a_4403_);
lean_closure_set(v___f_4406_, 2, v___y_4392_);
lean_inc(v_decl_3571_);
lean_inc(v_a_4403_);
lean_inc_ref(v_asyncEnv_4405_);
v___f_4407_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4407_, 0, v_asyncEnv_4405_);
lean_closure_set(v___f_4407_, 1, v_a_4403_);
lean_closure_set(v___f_4407_, 2, v_decl_3571_);
v___x_4408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4408_, 0, v___y_4400_);
if (lean_obj_tag(v___y_4395_) == 0)
{
lean_inc_ref(v___x_4408_);
v___y_4319_ = v___f_4407_;
v___y_4320_ = v_a_4403_;
v___y_4321_ = v___y_4396_;
v___y_4322_ = v___y_4397_;
v___y_4323_ = v___f_4406_;
v___y_4324_ = v_asyncEnv_4405_;
v___y_4325_ = v___y_4394_;
v___y_4326_ = v_mainEnv_4404_;
v___y_4327_ = v___x_4408_;
v___y_4328_ = v___x_4408_;
goto v___jp_4318_;
}
else
{
v___y_4319_ = v___f_4407_;
v___y_4320_ = v_a_4403_;
v___y_4321_ = v___y_4396_;
v___y_4322_ = v___y_4397_;
v___y_4323_ = v___f_4406_;
v___y_4324_ = v_asyncEnv_4405_;
v___y_4325_ = v___y_4394_;
v___y_4326_ = v_mainEnv_4404_;
v___y_4327_ = v___x_4408_;
v___y_4328_ = v___y_4395_;
goto v___jp_4318_;
}
}
else
{
lean_object* v_a_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4421_; 
lean_dec_ref(v___y_4400_);
lean_dec(v___y_4397_);
lean_dec(v___y_4395_);
lean_dec_ref(v___y_4394_);
lean_dec(v___y_4393_);
lean_dec_ref(v___y_4392_);
lean_dec(v_decl_3571_);
v_a_4409_ = lean_ctor_get(v___x_4402_, 0);
v_isSharedCheck_4421_ = !lean_is_exclusive(v___x_4402_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4411_ = v___x_4402_;
v_isShared_4412_ = v_isSharedCheck_4421_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_a_4409_);
lean_dec(v___x_4402_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4421_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v_ref_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4419_; 
v_ref_4413_ = lean_ctor_get(v___y_4396_, 5);
lean_inc(v_ref_4413_);
lean_dec_ref(v___y_4396_);
v___x_4414_ = lean_io_error_to_string(v_a_4409_);
v___x_4415_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4415_, 0, v___x_4414_);
v___x_4416_ = l_Lean_MessageData_ofFormat(v___x_4415_);
v___x_4417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4417_, 0, v_ref_4413_);
lean_ctor_set(v___x_4417_, 1, v___x_4416_);
if (v_isShared_4412_ == 0)
{
lean_ctor_set(v___x_4411_, 0, v___x_4417_);
v___x_4419_ = v___x_4411_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v___x_4417_);
v___x_4419_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
return v___x_4419_;
}
}
}
}
v___jp_4422_:
{
lean_object* v___x_4429_; 
v___x_4429_ = lean_st_ref_get(v___y_4428_);
if (lean_obj_tag(v_exportedInfo_x3f_4426_) == 0)
{
lean_object* v_env_4430_; lean_object* v___x_4431_; 
v_env_4430_ = lean_ctor_get(v___x_4429_, 0);
lean_inc_ref(v_env_4430_);
lean_dec(v___x_4429_);
v___x_4431_ = lean_box(0);
lean_inc(v___y_4428_);
lean_inc_ref(v___y_4427_);
v___y_4392_ = v___y_4427_;
v___y_4393_ = v___y_4428_;
v___y_4394_ = v_env_4430_;
v___y_4395_ = v_exportedInfo_x3f_4426_;
v___y_4396_ = v___y_4427_;
v___y_4397_ = v___y_4428_;
v___y_4398_ = v___y_4424_;
v___y_4399_ = v___y_4423_;
v___y_4400_ = v___y_4425_;
v___y_4401_ = v___x_4431_;
goto v___jp_4391_;
}
else
{
lean_object* v_env_4432_; lean_object* v_val_4433_; uint8_t v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; 
v_env_4432_ = lean_ctor_get(v___x_4429_, 0);
lean_inc_ref(v_env_4432_);
lean_dec(v___x_4429_);
v_val_4433_ = lean_ctor_get(v_exportedInfo_x3f_4426_, 0);
v___x_4434_ = l_Lean_ConstantKind_ofConstantInfo(v_val_4433_);
v___x_4435_ = lean_box(v___x_4434_);
v___x_4436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4436_, 0, v___x_4435_);
lean_inc(v___y_4428_);
lean_inc_ref(v___y_4427_);
v___y_4392_ = v___y_4427_;
v___y_4393_ = v___y_4428_;
v___y_4394_ = v_env_4432_;
v___y_4395_ = v_exportedInfo_x3f_4426_;
v___y_4396_ = v___y_4427_;
v___y_4397_ = v___y_4428_;
v___y_4398_ = v___y_4424_;
v___y_4399_ = v___y_4423_;
v___y_4400_ = v___y_4425_;
v___y_4401_ = v___x_4436_;
goto v___jp_4391_;
}
}
v___jp_4437_:
{
lean_object* v___x_4443_; 
lean_inc_ref(v___y_4440_);
v___x_4443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4443_, 0, v___y_4440_);
v___y_4423_ = v___y_4439_;
v___y_4424_ = v___y_4438_;
v___y_4425_ = v___y_4440_;
v_exportedInfo_x3f_4426_ = v___x_4443_;
v___y_4427_ = v___y_4441_;
v___y_4428_ = v___y_4442_;
goto v___jp_4422_;
}
v___jp_4444_:
{
lean_object* v___x_4450_; 
lean_inc_ref(v___y_4447_);
v___x_4450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4450_, 0, v___y_4447_);
v___y_4423_ = v___y_4446_;
v___y_4424_ = v___y_4445_;
v___y_4425_ = v___y_4447_;
v_exportedInfo_x3f_4426_ = v___x_4450_;
v___y_4427_ = v___y_4448_;
v___y_4428_ = v___y_4449_;
goto v___jp_4422_;
}
}
else
{
goto v___jp_4157_;
}
v___jp_4004_:
{
lean_object* v___x_4008_; double v___x_4009_; double v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; uint8_t v___x_4015_; lean_object* v___x_4016_; 
v___x_4008_ = lean_io_get_num_heartbeats();
v___x_4009_ = lean_float_of_nat(v___y_4006_);
v___x_4010_ = lean_float_of_nat(v___x_4008_);
v___x_4011_ = lean_box_float(v___x_4009_);
v___x_4012_ = lean_box_float(v___x_4010_);
v___x_4013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4013_, 0, v___x_4011_);
lean_ctor_set(v___x_4013_, 1, v___x_4012_);
v___x_4014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4014_, 0, v_a_4007_);
lean_ctor_set(v___x_4014_, 1, v___x_4013_);
v___x_4015_ = lean_unbox(v_a_3998_);
lean_dec(v_a_3998_);
v___x_4016_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3(v_cls_3766_, v_hasTrace_3629_, v___x_4003_, v_options_3628_, v___x_4015_, v___y_4005_, v___f_4002_, v___x_4014_, v_a_3573_, v_a_3574_);
lean_dec_ref(v_options_3628_);
return v___x_4016_;
}
v___jp_4017_:
{
lean_object* v___x_4022_; 
if (v_isShared_4001_ == 0)
{
lean_ctor_set(v___x_4000_, 0, v_a_4020_);
v___x_4022_ = v___x_4000_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v_a_4020_);
v___x_4022_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
v___y_4005_ = v___y_4018_;
v___y_4006_ = v___y_4019_;
v_a_4007_ = v___x_4022_;
goto v___jp_4004_;
}
}
v___jp_4024_:
{
if (lean_obj_tag(v___y_4027_) == 0)
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4035_; 
lean_del_object(v___x_4000_);
v_a_4028_ = lean_ctor_get(v___y_4027_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___y_4027_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4030_ = v___y_4027_;
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___y_4027_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4033_; 
if (v_isShared_4031_ == 0)
{
lean_ctor_set_tag(v___x_4030_, 1);
v___x_4033_ = v___x_4030_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_a_4028_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
v___y_4005_ = v___y_4025_;
v___y_4006_ = v___y_4026_;
v_a_4007_ = v___x_4033_;
goto v___jp_4004_;
}
}
}
else
{
lean_object* v_a_4036_; 
v_a_4036_ = lean_ctor_get(v___y_4027_, 0);
lean_inc(v_a_4036_);
lean_dec_ref(v___y_4027_);
v___y_4018_ = v___y_4025_;
v___y_4019_ = v___y_4026_;
v_a_4020_ = v_a_4036_;
goto v___jp_4017_;
}
}
v___jp_4037_:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; 
v___x_4042_ = lean_box(0);
lean_inc(v_a_3574_);
lean_inc_ref(v_a_3573_);
v___x_4043_ = lean_apply_5(v___y_4041_, v___x_4042_, v___y_4040_, v_a_3573_, v_a_3574_, lean_box(0));
v___y_4025_ = v___y_4038_;
v___y_4026_ = v___y_4039_;
v___y_4027_ = v___x_4043_;
goto v___jp_4024_;
}
v___jp_4044_:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___x_4049_ = lean_box(0);
lean_inc(v_a_3574_);
lean_inc_ref(v_a_3573_);
v___x_4050_ = lean_apply_5(v___y_4046_, v___x_4049_, v___y_4048_, v_a_3573_, v_a_3574_, lean_box(0));
v___y_4025_ = v___y_4045_;
v___y_4026_ = v___y_4047_;
v___y_4027_ = v___x_4050_;
goto v___jp_4024_;
}
v___jp_4051_:
{
lean_object* v___x_4055_; double v___x_4056_; double v___x_4057_; double v___x_4058_; double v___x_4059_; double v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; uint8_t v___x_4065_; lean_object* v___x_4066_; 
v___x_4055_ = lean_io_mono_nanos_now();
v___x_4056_ = lean_float_of_nat(v___y_4053_);
v___x_4057_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0, &l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0);
v___x_4058_ = lean_float_div(v___x_4056_, v___x_4057_);
v___x_4059_ = lean_float_of_nat(v___x_4055_);
v___x_4060_ = lean_float_div(v___x_4059_, v___x_4057_);
v___x_4061_ = lean_box_float(v___x_4058_);
v___x_4062_ = lean_box_float(v___x_4060_);
v___x_4063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4063_, 0, v___x_4061_);
lean_ctor_set(v___x_4063_, 1, v___x_4062_);
v___x_4064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4064_, 0, v_a_4054_);
lean_ctor_set(v___x_4064_, 1, v___x_4063_);
v___x_4065_ = lean_unbox(v_a_3998_);
lean_dec(v_a_3998_);
v___x_4066_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3(v_cls_3766_, v_hasTrace_3629_, v___x_4003_, v_options_3628_, v___x_4065_, v___y_4052_, v___f_4002_, v___x_4064_, v_a_3573_, v_a_3574_);
lean_dec_ref(v_options_3628_);
return v___x_4066_;
}
v___jp_4067_:
{
lean_object* v___x_4071_; 
v___x_4071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4071_, 0, v_a_4070_);
v___y_4052_ = v___y_4069_;
v___y_4053_ = v___y_4068_;
v_a_4054_ = v___x_4071_;
goto v___jp_4051_;
}
v___jp_4072_:
{
if (lean_obj_tag(v___y_4075_) == 0)
{
lean_object* v_a_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4083_; 
v_a_4076_ = lean_ctor_get(v___y_4075_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v___y_4075_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4078_ = v___y_4075_;
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_a_4076_);
lean_dec(v___y_4075_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4081_; 
if (v_isShared_4079_ == 0)
{
lean_ctor_set_tag(v___x_4078_, 1);
v___x_4081_ = v___x_4078_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_a_4076_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
v___y_4052_ = v___y_4074_;
v___y_4053_ = v___y_4073_;
v_a_4054_ = v___x_4081_;
goto v___jp_4051_;
}
}
}
else
{
lean_object* v_a_4084_; 
v_a_4084_ = lean_ctor_get(v___y_4075_, 0);
lean_inc(v_a_4084_);
lean_dec_ref(v___y_4075_);
v___y_4068_ = v___y_4073_;
v___y_4069_ = v___y_4074_;
v_a_4070_ = v_a_4084_;
goto v___jp_4067_;
}
}
v___jp_4085_:
{
lean_object* v___x_4090_; lean_object* v___x_4091_; 
v___x_4090_ = lean_box(0);
lean_inc(v_a_3574_);
lean_inc_ref(v_a_3573_);
v___x_4091_ = lean_apply_5(v___y_4088_, v___x_4090_, v___y_4089_, v_a_3573_, v_a_3574_, lean_box(0));
v___y_4073_ = v___y_4087_;
v___y_4074_ = v___y_4086_;
v___y_4075_ = v___x_4091_;
goto v___jp_4072_;
}
v___jp_4092_:
{
lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4097_ = lean_box(0);
lean_inc(v_a_3574_);
lean_inc_ref(v_a_3573_);
v___x_4098_ = lean_apply_5(v___y_4093_, v___x_4097_, v___y_4096_, v_a_3573_, v_a_3574_, lean_box(0));
v___y_4073_ = v___y_4095_;
v___y_4074_ = v___y_4094_;
v___y_4075_ = v___x_4098_;
goto v___jp_4072_;
}
v___jp_4099_:
{
lean_object* v___x_4104_; lean_object* v_a_4105_; uint8_t v___x_4106_; 
v___x_4104_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_3766_, v_a_3573_);
v_a_4105_ = lean_ctor_get(v___x_4104_, 0);
lean_inc(v_a_4105_);
lean_dec_ref(v___x_4104_);
v___x_4106_ = lean_unbox(v_a_4105_);
lean_dec(v_a_4105_);
if (v___x_4106_ == 0)
{
lean_object* v___x_4107_; lean_object* v___x_4108_; 
lean_dec_ref(v___y_4102_);
v___x_4107_ = lean_box(0);
lean_inc(v_a_3574_);
lean_inc_ref(v_a_3573_);
v___x_4108_ = lean_apply_4(v___y_4103_, v___x_4107_, v_a_3573_, v_a_3574_, lean_box(0));
v___y_4073_ = v___y_4101_;
v___y_4074_ = v___y_4100_;
v___y_4075_ = v___x_4108_;
goto v___jp_4072_;
}
else
{
lean_object* v_toConstantVal_4109_; lean_object* v_name_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; 
v_toConstantVal_4109_ = lean_ctor_get(v___y_4102_, 0);
lean_inc_ref(v_toConstantVal_4109_);
lean_dec_ref(v___y_4102_);
v_name_4110_ = lean_ctor_get(v_toConstantVal_4109_, 0);
lean_inc(v_name_4110_);
lean_dec_ref(v_toConstantVal_4109_);
v___x_4111_ = lean_obj_once(&l_Lean_addDecl___closed__4, &l_Lean_addDecl___closed__4_once, _init_l_Lean_addDecl___closed__4);
v___x_4112_ = l_Lean_MessageData_ofName(v_name_4110_);
v___x_4113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4111_);
lean_ctor_set(v___x_4113_, 1, v___x_4112_);
v___x_4114_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_4115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4113_);
lean_ctor_set(v___x_4115_, 1, v___x_4114_);
v___x_4116_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3766_, v___x_4115_, v_a_3573_, v_a_3574_);
if (lean_obj_tag(v___x_4116_) == 0)
{
lean_object* v_a_4117_; lean_object* v___x_4118_; 
v_a_4117_ = lean_ctor_get(v___x_4116_, 0);
lean_inc(v_a_4117_);
lean_dec_ref(v___x_4116_);
lean_inc(v_a_3574_);
lean_inc_ref(v_a_3573_);
v___x_4118_ = lean_apply_4(v___y_4103_, v_a_4117_, v_a_3573_, v_a_3574_, lean_box(0));
v___y_4073_ = v___y_4101_;
v___y_4074_ = v___y_4100_;
v___y_4075_ = v___x_4118_;
goto v___jp_4072_;
}
else
{
lean_dec_ref(v___y_4103_);
v___y_4073_ = v___y_4101_;
v___y_4074_ = v___y_4100_;
v___y_4075_ = v___x_4116_;
goto v___jp_4072_;
}
}
}
v___jp_4119_:
{
lean_object* v___x_4129_; uint8_t v_isModule_4130_; 
v___x_4129_ = l_Lean_Environment_header(v___y_4124_);
lean_dec_ref(v___y_4124_);
v_isModule_4130_ = lean_ctor_get_uint8(v___x_4129_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4129_);
if (v_isModule_4130_ == 0)
{
lean_dec_ref(v___y_4128_);
lean_dec_ref(v___y_4126_);
lean_dec_ref(v___y_4122_);
v___y_4086_ = v___y_4121_;
v___y_4087_ = v___y_4120_;
v___y_4088_ = v___y_4123_;
v___y_4089_ = v___y_4125_;
goto v___jp_4085_;
}
else
{
uint8_t v_isExporting_4131_; 
v_isExporting_4131_ = lean_ctor_get_uint8(v___y_4122_, sizeof(void*)*8);
lean_dec_ref(v___y_4122_);
if (v_isExporting_4131_ == 0)
{
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4123_);
v___y_4100_ = v___y_4121_;
v___y_4101_ = v___y_4120_;
v___y_4102_ = v___y_4126_;
v___y_4103_ = v___y_4128_;
goto v___jp_4099_;
}
else
{
if (v___y_4127_ == 0)
{
lean_dec_ref(v___y_4128_);
lean_dec_ref(v___y_4126_);
v___y_4086_ = v___y_4121_;
v___y_4087_ = v___y_4120_;
v___y_4088_ = v___y_4123_;
v___y_4089_ = v___y_4125_;
goto v___jp_4085_;
}
else
{
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4123_);
v___y_4100_ = v___y_4121_;
v___y_4101_ = v___y_4120_;
v___y_4102_ = v___y_4126_;
v___y_4103_ = v___y_4128_;
goto v___jp_4099_;
}
}
}
}
v___jp_4132_:
{
lean_object* v___x_4140_; uint8_t v_isModule_4141_; 
v___x_4140_ = l_Lean_Environment_header(v___y_4139_);
lean_dec_ref(v___y_4139_);
v_isModule_4141_ = lean_ctor_get_uint8(v___x_4140_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4140_);
if (v_isModule_4141_ == 0)
{
lean_dec_ref(v___y_4138_);
lean_dec_ref(v___y_4136_);
v___y_4093_ = v___y_4133_;
v___y_4094_ = v___y_4135_;
v___y_4095_ = v___y_4134_;
v___y_4096_ = v___y_4137_;
goto v___jp_4092_;
}
else
{
lean_object* v___x_4142_; lean_object* v_a_4143_; uint8_t v___x_4144_; 
lean_dec(v___y_4137_);
lean_dec_ref(v___y_4133_);
v___x_4142_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_3766_, v_a_3573_);
v_a_4143_ = lean_ctor_get(v___x_4142_, 0);
lean_inc(v_a_4143_);
lean_dec_ref(v___x_4142_);
v___x_4144_ = lean_unbox(v_a_4143_);
lean_dec(v_a_4143_);
if (v___x_4144_ == 0)
{
lean_object* v___x_4145_; lean_object* v___x_4146_; 
lean_dec_ref(v___y_4136_);
v___x_4145_ = lean_box(0);
lean_inc(v_a_3574_);
lean_inc_ref(v_a_3573_);
v___x_4146_ = lean_apply_4(v___y_4138_, v___x_4145_, v_a_3573_, v_a_3574_, lean_box(0));
v___y_4073_ = v___y_4134_;
v___y_4074_ = v___y_4135_;
v___y_4075_ = v___x_4146_;
goto v___jp_4072_;
}
else
{
lean_object* v_toConstantVal_4147_; lean_object* v_name_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; 
v_toConstantVal_4147_ = lean_ctor_get(v___y_4136_, 0);
lean_inc_ref(v_toConstantVal_4147_);
lean_dec_ref(v___y_4136_);
v_name_4148_ = lean_ctor_get(v_toConstantVal_4147_, 0);
lean_inc(v_name_4148_);
lean_dec_ref(v_toConstantVal_4147_);
v___x_4149_ = lean_obj_once(&l_Lean_addDecl___closed__2, &l_Lean_addDecl___closed__2_once, _init_l_Lean_addDecl___closed__2);
v___x_4150_ = l_Lean_MessageData_ofName(v_name_4148_);
v___x_4151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4149_);
lean_ctor_set(v___x_4151_, 1, v___x_4150_);
v___x_4152_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_4153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4153_, 0, v___x_4151_);
lean_ctor_set(v___x_4153_, 1, v___x_4152_);
v___x_4154_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3766_, v___x_4153_, v_a_3573_, v_a_3574_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_object* v_a_4155_; lean_object* v___x_4156_; 
v_a_4155_ = lean_ctor_get(v___x_4154_, 0);
lean_inc(v_a_4155_);
lean_dec_ref(v___x_4154_);
lean_inc(v_a_3574_);
lean_inc_ref(v_a_3573_);
v___x_4156_ = lean_apply_4(v___y_4138_, v_a_4155_, v_a_3573_, v_a_3574_, lean_box(0));
v___y_4073_ = v___y_4134_;
v___y_4074_ = v___y_4135_;
v___y_4075_ = v___x_4156_;
goto v___jp_4072_;
}
else
{
lean_dec_ref(v___y_4138_);
v___y_4073_ = v___y_4134_;
v___y_4074_ = v___y_4135_;
v___y_4075_ = v___x_4154_;
goto v___jp_4072_;
}
}
}
}
v___jp_4157_:
{
lean_object* v___x_4158_; lean_object* v_a_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4314_; 
v___x_4158_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___redArg(v_a_3574_);
v_a_4159_ = lean_ctor_get(v___x_4158_, 0);
v_isSharedCheck_4314_ = !lean_is_exclusive(v___x_4158_);
if (v_isSharedCheck_4314_ == 0)
{
v___x_4161_ = v___x_4158_;
v_isShared_4162_ = v_isSharedCheck_4314_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_a_4159_);
lean_dec(v___x_4158_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4314_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v___x_4163_; uint8_t v___x_4164_; 
v___x_4163_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4164_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3628_, v___x_4163_);
if (v___x_4164_ == 0)
{
lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v_env_4167_; lean_object* v_nextMacroScope_4168_; lean_object* v_ngen_4169_; lean_object* v_auxDeclNGen_4170_; lean_object* v_traceState_4171_; lean_object* v_messages_4172_; lean_object* v_infoState_4173_; lean_object* v_snapshotTasks_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4222_; 
lean_del_object(v___x_4000_);
v___x_4165_ = lean_io_mono_nanos_now();
v___x_4166_ = lean_st_ref_take(v_a_3574_);
v_env_4167_ = lean_ctor_get(v___x_4166_, 0);
v_nextMacroScope_4168_ = lean_ctor_get(v___x_4166_, 1);
v_ngen_4169_ = lean_ctor_get(v___x_4166_, 2);
v_auxDeclNGen_4170_ = lean_ctor_get(v___x_4166_, 3);
v_traceState_4171_ = lean_ctor_get(v___x_4166_, 4);
v_messages_4172_ = lean_ctor_get(v___x_4166_, 6);
v_infoState_4173_ = lean_ctor_get(v___x_4166_, 7);
v_snapshotTasks_4174_ = lean_ctor_get(v___x_4166_, 8);
v_isSharedCheck_4222_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4222_ == 0)
{
lean_object* v_unused_4223_; 
v_unused_4223_ = lean_ctor_get(v___x_4166_, 5);
lean_dec(v_unused_4223_);
v___x_4176_ = v___x_4166_;
v_isShared_4177_ = v_isSharedCheck_4222_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_snapshotTasks_4174_);
lean_inc(v_infoState_4173_);
lean_inc(v_messages_4172_);
lean_inc(v_traceState_4171_);
lean_inc(v_auxDeclNGen_4170_);
lean_inc(v_ngen_4169_);
lean_inc(v_nextMacroScope_4168_);
lean_inc(v_env_4167_);
lean_dec(v___x_4166_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4222_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4182_; 
lean_inc(v_decl_3571_);
v___x_4178_ = l_Lean_Declaration_getNames(v_decl_3571_);
v___x_4179_ = l_List_foldl___at___00Lean_addDecl_spec__1(v_env_4167_, v___x_4178_);
v___x_4180_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2);
if (v_isShared_4177_ == 0)
{
lean_ctor_set(v___x_4176_, 5, v___x_4180_);
lean_ctor_set(v___x_4176_, 0, v___x_4179_);
v___x_4182_ = v___x_4176_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v___x_4179_);
lean_ctor_set(v_reuseFailAlloc_4221_, 1, v_nextMacroScope_4168_);
lean_ctor_set(v_reuseFailAlloc_4221_, 2, v_ngen_4169_);
lean_ctor_set(v_reuseFailAlloc_4221_, 3, v_auxDeclNGen_4170_);
lean_ctor_set(v_reuseFailAlloc_4221_, 4, v_traceState_4171_);
lean_ctor_set(v_reuseFailAlloc_4221_, 5, v___x_4180_);
lean_ctor_set(v_reuseFailAlloc_4221_, 6, v_messages_4172_);
lean_ctor_set(v_reuseFailAlloc_4221_, 7, v_infoState_4173_);
lean_ctor_set(v_reuseFailAlloc_4221_, 8, v_snapshotTasks_4174_);
v___x_4182_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___f_4187_; 
v___x_4183_ = lean_st_ref_set(v_a_3574_, v___x_4182_);
v___x_4184_ = lean_box(0);
v___x_4185_ = lean_box(v_hasTrace_3629_);
v___x_4186_ = lean_box(v___x_4164_);
lean_inc(v_decl_3571_);
v___f_4187_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__8___boxed), 12, 7);
lean_closure_set(v___f_4187_, 0, v_decl_3571_);
lean_closure_set(v___f_4187_, 1, v___x_3630_);
lean_closure_set(v___f_4187_, 2, v___x_4185_);
lean_closure_set(v___f_4187_, 3, v___x_4186_);
lean_closure_set(v___f_4187_, 4, v___x_4180_);
lean_closure_set(v___f_4187_, 5, v_cls_3766_);
lean_closure_set(v___f_4187_, 6, v___x_4184_);
switch(lean_obj_tag(v_decl_3571_))
{
case 2:
{
lean_object* v_val_4188_; lean_object* v___x_4189_; lean_object* v_env_4190_; lean_object* v___f_4191_; lean_object* v___x_4192_; lean_object* v___f_4193_; 
lean_del_object(v___x_4161_);
v_val_4188_ = lean_ctor_get(v_decl_3571_, 0);
lean_inc_ref(v_val_4188_);
lean_dec_ref(v_decl_3571_);
v___x_4189_ = lean_st_ref_get(v_a_3574_);
v_env_4190_ = lean_ctor_get(v___x_4189_, 0);
lean_inc_ref(v_env_4190_);
lean_dec(v___x_4189_);
lean_inc_ref(v_val_4188_);
v___f_4191_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__5___boxed), 7, 2);
lean_closure_set(v___f_4191_, 0, v_val_4188_);
lean_closure_set(v___f_4191_, 1, v___f_4187_);
v___x_4192_ = lean_box(v___x_4164_);
lean_inc_ref(v___f_4191_);
lean_inc_ref(v_val_4188_);
v___f_4193_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__6___boxed), 7, 3);
lean_closure_set(v___f_4193_, 0, v_val_4188_);
lean_closure_set(v___f_4193_, 1, v___x_4192_);
lean_closure_set(v___f_4193_, 2, v___f_4191_);
if (v_forceExpose_3572_ == 0)
{
v___y_4133_ = v___f_4191_;
v___y_4134_ = v___x_4165_;
v___y_4135_ = v_a_4159_;
v___y_4136_ = v_val_4188_;
v___y_4137_ = v___x_4184_;
v___y_4138_ = v___f_4193_;
v___y_4139_ = v_env_4190_;
goto v___jp_4132_;
}
else
{
if (v___x_4164_ == 0)
{
lean_dec_ref(v___f_4193_);
lean_dec_ref(v_env_4190_);
lean_dec_ref(v_val_4188_);
v___y_4093_ = v___f_4191_;
v___y_4094_ = v_a_4159_;
v___y_4095_ = v___x_4165_;
v___y_4096_ = v___x_4184_;
goto v___jp_4092_;
}
else
{
v___y_4133_ = v___f_4191_;
v___y_4134_ = v___x_4165_;
v___y_4135_ = v_a_4159_;
v___y_4136_ = v_val_4188_;
v___y_4137_ = v___x_4184_;
v___y_4138_ = v___f_4193_;
v___y_4139_ = v_env_4190_;
goto v___jp_4132_;
}
}
}
case 1:
{
lean_object* v_val_4194_; lean_object* v___x_4195_; 
lean_del_object(v___x_4161_);
v_val_4194_ = lean_ctor_get(v_decl_3571_, 0);
lean_inc_ref(v_val_4194_);
lean_dec_ref(v_decl_3571_);
lean_inc(v_a_3574_);
lean_inc_ref(v_a_3573_);
v___x_4195_ = l_Lean_addDecl___lam__4(v___f_4187_, v_cls_3766_, v___x_4184_, v___x_4164_, v_forceExpose_3572_, v_val_4194_, v_a_3573_, v_a_3574_);
v___y_4073_ = v___x_4165_;
v___y_4074_ = v_a_4159_;
v___y_4075_ = v___x_4195_;
goto v___jp_4072_;
}
case 5:
{
lean_object* v_defns_4196_; 
lean_del_object(v___x_4161_);
v_defns_4196_ = lean_ctor_get(v_decl_3571_, 0);
if (lean_obj_tag(v_defns_4196_) == 1)
{
lean_object* v_tail_4197_; 
v_tail_4197_ = lean_ctor_get(v_defns_4196_, 1);
if (lean_obj_tag(v_tail_4197_) == 0)
{
lean_object* v_head_4198_; lean_object* v___x_4199_; 
lean_inc_ref(v_defns_4196_);
lean_dec_ref(v_decl_3571_);
v_head_4198_ = lean_ctor_get(v_defns_4196_, 0);
lean_inc(v_head_4198_);
lean_dec_ref(v_defns_4196_);
lean_inc(v_a_3574_);
lean_inc_ref(v_a_3573_);
v___x_4199_ = l_Lean_addDecl___lam__4(v___f_4187_, v_cls_3766_, v___x_4184_, v___x_4164_, v_forceExpose_3572_, v_head_4198_, v_a_3573_, v_a_3574_);
v___y_4073_ = v___x_4165_;
v___y_4074_ = v_a_4159_;
v___y_4075_ = v___x_4199_;
goto v___jp_4072_;
}
else
{
lean_object* v___x_4200_; 
lean_dec_ref(v___f_4187_);
lean_inc(v_a_3574_);
lean_inc_ref(v_a_3573_);
lean_inc_ref(v_decl_3571_);
v___x_4200_ = l_Lean_addDecl___lam__3(v_cls_3766_, v_decl_3571_, v_decl_3571_, v_a_3573_, v_a_3574_);
lean_dec_ref(v_decl_3571_);
v___y_4073_ = v___x_4165_;
v___y_4074_ = v_a_4159_;
v___y_4075_ = v___x_4200_;
goto v___jp_4072_;
}
}
else
{
lean_object* v___x_4201_; 
lean_dec_ref(v___f_4187_);
lean_inc(v_a_3574_);
lean_inc_ref(v_a_3573_);
lean_inc_ref(v_decl_3571_);
v___x_4201_ = l_Lean_addDecl___lam__3(v_cls_3766_, v_decl_3571_, v_decl_3571_, v_a_3573_, v_a_3574_);
lean_dec_ref(v_decl_3571_);
v___y_4073_ = v___x_4165_;
v___y_4074_ = v_a_4159_;
v___y_4075_ = v___x_4201_;
goto v___jp_4072_;
}
}
case 3:
{
lean_object* v_val_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v_env_4205_; lean_object* v_env_4206_; lean_object* v___f_4207_; lean_object* v___f_4208_; 
lean_del_object(v___x_4161_);
v_val_4202_ = lean_ctor_get(v_decl_3571_, 0);
lean_inc_ref(v_val_4202_);
lean_dec_ref(v_decl_3571_);
v___x_4203_ = lean_st_ref_get(v_a_3574_);
v___x_4204_ = lean_st_ref_get(v_a_3574_);
v_env_4205_ = lean_ctor_get(v___x_4203_, 0);
lean_inc_ref(v_env_4205_);
lean_dec(v___x_4203_);
v_env_4206_ = lean_ctor_get(v___x_4204_, 0);
lean_inc_ref(v_env_4206_);
lean_dec(v___x_4204_);
lean_inc_ref(v_val_4202_);
v___f_4207_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__7___boxed), 7, 2);
lean_closure_set(v___f_4207_, 0, v_val_4202_);
lean_closure_set(v___f_4207_, 1, v___f_4187_);
lean_inc_ref(v___f_4207_);
lean_inc_ref(v_val_4202_);
v___f_4208_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__9___boxed), 6, 2);
lean_closure_set(v___f_4208_, 0, v_val_4202_);
lean_closure_set(v___f_4208_, 1, v___f_4207_);
if (v_forceExpose_3572_ == 0)
{
v___y_4120_ = v___x_4165_;
v___y_4121_ = v_a_4159_;
v___y_4122_ = v_env_4206_;
v___y_4123_ = v___f_4207_;
v___y_4124_ = v_env_4205_;
v___y_4125_ = v___x_4184_;
v___y_4126_ = v_val_4202_;
v___y_4127_ = v___x_4164_;
v___y_4128_ = v___f_4208_;
goto v___jp_4119_;
}
else
{
if (v___x_4164_ == 0)
{
lean_dec_ref(v___f_4208_);
lean_dec_ref(v_env_4206_);
lean_dec_ref(v_env_4205_);
lean_dec_ref(v_val_4202_);
v___y_4086_ = v_a_4159_;
v___y_4087_ = v___x_4165_;
v___y_4088_ = v___f_4207_;
v___y_4089_ = v___x_4184_;
goto v___jp_4085_;
}
else
{
v___y_4120_ = v___x_4165_;
v___y_4121_ = v_a_4159_;
v___y_4122_ = v_env_4206_;
v___y_4123_ = v___f_4207_;
v___y_4124_ = v_env_4205_;
v___y_4125_ = v___x_4184_;
v___y_4126_ = v_val_4202_;
v___y_4127_ = v___x_4164_;
v___y_4128_ = v___f_4208_;
goto v___jp_4119_;
}
}
}
case 0:
{
lean_object* v_val_4209_; lean_object* v_toConstantVal_4210_; lean_object* v_name_4211_; lean_object* v___x_4213_; 
lean_dec_ref(v___f_4187_);
v_val_4209_ = lean_ctor_get(v_decl_3571_, 0);
v_toConstantVal_4210_ = lean_ctor_get(v_val_4209_, 0);
v_name_4211_ = lean_ctor_get(v_toConstantVal_4210_, 0);
lean_inc_ref(v_val_4209_);
if (v_isShared_4162_ == 0)
{
lean_ctor_set(v___x_4161_, 0, v_val_4209_);
v___x_4213_ = v___x_4161_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_val_4209_);
v___x_4213_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
uint8_t v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; 
v___x_4214_ = 2;
v___x_4215_ = lean_box(v___x_4214_);
v___x_4216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4216_, 0, v___x_4213_);
lean_ctor_set(v___x_4216_, 1, v___x_4215_);
lean_inc(v_name_4211_);
v___x_4217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4217_, 0, v_name_4211_);
lean_ctor_set(v___x_4217_, 1, v___x_4216_);
lean_inc(v_a_3574_);
lean_inc_ref(v_a_3573_);
v___x_4218_ = l_Lean_addDecl___lam__8(v_decl_3571_, v___x_3630_, v_hasTrace_3629_, v___x_4164_, v___x_4180_, v_cls_3766_, v___x_4184_, v___x_4217_, v___x_4184_, v_a_3573_, v_a_3574_);
v___y_4073_ = v___x_4165_;
v___y_4074_ = v_a_4159_;
v___y_4075_ = v___x_4218_;
goto v___jp_4072_;
}
}
default: 
{
lean_object* v___x_4220_; 
lean_dec_ref(v___f_4187_);
lean_del_object(v___x_4161_);
lean_inc(v_a_3574_);
lean_inc_ref(v_a_3573_);
lean_inc(v_decl_3571_);
v___x_4220_ = l_Lean_addDecl___lam__3(v_cls_3766_, v_decl_3571_, v_decl_3571_, v_a_3573_, v_a_3574_);
lean_dec(v_decl_3571_);
v___y_4073_ = v___x_4165_;
v___y_4074_ = v_a_4159_;
v___y_4075_ = v___x_4220_;
goto v___jp_4072_;
}
}
}
}
}
else
{
lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v_env_4226_; lean_object* v_nextMacroScope_4227_; lean_object* v_ngen_4228_; lean_object* v_auxDeclNGen_4229_; lean_object* v_traceState_4230_; lean_object* v_messages_4231_; lean_object* v_infoState_4232_; lean_object* v_snapshotTasks_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4312_; 
v___x_4224_ = lean_io_get_num_heartbeats();
v___x_4225_ = lean_st_ref_take(v_a_3574_);
v_env_4226_ = lean_ctor_get(v___x_4225_, 0);
v_nextMacroScope_4227_ = lean_ctor_get(v___x_4225_, 1);
v_ngen_4228_ = lean_ctor_get(v___x_4225_, 2);
v_auxDeclNGen_4229_ = lean_ctor_get(v___x_4225_, 3);
v_traceState_4230_ = lean_ctor_get(v___x_4225_, 4);
v_messages_4231_ = lean_ctor_get(v___x_4225_, 6);
v_infoState_4232_ = lean_ctor_get(v___x_4225_, 7);
v_snapshotTasks_4233_ = lean_ctor_get(v___x_4225_, 8);
v_isSharedCheck_4312_ = !lean_is_exclusive(v___x_4225_);
if (v_isSharedCheck_4312_ == 0)
{
lean_object* v_unused_4313_; 
v_unused_4313_ = lean_ctor_get(v___x_4225_, 5);
lean_dec(v_unused_4313_);
v___x_4235_ = v___x_4225_;
v_isShared_4236_ = v_isSharedCheck_4312_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_snapshotTasks_4233_);
lean_inc(v_infoState_4232_);
lean_inc(v_messages_4231_);
lean_inc(v_traceState_4230_);
lean_inc(v_auxDeclNGen_4229_);
lean_inc(v_ngen_4228_);
lean_inc(v_nextMacroScope_4227_);
lean_inc(v_env_4226_);
lean_dec(v___x_4225_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4312_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4241_; 
lean_inc(v_decl_3571_);
v___x_4237_ = l_Lean_Declaration_getNames(v_decl_3571_);
v___x_4238_ = l_List_foldl___at___00Lean_addDecl_spec__1(v_env_4226_, v___x_4237_);
v___x_4239_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2);
if (v_isShared_4236_ == 0)
{
lean_ctor_set(v___x_4235_, 5, v___x_4239_);
lean_ctor_set(v___x_4235_, 0, v___x_4238_);
v___x_4241_ = v___x_4235_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v___x_4238_);
lean_ctor_set(v_reuseFailAlloc_4311_, 1, v_nextMacroScope_4227_);
lean_ctor_set(v_reuseFailAlloc_4311_, 2, v_ngen_4228_);
lean_ctor_set(v_reuseFailAlloc_4311_, 3, v_auxDeclNGen_4229_);
lean_ctor_set(v_reuseFailAlloc_4311_, 4, v_traceState_4230_);
lean_ctor_set(v_reuseFailAlloc_4311_, 5, v___x_4239_);
lean_ctor_set(v_reuseFailAlloc_4311_, 6, v_messages_4231_);
lean_ctor_set(v_reuseFailAlloc_4311_, 7, v_infoState_4232_);
lean_ctor_set(v_reuseFailAlloc_4311_, 8, v_snapshotTasks_4233_);
v___x_4241_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___f_4245_; 
v___x_4242_ = lean_st_ref_set(v_a_3574_, v___x_4241_);
v___x_4243_ = lean_box(0);
v___x_4244_ = lean_box(v___x_4164_);
lean_inc(v_decl_3571_);
v___f_4245_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__13___boxed), 11, 6);
lean_closure_set(v___f_4245_, 0, v_decl_3571_);
lean_closure_set(v___f_4245_, 1, v___x_3630_);
lean_closure_set(v___f_4245_, 2, v___x_4244_);
lean_closure_set(v___f_4245_, 3, v_cls_3766_);
lean_closure_set(v___f_4245_, 4, v___x_4239_);
lean_closure_set(v___f_4245_, 5, v___x_4243_);
switch(lean_obj_tag(v_decl_3571_))
{
case 2:
{
lean_object* v_val_4246_; lean_object* v___x_4247_; lean_object* v_env_4248_; lean_object* v___f_4249_; 
lean_del_object(v___x_4161_);
v_val_4246_ = lean_ctor_get(v_decl_3571_, 0);
lean_inc_ref(v_val_4246_);
lean_dec_ref(v_decl_3571_);
v___x_4247_ = lean_st_ref_get(v_a_3574_);
v_env_4248_ = lean_ctor_get(v___x_4247_, 0);
lean_inc_ref(v_env_4248_);
lean_dec(v___x_4247_);
lean_inc_ref(v_val_4246_);
v___f_4249_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__5___boxed), 7, 2);
lean_closure_set(v___f_4249_, 0, v_val_4246_);
lean_closure_set(v___f_4249_, 1, v___f_4245_);
if (v_forceExpose_3572_ == 0)
{
if (v___x_4164_ == 0)
{
lean_dec_ref(v_env_4248_);
lean_dec_ref(v_val_4246_);
v___y_4038_ = v_a_4159_;
v___y_4039_ = v___x_4224_;
v___y_4040_ = v___x_4243_;
v___y_4041_ = v___f_4249_;
goto v___jp_4037_;
}
else
{
lean_object* v___x_4250_; uint8_t v_isModule_4251_; 
v___x_4250_ = l_Lean_Environment_header(v_env_4248_);
lean_dec_ref(v_env_4248_);
v_isModule_4251_ = lean_ctor_get_uint8(v___x_4250_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4250_);
if (v_isModule_4251_ == 0)
{
lean_dec_ref(v_val_4246_);
v___y_4038_ = v_a_4159_;
v___y_4039_ = v___x_4224_;
v___y_4040_ = v___x_4243_;
v___y_4041_ = v___f_4249_;
goto v___jp_4037_;
}
else
{
lean_object* v___x_4252_; lean_object* v_a_4253_; uint8_t v___x_4254_; 
v___x_4252_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_3766_, v_a_3573_);
v_a_4253_ = lean_ctor_get(v___x_4252_, 0);
lean_inc(v_a_4253_);
lean_dec_ref(v___x_4252_);
v___x_4254_ = lean_unbox(v_a_4253_);
lean_dec(v_a_4253_);
if (v___x_4254_ == 0)
{
lean_object* v___x_4255_; lean_object* v___x_4256_; 
v___x_4255_ = lean_box(0);
lean_inc(v_a_3574_);
lean_inc_ref(v_a_3573_);
v___x_4256_ = l_Lean_addDecl___lam__12(v_val_4246_, v_forceExpose_3572_, v___f_4249_, v___x_4255_, v_a_3573_, v_a_3574_);
lean_dec_ref(v_val_4246_);
v___y_4025_ = v_a_4159_;
v___y_4026_ = v___x_4224_;
v___y_4027_ = v___x_4256_;
goto v___jp_4024_;
}
else
{
lean_object* v_toConstantVal_4257_; lean_object* v_name_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
v_toConstantVal_4257_ = lean_ctor_get(v_val_4246_, 0);
v_name_4258_ = lean_ctor_get(v_toConstantVal_4257_, 0);
v___x_4259_ = lean_obj_once(&l_Lean_addDecl___closed__2, &l_Lean_addDecl___closed__2_once, _init_l_Lean_addDecl___closed__2);
lean_inc(v_name_4258_);
v___x_4260_ = l_Lean_MessageData_ofName(v_name_4258_);
v___x_4261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4261_, 0, v___x_4259_);
lean_ctor_set(v___x_4261_, 1, v___x_4260_);
v___x_4262_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_4263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4263_, 0, v___x_4261_);
lean_ctor_set(v___x_4263_, 1, v___x_4262_);
v___x_4264_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3766_, v___x_4263_, v_a_3573_, v_a_3574_);
if (lean_obj_tag(v___x_4264_) == 0)
{
lean_object* v_a_4265_; lean_object* v___x_4266_; 
v_a_4265_ = lean_ctor_get(v___x_4264_, 0);
lean_inc(v_a_4265_);
lean_dec_ref(v___x_4264_);
lean_inc(v_a_3574_);
lean_inc_ref(v_a_3573_);
v___x_4266_ = l_Lean_addDecl___lam__12(v_val_4246_, v_forceExpose_3572_, v___f_4249_, v_a_4265_, v_a_3573_, v_a_3574_);
lean_dec_ref(v_val_4246_);
v___y_4025_ = v_a_4159_;
v___y_4026_ = v___x_4224_;
v___y_4027_ = v___x_4266_;
goto v___jp_4024_;
}
else
{
lean_dec_ref(v___f_4249_);
lean_dec_ref(v_val_4246_);
v___y_4025_ = v_a_4159_;
v___y_4026_ = v___x_4224_;
v___y_4027_ = v___x_4264_;
goto v___jp_4024_;
}
}
}
}
}
else
{
lean_dec_ref(v_env_4248_);
lean_dec_ref(v_val_4246_);
v___y_4038_ = v_a_4159_;
v___y_4039_ = v___x_4224_;
v___y_4040_ = v___x_4243_;
v___y_4041_ = v___f_4249_;
goto v___jp_4037_;
}
}
case 1:
{
lean_object* v_val_4267_; lean_object* v___x_4268_; 
lean_del_object(v___x_4161_);
v_val_4267_ = lean_ctor_get(v_decl_3571_, 0);
lean_inc_ref(v_val_4267_);
lean_dec_ref(v_decl_3571_);
lean_inc(v_a_3574_);
lean_inc_ref(v_a_3573_);
v___x_4268_ = l_Lean_addDecl___lam__10(v___f_4245_, v_forceExpose_3572_, v___x_4164_, v___x_4243_, v_cls_3766_, v_val_4267_, v_a_3573_, v_a_3574_);
v___y_4025_ = v_a_4159_;
v___y_4026_ = v___x_4224_;
v___y_4027_ = v___x_4268_;
goto v___jp_4024_;
}
case 5:
{
lean_object* v_defns_4269_; 
lean_del_object(v___x_4161_);
v_defns_4269_ = lean_ctor_get(v_decl_3571_, 0);
if (lean_obj_tag(v_defns_4269_) == 1)
{
lean_object* v_tail_4270_; 
v_tail_4270_ = lean_ctor_get(v_defns_4269_, 1);
if (lean_obj_tag(v_tail_4270_) == 0)
{
lean_object* v_head_4271_; lean_object* v___x_4272_; 
lean_inc_ref(v_defns_4269_);
lean_dec_ref(v_decl_3571_);
v_head_4271_ = lean_ctor_get(v_defns_4269_, 0);
lean_inc(v_head_4271_);
lean_dec_ref(v_defns_4269_);
lean_inc(v_a_3574_);
lean_inc_ref(v_a_3573_);
v___x_4272_ = l_Lean_addDecl___lam__10(v___f_4245_, v_forceExpose_3572_, v___x_4164_, v___x_4243_, v_cls_3766_, v_head_4271_, v_a_3573_, v_a_3574_);
v___y_4025_ = v_a_4159_;
v___y_4026_ = v___x_4224_;
v___y_4027_ = v___x_4272_;
goto v___jp_4024_;
}
else
{
lean_object* v___x_4273_; 
lean_dec_ref(v___f_4245_);
lean_inc(v_a_3574_);
lean_inc_ref(v_a_3573_);
lean_inc_ref(v_decl_3571_);
v___x_4273_ = l_Lean_addDecl___lam__3(v_cls_3766_, v_decl_3571_, v_decl_3571_, v_a_3573_, v_a_3574_);
lean_dec_ref(v_decl_3571_);
v___y_4025_ = v_a_4159_;
v___y_4026_ = v___x_4224_;
v___y_4027_ = v___x_4273_;
goto v___jp_4024_;
}
}
else
{
lean_object* v___x_4274_; 
lean_dec_ref(v___f_4245_);
lean_inc(v_a_3574_);
lean_inc_ref(v_a_3573_);
lean_inc_ref(v_decl_3571_);
v___x_4274_ = l_Lean_addDecl___lam__3(v_cls_3766_, v_decl_3571_, v_decl_3571_, v_a_3573_, v_a_3574_);
lean_dec_ref(v_decl_3571_);
v___y_4025_ = v_a_4159_;
v___y_4026_ = v___x_4224_;
v___y_4027_ = v___x_4274_;
goto v___jp_4024_;
}
}
case 3:
{
lean_object* v_val_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v_env_4278_; lean_object* v_env_4279_; lean_object* v___f_4280_; 
lean_del_object(v___x_4161_);
v_val_4275_ = lean_ctor_get(v_decl_3571_, 0);
lean_inc_ref(v_val_4275_);
lean_dec_ref(v_decl_3571_);
v___x_4276_ = lean_st_ref_get(v_a_3574_);
v___x_4277_ = lean_st_ref_get(v_a_3574_);
v_env_4278_ = lean_ctor_get(v___x_4276_, 0);
lean_inc_ref(v_env_4278_);
lean_dec(v___x_4276_);
v_env_4279_ = lean_ctor_get(v___x_4277_, 0);
lean_inc_ref(v_env_4279_);
lean_dec(v___x_4277_);
lean_inc_ref(v_val_4275_);
v___f_4280_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__7___boxed), 7, 2);
lean_closure_set(v___f_4280_, 0, v_val_4275_);
lean_closure_set(v___f_4280_, 1, v___f_4245_);
if (v_forceExpose_3572_ == 0)
{
if (v___x_4164_ == 0)
{
lean_dec_ref(v_env_4279_);
lean_dec_ref(v_env_4278_);
lean_dec_ref(v_val_4275_);
v___y_4045_ = v_a_4159_;
v___y_4046_ = v___f_4280_;
v___y_4047_ = v___x_4224_;
v___y_4048_ = v___x_4243_;
goto v___jp_4044_;
}
else
{
lean_object* v___x_4281_; uint8_t v_isModule_4282_; 
v___x_4281_ = l_Lean_Environment_header(v_env_4278_);
lean_dec_ref(v_env_4278_);
v_isModule_4282_ = lean_ctor_get_uint8(v___x_4281_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4281_);
if (v_isModule_4282_ == 0)
{
lean_dec_ref(v_env_4279_);
lean_dec_ref(v_val_4275_);
v___y_4045_ = v_a_4159_;
v___y_4046_ = v___f_4280_;
v___y_4047_ = v___x_4224_;
v___y_4048_ = v___x_4243_;
goto v___jp_4044_;
}
else
{
uint8_t v_isExporting_4283_; 
v_isExporting_4283_ = lean_ctor_get_uint8(v_env_4279_, sizeof(void*)*8);
lean_dec_ref(v_env_4279_);
if (v_isExporting_4283_ == 0)
{
lean_object* v___x_4284_; lean_object* v_a_4285_; uint8_t v___x_4286_; 
v___x_4284_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_cls_3766_, v_a_3573_);
v_a_4285_ = lean_ctor_get(v___x_4284_, 0);
lean_inc(v_a_4285_);
lean_dec_ref(v___x_4284_);
v___x_4286_ = lean_unbox(v_a_4285_);
lean_dec(v_a_4285_);
if (v___x_4286_ == 0)
{
lean_object* v___x_4287_; lean_object* v___x_4288_; 
v___x_4287_ = lean_box(0);
lean_inc(v_a_3574_);
lean_inc_ref(v_a_3573_);
v___x_4288_ = l_Lean_addDecl___lam__9(v_val_4275_, v___f_4280_, v___x_4287_, v_a_3573_, v_a_3574_);
lean_dec_ref(v_val_4275_);
v___y_4025_ = v_a_4159_;
v___y_4026_ = v___x_4224_;
v___y_4027_ = v___x_4288_;
goto v___jp_4024_;
}
else
{
lean_object* v_toConstantVal_4289_; lean_object* v_name_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; 
v_toConstantVal_4289_ = lean_ctor_get(v_val_4275_, 0);
v_name_4290_ = lean_ctor_get(v_toConstantVal_4289_, 0);
v___x_4291_ = lean_obj_once(&l_Lean_addDecl___closed__4, &l_Lean_addDecl___closed__4_once, _init_l_Lean_addDecl___closed__4);
lean_inc(v_name_4290_);
v___x_4292_ = l_Lean_MessageData_ofName(v_name_4290_);
v___x_4293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4293_, 0, v___x_4291_);
lean_ctor_set(v___x_4293_, 1, v___x_4292_);
v___x_4294_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_4295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4295_, 0, v___x_4293_);
lean_ctor_set(v___x_4295_, 1, v___x_4294_);
v___x_4296_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3766_, v___x_4295_, v_a_3573_, v_a_3574_);
if (lean_obj_tag(v___x_4296_) == 0)
{
lean_object* v_a_4297_; lean_object* v___x_4298_; 
v_a_4297_ = lean_ctor_get(v___x_4296_, 0);
lean_inc(v_a_4297_);
lean_dec_ref(v___x_4296_);
lean_inc(v_a_3574_);
lean_inc_ref(v_a_3573_);
v___x_4298_ = l_Lean_addDecl___lam__9(v_val_4275_, v___f_4280_, v_a_4297_, v_a_3573_, v_a_3574_);
lean_dec_ref(v_val_4275_);
v___y_4025_ = v_a_4159_;
v___y_4026_ = v___x_4224_;
v___y_4027_ = v___x_4298_;
goto v___jp_4024_;
}
else
{
lean_dec_ref(v___f_4280_);
lean_dec_ref(v_val_4275_);
v___y_4025_ = v_a_4159_;
v___y_4026_ = v___x_4224_;
v___y_4027_ = v___x_4296_;
goto v___jp_4024_;
}
}
}
else
{
lean_dec_ref(v_val_4275_);
v___y_4045_ = v_a_4159_;
v___y_4046_ = v___f_4280_;
v___y_4047_ = v___x_4224_;
v___y_4048_ = v___x_4243_;
goto v___jp_4044_;
}
}
}
}
else
{
lean_dec_ref(v_env_4279_);
lean_dec_ref(v_env_4278_);
lean_dec_ref(v_val_4275_);
v___y_4045_ = v_a_4159_;
v___y_4046_ = v___f_4280_;
v___y_4047_ = v___x_4224_;
v___y_4048_ = v___x_4243_;
goto v___jp_4044_;
}
}
case 0:
{
lean_object* v_val_4299_; lean_object* v_toConstantVal_4300_; lean_object* v_name_4301_; lean_object* v___x_4303_; 
lean_dec_ref(v___f_4245_);
v_val_4299_ = lean_ctor_get(v_decl_3571_, 0);
v_toConstantVal_4300_ = lean_ctor_get(v_val_4299_, 0);
v_name_4301_ = lean_ctor_get(v_toConstantVal_4300_, 0);
lean_inc_ref(v_val_4299_);
if (v_isShared_4162_ == 0)
{
lean_ctor_set(v___x_4161_, 0, v_val_4299_);
v___x_4303_ = v___x_4161_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v_val_4299_);
v___x_4303_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
uint8_t v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; 
v___x_4304_ = 2;
v___x_4305_ = lean_box(v___x_4304_);
v___x_4306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4303_);
lean_ctor_set(v___x_4306_, 1, v___x_4305_);
lean_inc(v_name_4301_);
v___x_4307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4307_, 0, v_name_4301_);
lean_ctor_set(v___x_4307_, 1, v___x_4306_);
lean_inc(v_a_3574_);
lean_inc_ref(v_a_3573_);
v___x_4308_ = l_Lean_addDecl___lam__13(v_decl_3571_, v___x_3630_, v___x_4164_, v_cls_3766_, v___x_4239_, v___x_4243_, v___x_4307_, v___x_4243_, v_a_3573_, v_a_3574_);
v___y_4025_ = v_a_4159_;
v___y_4026_ = v___x_4224_;
v___y_4027_ = v___x_4308_;
goto v___jp_4024_;
}
}
default: 
{
lean_object* v___x_4310_; 
lean_dec_ref(v___f_4245_);
lean_del_object(v___x_4161_);
lean_inc(v_a_3574_);
lean_inc_ref(v_a_3573_);
lean_inc(v_decl_3571_);
v___x_4310_ = l_Lean_addDecl___lam__3(v_cls_3766_, v_decl_3571_, v_decl_3571_, v_a_3573_, v_a_3574_);
lean_dec(v_decl_3571_);
v___y_4025_ = v_a_4159_;
v___y_4026_ = v___x_4224_;
v___y_4027_ = v___x_4310_;
goto v___jp_4024_;
}
}
}
}
}
}
}
}
}
v___jp_3576_:
{
lean_object* v___x_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3587_; 
v___x_3580_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3578_, v___y_3577_);
lean_dec(v___y_3577_);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3587_ == 0)
{
lean_object* v_unused_3588_; 
v_unused_3588_ = lean_ctor_get(v___x_3580_, 0);
lean_dec(v_unused_3588_);
v___x_3582_ = v___x_3580_;
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
else
{
lean_dec(v___x_3580_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3585_; 
if (v_isShared_3583_ == 0)
{
lean_ctor_set_tag(v___x_3582_, 1);
lean_ctor_set(v___x_3582_, 0, v_a_3579_);
v___x_3585_ = v___x_3582_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3579_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
v___jp_3589_:
{
lean_object* v___x_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3600_; 
v___x_3593_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3591_, v___y_3590_);
lean_dec(v___y_3590_);
v_isSharedCheck_3600_ = !lean_is_exclusive(v___x_3593_);
if (v_isSharedCheck_3600_ == 0)
{
lean_object* v_unused_3601_; 
v_unused_3601_ = lean_ctor_get(v___x_3593_, 0);
lean_dec(v_unused_3601_);
v___x_3595_ = v___x_3593_;
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
else
{
lean_dec(v___x_3593_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v___x_3598_; 
if (v_isShared_3596_ == 0)
{
lean_ctor_set(v___x_3595_, 0, v_a_3592_);
v___x_3598_ = v___x_3595_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_a_3592_);
v___x_3598_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
return v___x_3598_;
}
}
}
v___jp_3602_:
{
lean_object* v___x_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3613_; 
v___x_3606_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3603_, v___y_3604_);
lean_dec(v___y_3604_);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3613_ == 0)
{
lean_object* v_unused_3614_; 
v_unused_3614_ = lean_ctor_get(v___x_3606_, 0);
lean_dec(v_unused_3614_);
v___x_3608_ = v___x_3606_;
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
else
{
lean_dec(v___x_3606_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3611_; 
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 0, v_a_3605_);
v___x_3611_ = v___x_3608_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_a_3605_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
v___jp_3615_:
{
lean_object* v___x_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3626_; 
v___x_3619_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3616_, v___y_3617_);
lean_dec(v___y_3617_);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3619_);
if (v_isSharedCheck_3626_ == 0)
{
lean_object* v_unused_3627_; 
v_unused_3627_ = lean_ctor_get(v___x_3619_, 0);
lean_dec(v_unused_3627_);
v___x_3621_ = v___x_3619_;
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
else
{
lean_dec(v___x_3619_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3624_; 
if (v_isShared_3622_ == 0)
{
lean_ctor_set_tag(v___x_3621_, 1);
lean_ctor_set(v___x_3621_, 0, v_a_3618_);
v___x_3624_ = v___x_3621_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3618_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
v___jp_3631_:
{
lean_object* v___x_3643_; 
lean_inc_ref(v___y_3639_);
v___x_3643_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3633_, v___y_3639_, v___y_3638_, v___y_3642_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_object* v___x_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3690_; 
lean_dec_ref(v___x_3643_);
lean_inc_ref(v___y_3635_);
v___x_3644_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3635_, v___y_3640_);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3690_ == 0)
{
lean_object* v_unused_3691_; 
v_unused_3691_ = lean_ctor_get(v___x_3644_, 0);
lean_dec(v_unused_3691_);
v___x_3646_ = v___x_3644_;
v_isShared_3647_ = v_isSharedCheck_3690_;
goto v_resetjp_3645_;
}
else
{
lean_dec(v___x_3644_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3690_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v_options_3648_; lean_object* v___x_3649_; uint8_t v___x_3650_; 
v_options_3648_ = lean_ctor_get(v___y_3641_, 2);
v___x_3649_ = l_Lean_Elab_async;
v___x_3650_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3648_, v___x_3649_);
if (v___x_3650_ == 0)
{
lean_object* v___x_3651_; lean_object* v_r_3652_; 
lean_del_object(v___x_3646_);
lean_dec_ref(v___y_3636_);
lean_dec_ref(v___y_3634_);
v___x_3651_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3639_, v___y_3640_);
lean_dec_ref(v___x_3651_);
lean_inc(v___y_3640_);
v_r_3652_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3571_, v___y_3641_, v___y_3640_);
if (lean_obj_tag(v_r_3652_) == 0)
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3662_; 
v_a_3653_ = lean_ctor_get(v_r_3652_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v_r_3652_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3655_ = v_r_3652_;
v_isShared_3656_ = v_isSharedCheck_3662_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v_r_3652_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3662_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3658_; 
lean_inc(v_a_3653_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set_tag(v___x_3655_, 1);
v___x_3658_ = v___x_3655_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_a_3653_);
v___x_3658_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
lean_object* v___x_3659_; 
v___x_3659_ = lean_apply_2(v___y_3632_, v___x_3658_, lean_box(0));
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_dec_ref(v___x_3659_);
v___y_3603_ = v___y_3635_;
v___y_3604_ = v___y_3640_;
v_a_3605_ = v_a_3653_;
goto v___jp_3602_;
}
else
{
lean_object* v_a_3660_; 
lean_dec(v_a_3653_);
v_a_3660_ = lean_ctor_get(v___x_3659_, 0);
lean_inc(v_a_3660_);
lean_dec_ref(v___x_3659_);
v___y_3616_ = v___y_3635_;
v___y_3617_ = v___y_3640_;
v_a_3618_ = v_a_3660_;
goto v___jp_3615_;
}
}
}
}
else
{
lean_object* v_a_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v_a_3663_ = lean_ctor_get(v_r_3652_, 0);
lean_inc(v_a_3663_);
lean_dec_ref(v_r_3652_);
v___x_3664_ = lean_box(0);
v___x_3665_ = lean_apply_2(v___y_3632_, v___x_3664_, lean_box(0));
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_dec_ref(v___x_3665_);
v___y_3616_ = v___y_3635_;
v___y_3617_ = v___y_3640_;
v_a_3618_ = v_a_3663_;
goto v___jp_3615_;
}
else
{
lean_object* v_a_3666_; 
lean_dec(v_a_3663_);
v_a_3666_ = lean_ctor_get(v___x_3665_, 0);
lean_inc(v_a_3666_);
lean_dec_ref(v___x_3665_);
v___y_3616_ = v___y_3635_;
v___y_3617_ = v___y_3640_;
v_a_3618_ = v_a_3666_;
goto v___jp_3615_;
}
}
}
else
{
lean_object* v___x_3667_; lean_object* v___x_3669_; 
lean_dec_ref(v___y_3639_);
lean_dec_ref(v___y_3635_);
lean_dec_ref(v___y_3632_);
lean_dec(v_decl_3571_);
v___x_3667_ = l_IO_CancelToken_new();
if (v_isShared_3647_ == 0)
{
lean_ctor_set_tag(v___x_3646_, 1);
lean_ctor_set(v___x_3646_, 0, v___x_3667_);
v___x_3669_ = v___x_3646_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v___x_3667_);
v___x_3669_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
v___x_3670_ = ((lean_object*)(l_Lean_addDecl___closed__0));
v___x_3671_ = l_Lean_Name_toString(v___x_3670_, v___y_3637_);
lean_inc_ref(v___x_3669_);
v___x_3672_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3636_, v___x_3669_, v___x_3671_, v___y_3641_, v___y_3640_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v_a_3673_; lean_object* v_checked_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; 
v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
lean_inc(v_a_3673_);
lean_dec_ref(v___x_3672_);
v_checked_3674_ = lean_ctor_get(v___y_3634_, 2);
lean_inc_ref(v_checked_3674_);
lean_dec_ref(v___y_3634_);
v___x_3675_ = lean_unsigned_to_nat(0u);
v___x_3676_ = lean_io_map_task(v_a_3673_, v_checked_3674_, v___x_3675_, v_hasTrace_3629_);
v___x_3677_ = lean_box(0);
v___x_3678_ = lean_box(2);
v___x_3679_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3677_);
lean_ctor_set(v___x_3679_, 1, v___x_3678_);
lean_ctor_set(v___x_3679_, 2, v___x_3669_);
lean_ctor_set(v___x_3679_, 3, v___x_3676_);
v___x_3680_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3679_, v___y_3640_);
lean_dec(v___y_3640_);
return v___x_3680_;
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_dec_ref(v___x_3669_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3634_);
v_a_3681_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3672_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3672_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
if (v_isShared_3684_ == 0)
{
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3681_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3704_; 
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec_ref(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec_ref(v___y_3632_);
lean_dec(v_decl_3571_);
v_a_3692_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3704_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3694_ = v___x_3643_;
v_isShared_3695_ = v_isSharedCheck_3704_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v___x_3643_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3704_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v_ref_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3702_; 
v_ref_3696_ = lean_ctor_get(v___y_3641_, 5);
lean_inc(v_ref_3696_);
lean_dec_ref(v___y_3641_);
v___x_3697_ = lean_io_error_to_string(v_a_3692_);
v___x_3698_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3697_);
v___x_3699_ = l_Lean_MessageData_ofFormat(v___x_3698_);
v___x_3700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3700_, 0, v_ref_3696_);
lean_ctor_set(v___x_3700_, 1, v___x_3699_);
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 0, v___x_3700_);
v___x_3702_ = v___x_3694_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v___x_3700_);
v___x_3702_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
return v___x_3702_;
}
}
}
}
v___jp_3705_:
{
uint8_t v___x_3716_; lean_object* v___x_3717_; 
v___x_3716_ = 1;
lean_inc_ref(v___y_3706_);
v___x_3717_ = l_Lean_Environment_addConstAsync(v___y_3706_, v___y_3709_, v___y_3710_, v___y_3715_, v_hasTrace_3629_, v___x_3716_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v_mainEnv_3719_; lean_object* v_asyncEnv_3720_; lean_object* v___f_3721_; lean_object* v___f_3722_; lean_object* v___x_3723_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3718_);
lean_dec_ref(v___x_3717_);
v_mainEnv_3719_ = lean_ctor_get(v_a_3718_, 0);
lean_inc_ref(v_mainEnv_3719_);
v_asyncEnv_3720_ = lean_ctor_get(v_a_3718_, 1);
lean_inc_ref(v_asyncEnv_3720_);
lean_inc(v_a_3718_);
v___f_3721_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3721_, 0, v___y_3707_);
lean_closure_set(v___f_3721_, 1, v_a_3718_);
lean_closure_set(v___f_3721_, 2, v___y_3708_);
lean_inc(v_decl_3571_);
lean_inc(v_a_3718_);
lean_inc_ref(v_asyncEnv_3720_);
v___f_3722_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3722_, 0, v_asyncEnv_3720_);
lean_closure_set(v___f_3722_, 1, v_a_3718_);
lean_closure_set(v___f_3722_, 2, v_decl_3571_);
v___x_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3723_, 0, v___y_3714_);
if (lean_obj_tag(v___y_3712_) == 0)
{
lean_inc_ref(v___x_3723_);
v___y_3632_ = v___f_3721_;
v___y_3633_ = v_a_3718_;
v___y_3634_ = v___y_3706_;
v___y_3635_ = v_mainEnv_3719_;
v___y_3636_ = v___f_3722_;
v___y_3637_ = v___x_3716_;
v___y_3638_ = v___x_3723_;
v___y_3639_ = v_asyncEnv_3720_;
v___y_3640_ = v___y_3711_;
v___y_3641_ = v___y_3713_;
v___y_3642_ = v___x_3723_;
goto v___jp_3631_;
}
else
{
v___y_3632_ = v___f_3721_;
v___y_3633_ = v_a_3718_;
v___y_3634_ = v___y_3706_;
v___y_3635_ = v_mainEnv_3719_;
v___y_3636_ = v___f_3722_;
v___y_3637_ = v___x_3716_;
v___y_3638_ = v___x_3723_;
v___y_3639_ = v_asyncEnv_3720_;
v___y_3640_ = v___y_3711_;
v___y_3641_ = v___y_3713_;
v___y_3642_ = v___y_3712_;
goto v___jp_3631_;
}
}
else
{
lean_object* v_a_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3736_; 
lean_dec_ref(v___y_3714_);
lean_dec(v___y_3712_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3708_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v_decl_3571_);
v_a_3724_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3726_ = v___x_3717_;
v_isShared_3727_ = v_isSharedCheck_3736_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_a_3724_);
lean_dec(v___x_3717_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3736_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v_ref_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3734_; 
v_ref_3728_ = lean_ctor_get(v___y_3713_, 5);
lean_inc(v_ref_3728_);
lean_dec_ref(v___y_3713_);
v___x_3729_ = lean_io_error_to_string(v_a_3724_);
v___x_3730_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3729_);
v___x_3731_ = l_Lean_MessageData_ofFormat(v___x_3730_);
v___x_3732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3732_, 0, v_ref_3728_);
lean_ctor_set(v___x_3732_, 1, v___x_3731_);
if (v_isShared_3727_ == 0)
{
lean_ctor_set(v___x_3726_, 0, v___x_3732_);
v___x_3734_ = v___x_3726_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3732_);
v___x_3734_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
return v___x_3734_;
}
}
}
}
v___jp_3737_:
{
lean_object* v___x_3744_; 
v___x_3744_ = lean_st_ref_get(v___y_3743_);
if (lean_obj_tag(v_exportedInfo_x3f_3741_) == 0)
{
lean_object* v_env_3745_; lean_object* v___x_3746_; 
v_env_3745_ = lean_ctor_get(v___x_3744_, 0);
lean_inc_ref(v_env_3745_);
lean_dec(v___x_3744_);
v___x_3746_ = lean_box(0);
lean_inc_ref(v___y_3742_);
lean_inc(v___y_3743_);
v___y_3706_ = v_env_3745_;
v___y_3707_ = v___y_3743_;
v___y_3708_ = v___y_3742_;
v___y_3709_ = v___y_3738_;
v___y_3710_ = v___y_3739_;
v___y_3711_ = v___y_3743_;
v___y_3712_ = v_exportedInfo_x3f_3741_;
v___y_3713_ = v___y_3742_;
v___y_3714_ = v___y_3740_;
v___y_3715_ = v___x_3746_;
goto v___jp_3705_;
}
else
{
lean_object* v_env_3747_; lean_object* v_val_3748_; uint8_t v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; 
v_env_3747_ = lean_ctor_get(v___x_3744_, 0);
lean_inc_ref(v_env_3747_);
lean_dec(v___x_3744_);
v_val_3748_ = lean_ctor_get(v_exportedInfo_x3f_3741_, 0);
v___x_3749_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3748_);
v___x_3750_ = lean_box(v___x_3749_);
v___x_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3750_);
lean_inc_ref(v___y_3742_);
lean_inc(v___y_3743_);
v___y_3706_ = v_env_3747_;
v___y_3707_ = v___y_3743_;
v___y_3708_ = v___y_3742_;
v___y_3709_ = v___y_3738_;
v___y_3710_ = v___y_3739_;
v___y_3711_ = v___y_3743_;
v___y_3712_ = v_exportedInfo_x3f_3741_;
v___y_3713_ = v___y_3742_;
v___y_3714_ = v___y_3740_;
v___y_3715_ = v___x_3751_;
goto v___jp_3705_;
}
}
v___jp_3752_:
{
lean_object* v___x_3758_; 
lean_inc_ref(v___y_3755_);
v___x_3758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3758_, 0, v___y_3755_);
v___y_3738_ = v___y_3753_;
v___y_3739_ = v___y_3754_;
v___y_3740_ = v___y_3755_;
v_exportedInfo_x3f_3741_ = v___x_3758_;
v___y_3742_ = v___y_3756_;
v___y_3743_ = v___y_3757_;
goto v___jp_3737_;
}
v___jp_3759_:
{
lean_object* v___x_3765_; 
lean_inc_ref(v___y_3762_);
v___x_3765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3765_, 0, v___y_3762_);
v___y_3738_ = v___y_3760_;
v___y_3739_ = v___y_3761_;
v___y_3740_ = v___y_3762_;
v_exportedInfo_x3f_3741_ = v___x_3765_;
v___y_3742_ = v___y_3763_;
v___y_3743_ = v___y_3764_;
goto v___jp_3737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___boxed(lean_object* v_decl_4704_, lean_object* v_forceExpose_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_){
_start:
{
uint8_t v_forceExpose_boxed_4709_; lean_object* v_res_4710_; 
v_forceExpose_boxed_4709_ = lean_unbox(v_forceExpose_4705_);
v_res_4710_ = l_Lean_addDecl(v_decl_4704_, v_forceExpose_boxed_4709_, v_a_4706_, v_a_4707_);
return v_res_4710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_addDecl_spec__2(lean_object* v_opt_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_){
_start:
{
lean_object* v___x_4715_; 
v___x_4715_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__2___redArg(v_opt_4711_, v___y_4712_);
return v___x_4715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_addDecl_spec__2___boxed(lean_object* v_opt_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_){
_start:
{
lean_object* v_res_4720_; 
v_res_4720_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__2(v_opt_4716_, v___y_4717_, v___y_4718_);
lean_dec(v___y_4718_);
lean_dec_ref(v___y_4717_);
lean_dec_ref(v_opt_4716_);
return v_res_4720_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object* v_decl_4721_, uint8_t v_logCompileErrors_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_){
_start:
{
uint8_t v___x_4726_; lean_object* v___x_4727_; 
v___x_4726_ = 0;
lean_inc(v_a_4724_);
lean_inc_ref(v_a_4723_);
lean_inc(v_decl_4721_);
v___x_4727_ = l_Lean_addDecl(v_decl_4721_, v___x_4726_, v_a_4723_, v_a_4724_);
if (lean_obj_tag(v___x_4727_) == 0)
{
lean_object* v___x_4728_; 
lean_dec_ref(v___x_4727_);
v___x_4728_ = l_Lean_compileDecl(v_decl_4721_, v_logCompileErrors_4722_, v_a_4723_, v_a_4724_);
return v___x_4728_;
}
else
{
lean_dec(v_a_4724_);
lean_dec_ref(v_a_4723_);
lean_dec(v_decl_4721_);
return v___x_4727_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___boxed(lean_object* v_decl_4729_, lean_object* v_logCompileErrors_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_){
_start:
{
uint8_t v_logCompileErrors_boxed_4734_; lean_object* v_res_4735_; 
v_logCompileErrors_boxed_4734_ = lean_unbox(v_logCompileErrors_4730_);
v_res_4735_ = l_Lean_addAndCompile(v_decl_4729_, v_logCompileErrors_boxed_4734_, v_a_4731_, v_a_4732_);
return v_res_4735_;
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
