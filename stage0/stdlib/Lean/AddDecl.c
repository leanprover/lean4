// Lean compiler output
// Module: Lean.AddDecl
// Imports: public import Lean.Meta.Sorry public import Lean.Util.CollectAxioms public import Lean.OriginalConstKind import Lean.Compiler.MetaAttr import all Lean.OriginalConstKind
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
uint8_t l_Lean_isPrivateName(lean_object*);
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
lean_object* l_Lean_markMeta(lean_object*, lean_object*);
lean_object* l_Lean_Environment_AddConstAsyncResult_commitConst(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_async;
lean_object* l_IO_CancelToken_new();
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Core_logSnapshotTask___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_addConstAsync(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t);
uint8_t l_Lean_ConstantKind_ofConstantInfo(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_AddDecl_0__Lean_initFn___closed__0_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "warn"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__0_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__0_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sorry"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_initFn___closed__2_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__0_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(187, 250, 156, 61, 219, 107, 141, 135)}};
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_initFn___closed__2_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__2_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(122, 28, 133, 152, 90, 118, 109, 25)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__2_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__2_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_initFn___closed__3_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "warn about uses of `sorry` in declarations added to the environment"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__3_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__3_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_initFn___closed__4_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__3_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__4_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__4_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_initFn___closed__5_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__5_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__5_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_initFn___closed__6_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__5_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_initFn___closed__6_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__6_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__0_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(218, 70, 28, 226, 178, 151, 16, 11)}};
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_initFn___closed__6_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__6_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(239, 41, 235, 79, 240, 234, 67, 166)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__6_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__6_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4____boxed(lean_object*);
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
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_initFn___closed__4_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__3_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__5_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__4_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__4_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_initFn___closed__5_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "AddDecl"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__5_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__5_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_initFn___closed__6_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__4_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__5_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(15, 97, 208, 69, 128, 127, 228, 3)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__6_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__6_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_initFn___closed__7_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__6_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(162, 171, 242, 31, 173, 26, 83, 224)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__7_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__7_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_initFn___closed__8_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__7_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__5_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(131, 0, 147, 169, 205, 191, 49, 101)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__8_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__8_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_initFn___closed__9_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__9_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__9_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_initFn___closed__10_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__8_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__9_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(226, 50, 5, 71, 0, 154, 50, 2)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__10_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__10_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_initFn___closed__11_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__11_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__11_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_initFn___closed__12_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__10_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__11_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(107, 66, 231, 246, 189, 183, 24, 140)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_initFn___closed__12_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__12_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_initFn___closed__13_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__12_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__5_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(86, 225, 3, 95, 219, 217, 43, 37)}};
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
LEAN_EXPORT uint8_t l_List_all___at___00Lean_addDecl_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00Lean_addDecl_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_addDecl_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_addDecl_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addDecl___lam__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "no matching exporting rules, exporting as is"};
static const lean_object* l_Lean_addDecl___lam__8___closed__0 = (const lean_object*)&l_Lean_addDecl___lam__8___closed__0_value;
static lean_once_cell_t l_Lean_addDecl___lam__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addDecl___lam__8___closed__1;
static const lean_string_object l_Lean_addDecl___lam__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "not exporting private declaration at all"};
static const lean_object* l_Lean_addDecl___lam__8___closed__2 = (const lean_object*)&l_Lean_addDecl___lam__8___closed__2_value;
static lean_once_cell_t l_Lean_addDecl___lam__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addDecl___lam__8___closed__3;
static const lean_string_object l_Lean_addDecl___lam__8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "private decl under `privateInPublic`, exporting as is"};
static const lean_object* l_Lean_addDecl___lam__8___closed__4 = (const lean_object*)&l_Lean_addDecl___lam__8___closed__4_value;
static lean_once_cell_t l_Lean_addDecl___lam__8___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addDecl___lam__8___closed__5;
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
static const lean_ctor_object l_Lean_addDecl___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__5_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_addDecl_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_addDecl_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addAndCompile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(lean_object* v_name_76_, lean_object* v_decl_77_, lean_object* v_ref_78_){
_start:
{
lean_object* v_defValue_80_; lean_object* v_descr_81_; lean_object* v_deprecation_x3f_82_; lean_object* v___x_83_; uint8_t v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v_defValue_80_ = lean_ctor_get(v_decl_77_, 0);
v_descr_81_ = lean_ctor_get(v_decl_77_, 1);
v_deprecation_x3f_82_ = lean_ctor_get(v_decl_77_, 2);
v___x_83_ = lean_alloc_ctor(1, 0, 1);
v___x_84_ = lean_unbox(v_defValue_80_);
lean_ctor_set_uint8(v___x_83_, 0, v___x_84_);
lean_inc(v_deprecation_x3f_82_);
lean_inc_ref(v_descr_81_);
lean_inc_n(v_name_76_, 2);
v___x_85_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_85_, 0, v_name_76_);
lean_ctor_set(v___x_85_, 1, v_ref_78_);
lean_ctor_set(v___x_85_, 2, v___x_83_);
lean_ctor_set(v___x_85_, 3, v_descr_81_);
lean_ctor_set(v___x_85_, 4, v_deprecation_x3f_82_);
v___x_86_ = lean_register_option(v_name_76_, v___x_85_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_94_; 
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_94_ == 0)
{
lean_object* v_unused_95_; 
v_unused_95_ = lean_ctor_get(v___x_86_, 0);
lean_dec(v_unused_95_);
v___x_88_ = v___x_86_;
v_isShared_89_ = v_isSharedCheck_94_;
goto v_resetjp_87_;
}
else
{
lean_dec(v___x_86_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_94_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; lean_object* v___x_92_; 
lean_inc(v_defValue_80_);
v___x_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_90_, 0, v_name_76_);
lean_ctor_set(v___x_90_, 1, v_defValue_80_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 0, v___x_90_);
v___x_92_ = v___x_88_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_90_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
lean_dec(v_name_76_);
v_a_96_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_86_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_86_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_96_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_104_, lean_object* v_decl_105_, lean_object* v_ref_106_, lean_object* v_a_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(v_name_104_, v_decl_105_, v_ref_106_);
lean_dec_ref(v_decl_105_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_126_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__2_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_127_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__4_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_128_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__6_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_129_ = l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(v___x_126_, v___x_127_, v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4____boxed(lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_();
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(lean_object* v_msgData_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v___x_138_; lean_object* v_env_139_; lean_object* v___x_140_; lean_object* v_mctx_141_; lean_object* v_lctx_142_; lean_object* v_options_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_138_ = lean_st_ref_get(v___y_136_);
v_env_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc_ref(v_env_139_);
lean_dec(v___x_138_);
v___x_140_ = lean_st_ref_get(v___y_134_);
v_mctx_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc_ref(v_mctx_141_);
lean_dec(v___x_140_);
v_lctx_142_ = lean_ctor_get(v___y_133_, 2);
v_options_143_ = lean_ctor_get(v___y_135_, 2);
lean_inc_ref(v_options_143_);
lean_inc_ref(v_lctx_142_);
v___x_144_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_144_, 0, v_env_139_);
lean_ctor_set(v___x_144_, 1, v_mctx_141_);
lean_ctor_set(v___x_144_, 2, v_lctx_142_);
lean_ctor_set(v___x_144_, 3, v_options_143_);
v___x_145_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v_msgData_132_);
v___x_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0___boxed(lean_object* v_msgData_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(v_msgData_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___lam__0(lean_object* v_s_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v_a_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_177_; 
lean_inc_ref(v_s_154_);
v___x_161_ = l_Lean_MessageData_ofExpr(v_s_154_);
v___x_162_ = l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(v___x_161_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
v_a_163_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_177_ == 0)
{
v___x_165_ = v___x_162_;
v_isShared_166_ = v_isSharedCheck_177_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_a_163_);
lean_dec(v___x_162_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_177_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_167_; uint8_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_175_; 
v___x_167_ = lean_st_ref_take(v___y_155_);
v___x_168_ = l_Lean_Expr_isSyntheticSorry(v_s_154_);
lean_dec_ref(v_s_154_);
v___x_169_ = lean_box(v___x_168_);
v___x_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v_a_163_);
v___x_171_ = lean_array_push(v___x_167_, v___x_170_);
v___x_172_ = lean_st_ref_set(v___y_155_, v___x_171_);
v___x_173_ = lean_box(0);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v___x_173_);
v___x_175_ = v___x_165_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_173_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___lam__0___boxed(lean_object* v_s_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_warnIfUsesSorry___lam__0(v_s_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
return v_res_185_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(uint8_t v___y_194_, uint8_t v_suppressElabErrors_195_, lean_object* v_x_196_){
_start:
{
if (lean_obj_tag(v_x_196_) == 1)
{
lean_object* v_pre_197_; 
v_pre_197_ = lean_ctor_get(v_x_196_, 0);
switch(lean_obj_tag(v_pre_197_))
{
case 1:
{
lean_object* v_pre_198_; 
v_pre_198_ = lean_ctor_get(v_pre_197_, 0);
switch(lean_obj_tag(v_pre_198_))
{
case 0:
{
lean_object* v_str_199_; lean_object* v_str_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v_str_199_ = lean_ctor_get(v_x_196_, 1);
v_str_200_ = lean_ctor_get(v_pre_197_, 1);
v___x_201_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__0));
v___x_202_ = lean_string_dec_eq(v_str_200_, v___x_201_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_203_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__1));
v___x_204_ = lean_string_dec_eq(v_str_200_, v___x_203_);
if (v___x_204_ == 0)
{
return v___y_194_;
}
else
{
lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_205_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__2));
v___x_206_ = lean_string_dec_eq(v_str_199_, v___x_205_);
if (v___x_206_ == 0)
{
return v___y_194_;
}
else
{
return v_suppressElabErrors_195_;
}
}
}
else
{
lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_207_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__3));
v___x_208_ = lean_string_dec_eq(v_str_199_, v___x_207_);
if (v___x_208_ == 0)
{
return v___y_194_;
}
else
{
return v_suppressElabErrors_195_;
}
}
}
case 1:
{
lean_object* v_pre_209_; 
v_pre_209_ = lean_ctor_get(v_pre_198_, 0);
if (lean_obj_tag(v_pre_209_) == 0)
{
lean_object* v_str_210_; lean_object* v_str_211_; lean_object* v_str_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v_str_210_ = lean_ctor_get(v_x_196_, 1);
v_str_211_ = lean_ctor_get(v_pre_197_, 1);
v_str_212_ = lean_ctor_get(v_pre_198_, 1);
v___x_213_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__4));
v___x_214_ = lean_string_dec_eq(v_str_212_, v___x_213_);
if (v___x_214_ == 0)
{
return v___y_194_;
}
else
{
lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_215_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__5));
v___x_216_ = lean_string_dec_eq(v_str_211_, v___x_215_);
if (v___x_216_ == 0)
{
return v___y_194_;
}
else
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__6));
v___x_218_ = lean_string_dec_eq(v_str_210_, v___x_217_);
if (v___x_218_ == 0)
{
return v___y_194_;
}
else
{
return v_suppressElabErrors_195_;
}
}
}
}
else
{
return v___y_194_;
}
}
default: 
{
return v___y_194_;
}
}
}
case 0:
{
lean_object* v_str_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v_str_219_ = lean_ctor_get(v_x_196_, 1);
v___x_220_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__7));
v___x_221_ = lean_string_dec_eq(v_str_219_, v___x_220_);
if (v___x_221_ == 0)
{
return v___y_194_;
}
else
{
return v_suppressElabErrors_195_;
}
}
default: 
{
return v___y_194_;
}
}
}
else
{
return v___y_194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed(lean_object* v___y_222_, lean_object* v_suppressElabErrors_223_, lean_object* v_x_224_){
_start:
{
uint8_t v___y_15958__boxed_225_; uint8_t v_suppressElabErrors_boxed_226_; uint8_t v_res_227_; lean_object* v_r_228_; 
v___y_15958__boxed_225_ = lean_unbox(v___y_222_);
v_suppressElabErrors_boxed_226_ = lean_unbox(v_suppressElabErrors_223_);
v_res_227_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(v___y_15958__boxed_225_, v_suppressElabErrors_boxed_226_, v_x_224_);
lean_dec(v_x_224_);
v_r_228_ = lean_box(v_res_227_);
return v_r_228_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0(void){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_229_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0);
v___x_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_232_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1);
v___x_233_ = lean_unsigned_to_nat(0u);
v___x_234_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
lean_ctor_set(v___x_234_, 2, v___x_233_);
lean_ctor_set(v___x_234_, 3, v___x_233_);
lean_ctor_set(v___x_234_, 4, v___x_232_);
lean_ctor_set(v___x_234_, 5, v___x_232_);
lean_ctor_set(v___x_234_, 6, v___x_232_);
lean_ctor_set(v___x_234_, 7, v___x_232_);
lean_ctor_set(v___x_234_, 8, v___x_232_);
lean_ctor_set(v___x_234_, 9, v___x_232_);
return v___x_234_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_235_ = lean_unsigned_to_nat(32u);
v___x_236_ = lean_mk_empty_array_with_capacity(v___x_235_);
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4(void){
_start:
{
size_t v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_238_ = ((size_t)5ULL);
v___x_239_ = lean_unsigned_to_nat(0u);
v___x_240_ = lean_unsigned_to_nat(32u);
v___x_241_ = lean_mk_empty_array_with_capacity(v___x_240_);
v___x_242_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3);
v___x_243_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v___x_241_);
lean_ctor_set(v___x_243_, 2, v___x_239_);
lean_ctor_set(v___x_243_, 3, v___x_239_);
lean_ctor_set_usize(v___x_243_, 4, v___x_238_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_244_ = lean_box(1);
v___x_245_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_246_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1);
v___x_247_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v___x_245_);
lean_ctor_set(v___x_247_, 2, v___x_244_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(lean_object* v_msgData_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v___x_252_; lean_object* v_env_253_; lean_object* v_options_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_252_ = lean_st_ref_get(v___y_250_);
v_env_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc_ref(v_env_253_);
lean_dec(v___x_252_);
v_options_254_ = lean_ctor_get(v___y_249_, 2);
v___x_255_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2);
v___x_256_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5);
lean_inc_ref(v_options_254_);
v___x_257_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_257_, 0, v_env_253_);
lean_ctor_set(v___x_257_, 1, v___x_255_);
lean_ctor_set(v___x_257_, 2, v___x_256_);
lean_ctor_set(v___x_257_, 3, v_options_254_);
v___x_258_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set(v___x_258_, 1, v_msgData_248_);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___boxed(lean_object* v_msgData_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msgData_260_, v___y_261_, v___y_262_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(lean_object* v_ref_266_, lean_object* v_msgData_267_, uint8_t v_severity_268_, uint8_t v_isSilent_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
uint8_t v___y_274_; lean_object* v___y_275_; lean_object* v___y_276_; lean_object* v___y_277_; uint8_t v___y_278_; lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v___y_282_; lean_object* v___y_311_; uint8_t v___y_312_; lean_object* v___y_313_; uint8_t v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; uint8_t v___y_317_; lean_object* v___y_318_; lean_object* v___y_336_; uint8_t v___y_337_; lean_object* v___y_338_; lean_object* v___y_339_; uint8_t v___y_340_; lean_object* v___y_341_; uint8_t v___y_342_; lean_object* v___y_343_; lean_object* v___y_347_; lean_object* v___y_348_; uint8_t v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; uint8_t v___y_352_; uint8_t v___y_353_; uint8_t v___x_358_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; uint8_t v___y_364_; uint8_t v___y_365_; uint8_t v___y_366_; uint8_t v___y_368_; uint8_t v___x_383_; 
v___x_358_ = 2;
v___x_383_ = l_Lean_instBEqMessageSeverity_beq(v_severity_268_, v___x_358_);
if (v___x_383_ == 0)
{
v___y_368_ = v___x_383_;
goto v___jp_367_;
}
else
{
uint8_t v___x_384_; 
lean_inc_ref(v_msgData_267_);
v___x_384_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_267_);
v___y_368_ = v___x_384_;
goto v___jp_367_;
}
v___jp_273_:
{
lean_object* v___x_283_; lean_object* v_currNamespace_284_; lean_object* v_openDecls_285_; lean_object* v_env_286_; lean_object* v_nextMacroScope_287_; lean_object* v_ngen_288_; lean_object* v_auxDeclNGen_289_; lean_object* v_traceState_290_; lean_object* v_cache_291_; lean_object* v_messages_292_; lean_object* v_infoState_293_; lean_object* v_snapshotTasks_294_; lean_object* v_newDecls_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_309_; 
v___x_283_ = lean_st_ref_take(v___y_282_);
v_currNamespace_284_ = lean_ctor_get(v___y_281_, 6);
v_openDecls_285_ = lean_ctor_get(v___y_281_, 7);
v_env_286_ = lean_ctor_get(v___x_283_, 0);
v_nextMacroScope_287_ = lean_ctor_get(v___x_283_, 1);
v_ngen_288_ = lean_ctor_get(v___x_283_, 2);
v_auxDeclNGen_289_ = lean_ctor_get(v___x_283_, 3);
v_traceState_290_ = lean_ctor_get(v___x_283_, 4);
v_cache_291_ = lean_ctor_get(v___x_283_, 5);
v_messages_292_ = lean_ctor_get(v___x_283_, 6);
v_infoState_293_ = lean_ctor_get(v___x_283_, 7);
v_snapshotTasks_294_ = lean_ctor_get(v___x_283_, 8);
v_newDecls_295_ = lean_ctor_get(v___x_283_, 9);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_309_ == 0)
{
v___x_297_ = v___x_283_;
v_isShared_298_ = v_isSharedCheck_309_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_newDecls_295_);
lean_inc(v_snapshotTasks_294_);
lean_inc(v_infoState_293_);
lean_inc(v_messages_292_);
lean_inc(v_cache_291_);
lean_inc(v_traceState_290_);
lean_inc(v_auxDeclNGen_289_);
lean_inc(v_ngen_288_);
lean_inc(v_nextMacroScope_287_);
lean_inc(v_env_286_);
lean_dec(v___x_283_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_309_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_304_; 
lean_inc(v_openDecls_285_);
lean_inc(v_currNamespace_284_);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v_currNamespace_284_);
lean_ctor_set(v___x_299_, 1, v_openDecls_285_);
v___x_300_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v___y_277_);
lean_inc_ref(v___y_275_);
lean_inc_ref(v___y_279_);
v___x_301_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_301_, 0, v___y_279_);
lean_ctor_set(v___x_301_, 1, v___y_276_);
lean_ctor_set(v___x_301_, 2, v___y_280_);
lean_ctor_set(v___x_301_, 3, v___y_275_);
lean_ctor_set(v___x_301_, 4, v___x_300_);
lean_ctor_set_uint8(v___x_301_, sizeof(void*)*5, v___y_278_);
lean_ctor_set_uint8(v___x_301_, sizeof(void*)*5 + 1, v___y_274_);
lean_ctor_set_uint8(v___x_301_, sizeof(void*)*5 + 2, v_isSilent_269_);
v___x_302_ = l_Lean_MessageLog_add(v___x_301_, v_messages_292_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 6, v___x_302_);
v___x_304_ = v___x_297_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_env_286_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_nextMacroScope_287_);
lean_ctor_set(v_reuseFailAlloc_308_, 2, v_ngen_288_);
lean_ctor_set(v_reuseFailAlloc_308_, 3, v_auxDeclNGen_289_);
lean_ctor_set(v_reuseFailAlloc_308_, 4, v_traceState_290_);
lean_ctor_set(v_reuseFailAlloc_308_, 5, v_cache_291_);
lean_ctor_set(v_reuseFailAlloc_308_, 6, v___x_302_);
lean_ctor_set(v_reuseFailAlloc_308_, 7, v_infoState_293_);
lean_ctor_set(v_reuseFailAlloc_308_, 8, v_snapshotTasks_294_);
lean_ctor_set(v_reuseFailAlloc_308_, 9, v_newDecls_295_);
v___x_304_ = v_reuseFailAlloc_308_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = lean_st_ref_set(v___y_282_, v___x_304_);
v___x_306_ = lean_box(0);
v___x_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
return v___x_307_;
}
}
}
v___jp_310_:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_334_; 
v___x_319_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_267_);
v___x_320_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v___x_319_, v___y_270_, v___y_271_);
v_a_321_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_334_ == 0)
{
v___x_323_ = v___x_320_;
v_isShared_324_ = v_isSharedCheck_334_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_320_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_334_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
lean_inc_ref_n(v___y_313_, 2);
v___x_325_ = l_Lean_FileMap_toPosition(v___y_313_, v___y_315_);
lean_dec(v___y_315_);
v___x_326_ = l_Lean_FileMap_toPosition(v___y_313_, v___y_318_);
lean_dec(v___y_318_);
v___x_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
v___x_328_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
if (v___y_317_ == 0)
{
lean_del_object(v___x_323_);
lean_dec_ref(v___y_311_);
v___y_274_ = v___y_312_;
v___y_275_ = v___x_328_;
v___y_276_ = v___x_325_;
v___y_277_ = v_a_321_;
v___y_278_ = v___y_314_;
v___y_279_ = v___y_316_;
v___y_280_ = v___x_327_;
v___y_281_ = v___y_270_;
v___y_282_ = v___y_271_;
goto v___jp_273_;
}
else
{
uint8_t v___x_329_; 
lean_inc(v_a_321_);
v___x_329_ = l_Lean_MessageData_hasTag(v___y_311_, v_a_321_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v___x_332_; 
lean_dec_ref(v___x_327_);
lean_dec_ref(v___x_325_);
lean_dec(v_a_321_);
v___x_330_ = lean_box(0);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_330_);
v___x_332_ = v___x_323_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
else
{
lean_del_object(v___x_323_);
v___y_274_ = v___y_312_;
v___y_275_ = v___x_328_;
v___y_276_ = v___x_325_;
v___y_277_ = v_a_321_;
v___y_278_ = v___y_314_;
v___y_279_ = v___y_316_;
v___y_280_ = v___x_327_;
v___y_281_ = v___y_270_;
v___y_282_ = v___y_271_;
goto v___jp_273_;
}
}
}
}
v___jp_335_:
{
lean_object* v___x_344_; 
v___x_344_ = l_Lean_Syntax_getTailPos_x3f(v___y_338_, v___y_340_);
lean_dec(v___y_338_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_inc(v___y_343_);
v___y_311_ = v___y_336_;
v___y_312_ = v___y_337_;
v___y_313_ = v___y_339_;
v___y_314_ = v___y_340_;
v___y_315_ = v___y_343_;
v___y_316_ = v___y_341_;
v___y_317_ = v___y_342_;
v___y_318_ = v___y_343_;
goto v___jp_310_;
}
else
{
lean_object* v_val_345_; 
v_val_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_val_345_);
lean_dec_ref(v___x_344_);
v___y_311_ = v___y_336_;
v___y_312_ = v___y_337_;
v___y_313_ = v___y_339_;
v___y_314_ = v___y_340_;
v___y_315_ = v___y_343_;
v___y_316_ = v___y_341_;
v___y_317_ = v___y_342_;
v___y_318_ = v_val_345_;
goto v___jp_310_;
}
}
v___jp_346_:
{
lean_object* v_ref_354_; lean_object* v___x_355_; 
v_ref_354_ = l_Lean_replaceRef(v_ref_266_, v___y_350_);
v___x_355_ = l_Lean_Syntax_getPos_x3f(v_ref_354_, v___y_349_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v___x_356_; 
v___x_356_ = lean_unsigned_to_nat(0u);
v___y_336_ = v___y_347_;
v___y_337_ = v___y_353_;
v___y_338_ = v_ref_354_;
v___y_339_ = v___y_348_;
v___y_340_ = v___y_349_;
v___y_341_ = v___y_351_;
v___y_342_ = v___y_352_;
v___y_343_ = v___x_356_;
goto v___jp_335_;
}
else
{
lean_object* v_val_357_; 
v_val_357_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_val_357_);
lean_dec_ref(v___x_355_);
v___y_336_ = v___y_347_;
v___y_337_ = v___y_353_;
v___y_338_ = v_ref_354_;
v___y_339_ = v___y_348_;
v___y_340_ = v___y_349_;
v___y_341_ = v___y_351_;
v___y_342_ = v___y_352_;
v___y_343_ = v_val_357_;
goto v___jp_335_;
}
}
v___jp_359_:
{
if (v___y_366_ == 0)
{
v___y_347_ = v___y_360_;
v___y_348_ = v___y_361_;
v___y_349_ = v___y_365_;
v___y_350_ = v___y_362_;
v___y_351_ = v___y_363_;
v___y_352_ = v___y_364_;
v___y_353_ = v_severity_268_;
goto v___jp_346_;
}
else
{
v___y_347_ = v___y_360_;
v___y_348_ = v___y_361_;
v___y_349_ = v___y_365_;
v___y_350_ = v___y_362_;
v___y_351_ = v___y_363_;
v___y_352_ = v___y_364_;
v___y_353_ = v___x_358_;
goto v___jp_346_;
}
}
v___jp_367_:
{
if (v___y_368_ == 0)
{
lean_object* v_fileName_369_; lean_object* v_fileMap_370_; lean_object* v_options_371_; lean_object* v_ref_372_; uint8_t v_suppressElabErrors_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___f_376_; uint8_t v___x_377_; uint8_t v___x_378_; 
v_fileName_369_ = lean_ctor_get(v___y_270_, 0);
v_fileMap_370_ = lean_ctor_get(v___y_270_, 1);
v_options_371_ = lean_ctor_get(v___y_270_, 2);
v_ref_372_ = lean_ctor_get(v___y_270_, 5);
v_suppressElabErrors_373_ = lean_ctor_get_uint8(v___y_270_, sizeof(void*)*14 + 1);
v___x_374_ = lean_box(v___y_368_);
v___x_375_ = lean_box(v_suppressElabErrors_373_);
v___f_376_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed), 3, 2);
lean_closure_set(v___f_376_, 0, v___x_374_);
lean_closure_set(v___f_376_, 1, v___x_375_);
v___x_377_ = 1;
v___x_378_ = l_Lean_instBEqMessageSeverity_beq(v_severity_268_, v___x_377_);
if (v___x_378_ == 0)
{
v___y_360_ = v___f_376_;
v___y_361_ = v_fileMap_370_;
v___y_362_ = v_ref_372_;
v___y_363_ = v_fileName_369_;
v___y_364_ = v_suppressElabErrors_373_;
v___y_365_ = v___y_368_;
v___y_366_ = v___x_378_;
goto v___jp_359_;
}
else
{
lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_379_ = l_Lean_warningAsError;
v___x_380_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_371_, v___x_379_);
v___y_360_ = v___f_376_;
v___y_361_ = v_fileMap_370_;
v___y_362_ = v_ref_372_;
v___y_363_ = v_fileName_369_;
v___y_364_ = v_suppressElabErrors_373_;
v___y_365_ = v___y_368_;
v___y_366_ = v___x_380_;
goto v___jp_359_;
}
}
else
{
lean_object* v___x_381_; lean_object* v___x_382_; 
lean_dec_ref(v_msgData_267_);
v___x_381_ = lean_box(0);
v___x_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
return v___x_382_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___boxed(lean_object* v_ref_385_, lean_object* v_msgData_386_, lean_object* v_severity_387_, lean_object* v_isSilent_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
uint8_t v_severity_boxed_392_; uint8_t v_isSilent_boxed_393_; lean_object* v_res_394_; 
v_severity_boxed_392_ = lean_unbox(v_severity_387_);
v_isSilent_boxed_393_ = lean_unbox(v_isSilent_388_);
v_res_394_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_385_, v_msgData_386_, v_severity_boxed_392_, v_isSilent_boxed_393_, v___y_389_, v___y_390_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v_ref_385_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(lean_object* v_msgData_395_, uint8_t v_severity_396_, uint8_t v_isSilent_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_ref_401_; lean_object* v___x_402_; 
v_ref_401_ = lean_ctor_get(v___y_398_, 5);
v___x_402_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_401_, v_msgData_395_, v_severity_396_, v_isSilent_397_, v___y_398_, v___y_399_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4___boxed(lean_object* v_msgData_403_, lean_object* v_severity_404_, lean_object* v_isSilent_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
uint8_t v_severity_boxed_409_; uint8_t v_isSilent_boxed_410_; lean_object* v_res_411_; 
v_severity_boxed_409_ = lean_unbox(v_severity_404_);
v_isSilent_boxed_410_ = lean_unbox(v_isSilent_405_);
v_res_411_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_403_, v_severity_boxed_409_, v_isSilent_boxed_410_, v___y_406_, v___y_407_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(lean_object* v_msgData_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
uint8_t v___x_416_; uint8_t v___x_417_; lean_object* v___x_418_; 
v___x_416_ = 1;
v___x_417_ = 0;
v___x_418_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_412_, v___x_416_, v___x_417_, v___y_413_, v___y_414_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2___boxed(lean_object* v_msgData_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v_msgData_419_, v___y_420_, v___y_421_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(lean_object* v_as_427_, size_t v_sz_428_, size_t v_i_429_, lean_object* v_b_430_){
_start:
{
uint8_t v___x_431_; 
v___x_431_ = lean_usize_dec_lt(v_i_429_, v_sz_428_);
if (v___x_431_ == 0)
{
lean_inc_ref(v_b_430_);
return v_b_430_;
}
else
{
lean_object* v_a_432_; lean_object* v_fst_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v_a_432_ = lean_array_uget_borrowed(v_as_427_, v_i_429_);
v_fst_433_ = lean_ctor_get(v_a_432_, 0);
v___x_434_ = lean_box(0);
v___x_435_ = lean_unbox(v_fst_433_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; size_t v___x_437_; size_t v___x_438_; 
v___x_436_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___closed__0));
v___x_437_ = ((size_t)1ULL);
v___x_438_ = lean_usize_add(v_i_429_, v___x_437_);
v_i_429_ = v___x_438_;
v_b_430_ = v___x_436_;
goto _start;
}
else
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
lean_inc(v_a_432_);
v___x_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_440_, 0, v_a_432_);
v___x_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
v___x_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
lean_ctor_set(v___x_442_, 1, v___x_434_);
return v___x_442_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___boxed(lean_object* v_as_443_, lean_object* v_sz_444_, lean_object* v_i_445_, lean_object* v_b_446_){
_start:
{
size_t v_sz_boxed_447_; size_t v_i_boxed_448_; lean_object* v_res_449_; 
v_sz_boxed_447_ = lean_unbox_usize(v_sz_444_);
lean_dec(v_sz_444_);
v_i_boxed_448_ = lean_unbox_usize(v_i_445_);
lean_dec(v_i_445_);
v_res_449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v_as_443_, v_sz_boxed_447_, v_i_boxed_448_, v_b_446_);
lean_dec_ref(v_b_446_);
lean_dec_ref(v_as_443_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(lean_object* v_fn_450_, lean_object* v_e_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_Expr_getSorry_x3f(v_e_451_);
if (lean_obj_tag(v___x_458_) == 1)
{
lean_object* v_val_459_; lean_object* v___x_460_; 
v_val_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_val_459_);
lean_dec_ref(v___x_458_);
lean_inc(v___y_456_);
lean_inc_ref(v___y_455_);
lean_inc(v___y_454_);
lean_inc_ref(v___y_453_);
lean_inc(v___y_452_);
v___x_460_ = lean_apply_7(v_fn_450_, v_val_459_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, lean_box(0));
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_469_; 
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; 
v_unused_470_ = lean_ctor_get(v___x_460_, 0);
lean_dec(v_unused_470_);
v___x_462_ = v___x_460_;
v_isShared_463_ = v_isSharedCheck_469_;
goto v_resetjp_461_;
}
else
{
lean_dec(v___x_460_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_469_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
uint8_t v___x_464_; lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_464_ = 0;
v___x_465_ = lean_box(v___x_464_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v___x_465_);
v___x_467_ = v___x_462_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
v_a_471_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_460_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_460_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
else
{
uint8_t v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec(v___x_458_);
lean_dec_ref(v_fn_450_);
v___x_479_ = 1;
v___x_480_ = lean_box(v___x_479_);
v___x_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
return v___x_481_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed(lean_object* v_fn_482_, lean_object* v_e_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(v_fn_482_, v_e_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v_e_483_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_object* v_00_u03b1_491_, lean_object* v_x_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_apply_1(v_x_492_, lean_box(0));
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v_00_u03b1_501_, lean_object* v_x_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(v_00_u03b1_501_, v_x_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v___y_503_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(lean_object* v_k_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v_b_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v___x_519_; 
lean_inc(v___y_517_);
lean_inc_ref(v___y_516_);
lean_inc(v___y_515_);
lean_inc_ref(v___y_514_);
lean_inc(v___y_512_);
lean_inc(v___y_511_);
v___x_519_ = lean_apply_8(v_k_510_, v_b_513_, v___y_511_, v___y_512_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, lean_box(0));
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed(lean_object* v_k_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v_b_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(v_k_520_, v___y_521_, v___y_522_, v_b_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_522_);
lean_dec(v___y_521_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(lean_object* v_name_530_, lean_object* v_type_531_, lean_object* v_val_532_, lean_object* v_k_533_, uint8_t v_nondep_534_, uint8_t v_kind_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v___f_543_; lean_object* v___x_544_; 
lean_inc(v___y_537_);
lean_inc(v___y_536_);
v___f_543_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_543_, 0, v_k_533_);
lean_closure_set(v___f_543_, 1, v___y_536_);
lean_closure_set(v___f_543_, 2, v___y_537_);
v___x_544_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_530_, v_type_531_, v_val_532_, v___f_543_, v_nondep_534_, v_kind_535_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
if (lean_obj_tag(v___x_544_) == 0)
{
return v___x_544_;
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_544_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_544_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg___boxed(lean_object* v_name_553_, lean_object* v_type_554_, lean_object* v_val_555_, lean_object* v_k_556_, lean_object* v_nondep_557_, lean_object* v_kind_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
uint8_t v_nondep_boxed_566_; uint8_t v_kind_boxed_567_; lean_object* v_res_568_; 
v_nondep_boxed_566_ = lean_unbox(v_nondep_557_);
v_kind_boxed_567_ = lean_unbox(v_kind_558_);
v_res_568_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_553_, v_type_554_, v_val_555_, v_k_556_, v_nondep_boxed_566_, v_kind_boxed_567_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec(v___y_559_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed(lean_object* v_fvars_569_, lean_object* v_f_570_, lean_object* v_body_571_, lean_object* v_x_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(v_fvars_569_, v_f_570_, v_body_571_, v_x_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec(v___y_573_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(lean_object* v_f_581_, lean_object* v_fvars_582_, lean_object* v_a_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
if (lean_obj_tag(v_a_583_) == 8)
{
lean_object* v_declName_591_; lean_object* v_type_592_; lean_object* v_value_593_; lean_object* v_body_594_; lean_object* v_d_595_; lean_object* v___x_596_; 
v_declName_591_ = lean_ctor_get(v_a_583_, 0);
lean_inc(v_declName_591_);
v_type_592_ = lean_ctor_get(v_a_583_, 1);
lean_inc_ref(v_type_592_);
v_value_593_ = lean_ctor_get(v_a_583_, 2);
lean_inc_ref(v_value_593_);
v_body_594_ = lean_ctor_get(v_a_583_, 3);
lean_inc_ref(v_body_594_);
lean_dec_ref(v_a_583_);
v_d_595_ = lean_expr_instantiate_rev(v_type_592_, v_fvars_582_);
lean_dec_ref(v_type_592_);
lean_inc_ref(v_f_581_);
lean_inc(v___y_589_);
lean_inc_ref(v___y_588_);
lean_inc(v___y_587_);
lean_inc_ref(v___y_586_);
lean_inc(v___y_585_);
lean_inc(v___y_584_);
lean_inc_ref(v_d_595_);
v___x_596_ = lean_apply_8(v_f_581_, v_d_595_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, lean_box(0));
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_v_597_; lean_object* v___x_598_; 
lean_dec_ref(v___x_596_);
v_v_597_ = lean_expr_instantiate_rev(v_value_593_, v_fvars_582_);
lean_dec_ref(v_value_593_);
lean_inc_ref(v_f_581_);
lean_inc(v___y_589_);
lean_inc_ref(v___y_588_);
lean_inc(v___y_587_);
lean_inc_ref(v___y_586_);
lean_inc(v___y_585_);
lean_inc(v___y_584_);
lean_inc_ref(v_v_597_);
v___x_598_ = lean_apply_8(v_f_581_, v_v_597_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, lean_box(0));
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v___f_599_; uint8_t v___x_600_; uint8_t v___x_601_; lean_object* v___x_602_; 
lean_dec_ref(v___x_598_);
v___f_599_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed), 11, 3);
lean_closure_set(v___f_599_, 0, v_fvars_582_);
lean_closure_set(v___f_599_, 1, v_f_581_);
lean_closure_set(v___f_599_, 2, v_body_594_);
v___x_600_ = 0;
v___x_601_ = 0;
v___x_602_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_declName_591_, v_d_595_, v_v_597_, v___f_599_, v___x_600_, v___x_601_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
return v___x_602_;
}
else
{
lean_dec_ref(v_v_597_);
lean_dec_ref(v_d_595_);
lean_dec_ref(v_body_594_);
lean_dec(v_declName_591_);
lean_dec_ref(v_fvars_582_);
lean_dec_ref(v_f_581_);
return v___x_598_;
}
}
else
{
lean_dec_ref(v_d_595_);
lean_dec_ref(v_body_594_);
lean_dec_ref(v_value_593_);
lean_dec(v_declName_591_);
lean_dec_ref(v_fvars_582_);
lean_dec_ref(v_f_581_);
return v___x_596_;
}
}
else
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = lean_expr_instantiate_rev(v_a_583_, v_fvars_582_);
lean_dec_ref(v_fvars_582_);
lean_dec_ref(v_a_583_);
lean_inc(v___y_589_);
lean_inc_ref(v___y_588_);
lean_inc(v___y_587_);
lean_inc_ref(v___y_586_);
lean_inc(v___y_585_);
lean_inc(v___y_584_);
v___x_604_ = lean_apply_8(v_f_581_, v___x_603_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, lean_box(0));
return v___x_604_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(lean_object* v_fvars_605_, lean_object* v_f_606_, lean_object* v_body_607_, lean_object* v_x_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_array_push(v_fvars_605_, v_x_608_);
v___x_617_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_606_, v___x_616_, v_body_607_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___boxed(lean_object* v_f_618_, lean_object* v_fvars_619_, lean_object* v_a_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_618_, v_fvars_619_, v_a_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec(v___y_621_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(lean_object* v_f_631_, lean_object* v_e_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_641_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_631_, v___x_640_, v_e_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___boxed(lean_object* v_f_642_, lean_object* v_e_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v_f_642_, v_e_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec(v___y_644_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(lean_object* v_name_652_, uint8_t v_bi_653_, lean_object* v_type_654_, lean_object* v_k_655_, uint8_t v_kind_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v___f_664_; lean_object* v___x_665_; 
lean_inc(v___y_658_);
lean_inc(v___y_657_);
v___f_664_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_664_, 0, v_k_655_);
lean_closure_set(v___f_664_, 1, v___y_657_);
lean_closure_set(v___f_664_, 2, v___y_658_);
v___x_665_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_652_, v_bi_653_, v_type_654_, v___f_664_, v_kind_656_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
if (lean_obj_tag(v___x_665_) == 0)
{
return v___x_665_;
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_665_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___boxed(lean_object* v_name_674_, lean_object* v_bi_675_, lean_object* v_type_676_, lean_object* v_k_677_, lean_object* v_kind_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
uint8_t v_bi_boxed_686_; uint8_t v_kind_boxed_687_; lean_object* v_res_688_; 
v_bi_boxed_686_ = lean_unbox(v_bi_675_);
v_kind_boxed_687_ = lean_unbox(v_kind_678_);
v_res_688_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_674_, v_bi_boxed_686_, v_type_676_, v_k_677_, v_kind_boxed_687_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec(v___y_679_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed(lean_object* v_fvars_689_, lean_object* v_f_690_, lean_object* v_body_691_, lean_object* v_x_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(v_fvars_689_, v_f_690_, v_body_691_, v_x_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec(v___y_693_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(lean_object* v_f_701_, lean_object* v_fvars_702_, lean_object* v_a_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
if (lean_obj_tag(v_a_703_) == 7)
{
lean_object* v_binderName_711_; lean_object* v_binderType_712_; lean_object* v_body_713_; uint8_t v_binderInfo_714_; lean_object* v_d_715_; lean_object* v___x_716_; 
v_binderName_711_ = lean_ctor_get(v_a_703_, 0);
lean_inc(v_binderName_711_);
v_binderType_712_ = lean_ctor_get(v_a_703_, 1);
lean_inc_ref(v_binderType_712_);
v_body_713_ = lean_ctor_get(v_a_703_, 2);
lean_inc_ref(v_body_713_);
v_binderInfo_714_ = lean_ctor_get_uint8(v_a_703_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_703_);
v_d_715_ = lean_expr_instantiate_rev(v_binderType_712_, v_fvars_702_);
lean_dec_ref(v_binderType_712_);
lean_inc_ref(v_f_701_);
lean_inc(v___y_709_);
lean_inc_ref(v___y_708_);
lean_inc(v___y_707_);
lean_inc_ref(v___y_706_);
lean_inc(v___y_705_);
lean_inc(v___y_704_);
lean_inc_ref(v_d_715_);
v___x_716_ = lean_apply_8(v_f_701_, v_d_715_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, lean_box(0));
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v___f_717_; uint8_t v___x_718_; lean_object* v___x_719_; 
lean_dec_ref(v___x_716_);
v___f_717_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed), 11, 3);
lean_closure_set(v___f_717_, 0, v_fvars_702_);
lean_closure_set(v___f_717_, 1, v_f_701_);
lean_closure_set(v___f_717_, 2, v_body_713_);
v___x_718_ = 0;
v___x_719_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_711_, v_binderInfo_714_, v_d_715_, v___f_717_, v___x_718_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
return v___x_719_;
}
else
{
lean_dec_ref(v_d_715_);
lean_dec_ref(v_body_713_);
lean_dec(v_binderName_711_);
lean_dec_ref(v_fvars_702_);
lean_dec_ref(v_f_701_);
return v___x_716_;
}
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_expr_instantiate_rev(v_a_703_, v_fvars_702_);
lean_dec_ref(v_fvars_702_);
lean_dec_ref(v_a_703_);
lean_inc(v___y_709_);
lean_inc_ref(v___y_708_);
lean_inc(v___y_707_);
lean_inc_ref(v___y_706_);
lean_inc(v___y_705_);
lean_inc(v___y_704_);
v___x_721_ = lean_apply_8(v_f_701_, v___x_720_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, lean_box(0));
return v___x_721_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(lean_object* v_fvars_722_, lean_object* v_f_723_, lean_object* v_body_724_, lean_object* v_x_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = lean_array_push(v_fvars_722_, v_x_725_);
v___x_734_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_723_, v___x_733_, v_body_724_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___boxed(lean_object* v_f_735_, lean_object* v_fvars_736_, lean_object* v_a_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_735_, v_fvars_736_, v_a_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec(v___y_738_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(lean_object* v_f_746_, lean_object* v_e_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_756_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_746_, v___x_755_, v_e_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10___boxed(lean_object* v_f_757_, lean_object* v_e_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v_f_757_, v_e_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec(v___y_759_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed(lean_object* v_fvars_767_, lean_object* v_f_768_, lean_object* v_body_769_, lean_object* v_x_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(v_fvars_767_, v_f_768_, v_body_769_, v_x_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec(v___y_771_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(lean_object* v_f_779_, lean_object* v_fvars_780_, lean_object* v_a_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
if (lean_obj_tag(v_a_781_) == 6)
{
lean_object* v_binderName_789_; lean_object* v_binderType_790_; lean_object* v_body_791_; uint8_t v_binderInfo_792_; lean_object* v_d_793_; lean_object* v___x_794_; 
v_binderName_789_ = lean_ctor_get(v_a_781_, 0);
lean_inc(v_binderName_789_);
v_binderType_790_ = lean_ctor_get(v_a_781_, 1);
lean_inc_ref(v_binderType_790_);
v_body_791_ = lean_ctor_get(v_a_781_, 2);
lean_inc_ref(v_body_791_);
v_binderInfo_792_ = lean_ctor_get_uint8(v_a_781_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_781_);
v_d_793_ = lean_expr_instantiate_rev(v_binderType_790_, v_fvars_780_);
lean_dec_ref(v_binderType_790_);
lean_inc_ref(v_f_779_);
lean_inc(v___y_787_);
lean_inc_ref(v___y_786_);
lean_inc(v___y_785_);
lean_inc_ref(v___y_784_);
lean_inc(v___y_783_);
lean_inc(v___y_782_);
lean_inc_ref(v_d_793_);
v___x_794_ = lean_apply_8(v_f_779_, v_d_793_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, lean_box(0));
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v___f_795_; uint8_t v___x_796_; lean_object* v___x_797_; 
lean_dec_ref(v___x_794_);
v___f_795_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed), 11, 3);
lean_closure_set(v___f_795_, 0, v_fvars_780_);
lean_closure_set(v___f_795_, 1, v_f_779_);
lean_closure_set(v___f_795_, 2, v_body_791_);
v___x_796_ = 0;
v___x_797_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_789_, v_binderInfo_792_, v_d_793_, v___f_795_, v___x_796_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
return v___x_797_;
}
else
{
lean_dec_ref(v_d_793_);
lean_dec_ref(v_body_791_);
lean_dec(v_binderName_789_);
lean_dec_ref(v_fvars_780_);
lean_dec_ref(v_f_779_);
return v___x_794_;
}
}
else
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = lean_expr_instantiate_rev(v_a_781_, v_fvars_780_);
lean_dec_ref(v_fvars_780_);
lean_dec_ref(v_a_781_);
lean_inc(v___y_787_);
lean_inc_ref(v___y_786_);
lean_inc(v___y_785_);
lean_inc_ref(v___y_784_);
lean_inc(v___y_783_);
lean_inc(v___y_782_);
v___x_799_ = lean_apply_8(v_f_779_, v___x_798_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, lean_box(0));
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(lean_object* v_fvars_800_, lean_object* v_f_801_, lean_object* v_body_802_, lean_object* v_x_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_array_push(v_fvars_800_, v_x_803_);
v___x_812_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_801_, v___x_811_, v_body_802_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___boxed(lean_object* v_f_813_, lean_object* v_fvars_814_, lean_object* v_a_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_813_, v_fvars_814_, v_a_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___y_817_);
lean_dec(v___y_816_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(lean_object* v_f_824_, lean_object* v_e_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_834_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_824_, v___x_833_, v_e_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11___boxed(lean_object* v_f_835_, lean_object* v_e_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v_f_835_, v_e_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec(v___y_837_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(lean_object* v_a_845_, lean_object* v_x_846_){
_start:
{
if (lean_obj_tag(v_x_846_) == 0)
{
lean_object* v___x_847_; 
v___x_847_ = lean_box(0);
return v___x_847_;
}
else
{
lean_object* v_key_848_; lean_object* v_value_849_; lean_object* v_tail_850_; uint8_t v___x_851_; 
v_key_848_ = lean_ctor_get(v_x_846_, 0);
v_value_849_ = lean_ctor_get(v_x_846_, 1);
v_tail_850_ = lean_ctor_get(v_x_846_, 2);
v___x_851_ = lean_expr_eqv(v_key_848_, v_a_845_);
if (v___x_851_ == 0)
{
v_x_846_ = v_tail_850_;
goto _start;
}
else
{
lean_object* v___x_853_; 
lean_inc(v_value_849_);
v___x_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_853_, 0, v_value_849_);
return v___x_853_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_a_854_, lean_object* v_x_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_854_, v_x_855_);
lean_dec(v_x_855_);
lean_dec_ref(v_a_854_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_m_857_, lean_object* v_a_858_){
_start:
{
lean_object* v_buckets_859_; lean_object* v___x_860_; uint64_t v___x_861_; uint64_t v___x_862_; uint64_t v___x_863_; uint64_t v_fold_864_; uint64_t v___x_865_; uint64_t v___x_866_; uint64_t v___x_867_; size_t v___x_868_; size_t v___x_869_; size_t v___x_870_; size_t v___x_871_; size_t v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v_buckets_859_ = lean_ctor_get(v_m_857_, 1);
v___x_860_ = lean_array_get_size(v_buckets_859_);
v___x_861_ = l_Lean_Expr_hash(v_a_858_);
v___x_862_ = 32ULL;
v___x_863_ = lean_uint64_shift_right(v___x_861_, v___x_862_);
v_fold_864_ = lean_uint64_xor(v___x_861_, v___x_863_);
v___x_865_ = 16ULL;
v___x_866_ = lean_uint64_shift_right(v_fold_864_, v___x_865_);
v___x_867_ = lean_uint64_xor(v_fold_864_, v___x_866_);
v___x_868_ = lean_uint64_to_usize(v___x_867_);
v___x_869_ = lean_usize_of_nat(v___x_860_);
v___x_870_ = ((size_t)1ULL);
v___x_871_ = lean_usize_sub(v___x_869_, v___x_870_);
v___x_872_ = lean_usize_land(v___x_868_, v___x_871_);
v___x_873_ = lean_array_uget_borrowed(v_buckets_859_, v___x_872_);
v___x_874_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_858_, v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_m_875_, lean_object* v_a_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_875_, v_a_876_);
lean_dec_ref(v_a_876_);
lean_dec_ref(v_m_875_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_object* v_00_u03b1_878_, lean_object* v_x_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = lean_apply_1(v_x_879_, lean_box(0));
v___x_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0___boxed(lean_object* v_00_u03b1_888_, lean_object* v_x_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(v_00_u03b1_888_, v_x_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(lean_object* v_x_897_, lean_object* v_x_898_){
_start:
{
if (lean_obj_tag(v_x_898_) == 0)
{
return v_x_897_;
}
else
{
lean_object* v_key_899_; lean_object* v_value_900_; lean_object* v_tail_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_924_; 
v_key_899_ = lean_ctor_get(v_x_898_, 0);
v_value_900_ = lean_ctor_get(v_x_898_, 1);
v_tail_901_ = lean_ctor_get(v_x_898_, 2);
v_isSharedCheck_924_ = !lean_is_exclusive(v_x_898_);
if (v_isSharedCheck_924_ == 0)
{
v___x_903_ = v_x_898_;
v_isShared_904_ = v_isSharedCheck_924_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_tail_901_);
lean_inc(v_value_900_);
lean_inc(v_key_899_);
lean_dec(v_x_898_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_924_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_905_; uint64_t v___x_906_; uint64_t v___x_907_; uint64_t v___x_908_; uint64_t v_fold_909_; uint64_t v___x_910_; uint64_t v___x_911_; uint64_t v___x_912_; size_t v___x_913_; size_t v___x_914_; size_t v___x_915_; size_t v___x_916_; size_t v___x_917_; lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_905_ = lean_array_get_size(v_x_897_);
v___x_906_ = l_Lean_Expr_hash(v_key_899_);
v___x_907_ = 32ULL;
v___x_908_ = lean_uint64_shift_right(v___x_906_, v___x_907_);
v_fold_909_ = lean_uint64_xor(v___x_906_, v___x_908_);
v___x_910_ = 16ULL;
v___x_911_ = lean_uint64_shift_right(v_fold_909_, v___x_910_);
v___x_912_ = lean_uint64_xor(v_fold_909_, v___x_911_);
v___x_913_ = lean_uint64_to_usize(v___x_912_);
v___x_914_ = lean_usize_of_nat(v___x_905_);
v___x_915_ = ((size_t)1ULL);
v___x_916_ = lean_usize_sub(v___x_914_, v___x_915_);
v___x_917_ = lean_usize_land(v___x_913_, v___x_916_);
v___x_918_ = lean_array_uget_borrowed(v_x_897_, v___x_917_);
lean_inc(v___x_918_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 2, v___x_918_);
v___x_920_ = v___x_903_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_key_899_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_value_900_);
lean_ctor_set(v_reuseFailAlloc_923_, 2, v___x_918_);
v___x_920_ = v_reuseFailAlloc_923_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_921_; 
v___x_921_ = lean_array_uset(v_x_897_, v___x_917_, v___x_920_);
v_x_897_ = v___x_921_;
v_x_898_ = v_tail_901_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(lean_object* v_i_925_, lean_object* v_source_926_, lean_object* v_target_927_){
_start:
{
lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_928_ = lean_array_get_size(v_source_926_);
v___x_929_ = lean_nat_dec_lt(v_i_925_, v___x_928_);
if (v___x_929_ == 0)
{
lean_dec_ref(v_source_926_);
lean_dec(v_i_925_);
return v_target_927_;
}
else
{
lean_object* v_es_930_; lean_object* v___x_931_; lean_object* v_source_932_; lean_object* v_target_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v_es_930_ = lean_array_fget(v_source_926_, v_i_925_);
v___x_931_ = lean_box(0);
v_source_932_ = lean_array_fset(v_source_926_, v_i_925_, v___x_931_);
v_target_933_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_target_927_, v_es_930_);
v___x_934_ = lean_unsigned_to_nat(1u);
v___x_935_ = lean_nat_add(v_i_925_, v___x_934_);
lean_dec(v_i_925_);
v_i_925_ = v___x_935_;
v_source_926_ = v_source_932_;
v_target_927_ = v_target_933_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(lean_object* v_data_937_){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v_nbuckets_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_938_ = lean_array_get_size(v_data_937_);
v___x_939_ = lean_unsigned_to_nat(2u);
v_nbuckets_940_ = lean_nat_mul(v___x_938_, v___x_939_);
v___x_941_ = lean_unsigned_to_nat(0u);
v___x_942_ = lean_box(0);
v___x_943_ = lean_mk_array(v_nbuckets_940_, v___x_942_);
v___x_944_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v___x_941_, v_data_937_, v___x_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(lean_object* v_a_945_, lean_object* v_b_946_, lean_object* v_x_947_){
_start:
{
if (lean_obj_tag(v_x_947_) == 0)
{
lean_dec(v_b_946_);
lean_dec_ref(v_a_945_);
return v_x_947_;
}
else
{
lean_object* v_key_948_; lean_object* v_value_949_; lean_object* v_tail_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_962_; 
v_key_948_ = lean_ctor_get(v_x_947_, 0);
v_value_949_ = lean_ctor_get(v_x_947_, 1);
v_tail_950_ = lean_ctor_get(v_x_947_, 2);
v_isSharedCheck_962_ = !lean_is_exclusive(v_x_947_);
if (v_isSharedCheck_962_ == 0)
{
v___x_952_ = v_x_947_;
v_isShared_953_ = v_isSharedCheck_962_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_tail_950_);
lean_inc(v_value_949_);
lean_inc(v_key_948_);
lean_dec(v_x_947_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_962_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
uint8_t v___x_954_; 
v___x_954_ = lean_expr_eqv(v_key_948_, v_a_945_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; lean_object* v___x_957_; 
v___x_955_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_945_, v_b_946_, v_tail_950_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 2, v___x_955_);
v___x_957_ = v___x_952_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_key_948_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_value_949_);
lean_ctor_set(v_reuseFailAlloc_958_, 2, v___x_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
else
{
lean_object* v___x_960_; 
lean_dec(v_value_949_);
lean_dec(v_key_948_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 1, v_b_946_);
lean_ctor_set(v___x_952_, 0, v_a_945_);
v___x_960_ = v___x_952_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_945_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_b_946_);
lean_ctor_set(v_reuseFailAlloc_961_, 2, v_tail_950_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(lean_object* v_a_963_, lean_object* v_x_964_){
_start:
{
if (lean_obj_tag(v_x_964_) == 0)
{
uint8_t v___x_965_; 
v___x_965_ = 0;
return v___x_965_;
}
else
{
lean_object* v_key_966_; lean_object* v_tail_967_; uint8_t v___x_968_; 
v_key_966_ = lean_ctor_get(v_x_964_, 0);
v_tail_967_ = lean_ctor_get(v_x_964_, 2);
v___x_968_ = lean_expr_eqv(v_key_966_, v_a_963_);
if (v___x_968_ == 0)
{
v_x_964_ = v_tail_967_;
goto _start;
}
else
{
return v___x_968_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg___boxed(lean_object* v_a_970_, lean_object* v_x_971_){
_start:
{
uint8_t v_res_972_; lean_object* v_r_973_; 
v_res_972_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_970_, v_x_971_);
lean_dec(v_x_971_);
lean_dec_ref(v_a_970_);
v_r_973_ = lean_box(v_res_972_);
return v_r_973_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(lean_object* v_m_974_, lean_object* v_a_975_, lean_object* v_b_976_){
_start:
{
lean_object* v_size_977_; lean_object* v_buckets_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_1021_; 
v_size_977_ = lean_ctor_get(v_m_974_, 0);
v_buckets_978_ = lean_ctor_get(v_m_974_, 1);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_m_974_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_980_ = v_m_974_;
v_isShared_981_ = v_isSharedCheck_1021_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_buckets_978_);
lean_inc(v_size_977_);
lean_dec(v_m_974_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_1021_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_982_; uint64_t v___x_983_; uint64_t v___x_984_; uint64_t v___x_985_; uint64_t v_fold_986_; uint64_t v___x_987_; uint64_t v___x_988_; uint64_t v___x_989_; size_t v___x_990_; size_t v___x_991_; size_t v___x_992_; size_t v___x_993_; size_t v___x_994_; lean_object* v_bkt_995_; uint8_t v___x_996_; 
v___x_982_ = lean_array_get_size(v_buckets_978_);
v___x_983_ = l_Lean_Expr_hash(v_a_975_);
v___x_984_ = 32ULL;
v___x_985_ = lean_uint64_shift_right(v___x_983_, v___x_984_);
v_fold_986_ = lean_uint64_xor(v___x_983_, v___x_985_);
v___x_987_ = 16ULL;
v___x_988_ = lean_uint64_shift_right(v_fold_986_, v___x_987_);
v___x_989_ = lean_uint64_xor(v_fold_986_, v___x_988_);
v___x_990_ = lean_uint64_to_usize(v___x_989_);
v___x_991_ = lean_usize_of_nat(v___x_982_);
v___x_992_ = ((size_t)1ULL);
v___x_993_ = lean_usize_sub(v___x_991_, v___x_992_);
v___x_994_ = lean_usize_land(v___x_990_, v___x_993_);
v_bkt_995_ = lean_array_uget_borrowed(v_buckets_978_, v___x_994_);
v___x_996_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_975_, v_bkt_995_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; lean_object* v_size_x27_998_; lean_object* v___x_999_; lean_object* v_buckets_x27_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_997_ = lean_unsigned_to_nat(1u);
v_size_x27_998_ = lean_nat_add(v_size_977_, v___x_997_);
lean_dec(v_size_977_);
lean_inc(v_bkt_995_);
v___x_999_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_999_, 0, v_a_975_);
lean_ctor_set(v___x_999_, 1, v_b_976_);
lean_ctor_set(v___x_999_, 2, v_bkt_995_);
v_buckets_x27_1000_ = lean_array_uset(v_buckets_978_, v___x_994_, v___x_999_);
v___x_1001_ = lean_unsigned_to_nat(4u);
v___x_1002_ = lean_nat_mul(v_size_x27_998_, v___x_1001_);
v___x_1003_ = lean_unsigned_to_nat(3u);
v___x_1004_ = lean_nat_div(v___x_1002_, v___x_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_array_get_size(v_buckets_x27_1000_);
v___x_1006_ = lean_nat_dec_le(v___x_1004_, v___x_1005_);
lean_dec(v___x_1004_);
if (v___x_1006_ == 0)
{
lean_object* v_val_1007_; lean_object* v___x_1009_; 
v_val_1007_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_buckets_x27_1000_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 1, v_val_1007_);
lean_ctor_set(v___x_980_, 0, v_size_x27_998_);
v___x_1009_ = v___x_980_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_size_x27_998_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_val_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
else
{
lean_object* v___x_1012_; 
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 1, v_buckets_x27_1000_);
lean_ctor_set(v___x_980_, 0, v_size_x27_998_);
v___x_1012_ = v___x_980_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_size_x27_998_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_buckets_x27_1000_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
else
{
lean_object* v___x_1014_; lean_object* v_buckets_x27_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1019_; 
lean_inc(v_bkt_995_);
v___x_1014_ = lean_box(0);
v_buckets_x27_1015_ = lean_array_uset(v_buckets_978_, v___x_994_, v___x_1014_);
v___x_1016_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_975_, v_b_976_, v_bkt_995_);
v___x_1017_ = lean_array_uset(v_buckets_x27_1015_, v___x_994_, v___x_1016_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 1, v___x_1017_);
v___x_1019_ = v___x_980_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_size_977_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(lean_object* v_a_1022_, lean_object* v_e_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1026_ = lean_st_ref_take(v_a_1022_);
v___x_1027_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v___x_1026_, v_e_1023_, v_a_1024_);
v___x_1028_ = lean_st_ref_set(v_a_1022_, v___x_1027_);
v___x_1029_ = lean_box(0);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed(lean_object* v_a_1030_, lean_object* v_e_1031_, lean_object* v_a_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(v_a_1030_, v_e_1031_, v_a_1032_);
lean_dec(v_a_1030_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1035_, lean_object* v_e_1036_, lean_object* v_a_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1035_, v_e_1036_, v_a_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec(v_a_1037_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(lean_object* v_fn_1045_, lean_object* v_e_1046_, lean_object* v_a_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_a_1055_; lean_object* v___y_1067_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
lean_inc(v_a_1047_);
v___x_1069_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1069_, 0, lean_box(0));
lean_closure_set(v___x_1069_, 1, lean_box(0));
lean_closure_set(v___x_1069_, 2, v_a_1047_);
v___x_1070_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___x_1069_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1107_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1073_ = v___x_1070_;
v_isShared_1074_ = v_isSharedCheck_1107_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1070_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1107_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_a_1071_, v_e_1046_);
lean_dec(v_a_1071_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v___x_1076_; 
lean_del_object(v___x_1073_);
lean_inc_ref(v_fn_1045_);
lean_inc(v___y_1052_);
lean_inc_ref(v___y_1051_);
lean_inc(v___y_1050_);
lean_inc_ref(v___y_1049_);
lean_inc(v___y_1048_);
lean_inc_ref(v_e_1046_);
v___x_1076_ = lean_apply_7(v_fn_1045_, v_e_1046_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, lean_box(0));
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; uint8_t v___x_1078_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
lean_dec_ref(v___x_1076_);
v___x_1078_ = lean_unbox(v_a_1077_);
lean_dec(v_a_1077_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; 
lean_dec_ref(v_fn_1045_);
v___x_1079_ = lean_box(0);
v_a_1055_ = v___x_1079_;
goto v___jp_1054_;
}
else
{
switch(lean_obj_tag(v_e_1046_))
{
case 7:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1080_, 0, v_fn_1045_);
lean_inc_ref(v_e_1046_);
v___x_1081_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v___x_1080_, v_e_1046_, v_a_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
v___y_1067_ = v___x_1081_;
goto v___jp_1066_;
}
case 6:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1082_, 0, v_fn_1045_);
lean_inc_ref(v_e_1046_);
v___x_1083_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v___x_1082_, v_e_1046_, v_a_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
v___y_1067_ = v___x_1083_;
goto v___jp_1066_;
}
case 8:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1084_, 0, v_fn_1045_);
lean_inc_ref(v_e_1046_);
v___x_1085_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v___x_1084_, v_e_1046_, v_a_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
v___y_1067_ = v___x_1085_;
goto v___jp_1066_;
}
case 5:
{
lean_object* v_fn_1086_; lean_object* v_arg_1087_; lean_object* v___x_1088_; 
v_fn_1086_ = lean_ctor_get(v_e_1046_, 0);
v_arg_1087_ = lean_ctor_get(v_e_1046_, 1);
lean_inc_ref(v_fn_1086_);
lean_inc_ref(v_fn_1045_);
v___x_1088_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1045_, v_fn_1086_, v_a_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v___x_1089_; 
lean_dec_ref(v___x_1088_);
lean_inc_ref(v_arg_1087_);
v___x_1089_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1045_, v_arg_1087_, v_a_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
v___y_1067_ = v___x_1089_;
goto v___jp_1066_;
}
else
{
lean_dec_ref(v_fn_1045_);
v___y_1067_ = v___x_1088_;
goto v___jp_1066_;
}
}
case 10:
{
lean_object* v_expr_1090_; lean_object* v___x_1091_; 
v_expr_1090_ = lean_ctor_get(v_e_1046_, 1);
lean_inc_ref(v_expr_1090_);
v___x_1091_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1045_, v_expr_1090_, v_a_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
v___y_1067_ = v___x_1091_;
goto v___jp_1066_;
}
case 11:
{
lean_object* v_struct_1092_; lean_object* v___x_1093_; 
v_struct_1092_ = lean_ctor_get(v_e_1046_, 2);
lean_inc_ref(v_struct_1092_);
v___x_1093_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1045_, v_struct_1092_, v_a_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
v___y_1067_ = v___x_1093_;
goto v___jp_1066_;
}
default: 
{
lean_object* v___x_1094_; 
lean_dec_ref(v_fn_1045_);
v___x_1094_ = lean_box(0);
v_a_1055_ = v___x_1094_;
goto v___jp_1054_;
}
}
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
lean_dec_ref(v_e_1046_);
lean_dec_ref(v_fn_1045_);
v_a_1095_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1076_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1076_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
else
{
lean_object* v_val_1103_; lean_object* v___x_1105_; 
lean_dec_ref(v_e_1046_);
lean_dec_ref(v_fn_1045_);
v_val_1103_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_val_1103_);
lean_dec_ref(v___x_1075_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 0, v_val_1103_);
v___x_1105_ = v___x_1073_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_val_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec_ref(v_e_1046_);
lean_dec_ref(v_fn_1045_);
v_a_1108_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1070_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1070_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
v___jp_1054_:
{
lean_object* v___f_1056_; lean_object* v___x_1057_; 
lean_inc(v_a_1047_);
v___f_1056_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1056_, 0, v_a_1047_);
lean_closure_set(v___f_1056_, 1, v_e_1046_);
lean_closure_set(v___f_1056_, 2, v_a_1055_);
v___x_1057_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___f_1056_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; 
v_unused_1065_ = lean_ctor_get(v___x_1057_, 0);
lean_dec(v_unused_1065_);
v___x_1059_ = v___x_1057_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_dec(v___x_1057_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 0, v_a_1055_);
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1055_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
else
{
return v___x_1057_;
}
}
v___jp_1066_:
{
if (lean_obj_tag(v___y_1067_) == 0)
{
lean_object* v_a_1068_; 
v_a_1068_ = lean_ctor_get(v___y_1067_, 0);
lean_inc(v_a_1068_);
lean_dec_ref(v___y_1067_);
v_a_1055_ = v_a_1068_;
goto v___jp_1054_;
}
else
{
lean_dec_ref(v_e_1046_);
return v___y_1067_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1116_ = lean_box(0);
v___x_1117_ = lean_unsigned_to_nat(16u);
v___x_1118_ = lean_mk_array(v___x_1117_, v___x_1116_);
return v___x_1118_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1119_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0);
v___x_1120_ = lean_unsigned_to_nat(0u);
v___x_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
lean_ctor_set(v___x_1121_, 1, v___x_1119_);
return v___x_1121_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1);
v___x_1123_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1123_, 0, lean_box(0));
lean_closure_set(v___x_1123_, 1, lean_box(0));
lean_closure_set(v___x_1123_, 2, v___x_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(lean_object* v_input_1124_, lean_object* v_fn_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v_a_1134_; lean_object* v___x_1135_; 
v___x_1132_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2);
v___x_1133_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1132_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1134_);
lean_dec_ref(v___x_1133_);
v___x_1135_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1125_, v_input_1124_, v_a_1134_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1136_);
lean_dec_ref(v___x_1135_);
v___x_1137_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1137_, 0, lean_box(0));
lean_closure_set(v___x_1137_, 1, lean_box(0));
lean_closure_set(v___x_1137_, 2, v_a_1134_);
v___x_1138_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1137_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1145_ == 0)
{
lean_object* v_unused_1146_; 
v_unused_1146_ = lean_ctor_get(v___x_1138_, 0);
lean_dec(v_unused_1146_);
v___x_1140_ = v___x_1138_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_dec(v___x_1138_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v_a_1136_);
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1136_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
else
{
lean_dec(v_a_1134_);
return v___x_1135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___boxed(lean_object* v_input_1147_, lean_object* v_fn_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1147_, v_fn_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(lean_object* v_input_1156_, lean_object* v_fn_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v___f_1164_; lean_object* v___x_1165_; 
v___f_1164_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1164_, 0, v_fn_1157_);
v___x_1165_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1156_, v___f_1164_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___boxed(lean_object* v_input_1166_, lean_object* v_fn_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_input_1166_, v_fn_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(lean_object* v_fn_1175_, lean_object* v_x_1176_, lean_object* v_x_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
if (lean_obj_tag(v_x_1177_) == 0)
{
lean_object* v___x_1184_; 
lean_dec_ref(v_fn_1175_);
v___x_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1184_, 0, v_x_1176_);
return v___x_1184_;
}
else
{
lean_object* v_head_1185_; lean_object* v_tail_1186_; lean_object* v_type_1187_; lean_object* v___x_1188_; 
v_head_1185_ = lean_ctor_get(v_x_1177_, 0);
lean_inc(v_head_1185_);
v_tail_1186_ = lean_ctor_get(v_x_1177_, 1);
lean_inc(v_tail_1186_);
lean_dec_ref(v_x_1177_);
v_type_1187_ = lean_ctor_get(v_head_1185_, 1);
lean_inc_ref(v_type_1187_);
lean_dec(v_head_1185_);
lean_inc_ref(v_fn_1175_);
v___x_1188_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1187_, v_fn_1175_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_a_1189_);
lean_dec_ref(v___x_1188_);
v_x_1176_ = v_a_1189_;
v_x_1177_ = v_tail_1186_;
goto _start;
}
else
{
lean_dec(v_tail_1186_);
lean_dec_ref(v_fn_1175_);
return v___x_1188_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4___boxed(lean_object* v_fn_1191_, lean_object* v_x_1192_, lean_object* v_x_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1191_, v_x_1192_, v_x_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(lean_object* v_fn_1201_, lean_object* v_x_1202_, lean_object* v_x_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
if (lean_obj_tag(v_x_1203_) == 0)
{
lean_object* v___x_1210_; 
lean_dec_ref(v_fn_1201_);
v___x_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1210_, 0, v_x_1202_);
return v___x_1210_;
}
else
{
lean_object* v_head_1211_; lean_object* v_tail_1212_; lean_object* v___y_1214_; lean_object* v_type_1217_; lean_object* v_ctors_1218_; lean_object* v___x_1219_; 
v_head_1211_ = lean_ctor_get(v_x_1203_, 0);
lean_inc(v_head_1211_);
v_tail_1212_ = lean_ctor_get(v_x_1203_, 1);
lean_inc(v_tail_1212_);
lean_dec_ref(v_x_1203_);
v_type_1217_ = lean_ctor_get(v_head_1211_, 1);
lean_inc_ref(v_type_1217_);
v_ctors_1218_ = lean_ctor_get(v_head_1211_, 2);
lean_inc(v_ctors_1218_);
lean_dec(v_head_1211_);
lean_inc_ref(v_fn_1201_);
v___x_1219_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1217_, v_fn_1201_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1220_; lean_object* v___x_1221_; 
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_a_1220_);
lean_dec_ref(v___x_1219_);
lean_inc_ref(v_fn_1201_);
v___x_1221_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1201_, v_a_1220_, v_ctors_1218_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
v___y_1214_ = v___x_1221_;
goto v___jp_1213_;
}
else
{
lean_dec(v_ctors_1218_);
v___y_1214_ = v___x_1219_;
goto v___jp_1213_;
}
v___jp_1213_:
{
if (lean_obj_tag(v___y_1214_) == 0)
{
lean_object* v_a_1215_; 
v_a_1215_ = lean_ctor_get(v___y_1214_, 0);
lean_inc(v_a_1215_);
lean_dec_ref(v___y_1214_);
v_x_1202_ = v_a_1215_;
v_x_1203_ = v_tail_1212_;
goto _start;
}
else
{
lean_dec(v_tail_1212_);
lean_dec_ref(v_fn_1201_);
return v___y_1214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6___boxed(lean_object* v_fn_1222_, lean_object* v_x_1223_, lean_object* v_x_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1222_, v_x_1223_, v_x_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(lean_object* v_fn_1232_, lean_object* v_x_1233_, lean_object* v_x_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
if (lean_obj_tag(v_x_1234_) == 0)
{
lean_object* v___x_1241_; 
lean_dec_ref(v_fn_1232_);
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v_x_1233_);
return v___x_1241_;
}
else
{
lean_object* v_head_1242_; lean_object* v_tail_1243_; lean_object* v___y_1245_; lean_object* v_toConstantVal_1248_; lean_object* v_value_1249_; lean_object* v_type_1250_; lean_object* v___x_1251_; 
v_head_1242_ = lean_ctor_get(v_x_1234_, 0);
lean_inc(v_head_1242_);
v_tail_1243_ = lean_ctor_get(v_x_1234_, 1);
lean_inc(v_tail_1243_);
lean_dec_ref(v_x_1234_);
v_toConstantVal_1248_ = lean_ctor_get(v_head_1242_, 0);
lean_inc_ref(v_toConstantVal_1248_);
v_value_1249_ = lean_ctor_get(v_head_1242_, 1);
lean_inc_ref(v_value_1249_);
lean_dec(v_head_1242_);
v_type_1250_ = lean_ctor_get(v_toConstantVal_1248_, 2);
lean_inc_ref(v_type_1250_);
lean_dec_ref(v_toConstantVal_1248_);
lean_inc_ref(v_fn_1232_);
v___x_1251_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1250_, v_fn_1232_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v___x_1252_; 
lean_dec_ref(v___x_1251_);
lean_inc_ref(v_fn_1232_);
v___x_1252_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1249_, v_fn_1232_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
v___y_1245_ = v___x_1252_;
goto v___jp_1244_;
}
else
{
lean_dec_ref(v_value_1249_);
v___y_1245_ = v___x_1251_;
goto v___jp_1244_;
}
v___jp_1244_:
{
if (lean_obj_tag(v___y_1245_) == 0)
{
lean_object* v_a_1246_; 
v_a_1246_ = lean_ctor_get(v___y_1245_, 0);
lean_inc(v_a_1246_);
lean_dec_ref(v___y_1245_);
v_x_1233_ = v_a_1246_;
v_x_1234_ = v_tail_1243_;
goto _start;
}
else
{
lean_dec(v_tail_1243_);
lean_dec_ref(v_fn_1232_);
return v___y_1245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1253_, lean_object* v_x_1254_, lean_object* v_x_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1253_, v_x_1254_, v_x_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(lean_object* v_fn_1263_, lean_object* v_d_1264_, lean_object* v_a_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
switch(lean_obj_tag(v_d_1264_))
{
case 0:
{
lean_object* v_val_1272_; lean_object* v_toConstantVal_1273_; lean_object* v_type_1274_; lean_object* v___x_1275_; 
v_val_1272_ = lean_ctor_get(v_d_1264_, 0);
lean_inc_ref(v_val_1272_);
lean_dec_ref(v_d_1264_);
v_toConstantVal_1273_ = lean_ctor_get(v_val_1272_, 0);
lean_inc_ref(v_toConstantVal_1273_);
lean_dec_ref(v_val_1272_);
v_type_1274_ = lean_ctor_get(v_toConstantVal_1273_, 2);
lean_inc_ref(v_type_1274_);
lean_dec_ref(v_toConstantVal_1273_);
v___x_1275_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1274_, v_fn_1263_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
return v___x_1275_;
}
case 4:
{
lean_object* v___x_1276_; 
lean_dec_ref(v_fn_1263_);
v___x_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1276_, 0, v_a_1265_);
return v___x_1276_;
}
case 5:
{
lean_object* v_defns_1277_; lean_object* v___x_1278_; 
v_defns_1277_ = lean_ctor_get(v_d_1264_, 0);
lean_inc(v_defns_1277_);
lean_dec_ref(v_d_1264_);
v___x_1278_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1263_, v_a_1265_, v_defns_1277_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
return v___x_1278_;
}
case 6:
{
lean_object* v_types_1279_; lean_object* v___x_1280_; 
v_types_1279_ = lean_ctor_get(v_d_1264_, 2);
lean_inc(v_types_1279_);
lean_dec_ref(v_d_1264_);
v___x_1280_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1263_, v_a_1265_, v_types_1279_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
return v___x_1280_;
}
default: 
{
lean_object* v_val_1281_; lean_object* v_toConstantVal_1282_; lean_object* v_value_1283_; lean_object* v_type_1284_; lean_object* v___x_1285_; 
v_val_1281_ = lean_ctor_get(v_d_1264_, 0);
lean_inc_ref(v_val_1281_);
lean_dec(v_d_1264_);
v_toConstantVal_1282_ = lean_ctor_get(v_val_1281_, 0);
lean_inc_ref(v_toConstantVal_1282_);
v_value_1283_ = lean_ctor_get(v_val_1281_, 1);
lean_inc_ref(v_value_1283_);
lean_dec_ref(v_val_1281_);
v_type_1284_ = lean_ctor_get(v_toConstantVal_1282_, 2);
lean_inc_ref(v_type_1284_);
lean_dec_ref(v_toConstantVal_1282_);
lean_inc_ref(v_fn_1263_);
v___x_1285_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1284_, v_fn_1263_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v___x_1286_; 
lean_dec_ref(v___x_1285_);
v___x_1286_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1283_, v_fn_1263_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
return v___x_1286_;
}
else
{
lean_dec_ref(v_value_1283_);
lean_dec_ref(v_fn_1263_);
return v___x_1285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2___boxed(lean_object* v_fn_1287_, lean_object* v_d_1288_, lean_object* v_a_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1287_, v_d_1288_, v_a_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(lean_object* v_decl_1297_, lean_object* v_fn_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = lean_box(0);
v___x_1306_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1298_, v_decl_1297_, v___x_1305_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1___boxed(lean_object* v_decl_1307_, lean_object* v_fn_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1307_, v_fn_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
return v_res_1315_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__0(void){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1316_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__1(void){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__0, &l_Lean_warnIfUsesSorry___closed__0_once, _init_l_Lean_warnIfUsesSorry___closed__0);
v___x_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1317_);
return v___x_1318_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__2(void){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1319_ = lean_box(1);
v___x_1320_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_1321_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1322_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
lean_ctor_set(v___x_1322_, 1, v___x_1320_);
lean_ctor_set(v___x_1322_, 2, v___x_1319_);
return v___x_1322_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__4(void){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1325_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1326_ = lean_unsigned_to_nat(0u);
v___x_1327_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
lean_ctor_set(v___x_1327_, 1, v___x_1326_);
lean_ctor_set(v___x_1327_, 2, v___x_1326_);
lean_ctor_set(v___x_1327_, 3, v___x_1326_);
lean_ctor_set(v___x_1327_, 4, v___x_1325_);
lean_ctor_set(v___x_1327_, 5, v___x_1325_);
lean_ctor_set(v___x_1327_, 6, v___x_1325_);
lean_ctor_set(v___x_1327_, 7, v___x_1325_);
lean_ctor_set(v___x_1327_, 8, v___x_1325_);
lean_ctor_set(v___x_1327_, 9, v___x_1325_);
return v___x_1327_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__5(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1329_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
lean_ctor_set(v___x_1329_, 1, v___x_1328_);
lean_ctor_set(v___x_1329_, 2, v___x_1328_);
lean_ctor_set(v___x_1329_, 3, v___x_1328_);
lean_ctor_set(v___x_1329_, 4, v___x_1328_);
lean_ctor_set(v___x_1329_, 5, v___x_1328_);
return v___x_1329_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__6(void){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
lean_ctor_set(v___x_1331_, 2, v___x_1330_);
lean_ctor_set(v___x_1331_, 3, v___x_1330_);
lean_ctor_set(v___x_1331_, 4, v___x_1330_);
return v___x_1331_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__7(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1332_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__6, &l_Lean_warnIfUsesSorry___closed__6_once, _init_l_Lean_warnIfUsesSorry___closed__6);
v___x_1333_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_1334_ = lean_box(1);
v___x_1335_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__5, &l_Lean_warnIfUsesSorry___closed__5_once, _init_l_Lean_warnIfUsesSorry___closed__5);
v___x_1336_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__4, &l_Lean_warnIfUsesSorry___closed__4_once, _init_l_Lean_warnIfUsesSorry___closed__4);
v___x_1337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
lean_ctor_set(v___x_1337_, 1, v___x_1335_);
lean_ctor_set(v___x_1337_, 2, v___x_1334_);
lean_ctor_set(v___x_1337_, 3, v___x_1333_);
lean_ctor_set(v___x_1337_, 4, v___x_1332_);
return v___x_1337_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__12(void){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__11));
v___x_1344_ = l_Lean_stringToMessageData(v___x_1343_);
return v___x_1344_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__14(void){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__13));
v___x_1347_ = l_Lean_stringToMessageData(v___x_1346_);
return v___x_1347_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__16(void){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__15));
v___x_1350_ = l_Lean_stringToMessageData(v___x_1349_);
return v___x_1350_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__17(void){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1351_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__16, &l_Lean_warnIfUsesSorry___closed__16_once, _init_l_Lean_warnIfUsesSorry___closed__16);
v___x_1352_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__10));
v___x_1353_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
lean_ctor_set(v___x_1353_, 1, v___x_1351_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry(lean_object* v_decl_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v_options_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v_options_1361_ = lean_ctor_get(v_a_1358_, 2);
v___x_1362_ = l_Lean_warn_sorry;
v___x_1363_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_1361_, v___x_1362_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
lean_dec(v_decl_1357_);
v___x_1364_ = lean_box(0);
v___x_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
return v___x_1365_;
}
else
{
lean_object* v___x_1366_; lean_object* v_messages_1370_; uint8_t v___x_1371_; 
v___x_1366_ = lean_st_ref_get(v_a_1359_);
v_messages_1370_ = lean_ctor_get(v___x_1366_, 6);
lean_inc_ref(v_messages_1370_);
lean_dec(v___x_1366_);
v___x_1371_ = l_Lean_MessageLog_hasErrors(v_messages_1370_);
lean_dec_ref(v_messages_1370_);
if (v___x_1371_ == 0)
{
if (v___x_1363_ == 0)
{
lean_dec(v_decl_1357_);
goto v___jp_1367_;
}
else
{
uint8_t v___x_1372_; 
v___x_1372_ = l_Lean_Declaration_hasSorry(v_decl_1357_);
if (v___x_1372_ == 0)
{
lean_dec(v_decl_1357_);
goto v___jp_1367_;
}
else
{
uint8_t v___x_1373_; uint8_t v___x_1374_; uint8_t v___x_1375_; lean_object* v___x_1376_; uint64_t v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___f_1388_; lean_object* v___x_1389_; 
v___x_1373_ = 1;
v___x_1374_ = 0;
v___x_1375_ = 2;
v___x_1376_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_1376_, 0, v___x_1371_);
lean_ctor_set_uint8(v___x_1376_, 1, v___x_1371_);
lean_ctor_set_uint8(v___x_1376_, 2, v___x_1371_);
lean_ctor_set_uint8(v___x_1376_, 3, v___x_1371_);
lean_ctor_set_uint8(v___x_1376_, 4, v___x_1371_);
lean_ctor_set_uint8(v___x_1376_, 5, v___x_1372_);
lean_ctor_set_uint8(v___x_1376_, 6, v___x_1372_);
lean_ctor_set_uint8(v___x_1376_, 7, v___x_1371_);
lean_ctor_set_uint8(v___x_1376_, 8, v___x_1372_);
lean_ctor_set_uint8(v___x_1376_, 9, v___x_1373_);
lean_ctor_set_uint8(v___x_1376_, 10, v___x_1374_);
lean_ctor_set_uint8(v___x_1376_, 11, v___x_1372_);
lean_ctor_set_uint8(v___x_1376_, 12, v___x_1372_);
lean_ctor_set_uint8(v___x_1376_, 13, v___x_1372_);
lean_ctor_set_uint8(v___x_1376_, 14, v___x_1375_);
lean_ctor_set_uint8(v___x_1376_, 15, v___x_1372_);
lean_ctor_set_uint8(v___x_1376_, 16, v___x_1372_);
lean_ctor_set_uint8(v___x_1376_, 17, v___x_1372_);
lean_ctor_set_uint8(v___x_1376_, 18, v___x_1372_);
v___x_1377_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1376_);
v___x_1378_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1378_, 0, v___x_1376_);
lean_ctor_set_uint64(v___x_1378_, sizeof(void*)*1, v___x_1377_);
v___x_1379_ = lean_box(1);
v___x_1380_ = lean_unsigned_to_nat(0u);
v___x_1381_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1382_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__3));
v___x_1383_ = lean_box(0);
v___x_1384_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1384_, 0, v___x_1378_);
lean_ctor_set(v___x_1384_, 1, v___x_1379_);
lean_ctor_set(v___x_1384_, 2, v___x_1381_);
lean_ctor_set(v___x_1384_, 3, v___x_1382_);
lean_ctor_set(v___x_1384_, 4, v___x_1383_);
lean_ctor_set(v___x_1384_, 5, v___x_1380_);
lean_ctor_set(v___x_1384_, 6, v___x_1383_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*7, v___x_1371_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*7 + 1, v___x_1371_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*7 + 2, v___x_1371_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*7 + 3, v___x_1363_);
v___x_1385_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__7, &l_Lean_warnIfUsesSorry___closed__7_once, _init_l_Lean_warnIfUsesSorry___closed__7);
v___x_1386_ = lean_st_mk_ref(v___x_1385_);
v___x_1387_ = lean_st_mk_ref(v___x_1382_);
v___f_1388_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__8));
v___x_1389_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1357_, v___f_1388_, v___x_1387_, v___x_1384_, v___x_1386_, v_a_1358_, v_a_1359_);
lean_dec_ref(v___x_1384_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v_val_1393_; lean_object* v___x_1415_; size_t v_sz_1416_; size_t v___x_1417_; lean_object* v___x_1418_; lean_object* v_fst_1419_; 
lean_dec_ref(v___x_1389_);
v___x_1390_ = lean_st_ref_get(v___x_1387_);
lean_dec(v___x_1387_);
v___x_1391_ = lean_st_ref_get(v___x_1386_);
lean_dec(v___x_1386_);
lean_dec(v___x_1391_);
v___x_1415_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__18));
v_sz_1416_ = lean_array_size(v___x_1390_);
v___x_1417_ = ((size_t)0ULL);
v___x_1418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v___x_1390_, v_sz_1416_, v___x_1417_, v___x_1415_);
v_fst_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_fst_1419_);
lean_dec_ref(v___x_1418_);
if (lean_obj_tag(v_fst_1419_) == 0)
{
goto v___jp_1409_;
}
else
{
lean_object* v_val_1420_; 
v_val_1420_ = lean_ctor_get(v_fst_1419_, 0);
lean_inc(v_val_1420_);
lean_dec_ref(v_fst_1419_);
if (lean_obj_tag(v_val_1420_) == 0)
{
goto v___jp_1409_;
}
else
{
lean_object* v_val_1421_; 
lean_dec(v___x_1390_);
v_val_1421_ = lean_ctor_get(v_val_1420_, 0);
lean_inc(v_val_1421_);
lean_dec_ref(v_val_1420_);
v_val_1393_ = v_val_1421_;
goto v___jp_1392_;
}
}
v___jp_1392_:
{
lean_object* v_snd_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1407_; 
v_snd_1394_ = lean_ctor_get(v_val_1393_, 1);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_val_1393_);
if (v_isSharedCheck_1407_ == 0)
{
lean_object* v_unused_1408_; 
v_unused_1408_ = lean_ctor_get(v_val_1393_, 0);
lean_dec(v_unused_1408_);
v___x_1396_ = v_val_1393_;
v_isShared_1397_ = v_isSharedCheck_1407_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_snd_1394_);
lean_dec(v_val_1393_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1407_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1401_; 
v___x_1398_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__10));
v___x_1399_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__12, &l_Lean_warnIfUsesSorry___closed__12_once, _init_l_Lean_warnIfUsesSorry___closed__12);
if (v_isShared_1397_ == 0)
{
lean_ctor_set_tag(v___x_1396_, 7);
lean_ctor_set(v___x_1396_, 0, v___x_1399_);
v___x_1401_ = v___x_1396_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1399_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_snd_1394_);
v___x_1401_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1402_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__14, &l_Lean_warnIfUsesSorry___closed__14_once, _init_l_Lean_warnIfUsesSorry___closed__14);
v___x_1403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1401_);
lean_ctor_set(v___x_1403_, 1, v___x_1402_);
v___x_1404_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1398_);
lean_ctor_set(v___x_1404_, 1, v___x_1403_);
v___x_1405_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1404_, v_a_1358_, v_a_1359_);
return v___x_1405_;
}
}
}
v___jp_1409_:
{
lean_object* v___x_1410_; uint8_t v___x_1411_; 
v___x_1410_ = lean_array_get_size(v___x_1390_);
v___x_1411_ = lean_nat_dec_lt(v___x_1380_, v___x_1410_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
lean_dec(v___x_1390_);
v___x_1412_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__17, &l_Lean_warnIfUsesSorry___closed__17_once, _init_l_Lean_warnIfUsesSorry___closed__17);
v___x_1413_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1412_, v_a_1358_, v_a_1359_);
return v___x_1413_;
}
else
{
lean_object* v___x_1414_; 
v___x_1414_ = lean_array_fget(v___x_1390_, v___x_1380_);
lean_dec(v___x_1390_);
v_val_1393_ = v___x_1414_;
goto v___jp_1392_;
}
}
}
else
{
lean_dec(v___x_1387_);
lean_dec(v___x_1386_);
return v___x_1389_;
}
}
}
}
else
{
lean_dec(v_decl_1357_);
goto v___jp_1367_;
}
v___jp_1367_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_box(0);
v___x_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
return v___x_1369_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___boxed(lean_object* v_decl_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_warnIfUsesSorry(v_decl_1422_, v_a_1423_, v_a_1424_);
lean_dec(v_a_1424_);
lean_dec_ref(v_a_1423_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1427_, lean_object* v_m_1428_, lean_object* v_a_1429_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1428_, v_a_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1431_, lean_object* v_m_1432_, lean_object* v_a_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(v_00_u03b2_1431_, v_m_1432_, v_a_1433_);
lean_dec_ref(v_a_1433_);
lean_dec_ref(v_m_1432_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_1435_, lean_object* v_m_1436_, lean_object* v_a_1437_, lean_object* v_b_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_m_1436_, v_a_1437_, v_b_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_1440_, lean_object* v_a_1441_, lean_object* v_x_1442_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1441_, v_x_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1444_, lean_object* v_a_1445_, lean_object* v_x_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(v_00_u03b2_1444_, v_a_1445_, v_x_1446_);
lean_dec(v_x_1446_);
lean_dec_ref(v_a_1445_);
return v_res_1447_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(lean_object* v_00_u03b2_1448_, lean_object* v_a_1449_, lean_object* v_x_1450_){
_start:
{
uint8_t v___x_1451_; 
v___x_1451_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1449_, v_x_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___boxed(lean_object* v_00_u03b2_1452_, lean_object* v_a_1453_, lean_object* v_x_1454_){
_start:
{
uint8_t v_res_1455_; lean_object* v_r_1456_; 
v_res_1455_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(v_00_u03b2_1452_, v_a_1453_, v_x_1454_);
lean_dec(v_x_1454_);
lean_dec_ref(v_a_1453_);
v_r_1456_ = lean_box(v_res_1455_);
return v_r_1456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17(lean_object* v_00_u03b2_1457_, lean_object* v_data_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_data_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18(lean_object* v_00_u03b2_1460_, lean_object* v_a_1461_, lean_object* v_b_1462_, lean_object* v_x_1463_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1461_, v_b_1462_, v_x_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(lean_object* v_00_u03b1_1465_, lean_object* v_name_1466_, uint8_t v_bi_1467_, lean_object* v_type_1468_, lean_object* v_k_1469_, uint8_t v_kind_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_1466_, v_bi_1467_, v_type_1468_, v_k_1469_, v_kind_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___boxed(lean_object* v_00_u03b1_1479_, lean_object* v_name_1480_, lean_object* v_bi_1481_, lean_object* v_type_1482_, lean_object* v_k_1483_, lean_object* v_kind_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
uint8_t v_bi_boxed_1492_; uint8_t v_kind_boxed_1493_; lean_object* v_res_1494_; 
v_bi_boxed_1492_ = lean_unbox(v_bi_1481_);
v_kind_boxed_1493_ = lean_unbox(v_kind_1484_);
v_res_1494_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(v_00_u03b1_1479_, v_name_1480_, v_bi_boxed_1492_, v_type_1482_, v_k_1483_, v_kind_boxed_1493_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec(v___y_1485_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(lean_object* v_00_u03b1_1495_, lean_object* v_name_1496_, lean_object* v_type_1497_, lean_object* v_val_1498_, lean_object* v_k_1499_, uint8_t v_nondep_1500_, uint8_t v_kind_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_1496_, v_type_1497_, v_val_1498_, v_k_1499_, v_nondep_1500_, v_kind_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___boxed(lean_object* v_00_u03b1_1510_, lean_object* v_name_1511_, lean_object* v_type_1512_, lean_object* v_val_1513_, lean_object* v_k_1514_, lean_object* v_nondep_1515_, lean_object* v_kind_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
uint8_t v_nondep_boxed_1524_; uint8_t v_kind_boxed_1525_; lean_object* v_res_1526_; 
v_nondep_boxed_1524_ = lean_unbox(v_nondep_1515_);
v_kind_boxed_1525_ = lean_unbox(v_kind_1516_);
v_res_1526_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(v_00_u03b1_1510_, v_name_1511_, v_type_1512_, v_val_1513_, v_k_1514_, v_nondep_boxed_1524_, v_kind_boxed_1525_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec(v___y_1517_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18(lean_object* v_00_u03b2_1527_, lean_object* v_i_1528_, lean_object* v_source_1529_, lean_object* v_target_1530_){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v_i_1528_, v_source_1529_, v_target_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22(lean_object* v_00_u03b2_1532_, lean_object* v_x_1533_, lean_object* v_x_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_x_1533_, v_x_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1585_; uint8_t v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1585_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1586_ = 0;
v___x_1587_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__20_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1588_ = l_Lean_registerTraceClass(v___x_1585_, v___x_1586_, v___x_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2____boxed(lean_object* v_a_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_();
return v_res_1590_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1591_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__0);
v___x_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1592_);
return v___x_1593_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__1);
v___x_1595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1594_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(lean_object* v_env_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v___x_1599_; lean_object* v_nextMacroScope_1600_; lean_object* v_ngen_1601_; lean_object* v_auxDeclNGen_1602_; lean_object* v_traceState_1603_; lean_object* v_messages_1604_; lean_object* v_infoState_1605_; lean_object* v_snapshotTasks_1606_; lean_object* v_newDecls_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1618_; 
v___x_1599_ = lean_st_ref_take(v___y_1597_);
v_nextMacroScope_1600_ = lean_ctor_get(v___x_1599_, 1);
v_ngen_1601_ = lean_ctor_get(v___x_1599_, 2);
v_auxDeclNGen_1602_ = lean_ctor_get(v___x_1599_, 3);
v_traceState_1603_ = lean_ctor_get(v___x_1599_, 4);
v_messages_1604_ = lean_ctor_get(v___x_1599_, 6);
v_infoState_1605_ = lean_ctor_get(v___x_1599_, 7);
v_snapshotTasks_1606_ = lean_ctor_get(v___x_1599_, 8);
v_newDecls_1607_ = lean_ctor_get(v___x_1599_, 9);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1618_ == 0)
{
lean_object* v_unused_1619_; lean_object* v_unused_1620_; 
v_unused_1619_ = lean_ctor_get(v___x_1599_, 5);
lean_dec(v_unused_1619_);
v_unused_1620_ = lean_ctor_get(v___x_1599_, 0);
lean_dec(v_unused_1620_);
v___x_1609_ = v___x_1599_;
v_isShared_1610_ = v_isSharedCheck_1618_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_newDecls_1607_);
lean_inc(v_snapshotTasks_1606_);
lean_inc(v_infoState_1605_);
lean_inc(v_messages_1604_);
lean_inc(v_traceState_1603_);
lean_inc(v_auxDeclNGen_1602_);
lean_inc(v_ngen_1601_);
lean_inc(v_nextMacroScope_1600_);
lean_dec(v___x_1599_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1618_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1611_; lean_object* v___x_1613_; 
v___x_1611_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 5, v___x_1611_);
lean_ctor_set(v___x_1609_, 0, v_env_1596_);
v___x_1613_ = v___x_1609_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_env_1596_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_nextMacroScope_1600_);
lean_ctor_set(v_reuseFailAlloc_1617_, 2, v_ngen_1601_);
lean_ctor_set(v_reuseFailAlloc_1617_, 3, v_auxDeclNGen_1602_);
lean_ctor_set(v_reuseFailAlloc_1617_, 4, v_traceState_1603_);
lean_ctor_set(v_reuseFailAlloc_1617_, 5, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1617_, 6, v_messages_1604_);
lean_ctor_set(v_reuseFailAlloc_1617_, 7, v_infoState_1605_);
lean_ctor_set(v_reuseFailAlloc_1617_, 8, v_snapshotTasks_1606_);
lean_ctor_set(v_reuseFailAlloc_1617_, 9, v_newDecls_1607_);
v___x_1613_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1614_ = lean_st_ref_set(v___y_1597_, v___x_1613_);
v___x_1615_ = lean_box(0);
v___x_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
return v___x_1616_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___boxed(lean_object* v_env_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_env_1621_, v___y_1622_);
lean_dec(v___y_1622_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1(lean_object* v_env_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_env_1625_, v___y_1627_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___boxed(lean_object* v_env_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1(v_env_1630_, v___y_1631_, v___y_1632_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2___redArg(lean_object* v_msg_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v_ref_1639_; lean_object* v___x_1640_; lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1649_; 
v_ref_1639_ = lean_ctor_get(v___y_1636_, 5);
v___x_1640_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_1635_, v___y_1636_, v___y_1637_);
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1643_ = v___x_1640_;
v_isShared_1644_ = v_isSharedCheck_1649_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1640_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1649_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1645_; lean_object* v___x_1647_; 
lean_inc(v_ref_1639_);
v___x_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1645_, 0, v_ref_1639_);
lean_ctor_set(v___x_1645_, 1, v_a_1641_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set_tag(v___x_1643_, 1);
lean_ctor_set(v___x_1643_, 0, v___x_1645_);
v___x_1647_ = v___x_1643_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1645_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msg_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_1650_, v___y_1651_, v___y_1652_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
return v_res_1654_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1655_ = lean_box(0);
v___x_1656_ = l_Lean_interruptExceptionId;
v___x_1657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
lean_ctor_set(v___x_1657_, 1, v___x_1655_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg(){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1659_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v___y_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(lean_object* v_ex_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v___y_1668_; lean_object* v___y_1669_; 
if (lean_obj_tag(v_ex_1663_) == 16)
{
lean_object* v___x_1673_; lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
v___x_1673_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg();
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1673_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1673_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
else
{
v___y_1668_ = v___y_1664_;
v___y_1669_ = v___y_1665_;
goto v___jp_1667_;
}
v___jp_1667_:
{
lean_object* v_options_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v_options_1670_ = lean_ctor_get(v___y_1668_, 2);
lean_inc_ref(v_options_1670_);
v___x_1671_ = l_Lean_Kernel_Exception_toMessageData(v_ex_1663_, v_options_1670_);
v___x_1672_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2___redArg(v___x_1671_, v___y_1668_, v___y_1669_);
return v___x_1672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg___boxed(lean_object* v_ex_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(v_ex_1682_, v___y_1683_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(lean_object* v_x_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
if (lean_obj_tag(v_x_1687_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1692_; 
v_a_1691_ = lean_ctor_get(v_x_1687_, 0);
lean_inc(v_a_1691_);
lean_dec_ref(v_x_1687_);
v___x_1692_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(v_a_1691_, v___y_1688_, v___y_1689_);
return v___x_1692_;
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
v_a_1693_ = lean_ctor_get(v_x_1687_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v_x_1687_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v_x_1687_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
lean_ctor_set_tag(v___x_1695_, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg___boxed(lean_object* v_x_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v_x_1701_, v___y_1702_, v___y_1703_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
return v_res_1705_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = lean_unsigned_to_nat(1u);
v___x_1707_ = l_Lean_Level_ofNat(v___x_1706_);
return v___x_1707_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1708_ = lean_box(0);
v___x_1709_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__0);
v___x_1710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
lean_ctor_set(v___x_1710_, 1, v___x_1708_);
return v___x_1710_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1717_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__1);
v___x_1718_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__4));
v___x_1719_ = l_Lean_mkConst(v___x_1718_, v___x_1717_);
return v___x_1719_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1720_ = lean_unsigned_to_nat(0u);
v___x_1721_ = l_Lean_Level_ofNat(v___x_1720_);
return v___x_1721_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__6);
v___x_1723_ = l_Lean_mkSort(v___x_1722_);
return v___x_1723_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__11(void){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1729_ = lean_box(0);
v___x_1730_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__10));
v___x_1731_ = l_Lean_mkConst(v___x_1730_, v___x_1729_);
return v___x_1731_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__12(void){
_start:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1732_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__11);
v___x_1733_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__7);
v___x_1734_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__5);
v___x_1735_ = l_Lean_mkAppB(v___x_1734_, v___x_1733_, v___x_1732_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg(lean_object* v_as_x27_1741_, lean_object* v_b_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
if (lean_obj_tag(v_as_x27_1741_) == 0)
{
lean_object* v___x_1746_; 
v___x_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1746_, 0, v_b_1742_);
return v___x_1746_;
}
else
{
lean_object* v_head_1747_; lean_object* v_tail_1748_; lean_object* v___x_1749_; lean_object* v_env_1750_; lean_object* v_options_1751_; lean_object* v_cancelTk_x3f_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___y_1756_; uint8_t v___y_1757_; lean_object* v_a_1761_; lean_object* v___x_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
lean_dec_ref(v_b_1742_);
v_head_1747_ = lean_ctor_get(v_as_x27_1741_, 0);
v_tail_1748_ = lean_ctor_get(v_as_x27_1741_, 1);
v___x_1749_ = lean_st_ref_get(v___y_1744_);
v_env_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc_ref(v_env_1750_);
lean_dec(v___x_1749_);
v_options_1751_ = lean_ctor_get(v___y_1743_, 2);
v_cancelTk_x3f_1752_ = lean_ctor_get(v___y_1743_, 12);
v___x_1753_ = lean_box(0);
v___x_1754_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__2));
v___x_1764_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__12, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__12_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__12);
lean_inc(v_head_1747_);
v___x_1765_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1765_, 0, v_head_1747_);
lean_ctor_set(v___x_1765_, 1, v___x_1753_);
lean_ctor_set(v___x_1765_, 2, v___x_1764_);
v___x_1766_ = 0;
v___x_1767_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1767_, 0, v___x_1765_);
lean_ctor_set_uint8(v___x_1767_, sizeof(void*)*1, v___x_1766_);
v___x_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
v___x_1769_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_1750_, v_options_1751_, v___x_1768_, v_cancelTk_x3f_1752_);
lean_dec_ref(v___x_1768_);
v___x_1770_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_1769_, v___y_1743_, v___y_1744_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1780_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref(v___x_1770_);
v___x_1772_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_1771_, v___y_1744_);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1780_ == 0)
{
lean_object* v_unused_1781_; 
v_unused_1781_ = lean_ctor_get(v___x_1772_, 0);
lean_dec(v_unused_1781_);
v___x_1774_ = v___x_1772_;
v_isShared_1775_ = v_isSharedCheck_1780_;
goto v_resetjp_1773_;
}
else
{
lean_dec(v___x_1772_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1780_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1776_; lean_object* v___x_1778_; 
v___x_1776_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__14));
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 0, v___x_1776_);
v___x_1778_ = v___x_1774_;
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
else
{
lean_object* v_a_1782_; 
v_a_1782_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1782_);
lean_dec_ref(v___x_1770_);
v_a_1761_ = v_a_1782_;
goto v___jp_1760_;
}
v___jp_1755_:
{
if (v___y_1757_ == 0)
{
lean_dec_ref(v___y_1756_);
v_as_x27_1741_ = v_tail_1748_;
v_b_1742_ = v___x_1754_;
goto _start;
}
else
{
lean_object* v___x_1759_; 
v___x_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1759_, 0, v___y_1756_);
return v___x_1759_;
}
}
v___jp_1760_:
{
uint8_t v___x_1762_; 
v___x_1762_ = l_Lean_Exception_isInterrupt(v_a_1761_);
if (v___x_1762_ == 0)
{
uint8_t v___x_1763_; 
lean_inc_ref(v_a_1761_);
v___x_1763_ = l_Lean_Exception_isRuntime(v_a_1761_);
v___y_1756_ = v_a_1761_;
v___y_1757_ = v___x_1763_;
goto v___jp_1755_;
}
else
{
v___y_1756_ = v_a_1761_;
v___y_1757_ = v___x_1762_;
goto v___jp_1755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___boxed(lean_object* v_as_x27_1783_, lean_object* v_b_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg(v_as_x27_1783_, v_b_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v_as_x27_1783_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom(lean_object* v_decl_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_){
_start:
{
lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1822_; uint8_t v___y_1823_; lean_object* v_a_1826_; lean_object* v___y_1830_; uint8_t v___y_1831_; lean_object* v_a_1834_; 
switch(lean_obj_tag(v_decl_1789_))
{
case 1:
{
lean_object* v_val_1837_; lean_object* v___x_1838_; lean_object* v_toConstantVal_1839_; lean_object* v_env_1840_; lean_object* v_options_1841_; lean_object* v_cancelTk_x3f_1842_; uint8_t v___x_1843_; lean_object* v___x_1844_; lean_object* v_fallbackDecl_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v_val_1837_ = lean_ctor_get(v_decl_1789_, 0);
v___x_1838_ = lean_st_ref_get(v_a_1791_);
v_toConstantVal_1839_ = lean_ctor_get(v_val_1837_, 0);
v_env_1840_ = lean_ctor_get(v___x_1838_, 0);
lean_inc_ref(v_env_1840_);
lean_dec(v___x_1838_);
v_options_1841_ = lean_ctor_get(v_a_1790_, 2);
v_cancelTk_x3f_1842_ = lean_ctor_get(v_a_1790_, 12);
v___x_1843_ = 0;
lean_inc_ref(v_toConstantVal_1839_);
v___x_1844_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1844_, 0, v_toConstantVal_1839_);
lean_ctor_set_uint8(v___x_1844_, sizeof(void*)*1, v___x_1843_);
v_fallbackDecl_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_1845_, 0, v___x_1844_);
v___x_1846_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_1840_, v_options_1841_, v_fallbackDecl_1845_, v_cancelTk_x3f_1842_);
lean_dec_ref(v_fallbackDecl_1845_);
v___x_1847_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_1846_, v_a_1790_, v_a_1791_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1857_; 
lean_dec_ref(v_decl_1789_);
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1848_);
lean_dec_ref(v___x_1847_);
v___x_1849_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_1848_, v_a_1791_);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1857_ == 0)
{
lean_object* v_unused_1858_; 
v_unused_1858_ = lean_ctor_get(v___x_1849_, 0);
lean_dec(v_unused_1858_);
v___x_1851_ = v___x_1849_;
v_isShared_1852_ = v_isSharedCheck_1857_;
goto v_resetjp_1850_;
}
else
{
lean_dec(v___x_1849_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1857_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1853_; lean_object* v___x_1855_; 
v___x_1853_ = lean_box(0);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 0, v___x_1853_);
v___x_1855_ = v___x_1851_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
else
{
lean_object* v_a_1859_; 
v_a_1859_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1859_);
lean_dec_ref(v___x_1847_);
v_a_1826_ = v_a_1859_;
goto v___jp_1825_;
}
}
case 2:
{
lean_object* v_val_1860_; lean_object* v___x_1861_; lean_object* v_toConstantVal_1862_; lean_object* v_env_1863_; lean_object* v_options_1864_; lean_object* v_cancelTk_x3f_1865_; uint8_t v___x_1866_; lean_object* v___x_1867_; lean_object* v_fallbackDecl_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v_val_1860_ = lean_ctor_get(v_decl_1789_, 0);
v___x_1861_ = lean_st_ref_get(v_a_1791_);
v_toConstantVal_1862_ = lean_ctor_get(v_val_1860_, 0);
v_env_1863_ = lean_ctor_get(v___x_1861_, 0);
lean_inc_ref(v_env_1863_);
lean_dec(v___x_1861_);
v_options_1864_ = lean_ctor_get(v_a_1790_, 2);
v_cancelTk_x3f_1865_ = lean_ctor_get(v_a_1790_, 12);
v___x_1866_ = 0;
lean_inc_ref(v_toConstantVal_1862_);
v___x_1867_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1867_, 0, v_toConstantVal_1862_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*1, v___x_1866_);
v_fallbackDecl_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_1868_, 0, v___x_1867_);
v___x_1869_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_1863_, v_options_1864_, v_fallbackDecl_1868_, v_cancelTk_x3f_1865_);
lean_dec_ref(v_fallbackDecl_1868_);
v___x_1870_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_1869_, v_a_1790_, v_a_1791_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1880_; 
lean_dec_ref(v_decl_1789_);
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref(v___x_1870_);
v___x_1872_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_1871_, v_a_1791_);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1880_ == 0)
{
lean_object* v_unused_1881_; 
v_unused_1881_ = lean_ctor_get(v___x_1872_, 0);
lean_dec(v_unused_1881_);
v___x_1874_ = v___x_1872_;
v_isShared_1875_ = v_isSharedCheck_1880_;
goto v_resetjp_1873_;
}
else
{
lean_dec(v___x_1872_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1880_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1876_; lean_object* v___x_1878_; 
v___x_1876_ = lean_box(0);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v___x_1876_);
v___x_1878_ = v___x_1874_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
else
{
lean_object* v_a_1882_; 
v_a_1882_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1882_);
lean_dec_ref(v___x_1870_);
v_a_1834_ = v_a_1882_;
goto v___jp_1833_;
}
}
default: 
{
v___y_1794_ = v_a_1790_;
v___y_1795_ = v_a_1791_;
goto v___jp_1793_;
}
}
v___jp_1793_:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1796_ = l_Lean_Declaration_getNames(v_decl_1789_);
v___x_1797_ = lean_box(0);
v___x_1798_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__2));
v___x_1799_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg(v___x_1796_, v___x_1798_, v___y_1794_, v___y_1795_);
lean_dec(v___x_1796_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1812_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1802_ = v___x_1799_;
v_isShared_1803_ = v_isSharedCheck_1812_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1799_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1812_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v_fst_1804_; 
v_fst_1804_ = lean_ctor_get(v_a_1800_, 0);
lean_inc(v_fst_1804_);
lean_dec(v_a_1800_);
if (lean_obj_tag(v_fst_1804_) == 0)
{
lean_object* v___x_1806_; 
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v___x_1797_);
v___x_1806_ = v___x_1802_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1797_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
else
{
lean_object* v_val_1808_; lean_object* v___x_1810_; 
v_val_1808_ = lean_ctor_get(v_fst_1804_, 0);
lean_inc(v_val_1808_);
lean_dec_ref(v_fst_1804_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v_val_1808_);
v___x_1810_ = v___x_1802_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_val_1808_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
v_a_1813_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1799_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1799_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
v___jp_1821_:
{
if (v___y_1823_ == 0)
{
lean_dec_ref(v___y_1822_);
v___y_1794_ = v_a_1790_;
v___y_1795_ = v_a_1791_;
goto v___jp_1793_;
}
else
{
lean_object* v___x_1824_; 
lean_dec(v_decl_1789_);
v___x_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1824_, 0, v___y_1822_);
return v___x_1824_;
}
}
v___jp_1825_:
{
uint8_t v___x_1827_; 
v___x_1827_ = l_Lean_Exception_isInterrupt(v_a_1826_);
if (v___x_1827_ == 0)
{
uint8_t v___x_1828_; 
lean_inc_ref(v_a_1826_);
v___x_1828_ = l_Lean_Exception_isRuntime(v_a_1826_);
v___y_1822_ = v_a_1826_;
v___y_1823_ = v___x_1828_;
goto v___jp_1821_;
}
else
{
v___y_1822_ = v_a_1826_;
v___y_1823_ = v___x_1827_;
goto v___jp_1821_;
}
}
v___jp_1829_:
{
if (v___y_1831_ == 0)
{
lean_dec_ref(v___y_1830_);
v___y_1794_ = v_a_1790_;
v___y_1795_ = v_a_1791_;
goto v___jp_1793_;
}
else
{
lean_object* v___x_1832_; 
lean_dec(v_decl_1789_);
v___x_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1832_, 0, v___y_1830_);
return v___x_1832_;
}
}
v___jp_1833_:
{
uint8_t v___x_1835_; 
v___x_1835_ = l_Lean_Exception_isInterrupt(v_a_1834_);
if (v___x_1835_ == 0)
{
uint8_t v___x_1836_; 
lean_inc_ref(v_a_1834_);
v___x_1836_ = l_Lean_Exception_isRuntime(v_a_1834_);
v___y_1830_ = v_a_1834_;
v___y_1831_ = v___x_1836_;
goto v___jp_1829_;
}
else
{
v___y_1830_ = v_a_1834_;
v___y_1831_ = v___x_1835_;
goto v___jp_1829_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom___boxed(lean_object* v_decl_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom(v_decl_1883_, v_a_1884_, v_a_1885_);
lean_dec(v_a_1885_);
lean_dec_ref(v_a_1884_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0(lean_object* v_00_u03b1_1888_, lean_object* v_x_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v_x_1889_, v___y_1890_, v___y_1891_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___boxed(lean_object* v_00_u03b1_1894_, lean_object* v_x_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0(v_00_u03b1_1894_, v_x_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2(lean_object* v_as_1900_, lean_object* v_as_x27_1901_, lean_object* v_b_1902_, lean_object* v_a_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg(v_as_x27_1901_, v_b_1902_, v___y_1904_, v___y_1905_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___boxed(lean_object* v_as_1908_, lean_object* v_as_x27_1909_, lean_object* v_b_1910_, lean_object* v_a_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2(v_as_1908_, v_as_x27_1909_, v_b_1910_, v_a_1911_, v___y_1912_, v___y_1913_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v_as_x27_1909_);
lean_dec(v_as_1908_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3(v_00_u03b1_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0(lean_object* v_00_u03b1_1926_, lean_object* v_ex_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(v_ex_1927_, v___y_1928_, v___y_1929_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1932_, lean_object* v_ex_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0(v_00_u03b1_1932_, v_ex_1933_, v___y_1934_, v___y_1935_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1938_, lean_object* v_msg_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v___x_1943_; 
v___x_1943_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_1939_, v___y_1940_, v___y_1941_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1944_, lean_object* v_msg_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2(v_00_u03b1_1944_, v_msg_1945_, v___y_1946_, v___y_1947_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
return v_res_1949_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1950_ = lean_unsigned_to_nat(32u);
v___x_1951_ = lean_mk_empty_array_with_capacity(v___x_1950_);
v___x_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
return v___x_1952_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1953_ = ((size_t)5ULL);
v___x_1954_ = lean_unsigned_to_nat(0u);
v___x_1955_ = lean_unsigned_to_nat(32u);
v___x_1956_ = lean_mk_empty_array_with_capacity(v___x_1955_);
v___x_1957_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__0);
v___x_1958_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1958_, 0, v___x_1957_);
lean_ctor_set(v___x_1958_, 1, v___x_1956_);
lean_ctor_set(v___x_1958_, 2, v___x_1954_);
lean_ctor_set(v___x_1958_, 3, v___x_1954_);
lean_ctor_set_usize(v___x_1958_, 4, v___x_1953_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(lean_object* v___y_1959_){
_start:
{
lean_object* v___x_1961_; lean_object* v_traceState_1962_; lean_object* v_traces_1963_; lean_object* v___x_1964_; lean_object* v_traceState_1965_; lean_object* v_env_1966_; lean_object* v_nextMacroScope_1967_; lean_object* v_ngen_1968_; lean_object* v_auxDeclNGen_1969_; lean_object* v_cache_1970_; lean_object* v_messages_1971_; lean_object* v_infoState_1972_; lean_object* v_snapshotTasks_1973_; lean_object* v_newDecls_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1993_; 
v___x_1961_ = lean_st_ref_get(v___y_1959_);
v_traceState_1962_ = lean_ctor_get(v___x_1961_, 4);
lean_inc_ref(v_traceState_1962_);
lean_dec(v___x_1961_);
v_traces_1963_ = lean_ctor_get(v_traceState_1962_, 0);
lean_inc_ref(v_traces_1963_);
lean_dec_ref(v_traceState_1962_);
v___x_1964_ = lean_st_ref_take(v___y_1959_);
v_traceState_1965_ = lean_ctor_get(v___x_1964_, 4);
v_env_1966_ = lean_ctor_get(v___x_1964_, 0);
v_nextMacroScope_1967_ = lean_ctor_get(v___x_1964_, 1);
v_ngen_1968_ = lean_ctor_get(v___x_1964_, 2);
v_auxDeclNGen_1969_ = lean_ctor_get(v___x_1964_, 3);
v_cache_1970_ = lean_ctor_get(v___x_1964_, 5);
v_messages_1971_ = lean_ctor_get(v___x_1964_, 6);
v_infoState_1972_ = lean_ctor_get(v___x_1964_, 7);
v_snapshotTasks_1973_ = lean_ctor_get(v___x_1964_, 8);
v_newDecls_1974_ = lean_ctor_get(v___x_1964_, 9);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1976_ = v___x_1964_;
v_isShared_1977_ = v_isSharedCheck_1993_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_newDecls_1974_);
lean_inc(v_snapshotTasks_1973_);
lean_inc(v_infoState_1972_);
lean_inc(v_messages_1971_);
lean_inc(v_cache_1970_);
lean_inc(v_traceState_1965_);
lean_inc(v_auxDeclNGen_1969_);
lean_inc(v_ngen_1968_);
lean_inc(v_nextMacroScope_1967_);
lean_inc(v_env_1966_);
lean_dec(v___x_1964_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1993_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
uint64_t v_tid_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1991_; 
v_tid_1978_ = lean_ctor_get_uint64(v_traceState_1965_, sizeof(void*)*1);
v_isSharedCheck_1991_ = !lean_is_exclusive(v_traceState_1965_);
if (v_isSharedCheck_1991_ == 0)
{
lean_object* v_unused_1992_; 
v_unused_1992_ = lean_ctor_get(v_traceState_1965_, 0);
lean_dec(v_unused_1992_);
v___x_1980_ = v_traceState_1965_;
v_isShared_1981_ = v_isSharedCheck_1991_;
goto v_resetjp_1979_;
}
else
{
lean_dec(v_traceState_1965_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1991_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1982_; lean_object* v___x_1984_; 
v___x_1982_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__1);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_1982_);
v___x_1984_ = v___x_1980_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1982_);
lean_ctor_set_uint64(v_reuseFailAlloc_1990_, sizeof(void*)*1, v_tid_1978_);
v___x_1984_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1986_; 
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 4, v___x_1984_);
v___x_1986_ = v___x_1976_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_env_1966_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v_nextMacroScope_1967_);
lean_ctor_set(v_reuseFailAlloc_1989_, 2, v_ngen_1968_);
lean_ctor_set(v_reuseFailAlloc_1989_, 3, v_auxDeclNGen_1969_);
lean_ctor_set(v_reuseFailAlloc_1989_, 4, v___x_1984_);
lean_ctor_set(v_reuseFailAlloc_1989_, 5, v_cache_1970_);
lean_ctor_set(v_reuseFailAlloc_1989_, 6, v_messages_1971_);
lean_ctor_set(v_reuseFailAlloc_1989_, 7, v_infoState_1972_);
lean_ctor_set(v_reuseFailAlloc_1989_, 8, v_snapshotTasks_1973_);
lean_ctor_set(v_reuseFailAlloc_1989_, 9, v_newDecls_1974_);
v___x_1986_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1987_ = lean_st_ref_set(v___y_1959_, v___x_1986_);
v___x_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1988_, 0, v_traces_1963_);
return v___x_1988_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___boxed(lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v___y_1994_);
lean_dec(v___y_1994_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1(lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v___x_2000_; 
v___x_2000_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v___y_1998_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___boxed(lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1(v___y_2001_, v___y_2002_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___redArg(lean_object* v_category_2005_, lean_object* v_opts_2006_, lean_object* v_act_2007_, lean_object* v_decl_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
lean_inc(v___y_2010_);
lean_inc_ref(v___y_2009_);
v___x_2012_ = lean_apply_2(v_act_2007_, v___y_2009_, v___y_2010_);
v___x_2013_ = l_Lean_profileitIOUnsafe___redArg(v_category_2005_, v_opts_2006_, v___x_2012_, v_decl_2008_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___redArg___boxed(lean_object* v_category_2014_, lean_object* v_opts_2015_, lean_object* v_act_2016_, lean_object* v_decl_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___redArg(v_category_2014_, v_opts_2015_, v_act_2016_, v_decl_2017_, v___y_2018_, v___y_2019_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec_ref(v_opts_2015_);
lean_dec_ref(v_category_2014_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3(lean_object* v_00_u03b1_2022_, lean_object* v_category_2023_, lean_object* v_opts_2024_, lean_object* v_act_2025_, lean_object* v_decl_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___redArg(v_category_2023_, v_opts_2024_, v_act_2025_, v_decl_2026_, v___y_2027_, v___y_2028_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___boxed(lean_object* v_00_u03b1_2031_, lean_object* v_category_2032_, lean_object* v_opts_2033_, lean_object* v_act_2034_, lean_object* v_decl_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3(v_00_u03b1_2031_, v_category_2032_, v_opts_2033_, v_act_2034_, v_decl_2035_, v___y_2036_, v___y_2037_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec_ref(v_opts_2033_);
lean_dec_ref(v_category_2032_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__0(lean_object* v_a_2040_, lean_object* v_a_2041_){
_start:
{
if (lean_obj_tag(v_a_2040_) == 0)
{
lean_object* v___x_2042_; 
v___x_2042_ = l_List_reverse___redArg(v_a_2041_);
return v___x_2042_;
}
else
{
lean_object* v_head_2043_; lean_object* v_tail_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2053_; 
v_head_2043_ = lean_ctor_get(v_a_2040_, 0);
v_tail_2044_ = lean_ctor_get(v_a_2040_, 1);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_a_2040_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2046_ = v_a_2040_;
v_isShared_2047_ = v_isSharedCheck_2053_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_tail_2044_);
lean_inc(v_head_2043_);
lean_dec(v_a_2040_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2053_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2048_; lean_object* v___x_2050_; 
v___x_2048_ = l_Lean_MessageData_ofName(v_head_2043_);
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 1, v_a_2041_);
lean_ctor_set(v___x_2046_, 0, v___x_2048_);
v___x_2050_ = v___x_2046_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2048_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_a_2041_);
v___x_2050_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
v_a_2040_ = v_tail_2044_;
v_a_2041_ = v___x_2050_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__0));
v___x_2056_ = l_Lean_stringToMessageData(v___x_2055_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0(lean_object* v_decl_2057_, lean_object* v_x_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2062_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__1, &l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__1);
v___x_2063_ = l_Lean_Declaration_getTopLevelNames(v_decl_2057_);
v___x_2064_ = lean_box(0);
v___x_2065_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__0(v___x_2063_, v___x_2064_);
v___x_2066_ = l_Lean_MessageData_ofList(v___x_2065_);
v___x_2067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2062_);
lean_ctor_set(v___x_2067_, 1, v___x_2066_);
v___x_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___boxed(lean_object* v_decl_2069_, lean_object* v_x_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0(v_decl_2069_, v_x_2070_, v___y_2071_, v___y_2072_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec_ref(v_x_2070_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__5(lean_object* v_opts_2075_, lean_object* v_opt_2076_){
_start:
{
lean_object* v_name_2077_; lean_object* v_defValue_2078_; lean_object* v_map_2079_; lean_object* v___x_2080_; 
v_name_2077_ = lean_ctor_get(v_opt_2076_, 0);
v_defValue_2078_ = lean_ctor_get(v_opt_2076_, 1);
v_map_2079_ = lean_ctor_get(v_opts_2075_, 0);
v___x_2080_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2079_, v_name_2077_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_inc(v_defValue_2078_);
return v_defValue_2078_;
}
else
{
lean_object* v_val_2081_; 
v_val_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc(v_val_2081_);
lean_dec_ref(v___x_2080_);
if (lean_obj_tag(v_val_2081_) == 3)
{
lean_object* v_v_2082_; 
v_v_2082_ = lean_ctor_get(v_val_2081_, 0);
lean_inc(v_v_2082_);
lean_dec_ref(v_val_2081_);
return v_v_2082_;
}
else
{
lean_dec(v_val_2081_);
lean_inc(v_defValue_2078_);
return v_defValue_2078_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__5___boxed(lean_object* v_opts_2083_, lean_object* v_opt_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__5(v_opts_2083_, v_opt_2084_);
lean_dec_ref(v_opt_2084_);
lean_dec_ref(v_opts_2083_);
return v_res_2085_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__2(lean_object* v_e_2086_){
_start:
{
if (lean_obj_tag(v_e_2086_) == 0)
{
uint8_t v___x_2087_; 
v___x_2087_ = 2;
return v___x_2087_;
}
else
{
uint8_t v___x_2088_; 
v___x_2088_ = 0;
return v___x_2088_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__2___boxed(lean_object* v_e_2089_){
_start:
{
uint8_t v_res_2090_; lean_object* v_r_2091_; 
v_res_2090_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__2(v_e_2089_);
lean_dec_ref(v_e_2089_);
v_r_2091_ = lean_box(v_res_2090_);
return v_r_2091_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4___redArg(lean_object* v_x_2092_){
_start:
{
if (lean_obj_tag(v_x_2092_) == 0)
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2101_; 
v_a_2094_ = lean_ctor_get(v_x_2092_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v_x_2092_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2096_ = v_x_2092_;
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v_x_2092_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
lean_ctor_set_tag(v___x_2096_, 1);
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
v_a_2102_ = lean_ctor_get(v_x_2092_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_x_2092_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v_x_2092_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v_x_2092_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
lean_ctor_set_tag(v___x_2104_, 0);
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4___redArg___boxed(lean_object* v_x_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4___redArg(v_x_2110_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__3_spec__5(size_t v_sz_2113_, size_t v_i_2114_, lean_object* v_bs_2115_){
_start:
{
uint8_t v___x_2116_; 
v___x_2116_ = lean_usize_dec_lt(v_i_2114_, v_sz_2113_);
if (v___x_2116_ == 0)
{
return v_bs_2115_;
}
else
{
lean_object* v_v_2117_; lean_object* v_msg_2118_; lean_object* v___x_2119_; lean_object* v_bs_x27_2120_; size_t v___x_2121_; size_t v___x_2122_; lean_object* v___x_2123_; 
v_v_2117_ = lean_array_uget_borrowed(v_bs_2115_, v_i_2114_);
v_msg_2118_ = lean_ctor_get(v_v_2117_, 1);
lean_inc_ref(v_msg_2118_);
v___x_2119_ = lean_unsigned_to_nat(0u);
v_bs_x27_2120_ = lean_array_uset(v_bs_2115_, v_i_2114_, v___x_2119_);
v___x_2121_ = ((size_t)1ULL);
v___x_2122_ = lean_usize_add(v_i_2114_, v___x_2121_);
v___x_2123_ = lean_array_uset(v_bs_x27_2120_, v_i_2114_, v_msg_2118_);
v_i_2114_ = v___x_2122_;
v_bs_2115_ = v___x_2123_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__3_spec__5___boxed(lean_object* v_sz_2125_, lean_object* v_i_2126_, lean_object* v_bs_2127_){
_start:
{
size_t v_sz_boxed_2128_; size_t v_i_boxed_2129_; lean_object* v_res_2130_; 
v_sz_boxed_2128_ = lean_unbox_usize(v_sz_2125_);
lean_dec(v_sz_2125_);
v_i_boxed_2129_ = lean_unbox_usize(v_i_2126_);
lean_dec(v_i_2126_);
v_res_2130_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__3_spec__5(v_sz_boxed_2128_, v_i_boxed_2129_, v_bs_2127_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__3(lean_object* v_oldTraces_2131_, lean_object* v_data_2132_, lean_object* v_ref_2133_, lean_object* v_msg_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_fileName_2138_; lean_object* v_fileMap_2139_; lean_object* v_options_2140_; lean_object* v_currRecDepth_2141_; lean_object* v_maxRecDepth_2142_; lean_object* v_ref_2143_; lean_object* v_currNamespace_2144_; lean_object* v_openDecls_2145_; lean_object* v_initHeartbeats_2146_; lean_object* v_maxHeartbeats_2147_; lean_object* v_quotContext_2148_; lean_object* v_currMacroScope_2149_; uint8_t v_diag_2150_; lean_object* v_cancelTk_x3f_2151_; uint8_t v_suppressElabErrors_2152_; lean_object* v_inheritedTraceOptions_2153_; lean_object* v___x_2154_; lean_object* v_traceState_2155_; lean_object* v_traces_2156_; lean_object* v_ref_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; size_t v_sz_2160_; size_t v___x_2161_; lean_object* v___x_2162_; lean_object* v_msg_2163_; lean_object* v___x_2164_; lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2203_; 
v_fileName_2138_ = lean_ctor_get(v___y_2135_, 0);
v_fileMap_2139_ = lean_ctor_get(v___y_2135_, 1);
v_options_2140_ = lean_ctor_get(v___y_2135_, 2);
v_currRecDepth_2141_ = lean_ctor_get(v___y_2135_, 3);
v_maxRecDepth_2142_ = lean_ctor_get(v___y_2135_, 4);
v_ref_2143_ = lean_ctor_get(v___y_2135_, 5);
v_currNamespace_2144_ = lean_ctor_get(v___y_2135_, 6);
v_openDecls_2145_ = lean_ctor_get(v___y_2135_, 7);
v_initHeartbeats_2146_ = lean_ctor_get(v___y_2135_, 8);
v_maxHeartbeats_2147_ = lean_ctor_get(v___y_2135_, 9);
v_quotContext_2148_ = lean_ctor_get(v___y_2135_, 10);
v_currMacroScope_2149_ = lean_ctor_get(v___y_2135_, 11);
v_diag_2150_ = lean_ctor_get_uint8(v___y_2135_, sizeof(void*)*14);
v_cancelTk_x3f_2151_ = lean_ctor_get(v___y_2135_, 12);
v_suppressElabErrors_2152_ = lean_ctor_get_uint8(v___y_2135_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2153_ = lean_ctor_get(v___y_2135_, 13);
v___x_2154_ = lean_st_ref_get(v___y_2136_);
v_traceState_2155_ = lean_ctor_get(v___x_2154_, 4);
lean_inc_ref(v_traceState_2155_);
lean_dec(v___x_2154_);
v_traces_2156_ = lean_ctor_get(v_traceState_2155_, 0);
lean_inc_ref(v_traces_2156_);
lean_dec_ref(v_traceState_2155_);
v_ref_2157_ = l_Lean_replaceRef(v_ref_2133_, v_ref_2143_);
lean_inc_ref(v_inheritedTraceOptions_2153_);
lean_inc(v_cancelTk_x3f_2151_);
lean_inc(v_currMacroScope_2149_);
lean_inc(v_quotContext_2148_);
lean_inc(v_maxHeartbeats_2147_);
lean_inc(v_initHeartbeats_2146_);
lean_inc(v_openDecls_2145_);
lean_inc(v_currNamespace_2144_);
lean_inc(v_maxRecDepth_2142_);
lean_inc(v_currRecDepth_2141_);
lean_inc_ref(v_options_2140_);
lean_inc_ref(v_fileMap_2139_);
lean_inc_ref(v_fileName_2138_);
v___x_2158_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2158_, 0, v_fileName_2138_);
lean_ctor_set(v___x_2158_, 1, v_fileMap_2139_);
lean_ctor_set(v___x_2158_, 2, v_options_2140_);
lean_ctor_set(v___x_2158_, 3, v_currRecDepth_2141_);
lean_ctor_set(v___x_2158_, 4, v_maxRecDepth_2142_);
lean_ctor_set(v___x_2158_, 5, v_ref_2157_);
lean_ctor_set(v___x_2158_, 6, v_currNamespace_2144_);
lean_ctor_set(v___x_2158_, 7, v_openDecls_2145_);
lean_ctor_set(v___x_2158_, 8, v_initHeartbeats_2146_);
lean_ctor_set(v___x_2158_, 9, v_maxHeartbeats_2147_);
lean_ctor_set(v___x_2158_, 10, v_quotContext_2148_);
lean_ctor_set(v___x_2158_, 11, v_currMacroScope_2149_);
lean_ctor_set(v___x_2158_, 12, v_cancelTk_x3f_2151_);
lean_ctor_set(v___x_2158_, 13, v_inheritedTraceOptions_2153_);
lean_ctor_set_uint8(v___x_2158_, sizeof(void*)*14, v_diag_2150_);
lean_ctor_set_uint8(v___x_2158_, sizeof(void*)*14 + 1, v_suppressElabErrors_2152_);
v___x_2159_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2156_);
lean_dec_ref(v_traces_2156_);
v_sz_2160_ = lean_array_size(v___x_2159_);
v___x_2161_ = ((size_t)0ULL);
v___x_2162_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__3_spec__5(v_sz_2160_, v___x_2161_, v___x_2159_);
v_msg_2163_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2163_, 0, v_data_2132_);
lean_ctor_set(v_msg_2163_, 1, v_msg_2134_);
lean_ctor_set(v_msg_2163_, 2, v___x_2162_);
v___x_2164_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2163_, v___x_2158_, v___y_2136_);
lean_dec_ref(v___x_2158_);
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2167_ = v___x_2164_;
v_isShared_2168_ = v_isSharedCheck_2203_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2164_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2203_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2169_; lean_object* v_traceState_2170_; lean_object* v_env_2171_; lean_object* v_nextMacroScope_2172_; lean_object* v_ngen_2173_; lean_object* v_auxDeclNGen_2174_; lean_object* v_cache_2175_; lean_object* v_messages_2176_; lean_object* v_infoState_2177_; lean_object* v_snapshotTasks_2178_; lean_object* v_newDecls_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2202_; 
v___x_2169_ = lean_st_ref_take(v___y_2136_);
v_traceState_2170_ = lean_ctor_get(v___x_2169_, 4);
v_env_2171_ = lean_ctor_get(v___x_2169_, 0);
v_nextMacroScope_2172_ = lean_ctor_get(v___x_2169_, 1);
v_ngen_2173_ = lean_ctor_get(v___x_2169_, 2);
v_auxDeclNGen_2174_ = lean_ctor_get(v___x_2169_, 3);
v_cache_2175_ = lean_ctor_get(v___x_2169_, 5);
v_messages_2176_ = lean_ctor_get(v___x_2169_, 6);
v_infoState_2177_ = lean_ctor_get(v___x_2169_, 7);
v_snapshotTasks_2178_ = lean_ctor_get(v___x_2169_, 8);
v_newDecls_2179_ = lean_ctor_get(v___x_2169_, 9);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2181_ = v___x_2169_;
v_isShared_2182_ = v_isSharedCheck_2202_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_newDecls_2179_);
lean_inc(v_snapshotTasks_2178_);
lean_inc(v_infoState_2177_);
lean_inc(v_messages_2176_);
lean_inc(v_cache_2175_);
lean_inc(v_traceState_2170_);
lean_inc(v_auxDeclNGen_2174_);
lean_inc(v_ngen_2173_);
lean_inc(v_nextMacroScope_2172_);
lean_inc(v_env_2171_);
lean_dec(v___x_2169_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2202_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
uint64_t v_tid_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2200_; 
v_tid_2183_ = lean_ctor_get_uint64(v_traceState_2170_, sizeof(void*)*1);
v_isSharedCheck_2200_ = !lean_is_exclusive(v_traceState_2170_);
if (v_isSharedCheck_2200_ == 0)
{
lean_object* v_unused_2201_; 
v_unused_2201_ = lean_ctor_get(v_traceState_2170_, 0);
lean_dec(v_unused_2201_);
v___x_2185_ = v_traceState_2170_;
v_isShared_2186_ = v_isSharedCheck_2200_;
goto v_resetjp_2184_;
}
else
{
lean_dec(v_traceState_2170_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2200_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2190_; 
v___x_2187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2187_, 0, v_ref_2133_);
lean_ctor_set(v___x_2187_, 1, v_a_2165_);
v___x_2188_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2131_, v___x_2187_);
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
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_env_2171_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_nextMacroScope_2172_);
lean_ctor_set(v_reuseFailAlloc_2198_, 2, v_ngen_2173_);
lean_ctor_set(v_reuseFailAlloc_2198_, 3, v_auxDeclNGen_2174_);
lean_ctor_set(v_reuseFailAlloc_2198_, 4, v___x_2190_);
lean_ctor_set(v_reuseFailAlloc_2198_, 5, v_cache_2175_);
lean_ctor_set(v_reuseFailAlloc_2198_, 6, v_messages_2176_);
lean_ctor_set(v_reuseFailAlloc_2198_, 7, v_infoState_2177_);
lean_ctor_set(v_reuseFailAlloc_2198_, 8, v_snapshotTasks_2178_);
lean_ctor_set(v_reuseFailAlloc_2198_, 9, v_newDecls_2179_);
v___x_2192_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2193_ = lean_st_ref_set(v___y_2136_, v___x_2192_);
v___x_2194_ = lean_box(0);
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 0, v___x_2194_);
v___x_2196_ = v___x_2167_;
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
lean_object* v_fst_2233_; lean_object* v_snd_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2325_; 
v_fst_2233_ = lean_ctor_get(v_resStartStop_2229_, 0);
v_snd_2234_ = lean_ctor_get(v_resStartStop_2229_, 1);
v_isSharedCheck_2325_ = !lean_is_exclusive(v_resStartStop_2229_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2236_ = v_resStartStop_2229_;
v_isShared_2237_ = v_isSharedCheck_2325_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_snd_2234_);
lean_inc(v_fst_2233_);
lean_dec(v_resStartStop_2229_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2325_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v_data_2241_; lean_object* v_fst_2244_; lean_object* v_snd_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2324_; 
v_fst_2244_ = lean_ctor_get(v_snd_2234_, 0);
v_snd_2245_ = lean_ctor_get(v_snd_2234_, 1);
v_isSharedCheck_2324_ = !lean_is_exclusive(v_snd_2234_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2247_ = v_snd_2234_;
v_isShared_2248_ = v_isSharedCheck_2324_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_snd_2245_);
lean_inc(v_fst_2244_);
lean_dec(v_snd_2234_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2324_;
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
lean_object* v___x_2249_; uint8_t v___x_2250_; lean_object* v___y_2252_; lean_object* v_a_2253_; uint8_t v___y_2277_; double v___y_2309_; 
v___x_2249_ = l_Lean_trace_profiler;
v___x_2250_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2225_, v___x_2249_);
if (v___x_2250_ == 0)
{
v___y_2277_ = v___x_2250_;
goto v___jp_2276_;
}
else
{
lean_object* v___x_2314_; uint8_t v___x_2315_; 
v___x_2314_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2315_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2225_, v___x_2314_);
if (v___x_2315_ == 0)
{
lean_object* v___x_2316_; lean_object* v___x_2317_; double v___x_2318_; double v___x_2319_; double v___x_2320_; 
v___x_2316_ = l_Lean_trace_profiler_threshold;
v___x_2317_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__5(v_opts_2225_, v___x_2316_);
v___x_2318_ = lean_float_of_nat(v___x_2317_);
v___x_2319_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__5);
v___x_2320_ = lean_float_div(v___x_2318_, v___x_2319_);
v___y_2309_ = v___x_2320_;
goto v___jp_2308_;
}
else
{
lean_object* v___x_2321_; lean_object* v___x_2322_; double v___x_2323_; 
v___x_2321_ = l_Lean_trace_profiler_threshold;
v___x_2322_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__5(v_opts_2225_, v___x_2321_);
v___x_2323_ = lean_float_of_nat(v___x_2322_);
v___y_2309_ = v___x_2323_;
goto v___jp_2308_;
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
lean_object* v___x_2278_; lean_object* v_traceState_2279_; lean_object* v_env_2280_; lean_object* v_nextMacroScope_2281_; lean_object* v_ngen_2282_; lean_object* v_auxDeclNGen_2283_; lean_object* v_cache_2284_; lean_object* v_messages_2285_; lean_object* v_infoState_2286_; lean_object* v_snapshotTasks_2287_; lean_object* v_newDecls_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2307_; 
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
v_newDecls_2288_ = lean_ctor_get(v___x_2278_, 9);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2290_ = v___x_2278_;
v_isShared_2291_ = v_isSharedCheck_2307_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_newDecls_2288_);
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
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2307_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
uint64_t v_tid_2292_; lean_object* v_traces_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2306_; 
v_tid_2292_ = lean_ctor_get_uint64(v_traceState_2279_, sizeof(void*)*1);
v_traces_2293_ = lean_ctor_get(v_traceState_2279_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v_traceState_2279_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2295_ = v_traceState_2279_;
v_isShared_2296_ = v_isSharedCheck_2306_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_traces_2293_);
lean_dec(v_traceState_2279_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2306_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2297_; lean_object* v___x_2299_; 
v___x_2297_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2227_, v_traces_2293_);
lean_dec_ref(v_traces_2293_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 0, v___x_2297_);
v___x_2299_ = v___x_2295_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2297_);
lean_ctor_set_uint64(v_reuseFailAlloc_2305_, sizeof(void*)*1, v_tid_2292_);
v___x_2299_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
lean_object* v___x_2301_; 
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 4, v___x_2299_);
v___x_2301_ = v___x_2290_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_env_2280_);
lean_ctor_set(v_reuseFailAlloc_2304_, 1, v_nextMacroScope_2281_);
lean_ctor_set(v_reuseFailAlloc_2304_, 2, v_ngen_2282_);
lean_ctor_set(v_reuseFailAlloc_2304_, 3, v_auxDeclNGen_2283_);
lean_ctor_set(v_reuseFailAlloc_2304_, 4, v___x_2299_);
lean_ctor_set(v_reuseFailAlloc_2304_, 5, v_cache_2284_);
lean_ctor_set(v_reuseFailAlloc_2304_, 6, v_messages_2285_);
lean_ctor_set(v_reuseFailAlloc_2304_, 7, v_infoState_2286_);
lean_ctor_set(v_reuseFailAlloc_2304_, 8, v_snapshotTasks_2287_);
lean_ctor_set(v_reuseFailAlloc_2304_, 9, v_newDecls_2288_);
v___x_2301_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2302_ = lean_st_ref_set(v___y_2231_, v___x_2301_);
v___x_2303_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4___redArg(v_fst_2233_);
return v___x_2303_;
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
v___jp_2308_:
{
double v___x_2310_; double v___x_2311_; double v___x_2312_; uint8_t v___x_2313_; 
v___x_2310_ = lean_unbox_float(v_snd_2245_);
v___x_2311_ = lean_unbox_float(v_fst_2244_);
v___x_2312_ = lean_float_sub(v___x_2310_, v___x_2311_);
v___x_2313_ = lean_float_decLt(v___y_2309_, v___x_2312_);
v___y_2277_ = v___x_2313_;
goto v___jp_2276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___boxed(lean_object* v_cls_2326_, lean_object* v_collapsed_2327_, lean_object* v_tag_2328_, lean_object* v_opts_2329_, lean_object* v_clsEnabled_2330_, lean_object* v_oldTraces_2331_, lean_object* v_msg_2332_, lean_object* v_resStartStop_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
uint8_t v_collapsed_boxed_2337_; uint8_t v_clsEnabled_boxed_2338_; lean_object* v_res_2339_; 
v_collapsed_boxed_2337_ = lean_unbox(v_collapsed_2327_);
v_clsEnabled_boxed_2338_ = lean_unbox(v_clsEnabled_2330_);
v_res_2339_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2(v_cls_2326_, v_collapsed_boxed_2337_, v_tag_2328_, v_opts_2329_, v_clsEnabled_boxed_2338_, v_oldTraces_2331_, v_msg_2332_, v_resStartStop_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec_ref(v_opts_2329_);
return v_res_2339_;
}
}
static double _init_l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2342_; double v___x_2343_; 
v___x_2342_ = lean_unsigned_to_nat(1000000000u);
v___x_2343_ = lean_float_of_nat(v___x_2342_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1(lean_object* v_decl_2344_, lean_object* v___x_2345_, uint8_t v___x_2346_, lean_object* v___x_2347_, lean_object* v___f_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v___y_2353_; lean_object* v___y_2354_; uint8_t v___y_2355_; lean_object* v___y_2366_; lean_object* v_a_2367_; lean_object* v___y_2371_; lean_object* v___y_2372_; uint8_t v___y_2373_; lean_object* v___y_2384_; lean_object* v_a_2385_; lean_object* v_options_2388_; uint8_t v_hasTrace_2389_; 
v_options_2388_ = lean_ctor_get(v___y_2349_, 2);
v_hasTrace_2389_ = lean_ctor_get_uint8(v_options_2388_, sizeof(void*)*1);
if (v_hasTrace_2389_ == 0)
{
lean_object* v_cancelTk_x3f_2390_; lean_object* v___x_2391_; 
lean_dec_ref(v___f_2348_);
lean_dec_ref(v___x_2347_);
lean_dec(v___x_2345_);
v_cancelTk_x3f_2390_ = lean_ctor_get(v___y_2349_, 12);
lean_inc(v_decl_2344_);
v___x_2391_ = l_Lean_warnIfUsesSorry(v_decl_2344_, v___y_2349_, v___y_2350_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v___x_2392_; lean_object* v_env_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
lean_dec_ref(v___x_2391_);
v___x_2392_ = lean_st_ref_get(v___y_2350_);
v_env_2393_ = lean_ctor_get(v___x_2392_, 0);
lean_inc_ref(v_env_2393_);
lean_dec(v___x_2392_);
v___x_2394_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2393_, v_options_2388_, v_decl_2344_, v_cancelTk_x3f_2390_);
v___x_2395_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_2394_, v___y_2349_, v___y_2350_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; lean_object* v___x_2397_; 
lean_dec(v_decl_2344_);
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_a_2396_);
lean_dec_ref(v___x_2395_);
v___x_2397_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_2396_, v___y_2350_);
return v___x_2397_;
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
v_a_2398_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2395_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2395_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
lean_inc(v_a_2398_);
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_a_2398_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
v___y_2384_ = v___x_2403_;
v_a_2385_ = v_a_2398_;
goto v___jp_2383_;
}
}
}
}
else
{
lean_dec(v_decl_2344_);
return v___x_2391_;
}
}
else
{
lean_object* v_cancelTk_x3f_2406_; lean_object* v_inheritedTraceOptions_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; uint8_t v___x_2410_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v_a_2414_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v_a_2429_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v_a_2434_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; uint8_t v___y_2446_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v_a_2451_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v_a_2457_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v_a_2469_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v_a_2474_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; uint8_t v___y_2486_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v_a_2491_; 
v_cancelTk_x3f_2406_ = lean_ctor_get(v___y_2349_, 12);
v_inheritedTraceOptions_2407_ = lean_ctor_get(v___y_2349_, 13);
v___x_2408_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v___x_2345_);
v___x_2409_ = l_Lean_Name_append(v___x_2408_, v___x_2345_);
v___x_2410_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2407_, v_options_2388_, v___x_2409_);
lean_dec(v___x_2409_);
if (v___x_2410_ == 0)
{
lean_object* v___x_2519_; uint8_t v___x_2520_; 
v___x_2519_ = l_Lean_trace_profiler;
v___x_2520_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2388_, v___x_2519_);
if (v___x_2520_ == 0)
{
lean_object* v___x_2521_; 
lean_dec_ref(v___f_2348_);
lean_dec_ref(v___x_2347_);
lean_dec(v___x_2345_);
lean_inc(v_decl_2344_);
v___x_2521_ = l_Lean_warnIfUsesSorry(v_decl_2344_, v___y_2349_, v___y_2350_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v___x_2522_; lean_object* v_env_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
lean_dec_ref(v___x_2521_);
v___x_2522_ = lean_st_ref_get(v___y_2350_);
v_env_2523_ = lean_ctor_get(v___x_2522_, 0);
lean_inc_ref(v_env_2523_);
lean_dec(v___x_2522_);
v___x_2524_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2523_, v_options_2388_, v_decl_2344_, v_cancelTk_x3f_2406_);
v___x_2525_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_2524_, v___y_2349_, v___y_2350_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; lean_object* v___x_2527_; 
lean_dec(v_decl_2344_);
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_a_2526_);
lean_dec_ref(v___x_2525_);
v___x_2527_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_2526_, v___y_2350_);
return v___x_2527_;
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
v_a_2528_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2525_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2525_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
lean_inc(v_a_2528_);
if (v_isShared_2531_ == 0)
{
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2528_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
v___y_2366_ = v___x_2533_;
v_a_2367_ = v_a_2528_;
goto v___jp_2365_;
}
}
}
}
else
{
lean_dec(v_decl_2344_);
return v___x_2521_;
}
}
else
{
goto v___jp_2494_;
}
}
else
{
goto v___jp_2494_;
}
v___jp_2411_:
{
lean_object* v___x_2415_; double v___x_2416_; double v___x_2417_; double v___x_2418_; double v___x_2419_; double v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2415_ = lean_io_mono_nanos_now();
v___x_2416_ = lean_float_of_nat(v___y_2412_);
v___x_2417_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__1);
v___x_2418_ = lean_float_div(v___x_2416_, v___x_2417_);
v___x_2419_ = lean_float_of_nat(v___x_2415_);
v___x_2420_ = lean_float_div(v___x_2419_, v___x_2417_);
v___x_2421_ = lean_box_float(v___x_2418_);
v___x_2422_ = lean_box_float(v___x_2420_);
v___x_2423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2421_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
v___x_2424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2424_, 0, v_a_2414_);
lean_ctor_set(v___x_2424_, 1, v___x_2423_);
v___x_2425_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2(v___x_2345_, v___x_2346_, v___x_2347_, v_options_2388_, v___x_2410_, v___y_2413_, v___f_2348_, v___x_2424_, v___y_2349_, v___y_2350_);
return v___x_2425_;
}
v___jp_2426_:
{
lean_object* v___x_2430_; 
v___x_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2430_, 0, v_a_2429_);
v___y_2412_ = v___y_2427_;
v___y_2413_ = v___y_2428_;
v_a_2414_ = v___x_2430_;
goto v___jp_2411_;
}
v___jp_2431_:
{
lean_object* v___x_2435_; 
v___x_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2435_, 0, v_a_2434_);
v___y_2412_ = v___y_2432_;
v___y_2413_ = v___y_2433_;
v_a_2414_ = v___x_2435_;
goto v___jp_2411_;
}
v___jp_2436_:
{
if (lean_obj_tag(v___y_2439_) == 0)
{
lean_object* v_a_2440_; 
v_a_2440_ = lean_ctor_get(v___y_2439_, 0);
lean_inc(v_a_2440_);
lean_dec_ref(v___y_2439_);
v___y_2432_ = v___y_2437_;
v___y_2433_ = v___y_2438_;
v_a_2434_ = v_a_2440_;
goto v___jp_2431_;
}
else
{
lean_object* v_a_2441_; 
v_a_2441_ = lean_ctor_get(v___y_2439_, 0);
lean_inc(v_a_2441_);
lean_dec_ref(v___y_2439_);
v___y_2427_ = v___y_2437_;
v___y_2428_ = v___y_2438_;
v_a_2429_ = v_a_2441_;
goto v___jp_2426_;
}
}
v___jp_2442_:
{
if (v___y_2446_ == 0)
{
lean_object* v___x_2447_; 
v___x_2447_ = l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom(v_decl_2344_, v___y_2349_, v___y_2350_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_dec_ref(v___x_2447_);
v___y_2427_ = v___y_2444_;
v___y_2428_ = v___y_2445_;
v_a_2429_ = v___y_2443_;
goto v___jp_2426_;
}
else
{
lean_dec_ref(v___y_2443_);
v___y_2437_ = v___y_2444_;
v___y_2438_ = v___y_2445_;
v___y_2439_ = v___x_2447_;
goto v___jp_2436_;
}
}
else
{
lean_dec(v_decl_2344_);
v___y_2427_ = v___y_2444_;
v___y_2428_ = v___y_2445_;
v_a_2429_ = v___y_2443_;
goto v___jp_2426_;
}
}
v___jp_2448_:
{
uint8_t v___x_2452_; 
v___x_2452_ = l_Lean_Exception_isInterrupt(v_a_2451_);
if (v___x_2452_ == 0)
{
uint8_t v___x_2453_; 
lean_inc_ref(v_a_2451_);
v___x_2453_ = l_Lean_Exception_isRuntime(v_a_2451_);
v___y_2443_ = v_a_2451_;
v___y_2444_ = v___y_2449_;
v___y_2445_ = v___y_2450_;
v___y_2446_ = v___x_2453_;
goto v___jp_2442_;
}
else
{
v___y_2443_ = v_a_2451_;
v___y_2444_ = v___y_2449_;
v___y_2445_ = v___y_2450_;
v___y_2446_ = v___x_2452_;
goto v___jp_2442_;
}
}
v___jp_2454_:
{
lean_object* v___x_2458_; double v___x_2459_; double v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2458_ = lean_io_get_num_heartbeats();
v___x_2459_ = lean_float_of_nat(v___y_2456_);
v___x_2460_ = lean_float_of_nat(v___x_2458_);
v___x_2461_ = lean_box_float(v___x_2459_);
v___x_2462_ = lean_box_float(v___x_2460_);
v___x_2463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2461_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
v___x_2464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2464_, 0, v_a_2457_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
v___x_2465_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2(v___x_2345_, v___x_2346_, v___x_2347_, v_options_2388_, v___x_2410_, v___y_2455_, v___f_2348_, v___x_2464_, v___y_2349_, v___y_2350_);
return v___x_2465_;
}
v___jp_2466_:
{
lean_object* v___x_2470_; 
v___x_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2470_, 0, v_a_2469_);
v___y_2455_ = v___y_2467_;
v___y_2456_ = v___y_2468_;
v_a_2457_ = v___x_2470_;
goto v___jp_2454_;
}
v___jp_2471_:
{
lean_object* v___x_2475_; 
v___x_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2475_, 0, v_a_2474_);
v___y_2455_ = v___y_2472_;
v___y_2456_ = v___y_2473_;
v_a_2457_ = v___x_2475_;
goto v___jp_2454_;
}
v___jp_2476_:
{
if (lean_obj_tag(v___y_2479_) == 0)
{
lean_object* v_a_2480_; 
v_a_2480_ = lean_ctor_get(v___y_2479_, 0);
lean_inc(v_a_2480_);
lean_dec_ref(v___y_2479_);
v___y_2472_ = v___y_2477_;
v___y_2473_ = v___y_2478_;
v_a_2474_ = v_a_2480_;
goto v___jp_2471_;
}
else
{
lean_object* v_a_2481_; 
v_a_2481_ = lean_ctor_get(v___y_2479_, 0);
lean_inc(v_a_2481_);
lean_dec_ref(v___y_2479_);
v___y_2467_ = v___y_2477_;
v___y_2468_ = v___y_2478_;
v_a_2469_ = v_a_2481_;
goto v___jp_2466_;
}
}
v___jp_2482_:
{
if (v___y_2486_ == 0)
{
lean_object* v___x_2487_; 
v___x_2487_ = l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom(v_decl_2344_, v___y_2349_, v___y_2350_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_dec_ref(v___x_2487_);
v___y_2467_ = v___y_2483_;
v___y_2468_ = v___y_2484_;
v_a_2469_ = v___y_2485_;
goto v___jp_2466_;
}
else
{
lean_dec_ref(v___y_2485_);
v___y_2477_ = v___y_2483_;
v___y_2478_ = v___y_2484_;
v___y_2479_ = v___x_2487_;
goto v___jp_2476_;
}
}
else
{
lean_dec(v_decl_2344_);
v___y_2467_ = v___y_2483_;
v___y_2468_ = v___y_2484_;
v_a_2469_ = v___y_2485_;
goto v___jp_2466_;
}
}
v___jp_2488_:
{
uint8_t v___x_2492_; 
v___x_2492_ = l_Lean_Exception_isInterrupt(v_a_2491_);
if (v___x_2492_ == 0)
{
uint8_t v___x_2493_; 
lean_inc_ref(v_a_2491_);
v___x_2493_ = l_Lean_Exception_isRuntime(v_a_2491_);
v___y_2483_ = v___y_2489_;
v___y_2484_ = v___y_2490_;
v___y_2485_ = v_a_2491_;
v___y_2486_ = v___x_2493_;
goto v___jp_2482_;
}
else
{
v___y_2483_ = v___y_2489_;
v___y_2484_ = v___y_2490_;
v___y_2485_ = v_a_2491_;
v___y_2486_ = v___x_2492_;
goto v___jp_2482_;
}
}
v___jp_2494_:
{
lean_object* v___x_2495_; lean_object* v_a_2496_; lean_object* v___x_2497_; uint8_t v___x_2498_; 
v___x_2495_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v___y_2350_);
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_a_2496_);
lean_dec_ref(v___x_2495_);
v___x_2497_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2498_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2388_, v___x_2497_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2499_ = lean_io_mono_nanos_now();
lean_inc(v_decl_2344_);
v___x_2500_ = l_Lean_warnIfUsesSorry(v_decl_2344_, v___y_2349_, v___y_2350_);
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v___x_2501_; lean_object* v_env_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
lean_dec_ref(v___x_2500_);
v___x_2501_ = lean_st_ref_get(v___y_2350_);
v_env_2502_ = lean_ctor_get(v___x_2501_, 0);
lean_inc_ref(v_env_2502_);
lean_dec(v___x_2501_);
v___x_2503_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2502_, v_options_2388_, v_decl_2344_, v_cancelTk_x3f_2406_);
v___x_2504_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_2503_, v___y_2349_, v___y_2350_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2505_; lean_object* v___x_2506_; lean_object* v_a_2507_; 
lean_dec(v_decl_2344_);
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_a_2505_);
lean_dec_ref(v___x_2504_);
v___x_2506_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_2505_, v___y_2350_);
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
lean_inc(v_a_2507_);
lean_dec_ref(v___x_2506_);
v___y_2432_ = v___x_2499_;
v___y_2433_ = v_a_2496_;
v_a_2434_ = v_a_2507_;
goto v___jp_2431_;
}
else
{
lean_object* v_a_2508_; 
v_a_2508_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_a_2508_);
lean_dec_ref(v___x_2504_);
v___y_2449_ = v___x_2499_;
v___y_2450_ = v_a_2496_;
v_a_2451_ = v_a_2508_;
goto v___jp_2448_;
}
}
else
{
lean_dec(v_decl_2344_);
v___y_2437_ = v___x_2499_;
v___y_2438_ = v_a_2496_;
v___y_2439_ = v___x_2500_;
goto v___jp_2436_;
}
}
else
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2509_ = lean_io_get_num_heartbeats();
lean_inc(v_decl_2344_);
v___x_2510_ = l_Lean_warnIfUsesSorry(v_decl_2344_, v___y_2349_, v___y_2350_);
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v___x_2511_; lean_object* v_env_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
lean_dec_ref(v___x_2510_);
v___x_2511_ = lean_st_ref_get(v___y_2350_);
v_env_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc_ref(v_env_2512_);
lean_dec(v___x_2511_);
v___x_2513_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2512_, v_options_2388_, v_decl_2344_, v_cancelTk_x3f_2406_);
v___x_2514_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_2513_, v___y_2349_, v___y_2350_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; lean_object* v___x_2516_; lean_object* v_a_2517_; 
lean_dec(v_decl_2344_);
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2515_);
lean_dec_ref(v___x_2514_);
v___x_2516_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_2515_, v___y_2350_);
v_a_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_a_2517_);
lean_dec_ref(v___x_2516_);
v___y_2472_ = v_a_2496_;
v___y_2473_ = v___x_2509_;
v_a_2474_ = v_a_2517_;
goto v___jp_2471_;
}
else
{
lean_object* v_a_2518_; 
v_a_2518_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2518_);
lean_dec_ref(v___x_2514_);
v___y_2489_ = v_a_2496_;
v___y_2490_ = v___x_2509_;
v_a_2491_ = v_a_2518_;
goto v___jp_2488_;
}
}
else
{
lean_dec(v_decl_2344_);
v___y_2477_ = v_a_2496_;
v___y_2478_ = v___x_2509_;
v___y_2479_ = v___x_2510_;
goto v___jp_2476_;
}
}
}
}
v___jp_2352_:
{
if (v___y_2355_ == 0)
{
lean_object* v___x_2356_; 
lean_dec_ref(v___y_2353_);
v___x_2356_ = l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom(v_decl_2344_, v___y_2349_, v___y_2350_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2363_ == 0)
{
lean_object* v_unused_2364_; 
v_unused_2364_ = lean_ctor_get(v___x_2356_, 0);
lean_dec(v_unused_2364_);
v___x_2358_ = v___x_2356_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_dec(v___x_2356_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
lean_ctor_set_tag(v___x_2358_, 1);
lean_ctor_set(v___x_2358_, 0, v___y_2354_);
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___y_2354_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
else
{
lean_dec_ref(v___y_2354_);
return v___x_2356_;
}
}
else
{
lean_dec_ref(v___y_2354_);
lean_dec(v_decl_2344_);
return v___y_2353_;
}
}
v___jp_2365_:
{
uint8_t v___x_2368_; 
v___x_2368_ = l_Lean_Exception_isInterrupt(v_a_2367_);
if (v___x_2368_ == 0)
{
uint8_t v___x_2369_; 
lean_inc_ref(v_a_2367_);
v___x_2369_ = l_Lean_Exception_isRuntime(v_a_2367_);
v___y_2353_ = v___y_2366_;
v___y_2354_ = v_a_2367_;
v___y_2355_ = v___x_2369_;
goto v___jp_2352_;
}
else
{
v___y_2353_ = v___y_2366_;
v___y_2354_ = v_a_2367_;
v___y_2355_ = v___x_2368_;
goto v___jp_2352_;
}
}
v___jp_2370_:
{
if (v___y_2373_ == 0)
{
lean_object* v___x_2374_; 
lean_dec_ref(v___y_2372_);
v___x_2374_ = l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom(v_decl_2344_, v___y_2349_, v___y_2350_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2381_; 
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2381_ == 0)
{
lean_object* v_unused_2382_; 
v_unused_2382_ = lean_ctor_get(v___x_2374_, 0);
lean_dec(v_unused_2382_);
v___x_2376_ = v___x_2374_;
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
else
{
lean_dec(v___x_2374_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2377_ == 0)
{
lean_ctor_set_tag(v___x_2376_, 1);
lean_ctor_set(v___x_2376_, 0, v___y_2371_);
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___y_2371_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
else
{
lean_dec_ref(v___y_2371_);
return v___x_2374_;
}
}
else
{
lean_dec_ref(v___y_2371_);
lean_dec(v_decl_2344_);
return v___y_2372_;
}
}
v___jp_2383_:
{
uint8_t v___x_2386_; 
v___x_2386_ = l_Lean_Exception_isInterrupt(v_a_2385_);
if (v___x_2386_ == 0)
{
uint8_t v___x_2387_; 
lean_inc_ref(v_a_2385_);
v___x_2387_ = l_Lean_Exception_isRuntime(v_a_2385_);
v___y_2371_ = v_a_2385_;
v___y_2372_ = v___y_2384_;
v___y_2373_ = v___x_2387_;
goto v___jp_2370_;
}
else
{
v___y_2371_ = v_a_2385_;
v___y_2372_ = v___y_2384_;
v___y_2373_ = v___x_2386_;
goto v___jp_2370_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___boxed(lean_object* v_decl_2536_, lean_object* v___x_2537_, lean_object* v___x_2538_, lean_object* v___x_2539_, lean_object* v___f_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
uint8_t v___x_8068__boxed_2544_; lean_object* v_res_2545_; 
v___x_8068__boxed_2544_ = lean_unbox(v___x_2538_);
v_res_2545_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1(v_decl_2536_, v___x_2537_, v___x_8068__boxed_2544_, v___x_2539_, v___f_2540_, v___y_2541_, v___y_2542_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(lean_object* v_decl_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_){
_start:
{
lean_object* v_options_2554_; lean_object* v___f_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; uint8_t v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___f_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
v_options_2554_ = lean_ctor_get(v_a_2551_, 2);
lean_inc(v_decl_2550_);
v___f_2555_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2555_, 0, v_decl_2550_);
v___x_2556_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___closed__0));
v___x_2557_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___closed__2));
v___x_2558_ = 1;
v___x_2559_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2560_ = lean_box(v___x_2558_);
v___f_2561_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___boxed), 8, 5);
lean_closure_set(v___f_2561_, 0, v_decl_2550_);
lean_closure_set(v___f_2561_, 1, v___x_2557_);
lean_closure_set(v___f_2561_, 2, v___x_2560_);
lean_closure_set(v___f_2561_, 3, v___x_2559_);
lean_closure_set(v___f_2561_, 4, v___f_2555_);
v___x_2562_ = lean_box(0);
v___x_2563_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___redArg(v___x_2556_, v_options_2554_, v___f_2561_, v___x_2562_, v_a_2551_, v_a_2552_);
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___boxed(lean_object* v_decl_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_2564_, v_a_2565_, v_a_2566_);
lean_dec(v_a_2566_);
lean_dec_ref(v_a_2565_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4(lean_object* v_00_u03b1_2569_, lean_object* v_x_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v___x_2574_; 
v___x_2574_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4___redArg(v_x_2570_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2575_, lean_object* v_x_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4(v_00_u03b1_2575_, v_x_2576_, v___y_2577_, v___y_2578_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__0(lean_object* v___y_2581_, lean_object* v_a_2582_, lean_object* v___y_2583_, lean_object* v_a_x3f_2584_){
_start:
{
lean_object* v___x_2586_; lean_object* v_env_2587_; lean_object* v___x_2588_; 
v___x_2586_ = lean_st_ref_get(v___y_2581_);
v_env_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc_ref(v_env_2587_);
lean_dec(v___x_2586_);
v___x_2588_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2582_, v_env_2587_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2588_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2588_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
else
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2609_; 
v_a_2597_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2599_ = v___x_2588_;
v_isShared_2600_ = v_isSharedCheck_2609_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2588_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2609_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v_ref_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2607_; 
v_ref_2601_ = lean_ctor_get(v___y_2583_, 5);
v___x_2602_ = lean_io_error_to_string(v_a_2597_);
v___x_2603_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2602_);
v___x_2604_ = l_Lean_MessageData_ofFormat(v___x_2603_);
lean_inc(v_ref_2601_);
v___x_2605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2605_, 0, v_ref_2601_);
lean_ctor_set(v___x_2605_, 1, v___x_2604_);
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 0, v___x_2605_);
v___x_2607_ = v___x_2599_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2605_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__0___boxed(lean_object* v___y_2610_, lean_object* v_a_2611_, lean_object* v___y_2612_, lean_object* v_a_x3f_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Lean_addDecl___lam__0(v___y_2610_, v_a_2611_, v___y_2612_, v_a_x3f_2613_);
lean_dec(v_a_x3f_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2610_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__2(lean_object* v_asyncEnv_2616_, lean_object* v_a_2617_, lean_object* v_decl_2618_, lean_object* v_x_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v___x_2623_; lean_object* v_r_2624_; 
v___x_2623_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_asyncEnv_2616_, v___y_2621_);
lean_dec_ref(v___x_2623_);
v_r_2624_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_2618_, v___y_2620_, v___y_2621_);
if (lean_obj_tag(v_r_2624_) == 0)
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2641_; 
v_a_2625_ = lean_ctor_get(v_r_2624_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v_r_2624_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2627_ = v_r_2624_;
v_isShared_2628_ = v_isSharedCheck_2641_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v_r_2624_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2641_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
lean_inc(v_a_2625_);
if (v_isShared_2628_ == 0)
{
lean_ctor_set_tag(v___x_2627_, 1);
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
lean_object* v___x_2631_; 
v___x_2631_ = l_Lean_addDecl___lam__0(v___y_2621_, v_a_2617_, v___y_2620_, v___x_2630_);
lean_dec_ref(v___x_2630_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2638_ == 0)
{
lean_object* v_unused_2639_; 
v_unused_2639_ = lean_ctor_get(v___x_2631_, 0);
lean_dec(v_unused_2639_);
v___x_2633_ = v___x_2631_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_dec(v___x_2631_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 0, v_a_2625_);
v___x_2636_ = v___x_2633_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2625_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
else
{
lean_dec(v_a_2625_);
return v___x_2631_;
}
}
}
}
else
{
lean_object* v_a_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
v_a_2642_ = lean_ctor_get(v_r_2624_, 0);
lean_inc(v_a_2642_);
lean_dec_ref(v_r_2624_);
v___x_2643_ = lean_box(0);
v___x_2644_ = l_Lean_addDecl___lam__0(v___y_2621_, v_a_2617_, v___y_2620_, v___x_2643_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2651_ == 0)
{
lean_object* v_unused_2652_; 
v_unused_2652_ = lean_ctor_get(v___x_2644_, 0);
lean_dec(v_unused_2652_);
v___x_2646_ = v___x_2644_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_dec(v___x_2644_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
lean_ctor_set_tag(v___x_2646_, 1);
lean_ctor_set(v___x_2646_, 0, v_a_2642_);
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2642_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
else
{
lean_dec(v_a_2642_);
return v___x_2644_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__2___boxed(lean_object* v_asyncEnv_2653_, lean_object* v_a_2654_, lean_object* v_decl_2655_, lean_object* v_x_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l_Lean_addDecl___lam__2(v_asyncEnv_2653_, v_a_2654_, v_decl_2655_, v_x_2656_, v___y_2657_, v___y_2658_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec_ref(v_x_2656_);
return v_res_2660_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2662_ = ((lean_object*)(l_Lean_addDecl___lam__1___closed__0));
v___x_2663_ = l_Lean_stringToMessageData(v___x_2662_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__1(lean_object* v_decl_2664_, lean_object* v_x_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2669_ = lean_obj_once(&l_Lean_addDecl___lam__1___closed__1, &l_Lean_addDecl___lam__1___closed__1_once, _init_l_Lean_addDecl___lam__1___closed__1);
v___x_2670_ = l_Lean_Declaration_getNames(v_decl_2664_);
v___x_2671_ = lean_box(0);
v___x_2672_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__0(v___x_2670_, v___x_2671_);
v___x_2673_ = l_Lean_MessageData_ofList(v___x_2672_);
v___x_2674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2669_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
v___x_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2674_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__1___boxed(lean_object* v_decl_2676_, lean_object* v_x_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l_Lean_addDecl___lam__1(v_decl_2676_, v_x_2677_, v___y_2678_, v___y_2679_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec_ref(v_x_2677_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_addDecl_spec__0(lean_object* v_cls_2684_, lean_object* v_msg_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v_ref_2689_; lean_object* v___x_2690_; lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2736_; 
v_ref_2689_ = lean_ctor_get(v___y_2686_, 5);
v___x_2690_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2685_, v___y_2686_, v___y_2687_);
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2693_ = v___x_2690_;
v_isShared_2694_ = v_isSharedCheck_2736_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2690_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2736_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2695_; lean_object* v_traceState_2696_; lean_object* v_env_2697_; lean_object* v_nextMacroScope_2698_; lean_object* v_ngen_2699_; lean_object* v_auxDeclNGen_2700_; lean_object* v_cache_2701_; lean_object* v_messages_2702_; lean_object* v_infoState_2703_; lean_object* v_snapshotTasks_2704_; lean_object* v_newDecls_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2735_; 
v___x_2695_ = lean_st_ref_take(v___y_2687_);
v_traceState_2696_ = lean_ctor_get(v___x_2695_, 4);
v_env_2697_ = lean_ctor_get(v___x_2695_, 0);
v_nextMacroScope_2698_ = lean_ctor_get(v___x_2695_, 1);
v_ngen_2699_ = lean_ctor_get(v___x_2695_, 2);
v_auxDeclNGen_2700_ = lean_ctor_get(v___x_2695_, 3);
v_cache_2701_ = lean_ctor_get(v___x_2695_, 5);
v_messages_2702_ = lean_ctor_get(v___x_2695_, 6);
v_infoState_2703_ = lean_ctor_get(v___x_2695_, 7);
v_snapshotTasks_2704_ = lean_ctor_get(v___x_2695_, 8);
v_newDecls_2705_ = lean_ctor_get(v___x_2695_, 9);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2707_ = v___x_2695_;
v_isShared_2708_ = v_isSharedCheck_2735_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_newDecls_2705_);
lean_inc(v_snapshotTasks_2704_);
lean_inc(v_infoState_2703_);
lean_inc(v_messages_2702_);
lean_inc(v_cache_2701_);
lean_inc(v_traceState_2696_);
lean_inc(v_auxDeclNGen_2700_);
lean_inc(v_ngen_2699_);
lean_inc(v_nextMacroScope_2698_);
lean_inc(v_env_2697_);
lean_dec(v___x_2695_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2735_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
uint64_t v_tid_2709_; lean_object* v_traces_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2734_; 
v_tid_2709_ = lean_ctor_get_uint64(v_traceState_2696_, sizeof(void*)*1);
v_traces_2710_ = lean_ctor_get(v_traceState_2696_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v_traceState_2696_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2712_ = v_traceState_2696_;
v_isShared_2713_ = v_isSharedCheck_2734_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_traces_2710_);
lean_dec(v_traceState_2696_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2734_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2714_; double v___x_2715_; uint8_t v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2724_; 
v___x_2714_ = lean_box(0);
v___x_2715_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__2);
v___x_2716_ = 0;
v___x_2717_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2718_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2718_, 0, v_cls_2684_);
lean_ctor_set(v___x_2718_, 1, v___x_2714_);
lean_ctor_set(v___x_2718_, 2, v___x_2717_);
lean_ctor_set_float(v___x_2718_, sizeof(void*)*3, v___x_2715_);
lean_ctor_set_float(v___x_2718_, sizeof(void*)*3 + 8, v___x_2715_);
lean_ctor_set_uint8(v___x_2718_, sizeof(void*)*3 + 16, v___x_2716_);
v___x_2719_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_addDecl_spec__0___closed__0));
v___x_2720_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2718_);
lean_ctor_set(v___x_2720_, 1, v_a_2691_);
lean_ctor_set(v___x_2720_, 2, v___x_2719_);
lean_inc(v_ref_2689_);
v___x_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2721_, 0, v_ref_2689_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
v___x_2722_ = l_Lean_PersistentArray_push___redArg(v_traces_2710_, v___x_2721_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 0, v___x_2722_);
v___x_2724_ = v___x_2712_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v___x_2722_);
lean_ctor_set_uint64(v_reuseFailAlloc_2733_, sizeof(void*)*1, v_tid_2709_);
v___x_2724_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
lean_object* v___x_2726_; 
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 4, v___x_2724_);
v___x_2726_ = v___x_2707_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_env_2697_);
lean_ctor_set(v_reuseFailAlloc_2732_, 1, v_nextMacroScope_2698_);
lean_ctor_set(v_reuseFailAlloc_2732_, 2, v_ngen_2699_);
lean_ctor_set(v_reuseFailAlloc_2732_, 3, v_auxDeclNGen_2700_);
lean_ctor_set(v_reuseFailAlloc_2732_, 4, v___x_2724_);
lean_ctor_set(v_reuseFailAlloc_2732_, 5, v_cache_2701_);
lean_ctor_set(v_reuseFailAlloc_2732_, 6, v_messages_2702_);
lean_ctor_set(v_reuseFailAlloc_2732_, 7, v_infoState_2703_);
lean_ctor_set(v_reuseFailAlloc_2732_, 8, v_snapshotTasks_2704_);
lean_ctor_set(v_reuseFailAlloc_2732_, 9, v_newDecls_2705_);
v___x_2726_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2730_; 
v___x_2727_ = lean_st_ref_set(v___y_2687_, v___x_2726_);
v___x_2728_ = lean_box(0);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 0, v___x_2728_);
v___x_2730_ = v___x_2693_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v___x_2728_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_addDecl_spec__0___boxed(lean_object* v_cls_2737_, lean_object* v_msg_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_2737_, v_msg_2738_, v___y_2739_, v___y_2740_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
return v_res_2742_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2744_ = ((lean_object*)(l_Lean_addDecl___lam__3___closed__0));
v___x_2745_ = l_Lean_stringToMessageData(v___x_2744_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__3(lean_object* v_decl_2746_, lean_object* v_cls_2747_, lean_object* v_x_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_options_2752_; uint8_t v_hasTrace_2753_; 
v_options_2752_ = lean_ctor_get(v___y_2749_, 2);
v_hasTrace_2753_ = lean_ctor_get_uint8(v_options_2752_, sizeof(void*)*1);
if (v_hasTrace_2753_ == 0)
{
lean_object* v___x_2754_; 
lean_dec(v_cls_2747_);
v___x_2754_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_2746_, v___y_2749_, v___y_2750_);
return v___x_2754_;
}
else
{
lean_object* v_inheritedTraceOptions_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; uint8_t v___x_2758_; 
v_inheritedTraceOptions_2755_ = lean_ctor_get(v___y_2749_, 13);
v___x_2756_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v_cls_2747_);
v___x_2757_ = l_Lean_Name_append(v___x_2756_, v_cls_2747_);
v___x_2758_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2755_, v_options_2752_, v___x_2757_);
lean_dec(v___x_2757_);
if (v___x_2758_ == 0)
{
lean_object* v___x_2759_; 
lean_dec(v_cls_2747_);
v___x_2759_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_2746_, v___y_2749_, v___y_2750_);
return v___x_2759_;
}
else
{
lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2760_ = lean_obj_once(&l_Lean_addDecl___lam__3___closed__1, &l_Lean_addDecl___lam__3___closed__1_once, _init_l_Lean_addDecl___lam__3___closed__1);
v___x_2761_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_2747_, v___x_2760_, v___y_2749_, v___y_2750_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v___x_2762_; 
lean_dec_ref(v___x_2761_);
v___x_2762_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_2746_, v___y_2749_, v___y_2750_);
return v___x_2762_;
}
else
{
lean_dec(v_decl_2746_);
return v___x_2761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__3___boxed(lean_object* v_decl_2763_, lean_object* v_cls_2764_, lean_object* v_x_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l_Lean_addDecl___lam__3(v_decl_2763_, v_cls_2764_, v_x_2765_, v___y_2766_, v___y_2767_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v_x_2765_);
return v_res_2769_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_addDecl_spec__2(lean_object* v_x_2770_){
_start:
{
if (lean_obj_tag(v_x_2770_) == 0)
{
uint8_t v___x_2771_; 
v___x_2771_ = 1;
return v___x_2771_;
}
else
{
lean_object* v_head_2772_; lean_object* v_tail_2773_; uint8_t v___x_2774_; 
v_head_2772_ = lean_ctor_get(v_x_2770_, 0);
v_tail_2773_ = lean_ctor_get(v_x_2770_, 1);
v___x_2774_ = l_Lean_isPrivateName(v_head_2772_);
if (v___x_2774_ == 0)
{
return v___x_2774_;
}
else
{
v_x_2770_ = v_tail_2773_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_addDecl_spec__2___boxed(lean_object* v_x_2776_){
_start:
{
uint8_t v_res_2777_; lean_object* v_r_2778_; 
v_res_2777_ = l_List_all___at___00Lean_addDecl_spec__2(v_x_2776_);
lean_dec(v_x_2776_);
v_r_2778_ = lean_box(v_res_2777_);
return v_r_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_addDecl_spec__3___redArg(lean_object* v_opt_2779_, lean_object* v___y_2780_){
_start:
{
lean_object* v_options_2782_; uint8_t v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; 
v_options_2782_ = lean_ctor_get(v___y_2780_, 2);
v___x_2783_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2782_, v_opt_2779_);
v___x_2784_ = lean_box(v___x_2783_);
v___x_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_addDecl_spec__3___redArg___boxed(lean_object* v_opt_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__3___redArg(v_opt_2786_, v___y_2787_);
lean_dec_ref(v___y_2787_);
lean_dec_ref(v_opt_2786_);
return v_res_2789_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__8___closed__1(void){
_start:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2791_ = ((lean_object*)(l_Lean_addDecl___lam__8___closed__0));
v___x_2792_ = l_Lean_stringToMessageData(v___x_2791_);
return v___x_2792_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__8___closed__3(void){
_start:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2794_ = ((lean_object*)(l_Lean_addDecl___lam__8___closed__2));
v___x_2795_ = l_Lean_stringToMessageData(v___x_2794_);
return v___x_2795_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__8___closed__5(void){
_start:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2797_ = ((lean_object*)(l_Lean_addDecl___lam__8___closed__4));
v___x_2798_ = l_Lean_stringToMessageData(v___x_2797_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__8(lean_object* v_decl_2799_, lean_object* v___x_2800_, uint8_t v_hasTrace_2801_, uint8_t v___x_2802_, lean_object* v___x_2803_, lean_object* v_cls_2804_, lean_object* v___x_2805_, lean_object* v_____x_2806_, lean_object* v_exportedInfo_x3f_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v_a_2814_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v_a_2827_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v_snd_2911_; lean_object* v_fst_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_3040_; 
v_snd_2911_ = lean_ctor_get(v_____x_2806_, 1);
v_fst_2912_ = lean_ctor_get(v_____x_2806_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v_____x_2806_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_2914_ = v_____x_2806_;
v_isShared_2915_ = v_isSharedCheck_3040_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_snd_2911_);
lean_inc(v_fst_2912_);
lean_dec(v_____x_2806_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_3040_;
goto v_resetjp_2913_;
}
v___jp_2811_:
{
lean_object* v___x_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
v___x_2815_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_2813_, v___y_2812_);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2822_ == 0)
{
lean_object* v_unused_2823_; 
v_unused_2823_ = lean_ctor_get(v___x_2815_, 0);
lean_dec(v_unused_2823_);
v___x_2817_ = v___x_2815_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_dec(v___x_2815_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
lean_ctor_set_tag(v___x_2817_, 1);
lean_ctor_set(v___x_2817_, 0, v_a_2814_);
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2814_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
v___jp_2824_:
{
lean_object* v___x_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
v___x_2828_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_2826_, v___y_2825_);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2835_ == 0)
{
lean_object* v_unused_2836_; 
v_unused_2836_ = lean_ctor_get(v___x_2828_, 0);
lean_dec(v_unused_2836_);
v___x_2830_ = v___x_2828_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_dec(v___x_2828_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 0, v_a_2827_);
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2827_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
v___jp_2837_:
{
lean_object* v___x_2848_; 
lean_inc_ref(v___y_2846_);
v___x_2848_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_2839_, v___y_2846_, v___y_2842_, v___y_2847_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v___x_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2896_; 
lean_dec_ref(v___x_2848_);
lean_inc_ref(v___y_2843_);
v___x_2849_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_2843_, v___y_2841_);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2896_ == 0)
{
lean_object* v_unused_2897_; 
v_unused_2897_ = lean_ctor_get(v___x_2849_, 0);
lean_dec(v_unused_2897_);
v___x_2851_ = v___x_2849_;
v_isShared_2852_ = v_isSharedCheck_2896_;
goto v_resetjp_2850_;
}
else
{
lean_dec(v___x_2849_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2896_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v_options_2853_; lean_object* v___x_2854_; uint8_t v___x_2855_; 
v_options_2853_ = lean_ctor_get(v___y_2838_, 2);
v___x_2854_ = l_Lean_Elab_async;
v___x_2855_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2853_, v___x_2854_);
if (v___x_2855_ == 0)
{
lean_object* v___x_2856_; lean_object* v_r_2857_; 
lean_del_object(v___x_2851_);
lean_dec_ref(v___y_2845_);
lean_dec_ref(v___y_2840_);
lean_dec_ref(v___x_2800_);
v___x_2856_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_2846_, v___y_2841_);
lean_dec_ref(v___x_2856_);
v_r_2857_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_2799_, v___y_2838_, v___y_2841_);
if (lean_obj_tag(v_r_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2867_; 
v_a_2858_ = lean_ctor_get(v_r_2857_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v_r_2857_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2860_ = v_r_2857_;
v_isShared_2861_ = v_isSharedCheck_2867_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v_r_2857_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2867_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
lean_inc(v_a_2858_);
if (v_isShared_2861_ == 0)
{
lean_ctor_set_tag(v___x_2860_, 1);
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
lean_object* v___x_2864_; 
v___x_2864_ = lean_apply_2(v___y_2844_, v___x_2863_, lean_box(0));
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_dec_ref(v___x_2864_);
v___y_2825_ = v___y_2841_;
v___y_2826_ = v___y_2843_;
v_a_2827_ = v_a_2858_;
goto v___jp_2824_;
}
else
{
lean_object* v_a_2865_; 
lean_dec(v_a_2858_);
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2865_);
lean_dec_ref(v___x_2864_);
v___y_2812_ = v___y_2841_;
v___y_2813_ = v___y_2843_;
v_a_2814_ = v_a_2865_;
goto v___jp_2811_;
}
}
}
}
else
{
lean_object* v_a_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v_a_2868_ = lean_ctor_get(v_r_2857_, 0);
lean_inc(v_a_2868_);
lean_dec_ref(v_r_2857_);
v___x_2869_ = lean_box(0);
v___x_2870_ = lean_apply_2(v___y_2844_, v___x_2869_, lean_box(0));
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_dec_ref(v___x_2870_);
v___y_2812_ = v___y_2841_;
v___y_2813_ = v___y_2843_;
v_a_2814_ = v_a_2868_;
goto v___jp_2811_;
}
else
{
lean_object* v_a_2871_; 
lean_dec(v_a_2868_);
v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
lean_inc(v_a_2871_);
lean_dec_ref(v___x_2870_);
v___y_2812_ = v___y_2841_;
v___y_2813_ = v___y_2843_;
v_a_2814_ = v_a_2871_;
goto v___jp_2811_;
}
}
}
else
{
lean_object* v___x_2872_; lean_object* v___x_2874_; 
lean_dec_ref(v___y_2846_);
lean_dec_ref(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v_decl_2799_);
v___x_2872_ = l_IO_CancelToken_new();
if (v_isShared_2852_ == 0)
{
lean_ctor_set_tag(v___x_2851_, 1);
lean_ctor_set(v___x_2851_, 0, v___x_2872_);
v___x_2874_ = v___x_2851_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2872_);
v___x_2874_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2875_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__5_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_2876_ = l_Lean_Name_mkStr2(v___x_2875_, v___x_2800_);
v___x_2877_ = l_Lean_Name_toString(v___x_2876_, v_hasTrace_2801_);
lean_inc_ref(v___x_2874_);
v___x_2878_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_2840_, v___x_2874_, v___x_2877_, v___y_2838_, v___y_2841_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; lean_object* v_checked_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_a_2879_);
lean_dec_ref(v___x_2878_);
v_checked_2880_ = lean_ctor_get(v___y_2845_, 2);
lean_inc_ref(v_checked_2880_);
lean_dec_ref(v___y_2845_);
v___x_2881_ = lean_unsigned_to_nat(0u);
v___x_2882_ = lean_io_map_task(v_a_2879_, v_checked_2880_, v___x_2881_, v___x_2802_);
v___x_2883_ = lean_box(0);
v___x_2884_ = lean_box(2);
v___x_2885_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2883_);
lean_ctor_set(v___x_2885_, 1, v___x_2884_);
lean_ctor_set(v___x_2885_, 2, v___x_2874_);
lean_ctor_set(v___x_2885_, 3, v___x_2882_);
v___x_2886_ = l_Lean_Core_logSnapshotTask___redArg(v___x_2885_, v___y_2841_);
return v___x_2886_;
}
else
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
lean_dec_ref(v___x_2874_);
lean_dec_ref(v___y_2845_);
v_a_2887_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2878_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2878_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2892_; 
if (v_isShared_2890_ == 0)
{
v___x_2892_ = v___x_2889_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2887_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2910_; 
lean_dec_ref(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec_ref(v___y_2840_);
lean_dec_ref(v___x_2800_);
lean_dec(v_decl_2799_);
v_a_2898_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2900_ = v___x_2848_;
v_isShared_2901_ = v_isSharedCheck_2910_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2848_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2910_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v_ref_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2908_; 
v_ref_2902_ = lean_ctor_get(v___y_2838_, 5);
v___x_2903_ = lean_io_error_to_string(v_a_2898_);
v___x_2904_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2903_);
v___x_2905_ = l_Lean_MessageData_ofFormat(v___x_2904_);
lean_inc(v_ref_2902_);
v___x_2906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2906_, 0, v_ref_2902_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
if (v_isShared_2901_ == 0)
{
lean_ctor_set(v___x_2900_, 0, v___x_2906_);
v___x_2908_ = v___x_2900_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v___x_2906_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
}
v_resetjp_2913_:
{
lean_object* v_fst_2916_; lean_object* v_snd_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_3039_; 
v_fst_2916_ = lean_ctor_get(v_snd_2911_, 0);
v_snd_2917_ = lean_ctor_get(v_snd_2911_, 1);
v_isSharedCheck_3039_ = !lean_is_exclusive(v_snd_2911_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_2919_ = v_snd_2911_;
v_isShared_2920_ = v_isSharedCheck_3039_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_snd_2917_);
lean_inc(v_fst_2916_);
lean_dec(v_snd_2911_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_3039_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v_exportedInfo_x3f_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___x_3029_; lean_object* v_env_3030_; uint8_t v___x_3031_; 
v___x_3029_ = lean_st_ref_get(v___y_2809_);
v_env_3030_ = lean_ctor_get(v___x_3029_, 0);
lean_inc_ref(v_env_3030_);
lean_dec(v___x_3029_);
v___x_3031_ = l_Lean_Environment_containsOnBranch(v_env_3030_, v_fst_2912_);
lean_dec_ref(v_env_3030_);
if (v___x_3031_ == 0)
{
lean_del_object(v___x_2914_);
v___y_2997_ = v___y_2808_;
v___y_2998_ = v___y_2809_;
goto v___jp_2996_;
}
else
{
lean_object* v___x_3032_; lean_object* v_env_3033_; lean_object* v___x_3034_; lean_object* v___x_3036_; 
lean_del_object(v___x_2919_);
lean_dec(v_snd_2917_);
lean_dec(v_fst_2916_);
lean_dec(v_exportedInfo_x3f_2807_);
lean_dec(v___x_2805_);
lean_dec(v_cls_2804_);
lean_dec_ref(v___x_2803_);
lean_dec_ref(v___x_2800_);
lean_dec(v_decl_2799_);
v___x_3032_ = lean_st_ref_get(v___y_2809_);
v_env_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc_ref(v_env_3033_);
lean_dec(v___x_3032_);
v___x_3034_ = lean_elab_environment_to_kernel_env(v_env_3033_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set_tag(v___x_2914_, 1);
lean_ctor_set(v___x_2914_, 1, v_fst_2912_);
lean_ctor_set(v___x_2914_, 0, v___x_3034_);
v___x_3036_ = v___x_2914_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3034_);
lean_ctor_set(v_reuseFailAlloc_3038_, 1, v_fst_2912_);
v___x_3036_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
lean_object* v___x_3037_; 
v___x_3037_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(v___x_3036_, v___y_2808_, v___y_2809_);
return v___x_3037_;
}
}
v___jp_2921_:
{
uint8_t v___x_2929_; lean_object* v___x_2930_; 
v___x_2929_ = lean_unbox(v_snd_2917_);
lean_dec(v_snd_2917_);
lean_inc_ref(v___y_2923_);
v___x_2930_ = l_Lean_Environment_addConstAsync(v___y_2923_, v_fst_2912_, v___x_2929_, v___y_2928_, v___x_2802_, v_hasTrace_2801_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; lean_object* v_mainEnv_2932_; lean_object* v_asyncEnv_2933_; lean_object* v___f_2934_; lean_object* v___f_2935_; lean_object* v___x_2936_; 
lean_del_object(v___x_2919_);
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc_n(v_a_2931_, 3);
lean_dec_ref(v___x_2930_);
v_mainEnv_2932_ = lean_ctor_get(v_a_2931_, 0);
lean_inc_ref(v_mainEnv_2932_);
v_asyncEnv_2933_ = lean_ctor_get(v_a_2931_, 1);
lean_inc_ref_n(v_asyncEnv_2933_, 2);
lean_inc_ref(v___y_2924_);
lean_inc(v___y_2922_);
v___f_2934_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2934_, 0, v___y_2922_);
lean_closure_set(v___f_2934_, 1, v_a_2931_);
lean_closure_set(v___f_2934_, 2, v___y_2924_);
lean_inc(v_decl_2799_);
v___f_2935_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__2___boxed), 7, 3);
lean_closure_set(v___f_2935_, 0, v_asyncEnv_2933_);
lean_closure_set(v___f_2935_, 1, v_a_2931_);
lean_closure_set(v___f_2935_, 2, v_decl_2799_);
v___x_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2936_, 0, v_fst_2916_);
if (lean_obj_tag(v___y_2927_) == 0)
{
lean_inc_ref(v___x_2936_);
v___y_2838_ = v___y_2925_;
v___y_2839_ = v_a_2931_;
v___y_2840_ = v___f_2935_;
v___y_2841_ = v___y_2926_;
v___y_2842_ = v___x_2936_;
v___y_2843_ = v_mainEnv_2932_;
v___y_2844_ = v___f_2934_;
v___y_2845_ = v___y_2923_;
v___y_2846_ = v_asyncEnv_2933_;
v___y_2847_ = v___x_2936_;
goto v___jp_2837_;
}
else
{
v___y_2838_ = v___y_2925_;
v___y_2839_ = v_a_2931_;
v___y_2840_ = v___f_2935_;
v___y_2841_ = v___y_2926_;
v___y_2842_ = v___x_2936_;
v___y_2843_ = v_mainEnv_2932_;
v___y_2844_ = v___f_2934_;
v___y_2845_ = v___y_2923_;
v___y_2846_ = v_asyncEnv_2933_;
v___y_2847_ = v___y_2927_;
goto v___jp_2837_;
}
}
else
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2951_; 
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2923_);
lean_dec(v_fst_2916_);
lean_dec_ref(v___x_2800_);
lean_dec(v_decl_2799_);
v_a_2937_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2939_ = v___x_2930_;
v_isShared_2940_ = v_isSharedCheck_2951_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2930_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2951_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v_ref_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2946_; 
v_ref_2941_ = lean_ctor_get(v___y_2925_, 5);
v___x_2942_ = lean_io_error_to_string(v_a_2937_);
v___x_2943_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2942_);
v___x_2944_ = l_Lean_MessageData_ofFormat(v___x_2943_);
lean_inc(v_ref_2941_);
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 1, v___x_2944_);
lean_ctor_set(v___x_2919_, 0, v_ref_2941_);
v___x_2946_ = v___x_2919_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_ref_2941_);
lean_ctor_set(v_reuseFailAlloc_2950_, 1, v___x_2944_);
v___x_2946_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
lean_object* v___x_2948_; 
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 0, v___x_2946_);
v___x_2948_ = v___x_2939_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v___x_2946_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
}
v___jp_2952_:
{
lean_object* v___x_2956_; 
v___x_2956_ = lean_st_ref_get(v___y_2955_);
if (lean_obj_tag(v_exportedInfo_x3f_2953_) == 0)
{
lean_object* v_env_2957_; lean_object* v___x_2958_; 
v_env_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc_ref(v_env_2957_);
lean_dec(v___x_2956_);
v___x_2958_ = lean_box(0);
v___y_2922_ = v___y_2955_;
v___y_2923_ = v_env_2957_;
v___y_2924_ = v___y_2954_;
v___y_2925_ = v___y_2954_;
v___y_2926_ = v___y_2955_;
v___y_2927_ = v_exportedInfo_x3f_2953_;
v___y_2928_ = v___x_2958_;
goto v___jp_2921_;
}
else
{
lean_object* v_env_2959_; lean_object* v_val_2960_; uint8_t v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v_env_2959_ = lean_ctor_get(v___x_2956_, 0);
lean_inc_ref(v_env_2959_);
lean_dec(v___x_2956_);
v_val_2960_ = lean_ctor_get(v_exportedInfo_x3f_2953_, 0);
v___x_2961_ = l_Lean_ConstantKind_ofConstantInfo(v_val_2960_);
v___x_2962_ = lean_box(v___x_2961_);
v___x_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2962_);
v___y_2922_ = v___y_2955_;
v___y_2923_ = v_env_2959_;
v___y_2924_ = v___y_2954_;
v___y_2925_ = v___y_2954_;
v___y_2926_ = v___y_2955_;
v___y_2927_ = v_exportedInfo_x3f_2953_;
v___y_2928_ = v___x_2963_;
goto v___jp_2921_;
}
}
v___jp_2964_:
{
lean_object* v___x_2967_; 
lean_inc(v_fst_2916_);
v___x_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2967_, 0, v_fst_2916_);
v_exportedInfo_x3f_2953_ = v___x_2967_;
v___y_2954_ = v___y_2965_;
v___y_2955_ = v___y_2966_;
goto v___jp_2952_;
}
v___jp_2968_:
{
lean_object* v___x_2971_; 
lean_inc(v_fst_2916_);
v___x_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2971_, 0, v_fst_2916_);
v_exportedInfo_x3f_2953_ = v___x_2971_;
v___y_2954_ = v___y_2969_;
v___y_2955_ = v___y_2970_;
goto v___jp_2952_;
}
v___jp_2972_:
{
lean_object* v___x_2975_; lean_object* v_env_2976_; lean_object* v_nextMacroScope_2977_; lean_object* v_ngen_2978_; lean_object* v_auxDeclNGen_2979_; lean_object* v_traceState_2980_; lean_object* v_messages_2981_; lean_object* v_infoState_2982_; lean_object* v_snapshotTasks_2983_; lean_object* v_newDecls_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2994_; 
v___x_2975_ = lean_st_ref_take(v___y_2973_);
v_env_2976_ = lean_ctor_get(v___x_2975_, 0);
v_nextMacroScope_2977_ = lean_ctor_get(v___x_2975_, 1);
v_ngen_2978_ = lean_ctor_get(v___x_2975_, 2);
v_auxDeclNGen_2979_ = lean_ctor_get(v___x_2975_, 3);
v_traceState_2980_ = lean_ctor_get(v___x_2975_, 4);
v_messages_2981_ = lean_ctor_get(v___x_2975_, 6);
v_infoState_2982_ = lean_ctor_get(v___x_2975_, 7);
v_snapshotTasks_2983_ = lean_ctor_get(v___x_2975_, 8);
v_newDecls_2984_ = lean_ctor_get(v___x_2975_, 9);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_2994_ == 0)
{
lean_object* v_unused_2995_; 
v_unused_2995_ = lean_ctor_get(v___x_2975_, 5);
lean_dec(v_unused_2995_);
v___x_2986_ = v___x_2975_;
v_isShared_2987_ = v_isSharedCheck_2994_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_newDecls_2984_);
lean_inc(v_snapshotTasks_2983_);
lean_inc(v_infoState_2982_);
lean_inc(v_messages_2981_);
lean_inc(v_traceState_2980_);
lean_inc(v_auxDeclNGen_2979_);
lean_inc(v_ngen_2978_);
lean_inc(v_nextMacroScope_2977_);
lean_inc(v_env_2976_);
lean_dec(v___x_2975_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2994_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2991_; 
v___x_2988_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_2917_);
lean_inc(v_fst_2912_);
v___x_2989_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2988_, v_env_2976_, v_fst_2912_, v_snd_2917_);
if (v_isShared_2987_ == 0)
{
lean_ctor_set(v___x_2986_, 5, v___x_2803_);
lean_ctor_set(v___x_2986_, 0, v___x_2989_);
v___x_2991_ = v___x_2986_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2989_);
lean_ctor_set(v_reuseFailAlloc_2993_, 1, v_nextMacroScope_2977_);
lean_ctor_set(v_reuseFailAlloc_2993_, 2, v_ngen_2978_);
lean_ctor_set(v_reuseFailAlloc_2993_, 3, v_auxDeclNGen_2979_);
lean_ctor_set(v_reuseFailAlloc_2993_, 4, v_traceState_2980_);
lean_ctor_set(v_reuseFailAlloc_2993_, 5, v___x_2803_);
lean_ctor_set(v_reuseFailAlloc_2993_, 6, v_messages_2981_);
lean_ctor_set(v_reuseFailAlloc_2993_, 7, v_infoState_2982_);
lean_ctor_set(v_reuseFailAlloc_2993_, 8, v_snapshotTasks_2983_);
lean_ctor_set(v_reuseFailAlloc_2993_, 9, v_newDecls_2984_);
v___x_2991_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
lean_object* v___x_2992_; 
v___x_2992_ = lean_st_ref_set(v___y_2973_, v___x_2991_);
v_exportedInfo_x3f_2953_ = v_exportedInfo_x3f_2807_;
v___y_2954_ = v___y_2974_;
v___y_2955_ = v___y_2973_;
goto v___jp_2952_;
}
}
}
v___jp_2996_:
{
lean_object* v___x_2999_; uint8_t v___x_3000_; 
lean_inc(v_decl_2799_);
v___x_2999_ = l_Lean_Declaration_getTopLevelNames(v_decl_2799_);
v___x_3000_ = l_List_all___at___00Lean_addDecl_spec__2(v___x_2999_);
lean_dec(v___x_2999_);
if (v___x_3000_ == 0)
{
lean_dec(v___x_2805_);
if (lean_obj_tag(v_exportedInfo_x3f_2807_) == 0)
{
if (v___x_2802_ == 0)
{
lean_object* v_options_3001_; uint8_t v_hasTrace_3002_; 
lean_dec_ref(v___x_2803_);
v_options_3001_ = lean_ctor_get(v___y_2997_, 2);
v_hasTrace_3002_ = lean_ctor_get_uint8(v_options_3001_, sizeof(void*)*1);
if (v_hasTrace_3002_ == 0)
{
lean_dec(v_cls_2804_);
v___y_2965_ = v___y_2997_;
v___y_2966_ = v___y_2998_;
goto v___jp_2964_;
}
else
{
lean_object* v_inheritedTraceOptions_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; uint8_t v___x_3006_; 
v_inheritedTraceOptions_3003_ = lean_ctor_get(v___y_2997_, 13);
v___x_3004_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v_cls_2804_);
v___x_3005_ = l_Lean_Name_append(v___x_3004_, v_cls_2804_);
v___x_3006_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3003_, v_options_3001_, v___x_3005_);
lean_dec(v___x_3005_);
if (v___x_3006_ == 0)
{
lean_dec(v_cls_2804_);
v___y_2965_ = v___y_2997_;
v___y_2966_ = v___y_2998_;
goto v___jp_2964_;
}
else
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3007_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__1, &l_Lean_addDecl___lam__8___closed__1_once, _init_l_Lean_addDecl___lam__8___closed__1);
v___x_3008_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_2804_, v___x_3007_, v___y_2997_, v___y_2998_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_dec_ref(v___x_3008_);
v___y_2965_ = v___y_2997_;
v___y_2966_ = v___y_2998_;
goto v___jp_2964_;
}
else
{
lean_del_object(v___x_2919_);
lean_dec(v_snd_2917_);
lean_dec(v_fst_2916_);
lean_dec(v_fst_2912_);
lean_dec_ref(v___x_2800_);
lean_dec(v_decl_2799_);
return v___x_3008_;
}
}
}
}
else
{
lean_dec(v_cls_2804_);
v___y_2973_ = v___y_2998_;
v___y_2974_ = v___y_2997_;
goto v___jp_2972_;
}
}
else
{
lean_dec(v_cls_2804_);
v___y_2973_ = v___y_2998_;
v___y_2974_ = v___y_2997_;
goto v___jp_2972_;
}
}
else
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v_a_3011_; uint8_t v___x_3012_; 
lean_dec(v_exportedInfo_x3f_2807_);
lean_dec_ref(v___x_2803_);
v___x_3009_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3010_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__3___redArg(v___x_3009_, v___y_2997_);
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref(v___x_3010_);
v___x_3012_ = lean_unbox(v_a_3011_);
lean_dec(v_a_3011_);
if (v___x_3012_ == 0)
{
lean_object* v_options_3013_; uint8_t v_hasTrace_3014_; 
v_options_3013_ = lean_ctor_get(v___y_2997_, 2);
v_hasTrace_3014_ = lean_ctor_get_uint8(v_options_3013_, sizeof(void*)*1);
if (v_hasTrace_3014_ == 0)
{
lean_dec(v_cls_2804_);
v_exportedInfo_x3f_2953_ = v___x_2805_;
v___y_2954_ = v___y_2997_;
v___y_2955_ = v___y_2998_;
goto v___jp_2952_;
}
else
{
lean_object* v_inheritedTraceOptions_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; uint8_t v___x_3018_; 
v_inheritedTraceOptions_3015_ = lean_ctor_get(v___y_2997_, 13);
v___x_3016_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v_cls_2804_);
v___x_3017_ = l_Lean_Name_append(v___x_3016_, v_cls_2804_);
v___x_3018_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3015_, v_options_3013_, v___x_3017_);
lean_dec(v___x_3017_);
if (v___x_3018_ == 0)
{
lean_dec(v_cls_2804_);
v_exportedInfo_x3f_2953_ = v___x_2805_;
v___y_2954_ = v___y_2997_;
v___y_2955_ = v___y_2998_;
goto v___jp_2952_;
}
else
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3019_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__3, &l_Lean_addDecl___lam__8___closed__3_once, _init_l_Lean_addDecl___lam__8___closed__3);
v___x_3020_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_2804_, v___x_3019_, v___y_2997_, v___y_2998_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_dec_ref(v___x_3020_);
v_exportedInfo_x3f_2953_ = v___x_2805_;
v___y_2954_ = v___y_2997_;
v___y_2955_ = v___y_2998_;
goto v___jp_2952_;
}
else
{
lean_del_object(v___x_2919_);
lean_dec(v_snd_2917_);
lean_dec(v_fst_2916_);
lean_dec(v_fst_2912_);
lean_dec(v___x_2805_);
lean_dec_ref(v___x_2800_);
lean_dec(v_decl_2799_);
return v___x_3020_;
}
}
}
}
else
{
lean_object* v_options_3021_; uint8_t v_hasTrace_3022_; 
lean_dec(v___x_2805_);
v_options_3021_ = lean_ctor_get(v___y_2997_, 2);
v_hasTrace_3022_ = lean_ctor_get_uint8(v_options_3021_, sizeof(void*)*1);
if (v_hasTrace_3022_ == 0)
{
lean_dec(v_cls_2804_);
v___y_2969_ = v___y_2997_;
v___y_2970_ = v___y_2998_;
goto v___jp_2968_;
}
else
{
lean_object* v_inheritedTraceOptions_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; uint8_t v___x_3026_; 
v_inheritedTraceOptions_3023_ = lean_ctor_get(v___y_2997_, 13);
v___x_3024_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v_cls_2804_);
v___x_3025_ = l_Lean_Name_append(v___x_3024_, v_cls_2804_);
v___x_3026_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3023_, v_options_3021_, v___x_3025_);
lean_dec(v___x_3025_);
if (v___x_3026_ == 0)
{
lean_dec(v_cls_2804_);
v___y_2969_ = v___y_2997_;
v___y_2970_ = v___y_2998_;
goto v___jp_2968_;
}
else
{
lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3027_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__5, &l_Lean_addDecl___lam__8___closed__5_once, _init_l_Lean_addDecl___lam__8___closed__5);
v___x_3028_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_2804_, v___x_3027_, v___y_2997_, v___y_2998_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_dec_ref(v___x_3028_);
v___y_2969_ = v___y_2997_;
v___y_2970_ = v___y_2998_;
goto v___jp_2968_;
}
else
{
lean_del_object(v___x_2919_);
lean_dec(v_snd_2917_);
lean_dec(v_fst_2916_);
lean_dec(v_fst_2912_);
lean_dec_ref(v___x_2800_);
lean_dec(v_decl_2799_);
return v___x_3028_;
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
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__8___boxed(lean_object* v_decl_3041_, lean_object* v___x_3042_, lean_object* v_hasTrace_3043_, lean_object* v___x_3044_, lean_object* v___x_3045_, lean_object* v_cls_3046_, lean_object* v___x_3047_, lean_object* v_____x_3048_, lean_object* v_exportedInfo_x3f_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
uint8_t v_hasTrace_boxed_3053_; uint8_t v___x_61977__boxed_3054_; lean_object* v_res_3055_; 
v_hasTrace_boxed_3053_ = lean_unbox(v_hasTrace_3043_);
v___x_61977__boxed_3054_ = lean_unbox(v___x_3044_);
v_res_3055_ = l_Lean_addDecl___lam__8(v_decl_3041_, v___x_3042_, v_hasTrace_boxed_3053_, v___x_61977__boxed_3054_, v___x_3045_, v_cls_3046_, v___x_3047_, v_____x_3048_, v_exportedInfo_x3f_3049_, v___y_3050_, v___y_3051_);
lean_dec(v___y_3051_);
lean_dec_ref(v___y_3050_);
return v_res_3055_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__4___closed__1(void){
_start:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3057_ = ((lean_object*)(l_Lean_addDecl___lam__4___closed__0));
v___x_3058_ = l_Lean_stringToMessageData(v___x_3057_);
return v___x_3058_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__4___closed__3(void){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = ((lean_object*)(l_Lean_addDecl___lam__4___closed__2));
v___x_3061_ = l_Lean_stringToMessageData(v___x_3060_);
return v___x_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__4(lean_object* v___f_3062_, lean_object* v_cls_3063_, lean_object* v___x_3064_, uint8_t v___x_3065_, uint8_t v_forceExpose_3066_, lean_object* v_defn_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
lean_object* v_exportedInfo_x3f_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v_env_3110_; lean_object* v_env_3111_; 
v___x_3093_ = lean_st_ref_get(v___y_3069_);
v___x_3094_ = lean_st_ref_get(v___y_3069_);
v_env_3110_ = lean_ctor_get(v___x_3093_, 0);
lean_inc_ref(v_env_3110_);
lean_dec(v___x_3093_);
v_env_3111_ = lean_ctor_get(v___x_3094_, 0);
lean_inc_ref(v_env_3111_);
lean_dec(v___x_3094_);
if (v_forceExpose_3066_ == 0)
{
goto v___jp_3112_;
}
else
{
if (v___x_3065_ == 0)
{
lean_dec_ref(v_env_3111_);
lean_dec_ref(v_env_3110_);
lean_dec(v_cls_3063_);
v_exportedInfo_x3f_3072_ = v___x_3064_;
v___y_3073_ = v___y_3068_;
v___y_3074_ = v___y_3069_;
goto v___jp_3071_;
}
else
{
goto v___jp_3112_;
}
}
v___jp_3071_:
{
lean_object* v_toConstantVal_3075_; lean_object* v_name_3076_; lean_object* v___x_3077_; uint8_t v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v_toConstantVal_3075_ = lean_ctor_get(v_defn_3067_, 0);
v_name_3076_ = lean_ctor_get(v_toConstantVal_3075_, 0);
lean_inc(v_name_3076_);
v___x_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3077_, 0, v_defn_3067_);
v___x_3078_ = 0;
v___x_3079_ = lean_box(v___x_3078_);
v___x_3080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3077_);
lean_ctor_set(v___x_3080_, 1, v___x_3079_);
v___x_3081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3081_, 0, v_name_3076_);
lean_ctor_set(v___x_3081_, 1, v___x_3080_);
lean_inc(v___y_3074_);
lean_inc_ref(v___y_3073_);
v___x_3082_ = lean_apply_5(v___f_3062_, v___x_3081_, v_exportedInfo_x3f_3072_, v___y_3073_, v___y_3074_, lean_box(0));
return v___x_3082_;
}
v___jp_3083_:
{
lean_object* v_toConstantVal_3086_; uint8_t v_safety_3087_; uint8_t v___x_3088_; uint8_t v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v_toConstantVal_3086_ = lean_ctor_get(v_defn_3067_, 0);
v_safety_3087_ = lean_ctor_get_uint8(v_defn_3067_, sizeof(void*)*4);
v___x_3088_ = 0;
v___x_3089_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3087_, v___x_3088_);
lean_inc_ref(v_toConstantVal_3086_);
v___x_3090_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3090_, 0, v_toConstantVal_3086_);
lean_ctor_set_uint8(v___x_3090_, sizeof(void*)*1, v___x_3089_);
v___x_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
v___x_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3091_);
v_exportedInfo_x3f_3072_ = v___x_3092_;
v___y_3073_ = v___y_3084_;
v___y_3074_ = v___y_3085_;
goto v___jp_3071_;
}
v___jp_3095_:
{
lean_object* v_options_3096_; uint8_t v_hasTrace_3097_; 
v_options_3096_ = lean_ctor_get(v___y_3068_, 2);
v_hasTrace_3097_ = lean_ctor_get_uint8(v_options_3096_, sizeof(void*)*1);
if (v_hasTrace_3097_ == 0)
{
lean_dec(v_cls_3063_);
v___y_3084_ = v___y_3068_;
v___y_3085_ = v___y_3069_;
goto v___jp_3083_;
}
else
{
lean_object* v_inheritedTraceOptions_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; uint8_t v___x_3101_; 
v_inheritedTraceOptions_3098_ = lean_ctor_get(v___y_3068_, 13);
v___x_3099_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v_cls_3063_);
v___x_3100_ = l_Lean_Name_append(v___x_3099_, v_cls_3063_);
v___x_3101_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3098_, v_options_3096_, v___x_3100_);
lean_dec(v___x_3100_);
if (v___x_3101_ == 0)
{
lean_dec(v_cls_3063_);
v___y_3084_ = v___y_3068_;
v___y_3085_ = v___y_3069_;
goto v___jp_3083_;
}
else
{
lean_object* v_toConstantVal_3102_; lean_object* v_name_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v_toConstantVal_3102_ = lean_ctor_get(v_defn_3067_, 0);
v_name_3103_ = lean_ctor_get(v_toConstantVal_3102_, 0);
v___x_3104_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__1, &l_Lean_addDecl___lam__4___closed__1_once, _init_l_Lean_addDecl___lam__4___closed__1);
lean_inc(v_name_3103_);
v___x_3105_ = l_Lean_MessageData_ofName(v_name_3103_);
v___x_3106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3104_);
lean_ctor_set(v___x_3106_, 1, v___x_3105_);
v___x_3107_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_3108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3106_);
lean_ctor_set(v___x_3108_, 1, v___x_3107_);
v___x_3109_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3063_, v___x_3108_, v___y_3068_, v___y_3069_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_dec_ref(v___x_3109_);
v___y_3084_ = v___y_3068_;
v___y_3085_ = v___y_3069_;
goto v___jp_3083_;
}
else
{
lean_dec_ref(v_defn_3067_);
lean_dec_ref(v___f_3062_);
return v___x_3109_;
}
}
}
}
v___jp_3112_:
{
lean_object* v___x_3113_; uint8_t v_isModule_3114_; 
v___x_3113_ = l_Lean_Environment_header(v_env_3110_);
lean_dec_ref(v_env_3110_);
v_isModule_3114_ = lean_ctor_get_uint8(v___x_3113_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3113_);
if (v_isModule_3114_ == 0)
{
lean_dec_ref(v_env_3111_);
lean_dec(v_cls_3063_);
v_exportedInfo_x3f_3072_ = v___x_3064_;
v___y_3073_ = v___y_3068_;
v___y_3074_ = v___y_3069_;
goto v___jp_3071_;
}
else
{
uint8_t v_isExporting_3115_; 
v_isExporting_3115_ = lean_ctor_get_uint8(v_env_3111_, sizeof(void*)*8);
lean_dec_ref(v_env_3111_);
if (v_isExporting_3115_ == 0)
{
lean_dec(v___x_3064_);
goto v___jp_3095_;
}
else
{
if (v___x_3065_ == 0)
{
lean_dec(v_cls_3063_);
v_exportedInfo_x3f_3072_ = v___x_3064_;
v___y_3073_ = v___y_3068_;
v___y_3074_ = v___y_3069_;
goto v___jp_3071_;
}
else
{
lean_dec(v___x_3064_);
goto v___jp_3095_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__4___boxed(lean_object* v___f_3116_, lean_object* v_cls_3117_, lean_object* v___x_3118_, lean_object* v___x_3119_, lean_object* v_forceExpose_3120_, lean_object* v_defn_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_){
_start:
{
uint8_t v___x_62451__boxed_3125_; uint8_t v_forceExpose_boxed_3126_; lean_object* v_res_3127_; 
v___x_62451__boxed_3125_ = lean_unbox(v___x_3119_);
v_forceExpose_boxed_3126_ = lean_unbox(v_forceExpose_3120_);
v_res_3127_ = l_Lean_addDecl___lam__4(v___f_3116_, v_cls_3117_, v___x_3118_, v___x_62451__boxed_3125_, v_forceExpose_boxed_3126_, v_defn_3121_, v___y_3122_, v___y_3123_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__5(lean_object* v_val_3128_, lean_object* v___f_3129_, lean_object* v_____r_3130_, lean_object* v_exportedInfo_x3f_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
lean_object* v_toConstantVal_3135_; lean_object* v_name_3136_; lean_object* v___x_3137_; uint8_t v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v_toConstantVal_3135_ = lean_ctor_get(v_val_3128_, 0);
v_name_3136_ = lean_ctor_get(v_toConstantVal_3135_, 0);
lean_inc(v_name_3136_);
v___x_3137_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3137_, 0, v_val_3128_);
v___x_3138_ = 1;
v___x_3139_ = lean_box(v___x_3138_);
v___x_3140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3137_);
lean_ctor_set(v___x_3140_, 1, v___x_3139_);
v___x_3141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3141_, 0, v_name_3136_);
lean_ctor_set(v___x_3141_, 1, v___x_3140_);
lean_inc(v___y_3133_);
lean_inc_ref(v___y_3132_);
v___x_3142_ = lean_apply_5(v___f_3129_, v___x_3141_, v_exportedInfo_x3f_3131_, v___y_3132_, v___y_3133_, lean_box(0));
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__5___boxed(lean_object* v_val_3143_, lean_object* v___f_3144_, lean_object* v_____r_3145_, lean_object* v_exportedInfo_x3f_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l_Lean_addDecl___lam__5(v_val_3143_, v___f_3144_, v_____r_3145_, v_exportedInfo_x3f_3146_, v___y_3147_, v___y_3148_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__6(lean_object* v_val_3151_, uint8_t v___x_3152_, lean_object* v___f_3153_, lean_object* v_____r_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_){
_start:
{
lean_object* v_toConstantVal_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v_toConstantVal_3158_ = lean_ctor_get(v_val_3151_, 0);
lean_inc_ref(v_toConstantVal_3158_);
v___x_3159_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3159_, 0, v_toConstantVal_3158_);
lean_ctor_set_uint8(v___x_3159_, sizeof(void*)*1, v___x_3152_);
v___x_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3159_);
v___x_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
v___x_3162_ = lean_box(0);
lean_inc(v___y_3156_);
lean_inc_ref(v___y_3155_);
v___x_3163_ = lean_apply_5(v___f_3153_, v___x_3162_, v___x_3161_, v___y_3155_, v___y_3156_, lean_box(0));
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__6___boxed(lean_object* v_val_3164_, lean_object* v___x_3165_, lean_object* v___f_3166_, lean_object* v_____r_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
uint8_t v___x_62570__boxed_3171_; lean_object* v_res_3172_; 
v___x_62570__boxed_3171_ = lean_unbox(v___x_3165_);
v_res_3172_ = l_Lean_addDecl___lam__6(v_val_3164_, v___x_62570__boxed_3171_, v___f_3166_, v_____r_3167_, v___y_3168_, v___y_3169_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec_ref(v_val_3164_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__7(lean_object* v_val_3173_, lean_object* v___f_3174_, lean_object* v_____r_3175_, lean_object* v_exportedInfo_x3f_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_){
_start:
{
lean_object* v_toConstantVal_3180_; lean_object* v_name_3181_; lean_object* v___x_3182_; uint8_t v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v_toConstantVal_3180_ = lean_ctor_get(v_val_3173_, 0);
v_name_3181_ = lean_ctor_get(v_toConstantVal_3180_, 0);
lean_inc(v_name_3181_);
v___x_3182_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3182_, 0, v_val_3173_);
v___x_3183_ = 3;
v___x_3184_ = lean_box(v___x_3183_);
v___x_3185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3182_);
lean_ctor_set(v___x_3185_, 1, v___x_3184_);
v___x_3186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3186_, 0, v_name_3181_);
lean_ctor_set(v___x_3186_, 1, v___x_3185_);
lean_inc(v___y_3178_);
lean_inc_ref(v___y_3177_);
v___x_3187_ = lean_apply_5(v___f_3174_, v___x_3186_, v_exportedInfo_x3f_3176_, v___y_3177_, v___y_3178_, lean_box(0));
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__7___boxed(lean_object* v_val_3188_, lean_object* v___f_3189_, lean_object* v_____r_3190_, lean_object* v_exportedInfo_x3f_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
lean_object* v_res_3195_; 
v_res_3195_ = l_Lean_addDecl___lam__7(v_val_3188_, v___f_3189_, v_____r_3190_, v_exportedInfo_x3f_3191_, v___y_3192_, v___y_3193_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__9(lean_object* v_val_3196_, lean_object* v___f_3197_, lean_object* v_____r_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_){
_start:
{
lean_object* v_toConstantVal_3202_; uint8_t v_isUnsafe_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v_toConstantVal_3202_ = lean_ctor_get(v_val_3196_, 0);
v_isUnsafe_3203_ = lean_ctor_get_uint8(v_val_3196_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_3202_);
v___x_3204_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3204_, 0, v_toConstantVal_3202_);
lean_ctor_set_uint8(v___x_3204_, sizeof(void*)*1, v_isUnsafe_3203_);
v___x_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3204_);
v___x_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3205_);
v___x_3207_ = lean_box(0);
lean_inc(v___y_3200_);
lean_inc_ref(v___y_3199_);
v___x_3208_ = lean_apply_5(v___f_3197_, v___x_3207_, v___x_3206_, v___y_3199_, v___y_3200_, lean_box(0));
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__9___boxed(lean_object* v_val_3209_, lean_object* v___f_3210_, lean_object* v_____r_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l_Lean_addDecl___lam__9(v_val_3209_, v___f_3210_, v_____r_3211_, v___y_3212_, v___y_3213_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec_ref(v_val_3209_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__13(lean_object* v_decl_3216_, lean_object* v___x_3217_, uint8_t v___x_3218_, lean_object* v_cls_3219_, lean_object* v___x_3220_, lean_object* v___x_3221_, lean_object* v_____x_3222_, lean_object* v_exportedInfo_x3f_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v_a_3230_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v_a_3243_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; uint8_t v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v_snd_3328_; lean_object* v_fst_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3459_; 
v_snd_3328_ = lean_ctor_get(v_____x_3222_, 1);
v_fst_3329_ = lean_ctor_get(v_____x_3222_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v_____x_3222_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3331_ = v_____x_3222_;
v_isShared_3332_ = v_isSharedCheck_3459_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_snd_3328_);
lean_inc(v_fst_3329_);
lean_dec(v_____x_3222_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3459_;
goto v_resetjp_3330_;
}
v___jp_3227_:
{
lean_object* v___x_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3238_; 
v___x_3231_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3229_, v___y_3228_);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3238_ == 0)
{
lean_object* v_unused_3239_; 
v_unused_3239_ = lean_ctor_get(v___x_3231_, 0);
lean_dec(v_unused_3239_);
v___x_3233_ = v___x_3231_;
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
else
{
lean_dec(v___x_3231_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3236_; 
if (v_isShared_3234_ == 0)
{
lean_ctor_set_tag(v___x_3233_, 1);
lean_ctor_set(v___x_3233_, 0, v_a_3230_);
v___x_3236_ = v___x_3233_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_a_3230_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
v___jp_3240_:
{
lean_object* v___x_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3251_; 
v___x_3244_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3242_, v___y_3241_);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3251_ == 0)
{
lean_object* v_unused_3252_; 
v_unused_3252_ = lean_ctor_get(v___x_3244_, 0);
lean_dec(v_unused_3252_);
v___x_3246_ = v___x_3244_;
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
else
{
lean_dec(v___x_3244_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3249_; 
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 0, v_a_3243_);
v___x_3249_ = v___x_3246_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_a_3243_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
}
v___jp_3253_:
{
lean_object* v___x_3265_; 
lean_inc_ref(v___y_3258_);
v___x_3265_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3256_, v___y_3258_, v___y_3257_, v___y_3264_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v___x_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3313_; 
lean_dec_ref(v___x_3265_);
lean_inc_ref(v___y_3263_);
v___x_3266_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3263_, v___y_3255_);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3313_ == 0)
{
lean_object* v_unused_3314_; 
v_unused_3314_ = lean_ctor_get(v___x_3266_, 0);
lean_dec(v_unused_3314_);
v___x_3268_ = v___x_3266_;
v_isShared_3269_ = v_isSharedCheck_3313_;
goto v_resetjp_3267_;
}
else
{
lean_dec(v___x_3266_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3313_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v_options_3270_; lean_object* v___x_3271_; uint8_t v___x_3272_; 
v_options_3270_ = lean_ctor_get(v___y_3254_, 2);
v___x_3271_ = l_Lean_Elab_async;
v___x_3272_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3270_, v___x_3271_);
if (v___x_3272_ == 0)
{
lean_object* v___x_3273_; lean_object* v_r_3274_; 
lean_del_object(v___x_3268_);
lean_dec_ref(v___y_3262_);
lean_dec_ref(v___y_3259_);
lean_dec_ref(v___x_3217_);
v___x_3273_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3258_, v___y_3255_);
lean_dec_ref(v___x_3273_);
v_r_3274_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3216_, v___y_3254_, v___y_3255_);
if (lean_obj_tag(v_r_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3284_; 
v_a_3275_ = lean_ctor_get(v_r_3274_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v_r_3274_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3277_ = v_r_3274_;
v_isShared_3278_ = v_isSharedCheck_3284_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v_r_3274_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3284_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3280_; 
lean_inc(v_a_3275_);
if (v_isShared_3278_ == 0)
{
lean_ctor_set_tag(v___x_3277_, 1);
v___x_3280_ = v___x_3277_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_a_3275_);
v___x_3280_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
lean_object* v___x_3281_; 
v___x_3281_ = lean_apply_2(v___y_3261_, v___x_3280_, lean_box(0));
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_dec_ref(v___x_3281_);
v___y_3241_ = v___y_3255_;
v___y_3242_ = v___y_3263_;
v_a_3243_ = v_a_3275_;
goto v___jp_3240_;
}
else
{
lean_object* v_a_3282_; 
lean_dec(v_a_3275_);
v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
lean_inc(v_a_3282_);
lean_dec_ref(v___x_3281_);
v___y_3228_ = v___y_3255_;
v___y_3229_ = v___y_3263_;
v_a_3230_ = v_a_3282_;
goto v___jp_3227_;
}
}
}
}
else
{
lean_object* v_a_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v_a_3285_ = lean_ctor_get(v_r_3274_, 0);
lean_inc(v_a_3285_);
lean_dec_ref(v_r_3274_);
v___x_3286_ = lean_box(0);
v___x_3287_ = lean_apply_2(v___y_3261_, v___x_3286_, lean_box(0));
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_dec_ref(v___x_3287_);
v___y_3228_ = v___y_3255_;
v___y_3229_ = v___y_3263_;
v_a_3230_ = v_a_3285_;
goto v___jp_3227_;
}
else
{
lean_object* v_a_3288_; 
lean_dec(v_a_3285_);
v_a_3288_ = lean_ctor_get(v___x_3287_, 0);
lean_inc(v_a_3288_);
lean_dec_ref(v___x_3287_);
v___y_3228_ = v___y_3255_;
v___y_3229_ = v___y_3263_;
v_a_3230_ = v_a_3288_;
goto v___jp_3227_;
}
}
}
else
{
lean_object* v___x_3289_; lean_object* v___x_3291_; 
lean_dec_ref(v___y_3263_);
lean_dec_ref(v___y_3261_);
lean_dec_ref(v___y_3258_);
lean_dec(v_decl_3216_);
v___x_3289_ = l_IO_CancelToken_new();
if (v_isShared_3269_ == 0)
{
lean_ctor_set_tag(v___x_3268_, 1);
lean_ctor_set(v___x_3268_, 0, v___x_3289_);
v___x_3291_ = v___x_3268_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3289_);
v___x_3291_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3292_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__5_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_3293_ = l_Lean_Name_mkStr2(v___x_3292_, v___x_3217_);
v___x_3294_ = l_Lean_Name_toString(v___x_3293_, v___x_3218_);
lean_inc_ref(v___x_3291_);
v___x_3295_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3259_, v___x_3291_, v___x_3294_, v___y_3254_, v___y_3255_);
if (lean_obj_tag(v___x_3295_) == 0)
{
lean_object* v_a_3296_; lean_object* v_checked_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v_a_3296_ = lean_ctor_get(v___x_3295_, 0);
lean_inc(v_a_3296_);
lean_dec_ref(v___x_3295_);
v_checked_3297_ = lean_ctor_get(v___y_3262_, 2);
lean_inc_ref(v_checked_3297_);
lean_dec_ref(v___y_3262_);
v___x_3298_ = lean_unsigned_to_nat(0u);
v___x_3299_ = lean_io_map_task(v_a_3296_, v_checked_3297_, v___x_3298_, v___y_3260_);
v___x_3300_ = lean_box(0);
v___x_3301_ = lean_box(2);
v___x_3302_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3300_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
lean_ctor_set(v___x_3302_, 2, v___x_3291_);
lean_ctor_set(v___x_3302_, 3, v___x_3299_);
v___x_3303_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3302_, v___y_3255_);
return v___x_3303_;
}
else
{
lean_object* v_a_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3311_; 
lean_dec_ref(v___x_3291_);
lean_dec_ref(v___y_3262_);
v_a_3304_ = lean_ctor_get(v___x_3295_, 0);
v_isSharedCheck_3311_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3306_ = v___x_3295_;
v_isShared_3307_ = v_isSharedCheck_3311_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_a_3304_);
lean_dec(v___x_3295_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3311_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v___x_3309_; 
if (v_isShared_3307_ == 0)
{
v___x_3309_ = v___x_3306_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_a_3304_);
v___x_3309_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
return v___x_3309_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3327_; 
lean_dec_ref(v___y_3263_);
lean_dec_ref(v___y_3262_);
lean_dec_ref(v___y_3261_);
lean_dec_ref(v___y_3259_);
lean_dec_ref(v___y_3258_);
lean_dec_ref(v___x_3217_);
lean_dec(v_decl_3216_);
v_a_3315_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3317_ = v___x_3265_;
v_isShared_3318_ = v_isSharedCheck_3327_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_a_3315_);
lean_dec(v___x_3265_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3327_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
lean_object* v_ref_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3325_; 
v_ref_3319_ = lean_ctor_get(v___y_3254_, 5);
v___x_3320_ = lean_io_error_to_string(v_a_3315_);
v___x_3321_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3320_);
v___x_3322_ = l_Lean_MessageData_ofFormat(v___x_3321_);
lean_inc(v_ref_3319_);
v___x_3323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3323_, 0, v_ref_3319_);
lean_ctor_set(v___x_3323_, 1, v___x_3322_);
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 0, v___x_3323_);
v___x_3325_ = v___x_3317_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v___x_3323_);
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
v_resetjp_3330_:
{
lean_object* v_fst_3333_; lean_object* v_snd_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3458_; 
v_fst_3333_ = lean_ctor_get(v_snd_3328_, 0);
v_snd_3334_ = lean_ctor_get(v_snd_3328_, 1);
v_isSharedCheck_3458_ = !lean_is_exclusive(v_snd_3328_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3336_ = v_snd_3328_;
v_isShared_3337_ = v_isSharedCheck_3458_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_snd_3334_);
lean_inc(v_fst_3333_);
lean_dec(v_snd_3328_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3458_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v_exportedInfo_x3f_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3391_; lean_object* v___y_3392_; uint8_t v___y_3393_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___x_3448_; lean_object* v_env_3449_; uint8_t v___x_3450_; 
v___x_3448_ = lean_st_ref_get(v___y_3225_);
v_env_3449_ = lean_ctor_get(v___x_3448_, 0);
lean_inc_ref(v_env_3449_);
lean_dec(v___x_3448_);
v___x_3450_ = l_Lean_Environment_containsOnBranch(v_env_3449_, v_fst_3329_);
lean_dec_ref(v_env_3449_);
if (v___x_3450_ == 0)
{
lean_del_object(v___x_3331_);
v___y_3424_ = v___y_3224_;
v___y_3425_ = v___y_3225_;
goto v___jp_3423_;
}
else
{
lean_object* v___x_3451_; lean_object* v_env_3452_; lean_object* v___x_3453_; lean_object* v___x_3455_; 
lean_del_object(v___x_3336_);
lean_dec(v_snd_3334_);
lean_dec(v_fst_3333_);
lean_dec(v_exportedInfo_x3f_3223_);
lean_dec(v___x_3221_);
lean_dec_ref(v___x_3220_);
lean_dec(v_cls_3219_);
lean_dec_ref(v___x_3217_);
lean_dec(v_decl_3216_);
v___x_3451_ = lean_st_ref_get(v___y_3225_);
v_env_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc_ref(v_env_3452_);
lean_dec(v___x_3451_);
v___x_3453_ = lean_elab_environment_to_kernel_env(v_env_3452_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set_tag(v___x_3331_, 1);
lean_ctor_set(v___x_3331_, 1, v_fst_3329_);
lean_ctor_set(v___x_3331_, 0, v___x_3453_);
v___x_3455_ = v___x_3331_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v___x_3453_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v_fst_3329_);
v___x_3455_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
lean_object* v___x_3456_; 
v___x_3456_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(v___x_3455_, v___y_3224_, v___y_3225_);
return v___x_3456_;
}
}
v___jp_3338_:
{
uint8_t v___x_3346_; uint8_t v___x_3347_; lean_object* v___x_3348_; 
v___x_3346_ = 0;
v___x_3347_ = lean_unbox(v_snd_3334_);
lean_dec(v_snd_3334_);
lean_inc_ref(v___y_3340_);
v___x_3348_ = l_Lean_Environment_addConstAsync(v___y_3340_, v_fst_3329_, v___x_3347_, v___y_3345_, v___x_3346_, v___x_3218_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v_a_3349_; lean_object* v_mainEnv_3350_; lean_object* v_asyncEnv_3351_; lean_object* v___f_3352_; lean_object* v___f_3353_; lean_object* v___x_3354_; 
lean_del_object(v___x_3336_);
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
lean_inc_n(v_a_3349_, 3);
lean_dec_ref(v___x_3348_);
v_mainEnv_3350_ = lean_ctor_get(v_a_3349_, 0);
lean_inc_ref(v_mainEnv_3350_);
v_asyncEnv_3351_ = lean_ctor_get(v_a_3349_, 1);
lean_inc_ref_n(v_asyncEnv_3351_, 2);
lean_inc_ref(v___y_3341_);
lean_inc(v___y_3339_);
v___f_3352_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3352_, 0, v___y_3339_);
lean_closure_set(v___f_3352_, 1, v_a_3349_);
lean_closure_set(v___f_3352_, 2, v___y_3341_);
lean_inc(v_decl_3216_);
v___f_3353_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3353_, 0, v_asyncEnv_3351_);
lean_closure_set(v___f_3353_, 1, v_a_3349_);
lean_closure_set(v___f_3353_, 2, v_decl_3216_);
v___x_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3354_, 0, v_fst_3333_);
if (lean_obj_tag(v___y_3344_) == 0)
{
lean_inc_ref(v___x_3354_);
v___y_3254_ = v___y_3343_;
v___y_3255_ = v___y_3342_;
v___y_3256_ = v_a_3349_;
v___y_3257_ = v___x_3354_;
v___y_3258_ = v_asyncEnv_3351_;
v___y_3259_ = v___f_3353_;
v___y_3260_ = v___x_3346_;
v___y_3261_ = v___f_3352_;
v___y_3262_ = v___y_3340_;
v___y_3263_ = v_mainEnv_3350_;
v___y_3264_ = v___x_3354_;
goto v___jp_3253_;
}
else
{
v___y_3254_ = v___y_3343_;
v___y_3255_ = v___y_3342_;
v___y_3256_ = v_a_3349_;
v___y_3257_ = v___x_3354_;
v___y_3258_ = v_asyncEnv_3351_;
v___y_3259_ = v___f_3353_;
v___y_3260_ = v___x_3346_;
v___y_3261_ = v___f_3352_;
v___y_3262_ = v___y_3340_;
v___y_3263_ = v_mainEnv_3350_;
v___y_3264_ = v___y_3344_;
goto v___jp_3253_;
}
}
else
{
lean_object* v_a_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3369_; 
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3340_);
lean_dec(v_fst_3333_);
lean_dec_ref(v___x_3217_);
lean_dec(v_decl_3216_);
v_a_3355_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3357_ = v___x_3348_;
v_isShared_3358_ = v_isSharedCheck_3369_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_a_3355_);
lean_dec(v___x_3348_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3369_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v_ref_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3364_; 
v_ref_3359_ = lean_ctor_get(v___y_3343_, 5);
v___x_3360_ = lean_io_error_to_string(v_a_3355_);
v___x_3361_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3360_);
v___x_3362_ = l_Lean_MessageData_ofFormat(v___x_3361_);
lean_inc(v_ref_3359_);
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 1, v___x_3362_);
lean_ctor_set(v___x_3336_, 0, v_ref_3359_);
v___x_3364_ = v___x_3336_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_ref_3359_);
lean_ctor_set(v_reuseFailAlloc_3368_, 1, v___x_3362_);
v___x_3364_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
lean_object* v___x_3366_; 
if (v_isShared_3358_ == 0)
{
lean_ctor_set(v___x_3357_, 0, v___x_3364_);
v___x_3366_ = v___x_3357_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v___x_3364_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
}
}
v___jp_3370_:
{
lean_object* v___x_3374_; 
v___x_3374_ = lean_st_ref_get(v___y_3373_);
if (lean_obj_tag(v_exportedInfo_x3f_3371_) == 0)
{
lean_object* v_env_3375_; lean_object* v___x_3376_; 
v_env_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc_ref(v_env_3375_);
lean_dec(v___x_3374_);
v___x_3376_ = lean_box(0);
v___y_3339_ = v___y_3373_;
v___y_3340_ = v_env_3375_;
v___y_3341_ = v___y_3372_;
v___y_3342_ = v___y_3373_;
v___y_3343_ = v___y_3372_;
v___y_3344_ = v_exportedInfo_x3f_3371_;
v___y_3345_ = v___x_3376_;
goto v___jp_3338_;
}
else
{
lean_object* v_env_3377_; lean_object* v_val_3378_; uint8_t v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
v_env_3377_ = lean_ctor_get(v___x_3374_, 0);
lean_inc_ref(v_env_3377_);
lean_dec(v___x_3374_);
v_val_3378_ = lean_ctor_get(v_exportedInfo_x3f_3371_, 0);
v___x_3379_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3378_);
v___x_3380_ = lean_box(v___x_3379_);
v___x_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3380_);
v___y_3339_ = v___y_3373_;
v___y_3340_ = v_env_3377_;
v___y_3341_ = v___y_3372_;
v___y_3342_ = v___y_3373_;
v___y_3343_ = v___y_3372_;
v___y_3344_ = v_exportedInfo_x3f_3371_;
v___y_3345_ = v___x_3381_;
goto v___jp_3338_;
}
}
v___jp_3382_:
{
lean_object* v___x_3385_; 
lean_inc(v_fst_3333_);
v___x_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3385_, 0, v_fst_3333_);
v_exportedInfo_x3f_3371_ = v___x_3385_;
v___y_3372_ = v___y_3383_;
v___y_3373_ = v___y_3384_;
goto v___jp_3370_;
}
v___jp_3386_:
{
lean_object* v___x_3389_; 
lean_inc(v_fst_3333_);
v___x_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3389_, 0, v_fst_3333_);
v_exportedInfo_x3f_3371_ = v___x_3389_;
v___y_3372_ = v___y_3387_;
v___y_3373_ = v___y_3388_;
goto v___jp_3370_;
}
v___jp_3390_:
{
if (v___y_3393_ == 0)
{
lean_object* v_options_3394_; uint8_t v_hasTrace_3395_; 
lean_dec(v_exportedInfo_x3f_3223_);
lean_dec_ref(v___x_3220_);
v_options_3394_ = lean_ctor_get(v___y_3391_, 2);
v_hasTrace_3395_ = lean_ctor_get_uint8(v_options_3394_, sizeof(void*)*1);
if (v_hasTrace_3395_ == 0)
{
lean_dec(v_cls_3219_);
v___y_3383_ = v___y_3391_;
v___y_3384_ = v___y_3392_;
goto v___jp_3382_;
}
else
{
lean_object* v_inheritedTraceOptions_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; uint8_t v___x_3399_; 
v_inheritedTraceOptions_3396_ = lean_ctor_get(v___y_3391_, 13);
v___x_3397_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v_cls_3219_);
v___x_3398_ = l_Lean_Name_append(v___x_3397_, v_cls_3219_);
v___x_3399_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3396_, v_options_3394_, v___x_3398_);
lean_dec(v___x_3398_);
if (v___x_3399_ == 0)
{
lean_dec(v_cls_3219_);
v___y_3383_ = v___y_3391_;
v___y_3384_ = v___y_3392_;
goto v___jp_3382_;
}
else
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3400_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__1, &l_Lean_addDecl___lam__8___closed__1_once, _init_l_Lean_addDecl___lam__8___closed__1);
v___x_3401_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3219_, v___x_3400_, v___y_3391_, v___y_3392_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_dec_ref(v___x_3401_);
v___y_3383_ = v___y_3391_;
v___y_3384_ = v___y_3392_;
goto v___jp_3382_;
}
else
{
lean_del_object(v___x_3336_);
lean_dec(v_snd_3334_);
lean_dec(v_fst_3333_);
lean_dec(v_fst_3329_);
lean_dec_ref(v___x_3217_);
lean_dec(v_decl_3216_);
return v___x_3401_;
}
}
}
}
else
{
lean_object* v___x_3402_; lean_object* v_env_3403_; lean_object* v_nextMacroScope_3404_; lean_object* v_ngen_3405_; lean_object* v_auxDeclNGen_3406_; lean_object* v_traceState_3407_; lean_object* v_messages_3408_; lean_object* v_infoState_3409_; lean_object* v_snapshotTasks_3410_; lean_object* v_newDecls_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3421_; 
lean_dec(v_cls_3219_);
v___x_3402_ = lean_st_ref_take(v___y_3392_);
v_env_3403_ = lean_ctor_get(v___x_3402_, 0);
v_nextMacroScope_3404_ = lean_ctor_get(v___x_3402_, 1);
v_ngen_3405_ = lean_ctor_get(v___x_3402_, 2);
v_auxDeclNGen_3406_ = lean_ctor_get(v___x_3402_, 3);
v_traceState_3407_ = lean_ctor_get(v___x_3402_, 4);
v_messages_3408_ = lean_ctor_get(v___x_3402_, 6);
v_infoState_3409_ = lean_ctor_get(v___x_3402_, 7);
v_snapshotTasks_3410_ = lean_ctor_get(v___x_3402_, 8);
v_newDecls_3411_ = lean_ctor_get(v___x_3402_, 9);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3421_ == 0)
{
lean_object* v_unused_3422_; 
v_unused_3422_ = lean_ctor_get(v___x_3402_, 5);
lean_dec(v_unused_3422_);
v___x_3413_ = v___x_3402_;
v_isShared_3414_ = v_isSharedCheck_3421_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_newDecls_3411_);
lean_inc(v_snapshotTasks_3410_);
lean_inc(v_infoState_3409_);
lean_inc(v_messages_3408_);
lean_inc(v_traceState_3407_);
lean_inc(v_auxDeclNGen_3406_);
lean_inc(v_ngen_3405_);
lean_inc(v_nextMacroScope_3404_);
lean_inc(v_env_3403_);
lean_dec(v___x_3402_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3421_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3418_; 
v___x_3415_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3334_);
lean_inc(v_fst_3329_);
v___x_3416_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3415_, v_env_3403_, v_fst_3329_, v_snd_3334_);
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 5, v___x_3220_);
lean_ctor_set(v___x_3413_, 0, v___x_3416_);
v___x_3418_ = v___x_3413_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3416_);
lean_ctor_set(v_reuseFailAlloc_3420_, 1, v_nextMacroScope_3404_);
lean_ctor_set(v_reuseFailAlloc_3420_, 2, v_ngen_3405_);
lean_ctor_set(v_reuseFailAlloc_3420_, 3, v_auxDeclNGen_3406_);
lean_ctor_set(v_reuseFailAlloc_3420_, 4, v_traceState_3407_);
lean_ctor_set(v_reuseFailAlloc_3420_, 5, v___x_3220_);
lean_ctor_set(v_reuseFailAlloc_3420_, 6, v_messages_3408_);
lean_ctor_set(v_reuseFailAlloc_3420_, 7, v_infoState_3409_);
lean_ctor_set(v_reuseFailAlloc_3420_, 8, v_snapshotTasks_3410_);
lean_ctor_set(v_reuseFailAlloc_3420_, 9, v_newDecls_3411_);
v___x_3418_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
lean_object* v___x_3419_; 
v___x_3419_ = lean_st_ref_set(v___y_3392_, v___x_3418_);
v_exportedInfo_x3f_3371_ = v_exportedInfo_x3f_3223_;
v___y_3372_ = v___y_3391_;
v___y_3373_ = v___y_3392_;
goto v___jp_3370_;
}
}
}
}
v___jp_3423_:
{
lean_object* v___x_3426_; uint8_t v___x_3427_; 
lean_inc(v_decl_3216_);
v___x_3426_ = l_Lean_Declaration_getTopLevelNames(v_decl_3216_);
v___x_3427_ = l_List_all___at___00Lean_addDecl_spec__2(v___x_3426_);
lean_dec(v___x_3426_);
if (v___x_3427_ == 0)
{
lean_dec(v___x_3221_);
if (lean_obj_tag(v_exportedInfo_x3f_3223_) == 0)
{
v___y_3391_ = v___y_3424_;
v___y_3392_ = v___y_3425_;
v___y_3393_ = v___x_3427_;
goto v___jp_3390_;
}
else
{
v___y_3391_ = v___y_3424_;
v___y_3392_ = v___y_3425_;
v___y_3393_ = v___x_3218_;
goto v___jp_3390_;
}
}
else
{
lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v_a_3430_; uint8_t v___x_3431_; 
lean_dec(v_exportedInfo_x3f_3223_);
lean_dec_ref(v___x_3220_);
v___x_3428_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3429_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__3___redArg(v___x_3428_, v___y_3424_);
v_a_3430_ = lean_ctor_get(v___x_3429_, 0);
lean_inc(v_a_3430_);
lean_dec_ref(v___x_3429_);
v___x_3431_ = lean_unbox(v_a_3430_);
lean_dec(v_a_3430_);
if (v___x_3431_ == 0)
{
lean_object* v_options_3432_; uint8_t v_hasTrace_3433_; 
v_options_3432_ = lean_ctor_get(v___y_3424_, 2);
v_hasTrace_3433_ = lean_ctor_get_uint8(v_options_3432_, sizeof(void*)*1);
if (v_hasTrace_3433_ == 0)
{
lean_dec(v_cls_3219_);
v_exportedInfo_x3f_3371_ = v___x_3221_;
v___y_3372_ = v___y_3424_;
v___y_3373_ = v___y_3425_;
goto v___jp_3370_;
}
else
{
lean_object* v_inheritedTraceOptions_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; uint8_t v___x_3437_; 
v_inheritedTraceOptions_3434_ = lean_ctor_get(v___y_3424_, 13);
v___x_3435_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v_cls_3219_);
v___x_3436_ = l_Lean_Name_append(v___x_3435_, v_cls_3219_);
v___x_3437_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3434_, v_options_3432_, v___x_3436_);
lean_dec(v___x_3436_);
if (v___x_3437_ == 0)
{
lean_dec(v_cls_3219_);
v_exportedInfo_x3f_3371_ = v___x_3221_;
v___y_3372_ = v___y_3424_;
v___y_3373_ = v___y_3425_;
goto v___jp_3370_;
}
else
{
lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3438_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__3, &l_Lean_addDecl___lam__8___closed__3_once, _init_l_Lean_addDecl___lam__8___closed__3);
v___x_3439_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3219_, v___x_3438_, v___y_3424_, v___y_3425_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_dec_ref(v___x_3439_);
v_exportedInfo_x3f_3371_ = v___x_3221_;
v___y_3372_ = v___y_3424_;
v___y_3373_ = v___y_3425_;
goto v___jp_3370_;
}
else
{
lean_del_object(v___x_3336_);
lean_dec(v_snd_3334_);
lean_dec(v_fst_3333_);
lean_dec(v_fst_3329_);
lean_dec(v___x_3221_);
lean_dec_ref(v___x_3217_);
lean_dec(v_decl_3216_);
return v___x_3439_;
}
}
}
}
else
{
lean_object* v_options_3440_; uint8_t v_hasTrace_3441_; 
lean_dec(v___x_3221_);
v_options_3440_ = lean_ctor_get(v___y_3424_, 2);
v_hasTrace_3441_ = lean_ctor_get_uint8(v_options_3440_, sizeof(void*)*1);
if (v_hasTrace_3441_ == 0)
{
lean_dec(v_cls_3219_);
v___y_3387_ = v___y_3424_;
v___y_3388_ = v___y_3425_;
goto v___jp_3386_;
}
else
{
lean_object* v_inheritedTraceOptions_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; uint8_t v___x_3445_; 
v_inheritedTraceOptions_3442_ = lean_ctor_get(v___y_3424_, 13);
v___x_3443_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v_cls_3219_);
v___x_3444_ = l_Lean_Name_append(v___x_3443_, v_cls_3219_);
v___x_3445_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3442_, v_options_3440_, v___x_3444_);
lean_dec(v___x_3444_);
if (v___x_3445_ == 0)
{
lean_dec(v_cls_3219_);
v___y_3387_ = v___y_3424_;
v___y_3388_ = v___y_3425_;
goto v___jp_3386_;
}
else
{
lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3446_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__5, &l_Lean_addDecl___lam__8___closed__5_once, _init_l_Lean_addDecl___lam__8___closed__5);
v___x_3447_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3219_, v___x_3446_, v___y_3424_, v___y_3425_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_dec_ref(v___x_3447_);
v___y_3387_ = v___y_3424_;
v___y_3388_ = v___y_3425_;
goto v___jp_3386_;
}
else
{
lean_del_object(v___x_3336_);
lean_dec(v_snd_3334_);
lean_dec(v_fst_3333_);
lean_dec(v_fst_3329_);
lean_dec_ref(v___x_3217_);
lean_dec(v_decl_3216_);
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
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__13___boxed(lean_object* v_decl_3460_, lean_object* v___x_3461_, lean_object* v___x_3462_, lean_object* v_cls_3463_, lean_object* v___x_3464_, lean_object* v___x_3465_, lean_object* v_____x_3466_, lean_object* v_exportedInfo_x3f_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
uint8_t v___x_62681__boxed_3471_; lean_object* v_res_3472_; 
v___x_62681__boxed_3471_ = lean_unbox(v___x_3462_);
v_res_3472_ = l_Lean_addDecl___lam__13(v_decl_3460_, v___x_3461_, v___x_62681__boxed_3471_, v_cls_3463_, v___x_3464_, v___x_3465_, v_____x_3466_, v_exportedInfo_x3f_3467_, v___y_3468_, v___y_3469_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
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
lean_object* v_options_3511_; uint8_t v_hasTrace_3512_; 
lean_dec(v___x_3476_);
v_options_3511_ = lean_ctor_get(v___y_3479_, 2);
v_hasTrace_3512_ = lean_ctor_get_uint8(v_options_3511_, sizeof(void*)*1);
if (v_hasTrace_3512_ == 0)
{
lean_dec(v_cls_3477_);
v___y_3495_ = v___y_3479_;
v___y_3496_ = v___y_3480_;
goto v___jp_3494_;
}
else
{
lean_object* v_inheritedTraceOptions_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; uint8_t v___x_3516_; 
v_inheritedTraceOptions_3513_ = lean_ctor_get(v___y_3479_, 13);
v___x_3514_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v_cls_3477_);
v___x_3515_ = l_Lean_Name_append(v___x_3514_, v_cls_3477_);
v___x_3516_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3513_, v_options_3511_, v___x_3515_);
lean_dec(v___x_3515_);
if (v___x_3516_ == 0)
{
lean_dec(v_cls_3477_);
v___y_3495_ = v___y_3479_;
v___y_3496_ = v___y_3480_;
goto v___jp_3494_;
}
else
{
lean_object* v_toConstantVal_3517_; lean_object* v_name_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
v_toConstantVal_3517_ = lean_ctor_get(v_defn_3478_, 0);
v_name_3518_ = lean_ctor_get(v_toConstantVal_3517_, 0);
v___x_3519_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__1, &l_Lean_addDecl___lam__4___closed__1_once, _init_l_Lean_addDecl___lam__4___closed__1);
lean_inc(v_name_3518_);
v___x_3520_ = l_Lean_MessageData_ofName(v_name_3518_);
v___x_3521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3519_);
lean_ctor_set(v___x_3521_, 1, v___x_3520_);
v___x_3522_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_3523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3521_);
lean_ctor_set(v___x_3523_, 1, v___x_3522_);
v___x_3524_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3477_, v___x_3523_, v___y_3479_, v___y_3480_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_dec_ref(v___x_3524_);
v___y_3495_ = v___y_3479_;
v___y_3496_ = v___y_3480_;
goto v___jp_3494_;
}
else
{
lean_dec_ref(v_defn_3478_);
lean_dec_ref(v___f_3473_);
return v___x_3524_;
}
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
lean_inc(v___y_3485_);
lean_inc_ref(v___y_3484_);
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
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__10___boxed(lean_object* v___f_3525_, lean_object* v_forceExpose_3526_, lean_object* v___x_3527_, lean_object* v___x_3528_, lean_object* v_cls_3529_, lean_object* v_defn_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
uint8_t v_forceExpose_boxed_3534_; uint8_t v___x_63150__boxed_3535_; lean_object* v_res_3536_; 
v_forceExpose_boxed_3534_ = lean_unbox(v_forceExpose_3526_);
v___x_63150__boxed_3535_ = lean_unbox(v___x_3527_);
v_res_3536_ = l_Lean_addDecl___lam__10(v___f_3525_, v_forceExpose_boxed_3534_, v___x_63150__boxed_3535_, v___x_3528_, v_cls_3529_, v_defn_3530_, v___y_3531_, v___y_3532_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__12(lean_object* v_val_3537_, uint8_t v_forceExpose_3538_, lean_object* v___f_3539_, lean_object* v_____r_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_){
_start:
{
lean_object* v_toConstantVal_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
v_toConstantVal_3544_ = lean_ctor_get(v_val_3537_, 0);
lean_inc_ref(v_toConstantVal_3544_);
v___x_3545_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3545_, 0, v_toConstantVal_3544_);
lean_ctor_set_uint8(v___x_3545_, sizeof(void*)*1, v_forceExpose_3538_);
v___x_3546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3545_);
v___x_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3546_);
v___x_3548_ = lean_box(0);
lean_inc(v___y_3542_);
lean_inc_ref(v___y_3541_);
v___x_3549_ = lean_apply_5(v___f_3539_, v___x_3548_, v___x_3547_, v___y_3541_, v___y_3542_, lean_box(0));
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__12___boxed(lean_object* v_val_3550_, lean_object* v_forceExpose_3551_, lean_object* v___f_3552_, lean_object* v_____r_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_){
_start:
{
uint8_t v_forceExpose_boxed_3557_; lean_object* v_res_3558_; 
v_forceExpose_boxed_3557_ = lean_unbox(v_forceExpose_3551_);
v_res_3558_ = l_Lean_addDecl___lam__12(v_val_3550_, v_forceExpose_boxed_3557_, v___f_3552_, v_____r_3553_, v___y_3554_, v___y_3555_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec_ref(v_val_3550_);
return v_res_3558_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_addDecl_spec__1(lean_object* v_x_3559_, lean_object* v_x_3560_){
_start:
{
if (lean_obj_tag(v_x_3560_) == 0)
{
return v_x_3559_;
}
else
{
lean_object* v_head_3561_; lean_object* v_tail_3562_; lean_object* v___x_3563_; 
v_head_3561_ = lean_ctor_get(v_x_3560_, 0);
lean_inc(v_head_3561_);
v_tail_3562_ = lean_ctor_get(v_x_3560_, 1);
lean_inc(v_tail_3562_);
lean_dec_ref(v_x_3560_);
v___x_3563_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(v_x_3559_, v_head_3561_);
v_x_3559_ = v___x_3563_;
v_x_3560_ = v_tail_3562_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_addDecl___closed__1(void){
_start:
{
lean_object* v_cls_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v_cls_3568_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_3569_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
v___x_3570_ = l_Lean_Name_append(v___x_3569_, v_cls_3568_);
return v___x_3570_;
}
}
static lean_object* _init_l_Lean_addDecl___closed__3(void){
_start:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3572_ = ((lean_object*)(l_Lean_addDecl___closed__2));
v___x_3573_ = l_Lean_stringToMessageData(v___x_3572_);
return v___x_3573_;
}
}
static lean_object* _init_l_Lean_addDecl___closed__5(void){
_start:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3575_ = ((lean_object*)(l_Lean_addDecl___closed__4));
v___x_3576_ = l_Lean_stringToMessageData(v___x_3575_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object* v_decl_3577_, uint8_t v_forceExpose_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_){
_start:
{
lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v_a_3585_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v_a_3598_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v_a_3611_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v_a_3624_; lean_object* v_options_3634_; lean_object* v_inheritedTraceOptions_3635_; uint8_t v_hasTrace_3636_; lean_object* v___x_3637_; lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3646_; uint8_t v___y_3647_; lean_object* v___y_3648_; lean_object* v___y_3649_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3716_; uint8_t v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3722_; uint8_t v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v_exportedInfo_x3f_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; uint8_t v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; uint8_t v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v_cls_3773_; 
v_options_3634_ = lean_ctor_get(v_a_3579_, 2);
v_inheritedTraceOptions_3635_ = lean_ctor_get(v_a_3579_, 13);
v_hasTrace_3636_ = lean_ctor_get_uint8(v_options_3634_, sizeof(void*)*1);
v___x_3637_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__0_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v_cls_3773_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
if (v_hasTrace_3636_ == 0)
{
lean_object* v___x_3774_; lean_object* v_env_3775_; lean_object* v_nextMacroScope_3776_; lean_object* v_ngen_3777_; lean_object* v_auxDeclNGen_3778_; lean_object* v_traceState_3779_; lean_object* v_messages_3780_; lean_object* v_infoState_3781_; lean_object* v_snapshotTasks_3782_; lean_object* v_newDecls_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3973_; 
v___x_3774_ = lean_st_ref_take(v_a_3580_);
v_env_3775_ = lean_ctor_get(v___x_3774_, 0);
v_nextMacroScope_3776_ = lean_ctor_get(v___x_3774_, 1);
v_ngen_3777_ = lean_ctor_get(v___x_3774_, 2);
v_auxDeclNGen_3778_ = lean_ctor_get(v___x_3774_, 3);
v_traceState_3779_ = lean_ctor_get(v___x_3774_, 4);
v_messages_3780_ = lean_ctor_get(v___x_3774_, 6);
v_infoState_3781_ = lean_ctor_get(v___x_3774_, 7);
v_snapshotTasks_3782_ = lean_ctor_get(v___x_3774_, 8);
v_newDecls_3783_ = lean_ctor_get(v___x_3774_, 9);
v_isSharedCheck_3973_ = !lean_is_exclusive(v___x_3774_);
if (v_isSharedCheck_3973_ == 0)
{
lean_object* v_unused_3974_; 
v_unused_3974_ = lean_ctor_get(v___x_3774_, 5);
lean_dec(v_unused_3974_);
v___x_3785_ = v___x_3774_;
v_isShared_3786_ = v_isSharedCheck_3973_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_newDecls_3783_);
lean_inc(v_snapshotTasks_3782_);
lean_inc(v_infoState_3781_);
lean_inc(v_messages_3780_);
lean_inc(v_traceState_3779_);
lean_inc(v_auxDeclNGen_3778_);
lean_inc(v_ngen_3777_);
lean_inc(v_nextMacroScope_3776_);
lean_inc(v_env_3775_);
lean_dec(v___x_3774_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3973_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3791_; 
lean_inc(v_decl_3577_);
v___x_3787_ = l_Lean_Declaration_getNames(v_decl_3577_);
v___x_3788_ = l_List_foldl___at___00Lean_addDecl_spec__1(v_env_3775_, v___x_3787_);
v___x_3789_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2);
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 5, v___x_3789_);
lean_ctor_set(v___x_3785_, 0, v___x_3788_);
v___x_3791_ = v___x_3785_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v___x_3788_);
lean_ctor_set(v_reuseFailAlloc_3972_, 1, v_nextMacroScope_3776_);
lean_ctor_set(v_reuseFailAlloc_3972_, 2, v_ngen_3777_);
lean_ctor_set(v_reuseFailAlloc_3972_, 3, v_auxDeclNGen_3778_);
lean_ctor_set(v_reuseFailAlloc_3972_, 4, v_traceState_3779_);
lean_ctor_set(v_reuseFailAlloc_3972_, 5, v___x_3789_);
lean_ctor_set(v_reuseFailAlloc_3972_, 6, v_messages_3780_);
lean_ctor_set(v_reuseFailAlloc_3972_, 7, v_infoState_3781_);
lean_ctor_set(v_reuseFailAlloc_3972_, 8, v_snapshotTasks_3782_);
lean_ctor_set(v_reuseFailAlloc_3972_, 9, v_newDecls_3783_);
v___x_3791_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___y_3795_; uint8_t v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v_fst_3851_; lean_object* v_fst_3852_; uint8_t v_snd_3853_; lean_object* v_exportedInfo_x3f_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3866_; lean_object* v_toConstantVal_3867_; lean_object* v_exportedInfo_x3f_3868_; lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3875_; lean_object* v_exportedInfo_x3f_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3881_; lean_object* v_toConstantVal_3882_; uint8_t v_safety_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v_defn_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; 
v___x_3792_ = lean_st_ref_set(v_a_3580_, v___x_3791_);
v___x_3793_ = lean_box(0);
switch(lean_obj_tag(v_decl_3577_))
{
case 2:
{
lean_object* v_val_3922_; lean_object* v_exportedInfo_x3f_3924_; lean_object* v___y_3925_; lean_object* v___y_3926_; lean_object* v___x_3931_; 
v_val_3922_ = lean_ctor_get(v_decl_3577_, 0);
v___x_3931_ = lean_st_ref_get(v_a_3580_);
if (v_forceExpose_3578_ == 0)
{
lean_object* v_env_3932_; lean_object* v___x_3933_; uint8_t v_isModule_3934_; 
v_env_3932_ = lean_ctor_get(v___x_3931_, 0);
lean_inc_ref(v_env_3932_);
lean_dec(v___x_3931_);
v___x_3933_ = l_Lean_Environment_header(v_env_3932_);
lean_dec_ref(v_env_3932_);
v_isModule_3934_ = lean_ctor_get_uint8(v___x_3933_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3933_);
if (v_isModule_3934_ == 0)
{
v_exportedInfo_x3f_3924_ = v___x_3793_;
v___y_3925_ = v_a_3579_;
v___y_3926_ = v_a_3580_;
goto v___jp_3923_;
}
else
{
lean_object* v_toConstantVal_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; 
v_toConstantVal_3935_ = lean_ctor_get(v_val_3922_, 0);
lean_inc_ref(v_toConstantVal_3935_);
v___x_3936_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3936_, 0, v_toConstantVal_3935_);
lean_ctor_set_uint8(v___x_3936_, sizeof(void*)*1, v_hasTrace_3636_);
v___x_3937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3936_);
v___x_3938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3938_, 0, v___x_3937_);
v_exportedInfo_x3f_3924_ = v___x_3938_;
v___y_3925_ = v_a_3579_;
v___y_3926_ = v_a_3580_;
goto v___jp_3923_;
}
}
else
{
lean_dec(v___x_3931_);
v_exportedInfo_x3f_3924_ = v___x_3793_;
v___y_3925_ = v_a_3579_;
v___y_3926_ = v_a_3580_;
goto v___jp_3923_;
}
v___jp_3923_:
{
lean_object* v_toConstantVal_3927_; lean_object* v_name_3928_; lean_object* v___x_3929_; uint8_t v___x_3930_; 
v_toConstantVal_3927_ = lean_ctor_get(v_val_3922_, 0);
v_name_3928_ = lean_ctor_get(v_toConstantVal_3927_, 0);
lean_inc_ref(v_val_3922_);
v___x_3929_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3929_, 0, v_val_3922_);
v___x_3930_ = 1;
lean_inc(v_name_3928_);
v_fst_3851_ = v_name_3928_;
v_fst_3852_ = v___x_3929_;
v_snd_3853_ = v___x_3930_;
v_exportedInfo_x3f_3854_ = v_exportedInfo_x3f_3924_;
v___y_3855_ = v___y_3925_;
v___y_3856_ = v___y_3926_;
goto v___jp_3850_;
}
}
case 1:
{
lean_object* v_val_3939_; 
v_val_3939_ = lean_ctor_get(v_decl_3577_, 0);
lean_inc_ref(v_val_3939_);
v_defn_3898_ = v_val_3939_;
v___y_3899_ = v_a_3579_;
v___y_3900_ = v_a_3580_;
goto v___jp_3897_;
}
case 5:
{
lean_object* v_defns_3940_; 
v_defns_3940_ = lean_ctor_get(v_decl_3577_, 0);
if (lean_obj_tag(v_defns_3940_) == 1)
{
lean_object* v_tail_3941_; 
v_tail_3941_ = lean_ctor_get(v_defns_3940_, 1);
if (lean_obj_tag(v_tail_3941_) == 0)
{
lean_object* v_head_3942_; 
v_head_3942_ = lean_ctor_get(v_defns_3940_, 0);
lean_inc(v_head_3942_);
v_defn_3898_ = v_head_3942_;
v___y_3899_ = v_a_3579_;
v___y_3900_ = v_a_3580_;
goto v___jp_3897_;
}
else
{
lean_object* v___x_3943_; 
v___x_3943_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3577_, v_a_3579_, v_a_3580_);
return v___x_3943_;
}
}
else
{
lean_object* v___x_3944_; 
v___x_3944_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3577_, v_a_3579_, v_a_3580_);
return v___x_3944_;
}
}
case 3:
{
lean_object* v_val_3945_; lean_object* v_exportedInfo_x3f_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v_val_3945_ = lean_ctor_get(v_decl_3577_, 0);
v___x_3954_ = lean_st_ref_get(v_a_3580_);
v___x_3955_ = lean_st_ref_get(v_a_3580_);
if (v_forceExpose_3578_ == 0)
{
lean_object* v_env_3956_; lean_object* v_env_3957_; lean_object* v___x_3958_; uint8_t v_isModule_3959_; 
v_env_3956_ = lean_ctor_get(v___x_3954_, 0);
lean_inc_ref(v_env_3956_);
lean_dec(v___x_3954_);
v_env_3957_ = lean_ctor_get(v___x_3955_, 0);
lean_inc_ref(v_env_3957_);
lean_dec(v___x_3955_);
v___x_3958_ = l_Lean_Environment_header(v_env_3956_);
lean_dec_ref(v_env_3956_);
v_isModule_3959_ = lean_ctor_get_uint8(v___x_3958_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3958_);
if (v_isModule_3959_ == 0)
{
lean_dec_ref(v_env_3957_);
v_exportedInfo_x3f_3947_ = v___x_3793_;
v___y_3948_ = v_a_3579_;
v___y_3949_ = v_a_3580_;
goto v___jp_3946_;
}
else
{
uint8_t v_isExporting_3960_; 
v_isExporting_3960_ = lean_ctor_get_uint8(v_env_3957_, sizeof(void*)*8);
lean_dec_ref(v_env_3957_);
if (v_isExporting_3960_ == 0)
{
lean_object* v_toConstantVal_3961_; uint8_t v_isUnsafe_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v_toConstantVal_3961_ = lean_ctor_get(v_val_3945_, 0);
v_isUnsafe_3962_ = lean_ctor_get_uint8(v_val_3945_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_3961_);
v___x_3963_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3963_, 0, v_toConstantVal_3961_);
lean_ctor_set_uint8(v___x_3963_, sizeof(void*)*1, v_isUnsafe_3962_);
v___x_3964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3963_);
v___x_3965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3964_);
v_exportedInfo_x3f_3947_ = v___x_3965_;
v___y_3948_ = v_a_3579_;
v___y_3949_ = v_a_3580_;
goto v___jp_3946_;
}
else
{
v_exportedInfo_x3f_3947_ = v___x_3793_;
v___y_3948_ = v_a_3579_;
v___y_3949_ = v_a_3580_;
goto v___jp_3946_;
}
}
}
else
{
lean_dec(v___x_3955_);
lean_dec(v___x_3954_);
v_exportedInfo_x3f_3947_ = v___x_3793_;
v___y_3948_ = v_a_3579_;
v___y_3949_ = v_a_3580_;
goto v___jp_3946_;
}
v___jp_3946_:
{
lean_object* v_toConstantVal_3950_; lean_object* v_name_3951_; lean_object* v___x_3952_; uint8_t v___x_3953_; 
v_toConstantVal_3950_ = lean_ctor_get(v_val_3945_, 0);
v_name_3951_ = lean_ctor_get(v_toConstantVal_3950_, 0);
lean_inc_ref(v_val_3945_);
v___x_3952_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3952_, 0, v_val_3945_);
v___x_3953_ = 3;
lean_inc(v_name_3951_);
v_fst_3851_ = v_name_3951_;
v_fst_3852_ = v___x_3952_;
v_snd_3853_ = v___x_3953_;
v_exportedInfo_x3f_3854_ = v_exportedInfo_x3f_3947_;
v___y_3855_ = v___y_3948_;
v___y_3856_ = v___y_3949_;
goto v___jp_3850_;
}
}
case 0:
{
lean_object* v_val_3966_; lean_object* v_toConstantVal_3967_; lean_object* v_name_3968_; lean_object* v___x_3969_; uint8_t v___x_3970_; 
v_val_3966_ = lean_ctor_get(v_decl_3577_, 0);
v_toConstantVal_3967_ = lean_ctor_get(v_val_3966_, 0);
v_name_3968_ = lean_ctor_get(v_toConstantVal_3967_, 0);
lean_inc_ref(v_val_3966_);
v___x_3969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3969_, 0, v_val_3966_);
v___x_3970_ = 2;
lean_inc(v_name_3968_);
v_fst_3851_ = v_name_3968_;
v_fst_3852_ = v___x_3969_;
v_snd_3853_ = v___x_3970_;
v_exportedInfo_x3f_3854_ = v___x_3793_;
v___y_3855_ = v_a_3579_;
v___y_3856_ = v_a_3580_;
goto v___jp_3850_;
}
default: 
{
lean_object* v___x_3971_; 
v___x_3971_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3577_, v_a_3579_, v_a_3580_);
return v___x_3971_;
}
}
v___jp_3794_:
{
lean_object* v___x_3801_; uint8_t v___x_3802_; 
lean_inc(v_decl_3577_);
v___x_3801_ = l_Lean_Declaration_getTopLevelNames(v_decl_3577_);
v___x_3802_ = l_List_all___at___00Lean_addDecl_spec__2(v___x_3801_);
lean_dec(v___x_3801_);
if (v___x_3802_ == 0)
{
if (lean_obj_tag(v___y_3795_) == 0)
{
lean_object* v_options_3803_; uint8_t v_hasTrace_3804_; 
v_options_3803_ = lean_ctor_get(v___y_3799_, 2);
v_hasTrace_3804_ = lean_ctor_get_uint8(v_options_3803_, sizeof(void*)*1);
if (v_hasTrace_3804_ == 0)
{
v___y_3767_ = v___y_3796_;
v___y_3768_ = v___y_3797_;
v___y_3769_ = v___y_3798_;
v___y_3770_ = v___y_3799_;
v___y_3771_ = v___y_3800_;
goto v___jp_3766_;
}
else
{
lean_object* v_inheritedTraceOptions_3805_; lean_object* v___x_3806_; uint8_t v___x_3807_; 
v_inheritedTraceOptions_3805_ = lean_ctor_get(v___y_3799_, 13);
v___x_3806_ = lean_obj_once(&l_Lean_addDecl___closed__1, &l_Lean_addDecl___closed__1_once, _init_l_Lean_addDecl___closed__1);
v___x_3807_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3805_, v_options_3803_, v___x_3806_);
if (v___x_3807_ == 0)
{
v___y_3767_ = v___y_3796_;
v___y_3768_ = v___y_3797_;
v___y_3769_ = v___y_3798_;
v___y_3770_ = v___y_3799_;
v___y_3771_ = v___y_3800_;
goto v___jp_3766_;
}
else
{
lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3808_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__1, &l_Lean_addDecl___lam__8___closed__1_once, _init_l_Lean_addDecl___lam__8___closed__1);
v___x_3809_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3773_, v___x_3808_, v___y_3799_, v___y_3800_);
if (lean_obj_tag(v___x_3809_) == 0)
{
lean_dec_ref(v___x_3809_);
v___y_3767_ = v___y_3796_;
v___y_3768_ = v___y_3797_;
v___y_3769_ = v___y_3798_;
v___y_3770_ = v___y_3799_;
v___y_3771_ = v___y_3800_;
goto v___jp_3766_;
}
else
{
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec(v_decl_3577_);
return v___x_3809_;
}
}
}
}
else
{
lean_object* v___x_3810_; lean_object* v_env_3811_; lean_object* v_nextMacroScope_3812_; lean_object* v_ngen_3813_; lean_object* v_auxDeclNGen_3814_; lean_object* v_traceState_3815_; lean_object* v_messages_3816_; lean_object* v_infoState_3817_; lean_object* v_snapshotTasks_3818_; lean_object* v_newDecls_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3830_; 
v___x_3810_ = lean_st_ref_take(v___y_3800_);
v_env_3811_ = lean_ctor_get(v___x_3810_, 0);
v_nextMacroScope_3812_ = lean_ctor_get(v___x_3810_, 1);
v_ngen_3813_ = lean_ctor_get(v___x_3810_, 2);
v_auxDeclNGen_3814_ = lean_ctor_get(v___x_3810_, 3);
v_traceState_3815_ = lean_ctor_get(v___x_3810_, 4);
v_messages_3816_ = lean_ctor_get(v___x_3810_, 6);
v_infoState_3817_ = lean_ctor_get(v___x_3810_, 7);
v_snapshotTasks_3818_ = lean_ctor_get(v___x_3810_, 8);
v_newDecls_3819_ = lean_ctor_get(v___x_3810_, 9);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3830_ == 0)
{
lean_object* v_unused_3831_; 
v_unused_3831_ = lean_ctor_get(v___x_3810_, 5);
lean_dec(v_unused_3831_);
v___x_3821_ = v___x_3810_;
v_isShared_3822_ = v_isSharedCheck_3830_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_newDecls_3819_);
lean_inc(v_snapshotTasks_3818_);
lean_inc(v_infoState_3817_);
lean_inc(v_messages_3816_);
lean_inc(v_traceState_3815_);
lean_inc(v_auxDeclNGen_3814_);
lean_inc(v_ngen_3813_);
lean_inc(v_nextMacroScope_3812_);
lean_inc(v_env_3811_);
lean_dec(v___x_3810_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3830_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3827_; 
v___x_3823_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_3824_ = lean_box(v___y_3796_);
lean_inc(v___y_3798_);
v___x_3825_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3823_, v_env_3811_, v___y_3798_, v___x_3824_);
if (v_isShared_3822_ == 0)
{
lean_ctor_set(v___x_3821_, 5, v___x_3789_);
lean_ctor_set(v___x_3821_, 0, v___x_3825_);
v___x_3827_ = v___x_3821_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v___x_3825_);
lean_ctor_set(v_reuseFailAlloc_3829_, 1, v_nextMacroScope_3812_);
lean_ctor_set(v_reuseFailAlloc_3829_, 2, v_ngen_3813_);
lean_ctor_set(v_reuseFailAlloc_3829_, 3, v_auxDeclNGen_3814_);
lean_ctor_set(v_reuseFailAlloc_3829_, 4, v_traceState_3815_);
lean_ctor_set(v_reuseFailAlloc_3829_, 5, v___x_3789_);
lean_ctor_set(v_reuseFailAlloc_3829_, 6, v_messages_3816_);
lean_ctor_set(v_reuseFailAlloc_3829_, 7, v_infoState_3817_);
lean_ctor_set(v_reuseFailAlloc_3829_, 8, v_snapshotTasks_3818_);
lean_ctor_set(v_reuseFailAlloc_3829_, 9, v_newDecls_3819_);
v___x_3827_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
lean_object* v___x_3828_; 
v___x_3828_ = lean_st_ref_set(v___y_3800_, v___x_3827_);
v___y_3745_ = v___y_3796_;
v___y_3746_ = v___y_3797_;
v___y_3747_ = v___y_3798_;
v_exportedInfo_x3f_3748_ = v___y_3795_;
v___y_3749_ = v___y_3799_;
v___y_3750_ = v___y_3800_;
goto v___jp_3744_;
}
}
}
}
else
{
lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v_a_3834_; uint8_t v___x_3835_; 
lean_dec(v___y_3795_);
v___x_3832_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3833_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__3___redArg(v___x_3832_, v___y_3799_);
v_a_3834_ = lean_ctor_get(v___x_3833_, 0);
lean_inc(v_a_3834_);
lean_dec_ref(v___x_3833_);
v___x_3835_ = lean_unbox(v_a_3834_);
lean_dec(v_a_3834_);
if (v___x_3835_ == 0)
{
lean_object* v_options_3836_; uint8_t v_hasTrace_3837_; 
v_options_3836_ = lean_ctor_get(v___y_3799_, 2);
v_hasTrace_3837_ = lean_ctor_get_uint8(v_options_3836_, sizeof(void*)*1);
if (v_hasTrace_3837_ == 0)
{
v___y_3745_ = v___y_3796_;
v___y_3746_ = v___y_3797_;
v___y_3747_ = v___y_3798_;
v_exportedInfo_x3f_3748_ = v___x_3793_;
v___y_3749_ = v___y_3799_;
v___y_3750_ = v___y_3800_;
goto v___jp_3744_;
}
else
{
lean_object* v_inheritedTraceOptions_3838_; lean_object* v___x_3839_; uint8_t v___x_3840_; 
v_inheritedTraceOptions_3838_ = lean_ctor_get(v___y_3799_, 13);
v___x_3839_ = lean_obj_once(&l_Lean_addDecl___closed__1, &l_Lean_addDecl___closed__1_once, _init_l_Lean_addDecl___closed__1);
v___x_3840_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3838_, v_options_3836_, v___x_3839_);
if (v___x_3840_ == 0)
{
v___y_3745_ = v___y_3796_;
v___y_3746_ = v___y_3797_;
v___y_3747_ = v___y_3798_;
v_exportedInfo_x3f_3748_ = v___x_3793_;
v___y_3749_ = v___y_3799_;
v___y_3750_ = v___y_3800_;
goto v___jp_3744_;
}
else
{
lean_object* v___x_3841_; lean_object* v___x_3842_; 
v___x_3841_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__3, &l_Lean_addDecl___lam__8___closed__3_once, _init_l_Lean_addDecl___lam__8___closed__3);
v___x_3842_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3773_, v___x_3841_, v___y_3799_, v___y_3800_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_dec_ref(v___x_3842_);
v___y_3745_ = v___y_3796_;
v___y_3746_ = v___y_3797_;
v___y_3747_ = v___y_3798_;
v_exportedInfo_x3f_3748_ = v___x_3793_;
v___y_3749_ = v___y_3799_;
v___y_3750_ = v___y_3800_;
goto v___jp_3744_;
}
else
{
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec(v_decl_3577_);
return v___x_3842_;
}
}
}
}
else
{
lean_object* v_options_3843_; uint8_t v_hasTrace_3844_; 
v_options_3843_ = lean_ctor_get(v___y_3799_, 2);
v_hasTrace_3844_ = lean_ctor_get_uint8(v_options_3843_, sizeof(void*)*1);
if (v_hasTrace_3844_ == 0)
{
v___y_3760_ = v___y_3796_;
v___y_3761_ = v___y_3797_;
v___y_3762_ = v___y_3798_;
v___y_3763_ = v___y_3799_;
v___y_3764_ = v___y_3800_;
goto v___jp_3759_;
}
else
{
lean_object* v_inheritedTraceOptions_3845_; lean_object* v___x_3846_; uint8_t v___x_3847_; 
v_inheritedTraceOptions_3845_ = lean_ctor_get(v___y_3799_, 13);
v___x_3846_ = lean_obj_once(&l_Lean_addDecl___closed__1, &l_Lean_addDecl___closed__1_once, _init_l_Lean_addDecl___closed__1);
v___x_3847_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3845_, v_options_3843_, v___x_3846_);
if (v___x_3847_ == 0)
{
v___y_3760_ = v___y_3796_;
v___y_3761_ = v___y_3797_;
v___y_3762_ = v___y_3798_;
v___y_3763_ = v___y_3799_;
v___y_3764_ = v___y_3800_;
goto v___jp_3759_;
}
else
{
lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3848_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__5, &l_Lean_addDecl___lam__8___closed__5_once, _init_l_Lean_addDecl___lam__8___closed__5);
v___x_3849_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3773_, v___x_3848_, v___y_3799_, v___y_3800_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_dec_ref(v___x_3849_);
v___y_3760_ = v___y_3796_;
v___y_3761_ = v___y_3797_;
v___y_3762_ = v___y_3798_;
v___y_3763_ = v___y_3799_;
v___y_3764_ = v___y_3800_;
goto v___jp_3759_;
}
else
{
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec(v_decl_3577_);
return v___x_3849_;
}
}
}
}
}
}
v___jp_3850_:
{
lean_object* v___x_3857_; lean_object* v_env_3858_; uint8_t v___x_3859_; 
v___x_3857_ = lean_st_ref_get(v___y_3856_);
v_env_3858_ = lean_ctor_get(v___x_3857_, 0);
lean_inc_ref(v_env_3858_);
lean_dec(v___x_3857_);
v___x_3859_ = l_Lean_Environment_containsOnBranch(v_env_3858_, v_fst_3851_);
lean_dec_ref(v_env_3858_);
if (v___x_3859_ == 0)
{
v___y_3795_ = v_exportedInfo_x3f_3854_;
v___y_3796_ = v_snd_3853_;
v___y_3797_ = v_fst_3852_;
v___y_3798_ = v_fst_3851_;
v___y_3799_ = v___y_3855_;
v___y_3800_ = v___y_3856_;
goto v___jp_3794_;
}
else
{
lean_object* v___x_3860_; lean_object* v_env_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; 
lean_dec(v_exportedInfo_x3f_3854_);
lean_dec_ref(v_fst_3852_);
lean_dec(v_decl_3577_);
v___x_3860_ = lean_st_ref_get(v___y_3856_);
v_env_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc_ref(v_env_3861_);
lean_dec(v___x_3860_);
v___x_3862_ = lean_elab_environment_to_kernel_env(v_env_3861_);
v___x_3863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3862_);
lean_ctor_set(v___x_3863_, 1, v_fst_3851_);
v___x_3864_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(v___x_3863_, v___y_3855_, v___y_3856_);
return v___x_3864_;
}
}
v___jp_3865_:
{
lean_object* v_name_3871_; lean_object* v___x_3872_; uint8_t v___x_3873_; 
v_name_3871_ = lean_ctor_get(v_toConstantVal_3867_, 0);
lean_inc(v_name_3871_);
lean_dec_ref(v_toConstantVal_3867_);
v___x_3872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3872_, 0, v___y_3866_);
v___x_3873_ = 0;
v_fst_3851_ = v_name_3871_;
v_fst_3852_ = v___x_3872_;
v_snd_3853_ = v___x_3873_;
v_exportedInfo_x3f_3854_ = v_exportedInfo_x3f_3868_;
v___y_3855_ = v___y_3869_;
v___y_3856_ = v___y_3870_;
goto v___jp_3850_;
}
v___jp_3874_:
{
lean_object* v_toConstantVal_3879_; 
v_toConstantVal_3879_ = lean_ctor_get(v___y_3875_, 0);
lean_inc_ref(v_toConstantVal_3879_);
v___y_3866_ = v___y_3875_;
v_toConstantVal_3867_ = v_toConstantVal_3879_;
v_exportedInfo_x3f_3868_ = v_exportedInfo_x3f_3876_;
v___y_3869_ = v___y_3877_;
v___y_3870_ = v___y_3878_;
goto v___jp_3865_;
}
v___jp_3880_:
{
uint8_t v___x_3886_; uint8_t v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3886_ = 0;
v___x_3887_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3883_, v___x_3886_);
lean_inc_ref(v_toConstantVal_3882_);
v___x_3888_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3888_, 0, v_toConstantVal_3882_);
lean_ctor_set_uint8(v___x_3888_, sizeof(void*)*1, v___x_3887_);
v___x_3889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3888_);
v___x_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3889_);
v___y_3866_ = v___y_3881_;
v_toConstantVal_3867_ = v_toConstantVal_3882_;
v_exportedInfo_x3f_3868_ = v___x_3890_;
v___y_3869_ = v___y_3884_;
v___y_3870_ = v___y_3885_;
goto v___jp_3865_;
}
v___jp_3891_:
{
lean_object* v_toConstantVal_3895_; uint8_t v_safety_3896_; 
v_toConstantVal_3895_ = lean_ctor_get(v___y_3892_, 0);
lean_inc_ref(v_toConstantVal_3895_);
v_safety_3896_ = lean_ctor_get_uint8(v___y_3892_, sizeof(void*)*4);
v___y_3881_ = v___y_3892_;
v_toConstantVal_3882_ = v_toConstantVal_3895_;
v_safety_3883_ = v_safety_3896_;
v___y_3884_ = v___y_3893_;
v___y_3885_ = v___y_3894_;
goto v___jp_3880_;
}
v___jp_3897_:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3901_ = lean_st_ref_get(v___y_3900_);
v___x_3902_ = lean_st_ref_get(v___y_3900_);
if (v_forceExpose_3578_ == 0)
{
lean_object* v_env_3903_; lean_object* v_env_3904_; lean_object* v___x_3905_; uint8_t v_isModule_3906_; 
v_env_3903_ = lean_ctor_get(v___x_3901_, 0);
lean_inc_ref(v_env_3903_);
lean_dec(v___x_3901_);
v_env_3904_ = lean_ctor_get(v___x_3902_, 0);
lean_inc_ref(v_env_3904_);
lean_dec(v___x_3902_);
v___x_3905_ = l_Lean_Environment_header(v_env_3903_);
lean_dec_ref(v_env_3903_);
v_isModule_3906_ = lean_ctor_get_uint8(v___x_3905_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3905_);
if (v_isModule_3906_ == 0)
{
lean_dec_ref(v_env_3904_);
v___y_3875_ = v_defn_3898_;
v_exportedInfo_x3f_3876_ = v___x_3793_;
v___y_3877_ = v___y_3899_;
v___y_3878_ = v___y_3900_;
goto v___jp_3874_;
}
else
{
uint8_t v_isExporting_3907_; 
v_isExporting_3907_ = lean_ctor_get_uint8(v_env_3904_, sizeof(void*)*8);
lean_dec_ref(v_env_3904_);
if (v_isExporting_3907_ == 0)
{
lean_object* v_options_3908_; uint8_t v_hasTrace_3909_; 
v_options_3908_ = lean_ctor_get(v___y_3899_, 2);
v_hasTrace_3909_ = lean_ctor_get_uint8(v_options_3908_, sizeof(void*)*1);
if (v_hasTrace_3909_ == 0)
{
v___y_3892_ = v_defn_3898_;
v___y_3893_ = v___y_3899_;
v___y_3894_ = v___y_3900_;
goto v___jp_3891_;
}
else
{
lean_object* v_inheritedTraceOptions_3910_; lean_object* v___x_3911_; uint8_t v___x_3912_; 
v_inheritedTraceOptions_3910_ = lean_ctor_get(v___y_3899_, 13);
v___x_3911_ = lean_obj_once(&l_Lean_addDecl___closed__1, &l_Lean_addDecl___closed__1_once, _init_l_Lean_addDecl___closed__1);
v___x_3912_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3910_, v_options_3908_, v___x_3911_);
if (v___x_3912_ == 0)
{
v___y_3892_ = v_defn_3898_;
v___y_3893_ = v___y_3899_;
v___y_3894_ = v___y_3900_;
goto v___jp_3891_;
}
else
{
lean_object* v_toConstantVal_3913_; uint8_t v_safety_3914_; lean_object* v_name_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
v_toConstantVal_3913_ = lean_ctor_get(v_defn_3898_, 0);
lean_inc_ref(v_toConstantVal_3913_);
v_safety_3914_ = lean_ctor_get_uint8(v_defn_3898_, sizeof(void*)*4);
v_name_3915_ = lean_ctor_get(v_toConstantVal_3913_, 0);
v___x_3916_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__1, &l_Lean_addDecl___lam__4___closed__1_once, _init_l_Lean_addDecl___lam__4___closed__1);
lean_inc(v_name_3915_);
v___x_3917_ = l_Lean_MessageData_ofName(v_name_3915_);
v___x_3918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3916_);
lean_ctor_set(v___x_3918_, 1, v___x_3917_);
v___x_3919_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_3920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3918_);
lean_ctor_set(v___x_3920_, 1, v___x_3919_);
v___x_3921_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3773_, v___x_3920_, v___y_3899_, v___y_3900_);
if (lean_obj_tag(v___x_3921_) == 0)
{
lean_dec_ref(v___x_3921_);
v___y_3881_ = v_defn_3898_;
v_toConstantVal_3882_ = v_toConstantVal_3913_;
v_safety_3883_ = v_safety_3914_;
v___y_3884_ = v___y_3899_;
v___y_3885_ = v___y_3900_;
goto v___jp_3880_;
}
else
{
lean_dec_ref(v_toConstantVal_3913_);
lean_dec_ref(v_defn_3898_);
lean_dec(v_decl_3577_);
return v___x_3921_;
}
}
}
}
else
{
v___y_3875_ = v_defn_3898_;
v_exportedInfo_x3f_3876_ = v___x_3793_;
v___y_3877_ = v___y_3899_;
v___y_3878_ = v___y_3900_;
goto v___jp_3874_;
}
}
}
else
{
lean_dec(v___x_3902_);
lean_dec(v___x_3901_);
v___y_3875_ = v_defn_3898_;
v_exportedInfo_x3f_3876_ = v___x_3793_;
v___y_3877_ = v___y_3899_;
v___y_3878_ = v___y_3900_;
goto v___jp_3874_;
}
}
}
}
}
else
{
lean_object* v___f_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; uint8_t v___x_3978_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v_a_3982_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v_a_4028_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; uint8_t v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; 
lean_inc(v_decl_3577_);
v___f_3975_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__1___boxed), 5, 1);
lean_closure_set(v___f_3975_, 0, v_decl_3577_);
v___x_3976_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_3977_ = lean_obj_once(&l_Lean_addDecl___closed__1, &l_Lean_addDecl___closed__1_once, _init_l_Lean_addDecl___closed__1);
v___x_3978_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3635_, v_options_3634_, v___x_3977_);
if (v___x_3978_ == 0)
{
lean_object* v___x_4280_; uint8_t v___x_4281_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; uint8_t v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4365_; uint8_t v___y_4387_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v_exportedInfo_x3f_4390_; lean_object* v___y_4391_; lean_object* v___y_4392_; uint8_t v___y_4402_; lean_object* v___y_4403_; lean_object* v___y_4404_; lean_object* v___y_4405_; lean_object* v___y_4406_; uint8_t v___y_4409_; lean_object* v___y_4410_; lean_object* v___y_4411_; lean_object* v___y_4412_; lean_object* v___y_4413_; 
v___x_4280_ = l_Lean_trace_profiler;
v___x_4281_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3634_, v___x_4280_);
if (v___x_4281_ == 0)
{
lean_object* v___x_4415_; lean_object* v_env_4416_; lean_object* v_nextMacroScope_4417_; lean_object* v_ngen_4418_; lean_object* v_auxDeclNGen_4419_; lean_object* v_traceState_4420_; lean_object* v_messages_4421_; lean_object* v_infoState_4422_; lean_object* v_snapshotTasks_4423_; lean_object* v_newDecls_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4661_; 
lean_dec_ref(v___f_3975_);
v___x_4415_ = lean_st_ref_take(v_a_3580_);
v_env_4416_ = lean_ctor_get(v___x_4415_, 0);
v_nextMacroScope_4417_ = lean_ctor_get(v___x_4415_, 1);
v_ngen_4418_ = lean_ctor_get(v___x_4415_, 2);
v_auxDeclNGen_4419_ = lean_ctor_get(v___x_4415_, 3);
v_traceState_4420_ = lean_ctor_get(v___x_4415_, 4);
v_messages_4421_ = lean_ctor_get(v___x_4415_, 6);
v_infoState_4422_ = lean_ctor_get(v___x_4415_, 7);
v_snapshotTasks_4423_ = lean_ctor_get(v___x_4415_, 8);
v_newDecls_4424_ = lean_ctor_get(v___x_4415_, 9);
v_isSharedCheck_4661_ = !lean_is_exclusive(v___x_4415_);
if (v_isSharedCheck_4661_ == 0)
{
lean_object* v_unused_4662_; 
v_unused_4662_ = lean_ctor_get(v___x_4415_, 5);
lean_dec(v_unused_4662_);
v___x_4426_ = v___x_4415_;
v_isShared_4427_ = v_isSharedCheck_4661_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_newDecls_4424_);
lean_inc(v_snapshotTasks_4423_);
lean_inc(v_infoState_4422_);
lean_inc(v_messages_4421_);
lean_inc(v_traceState_4420_);
lean_inc(v_auxDeclNGen_4419_);
lean_inc(v_ngen_4418_);
lean_inc(v_nextMacroScope_4417_);
lean_inc(v_env_4416_);
lean_dec(v___x_4415_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4661_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; uint8_t v___y_4432_; lean_object* v___y_4433_; lean_object* v___y_4434_; lean_object* v___y_4435_; lean_object* v___y_4436_; lean_object* v___y_4437_; lean_object* v___x_4461_; 
lean_inc(v_decl_3577_);
v___x_4428_ = l_Lean_Declaration_getNames(v_decl_3577_);
v___x_4429_ = l_List_foldl___at___00Lean_addDecl_spec__1(v_env_4416_, v___x_4428_);
v___x_4430_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2);
if (v_isShared_4427_ == 0)
{
lean_ctor_set(v___x_4426_, 5, v___x_4430_);
lean_ctor_set(v___x_4426_, 0, v___x_4429_);
v___x_4461_ = v___x_4426_;
goto v_reusejp_4460_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v___x_4429_);
lean_ctor_set(v_reuseFailAlloc_4660_, 1, v_nextMacroScope_4417_);
lean_ctor_set(v_reuseFailAlloc_4660_, 2, v_ngen_4418_);
lean_ctor_set(v_reuseFailAlloc_4660_, 3, v_auxDeclNGen_4419_);
lean_ctor_set(v_reuseFailAlloc_4660_, 4, v_traceState_4420_);
lean_ctor_set(v_reuseFailAlloc_4660_, 5, v___x_4430_);
lean_ctor_set(v_reuseFailAlloc_4660_, 6, v_messages_4421_);
lean_ctor_set(v_reuseFailAlloc_4660_, 7, v_infoState_4422_);
lean_ctor_set(v_reuseFailAlloc_4660_, 8, v_snapshotTasks_4423_);
lean_ctor_set(v_reuseFailAlloc_4660_, 9, v_newDecls_4424_);
v___x_4461_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4460_;
}
v___jp_4431_:
{
lean_object* v___x_4438_; lean_object* v_env_4439_; lean_object* v_nextMacroScope_4440_; lean_object* v_ngen_4441_; lean_object* v_auxDeclNGen_4442_; lean_object* v_traceState_4443_; lean_object* v_messages_4444_; lean_object* v_infoState_4445_; lean_object* v_snapshotTasks_4446_; lean_object* v_newDecls_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4458_; 
v___x_4438_ = lean_st_ref_take(v___y_4436_);
v_env_4439_ = lean_ctor_get(v___x_4438_, 0);
v_nextMacroScope_4440_ = lean_ctor_get(v___x_4438_, 1);
v_ngen_4441_ = lean_ctor_get(v___x_4438_, 2);
v_auxDeclNGen_4442_ = lean_ctor_get(v___x_4438_, 3);
v_traceState_4443_ = lean_ctor_get(v___x_4438_, 4);
v_messages_4444_ = lean_ctor_get(v___x_4438_, 6);
v_infoState_4445_ = lean_ctor_get(v___x_4438_, 7);
v_snapshotTasks_4446_ = lean_ctor_get(v___x_4438_, 8);
v_newDecls_4447_ = lean_ctor_get(v___x_4438_, 9);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4438_);
if (v_isSharedCheck_4458_ == 0)
{
lean_object* v_unused_4459_; 
v_unused_4459_ = lean_ctor_get(v___x_4438_, 5);
lean_dec(v_unused_4459_);
v___x_4449_ = v___x_4438_;
v_isShared_4450_ = v_isSharedCheck_4458_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_newDecls_4447_);
lean_inc(v_snapshotTasks_4446_);
lean_inc(v_infoState_4445_);
lean_inc(v_messages_4444_);
lean_inc(v_traceState_4443_);
lean_inc(v_auxDeclNGen_4442_);
lean_inc(v_ngen_4441_);
lean_inc(v_nextMacroScope_4440_);
lean_inc(v_env_4439_);
lean_dec(v___x_4438_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4458_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4455_; 
v___x_4451_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4452_ = lean_box(v___y_4432_);
lean_inc(v___y_4433_);
v___x_4453_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4451_, v_env_4439_, v___y_4433_, v___x_4452_);
if (v_isShared_4450_ == 0)
{
lean_ctor_set(v___x_4449_, 5, v___x_4430_);
lean_ctor_set(v___x_4449_, 0, v___x_4453_);
v___x_4455_ = v___x_4449_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v___x_4453_);
lean_ctor_set(v_reuseFailAlloc_4457_, 1, v_nextMacroScope_4440_);
lean_ctor_set(v_reuseFailAlloc_4457_, 2, v_ngen_4441_);
lean_ctor_set(v_reuseFailAlloc_4457_, 3, v_auxDeclNGen_4442_);
lean_ctor_set(v_reuseFailAlloc_4457_, 4, v_traceState_4443_);
lean_ctor_set(v_reuseFailAlloc_4457_, 5, v___x_4430_);
lean_ctor_set(v_reuseFailAlloc_4457_, 6, v_messages_4444_);
lean_ctor_set(v_reuseFailAlloc_4457_, 7, v_infoState_4445_);
lean_ctor_set(v_reuseFailAlloc_4457_, 8, v_snapshotTasks_4446_);
lean_ctor_set(v_reuseFailAlloc_4457_, 9, v_newDecls_4447_);
v___x_4455_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
lean_object* v___x_4456_; 
v___x_4456_ = lean_st_ref_set(v___y_4436_, v___x_4455_);
v___y_4387_ = v___y_4432_;
v___y_4388_ = v___y_4433_;
v___y_4389_ = v___y_4435_;
v_exportedInfo_x3f_4390_ = v___y_4434_;
v___y_4391_ = v___y_4437_;
v___y_4392_ = v___y_4436_;
goto v___jp_4386_;
}
}
}
v_reusejp_4460_:
{
lean_object* v___x_4462_; lean_object* v___y_4464_; lean_object* v_options_4465_; lean_object* v_inheritedTraceOptions_4466_; lean_object* v___y_4467_; lean_object* v___x_4473_; uint8_t v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; lean_object* v___y_4480_; lean_object* v_fst_4506_; lean_object* v_fst_4507_; uint8_t v_snd_4508_; lean_object* v_exportedInfo_x3f_4509_; lean_object* v___y_4510_; lean_object* v___y_4511_; lean_object* v___y_4521_; lean_object* v_toConstantVal_4522_; lean_object* v_exportedInfo_x3f_4523_; lean_object* v___y_4524_; lean_object* v___y_4525_; lean_object* v___y_4530_; lean_object* v_toConstantVal_4531_; uint8_t v_safety_4532_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4541_; lean_object* v___y_4542_; lean_object* v___y_4543_; lean_object* v___y_4547_; lean_object* v___y_4548_; lean_object* v___y_4549_; lean_object* v___y_4564_; lean_object* v_exportedInfo_x3f_4565_; lean_object* v___y_4566_; lean_object* v___y_4567_; lean_object* v___y_4570_; lean_object* v___y_4571_; lean_object* v___y_4572_; lean_object* v___y_4573_; lean_object* v___y_4574_; lean_object* v_defn_4579_; lean_object* v___y_4580_; lean_object* v___y_4581_; 
v___x_4462_ = lean_st_ref_set(v_a_3580_, v___x_4461_);
v___x_4473_ = lean_box(0);
switch(lean_obj_tag(v_decl_3577_))
{
case 2:
{
lean_object* v_val_4588_; lean_object* v_exportedInfo_x3f_4590_; lean_object* v___y_4591_; lean_object* v___y_4592_; lean_object* v___y_4598_; lean_object* v___y_4599_; lean_object* v___x_4604_; lean_object* v_env_4605_; 
v_val_4588_ = lean_ctor_get(v_decl_3577_, 0);
v___x_4604_ = lean_st_ref_get(v_a_3580_);
v_env_4605_ = lean_ctor_get(v___x_4604_, 0);
lean_inc_ref(v_env_4605_);
lean_dec(v___x_4604_);
if (v_forceExpose_3578_ == 0)
{
goto v___jp_4606_;
}
else
{
if (v___x_4281_ == 0)
{
lean_dec_ref(v_env_4605_);
v_exportedInfo_x3f_4590_ = v___x_4473_;
v___y_4591_ = v_a_3579_;
v___y_4592_ = v_a_3580_;
goto v___jp_4589_;
}
else
{
goto v___jp_4606_;
}
}
v___jp_4589_:
{
lean_object* v_toConstantVal_4593_; lean_object* v_name_4594_; lean_object* v___x_4595_; uint8_t v___x_4596_; 
v_toConstantVal_4593_ = lean_ctor_get(v_val_4588_, 0);
v_name_4594_ = lean_ctor_get(v_toConstantVal_4593_, 0);
lean_inc_ref(v_val_4588_);
v___x_4595_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4595_, 0, v_val_4588_);
v___x_4596_ = 1;
lean_inc(v_name_4594_);
v_fst_4506_ = v_name_4594_;
v_fst_4507_ = v___x_4595_;
v_snd_4508_ = v___x_4596_;
v_exportedInfo_x3f_4509_ = v_exportedInfo_x3f_4590_;
v___y_4510_ = v___y_4591_;
v___y_4511_ = v___y_4592_;
goto v___jp_4505_;
}
v___jp_4597_:
{
lean_object* v_toConstantVal_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; 
v_toConstantVal_4600_ = lean_ctor_get(v_val_4588_, 0);
lean_inc_ref(v_toConstantVal_4600_);
v___x_4601_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4601_, 0, v_toConstantVal_4600_);
lean_ctor_set_uint8(v___x_4601_, sizeof(void*)*1, v___x_4281_);
v___x_4602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4602_, 0, v___x_4601_);
v___x_4603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4603_, 0, v___x_4602_);
v_exportedInfo_x3f_4590_ = v___x_4603_;
v___y_4591_ = v___y_4598_;
v___y_4592_ = v___y_4599_;
goto v___jp_4589_;
}
v___jp_4606_:
{
lean_object* v___x_4607_; uint8_t v_isModule_4608_; 
v___x_4607_ = l_Lean_Environment_header(v_env_4605_);
lean_dec_ref(v_env_4605_);
v_isModule_4608_ = lean_ctor_get_uint8(v___x_4607_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4607_);
if (v_isModule_4608_ == 0)
{
v_exportedInfo_x3f_4590_ = v___x_4473_;
v___y_4591_ = v_a_3579_;
v___y_4592_ = v_a_3580_;
goto v___jp_4589_;
}
else
{
if (v___x_3978_ == 0)
{
v___y_4598_ = v_a_3579_;
v___y_4599_ = v_a_3580_;
goto v___jp_4597_;
}
else
{
lean_object* v_toConstantVal_4609_; lean_object* v_name_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; 
v_toConstantVal_4609_ = lean_ctor_get(v_val_4588_, 0);
v_name_4610_ = lean_ctor_get(v_toConstantVal_4609_, 0);
v___x_4611_ = lean_obj_once(&l_Lean_addDecl___closed__5, &l_Lean_addDecl___closed__5_once, _init_l_Lean_addDecl___closed__5);
lean_inc(v_name_4610_);
v___x_4612_ = l_Lean_MessageData_ofName(v_name_4610_);
v___x_4613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4613_, 0, v___x_4611_);
lean_ctor_set(v___x_4613_, 1, v___x_4612_);
v___x_4614_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_4615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4615_, 0, v___x_4613_);
lean_ctor_set(v___x_4615_, 1, v___x_4614_);
v___x_4616_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3773_, v___x_4615_, v_a_3579_, v_a_3580_);
if (lean_obj_tag(v___x_4616_) == 0)
{
lean_dec_ref(v___x_4616_);
v___y_4598_ = v_a_3579_;
v___y_4599_ = v_a_3580_;
goto v___jp_4597_;
}
else
{
lean_dec_ref(v_decl_3577_);
return v___x_4616_;
}
}
}
}
}
case 1:
{
lean_object* v_val_4617_; 
v_val_4617_ = lean_ctor_get(v_decl_3577_, 0);
lean_inc_ref(v_val_4617_);
v_defn_4579_ = v_val_4617_;
v___y_4580_ = v_a_3579_;
v___y_4581_ = v_a_3580_;
goto v___jp_4578_;
}
case 5:
{
lean_object* v_defns_4618_; 
v_defns_4618_ = lean_ctor_get(v_decl_3577_, 0);
if (lean_obj_tag(v_defns_4618_) == 1)
{
lean_object* v_tail_4619_; 
v_tail_4619_ = lean_ctor_get(v_defns_4618_, 1);
if (lean_obj_tag(v_tail_4619_) == 0)
{
lean_object* v_head_4620_; 
v_head_4620_ = lean_ctor_get(v_defns_4618_, 0);
lean_inc(v_head_4620_);
v_defn_4579_ = v_head_4620_;
v___y_4580_ = v_a_3579_;
v___y_4581_ = v_a_3580_;
goto v___jp_4578_;
}
else
{
v___y_4464_ = v_a_3579_;
v_options_4465_ = v_options_3634_;
v_inheritedTraceOptions_4466_ = v_inheritedTraceOptions_3635_;
v___y_4467_ = v_a_3580_;
goto v___jp_4463_;
}
}
else
{
v___y_4464_ = v_a_3579_;
v_options_4465_ = v_options_3634_;
v_inheritedTraceOptions_4466_ = v_inheritedTraceOptions_3635_;
v___y_4467_ = v_a_3580_;
goto v___jp_4463_;
}
}
case 3:
{
lean_object* v_val_4621_; lean_object* v_exportedInfo_x3f_4623_; lean_object* v___y_4624_; lean_object* v___y_4625_; lean_object* v___y_4631_; lean_object* v___y_4632_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v_env_4649_; lean_object* v_env_4650_; 
v_val_4621_ = lean_ctor_get(v_decl_3577_, 0);
v___x_4638_ = lean_st_ref_get(v_a_3580_);
v___x_4639_ = lean_st_ref_get(v_a_3580_);
v_env_4649_ = lean_ctor_get(v___x_4638_, 0);
lean_inc_ref(v_env_4649_);
lean_dec(v___x_4638_);
v_env_4650_ = lean_ctor_get(v___x_4639_, 0);
lean_inc_ref(v_env_4650_);
lean_dec(v___x_4639_);
if (v_forceExpose_3578_ == 0)
{
goto v___jp_4651_;
}
else
{
if (v___x_4281_ == 0)
{
lean_dec_ref(v_env_4650_);
lean_dec_ref(v_env_4649_);
v_exportedInfo_x3f_4623_ = v___x_4473_;
v___y_4624_ = v_a_3579_;
v___y_4625_ = v_a_3580_;
goto v___jp_4622_;
}
else
{
goto v___jp_4651_;
}
}
v___jp_4622_:
{
lean_object* v_toConstantVal_4626_; lean_object* v_name_4627_; lean_object* v___x_4628_; uint8_t v___x_4629_; 
v_toConstantVal_4626_ = lean_ctor_get(v_val_4621_, 0);
v_name_4627_ = lean_ctor_get(v_toConstantVal_4626_, 0);
lean_inc_ref(v_val_4621_);
v___x_4628_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4628_, 0, v_val_4621_);
v___x_4629_ = 3;
lean_inc(v_name_4627_);
v_fst_4506_ = v_name_4627_;
v_fst_4507_ = v___x_4628_;
v_snd_4508_ = v___x_4629_;
v_exportedInfo_x3f_4509_ = v_exportedInfo_x3f_4623_;
v___y_4510_ = v___y_4624_;
v___y_4511_ = v___y_4625_;
goto v___jp_4505_;
}
v___jp_4630_:
{
lean_object* v_toConstantVal_4633_; uint8_t v_isUnsafe_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; 
v_toConstantVal_4633_ = lean_ctor_get(v_val_4621_, 0);
v_isUnsafe_4634_ = lean_ctor_get_uint8(v_val_4621_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4633_);
v___x_4635_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4635_, 0, v_toConstantVal_4633_);
lean_ctor_set_uint8(v___x_4635_, sizeof(void*)*1, v_isUnsafe_4634_);
v___x_4636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4636_, 0, v___x_4635_);
v___x_4637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4637_, 0, v___x_4636_);
v_exportedInfo_x3f_4623_ = v___x_4637_;
v___y_4624_ = v___y_4631_;
v___y_4625_ = v___y_4632_;
goto v___jp_4622_;
}
v___jp_4640_:
{
if (v___x_3978_ == 0)
{
v___y_4631_ = v_a_3579_;
v___y_4632_ = v_a_3580_;
goto v___jp_4630_;
}
else
{
lean_object* v_toConstantVal_4641_; lean_object* v_name_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; 
v_toConstantVal_4641_ = lean_ctor_get(v_val_4621_, 0);
v_name_4642_ = lean_ctor_get(v_toConstantVal_4641_, 0);
v___x_4643_ = lean_obj_once(&l_Lean_addDecl___closed__3, &l_Lean_addDecl___closed__3_once, _init_l_Lean_addDecl___closed__3);
lean_inc(v_name_4642_);
v___x_4644_ = l_Lean_MessageData_ofName(v_name_4642_);
v___x_4645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4645_, 0, v___x_4643_);
lean_ctor_set(v___x_4645_, 1, v___x_4644_);
v___x_4646_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_4647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4647_, 0, v___x_4645_);
lean_ctor_set(v___x_4647_, 1, v___x_4646_);
v___x_4648_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3773_, v___x_4647_, v_a_3579_, v_a_3580_);
if (lean_obj_tag(v___x_4648_) == 0)
{
lean_dec_ref(v___x_4648_);
v___y_4631_ = v_a_3579_;
v___y_4632_ = v_a_3580_;
goto v___jp_4630_;
}
else
{
lean_dec_ref(v_decl_3577_);
return v___x_4648_;
}
}
}
v___jp_4651_:
{
lean_object* v___x_4652_; uint8_t v_isModule_4653_; 
v___x_4652_ = l_Lean_Environment_header(v_env_4649_);
lean_dec_ref(v_env_4649_);
v_isModule_4653_ = lean_ctor_get_uint8(v___x_4652_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4652_);
if (v_isModule_4653_ == 0)
{
lean_dec_ref(v_env_4650_);
v_exportedInfo_x3f_4623_ = v___x_4473_;
v___y_4624_ = v_a_3579_;
v___y_4625_ = v_a_3580_;
goto v___jp_4622_;
}
else
{
uint8_t v_isExporting_4654_; 
v_isExporting_4654_ = lean_ctor_get_uint8(v_env_4650_, sizeof(void*)*8);
lean_dec_ref(v_env_4650_);
if (v_isExporting_4654_ == 0)
{
goto v___jp_4640_;
}
else
{
if (v___x_4281_ == 0)
{
v_exportedInfo_x3f_4623_ = v___x_4473_;
v___y_4624_ = v_a_3579_;
v___y_4625_ = v_a_3580_;
goto v___jp_4622_;
}
else
{
goto v___jp_4640_;
}
}
}
}
}
case 0:
{
lean_object* v_val_4655_; lean_object* v_toConstantVal_4656_; lean_object* v_name_4657_; lean_object* v___x_4658_; uint8_t v___x_4659_; 
v_val_4655_ = lean_ctor_get(v_decl_3577_, 0);
v_toConstantVal_4656_ = lean_ctor_get(v_val_4655_, 0);
v_name_4657_ = lean_ctor_get(v_toConstantVal_4656_, 0);
lean_inc_ref(v_val_4655_);
v___x_4658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4658_, 0, v_val_4655_);
v___x_4659_ = 2;
lean_inc(v_name_4657_);
v_fst_4506_ = v_name_4657_;
v_fst_4507_ = v___x_4658_;
v_snd_4508_ = v___x_4659_;
v_exportedInfo_x3f_4509_ = v___x_4473_;
v___y_4510_ = v_a_3579_;
v___y_4511_ = v_a_3580_;
goto v___jp_4505_;
}
default: 
{
v___y_4464_ = v_a_3579_;
v_options_4465_ = v_options_3634_;
v_inheritedTraceOptions_4466_ = v_inheritedTraceOptions_3635_;
v___y_4467_ = v_a_3580_;
goto v___jp_4463_;
}
}
v___jp_4463_:
{
uint8_t v___x_4468_; 
v___x_4468_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4466_, v_options_4465_, v___x_3977_);
if (v___x_4468_ == 0)
{
lean_object* v___x_4469_; 
v___x_4469_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3577_, v___y_4464_, v___y_4467_);
return v___x_4469_;
}
else
{
lean_object* v___x_4470_; lean_object* v___x_4471_; 
v___x_4470_ = lean_obj_once(&l_Lean_addDecl___lam__3___closed__1, &l_Lean_addDecl___lam__3___closed__1_once, _init_l_Lean_addDecl___lam__3___closed__1);
v___x_4471_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3773_, v___x_4470_, v___y_4464_, v___y_4467_);
if (lean_obj_tag(v___x_4471_) == 0)
{
lean_object* v___x_4472_; 
lean_dec_ref(v___x_4471_);
v___x_4472_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3577_, v___y_4464_, v___y_4467_);
return v___x_4472_;
}
else
{
lean_dec(v_decl_3577_);
return v___x_4471_;
}
}
}
v___jp_4474_:
{
lean_object* v___x_4481_; uint8_t v___x_4482_; 
lean_inc(v_decl_3577_);
v___x_4481_ = l_Lean_Declaration_getTopLevelNames(v_decl_3577_);
v___x_4482_ = l_List_all___at___00Lean_addDecl_spec__2(v___x_4481_);
lean_dec(v___x_4481_);
if (v___x_4482_ == 0)
{
if (lean_obj_tag(v___y_4477_) == 0)
{
if (v___x_4281_ == 0)
{
lean_object* v_options_4483_; uint8_t v_hasTrace_4484_; 
v_options_4483_ = lean_ctor_get(v___y_4479_, 2);
v_hasTrace_4484_ = lean_ctor_get_uint8(v_options_4483_, sizeof(void*)*1);
if (v_hasTrace_4484_ == 0)
{
v___y_4402_ = v___y_4475_;
v___y_4403_ = v___y_4476_;
v___y_4404_ = v___y_4478_;
v___y_4405_ = v___y_4479_;
v___y_4406_ = v___y_4480_;
goto v___jp_4401_;
}
else
{
lean_object* v_inheritedTraceOptions_4485_; uint8_t v___x_4486_; 
v_inheritedTraceOptions_4485_ = lean_ctor_get(v___y_4479_, 13);
v___x_4486_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4485_, v_options_4483_, v___x_3977_);
if (v___x_4486_ == 0)
{
v___y_4402_ = v___y_4475_;
v___y_4403_ = v___y_4476_;
v___y_4404_ = v___y_4478_;
v___y_4405_ = v___y_4479_;
v___y_4406_ = v___y_4480_;
goto v___jp_4401_;
}
else
{
lean_object* v___x_4487_; lean_object* v___x_4488_; 
v___x_4487_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__1, &l_Lean_addDecl___lam__8___closed__1_once, _init_l_Lean_addDecl___lam__8___closed__1);
v___x_4488_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3773_, v___x_4487_, v___y_4479_, v___y_4480_);
if (lean_obj_tag(v___x_4488_) == 0)
{
lean_dec_ref(v___x_4488_);
v___y_4402_ = v___y_4475_;
v___y_4403_ = v___y_4476_;
v___y_4404_ = v___y_4478_;
v___y_4405_ = v___y_4479_;
v___y_4406_ = v___y_4480_;
goto v___jp_4401_;
}
else
{
lean_dec_ref(v___y_4478_);
lean_dec(v___y_4476_);
lean_dec(v_decl_3577_);
return v___x_4488_;
}
}
}
}
else
{
v___y_4432_ = v___y_4475_;
v___y_4433_ = v___y_4476_;
v___y_4434_ = v___y_4477_;
v___y_4435_ = v___y_4478_;
v___y_4436_ = v___y_4480_;
v___y_4437_ = v___y_4479_;
goto v___jp_4431_;
}
}
else
{
v___y_4432_ = v___y_4475_;
v___y_4433_ = v___y_4476_;
v___y_4434_ = v___y_4477_;
v___y_4435_ = v___y_4478_;
v___y_4436_ = v___y_4480_;
v___y_4437_ = v___y_4479_;
goto v___jp_4431_;
}
}
else
{
lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v_a_4491_; uint8_t v___x_4492_; 
lean_dec(v___y_4477_);
v___x_4489_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4490_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__3___redArg(v___x_4489_, v___y_4479_);
v_a_4491_ = lean_ctor_get(v___x_4490_, 0);
lean_inc(v_a_4491_);
lean_dec_ref(v___x_4490_);
v___x_4492_ = lean_unbox(v_a_4491_);
lean_dec(v_a_4491_);
if (v___x_4492_ == 0)
{
lean_object* v_options_4493_; uint8_t v_hasTrace_4494_; 
v_options_4493_ = lean_ctor_get(v___y_4479_, 2);
v_hasTrace_4494_ = lean_ctor_get_uint8(v_options_4493_, sizeof(void*)*1);
if (v_hasTrace_4494_ == 0)
{
v___y_4387_ = v___y_4475_;
v___y_4388_ = v___y_4476_;
v___y_4389_ = v___y_4478_;
v_exportedInfo_x3f_4390_ = v___x_4473_;
v___y_4391_ = v___y_4479_;
v___y_4392_ = v___y_4480_;
goto v___jp_4386_;
}
else
{
lean_object* v_inheritedTraceOptions_4495_; uint8_t v___x_4496_; 
v_inheritedTraceOptions_4495_ = lean_ctor_get(v___y_4479_, 13);
v___x_4496_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4495_, v_options_4493_, v___x_3977_);
if (v___x_4496_ == 0)
{
v___y_4387_ = v___y_4475_;
v___y_4388_ = v___y_4476_;
v___y_4389_ = v___y_4478_;
v_exportedInfo_x3f_4390_ = v___x_4473_;
v___y_4391_ = v___y_4479_;
v___y_4392_ = v___y_4480_;
goto v___jp_4386_;
}
else
{
lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4497_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__3, &l_Lean_addDecl___lam__8___closed__3_once, _init_l_Lean_addDecl___lam__8___closed__3);
v___x_4498_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3773_, v___x_4497_, v___y_4479_, v___y_4480_);
if (lean_obj_tag(v___x_4498_) == 0)
{
lean_dec_ref(v___x_4498_);
v___y_4387_ = v___y_4475_;
v___y_4388_ = v___y_4476_;
v___y_4389_ = v___y_4478_;
v_exportedInfo_x3f_4390_ = v___x_4473_;
v___y_4391_ = v___y_4479_;
v___y_4392_ = v___y_4480_;
goto v___jp_4386_;
}
else
{
lean_dec_ref(v___y_4478_);
lean_dec(v___y_4476_);
lean_dec(v_decl_3577_);
return v___x_4498_;
}
}
}
}
else
{
lean_object* v_options_4499_; uint8_t v_hasTrace_4500_; 
v_options_4499_ = lean_ctor_get(v___y_4479_, 2);
v_hasTrace_4500_ = lean_ctor_get_uint8(v_options_4499_, sizeof(void*)*1);
if (v_hasTrace_4500_ == 0)
{
v___y_4409_ = v___y_4475_;
v___y_4410_ = v___y_4476_;
v___y_4411_ = v___y_4478_;
v___y_4412_ = v___y_4479_;
v___y_4413_ = v___y_4480_;
goto v___jp_4408_;
}
else
{
lean_object* v_inheritedTraceOptions_4501_; uint8_t v___x_4502_; 
v_inheritedTraceOptions_4501_ = lean_ctor_get(v___y_4479_, 13);
v___x_4502_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4501_, v_options_4499_, v___x_3977_);
if (v___x_4502_ == 0)
{
v___y_4409_ = v___y_4475_;
v___y_4410_ = v___y_4476_;
v___y_4411_ = v___y_4478_;
v___y_4412_ = v___y_4479_;
v___y_4413_ = v___y_4480_;
goto v___jp_4408_;
}
else
{
lean_object* v___x_4503_; lean_object* v___x_4504_; 
v___x_4503_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__5, &l_Lean_addDecl___lam__8___closed__5_once, _init_l_Lean_addDecl___lam__8___closed__5);
v___x_4504_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3773_, v___x_4503_, v___y_4479_, v___y_4480_);
if (lean_obj_tag(v___x_4504_) == 0)
{
lean_dec_ref(v___x_4504_);
v___y_4409_ = v___y_4475_;
v___y_4410_ = v___y_4476_;
v___y_4411_ = v___y_4478_;
v___y_4412_ = v___y_4479_;
v___y_4413_ = v___y_4480_;
goto v___jp_4408_;
}
else
{
lean_dec_ref(v___y_4478_);
lean_dec(v___y_4476_);
lean_dec(v_decl_3577_);
return v___x_4504_;
}
}
}
}
}
}
v___jp_4505_:
{
lean_object* v___x_4512_; lean_object* v_env_4513_; uint8_t v___x_4514_; 
v___x_4512_ = lean_st_ref_get(v___y_4511_);
v_env_4513_ = lean_ctor_get(v___x_4512_, 0);
lean_inc_ref(v_env_4513_);
lean_dec(v___x_4512_);
v___x_4514_ = l_Lean_Environment_containsOnBranch(v_env_4513_, v_fst_4506_);
lean_dec_ref(v_env_4513_);
if (v___x_4514_ == 0)
{
v___y_4475_ = v_snd_4508_;
v___y_4476_ = v_fst_4506_;
v___y_4477_ = v_exportedInfo_x3f_4509_;
v___y_4478_ = v_fst_4507_;
v___y_4479_ = v___y_4510_;
v___y_4480_ = v___y_4511_;
goto v___jp_4474_;
}
else
{
lean_object* v___x_4515_; lean_object* v_env_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; 
lean_dec(v_exportedInfo_x3f_4509_);
lean_dec_ref(v_fst_4507_);
lean_dec(v_decl_3577_);
v___x_4515_ = lean_st_ref_get(v___y_4511_);
v_env_4516_ = lean_ctor_get(v___x_4515_, 0);
lean_inc_ref(v_env_4516_);
lean_dec(v___x_4515_);
v___x_4517_ = lean_elab_environment_to_kernel_env(v_env_4516_);
v___x_4518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4517_);
lean_ctor_set(v___x_4518_, 1, v_fst_4506_);
v___x_4519_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(v___x_4518_, v___y_4510_, v___y_4511_);
return v___x_4519_;
}
}
v___jp_4520_:
{
lean_object* v_name_4526_; lean_object* v___x_4527_; uint8_t v___x_4528_; 
v_name_4526_ = lean_ctor_get(v_toConstantVal_4522_, 0);
lean_inc(v_name_4526_);
lean_dec_ref(v_toConstantVal_4522_);
v___x_4527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4527_, 0, v___y_4521_);
v___x_4528_ = 0;
v_fst_4506_ = v_name_4526_;
v_fst_4507_ = v___x_4527_;
v_snd_4508_ = v___x_4528_;
v_exportedInfo_x3f_4509_ = v_exportedInfo_x3f_4523_;
v___y_4510_ = v___y_4524_;
v___y_4511_ = v___y_4525_;
goto v___jp_4505_;
}
v___jp_4529_:
{
uint8_t v___x_4535_; uint8_t v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; 
v___x_4535_ = 0;
v___x_4536_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4532_, v___x_4535_);
lean_inc_ref(v_toConstantVal_4531_);
v___x_4537_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4537_, 0, v_toConstantVal_4531_);
lean_ctor_set_uint8(v___x_4537_, sizeof(void*)*1, v___x_4536_);
v___x_4538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4538_, 0, v___x_4537_);
v___x_4539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4539_, 0, v___x_4538_);
v___y_4521_ = v___y_4530_;
v_toConstantVal_4522_ = v_toConstantVal_4531_;
v_exportedInfo_x3f_4523_ = v___x_4539_;
v___y_4524_ = v___y_4533_;
v___y_4525_ = v___y_4534_;
goto v___jp_4520_;
}
v___jp_4540_:
{
lean_object* v_toConstantVal_4544_; uint8_t v_safety_4545_; 
v_toConstantVal_4544_ = lean_ctor_get(v___y_4541_, 0);
lean_inc_ref(v_toConstantVal_4544_);
v_safety_4545_ = lean_ctor_get_uint8(v___y_4541_, sizeof(void*)*4);
v___y_4530_ = v___y_4541_;
v_toConstantVal_4531_ = v_toConstantVal_4544_;
v_safety_4532_ = v_safety_4545_;
v___y_4533_ = v___y_4542_;
v___y_4534_ = v___y_4543_;
goto v___jp_4529_;
}
v___jp_4546_:
{
lean_object* v_options_4550_; uint8_t v_hasTrace_4551_; 
v_options_4550_ = lean_ctor_get(v___y_4548_, 2);
v_hasTrace_4551_ = lean_ctor_get_uint8(v_options_4550_, sizeof(void*)*1);
if (v_hasTrace_4551_ == 0)
{
v___y_4541_ = v___y_4547_;
v___y_4542_ = v___y_4548_;
v___y_4543_ = v___y_4549_;
goto v___jp_4540_;
}
else
{
lean_object* v_inheritedTraceOptions_4552_; uint8_t v___x_4553_; 
v_inheritedTraceOptions_4552_ = lean_ctor_get(v___y_4548_, 13);
v___x_4553_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4552_, v_options_4550_, v___x_3977_);
if (v___x_4553_ == 0)
{
v___y_4541_ = v___y_4547_;
v___y_4542_ = v___y_4548_;
v___y_4543_ = v___y_4549_;
goto v___jp_4540_;
}
else
{
lean_object* v_toConstantVal_4554_; uint8_t v_safety_4555_; lean_object* v_name_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; 
v_toConstantVal_4554_ = lean_ctor_get(v___y_4547_, 0);
lean_inc_ref(v_toConstantVal_4554_);
v_safety_4555_ = lean_ctor_get_uint8(v___y_4547_, sizeof(void*)*4);
v_name_4556_ = lean_ctor_get(v_toConstantVal_4554_, 0);
v___x_4557_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__1, &l_Lean_addDecl___lam__4___closed__1_once, _init_l_Lean_addDecl___lam__4___closed__1);
lean_inc(v_name_4556_);
v___x_4558_ = l_Lean_MessageData_ofName(v_name_4556_);
v___x_4559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4559_, 0, v___x_4557_);
lean_ctor_set(v___x_4559_, 1, v___x_4558_);
v___x_4560_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_4561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4561_, 0, v___x_4559_);
lean_ctor_set(v___x_4561_, 1, v___x_4560_);
v___x_4562_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3773_, v___x_4561_, v___y_4548_, v___y_4549_);
if (lean_obj_tag(v___x_4562_) == 0)
{
lean_dec_ref(v___x_4562_);
v___y_4530_ = v___y_4547_;
v_toConstantVal_4531_ = v_toConstantVal_4554_;
v_safety_4532_ = v_safety_4555_;
v___y_4533_ = v___y_4548_;
v___y_4534_ = v___y_4549_;
goto v___jp_4529_;
}
else
{
lean_dec_ref(v_toConstantVal_4554_);
lean_dec_ref(v___y_4547_);
lean_dec(v_decl_3577_);
return v___x_4562_;
}
}
}
}
v___jp_4563_:
{
lean_object* v_toConstantVal_4568_; 
v_toConstantVal_4568_ = lean_ctor_get(v___y_4564_, 0);
lean_inc_ref(v_toConstantVal_4568_);
v___y_4521_ = v___y_4564_;
v_toConstantVal_4522_ = v_toConstantVal_4568_;
v_exportedInfo_x3f_4523_ = v_exportedInfo_x3f_4565_;
v___y_4524_ = v___y_4566_;
v___y_4525_ = v___y_4567_;
goto v___jp_4520_;
}
v___jp_4569_:
{
lean_object* v___x_4575_; uint8_t v_isModule_4576_; 
v___x_4575_ = l_Lean_Environment_header(v___y_4573_);
lean_dec_ref(v___y_4573_);
v_isModule_4576_ = lean_ctor_get_uint8(v___x_4575_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4575_);
if (v_isModule_4576_ == 0)
{
lean_dec_ref(v___y_4572_);
v___y_4564_ = v___y_4570_;
v_exportedInfo_x3f_4565_ = v___x_4473_;
v___y_4566_ = v___y_4571_;
v___y_4567_ = v___y_4574_;
goto v___jp_4563_;
}
else
{
uint8_t v_isExporting_4577_; 
v_isExporting_4577_ = lean_ctor_get_uint8(v___y_4572_, sizeof(void*)*8);
lean_dec_ref(v___y_4572_);
if (v_isExporting_4577_ == 0)
{
v___y_4547_ = v___y_4570_;
v___y_4548_ = v___y_4571_;
v___y_4549_ = v___y_4574_;
goto v___jp_4546_;
}
else
{
if (v___x_4281_ == 0)
{
v___y_4564_ = v___y_4570_;
v_exportedInfo_x3f_4565_ = v___x_4473_;
v___y_4566_ = v___y_4571_;
v___y_4567_ = v___y_4574_;
goto v___jp_4563_;
}
else
{
v___y_4547_ = v___y_4570_;
v___y_4548_ = v___y_4571_;
v___y_4549_ = v___y_4574_;
goto v___jp_4546_;
}
}
}
}
v___jp_4578_:
{
lean_object* v___x_4582_; lean_object* v___x_4583_; 
v___x_4582_ = lean_st_ref_get(v___y_4581_);
v___x_4583_ = lean_st_ref_get(v___y_4581_);
if (v_forceExpose_3578_ == 0)
{
lean_object* v_env_4584_; lean_object* v_env_4585_; 
v_env_4584_ = lean_ctor_get(v___x_4582_, 0);
lean_inc_ref(v_env_4584_);
lean_dec(v___x_4582_);
v_env_4585_ = lean_ctor_get(v___x_4583_, 0);
lean_inc_ref(v_env_4585_);
lean_dec(v___x_4583_);
v___y_4570_ = v_defn_4579_;
v___y_4571_ = v___y_4580_;
v___y_4572_ = v_env_4585_;
v___y_4573_ = v_env_4584_;
v___y_4574_ = v___y_4581_;
goto v___jp_4569_;
}
else
{
if (v___x_4281_ == 0)
{
lean_dec(v___x_4583_);
lean_dec(v___x_4582_);
v___y_4564_ = v_defn_4579_;
v_exportedInfo_x3f_4565_ = v___x_4473_;
v___y_4566_ = v___y_4580_;
v___y_4567_ = v___y_4581_;
goto v___jp_4563_;
}
else
{
lean_object* v_env_4586_; lean_object* v_env_4587_; 
v_env_4586_ = lean_ctor_get(v___x_4582_, 0);
lean_inc_ref(v_env_4586_);
lean_dec(v___x_4582_);
v_env_4587_ = lean_ctor_get(v___x_4583_, 0);
lean_inc_ref(v_env_4587_);
lean_dec(v___x_4583_);
v___y_4570_ = v_defn_4579_;
v___y_4571_ = v___y_4580_;
v___y_4572_ = v_env_4587_;
v___y_4573_ = v_env_4586_;
v___y_4574_ = v___y_4581_;
goto v___jp_4569_;
}
}
}
}
}
}
else
{
goto v___jp_4126_;
}
v___jp_4282_:
{
lean_object* v___x_4293_; 
lean_inc_ref(v___y_4286_);
v___x_4293_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_4285_, v___y_4286_, v___y_4289_, v___y_4292_);
if (lean_obj_tag(v___x_4293_) == 0)
{
lean_object* v___x_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4340_; 
lean_dec_ref(v___x_4293_);
lean_inc_ref(v___y_4288_);
v___x_4294_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_4288_, v___y_4290_);
v_isSharedCheck_4340_ = !lean_is_exclusive(v___x_4294_);
if (v_isSharedCheck_4340_ == 0)
{
lean_object* v_unused_4341_; 
v_unused_4341_ = lean_ctor_get(v___x_4294_, 0);
lean_dec(v_unused_4341_);
v___x_4296_ = v___x_4294_;
v_isShared_4297_ = v_isSharedCheck_4340_;
goto v_resetjp_4295_;
}
else
{
lean_dec(v___x_4294_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4340_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v_options_4298_; lean_object* v___x_4299_; uint8_t v___x_4300_; 
v_options_4298_ = lean_ctor_get(v___y_4284_, 2);
v___x_4299_ = l_Lean_Elab_async;
v___x_4300_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_4298_, v___x_4299_);
if (v___x_4300_ == 0)
{
lean_object* v___x_4301_; lean_object* v_r_4302_; 
lean_del_object(v___x_4296_);
lean_dec_ref(v___y_4291_);
lean_dec_ref(v___y_4283_);
v___x_4301_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_4286_, v___y_4290_);
lean_dec_ref(v___x_4301_);
v_r_4302_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3577_, v___y_4284_, v___y_4290_);
if (lean_obj_tag(v_r_4302_) == 0)
{
lean_object* v_a_4303_; lean_object* v___x_4305_; uint8_t v_isShared_4306_; uint8_t v_isSharedCheck_4312_; 
v_a_4303_ = lean_ctor_get(v_r_4302_, 0);
v_isSharedCheck_4312_ = !lean_is_exclusive(v_r_4302_);
if (v_isSharedCheck_4312_ == 0)
{
v___x_4305_ = v_r_4302_;
v_isShared_4306_ = v_isSharedCheck_4312_;
goto v_resetjp_4304_;
}
else
{
lean_inc(v_a_4303_);
lean_dec(v_r_4302_);
v___x_4305_ = lean_box(0);
v_isShared_4306_ = v_isSharedCheck_4312_;
goto v_resetjp_4304_;
}
v_resetjp_4304_:
{
lean_object* v___x_4308_; 
lean_inc(v_a_4303_);
if (v_isShared_4306_ == 0)
{
lean_ctor_set_tag(v___x_4305_, 1);
v___x_4308_ = v___x_4305_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v_a_4303_);
v___x_4308_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
lean_object* v___x_4309_; 
v___x_4309_ = lean_apply_2(v___y_4287_, v___x_4308_, lean_box(0));
if (lean_obj_tag(v___x_4309_) == 0)
{
lean_dec_ref(v___x_4309_);
v___y_3596_ = v___y_4288_;
v___y_3597_ = v___y_4290_;
v_a_3598_ = v_a_4303_;
goto v___jp_3595_;
}
else
{
lean_object* v_a_4310_; 
lean_dec(v_a_4303_);
v_a_4310_ = lean_ctor_get(v___x_4309_, 0);
lean_inc(v_a_4310_);
lean_dec_ref(v___x_4309_);
v___y_3583_ = v___y_4288_;
v___y_3584_ = v___y_4290_;
v_a_3585_ = v_a_4310_;
goto v___jp_3582_;
}
}
}
}
else
{
lean_object* v_a_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; 
v_a_4313_ = lean_ctor_get(v_r_4302_, 0);
lean_inc(v_a_4313_);
lean_dec_ref(v_r_4302_);
v___x_4314_ = lean_box(0);
v___x_4315_ = lean_apply_2(v___y_4287_, v___x_4314_, lean_box(0));
if (lean_obj_tag(v___x_4315_) == 0)
{
lean_dec_ref(v___x_4315_);
v___y_3583_ = v___y_4288_;
v___y_3584_ = v___y_4290_;
v_a_3585_ = v_a_4313_;
goto v___jp_3582_;
}
else
{
lean_object* v_a_4316_; 
lean_dec(v_a_4313_);
v_a_4316_ = lean_ctor_get(v___x_4315_, 0);
lean_inc(v_a_4316_);
lean_dec_ref(v___x_4315_);
v___y_3583_ = v___y_4288_;
v___y_3584_ = v___y_4290_;
v_a_3585_ = v_a_4316_;
goto v___jp_3582_;
}
}
}
else
{
lean_object* v___x_4317_; lean_object* v___x_4319_; 
lean_dec_ref(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec_ref(v___y_4286_);
lean_dec(v_decl_3577_);
v___x_4317_ = l_IO_CancelToken_new();
if (v_isShared_4297_ == 0)
{
lean_ctor_set_tag(v___x_4296_, 1);
lean_ctor_set(v___x_4296_, 0, v___x_4317_);
v___x_4319_ = v___x_4296_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4339_, 0, v___x_4317_);
v___x_4319_ = v_reuseFailAlloc_4339_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; 
v___x_4320_ = ((lean_object*)(l_Lean_addDecl___closed__0));
v___x_4321_ = l_Lean_Name_toString(v___x_4320_, v_hasTrace_3636_);
lean_inc_ref(v___x_4319_);
v___x_4322_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_4291_, v___x_4319_, v___x_4321_, v___y_4284_, v___y_4290_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_object* v_a_4323_; lean_object* v_checked_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; 
v_a_4323_ = lean_ctor_get(v___x_4322_, 0);
lean_inc(v_a_4323_);
lean_dec_ref(v___x_4322_);
v_checked_4324_ = lean_ctor_get(v___y_4283_, 2);
lean_inc_ref(v_checked_4324_);
lean_dec_ref(v___y_4283_);
v___x_4325_ = lean_unsigned_to_nat(0u);
v___x_4326_ = lean_io_map_task(v_a_4323_, v_checked_4324_, v___x_4325_, v___x_4281_);
v___x_4327_ = lean_box(0);
v___x_4328_ = lean_box(2);
v___x_4329_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4329_, 0, v___x_4327_);
lean_ctor_set(v___x_4329_, 1, v___x_4328_);
lean_ctor_set(v___x_4329_, 2, v___x_4319_);
lean_ctor_set(v___x_4329_, 3, v___x_4326_);
v___x_4330_ = l_Lean_Core_logSnapshotTask___redArg(v___x_4329_, v___y_4290_);
return v___x_4330_;
}
else
{
lean_object* v_a_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4338_; 
lean_dec_ref(v___x_4319_);
lean_dec_ref(v___y_4283_);
v_a_4331_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4333_ = v___x_4322_;
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_a_4331_);
lean_dec(v___x_4322_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v___x_4336_; 
if (v_isShared_4334_ == 0)
{
v___x_4336_ = v___x_4333_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_a_4331_);
v___x_4336_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
return v___x_4336_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4354_; 
lean_dec_ref(v___y_4291_);
lean_dec_ref(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec_ref(v___y_4286_);
lean_dec_ref(v___y_4283_);
lean_dec(v_decl_3577_);
v_a_4342_ = lean_ctor_get(v___x_4293_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4293_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4344_ = v___x_4293_;
v_isShared_4345_ = v_isSharedCheck_4354_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_a_4342_);
lean_dec(v___x_4293_);
v___x_4344_ = lean_box(0);
v_isShared_4345_ = v_isSharedCheck_4354_;
goto v_resetjp_4343_;
}
v_resetjp_4343_:
{
lean_object* v_ref_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4352_; 
v_ref_4346_ = lean_ctor_get(v___y_4284_, 5);
v___x_4347_ = lean_io_error_to_string(v_a_4342_);
v___x_4348_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4348_, 0, v___x_4347_);
v___x_4349_ = l_Lean_MessageData_ofFormat(v___x_4348_);
lean_inc(v_ref_4346_);
v___x_4350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4350_, 0, v_ref_4346_);
lean_ctor_set(v___x_4350_, 1, v___x_4349_);
if (v_isShared_4345_ == 0)
{
lean_ctor_set(v___x_4344_, 0, v___x_4350_);
v___x_4352_ = v___x_4344_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v___x_4350_);
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
v___jp_4355_:
{
lean_object* v___x_4366_; 
lean_inc_ref(v___y_4356_);
v___x_4366_ = l_Lean_Environment_addConstAsync(v___y_4356_, v___y_4361_, v___y_4360_, v___y_4365_, v___x_4281_, v_hasTrace_3636_);
if (lean_obj_tag(v___x_4366_) == 0)
{
lean_object* v_a_4367_; lean_object* v_mainEnv_4368_; lean_object* v_asyncEnv_4369_; lean_object* v___f_4370_; lean_object* v___f_4371_; lean_object* v___x_4372_; 
v_a_4367_ = lean_ctor_get(v___x_4366_, 0);
lean_inc_n(v_a_4367_, 3);
lean_dec_ref(v___x_4366_);
v_mainEnv_4368_ = lean_ctor_get(v_a_4367_, 0);
lean_inc_ref(v_mainEnv_4368_);
v_asyncEnv_4369_ = lean_ctor_get(v_a_4367_, 1);
lean_inc_ref_n(v_asyncEnv_4369_, 2);
lean_inc_ref(v___y_4357_);
lean_inc(v___y_4358_);
v___f_4370_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4370_, 0, v___y_4358_);
lean_closure_set(v___f_4370_, 1, v_a_4367_);
lean_closure_set(v___f_4370_, 2, v___y_4357_);
lean_inc(v_decl_3577_);
v___f_4371_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4371_, 0, v_asyncEnv_4369_);
lean_closure_set(v___f_4371_, 1, v_a_4367_);
lean_closure_set(v___f_4371_, 2, v_decl_3577_);
v___x_4372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4372_, 0, v___y_4363_);
if (lean_obj_tag(v___y_4359_) == 0)
{
lean_inc_ref(v___x_4372_);
v___y_4283_ = v___y_4356_;
v___y_4284_ = v___y_4362_;
v___y_4285_ = v_a_4367_;
v___y_4286_ = v_asyncEnv_4369_;
v___y_4287_ = v___f_4370_;
v___y_4288_ = v_mainEnv_4368_;
v___y_4289_ = v___x_4372_;
v___y_4290_ = v___y_4364_;
v___y_4291_ = v___f_4371_;
v___y_4292_ = v___x_4372_;
goto v___jp_4282_;
}
else
{
v___y_4283_ = v___y_4356_;
v___y_4284_ = v___y_4362_;
v___y_4285_ = v_a_4367_;
v___y_4286_ = v_asyncEnv_4369_;
v___y_4287_ = v___f_4370_;
v___y_4288_ = v_mainEnv_4368_;
v___y_4289_ = v___x_4372_;
v___y_4290_ = v___y_4364_;
v___y_4291_ = v___f_4371_;
v___y_4292_ = v___y_4359_;
goto v___jp_4282_;
}
}
else
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4385_; 
lean_dec_ref(v___y_4363_);
lean_dec(v___y_4359_);
lean_dec_ref(v___y_4356_);
lean_dec(v_decl_3577_);
v_a_4373_ = lean_ctor_get(v___x_4366_, 0);
v_isSharedCheck_4385_ = !lean_is_exclusive(v___x_4366_);
if (v_isSharedCheck_4385_ == 0)
{
v___x_4375_ = v___x_4366_;
v_isShared_4376_ = v_isSharedCheck_4385_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___x_4366_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4385_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v_ref_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4383_; 
v_ref_4377_ = lean_ctor_get(v___y_4362_, 5);
v___x_4378_ = lean_io_error_to_string(v_a_4373_);
v___x_4379_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4379_, 0, v___x_4378_);
v___x_4380_ = l_Lean_MessageData_ofFormat(v___x_4379_);
lean_inc(v_ref_4377_);
v___x_4381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4381_, 0, v_ref_4377_);
lean_ctor_set(v___x_4381_, 1, v___x_4380_);
if (v_isShared_4376_ == 0)
{
lean_ctor_set(v___x_4375_, 0, v___x_4381_);
v___x_4383_ = v___x_4375_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v___x_4381_);
v___x_4383_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
return v___x_4383_;
}
}
}
}
v___jp_4386_:
{
lean_object* v___x_4393_; 
v___x_4393_ = lean_st_ref_get(v___y_4392_);
if (lean_obj_tag(v_exportedInfo_x3f_4390_) == 0)
{
lean_object* v_env_4394_; lean_object* v___x_4395_; 
v_env_4394_ = lean_ctor_get(v___x_4393_, 0);
lean_inc_ref(v_env_4394_);
lean_dec(v___x_4393_);
v___x_4395_ = lean_box(0);
v___y_4356_ = v_env_4394_;
v___y_4357_ = v___y_4391_;
v___y_4358_ = v___y_4392_;
v___y_4359_ = v_exportedInfo_x3f_4390_;
v___y_4360_ = v___y_4387_;
v___y_4361_ = v___y_4388_;
v___y_4362_ = v___y_4391_;
v___y_4363_ = v___y_4389_;
v___y_4364_ = v___y_4392_;
v___y_4365_ = v___x_4395_;
goto v___jp_4355_;
}
else
{
lean_object* v_env_4396_; lean_object* v_val_4397_; uint8_t v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v_env_4396_ = lean_ctor_get(v___x_4393_, 0);
lean_inc_ref(v_env_4396_);
lean_dec(v___x_4393_);
v_val_4397_ = lean_ctor_get(v_exportedInfo_x3f_4390_, 0);
v___x_4398_ = l_Lean_ConstantKind_ofConstantInfo(v_val_4397_);
v___x_4399_ = lean_box(v___x_4398_);
v___x_4400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4400_, 0, v___x_4399_);
v___y_4356_ = v_env_4396_;
v___y_4357_ = v___y_4391_;
v___y_4358_ = v___y_4392_;
v___y_4359_ = v_exportedInfo_x3f_4390_;
v___y_4360_ = v___y_4387_;
v___y_4361_ = v___y_4388_;
v___y_4362_ = v___y_4391_;
v___y_4363_ = v___y_4389_;
v___y_4364_ = v___y_4392_;
v___y_4365_ = v___x_4400_;
goto v___jp_4355_;
}
}
v___jp_4401_:
{
lean_object* v___x_4407_; 
lean_inc_ref(v___y_4404_);
v___x_4407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4407_, 0, v___y_4404_);
v___y_4387_ = v___y_4402_;
v___y_4388_ = v___y_4403_;
v___y_4389_ = v___y_4404_;
v_exportedInfo_x3f_4390_ = v___x_4407_;
v___y_4391_ = v___y_4405_;
v___y_4392_ = v___y_4406_;
goto v___jp_4386_;
}
v___jp_4408_:
{
lean_object* v___x_4414_; 
lean_inc_ref(v___y_4411_);
v___x_4414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4414_, 0, v___y_4411_);
v___y_4387_ = v___y_4409_;
v___y_4388_ = v___y_4410_;
v___y_4389_ = v___y_4411_;
v_exportedInfo_x3f_4390_ = v___x_4414_;
v___y_4391_ = v___y_4412_;
v___y_4392_ = v___y_4413_;
goto v___jp_4386_;
}
}
else
{
goto v___jp_4126_;
}
v___jp_3979_:
{
lean_object* v___x_3983_; double v___x_3984_; double v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
v___x_3983_ = lean_io_get_num_heartbeats();
v___x_3984_ = lean_float_of_nat(v___y_3981_);
v___x_3985_ = lean_float_of_nat(v___x_3983_);
v___x_3986_ = lean_box_float(v___x_3984_);
v___x_3987_ = lean_box_float(v___x_3985_);
v___x_3988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3986_);
lean_ctor_set(v___x_3988_, 1, v___x_3987_);
v___x_3989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3989_, 0, v_a_3982_);
lean_ctor_set(v___x_3989_, 1, v___x_3988_);
v___x_3990_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2(v_cls_3773_, v_hasTrace_3636_, v___x_3976_, v_options_3634_, v___x_3978_, v___y_3980_, v___f_3975_, v___x_3989_, v_a_3579_, v_a_3580_);
return v___x_3990_;
}
v___jp_3991_:
{
if (lean_obj_tag(v___y_3994_) == 0)
{
lean_object* v_a_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4002_; 
v_a_3995_ = lean_ctor_get(v___y_3994_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___y_3994_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3997_ = v___y_3994_;
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_a_3995_);
lean_dec(v___y_3994_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v___x_4000_; 
if (v_isShared_3998_ == 0)
{
lean_ctor_set_tag(v___x_3997_, 1);
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
v___y_3980_ = v___y_3992_;
v___y_3981_ = v___y_3993_;
v_a_3982_ = v___x_4000_;
goto v___jp_3979_;
}
}
}
else
{
lean_object* v_a_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4010_; 
v_a_4003_ = lean_ctor_get(v___y_3994_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___y_3994_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_4005_ = v___y_3994_;
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_a_4003_);
lean_dec(v___y_3994_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v___x_4008_; 
if (v_isShared_4006_ == 0)
{
lean_ctor_set_tag(v___x_4005_, 0);
v___x_4008_ = v___x_4005_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_a_4003_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
v___y_3980_ = v___y_3992_;
v___y_3981_ = v___y_3993_;
v_a_3982_ = v___x_4008_;
goto v___jp_3979_;
}
}
}
}
v___jp_4011_:
{
lean_object* v___x_4016_; lean_object* v___x_4017_; 
v___x_4016_ = lean_box(0);
lean_inc(v_a_3580_);
lean_inc_ref(v_a_3579_);
v___x_4017_ = lean_apply_5(v___y_4014_, v___x_4016_, v___y_4013_, v_a_3579_, v_a_3580_, lean_box(0));
v___y_3992_ = v___y_4012_;
v___y_3993_ = v___y_4015_;
v___y_3994_ = v___x_4017_;
goto v___jp_3991_;
}
v___jp_4018_:
{
lean_object* v___x_4023_; lean_object* v___x_4024_; 
v___x_4023_ = lean_box(0);
lean_inc(v_a_3580_);
lean_inc_ref(v_a_3579_);
v___x_4024_ = lean_apply_5(v___y_4020_, v___x_4023_, v___y_4021_, v_a_3579_, v_a_3580_, lean_box(0));
v___y_3992_ = v___y_4019_;
v___y_3993_ = v___y_4022_;
v___y_3994_ = v___x_4024_;
goto v___jp_3991_;
}
v___jp_4025_:
{
lean_object* v___x_4029_; double v___x_4030_; double v___x_4031_; double v___x_4032_; double v___x_4033_; double v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; 
v___x_4029_ = lean_io_mono_nanos_now();
v___x_4030_ = lean_float_of_nat(v___y_4026_);
v___x_4031_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__1);
v___x_4032_ = lean_float_div(v___x_4030_, v___x_4031_);
v___x_4033_ = lean_float_of_nat(v___x_4029_);
v___x_4034_ = lean_float_div(v___x_4033_, v___x_4031_);
v___x_4035_ = lean_box_float(v___x_4032_);
v___x_4036_ = lean_box_float(v___x_4034_);
v___x_4037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4037_, 0, v___x_4035_);
lean_ctor_set(v___x_4037_, 1, v___x_4036_);
v___x_4038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4038_, 0, v_a_4028_);
lean_ctor_set(v___x_4038_, 1, v___x_4037_);
v___x_4039_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2(v_cls_3773_, v_hasTrace_3636_, v___x_3976_, v_options_3634_, v___x_3978_, v___y_4027_, v___f_3975_, v___x_4038_, v_a_3579_, v_a_3580_);
return v___x_4039_;
}
v___jp_4040_:
{
if (lean_obj_tag(v___y_4043_) == 0)
{
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4051_; 
v_a_4044_ = lean_ctor_get(v___y_4043_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___y_4043_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4046_ = v___y_4043_;
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___y_4043_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4049_; 
if (v_isShared_4047_ == 0)
{
lean_ctor_set_tag(v___x_4046_, 1);
v___x_4049_ = v___x_4046_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4044_);
v___x_4049_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
v___y_4026_ = v___y_4041_;
v___y_4027_ = v___y_4042_;
v_a_4028_ = v___x_4049_;
goto v___jp_4025_;
}
}
}
else
{
lean_object* v_a_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4059_; 
v_a_4052_ = lean_ctor_get(v___y_4043_, 0);
v_isSharedCheck_4059_ = !lean_is_exclusive(v___y_4043_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4054_ = v___y_4043_;
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_a_4052_);
lean_dec(v___y_4043_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v___x_4057_; 
if (v_isShared_4055_ == 0)
{
lean_ctor_set_tag(v___x_4054_, 0);
v___x_4057_ = v___x_4054_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_a_4052_);
v___x_4057_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
v___y_4026_ = v___y_4041_;
v___y_4027_ = v___y_4042_;
v_a_4028_ = v___x_4057_;
goto v___jp_4025_;
}
}
}
}
v___jp_4060_:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; 
v___x_4065_ = lean_box(0);
lean_inc(v_a_3580_);
lean_inc_ref(v_a_3579_);
v___x_4066_ = lean_apply_5(v___y_4062_, v___x_4065_, v___y_4064_, v_a_3579_, v_a_3580_, lean_box(0));
v___y_4041_ = v___y_4061_;
v___y_4042_ = v___y_4063_;
v___y_4043_ = v___x_4066_;
goto v___jp_4040_;
}
v___jp_4067_:
{
if (v___x_3978_ == 0)
{
lean_object* v___x_4072_; lean_object* v___x_4073_; 
lean_dec_ref(v___y_4071_);
v___x_4072_ = lean_box(0);
lean_inc(v_a_3580_);
lean_inc_ref(v_a_3579_);
v___x_4073_ = lean_apply_4(v___y_4070_, v___x_4072_, v_a_3579_, v_a_3580_, lean_box(0));
v___y_4041_ = v___y_4068_;
v___y_4042_ = v___y_4069_;
v___y_4043_ = v___x_4073_;
goto v___jp_4040_;
}
else
{
lean_object* v_toConstantVal_4074_; lean_object* v_name_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v_toConstantVal_4074_ = lean_ctor_get(v___y_4071_, 0);
lean_inc_ref(v_toConstantVal_4074_);
lean_dec_ref(v___y_4071_);
v_name_4075_ = lean_ctor_get(v_toConstantVal_4074_, 0);
lean_inc(v_name_4075_);
lean_dec_ref(v_toConstantVal_4074_);
v___x_4076_ = lean_obj_once(&l_Lean_addDecl___closed__3, &l_Lean_addDecl___closed__3_once, _init_l_Lean_addDecl___closed__3);
v___x_4077_ = l_Lean_MessageData_ofName(v_name_4075_);
v___x_4078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4078_, 0, v___x_4076_);
lean_ctor_set(v___x_4078_, 1, v___x_4077_);
v___x_4079_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_4080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4078_);
lean_ctor_set(v___x_4080_, 1, v___x_4079_);
v___x_4081_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3773_, v___x_4080_, v_a_3579_, v_a_3580_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_object* v_a_4082_; lean_object* v___x_4083_; 
v_a_4082_ = lean_ctor_get(v___x_4081_, 0);
lean_inc(v_a_4082_);
lean_dec_ref(v___x_4081_);
lean_inc(v_a_3580_);
lean_inc_ref(v_a_3579_);
v___x_4083_ = lean_apply_4(v___y_4070_, v_a_4082_, v_a_3579_, v_a_3580_, lean_box(0));
v___y_4041_ = v___y_4068_;
v___y_4042_ = v___y_4069_;
v___y_4043_ = v___x_4083_;
goto v___jp_4040_;
}
else
{
lean_dec_ref(v___y_4070_);
v___y_4041_ = v___y_4068_;
v___y_4042_ = v___y_4069_;
v___y_4043_ = v___x_4081_;
goto v___jp_4040_;
}
}
}
v___jp_4084_:
{
lean_object* v___x_4094_; uint8_t v_isModule_4095_; 
v___x_4094_ = l_Lean_Environment_header(v___y_4093_);
lean_dec_ref(v___y_4093_);
v_isModule_4095_ = lean_ctor_get_uint8(v___x_4094_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4094_);
if (v_isModule_4095_ == 0)
{
lean_dec_ref(v___y_4091_);
lean_dec_ref(v___y_4089_);
lean_dec_ref(v___y_4088_);
v___y_4061_ = v___y_4086_;
v___y_4062_ = v___y_4085_;
v___y_4063_ = v___y_4087_;
v___y_4064_ = v___y_4090_;
goto v___jp_4060_;
}
else
{
uint8_t v_isExporting_4096_; 
v_isExporting_4096_ = lean_ctor_get_uint8(v___y_4089_, sizeof(void*)*8);
lean_dec_ref(v___y_4089_);
if (v_isExporting_4096_ == 0)
{
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4085_);
v___y_4068_ = v___y_4086_;
v___y_4069_ = v___y_4087_;
v___y_4070_ = v___y_4088_;
v___y_4071_ = v___y_4091_;
goto v___jp_4067_;
}
else
{
if (v___y_4092_ == 0)
{
lean_dec_ref(v___y_4091_);
lean_dec_ref(v___y_4088_);
v___y_4061_ = v___y_4086_;
v___y_4062_ = v___y_4085_;
v___y_4063_ = v___y_4087_;
v___y_4064_ = v___y_4090_;
goto v___jp_4060_;
}
else
{
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4085_);
v___y_4068_ = v___y_4086_;
v___y_4069_ = v___y_4087_;
v___y_4070_ = v___y_4088_;
v___y_4071_ = v___y_4091_;
goto v___jp_4067_;
}
}
}
}
v___jp_4097_:
{
lean_object* v___x_4102_; lean_object* v___x_4103_; 
v___x_4102_ = lean_box(0);
lean_inc(v_a_3580_);
lean_inc_ref(v_a_3579_);
v___x_4103_ = lean_apply_5(v___y_4100_, v___x_4102_, v___y_4101_, v_a_3579_, v_a_3580_, lean_box(0));
v___y_4041_ = v___y_4098_;
v___y_4042_ = v___y_4099_;
v___y_4043_ = v___x_4103_;
goto v___jp_4040_;
}
v___jp_4104_:
{
lean_object* v___x_4112_; uint8_t v_isModule_4113_; 
v___x_4112_ = l_Lean_Environment_header(v___y_4106_);
lean_dec_ref(v___y_4106_);
v_isModule_4113_ = lean_ctor_get_uint8(v___x_4112_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4112_);
if (v_isModule_4113_ == 0)
{
lean_dec_ref(v___y_4111_);
lean_dec_ref(v___y_4109_);
v___y_4098_ = v___y_4105_;
v___y_4099_ = v___y_4108_;
v___y_4100_ = v___y_4107_;
v___y_4101_ = v___y_4110_;
goto v___jp_4097_;
}
else
{
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4107_);
if (v___x_3978_ == 0)
{
lean_object* v___x_4114_; lean_object* v___x_4115_; 
lean_dec_ref(v___y_4111_);
v___x_4114_ = lean_box(0);
lean_inc(v_a_3580_);
lean_inc_ref(v_a_3579_);
v___x_4115_ = lean_apply_4(v___y_4109_, v___x_4114_, v_a_3579_, v_a_3580_, lean_box(0));
v___y_4041_ = v___y_4105_;
v___y_4042_ = v___y_4108_;
v___y_4043_ = v___x_4115_;
goto v___jp_4040_;
}
else
{
lean_object* v_toConstantVal_4116_; lean_object* v_name_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; 
v_toConstantVal_4116_ = lean_ctor_get(v___y_4111_, 0);
lean_inc_ref(v_toConstantVal_4116_);
lean_dec_ref(v___y_4111_);
v_name_4117_ = lean_ctor_get(v_toConstantVal_4116_, 0);
lean_inc(v_name_4117_);
lean_dec_ref(v_toConstantVal_4116_);
v___x_4118_ = lean_obj_once(&l_Lean_addDecl___closed__5, &l_Lean_addDecl___closed__5_once, _init_l_Lean_addDecl___closed__5);
v___x_4119_ = l_Lean_MessageData_ofName(v_name_4117_);
v___x_4120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4120_, 0, v___x_4118_);
lean_ctor_set(v___x_4120_, 1, v___x_4119_);
v___x_4121_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_4122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4120_);
lean_ctor_set(v___x_4122_, 1, v___x_4121_);
v___x_4123_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3773_, v___x_4122_, v_a_3579_, v_a_3580_);
if (lean_obj_tag(v___x_4123_) == 0)
{
lean_object* v_a_4124_; lean_object* v___x_4125_; 
v_a_4124_ = lean_ctor_get(v___x_4123_, 0);
lean_inc(v_a_4124_);
lean_dec_ref(v___x_4123_);
lean_inc(v_a_3580_);
lean_inc_ref(v_a_3579_);
v___x_4125_ = lean_apply_4(v___y_4109_, v_a_4124_, v_a_3579_, v_a_3580_, lean_box(0));
v___y_4041_ = v___y_4105_;
v___y_4042_ = v___y_4108_;
v___y_4043_ = v___x_4125_;
goto v___jp_4040_;
}
else
{
lean_dec_ref(v___y_4109_);
v___y_4041_ = v___y_4105_;
v___y_4042_ = v___y_4108_;
v___y_4043_ = v___x_4123_;
goto v___jp_4040_;
}
}
}
}
v___jp_4126_:
{
lean_object* v___x_4127_; lean_object* v_a_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4279_; 
v___x_4127_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_a_3580_);
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4279_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_4130_ = v___x_4127_;
v_isShared_4131_ = v_isSharedCheck_4279_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_a_4128_);
lean_dec(v___x_4127_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4279_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v___x_4132_; uint8_t v___x_4133_; 
v___x_4132_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4133_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3634_, v___x_4132_);
if (v___x_4133_ == 0)
{
lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v_env_4136_; lean_object* v_nextMacroScope_4137_; lean_object* v_ngen_4138_; lean_object* v_auxDeclNGen_4139_; lean_object* v_traceState_4140_; lean_object* v_messages_4141_; lean_object* v_infoState_4142_; lean_object* v_snapshotTasks_4143_; lean_object* v_newDecls_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4192_; 
v___x_4134_ = lean_io_mono_nanos_now();
v___x_4135_ = lean_st_ref_take(v_a_3580_);
v_env_4136_ = lean_ctor_get(v___x_4135_, 0);
v_nextMacroScope_4137_ = lean_ctor_get(v___x_4135_, 1);
v_ngen_4138_ = lean_ctor_get(v___x_4135_, 2);
v_auxDeclNGen_4139_ = lean_ctor_get(v___x_4135_, 3);
v_traceState_4140_ = lean_ctor_get(v___x_4135_, 4);
v_messages_4141_ = lean_ctor_get(v___x_4135_, 6);
v_infoState_4142_ = lean_ctor_get(v___x_4135_, 7);
v_snapshotTasks_4143_ = lean_ctor_get(v___x_4135_, 8);
v_newDecls_4144_ = lean_ctor_get(v___x_4135_, 9);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4192_ == 0)
{
lean_object* v_unused_4193_; 
v_unused_4193_ = lean_ctor_get(v___x_4135_, 5);
lean_dec(v_unused_4193_);
v___x_4146_ = v___x_4135_;
v_isShared_4147_ = v_isSharedCheck_4192_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_newDecls_4144_);
lean_inc(v_snapshotTasks_4143_);
lean_inc(v_infoState_4142_);
lean_inc(v_messages_4141_);
lean_inc(v_traceState_4140_);
lean_inc(v_auxDeclNGen_4139_);
lean_inc(v_ngen_4138_);
lean_inc(v_nextMacroScope_4137_);
lean_inc(v_env_4136_);
lean_dec(v___x_4135_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4192_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4152_; 
lean_inc(v_decl_3577_);
v___x_4148_ = l_Lean_Declaration_getNames(v_decl_3577_);
v___x_4149_ = l_List_foldl___at___00Lean_addDecl_spec__1(v_env_4136_, v___x_4148_);
v___x_4150_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2);
if (v_isShared_4147_ == 0)
{
lean_ctor_set(v___x_4146_, 5, v___x_4150_);
lean_ctor_set(v___x_4146_, 0, v___x_4149_);
v___x_4152_ = v___x_4146_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v___x_4149_);
lean_ctor_set(v_reuseFailAlloc_4191_, 1, v_nextMacroScope_4137_);
lean_ctor_set(v_reuseFailAlloc_4191_, 2, v_ngen_4138_);
lean_ctor_set(v_reuseFailAlloc_4191_, 3, v_auxDeclNGen_4139_);
lean_ctor_set(v_reuseFailAlloc_4191_, 4, v_traceState_4140_);
lean_ctor_set(v_reuseFailAlloc_4191_, 5, v___x_4150_);
lean_ctor_set(v_reuseFailAlloc_4191_, 6, v_messages_4141_);
lean_ctor_set(v_reuseFailAlloc_4191_, 7, v_infoState_4142_);
lean_ctor_set(v_reuseFailAlloc_4191_, 8, v_snapshotTasks_4143_);
lean_ctor_set(v_reuseFailAlloc_4191_, 9, v_newDecls_4144_);
v___x_4152_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___f_4157_; 
v___x_4153_ = lean_st_ref_set(v_a_3580_, v___x_4152_);
v___x_4154_ = lean_box(0);
v___x_4155_ = lean_box(v_hasTrace_3636_);
v___x_4156_ = lean_box(v___x_4133_);
lean_inc(v_decl_3577_);
v___f_4157_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__8___boxed), 12, 7);
lean_closure_set(v___f_4157_, 0, v_decl_3577_);
lean_closure_set(v___f_4157_, 1, v___x_3637_);
lean_closure_set(v___f_4157_, 2, v___x_4155_);
lean_closure_set(v___f_4157_, 3, v___x_4156_);
lean_closure_set(v___f_4157_, 4, v___x_4150_);
lean_closure_set(v___f_4157_, 5, v_cls_3773_);
lean_closure_set(v___f_4157_, 6, v___x_4154_);
switch(lean_obj_tag(v_decl_3577_))
{
case 2:
{
lean_object* v_val_4158_; lean_object* v___x_4159_; lean_object* v_env_4160_; lean_object* v___f_4161_; lean_object* v___x_4162_; lean_object* v___f_4163_; 
lean_del_object(v___x_4130_);
v_val_4158_ = lean_ctor_get(v_decl_3577_, 0);
lean_inc_ref_n(v_val_4158_, 3);
lean_dec_ref(v_decl_3577_);
v___x_4159_ = lean_st_ref_get(v_a_3580_);
v_env_4160_ = lean_ctor_get(v___x_4159_, 0);
lean_inc_ref(v_env_4160_);
lean_dec(v___x_4159_);
v___f_4161_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__5___boxed), 7, 2);
lean_closure_set(v___f_4161_, 0, v_val_4158_);
lean_closure_set(v___f_4161_, 1, v___f_4157_);
v___x_4162_ = lean_box(v___x_4133_);
lean_inc_ref(v___f_4161_);
v___f_4163_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__6___boxed), 7, 3);
lean_closure_set(v___f_4163_, 0, v_val_4158_);
lean_closure_set(v___f_4163_, 1, v___x_4162_);
lean_closure_set(v___f_4163_, 2, v___f_4161_);
if (v_forceExpose_3578_ == 0)
{
v___y_4105_ = v___x_4134_;
v___y_4106_ = v_env_4160_;
v___y_4107_ = v___f_4161_;
v___y_4108_ = v_a_4128_;
v___y_4109_ = v___f_4163_;
v___y_4110_ = v___x_4154_;
v___y_4111_ = v_val_4158_;
goto v___jp_4104_;
}
else
{
if (v___x_4133_ == 0)
{
lean_dec_ref(v___f_4163_);
lean_dec_ref(v_env_4160_);
lean_dec_ref(v_val_4158_);
v___y_4098_ = v___x_4134_;
v___y_4099_ = v_a_4128_;
v___y_4100_ = v___f_4161_;
v___y_4101_ = v___x_4154_;
goto v___jp_4097_;
}
else
{
v___y_4105_ = v___x_4134_;
v___y_4106_ = v_env_4160_;
v___y_4107_ = v___f_4161_;
v___y_4108_ = v_a_4128_;
v___y_4109_ = v___f_4163_;
v___y_4110_ = v___x_4154_;
v___y_4111_ = v_val_4158_;
goto v___jp_4104_;
}
}
}
case 1:
{
lean_object* v_val_4164_; lean_object* v___x_4165_; 
lean_del_object(v___x_4130_);
v_val_4164_ = lean_ctor_get(v_decl_3577_, 0);
lean_inc_ref(v_val_4164_);
lean_dec_ref(v_decl_3577_);
v___x_4165_ = l_Lean_addDecl___lam__4(v___f_4157_, v_cls_3773_, v___x_4154_, v___x_4133_, v_forceExpose_3578_, v_val_4164_, v_a_3579_, v_a_3580_);
v___y_4041_ = v___x_4134_;
v___y_4042_ = v_a_4128_;
v___y_4043_ = v___x_4165_;
goto v___jp_4040_;
}
case 5:
{
lean_object* v_defns_4166_; 
lean_del_object(v___x_4130_);
v_defns_4166_ = lean_ctor_get(v_decl_3577_, 0);
if (lean_obj_tag(v_defns_4166_) == 1)
{
lean_object* v_tail_4167_; 
v_tail_4167_ = lean_ctor_get(v_defns_4166_, 1);
if (lean_obj_tag(v_tail_4167_) == 0)
{
lean_object* v_head_4168_; lean_object* v___x_4169_; 
lean_inc_ref(v_defns_4166_);
lean_dec_ref(v_decl_3577_);
v_head_4168_ = lean_ctor_get(v_defns_4166_, 0);
lean_inc(v_head_4168_);
lean_dec_ref(v_defns_4166_);
v___x_4169_ = l_Lean_addDecl___lam__4(v___f_4157_, v_cls_3773_, v___x_4154_, v___x_4133_, v_forceExpose_3578_, v_head_4168_, v_a_3579_, v_a_3580_);
v___y_4041_ = v___x_4134_;
v___y_4042_ = v_a_4128_;
v___y_4043_ = v___x_4169_;
goto v___jp_4040_;
}
else
{
lean_object* v___x_4170_; 
lean_dec_ref(v___f_4157_);
lean_inc_ref(v_decl_3577_);
v___x_4170_ = l_Lean_addDecl___lam__3(v_decl_3577_, v_cls_3773_, v_decl_3577_, v_a_3579_, v_a_3580_);
lean_dec_ref(v_decl_3577_);
v___y_4041_ = v___x_4134_;
v___y_4042_ = v_a_4128_;
v___y_4043_ = v___x_4170_;
goto v___jp_4040_;
}
}
else
{
lean_object* v___x_4171_; 
lean_dec_ref(v___f_4157_);
lean_inc_ref(v_decl_3577_);
v___x_4171_ = l_Lean_addDecl___lam__3(v_decl_3577_, v_cls_3773_, v_decl_3577_, v_a_3579_, v_a_3580_);
lean_dec_ref(v_decl_3577_);
v___y_4041_ = v___x_4134_;
v___y_4042_ = v_a_4128_;
v___y_4043_ = v___x_4171_;
goto v___jp_4040_;
}
}
case 3:
{
lean_object* v_val_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v_env_4175_; lean_object* v_env_4176_; lean_object* v___f_4177_; lean_object* v___f_4178_; 
lean_del_object(v___x_4130_);
v_val_4172_ = lean_ctor_get(v_decl_3577_, 0);
lean_inc_ref_n(v_val_4172_, 3);
lean_dec_ref(v_decl_3577_);
v___x_4173_ = lean_st_ref_get(v_a_3580_);
v___x_4174_ = lean_st_ref_get(v_a_3580_);
v_env_4175_ = lean_ctor_get(v___x_4173_, 0);
lean_inc_ref(v_env_4175_);
lean_dec(v___x_4173_);
v_env_4176_ = lean_ctor_get(v___x_4174_, 0);
lean_inc_ref(v_env_4176_);
lean_dec(v___x_4174_);
v___f_4177_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__7___boxed), 7, 2);
lean_closure_set(v___f_4177_, 0, v_val_4172_);
lean_closure_set(v___f_4177_, 1, v___f_4157_);
lean_inc_ref(v___f_4177_);
v___f_4178_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__9___boxed), 6, 2);
lean_closure_set(v___f_4178_, 0, v_val_4172_);
lean_closure_set(v___f_4178_, 1, v___f_4177_);
if (v_forceExpose_3578_ == 0)
{
v___y_4085_ = v___f_4177_;
v___y_4086_ = v___x_4134_;
v___y_4087_ = v_a_4128_;
v___y_4088_ = v___f_4178_;
v___y_4089_ = v_env_4176_;
v___y_4090_ = v___x_4154_;
v___y_4091_ = v_val_4172_;
v___y_4092_ = v___x_4133_;
v___y_4093_ = v_env_4175_;
goto v___jp_4084_;
}
else
{
if (v___x_4133_ == 0)
{
lean_dec_ref(v___f_4178_);
lean_dec_ref(v_env_4176_);
lean_dec_ref(v_env_4175_);
lean_dec_ref(v_val_4172_);
v___y_4061_ = v___x_4134_;
v___y_4062_ = v___f_4177_;
v___y_4063_ = v_a_4128_;
v___y_4064_ = v___x_4154_;
goto v___jp_4060_;
}
else
{
v___y_4085_ = v___f_4177_;
v___y_4086_ = v___x_4134_;
v___y_4087_ = v_a_4128_;
v___y_4088_ = v___f_4178_;
v___y_4089_ = v_env_4176_;
v___y_4090_ = v___x_4154_;
v___y_4091_ = v_val_4172_;
v___y_4092_ = v___x_4133_;
v___y_4093_ = v_env_4175_;
goto v___jp_4084_;
}
}
}
case 0:
{
lean_object* v_val_4179_; lean_object* v_toConstantVal_4180_; lean_object* v_name_4181_; lean_object* v___x_4183_; 
lean_dec_ref(v___f_4157_);
v_val_4179_ = lean_ctor_get(v_decl_3577_, 0);
v_toConstantVal_4180_ = lean_ctor_get(v_val_4179_, 0);
v_name_4181_ = lean_ctor_get(v_toConstantVal_4180_, 0);
lean_inc_ref(v_val_4179_);
if (v_isShared_4131_ == 0)
{
lean_ctor_set(v___x_4130_, 0, v_val_4179_);
v___x_4183_ = v___x_4130_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_val_4179_);
v___x_4183_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
uint8_t v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4184_ = 2;
v___x_4185_ = lean_box(v___x_4184_);
v___x_4186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4186_, 0, v___x_4183_);
lean_ctor_set(v___x_4186_, 1, v___x_4185_);
lean_inc(v_name_4181_);
v___x_4187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4187_, 0, v_name_4181_);
lean_ctor_set(v___x_4187_, 1, v___x_4186_);
v___x_4188_ = l_Lean_addDecl___lam__8(v_decl_3577_, v___x_3637_, v_hasTrace_3636_, v___x_4133_, v___x_4150_, v_cls_3773_, v___x_4154_, v___x_4187_, v___x_4154_, v_a_3579_, v_a_3580_);
v___y_4041_ = v___x_4134_;
v___y_4042_ = v_a_4128_;
v___y_4043_ = v___x_4188_;
goto v___jp_4040_;
}
}
default: 
{
lean_object* v___x_4190_; 
lean_dec_ref(v___f_4157_);
lean_del_object(v___x_4130_);
lean_inc(v_decl_3577_);
v___x_4190_ = l_Lean_addDecl___lam__3(v_decl_3577_, v_cls_3773_, v_decl_3577_, v_a_3579_, v_a_3580_);
lean_dec(v_decl_3577_);
v___y_4041_ = v___x_4134_;
v___y_4042_ = v_a_4128_;
v___y_4043_ = v___x_4190_;
goto v___jp_4040_;
}
}
}
}
}
else
{
lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v_env_4196_; lean_object* v_nextMacroScope_4197_; lean_object* v_ngen_4198_; lean_object* v_auxDeclNGen_4199_; lean_object* v_traceState_4200_; lean_object* v_messages_4201_; lean_object* v_infoState_4202_; lean_object* v_snapshotTasks_4203_; lean_object* v_newDecls_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4277_; 
v___x_4194_ = lean_io_get_num_heartbeats();
v___x_4195_ = lean_st_ref_take(v_a_3580_);
v_env_4196_ = lean_ctor_get(v___x_4195_, 0);
v_nextMacroScope_4197_ = lean_ctor_get(v___x_4195_, 1);
v_ngen_4198_ = lean_ctor_get(v___x_4195_, 2);
v_auxDeclNGen_4199_ = lean_ctor_get(v___x_4195_, 3);
v_traceState_4200_ = lean_ctor_get(v___x_4195_, 4);
v_messages_4201_ = lean_ctor_get(v___x_4195_, 6);
v_infoState_4202_ = lean_ctor_get(v___x_4195_, 7);
v_snapshotTasks_4203_ = lean_ctor_get(v___x_4195_, 8);
v_newDecls_4204_ = lean_ctor_get(v___x_4195_, 9);
v_isSharedCheck_4277_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4277_ == 0)
{
lean_object* v_unused_4278_; 
v_unused_4278_ = lean_ctor_get(v___x_4195_, 5);
lean_dec(v_unused_4278_);
v___x_4206_ = v___x_4195_;
v_isShared_4207_ = v_isSharedCheck_4277_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_newDecls_4204_);
lean_inc(v_snapshotTasks_4203_);
lean_inc(v_infoState_4202_);
lean_inc(v_messages_4201_);
lean_inc(v_traceState_4200_);
lean_inc(v_auxDeclNGen_4199_);
lean_inc(v_ngen_4198_);
lean_inc(v_nextMacroScope_4197_);
lean_inc(v_env_4196_);
lean_dec(v___x_4195_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4277_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4212_; 
lean_inc(v_decl_3577_);
v___x_4208_ = l_Lean_Declaration_getNames(v_decl_3577_);
v___x_4209_ = l_List_foldl___at___00Lean_addDecl_spec__1(v_env_4196_, v___x_4208_);
v___x_4210_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2);
if (v_isShared_4207_ == 0)
{
lean_ctor_set(v___x_4206_, 5, v___x_4210_);
lean_ctor_set(v___x_4206_, 0, v___x_4209_);
v___x_4212_ = v___x_4206_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v___x_4209_);
lean_ctor_set(v_reuseFailAlloc_4276_, 1, v_nextMacroScope_4197_);
lean_ctor_set(v_reuseFailAlloc_4276_, 2, v_ngen_4198_);
lean_ctor_set(v_reuseFailAlloc_4276_, 3, v_auxDeclNGen_4199_);
lean_ctor_set(v_reuseFailAlloc_4276_, 4, v_traceState_4200_);
lean_ctor_set(v_reuseFailAlloc_4276_, 5, v___x_4210_);
lean_ctor_set(v_reuseFailAlloc_4276_, 6, v_messages_4201_);
lean_ctor_set(v_reuseFailAlloc_4276_, 7, v_infoState_4202_);
lean_ctor_set(v_reuseFailAlloc_4276_, 8, v_snapshotTasks_4203_);
lean_ctor_set(v_reuseFailAlloc_4276_, 9, v_newDecls_4204_);
v___x_4212_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___f_4216_; 
v___x_4213_ = lean_st_ref_set(v_a_3580_, v___x_4212_);
v___x_4214_ = lean_box(0);
v___x_4215_ = lean_box(v___x_4133_);
lean_inc(v_decl_3577_);
v___f_4216_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__13___boxed), 11, 6);
lean_closure_set(v___f_4216_, 0, v_decl_3577_);
lean_closure_set(v___f_4216_, 1, v___x_3637_);
lean_closure_set(v___f_4216_, 2, v___x_4215_);
lean_closure_set(v___f_4216_, 3, v_cls_3773_);
lean_closure_set(v___f_4216_, 4, v___x_4210_);
lean_closure_set(v___f_4216_, 5, v___x_4214_);
switch(lean_obj_tag(v_decl_3577_))
{
case 2:
{
lean_object* v_val_4217_; lean_object* v___x_4218_; lean_object* v_env_4219_; lean_object* v___f_4220_; 
lean_del_object(v___x_4130_);
v_val_4217_ = lean_ctor_get(v_decl_3577_, 0);
lean_inc_ref_n(v_val_4217_, 2);
lean_dec_ref(v_decl_3577_);
v___x_4218_ = lean_st_ref_get(v_a_3580_);
v_env_4219_ = lean_ctor_get(v___x_4218_, 0);
lean_inc_ref(v_env_4219_);
lean_dec(v___x_4218_);
v___f_4220_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__5___boxed), 7, 2);
lean_closure_set(v___f_4220_, 0, v_val_4217_);
lean_closure_set(v___f_4220_, 1, v___f_4216_);
if (v_forceExpose_3578_ == 0)
{
if (v___x_4133_ == 0)
{
lean_dec_ref(v_env_4219_);
lean_dec_ref(v_val_4217_);
v___y_4012_ = v_a_4128_;
v___y_4013_ = v___x_4214_;
v___y_4014_ = v___f_4220_;
v___y_4015_ = v___x_4194_;
goto v___jp_4011_;
}
else
{
lean_object* v___x_4221_; uint8_t v_isModule_4222_; 
v___x_4221_ = l_Lean_Environment_header(v_env_4219_);
lean_dec_ref(v_env_4219_);
v_isModule_4222_ = lean_ctor_get_uint8(v___x_4221_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4221_);
if (v_isModule_4222_ == 0)
{
lean_dec_ref(v_val_4217_);
v___y_4012_ = v_a_4128_;
v___y_4013_ = v___x_4214_;
v___y_4014_ = v___f_4220_;
v___y_4015_ = v___x_4194_;
goto v___jp_4011_;
}
else
{
if (v___x_3978_ == 0)
{
lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4223_ = lean_box(0);
v___x_4224_ = l_Lean_addDecl___lam__12(v_val_4217_, v_forceExpose_3578_, v___f_4220_, v___x_4223_, v_a_3579_, v_a_3580_);
lean_dec_ref(v_val_4217_);
v___y_3992_ = v_a_4128_;
v___y_3993_ = v___x_4194_;
v___y_3994_ = v___x_4224_;
goto v___jp_3991_;
}
else
{
lean_object* v_toConstantVal_4225_; lean_object* v_name_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; 
v_toConstantVal_4225_ = lean_ctor_get(v_val_4217_, 0);
v_name_4226_ = lean_ctor_get(v_toConstantVal_4225_, 0);
v___x_4227_ = lean_obj_once(&l_Lean_addDecl___closed__5, &l_Lean_addDecl___closed__5_once, _init_l_Lean_addDecl___closed__5);
lean_inc(v_name_4226_);
v___x_4228_ = l_Lean_MessageData_ofName(v_name_4226_);
v___x_4229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4229_, 0, v___x_4227_);
lean_ctor_set(v___x_4229_, 1, v___x_4228_);
v___x_4230_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_4231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4231_, 0, v___x_4229_);
lean_ctor_set(v___x_4231_, 1, v___x_4230_);
v___x_4232_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3773_, v___x_4231_, v_a_3579_, v_a_3580_);
if (lean_obj_tag(v___x_4232_) == 0)
{
lean_object* v_a_4233_; lean_object* v___x_4234_; 
v_a_4233_ = lean_ctor_get(v___x_4232_, 0);
lean_inc(v_a_4233_);
lean_dec_ref(v___x_4232_);
v___x_4234_ = l_Lean_addDecl___lam__12(v_val_4217_, v_forceExpose_3578_, v___f_4220_, v_a_4233_, v_a_3579_, v_a_3580_);
lean_dec_ref(v_val_4217_);
v___y_3992_ = v_a_4128_;
v___y_3993_ = v___x_4194_;
v___y_3994_ = v___x_4234_;
goto v___jp_3991_;
}
else
{
lean_dec_ref(v___f_4220_);
lean_dec_ref(v_val_4217_);
v___y_3992_ = v_a_4128_;
v___y_3993_ = v___x_4194_;
v___y_3994_ = v___x_4232_;
goto v___jp_3991_;
}
}
}
}
}
else
{
lean_dec_ref(v_env_4219_);
lean_dec_ref(v_val_4217_);
v___y_4012_ = v_a_4128_;
v___y_4013_ = v___x_4214_;
v___y_4014_ = v___f_4220_;
v___y_4015_ = v___x_4194_;
goto v___jp_4011_;
}
}
case 1:
{
lean_object* v_val_4235_; lean_object* v___x_4236_; 
lean_del_object(v___x_4130_);
v_val_4235_ = lean_ctor_get(v_decl_3577_, 0);
lean_inc_ref(v_val_4235_);
lean_dec_ref(v_decl_3577_);
v___x_4236_ = l_Lean_addDecl___lam__10(v___f_4216_, v_forceExpose_3578_, v___x_4133_, v___x_4214_, v_cls_3773_, v_val_4235_, v_a_3579_, v_a_3580_);
v___y_3992_ = v_a_4128_;
v___y_3993_ = v___x_4194_;
v___y_3994_ = v___x_4236_;
goto v___jp_3991_;
}
case 5:
{
lean_object* v_defns_4237_; 
lean_del_object(v___x_4130_);
v_defns_4237_ = lean_ctor_get(v_decl_3577_, 0);
if (lean_obj_tag(v_defns_4237_) == 1)
{
lean_object* v_tail_4238_; 
v_tail_4238_ = lean_ctor_get(v_defns_4237_, 1);
if (lean_obj_tag(v_tail_4238_) == 0)
{
lean_object* v_head_4239_; lean_object* v___x_4240_; 
lean_inc_ref(v_defns_4237_);
lean_dec_ref(v_decl_3577_);
v_head_4239_ = lean_ctor_get(v_defns_4237_, 0);
lean_inc(v_head_4239_);
lean_dec_ref(v_defns_4237_);
v___x_4240_ = l_Lean_addDecl___lam__10(v___f_4216_, v_forceExpose_3578_, v___x_4133_, v___x_4214_, v_cls_3773_, v_head_4239_, v_a_3579_, v_a_3580_);
v___y_3992_ = v_a_4128_;
v___y_3993_ = v___x_4194_;
v___y_3994_ = v___x_4240_;
goto v___jp_3991_;
}
else
{
lean_object* v___x_4241_; 
lean_dec_ref(v___f_4216_);
lean_inc_ref(v_decl_3577_);
v___x_4241_ = l_Lean_addDecl___lam__3(v_decl_3577_, v_cls_3773_, v_decl_3577_, v_a_3579_, v_a_3580_);
lean_dec_ref(v_decl_3577_);
v___y_3992_ = v_a_4128_;
v___y_3993_ = v___x_4194_;
v___y_3994_ = v___x_4241_;
goto v___jp_3991_;
}
}
else
{
lean_object* v___x_4242_; 
lean_dec_ref(v___f_4216_);
lean_inc_ref(v_decl_3577_);
v___x_4242_ = l_Lean_addDecl___lam__3(v_decl_3577_, v_cls_3773_, v_decl_3577_, v_a_3579_, v_a_3580_);
lean_dec_ref(v_decl_3577_);
v___y_3992_ = v_a_4128_;
v___y_3993_ = v___x_4194_;
v___y_3994_ = v___x_4242_;
goto v___jp_3991_;
}
}
case 3:
{
lean_object* v_val_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v_env_4246_; lean_object* v_env_4247_; lean_object* v___f_4248_; 
lean_del_object(v___x_4130_);
v_val_4243_ = lean_ctor_get(v_decl_3577_, 0);
lean_inc_ref_n(v_val_4243_, 2);
lean_dec_ref(v_decl_3577_);
v___x_4244_ = lean_st_ref_get(v_a_3580_);
v___x_4245_ = lean_st_ref_get(v_a_3580_);
v_env_4246_ = lean_ctor_get(v___x_4244_, 0);
lean_inc_ref(v_env_4246_);
lean_dec(v___x_4244_);
v_env_4247_ = lean_ctor_get(v___x_4245_, 0);
lean_inc_ref(v_env_4247_);
lean_dec(v___x_4245_);
v___f_4248_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__7___boxed), 7, 2);
lean_closure_set(v___f_4248_, 0, v_val_4243_);
lean_closure_set(v___f_4248_, 1, v___f_4216_);
if (v_forceExpose_3578_ == 0)
{
if (v___x_4133_ == 0)
{
lean_dec_ref(v_env_4247_);
lean_dec_ref(v_env_4246_);
lean_dec_ref(v_val_4243_);
v___y_4019_ = v_a_4128_;
v___y_4020_ = v___f_4248_;
v___y_4021_ = v___x_4214_;
v___y_4022_ = v___x_4194_;
goto v___jp_4018_;
}
else
{
lean_object* v___x_4249_; uint8_t v_isModule_4250_; 
v___x_4249_ = l_Lean_Environment_header(v_env_4246_);
lean_dec_ref(v_env_4246_);
v_isModule_4250_ = lean_ctor_get_uint8(v___x_4249_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4249_);
if (v_isModule_4250_ == 0)
{
lean_dec_ref(v_env_4247_);
lean_dec_ref(v_val_4243_);
v___y_4019_ = v_a_4128_;
v___y_4020_ = v___f_4248_;
v___y_4021_ = v___x_4214_;
v___y_4022_ = v___x_4194_;
goto v___jp_4018_;
}
else
{
uint8_t v_isExporting_4251_; 
v_isExporting_4251_ = lean_ctor_get_uint8(v_env_4247_, sizeof(void*)*8);
lean_dec_ref(v_env_4247_);
if (v_isExporting_4251_ == 0)
{
if (v___x_3978_ == 0)
{
lean_object* v___x_4252_; lean_object* v___x_4253_; 
v___x_4252_ = lean_box(0);
v___x_4253_ = l_Lean_addDecl___lam__9(v_val_4243_, v___f_4248_, v___x_4252_, v_a_3579_, v_a_3580_);
lean_dec_ref(v_val_4243_);
v___y_3992_ = v_a_4128_;
v___y_3993_ = v___x_4194_;
v___y_3994_ = v___x_4253_;
goto v___jp_3991_;
}
else
{
lean_object* v_toConstantVal_4254_; lean_object* v_name_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; 
v_toConstantVal_4254_ = lean_ctor_get(v_val_4243_, 0);
v_name_4255_ = lean_ctor_get(v_toConstantVal_4254_, 0);
v___x_4256_ = lean_obj_once(&l_Lean_addDecl___closed__3, &l_Lean_addDecl___closed__3_once, _init_l_Lean_addDecl___closed__3);
lean_inc(v_name_4255_);
v___x_4257_ = l_Lean_MessageData_ofName(v_name_4255_);
v___x_4258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4258_, 0, v___x_4256_);
lean_ctor_set(v___x_4258_, 1, v___x_4257_);
v___x_4259_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_4260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4260_, 0, v___x_4258_);
lean_ctor_set(v___x_4260_, 1, v___x_4259_);
v___x_4261_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3773_, v___x_4260_, v_a_3579_, v_a_3580_);
if (lean_obj_tag(v___x_4261_) == 0)
{
lean_object* v_a_4262_; lean_object* v___x_4263_; 
v_a_4262_ = lean_ctor_get(v___x_4261_, 0);
lean_inc(v_a_4262_);
lean_dec_ref(v___x_4261_);
v___x_4263_ = l_Lean_addDecl___lam__9(v_val_4243_, v___f_4248_, v_a_4262_, v_a_3579_, v_a_3580_);
lean_dec_ref(v_val_4243_);
v___y_3992_ = v_a_4128_;
v___y_3993_ = v___x_4194_;
v___y_3994_ = v___x_4263_;
goto v___jp_3991_;
}
else
{
lean_dec_ref(v___f_4248_);
lean_dec_ref(v_val_4243_);
v___y_3992_ = v_a_4128_;
v___y_3993_ = v___x_4194_;
v___y_3994_ = v___x_4261_;
goto v___jp_3991_;
}
}
}
else
{
lean_dec_ref(v_val_4243_);
v___y_4019_ = v_a_4128_;
v___y_4020_ = v___f_4248_;
v___y_4021_ = v___x_4214_;
v___y_4022_ = v___x_4194_;
goto v___jp_4018_;
}
}
}
}
else
{
lean_dec_ref(v_env_4247_);
lean_dec_ref(v_env_4246_);
lean_dec_ref(v_val_4243_);
v___y_4019_ = v_a_4128_;
v___y_4020_ = v___f_4248_;
v___y_4021_ = v___x_4214_;
v___y_4022_ = v___x_4194_;
goto v___jp_4018_;
}
}
case 0:
{
lean_object* v_val_4264_; lean_object* v_toConstantVal_4265_; lean_object* v_name_4266_; lean_object* v___x_4268_; 
lean_dec_ref(v___f_4216_);
v_val_4264_ = lean_ctor_get(v_decl_3577_, 0);
v_toConstantVal_4265_ = lean_ctor_get(v_val_4264_, 0);
v_name_4266_ = lean_ctor_get(v_toConstantVal_4265_, 0);
lean_inc_ref(v_val_4264_);
if (v_isShared_4131_ == 0)
{
lean_ctor_set(v___x_4130_, 0, v_val_4264_);
v___x_4268_ = v___x_4130_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v_val_4264_);
v___x_4268_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
uint8_t v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; 
v___x_4269_ = 2;
v___x_4270_ = lean_box(v___x_4269_);
v___x_4271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4271_, 0, v___x_4268_);
lean_ctor_set(v___x_4271_, 1, v___x_4270_);
lean_inc(v_name_4266_);
v___x_4272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4272_, 0, v_name_4266_);
lean_ctor_set(v___x_4272_, 1, v___x_4271_);
v___x_4273_ = l_Lean_addDecl___lam__13(v_decl_3577_, v___x_3637_, v___x_4133_, v_cls_3773_, v___x_4210_, v___x_4214_, v___x_4272_, v___x_4214_, v_a_3579_, v_a_3580_);
v___y_3992_ = v_a_4128_;
v___y_3993_ = v___x_4194_;
v___y_3994_ = v___x_4273_;
goto v___jp_3991_;
}
}
default: 
{
lean_object* v___x_4275_; 
lean_dec_ref(v___f_4216_);
lean_del_object(v___x_4130_);
lean_inc(v_decl_3577_);
v___x_4275_ = l_Lean_addDecl___lam__3(v_decl_3577_, v_cls_3773_, v_decl_3577_, v_a_3579_, v_a_3580_);
lean_dec(v_decl_3577_);
v___y_3992_ = v_a_4128_;
v___y_3993_ = v___x_4194_;
v___y_3994_ = v___x_4275_;
goto v___jp_3991_;
}
}
}
}
}
}
}
}
v___jp_3582_:
{
lean_object* v___x_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3593_; 
v___x_3586_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3583_, v___y_3584_);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3586_);
if (v_isSharedCheck_3593_ == 0)
{
lean_object* v_unused_3594_; 
v_unused_3594_ = lean_ctor_get(v___x_3586_, 0);
lean_dec(v_unused_3594_);
v___x_3588_ = v___x_3586_;
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
else
{
lean_dec(v___x_3586_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3591_; 
if (v_isShared_3589_ == 0)
{
lean_ctor_set_tag(v___x_3588_, 1);
lean_ctor_set(v___x_3588_, 0, v_a_3585_);
v___x_3591_ = v___x_3588_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_a_3585_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
v___jp_3595_:
{
lean_object* v___x_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3606_; 
v___x_3599_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3596_, v___y_3597_);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3606_ == 0)
{
lean_object* v_unused_3607_; 
v_unused_3607_ = lean_ctor_get(v___x_3599_, 0);
lean_dec(v_unused_3607_);
v___x_3601_ = v___x_3599_;
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
else
{
lean_dec(v___x_3599_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3604_; 
if (v_isShared_3602_ == 0)
{
lean_ctor_set(v___x_3601_, 0, v_a_3598_);
v___x_3604_ = v___x_3601_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3598_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
v___jp_3608_:
{
lean_object* v___x_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
v___x_3612_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3609_, v___y_3610_);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3619_ == 0)
{
lean_object* v_unused_3620_; 
v_unused_3620_ = lean_ctor_get(v___x_3612_, 0);
lean_dec(v_unused_3620_);
v___x_3614_ = v___x_3612_;
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
else
{
lean_dec(v___x_3612_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3617_; 
if (v_isShared_3615_ == 0)
{
lean_ctor_set(v___x_3614_, 0, v_a_3611_);
v___x_3617_ = v___x_3614_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3611_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
v___jp_3621_:
{
lean_object* v___x_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3632_; 
v___x_3625_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3622_, v___y_3623_);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3632_ == 0)
{
lean_object* v_unused_3633_; 
v_unused_3633_ = lean_ctor_get(v___x_3625_, 0);
lean_dec(v_unused_3633_);
v___x_3627_ = v___x_3625_;
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
else
{
lean_dec(v___x_3625_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3630_; 
if (v_isShared_3628_ == 0)
{
lean_ctor_set_tag(v___x_3627_, 1);
lean_ctor_set(v___x_3627_, 0, v_a_3624_);
v___x_3630_ = v___x_3627_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_a_3624_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
v___jp_3638_:
{
lean_object* v___x_3650_; 
lean_inc_ref(v___y_3643_);
v___x_3650_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3645_, v___y_3643_, v___y_3648_, v___y_3649_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v___x_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3697_; 
lean_dec_ref(v___x_3650_);
lean_inc_ref(v___y_3641_);
v___x_3651_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3641_, v___y_3646_);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3697_ == 0)
{
lean_object* v_unused_3698_; 
v_unused_3698_ = lean_ctor_get(v___x_3651_, 0);
lean_dec(v_unused_3698_);
v___x_3653_ = v___x_3651_;
v_isShared_3654_ = v_isSharedCheck_3697_;
goto v_resetjp_3652_;
}
else
{
lean_dec(v___x_3651_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3697_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v_options_3655_; lean_object* v___x_3656_; uint8_t v___x_3657_; 
v_options_3655_ = lean_ctor_get(v___y_3644_, 2);
v___x_3656_ = l_Lean_Elab_async;
v___x_3657_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3655_, v___x_3656_);
if (v___x_3657_ == 0)
{
lean_object* v___x_3658_; lean_object* v_r_3659_; 
lean_del_object(v___x_3653_);
lean_dec_ref(v___y_3642_);
lean_dec_ref(v___y_3640_);
v___x_3658_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3643_, v___y_3646_);
lean_dec_ref(v___x_3658_);
v_r_3659_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3577_, v___y_3644_, v___y_3646_);
if (lean_obj_tag(v_r_3659_) == 0)
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3669_; 
v_a_3660_ = lean_ctor_get(v_r_3659_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v_r_3659_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3662_ = v_r_3659_;
v_isShared_3663_ = v_isSharedCheck_3669_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v_r_3659_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3669_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3665_; 
lean_inc(v_a_3660_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set_tag(v___x_3662_, 1);
v___x_3665_ = v___x_3662_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_a_3660_);
v___x_3665_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
lean_object* v___x_3666_; 
v___x_3666_ = lean_apply_2(v___y_3639_, v___x_3665_, lean_box(0));
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_dec_ref(v___x_3666_);
v___y_3609_ = v___y_3641_;
v___y_3610_ = v___y_3646_;
v_a_3611_ = v_a_3660_;
goto v___jp_3608_;
}
else
{
lean_object* v_a_3667_; 
lean_dec(v_a_3660_);
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
lean_inc(v_a_3667_);
lean_dec_ref(v___x_3666_);
v___y_3622_ = v___y_3641_;
v___y_3623_ = v___y_3646_;
v_a_3624_ = v_a_3667_;
goto v___jp_3621_;
}
}
}
}
else
{
lean_object* v_a_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
v_a_3670_ = lean_ctor_get(v_r_3659_, 0);
lean_inc(v_a_3670_);
lean_dec_ref(v_r_3659_);
v___x_3671_ = lean_box(0);
v___x_3672_ = lean_apply_2(v___y_3639_, v___x_3671_, lean_box(0));
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_dec_ref(v___x_3672_);
v___y_3622_ = v___y_3641_;
v___y_3623_ = v___y_3646_;
v_a_3624_ = v_a_3670_;
goto v___jp_3621_;
}
else
{
lean_object* v_a_3673_; 
lean_dec(v_a_3670_);
v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
lean_inc(v_a_3673_);
lean_dec_ref(v___x_3672_);
v___y_3622_ = v___y_3641_;
v___y_3623_ = v___y_3646_;
v_a_3624_ = v_a_3673_;
goto v___jp_3621_;
}
}
}
else
{
lean_object* v___x_3674_; lean_object* v___x_3676_; 
lean_dec_ref(v___y_3643_);
lean_dec_ref(v___y_3641_);
lean_dec_ref(v___y_3639_);
lean_dec(v_decl_3577_);
v___x_3674_ = l_IO_CancelToken_new();
if (v_isShared_3654_ == 0)
{
lean_ctor_set_tag(v___x_3653_, 1);
lean_ctor_set(v___x_3653_, 0, v___x_3674_);
v___x_3676_ = v___x_3653_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v___x_3674_);
v___x_3676_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3677_ = ((lean_object*)(l_Lean_addDecl___closed__0));
v___x_3678_ = l_Lean_Name_toString(v___x_3677_, v___y_3647_);
lean_inc_ref(v___x_3676_);
v___x_3679_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3642_, v___x_3676_, v___x_3678_, v___y_3644_, v___y_3646_);
if (lean_obj_tag(v___x_3679_) == 0)
{
lean_object* v_a_3680_; lean_object* v_checked_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v_a_3680_ = lean_ctor_get(v___x_3679_, 0);
lean_inc(v_a_3680_);
lean_dec_ref(v___x_3679_);
v_checked_3681_ = lean_ctor_get(v___y_3640_, 2);
lean_inc_ref(v_checked_3681_);
lean_dec_ref(v___y_3640_);
v___x_3682_ = lean_unsigned_to_nat(0u);
v___x_3683_ = lean_io_map_task(v_a_3680_, v_checked_3681_, v___x_3682_, v_hasTrace_3636_);
v___x_3684_ = lean_box(0);
v___x_3685_ = lean_box(2);
v___x_3686_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3684_);
lean_ctor_set(v___x_3686_, 1, v___x_3685_);
lean_ctor_set(v___x_3686_, 2, v___x_3676_);
lean_ctor_set(v___x_3686_, 3, v___x_3683_);
v___x_3687_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3686_, v___y_3646_);
return v___x_3687_;
}
else
{
lean_object* v_a_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3695_; 
lean_dec_ref(v___x_3676_);
lean_dec_ref(v___y_3640_);
v_a_3688_ = lean_ctor_get(v___x_3679_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3690_ = v___x_3679_;
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_a_3688_);
lean_dec(v___x_3679_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3693_; 
if (v_isShared_3691_ == 0)
{
v___x_3693_ = v___x_3690_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_a_3688_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3711_; 
lean_dec_ref(v___y_3643_);
lean_dec_ref(v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec_ref(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v_decl_3577_);
v_a_3699_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3701_ = v___x_3650_;
v_isShared_3702_ = v_isSharedCheck_3711_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3650_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3711_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v_ref_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3709_; 
v_ref_3703_ = lean_ctor_get(v___y_3644_, 5);
v___x_3704_ = lean_io_error_to_string(v_a_3699_);
v___x_3705_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3704_);
v___x_3706_ = l_Lean_MessageData_ofFormat(v___x_3705_);
lean_inc(v_ref_3703_);
v___x_3707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3707_, 0, v_ref_3703_);
lean_ctor_set(v___x_3707_, 1, v___x_3706_);
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 0, v___x_3707_);
v___x_3709_ = v___x_3701_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v___x_3707_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
v___jp_3712_:
{
uint8_t v___x_3723_; lean_object* v___x_3724_; 
v___x_3723_ = 1;
lean_inc_ref(v___y_3713_);
v___x_3724_ = l_Lean_Environment_addConstAsync(v___y_3713_, v___y_3720_, v___y_3717_, v___y_3722_, v_hasTrace_3636_, v___x_3723_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_object* v_a_3725_; lean_object* v_mainEnv_3726_; lean_object* v_asyncEnv_3727_; lean_object* v___f_3728_; lean_object* v___f_3729_; lean_object* v___x_3730_; 
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
lean_inc_n(v_a_3725_, 3);
lean_dec_ref(v___x_3724_);
v_mainEnv_3726_ = lean_ctor_get(v_a_3725_, 0);
lean_inc_ref(v_mainEnv_3726_);
v_asyncEnv_3727_ = lean_ctor_get(v_a_3725_, 1);
lean_inc_ref_n(v_asyncEnv_3727_, 2);
lean_inc_ref(v___y_3714_);
lean_inc(v___y_3715_);
v___f_3728_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3728_, 0, v___y_3715_);
lean_closure_set(v___f_3728_, 1, v_a_3725_);
lean_closure_set(v___f_3728_, 2, v___y_3714_);
lean_inc(v_decl_3577_);
v___f_3729_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3729_, 0, v_asyncEnv_3727_);
lean_closure_set(v___f_3729_, 1, v_a_3725_);
lean_closure_set(v___f_3729_, 2, v_decl_3577_);
v___x_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3730_, 0, v___y_3719_);
if (lean_obj_tag(v___y_3716_) == 0)
{
lean_inc_ref(v___x_3730_);
v___y_3639_ = v___f_3728_;
v___y_3640_ = v___y_3713_;
v___y_3641_ = v_mainEnv_3726_;
v___y_3642_ = v___f_3729_;
v___y_3643_ = v_asyncEnv_3727_;
v___y_3644_ = v___y_3718_;
v___y_3645_ = v_a_3725_;
v___y_3646_ = v___y_3721_;
v___y_3647_ = v___x_3723_;
v___y_3648_ = v___x_3730_;
v___y_3649_ = v___x_3730_;
goto v___jp_3638_;
}
else
{
v___y_3639_ = v___f_3728_;
v___y_3640_ = v___y_3713_;
v___y_3641_ = v_mainEnv_3726_;
v___y_3642_ = v___f_3729_;
v___y_3643_ = v_asyncEnv_3727_;
v___y_3644_ = v___y_3718_;
v___y_3645_ = v_a_3725_;
v___y_3646_ = v___y_3721_;
v___y_3647_ = v___x_3723_;
v___y_3648_ = v___x_3730_;
v___y_3649_ = v___y_3716_;
goto v___jp_3638_;
}
}
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3743_; 
lean_dec_ref(v___y_3719_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3713_);
lean_dec(v_decl_3577_);
v_a_3731_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3733_ = v___x_3724_;
v_isShared_3734_ = v_isSharedCheck_3743_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3724_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3743_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v_ref_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3741_; 
v_ref_3735_ = lean_ctor_get(v___y_3718_, 5);
v___x_3736_ = lean_io_error_to_string(v_a_3731_);
v___x_3737_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3736_);
v___x_3738_ = l_Lean_MessageData_ofFormat(v___x_3737_);
lean_inc(v_ref_3735_);
v___x_3739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3739_, 0, v_ref_3735_);
lean_ctor_set(v___x_3739_, 1, v___x_3738_);
if (v_isShared_3734_ == 0)
{
lean_ctor_set(v___x_3733_, 0, v___x_3739_);
v___x_3741_ = v___x_3733_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v___x_3739_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
}
v___jp_3744_:
{
lean_object* v___x_3751_; 
v___x_3751_ = lean_st_ref_get(v___y_3750_);
if (lean_obj_tag(v_exportedInfo_x3f_3748_) == 0)
{
lean_object* v_env_3752_; lean_object* v___x_3753_; 
v_env_3752_ = lean_ctor_get(v___x_3751_, 0);
lean_inc_ref(v_env_3752_);
lean_dec(v___x_3751_);
v___x_3753_ = lean_box(0);
v___y_3713_ = v_env_3752_;
v___y_3714_ = v___y_3749_;
v___y_3715_ = v___y_3750_;
v___y_3716_ = v_exportedInfo_x3f_3748_;
v___y_3717_ = v___y_3745_;
v___y_3718_ = v___y_3749_;
v___y_3719_ = v___y_3746_;
v___y_3720_ = v___y_3747_;
v___y_3721_ = v___y_3750_;
v___y_3722_ = v___x_3753_;
goto v___jp_3712_;
}
else
{
lean_object* v_env_3754_; lean_object* v_val_3755_; uint8_t v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v_env_3754_ = lean_ctor_get(v___x_3751_, 0);
lean_inc_ref(v_env_3754_);
lean_dec(v___x_3751_);
v_val_3755_ = lean_ctor_get(v_exportedInfo_x3f_3748_, 0);
v___x_3756_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3755_);
v___x_3757_ = lean_box(v___x_3756_);
v___x_3758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3758_, 0, v___x_3757_);
v___y_3713_ = v_env_3754_;
v___y_3714_ = v___y_3749_;
v___y_3715_ = v___y_3750_;
v___y_3716_ = v_exportedInfo_x3f_3748_;
v___y_3717_ = v___y_3745_;
v___y_3718_ = v___y_3749_;
v___y_3719_ = v___y_3746_;
v___y_3720_ = v___y_3747_;
v___y_3721_ = v___y_3750_;
v___y_3722_ = v___x_3758_;
goto v___jp_3712_;
}
}
v___jp_3759_:
{
lean_object* v___x_3765_; 
lean_inc_ref(v___y_3761_);
v___x_3765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3765_, 0, v___y_3761_);
v___y_3745_ = v___y_3760_;
v___y_3746_ = v___y_3761_;
v___y_3747_ = v___y_3762_;
v_exportedInfo_x3f_3748_ = v___x_3765_;
v___y_3749_ = v___y_3763_;
v___y_3750_ = v___y_3764_;
goto v___jp_3744_;
}
v___jp_3766_:
{
lean_object* v___x_3772_; 
lean_inc_ref(v___y_3768_);
v___x_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3772_, 0, v___y_3768_);
v___y_3745_ = v___y_3767_;
v___y_3746_ = v___y_3768_;
v___y_3747_ = v___y_3769_;
v_exportedInfo_x3f_3748_ = v___x_3772_;
v___y_3749_ = v___y_3770_;
v___y_3750_ = v___y_3771_;
goto v___jp_3744_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___boxed(lean_object* v_decl_4663_, lean_object* v_forceExpose_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_){
_start:
{
uint8_t v_forceExpose_boxed_4668_; lean_object* v_res_4669_; 
v_forceExpose_boxed_4668_ = lean_unbox(v_forceExpose_4664_);
v_res_4669_ = l_Lean_addDecl(v_decl_4663_, v_forceExpose_boxed_4668_, v_a_4665_, v_a_4666_);
lean_dec(v_a_4666_);
lean_dec_ref(v_a_4665_);
return v_res_4669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_addDecl_spec__3(lean_object* v_opt_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_){
_start:
{
lean_object* v___x_4674_; 
v___x_4674_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__3___redArg(v_opt_4670_, v___y_4671_);
return v___x_4674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_addDecl_spec__3___boxed(lean_object* v_opt_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_){
_start:
{
lean_object* v_res_4679_; 
v_res_4679_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__3(v_opt_4675_, v___y_4676_, v___y_4677_);
lean_dec(v___y_4677_);
lean_dec_ref(v___y_4676_);
lean_dec_ref(v_opt_4675_);
return v_res_4679_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(lean_object* v_as_x27_4680_, lean_object* v_b_4681_, lean_object* v___y_4682_){
_start:
{
if (lean_obj_tag(v_as_x27_4680_) == 0)
{
lean_object* v___x_4684_; 
v___x_4684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4684_, 0, v_b_4681_);
return v___x_4684_;
}
else
{
lean_object* v_head_4685_; lean_object* v_tail_4686_; lean_object* v___x_4687_; lean_object* v_env_4688_; lean_object* v_nextMacroScope_4689_; lean_object* v_ngen_4690_; lean_object* v_auxDeclNGen_4691_; lean_object* v_traceState_4692_; lean_object* v_messages_4693_; lean_object* v_infoState_4694_; lean_object* v_snapshotTasks_4695_; lean_object* v_newDecls_4696_; lean_object* v___x_4698_; uint8_t v_isShared_4699_; uint8_t v_isSharedCheck_4708_; 
v_head_4685_ = lean_ctor_get(v_as_x27_4680_, 0);
v_tail_4686_ = lean_ctor_get(v_as_x27_4680_, 1);
v___x_4687_ = lean_st_ref_take(v___y_4682_);
v_env_4688_ = lean_ctor_get(v___x_4687_, 0);
v_nextMacroScope_4689_ = lean_ctor_get(v___x_4687_, 1);
v_ngen_4690_ = lean_ctor_get(v___x_4687_, 2);
v_auxDeclNGen_4691_ = lean_ctor_get(v___x_4687_, 3);
v_traceState_4692_ = lean_ctor_get(v___x_4687_, 4);
v_messages_4693_ = lean_ctor_get(v___x_4687_, 6);
v_infoState_4694_ = lean_ctor_get(v___x_4687_, 7);
v_snapshotTasks_4695_ = lean_ctor_get(v___x_4687_, 8);
v_newDecls_4696_ = lean_ctor_get(v___x_4687_, 9);
v_isSharedCheck_4708_ = !lean_is_exclusive(v___x_4687_);
if (v_isSharedCheck_4708_ == 0)
{
lean_object* v_unused_4709_; 
v_unused_4709_ = lean_ctor_get(v___x_4687_, 5);
lean_dec(v_unused_4709_);
v___x_4698_ = v___x_4687_;
v_isShared_4699_ = v_isSharedCheck_4708_;
goto v_resetjp_4697_;
}
else
{
lean_inc(v_newDecls_4696_);
lean_inc(v_snapshotTasks_4695_);
lean_inc(v_infoState_4694_);
lean_inc(v_messages_4693_);
lean_inc(v_traceState_4692_);
lean_inc(v_auxDeclNGen_4691_);
lean_inc(v_ngen_4690_);
lean_inc(v_nextMacroScope_4689_);
lean_inc(v_env_4688_);
lean_dec(v___x_4687_);
v___x_4698_ = lean_box(0);
v_isShared_4699_ = v_isSharedCheck_4708_;
goto v_resetjp_4697_;
}
v_resetjp_4697_:
{
lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4703_; 
lean_inc(v_head_4685_);
v___x_4700_ = l_Lean_markMeta(v_env_4688_, v_head_4685_);
v___x_4701_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2);
if (v_isShared_4699_ == 0)
{
lean_ctor_set(v___x_4698_, 5, v___x_4701_);
lean_ctor_set(v___x_4698_, 0, v___x_4700_);
v___x_4703_ = v___x_4698_;
goto v_reusejp_4702_;
}
else
{
lean_object* v_reuseFailAlloc_4707_; 
v_reuseFailAlloc_4707_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4707_, 0, v___x_4700_);
lean_ctor_set(v_reuseFailAlloc_4707_, 1, v_nextMacroScope_4689_);
lean_ctor_set(v_reuseFailAlloc_4707_, 2, v_ngen_4690_);
lean_ctor_set(v_reuseFailAlloc_4707_, 3, v_auxDeclNGen_4691_);
lean_ctor_set(v_reuseFailAlloc_4707_, 4, v_traceState_4692_);
lean_ctor_set(v_reuseFailAlloc_4707_, 5, v___x_4701_);
lean_ctor_set(v_reuseFailAlloc_4707_, 6, v_messages_4693_);
lean_ctor_set(v_reuseFailAlloc_4707_, 7, v_infoState_4694_);
lean_ctor_set(v_reuseFailAlloc_4707_, 8, v_snapshotTasks_4695_);
lean_ctor_set(v_reuseFailAlloc_4707_, 9, v_newDecls_4696_);
v___x_4703_ = v_reuseFailAlloc_4707_;
goto v_reusejp_4702_;
}
v_reusejp_4702_:
{
lean_object* v___x_4704_; lean_object* v___x_4705_; 
v___x_4704_ = lean_st_ref_set(v___y_4682_, v___x_4703_);
v___x_4705_ = lean_box(0);
v_as_x27_4680_ = v_tail_4686_;
v_b_4681_ = v___x_4705_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg___boxed(lean_object* v_as_x27_4710_, lean_object* v_b_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_){
_start:
{
lean_object* v_res_4714_; 
v_res_4714_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_4710_, v_b_4711_, v___y_4712_);
lean_dec(v___y_4712_);
lean_dec(v_as_x27_4710_);
return v_res_4714_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object* v_decl_4715_, uint8_t v_logCompileErrors_4716_, uint8_t v_markMeta_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_){
_start:
{
uint8_t v___x_4721_; lean_object* v___x_4722_; 
v___x_4721_ = 0;
lean_inc(v_decl_4715_);
v___x_4722_ = l_Lean_addDecl(v_decl_4715_, v___x_4721_, v_a_4718_, v_a_4719_);
if (lean_obj_tag(v___x_4722_) == 0)
{
lean_dec_ref(v___x_4722_);
if (v_markMeta_4717_ == 0)
{
lean_object* v___x_4723_; 
v___x_4723_ = l_Lean_compileDecl(v_decl_4715_, v_logCompileErrors_4716_, v_a_4718_, v_a_4719_);
return v___x_4723_;
}
else
{
lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; 
lean_inc(v_decl_4715_);
v___x_4724_ = l_Lean_Declaration_getNames(v_decl_4715_);
v___x_4725_ = lean_box(0);
v___x_4726_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v___x_4724_, v___x_4725_, v_a_4719_);
lean_dec(v___x_4724_);
lean_dec_ref(v___x_4726_);
v___x_4727_ = l_Lean_compileDecl(v_decl_4715_, v_logCompileErrors_4716_, v_a_4718_, v_a_4719_);
return v___x_4727_;
}
}
else
{
lean_dec(v_decl_4715_);
return v___x_4722_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___boxed(lean_object* v_decl_4728_, lean_object* v_logCompileErrors_4729_, lean_object* v_markMeta_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_){
_start:
{
uint8_t v_logCompileErrors_boxed_4734_; uint8_t v_markMeta_boxed_4735_; lean_object* v_res_4736_; 
v_logCompileErrors_boxed_4734_ = lean_unbox(v_logCompileErrors_4729_);
v_markMeta_boxed_4735_ = lean_unbox(v_markMeta_4730_);
v_res_4736_ = l_Lean_addAndCompile(v_decl_4728_, v_logCompileErrors_boxed_4734_, v_markMeta_boxed_4735_, v_a_4731_, v_a_4732_);
lean_dec(v_a_4732_);
lean_dec_ref(v_a_4731_);
return v_res_4736_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(lean_object* v_as_4737_, lean_object* v_as_x27_4738_, lean_object* v_b_4739_, lean_object* v_a_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_){
_start:
{
lean_object* v___x_4744_; 
v___x_4744_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_4738_, v_b_4739_, v___y_4742_);
return v___x_4744_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___boxed(lean_object* v_as_4745_, lean_object* v_as_x27_4746_, lean_object* v_b_4747_, lean_object* v_a_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_){
_start:
{
lean_object* v_res_4752_; 
v_res_4752_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(v_as_4745_, v_as_x27_4746_, v_b_4747_, v_a_4748_, v___y_4749_, v___y_4750_);
lean_dec(v___y_4750_);
lean_dec_ref(v___y_4749_);
lean_dec(v_as_x27_4746_);
lean_dec(v_as_4745_);
return v_res_4752_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sorry(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectAxioms(uint8_t builtin);
lean_object* runtime_initialize_Lean_OriginalConstKind(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_MetaAttr(uint8_t builtin);
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
res = runtime_initialize_Lean_Compiler_MetaAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_OriginalConstKind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_();
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
lean_object* initialize_Lean_Compiler_MetaAttr(uint8_t builtin);
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
res = initialize_Lean_Compiler_MetaAttr(builtin);
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
