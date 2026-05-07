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
uint8_t v___y_15938__boxed_225_; uint8_t v_suppressElabErrors_boxed_226_; uint8_t v_res_227_; lean_object* v_r_228_; 
v___y_15938__boxed_225_ = lean_unbox(v___y_222_);
v_suppressElabErrors_boxed_226_ = lean_unbox(v_suppressElabErrors_223_);
v_res_227_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(v___y_15938__boxed_225_, v_suppressElabErrors_boxed_226_, v_x_224_);
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
uint8_t v___y_274_; uint8_t v___y_275_; lean_object* v___y_276_; lean_object* v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v___y_282_; lean_object* v___y_310_; uint8_t v___y_311_; lean_object* v___y_312_; uint8_t v___y_313_; lean_object* v___y_314_; uint8_t v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_335_; uint8_t v___y_336_; lean_object* v___y_337_; uint8_t v___y_338_; lean_object* v___y_339_; uint8_t v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; lean_object* v___y_346_; uint8_t v___y_347_; lean_object* v___y_348_; uint8_t v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; uint8_t v___y_352_; uint8_t v___x_357_; lean_object* v___y_359_; lean_object* v___y_360_; uint8_t v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; uint8_t v___y_364_; uint8_t v___y_365_; uint8_t v___y_367_; uint8_t v___x_382_; 
v___x_357_ = 2;
v___x_382_ = l_Lean_instBEqMessageSeverity_beq(v_severity_268_, v___x_357_);
if (v___x_382_ == 0)
{
v___y_367_ = v___x_382_;
goto v___jp_366_;
}
else
{
uint8_t v___x_383_; 
lean_inc_ref(v_msgData_267_);
v___x_383_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_267_);
v___y_367_ = v___x_383_;
goto v___jp_366_;
}
v___jp_273_:
{
lean_object* v___x_283_; lean_object* v_currNamespace_284_; lean_object* v_openDecls_285_; lean_object* v_env_286_; lean_object* v_nextMacroScope_287_; lean_object* v_ngen_288_; lean_object* v_auxDeclNGen_289_; lean_object* v_traceState_290_; lean_object* v_cache_291_; lean_object* v_messages_292_; lean_object* v_infoState_293_; lean_object* v_snapshotTasks_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_308_; 
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
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_308_ == 0)
{
v___x_296_ = v___x_283_;
v_isShared_297_ = v_isSharedCheck_308_;
goto v_resetjp_295_;
}
else
{
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
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_308_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_303_; 
lean_inc(v_openDecls_285_);
lean_inc(v_currNamespace_284_);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v_currNamespace_284_);
lean_ctor_set(v___x_298_, 1, v_openDecls_285_);
v___x_299_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v___y_277_);
lean_inc_ref(v___y_278_);
lean_inc_ref(v___y_280_);
v___x_300_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_300_, 0, v___y_280_);
lean_ctor_set(v___x_300_, 1, v___y_279_);
lean_ctor_set(v___x_300_, 2, v___y_276_);
lean_ctor_set(v___x_300_, 3, v___y_278_);
lean_ctor_set(v___x_300_, 4, v___x_299_);
lean_ctor_set_uint8(v___x_300_, sizeof(void*)*5, v___y_275_);
lean_ctor_set_uint8(v___x_300_, sizeof(void*)*5 + 1, v___y_274_);
lean_ctor_set_uint8(v___x_300_, sizeof(void*)*5 + 2, v_isSilent_269_);
v___x_301_ = l_Lean_MessageLog_add(v___x_300_, v_messages_292_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 6, v___x_301_);
v___x_303_ = v___x_296_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_env_286_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v_nextMacroScope_287_);
lean_ctor_set(v_reuseFailAlloc_307_, 2, v_ngen_288_);
lean_ctor_set(v_reuseFailAlloc_307_, 3, v_auxDeclNGen_289_);
lean_ctor_set(v_reuseFailAlloc_307_, 4, v_traceState_290_);
lean_ctor_set(v_reuseFailAlloc_307_, 5, v_cache_291_);
lean_ctor_set(v_reuseFailAlloc_307_, 6, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_307_, 7, v_infoState_293_);
lean_ctor_set(v_reuseFailAlloc_307_, 8, v_snapshotTasks_294_);
v___x_303_ = v_reuseFailAlloc_307_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_304_ = lean_st_ref_set(v___y_282_, v___x_303_);
v___x_305_ = lean_box(0);
v___x_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
return v___x_306_;
}
}
}
v___jp_309_:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_333_; 
v___x_318_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_267_);
v___x_319_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v___x_318_, v___y_270_, v___y_271_);
v_a_320_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_333_ == 0)
{
v___x_322_ = v___x_319_;
v_isShared_323_ = v_isSharedCheck_333_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_319_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_333_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
lean_inc_ref_n(v___y_314_, 2);
v___x_324_ = l_Lean_FileMap_toPosition(v___y_314_, v___y_312_);
lean_dec(v___y_312_);
v___x_325_ = l_Lean_FileMap_toPosition(v___y_314_, v___y_317_);
lean_dec(v___y_317_);
v___x_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
v___x_327_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
if (v___y_315_ == 0)
{
lean_del_object(v___x_322_);
lean_dec_ref(v___y_310_);
v___y_274_ = v___y_311_;
v___y_275_ = v___y_313_;
v___y_276_ = v___x_326_;
v___y_277_ = v_a_320_;
v___y_278_ = v___x_327_;
v___y_279_ = v___x_324_;
v___y_280_ = v___y_316_;
v___y_281_ = v___y_270_;
v___y_282_ = v___y_271_;
goto v___jp_273_;
}
else
{
uint8_t v___x_328_; 
lean_inc(v_a_320_);
v___x_328_ = l_Lean_MessageData_hasTag(v___y_310_, v_a_320_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v___x_331_; 
lean_dec_ref(v___x_326_);
lean_dec_ref(v___x_324_);
lean_dec(v_a_320_);
v___x_329_ = lean_box(0);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 0, v___x_329_);
v___x_331_ = v___x_322_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
else
{
lean_del_object(v___x_322_);
v___y_274_ = v___y_311_;
v___y_275_ = v___y_313_;
v___y_276_ = v___x_326_;
v___y_277_ = v_a_320_;
v___y_278_ = v___x_327_;
v___y_279_ = v___x_324_;
v___y_280_ = v___y_316_;
v___y_281_ = v___y_270_;
v___y_282_ = v___y_271_;
goto v___jp_273_;
}
}
}
}
v___jp_334_:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_Syntax_getTailPos_x3f(v___y_339_, v___y_338_);
lean_dec(v___y_339_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_inc(v___y_342_);
v___y_310_ = v___y_335_;
v___y_311_ = v___y_336_;
v___y_312_ = v___y_342_;
v___y_313_ = v___y_338_;
v___y_314_ = v___y_337_;
v___y_315_ = v___y_340_;
v___y_316_ = v___y_341_;
v___y_317_ = v___y_342_;
goto v___jp_309_;
}
else
{
lean_object* v_val_344_; 
v_val_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_val_344_);
lean_dec_ref(v___x_343_);
v___y_310_ = v___y_335_;
v___y_311_ = v___y_336_;
v___y_312_ = v___y_342_;
v___y_313_ = v___y_338_;
v___y_314_ = v___y_337_;
v___y_315_ = v___y_340_;
v___y_316_ = v___y_341_;
v___y_317_ = v_val_344_;
goto v___jp_309_;
}
}
v___jp_345_:
{
lean_object* v_ref_353_; lean_object* v___x_354_; 
v_ref_353_ = l_Lean_replaceRef(v_ref_266_, v___y_351_);
v___x_354_ = l_Lean_Syntax_getPos_x3f(v_ref_353_, v___y_347_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v___x_355_; 
v___x_355_ = lean_unsigned_to_nat(0u);
v___y_335_ = v___y_346_;
v___y_336_ = v___y_352_;
v___y_337_ = v___y_348_;
v___y_338_ = v___y_347_;
v___y_339_ = v_ref_353_;
v___y_340_ = v___y_349_;
v___y_341_ = v___y_350_;
v___y_342_ = v___x_355_;
goto v___jp_334_;
}
else
{
lean_object* v_val_356_; 
v_val_356_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_val_356_);
lean_dec_ref(v___x_354_);
v___y_335_ = v___y_346_;
v___y_336_ = v___y_352_;
v___y_337_ = v___y_348_;
v___y_338_ = v___y_347_;
v___y_339_ = v_ref_353_;
v___y_340_ = v___y_349_;
v___y_341_ = v___y_350_;
v___y_342_ = v_val_356_;
goto v___jp_334_;
}
}
v___jp_358_:
{
if (v___y_365_ == 0)
{
v___y_346_ = v___y_359_;
v___y_347_ = v___y_364_;
v___y_348_ = v___y_360_;
v___y_349_ = v___y_361_;
v___y_350_ = v___y_363_;
v___y_351_ = v___y_362_;
v___y_352_ = v_severity_268_;
goto v___jp_345_;
}
else
{
v___y_346_ = v___y_359_;
v___y_347_ = v___y_364_;
v___y_348_ = v___y_360_;
v___y_349_ = v___y_361_;
v___y_350_ = v___y_363_;
v___y_351_ = v___y_362_;
v___y_352_ = v___x_357_;
goto v___jp_345_;
}
}
v___jp_366_:
{
if (v___y_367_ == 0)
{
lean_object* v_fileName_368_; lean_object* v_fileMap_369_; lean_object* v_options_370_; lean_object* v_ref_371_; uint8_t v_suppressElabErrors_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___f_375_; uint8_t v___x_376_; uint8_t v___x_377_; 
v_fileName_368_ = lean_ctor_get(v___y_270_, 0);
v_fileMap_369_ = lean_ctor_get(v___y_270_, 1);
v_options_370_ = lean_ctor_get(v___y_270_, 2);
v_ref_371_ = lean_ctor_get(v___y_270_, 5);
v_suppressElabErrors_372_ = lean_ctor_get_uint8(v___y_270_, sizeof(void*)*14 + 1);
v___x_373_ = lean_box(v___y_367_);
v___x_374_ = lean_box(v_suppressElabErrors_372_);
v___f_375_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed), 3, 2);
lean_closure_set(v___f_375_, 0, v___x_373_);
lean_closure_set(v___f_375_, 1, v___x_374_);
v___x_376_ = 1;
v___x_377_ = l_Lean_instBEqMessageSeverity_beq(v_severity_268_, v___x_376_);
if (v___x_377_ == 0)
{
v___y_359_ = v___f_375_;
v___y_360_ = v_fileMap_369_;
v___y_361_ = v_suppressElabErrors_372_;
v___y_362_ = v_ref_371_;
v___y_363_ = v_fileName_368_;
v___y_364_ = v___y_367_;
v___y_365_ = v___x_377_;
goto v___jp_358_;
}
else
{
lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = l_Lean_warningAsError;
v___x_379_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_370_, v___x_378_);
v___y_359_ = v___f_375_;
v___y_360_ = v_fileMap_369_;
v___y_361_ = v_suppressElabErrors_372_;
v___y_362_ = v_ref_371_;
v___y_363_ = v_fileName_368_;
v___y_364_ = v___y_367_;
v___y_365_ = v___x_379_;
goto v___jp_358_;
}
}
else
{
lean_object* v___x_380_; lean_object* v___x_381_; 
lean_dec_ref(v_msgData_267_);
v___x_380_ = lean_box(0);
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
return v___x_381_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___boxed(lean_object* v_ref_384_, lean_object* v_msgData_385_, lean_object* v_severity_386_, lean_object* v_isSilent_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
uint8_t v_severity_boxed_391_; uint8_t v_isSilent_boxed_392_; lean_object* v_res_393_; 
v_severity_boxed_391_ = lean_unbox(v_severity_386_);
v_isSilent_boxed_392_ = lean_unbox(v_isSilent_387_);
v_res_393_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_384_, v_msgData_385_, v_severity_boxed_391_, v_isSilent_boxed_392_, v___y_388_, v___y_389_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v_ref_384_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(lean_object* v_msgData_394_, uint8_t v_severity_395_, uint8_t v_isSilent_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_ref_400_; lean_object* v___x_401_; 
v_ref_400_ = lean_ctor_get(v___y_397_, 5);
v___x_401_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_400_, v_msgData_394_, v_severity_395_, v_isSilent_396_, v___y_397_, v___y_398_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4___boxed(lean_object* v_msgData_402_, lean_object* v_severity_403_, lean_object* v_isSilent_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
uint8_t v_severity_boxed_408_; uint8_t v_isSilent_boxed_409_; lean_object* v_res_410_; 
v_severity_boxed_408_ = lean_unbox(v_severity_403_);
v_isSilent_boxed_409_ = lean_unbox(v_isSilent_404_);
v_res_410_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_402_, v_severity_boxed_408_, v_isSilent_boxed_409_, v___y_405_, v___y_406_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(lean_object* v_msgData_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
uint8_t v___x_415_; uint8_t v___x_416_; lean_object* v___x_417_; 
v___x_415_ = 1;
v___x_416_ = 0;
v___x_417_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_411_, v___x_415_, v___x_416_, v___y_412_, v___y_413_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2___boxed(lean_object* v_msgData_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v_msgData_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(lean_object* v_as_426_, size_t v_sz_427_, size_t v_i_428_, lean_object* v_b_429_){
_start:
{
uint8_t v___x_430_; 
v___x_430_ = lean_usize_dec_lt(v_i_428_, v_sz_427_);
if (v___x_430_ == 0)
{
lean_inc_ref(v_b_429_);
return v_b_429_;
}
else
{
lean_object* v_a_431_; lean_object* v_fst_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v_a_431_ = lean_array_uget_borrowed(v_as_426_, v_i_428_);
v_fst_432_ = lean_ctor_get(v_a_431_, 0);
v___x_433_ = lean_box(0);
v___x_434_ = lean_unbox(v_fst_432_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; size_t v___x_436_; size_t v___x_437_; 
v___x_435_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___closed__0));
v___x_436_ = ((size_t)1ULL);
v___x_437_ = lean_usize_add(v_i_428_, v___x_436_);
v_i_428_ = v___x_437_;
v_b_429_ = v___x_435_;
goto _start;
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
lean_inc(v_a_431_);
v___x_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_439_, 0, v_a_431_);
v___x_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
lean_ctor_set(v___x_441_, 1, v___x_433_);
return v___x_441_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___boxed(lean_object* v_as_442_, lean_object* v_sz_443_, lean_object* v_i_444_, lean_object* v_b_445_){
_start:
{
size_t v_sz_boxed_446_; size_t v_i_boxed_447_; lean_object* v_res_448_; 
v_sz_boxed_446_ = lean_unbox_usize(v_sz_443_);
lean_dec(v_sz_443_);
v_i_boxed_447_ = lean_unbox_usize(v_i_444_);
lean_dec(v_i_444_);
v_res_448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v_as_442_, v_sz_boxed_446_, v_i_boxed_447_, v_b_445_);
lean_dec_ref(v_b_445_);
lean_dec_ref(v_as_442_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(lean_object* v_fn_449_, lean_object* v_e_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_Expr_getSorry_x3f(v_e_450_);
if (lean_obj_tag(v___x_457_) == 1)
{
lean_object* v_val_458_; lean_object* v___x_459_; 
v_val_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_val_458_);
lean_dec_ref(v___x_457_);
lean_inc(v___y_455_);
lean_inc_ref(v___y_454_);
lean_inc(v___y_453_);
lean_inc_ref(v___y_452_);
lean_inc(v___y_451_);
v___x_459_ = lean_apply_7(v_fn_449_, v_val_458_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, lean_box(0));
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_468_; 
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_468_ == 0)
{
lean_object* v_unused_469_; 
v_unused_469_ = lean_ctor_get(v___x_459_, 0);
lean_dec(v_unused_469_);
v___x_461_ = v___x_459_;
v_isShared_462_ = v_isSharedCheck_468_;
goto v_resetjp_460_;
}
else
{
lean_dec(v___x_459_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_468_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
uint8_t v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_463_ = 0;
v___x_464_ = lean_box(v___x_463_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_464_);
v___x_466_ = v___x_461_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_464_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
else
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
v_a_470_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___x_459_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_459_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_a_470_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
else
{
uint8_t v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
lean_dec(v___x_457_);
lean_dec_ref(v_fn_449_);
v___x_478_ = 1;
v___x_479_ = lean_box(v___x_478_);
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
return v___x_480_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed(lean_object* v_fn_481_, lean_object* v_e_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(v_fn_481_, v_e_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v_e_482_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_object* v_00_u03b1_490_, lean_object* v_x_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_apply_1(v_x_491_, lean_box(0));
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v_00_u03b1_500_, lean_object* v_x_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(v_00_u03b1_500_, v_x_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(lean_object* v_k_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v_b_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v___x_518_; 
lean_inc(v___y_516_);
lean_inc_ref(v___y_515_);
lean_inc(v___y_514_);
lean_inc_ref(v___y_513_);
lean_inc(v___y_511_);
lean_inc(v___y_510_);
v___x_518_ = lean_apply_8(v_k_509_, v_b_512_, v___y_510_, v___y_511_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, lean_box(0));
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed(lean_object* v_k_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v_b_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(v_k_519_, v___y_520_, v___y_521_, v_b_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_521_);
lean_dec(v___y_520_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(lean_object* v_name_529_, lean_object* v_type_530_, lean_object* v_val_531_, lean_object* v_k_532_, uint8_t v_nondep_533_, uint8_t v_kind_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v___f_542_; lean_object* v___x_543_; 
lean_inc(v___y_536_);
lean_inc(v___y_535_);
v___f_542_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_542_, 0, v_k_532_);
lean_closure_set(v___f_542_, 1, v___y_535_);
lean_closure_set(v___f_542_, 2, v___y_536_);
v___x_543_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_529_, v_type_530_, v_val_531_, v___f_542_, v_nondep_533_, v_kind_534_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
if (lean_obj_tag(v___x_543_) == 0)
{
return v___x_543_;
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_543_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_543_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg___boxed(lean_object* v_name_552_, lean_object* v_type_553_, lean_object* v_val_554_, lean_object* v_k_555_, lean_object* v_nondep_556_, lean_object* v_kind_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
uint8_t v_nondep_boxed_565_; uint8_t v_kind_boxed_566_; lean_object* v_res_567_; 
v_nondep_boxed_565_ = lean_unbox(v_nondep_556_);
v_kind_boxed_566_ = lean_unbox(v_kind_557_);
v_res_567_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_552_, v_type_553_, v_val_554_, v_k_555_, v_nondep_boxed_565_, v_kind_boxed_566_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec(v___y_558_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed(lean_object* v_fvars_568_, lean_object* v_f_569_, lean_object* v_body_570_, lean_object* v_x_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(v_fvars_568_, v_f_569_, v_body_570_, v_x_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec(v___y_572_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(lean_object* v_f_580_, lean_object* v_fvars_581_, lean_object* v_a_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
if (lean_obj_tag(v_a_582_) == 8)
{
lean_object* v_declName_590_; lean_object* v_type_591_; lean_object* v_value_592_; lean_object* v_body_593_; lean_object* v_d_594_; lean_object* v___x_595_; 
v_declName_590_ = lean_ctor_get(v_a_582_, 0);
lean_inc(v_declName_590_);
v_type_591_ = lean_ctor_get(v_a_582_, 1);
lean_inc_ref(v_type_591_);
v_value_592_ = lean_ctor_get(v_a_582_, 2);
lean_inc_ref(v_value_592_);
v_body_593_ = lean_ctor_get(v_a_582_, 3);
lean_inc_ref(v_body_593_);
lean_dec_ref(v_a_582_);
v_d_594_ = lean_expr_instantiate_rev(v_type_591_, v_fvars_581_);
lean_dec_ref(v_type_591_);
lean_inc_ref(v_f_580_);
lean_inc(v___y_588_);
lean_inc_ref(v___y_587_);
lean_inc(v___y_586_);
lean_inc_ref(v___y_585_);
lean_inc(v___y_584_);
lean_inc(v___y_583_);
lean_inc_ref(v_d_594_);
v___x_595_ = lean_apply_8(v_f_580_, v_d_594_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, lean_box(0));
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_v_596_; lean_object* v___x_597_; 
lean_dec_ref(v___x_595_);
v_v_596_ = lean_expr_instantiate_rev(v_value_592_, v_fvars_581_);
lean_dec_ref(v_value_592_);
lean_inc_ref(v_f_580_);
lean_inc(v___y_588_);
lean_inc_ref(v___y_587_);
lean_inc(v___y_586_);
lean_inc_ref(v___y_585_);
lean_inc(v___y_584_);
lean_inc(v___y_583_);
lean_inc_ref(v_v_596_);
v___x_597_ = lean_apply_8(v_f_580_, v_v_596_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, lean_box(0));
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v___f_598_; uint8_t v___x_599_; uint8_t v___x_600_; lean_object* v___x_601_; 
lean_dec_ref(v___x_597_);
v___f_598_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed), 11, 3);
lean_closure_set(v___f_598_, 0, v_fvars_581_);
lean_closure_set(v___f_598_, 1, v_f_580_);
lean_closure_set(v___f_598_, 2, v_body_593_);
v___x_599_ = 0;
v___x_600_ = 0;
v___x_601_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_declName_590_, v_d_594_, v_v_596_, v___f_598_, v___x_599_, v___x_600_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
return v___x_601_;
}
else
{
lean_dec_ref(v_v_596_);
lean_dec_ref(v_d_594_);
lean_dec_ref(v_body_593_);
lean_dec(v_declName_590_);
lean_dec_ref(v_fvars_581_);
lean_dec_ref(v_f_580_);
return v___x_597_;
}
}
else
{
lean_dec_ref(v_d_594_);
lean_dec_ref(v_body_593_);
lean_dec_ref(v_value_592_);
lean_dec(v_declName_590_);
lean_dec_ref(v_fvars_581_);
lean_dec_ref(v_f_580_);
return v___x_595_;
}
}
else
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_expr_instantiate_rev(v_a_582_, v_fvars_581_);
lean_dec_ref(v_fvars_581_);
lean_dec_ref(v_a_582_);
lean_inc(v___y_588_);
lean_inc_ref(v___y_587_);
lean_inc(v___y_586_);
lean_inc_ref(v___y_585_);
lean_inc(v___y_584_);
lean_inc(v___y_583_);
v___x_603_ = lean_apply_8(v_f_580_, v___x_602_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, lean_box(0));
return v___x_603_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(lean_object* v_fvars_604_, lean_object* v_f_605_, lean_object* v_body_606_, lean_object* v_x_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_array_push(v_fvars_604_, v_x_607_);
v___x_616_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_605_, v___x_615_, v_body_606_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___boxed(lean_object* v_f_617_, lean_object* v_fvars_618_, lean_object* v_a_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_617_, v_fvars_618_, v_a_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec(v___y_620_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(lean_object* v_f_630_, lean_object* v_e_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_640_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_630_, v___x_639_, v_e_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___boxed(lean_object* v_f_641_, lean_object* v_e_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v_f_641_, v_e_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec(v___y_643_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(lean_object* v_name_651_, uint8_t v_bi_652_, lean_object* v_type_653_, lean_object* v_k_654_, uint8_t v_kind_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v___f_663_; lean_object* v___x_664_; 
lean_inc(v___y_657_);
lean_inc(v___y_656_);
v___f_663_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_663_, 0, v_k_654_);
lean_closure_set(v___f_663_, 1, v___y_656_);
lean_closure_set(v___f_663_, 2, v___y_657_);
v___x_664_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_651_, v_bi_652_, v_type_653_, v___f_663_, v_kind_655_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
if (lean_obj_tag(v___x_664_) == 0)
{
return v___x_664_;
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_664_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_664_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___boxed(lean_object* v_name_673_, lean_object* v_bi_674_, lean_object* v_type_675_, lean_object* v_k_676_, lean_object* v_kind_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
uint8_t v_bi_boxed_685_; uint8_t v_kind_boxed_686_; lean_object* v_res_687_; 
v_bi_boxed_685_ = lean_unbox(v_bi_674_);
v_kind_boxed_686_ = lean_unbox(v_kind_677_);
v_res_687_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_673_, v_bi_boxed_685_, v_type_675_, v_k_676_, v_kind_boxed_686_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec(v___y_678_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed(lean_object* v_fvars_688_, lean_object* v_f_689_, lean_object* v_body_690_, lean_object* v_x_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(v_fvars_688_, v_f_689_, v_body_690_, v_x_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec(v___y_692_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(lean_object* v_f_700_, lean_object* v_fvars_701_, lean_object* v_a_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
if (lean_obj_tag(v_a_702_) == 7)
{
lean_object* v_binderName_710_; lean_object* v_binderType_711_; lean_object* v_body_712_; uint8_t v_binderInfo_713_; lean_object* v_d_714_; lean_object* v___x_715_; 
v_binderName_710_ = lean_ctor_get(v_a_702_, 0);
lean_inc(v_binderName_710_);
v_binderType_711_ = lean_ctor_get(v_a_702_, 1);
lean_inc_ref(v_binderType_711_);
v_body_712_ = lean_ctor_get(v_a_702_, 2);
lean_inc_ref(v_body_712_);
v_binderInfo_713_ = lean_ctor_get_uint8(v_a_702_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_702_);
v_d_714_ = lean_expr_instantiate_rev(v_binderType_711_, v_fvars_701_);
lean_dec_ref(v_binderType_711_);
lean_inc_ref(v_f_700_);
lean_inc(v___y_708_);
lean_inc_ref(v___y_707_);
lean_inc(v___y_706_);
lean_inc_ref(v___y_705_);
lean_inc(v___y_704_);
lean_inc(v___y_703_);
lean_inc_ref(v_d_714_);
v___x_715_ = lean_apply_8(v_f_700_, v_d_714_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, lean_box(0));
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v___f_716_; uint8_t v___x_717_; lean_object* v___x_718_; 
lean_dec_ref(v___x_715_);
v___f_716_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed), 11, 3);
lean_closure_set(v___f_716_, 0, v_fvars_701_);
lean_closure_set(v___f_716_, 1, v_f_700_);
lean_closure_set(v___f_716_, 2, v_body_712_);
v___x_717_ = 0;
v___x_718_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_710_, v_binderInfo_713_, v_d_714_, v___f_716_, v___x_717_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
return v___x_718_;
}
else
{
lean_dec_ref(v_d_714_);
lean_dec_ref(v_body_712_);
lean_dec(v_binderName_710_);
lean_dec_ref(v_fvars_701_);
lean_dec_ref(v_f_700_);
return v___x_715_;
}
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_expr_instantiate_rev(v_a_702_, v_fvars_701_);
lean_dec_ref(v_fvars_701_);
lean_dec_ref(v_a_702_);
lean_inc(v___y_708_);
lean_inc_ref(v___y_707_);
lean_inc(v___y_706_);
lean_inc_ref(v___y_705_);
lean_inc(v___y_704_);
lean_inc(v___y_703_);
v___x_720_ = lean_apply_8(v_f_700_, v___x_719_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, lean_box(0));
return v___x_720_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(lean_object* v_fvars_721_, lean_object* v_f_722_, lean_object* v_body_723_, lean_object* v_x_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_array_push(v_fvars_721_, v_x_724_);
v___x_733_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_722_, v___x_732_, v_body_723_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___boxed(lean_object* v_f_734_, lean_object* v_fvars_735_, lean_object* v_a_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_734_, v_fvars_735_, v_a_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec(v___y_737_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(lean_object* v_f_745_, lean_object* v_e_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_755_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_745_, v___x_754_, v_e_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10___boxed(lean_object* v_f_756_, lean_object* v_e_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v_f_756_, v_e_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec(v___y_758_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed(lean_object* v_fvars_766_, lean_object* v_f_767_, lean_object* v_body_768_, lean_object* v_x_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(v_fvars_766_, v_f_767_, v_body_768_, v_x_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec(v___y_770_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(lean_object* v_f_778_, lean_object* v_fvars_779_, lean_object* v_a_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
if (lean_obj_tag(v_a_780_) == 6)
{
lean_object* v_binderName_788_; lean_object* v_binderType_789_; lean_object* v_body_790_; uint8_t v_binderInfo_791_; lean_object* v_d_792_; lean_object* v___x_793_; 
v_binderName_788_ = lean_ctor_get(v_a_780_, 0);
lean_inc(v_binderName_788_);
v_binderType_789_ = lean_ctor_get(v_a_780_, 1);
lean_inc_ref(v_binderType_789_);
v_body_790_ = lean_ctor_get(v_a_780_, 2);
lean_inc_ref(v_body_790_);
v_binderInfo_791_ = lean_ctor_get_uint8(v_a_780_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_780_);
v_d_792_ = lean_expr_instantiate_rev(v_binderType_789_, v_fvars_779_);
lean_dec_ref(v_binderType_789_);
lean_inc_ref(v_f_778_);
lean_inc(v___y_786_);
lean_inc_ref(v___y_785_);
lean_inc(v___y_784_);
lean_inc_ref(v___y_783_);
lean_inc(v___y_782_);
lean_inc(v___y_781_);
lean_inc_ref(v_d_792_);
v___x_793_ = lean_apply_8(v_f_778_, v_d_792_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, lean_box(0));
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v___f_794_; uint8_t v___x_795_; lean_object* v___x_796_; 
lean_dec_ref(v___x_793_);
v___f_794_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed), 11, 3);
lean_closure_set(v___f_794_, 0, v_fvars_779_);
lean_closure_set(v___f_794_, 1, v_f_778_);
lean_closure_set(v___f_794_, 2, v_body_790_);
v___x_795_ = 0;
v___x_796_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_788_, v_binderInfo_791_, v_d_792_, v___f_794_, v___x_795_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
return v___x_796_;
}
else
{
lean_dec_ref(v_d_792_);
lean_dec_ref(v_body_790_);
lean_dec(v_binderName_788_);
lean_dec_ref(v_fvars_779_);
lean_dec_ref(v_f_778_);
return v___x_793_;
}
}
else
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_expr_instantiate_rev(v_a_780_, v_fvars_779_);
lean_dec_ref(v_fvars_779_);
lean_dec_ref(v_a_780_);
lean_inc(v___y_786_);
lean_inc_ref(v___y_785_);
lean_inc(v___y_784_);
lean_inc_ref(v___y_783_);
lean_inc(v___y_782_);
lean_inc(v___y_781_);
v___x_798_ = lean_apply_8(v_f_778_, v___x_797_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, lean_box(0));
return v___x_798_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(lean_object* v_fvars_799_, lean_object* v_f_800_, lean_object* v_body_801_, lean_object* v_x_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = lean_array_push(v_fvars_799_, v_x_802_);
v___x_811_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_800_, v___x_810_, v_body_801_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___boxed(lean_object* v_f_812_, lean_object* v_fvars_813_, lean_object* v_a_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_812_, v_fvars_813_, v_a_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec(v___y_815_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(lean_object* v_f_823_, lean_object* v_e_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_833_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_823_, v___x_832_, v_e_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11___boxed(lean_object* v_f_834_, lean_object* v_e_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v_f_834_, v_e_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec(v___y_836_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(lean_object* v_a_844_, lean_object* v_x_845_){
_start:
{
if (lean_obj_tag(v_x_845_) == 0)
{
lean_object* v___x_846_; 
v___x_846_ = lean_box(0);
return v___x_846_;
}
else
{
lean_object* v_key_847_; lean_object* v_value_848_; lean_object* v_tail_849_; uint8_t v___x_850_; 
v_key_847_ = lean_ctor_get(v_x_845_, 0);
v_value_848_ = lean_ctor_get(v_x_845_, 1);
v_tail_849_ = lean_ctor_get(v_x_845_, 2);
v___x_850_ = lean_expr_eqv(v_key_847_, v_a_844_);
if (v___x_850_ == 0)
{
v_x_845_ = v_tail_849_;
goto _start;
}
else
{
lean_object* v___x_852_; 
lean_inc(v_value_848_);
v___x_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_852_, 0, v_value_848_);
return v___x_852_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_a_853_, lean_object* v_x_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_853_, v_x_854_);
lean_dec(v_x_854_);
lean_dec_ref(v_a_853_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_m_856_, lean_object* v_a_857_){
_start:
{
lean_object* v_buckets_858_; lean_object* v___x_859_; uint64_t v___x_860_; uint64_t v___x_861_; uint64_t v___x_862_; uint64_t v_fold_863_; uint64_t v___x_864_; uint64_t v___x_865_; uint64_t v___x_866_; size_t v___x_867_; size_t v___x_868_; size_t v___x_869_; size_t v___x_870_; size_t v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v_buckets_858_ = lean_ctor_get(v_m_856_, 1);
v___x_859_ = lean_array_get_size(v_buckets_858_);
v___x_860_ = l_Lean_Expr_hash(v_a_857_);
v___x_861_ = 32ULL;
v___x_862_ = lean_uint64_shift_right(v___x_860_, v___x_861_);
v_fold_863_ = lean_uint64_xor(v___x_860_, v___x_862_);
v___x_864_ = 16ULL;
v___x_865_ = lean_uint64_shift_right(v_fold_863_, v___x_864_);
v___x_866_ = lean_uint64_xor(v_fold_863_, v___x_865_);
v___x_867_ = lean_uint64_to_usize(v___x_866_);
v___x_868_ = lean_usize_of_nat(v___x_859_);
v___x_869_ = ((size_t)1ULL);
v___x_870_ = lean_usize_sub(v___x_868_, v___x_869_);
v___x_871_ = lean_usize_land(v___x_867_, v___x_870_);
v___x_872_ = lean_array_uget_borrowed(v_buckets_858_, v___x_871_);
v___x_873_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_857_, v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_m_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_874_, v_a_875_);
lean_dec_ref(v_a_875_);
lean_dec_ref(v_m_874_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_object* v_00_u03b1_877_, lean_object* v_x_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = lean_apply_1(v_x_878_, lean_box(0));
v___x_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0___boxed(lean_object* v_00_u03b1_887_, lean_object* v_x_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(v_00_u03b1_887_, v_x_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(lean_object* v_x_896_, lean_object* v_x_897_){
_start:
{
if (lean_obj_tag(v_x_897_) == 0)
{
return v_x_896_;
}
else
{
lean_object* v_key_898_; lean_object* v_value_899_; lean_object* v_tail_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_923_; 
v_key_898_ = lean_ctor_get(v_x_897_, 0);
v_value_899_ = lean_ctor_get(v_x_897_, 1);
v_tail_900_ = lean_ctor_get(v_x_897_, 2);
v_isSharedCheck_923_ = !lean_is_exclusive(v_x_897_);
if (v_isSharedCheck_923_ == 0)
{
v___x_902_ = v_x_897_;
v_isShared_903_ = v_isSharedCheck_923_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_tail_900_);
lean_inc(v_value_899_);
lean_inc(v_key_898_);
lean_dec(v_x_897_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_923_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_904_; uint64_t v___x_905_; uint64_t v___x_906_; uint64_t v___x_907_; uint64_t v_fold_908_; uint64_t v___x_909_; uint64_t v___x_910_; uint64_t v___x_911_; size_t v___x_912_; size_t v___x_913_; size_t v___x_914_; size_t v___x_915_; size_t v___x_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_904_ = lean_array_get_size(v_x_896_);
v___x_905_ = l_Lean_Expr_hash(v_key_898_);
v___x_906_ = 32ULL;
v___x_907_ = lean_uint64_shift_right(v___x_905_, v___x_906_);
v_fold_908_ = lean_uint64_xor(v___x_905_, v___x_907_);
v___x_909_ = 16ULL;
v___x_910_ = lean_uint64_shift_right(v_fold_908_, v___x_909_);
v___x_911_ = lean_uint64_xor(v_fold_908_, v___x_910_);
v___x_912_ = lean_uint64_to_usize(v___x_911_);
v___x_913_ = lean_usize_of_nat(v___x_904_);
v___x_914_ = ((size_t)1ULL);
v___x_915_ = lean_usize_sub(v___x_913_, v___x_914_);
v___x_916_ = lean_usize_land(v___x_912_, v___x_915_);
v___x_917_ = lean_array_uget_borrowed(v_x_896_, v___x_916_);
lean_inc(v___x_917_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 2, v___x_917_);
v___x_919_ = v___x_902_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_key_898_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_value_899_);
lean_ctor_set(v_reuseFailAlloc_922_, 2, v___x_917_);
v___x_919_ = v_reuseFailAlloc_922_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_920_; 
v___x_920_ = lean_array_uset(v_x_896_, v___x_916_, v___x_919_);
v_x_896_ = v___x_920_;
v_x_897_ = v_tail_900_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(lean_object* v_i_924_, lean_object* v_source_925_, lean_object* v_target_926_){
_start:
{
lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_927_ = lean_array_get_size(v_source_925_);
v___x_928_ = lean_nat_dec_lt(v_i_924_, v___x_927_);
if (v___x_928_ == 0)
{
lean_dec_ref(v_source_925_);
lean_dec(v_i_924_);
return v_target_926_;
}
else
{
lean_object* v_es_929_; lean_object* v___x_930_; lean_object* v_source_931_; lean_object* v_target_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v_es_929_ = lean_array_fget(v_source_925_, v_i_924_);
v___x_930_ = lean_box(0);
v_source_931_ = lean_array_fset(v_source_925_, v_i_924_, v___x_930_);
v_target_932_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_target_926_, v_es_929_);
v___x_933_ = lean_unsigned_to_nat(1u);
v___x_934_ = lean_nat_add(v_i_924_, v___x_933_);
lean_dec(v_i_924_);
v_i_924_ = v___x_934_;
v_source_925_ = v_source_931_;
v_target_926_ = v_target_932_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(lean_object* v_data_936_){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v_nbuckets_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_937_ = lean_array_get_size(v_data_936_);
v___x_938_ = lean_unsigned_to_nat(2u);
v_nbuckets_939_ = lean_nat_mul(v___x_937_, v___x_938_);
v___x_940_ = lean_unsigned_to_nat(0u);
v___x_941_ = lean_box(0);
v___x_942_ = lean_mk_array(v_nbuckets_939_, v___x_941_);
v___x_943_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v___x_940_, v_data_936_, v___x_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(lean_object* v_a_944_, lean_object* v_b_945_, lean_object* v_x_946_){
_start:
{
if (lean_obj_tag(v_x_946_) == 0)
{
lean_dec(v_b_945_);
lean_dec_ref(v_a_944_);
return v_x_946_;
}
else
{
lean_object* v_key_947_; lean_object* v_value_948_; lean_object* v_tail_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_961_; 
v_key_947_ = lean_ctor_get(v_x_946_, 0);
v_value_948_ = lean_ctor_get(v_x_946_, 1);
v_tail_949_ = lean_ctor_get(v_x_946_, 2);
v_isSharedCheck_961_ = !lean_is_exclusive(v_x_946_);
if (v_isSharedCheck_961_ == 0)
{
v___x_951_ = v_x_946_;
v_isShared_952_ = v_isSharedCheck_961_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_tail_949_);
lean_inc(v_value_948_);
lean_inc(v_key_947_);
lean_dec(v_x_946_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_961_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
uint8_t v___x_953_; 
v___x_953_ = lean_expr_eqv(v_key_947_, v_a_944_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; lean_object* v___x_956_; 
v___x_954_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_944_, v_b_945_, v_tail_949_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 2, v___x_954_);
v___x_956_ = v___x_951_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_key_947_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_value_948_);
lean_ctor_set(v_reuseFailAlloc_957_, 2, v___x_954_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
else
{
lean_object* v___x_959_; 
lean_dec(v_value_948_);
lean_dec(v_key_947_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 1, v_b_945_);
lean_ctor_set(v___x_951_, 0, v_a_944_);
v___x_959_ = v___x_951_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_944_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_b_945_);
lean_ctor_set(v_reuseFailAlloc_960_, 2, v_tail_949_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(lean_object* v_a_962_, lean_object* v_x_963_){
_start:
{
if (lean_obj_tag(v_x_963_) == 0)
{
uint8_t v___x_964_; 
v___x_964_ = 0;
return v___x_964_;
}
else
{
lean_object* v_key_965_; lean_object* v_tail_966_; uint8_t v___x_967_; 
v_key_965_ = lean_ctor_get(v_x_963_, 0);
v_tail_966_ = lean_ctor_get(v_x_963_, 2);
v___x_967_ = lean_expr_eqv(v_key_965_, v_a_962_);
if (v___x_967_ == 0)
{
v_x_963_ = v_tail_966_;
goto _start;
}
else
{
return v___x_967_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg___boxed(lean_object* v_a_969_, lean_object* v_x_970_){
_start:
{
uint8_t v_res_971_; lean_object* v_r_972_; 
v_res_971_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_969_, v_x_970_);
lean_dec(v_x_970_);
lean_dec_ref(v_a_969_);
v_r_972_ = lean_box(v_res_971_);
return v_r_972_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(lean_object* v_m_973_, lean_object* v_a_974_, lean_object* v_b_975_){
_start:
{
lean_object* v_size_976_; lean_object* v_buckets_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_1020_; 
v_size_976_ = lean_ctor_get(v_m_973_, 0);
v_buckets_977_ = lean_ctor_get(v_m_973_, 1);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_m_973_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_979_ = v_m_973_;
v_isShared_980_ = v_isSharedCheck_1020_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_buckets_977_);
lean_inc(v_size_976_);
lean_dec(v_m_973_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_1020_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_981_; uint64_t v___x_982_; uint64_t v___x_983_; uint64_t v___x_984_; uint64_t v_fold_985_; uint64_t v___x_986_; uint64_t v___x_987_; uint64_t v___x_988_; size_t v___x_989_; size_t v___x_990_; size_t v___x_991_; size_t v___x_992_; size_t v___x_993_; lean_object* v_bkt_994_; uint8_t v___x_995_; 
v___x_981_ = lean_array_get_size(v_buckets_977_);
v___x_982_ = l_Lean_Expr_hash(v_a_974_);
v___x_983_ = 32ULL;
v___x_984_ = lean_uint64_shift_right(v___x_982_, v___x_983_);
v_fold_985_ = lean_uint64_xor(v___x_982_, v___x_984_);
v___x_986_ = 16ULL;
v___x_987_ = lean_uint64_shift_right(v_fold_985_, v___x_986_);
v___x_988_ = lean_uint64_xor(v_fold_985_, v___x_987_);
v___x_989_ = lean_uint64_to_usize(v___x_988_);
v___x_990_ = lean_usize_of_nat(v___x_981_);
v___x_991_ = ((size_t)1ULL);
v___x_992_ = lean_usize_sub(v___x_990_, v___x_991_);
v___x_993_ = lean_usize_land(v___x_989_, v___x_992_);
v_bkt_994_ = lean_array_uget_borrowed(v_buckets_977_, v___x_993_);
v___x_995_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_974_, v_bkt_994_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; lean_object* v_size_x27_997_; lean_object* v___x_998_; lean_object* v_buckets_x27_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_996_ = lean_unsigned_to_nat(1u);
v_size_x27_997_ = lean_nat_add(v_size_976_, v___x_996_);
lean_dec(v_size_976_);
lean_inc(v_bkt_994_);
v___x_998_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_998_, 0, v_a_974_);
lean_ctor_set(v___x_998_, 1, v_b_975_);
lean_ctor_set(v___x_998_, 2, v_bkt_994_);
v_buckets_x27_999_ = lean_array_uset(v_buckets_977_, v___x_993_, v___x_998_);
v___x_1000_ = lean_unsigned_to_nat(4u);
v___x_1001_ = lean_nat_mul(v_size_x27_997_, v___x_1000_);
v___x_1002_ = lean_unsigned_to_nat(3u);
v___x_1003_ = lean_nat_div(v___x_1001_, v___x_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = lean_array_get_size(v_buckets_x27_999_);
v___x_1005_ = lean_nat_dec_le(v___x_1003_, v___x_1004_);
lean_dec(v___x_1003_);
if (v___x_1005_ == 0)
{
lean_object* v_val_1006_; lean_object* v___x_1008_; 
v_val_1006_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_buckets_x27_999_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 1, v_val_1006_);
lean_ctor_set(v___x_979_, 0, v_size_x27_997_);
v___x_1008_ = v___x_979_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_size_x27_997_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_val_1006_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
else
{
lean_object* v___x_1011_; 
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 1, v_buckets_x27_999_);
lean_ctor_set(v___x_979_, 0, v_size_x27_997_);
v___x_1011_ = v___x_979_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_size_x27_997_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_buckets_x27_999_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
else
{
lean_object* v___x_1013_; lean_object* v_buckets_x27_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1018_; 
lean_inc(v_bkt_994_);
v___x_1013_ = lean_box(0);
v_buckets_x27_1014_ = lean_array_uset(v_buckets_977_, v___x_993_, v___x_1013_);
v___x_1015_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_974_, v_b_975_, v_bkt_994_);
v___x_1016_ = lean_array_uset(v_buckets_x27_1014_, v___x_993_, v___x_1015_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 1, v___x_1016_);
v___x_1018_ = v___x_979_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_size_976_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(lean_object* v_a_1021_, lean_object* v_e_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1025_ = lean_st_ref_take(v_a_1021_);
v___x_1026_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v___x_1025_, v_e_1022_, v_a_1023_);
v___x_1027_ = lean_st_ref_set(v_a_1021_, v___x_1026_);
v___x_1028_ = lean_box(0);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed(lean_object* v_a_1029_, lean_object* v_e_1030_, lean_object* v_a_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(v_a_1029_, v_e_1030_, v_a_1031_);
lean_dec(v_a_1029_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1034_, lean_object* v_e_1035_, lean_object* v_a_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1034_, v_e_1035_, v_a_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec(v_a_1036_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(lean_object* v_fn_1044_, lean_object* v_e_1045_, lean_object* v_a_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_a_1054_; lean_object* v___y_1066_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
lean_inc(v_a_1046_);
v___x_1068_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1068_, 0, lean_box(0));
lean_closure_set(v___x_1068_, 1, lean_box(0));
lean_closure_set(v___x_1068_, 2, v_a_1046_);
v___x_1069_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___x_1068_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1106_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1106_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1106_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_a_1070_, v_e_1045_);
lean_dec(v_a_1070_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v___x_1075_; 
lean_del_object(v___x_1072_);
lean_inc_ref(v_fn_1044_);
lean_inc(v___y_1051_);
lean_inc_ref(v___y_1050_);
lean_inc(v___y_1049_);
lean_inc_ref(v___y_1048_);
lean_inc(v___y_1047_);
lean_inc_ref(v_e_1045_);
v___x_1075_ = lean_apply_7(v_fn_1044_, v_e_1045_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, lean_box(0));
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; uint8_t v___x_1077_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
lean_dec_ref(v___x_1075_);
v___x_1077_ = lean_unbox(v_a_1076_);
lean_dec(v_a_1076_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; 
lean_dec_ref(v_fn_1044_);
v___x_1078_ = lean_box(0);
v_a_1054_ = v___x_1078_;
goto v___jp_1053_;
}
else
{
switch(lean_obj_tag(v_e_1045_))
{
case 7:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1079_, 0, v_fn_1044_);
lean_inc_ref(v_e_1045_);
v___x_1080_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v___x_1079_, v_e_1045_, v_a_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
v___y_1066_ = v___x_1080_;
goto v___jp_1065_;
}
case 6:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1081_, 0, v_fn_1044_);
lean_inc_ref(v_e_1045_);
v___x_1082_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v___x_1081_, v_e_1045_, v_a_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
v___y_1066_ = v___x_1082_;
goto v___jp_1065_;
}
case 8:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1083_, 0, v_fn_1044_);
lean_inc_ref(v_e_1045_);
v___x_1084_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v___x_1083_, v_e_1045_, v_a_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
v___y_1066_ = v___x_1084_;
goto v___jp_1065_;
}
case 5:
{
lean_object* v_fn_1085_; lean_object* v_arg_1086_; lean_object* v___x_1087_; 
v_fn_1085_ = lean_ctor_get(v_e_1045_, 0);
v_arg_1086_ = lean_ctor_get(v_e_1045_, 1);
lean_inc_ref(v_fn_1085_);
lean_inc_ref(v_fn_1044_);
v___x_1087_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1044_, v_fn_1085_, v_a_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v___x_1088_; 
lean_dec_ref(v___x_1087_);
lean_inc_ref(v_arg_1086_);
v___x_1088_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1044_, v_arg_1086_, v_a_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
v___y_1066_ = v___x_1088_;
goto v___jp_1065_;
}
else
{
lean_dec_ref(v_fn_1044_);
v___y_1066_ = v___x_1087_;
goto v___jp_1065_;
}
}
case 10:
{
lean_object* v_expr_1089_; lean_object* v___x_1090_; 
v_expr_1089_ = lean_ctor_get(v_e_1045_, 1);
lean_inc_ref(v_expr_1089_);
v___x_1090_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1044_, v_expr_1089_, v_a_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
v___y_1066_ = v___x_1090_;
goto v___jp_1065_;
}
case 11:
{
lean_object* v_struct_1091_; lean_object* v___x_1092_; 
v_struct_1091_ = lean_ctor_get(v_e_1045_, 2);
lean_inc_ref(v_struct_1091_);
v___x_1092_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1044_, v_struct_1091_, v_a_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
v___y_1066_ = v___x_1092_;
goto v___jp_1065_;
}
default: 
{
lean_object* v___x_1093_; 
lean_dec_ref(v_fn_1044_);
v___x_1093_ = lean_box(0);
v_a_1054_ = v___x_1093_;
goto v___jp_1053_;
}
}
}
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
lean_dec_ref(v_e_1045_);
lean_dec_ref(v_fn_1044_);
v_a_1094_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1096_ = v___x_1075_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1075_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
else
{
lean_object* v_val_1102_; lean_object* v___x_1104_; 
lean_dec_ref(v_e_1045_);
lean_dec_ref(v_fn_1044_);
v_val_1102_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_val_1102_);
lean_dec_ref(v___x_1074_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v_val_1102_);
v___x_1104_ = v___x_1072_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_val_1102_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_dec_ref(v_e_1045_);
lean_dec_ref(v_fn_1044_);
v_a_1107_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1069_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1069_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
v___jp_1053_:
{
lean_object* v___f_1055_; lean_object* v___x_1056_; 
lean_inc(v_a_1046_);
v___f_1055_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1055_, 0, v_a_1046_);
lean_closure_set(v___f_1055_, 1, v_e_1045_);
lean_closure_set(v___f_1055_, 2, v_a_1054_);
v___x_1056_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___f_1055_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1063_ == 0)
{
lean_object* v_unused_1064_; 
v_unused_1064_ = lean_ctor_get(v___x_1056_, 0);
lean_dec(v_unused_1064_);
v___x_1058_ = v___x_1056_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_dec(v___x_1056_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 0, v_a_1054_);
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1054_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
else
{
return v___x_1056_;
}
}
v___jp_1065_:
{
if (lean_obj_tag(v___y_1066_) == 0)
{
lean_object* v_a_1067_; 
v_a_1067_ = lean_ctor_get(v___y_1066_, 0);
lean_inc(v_a_1067_);
lean_dec_ref(v___y_1066_);
v_a_1054_ = v_a_1067_;
goto v___jp_1053_;
}
else
{
lean_dec_ref(v_e_1045_);
return v___y_1066_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = lean_box(0);
v___x_1116_ = lean_unsigned_to_nat(16u);
v___x_1117_ = lean_mk_array(v___x_1116_, v___x_1115_);
return v___x_1117_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0);
v___x_1119_ = lean_unsigned_to_nat(0u);
v___x_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set(v___x_1120_, 1, v___x_1118_);
return v___x_1120_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1);
v___x_1122_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1122_, 0, lean_box(0));
lean_closure_set(v___x_1122_, 1, lean_box(0));
lean_closure_set(v___x_1122_, 2, v___x_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(lean_object* v_input_1123_, lean_object* v_fn_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v_a_1133_; lean_object* v___x_1134_; 
v___x_1131_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2);
v___x_1132_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1131_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_a_1133_);
lean_dec_ref(v___x_1132_);
v___x_1134_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1124_, v_input_1123_, v_a_1133_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_a_1135_);
lean_dec_ref(v___x_1134_);
v___x_1136_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1136_, 0, lean_box(0));
lean_closure_set(v___x_1136_, 1, lean_box(0));
lean_closure_set(v___x_1136_, 2, v_a_1133_);
v___x_1137_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1136_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; 
v_unused_1145_ = lean_ctor_get(v___x_1137_, 0);
lean_dec(v_unused_1145_);
v___x_1139_ = v___x_1137_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_dec(v___x_1137_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v_a_1135_);
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1135_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
else
{
lean_dec(v_a_1133_);
return v___x_1134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___boxed(lean_object* v_input_1146_, lean_object* v_fn_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1146_, v_fn_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(lean_object* v_input_1155_, lean_object* v_fn_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v___f_1163_; lean_object* v___x_1164_; 
v___f_1163_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1163_, 0, v_fn_1156_);
v___x_1164_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1155_, v___f_1163_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___boxed(lean_object* v_input_1165_, lean_object* v_fn_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_input_1165_, v_fn_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(lean_object* v_fn_1174_, lean_object* v_x_1175_, lean_object* v_x_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
if (lean_obj_tag(v_x_1176_) == 0)
{
lean_object* v___x_1183_; 
lean_dec_ref(v_fn_1174_);
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v_x_1175_);
return v___x_1183_;
}
else
{
lean_object* v_head_1184_; lean_object* v_tail_1185_; lean_object* v_type_1186_; lean_object* v___x_1187_; 
v_head_1184_ = lean_ctor_get(v_x_1176_, 0);
lean_inc(v_head_1184_);
v_tail_1185_ = lean_ctor_get(v_x_1176_, 1);
lean_inc(v_tail_1185_);
lean_dec_ref(v_x_1176_);
v_type_1186_ = lean_ctor_get(v_head_1184_, 1);
lean_inc_ref(v_type_1186_);
lean_dec(v_head_1184_);
lean_inc_ref(v_fn_1174_);
v___x_1187_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1186_, v_fn_1174_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1188_);
lean_dec_ref(v___x_1187_);
v_x_1175_ = v_a_1188_;
v_x_1176_ = v_tail_1185_;
goto _start;
}
else
{
lean_dec(v_tail_1185_);
lean_dec_ref(v_fn_1174_);
return v___x_1187_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4___boxed(lean_object* v_fn_1190_, lean_object* v_x_1191_, lean_object* v_x_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1190_, v_x_1191_, v_x_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(lean_object* v_fn_1200_, lean_object* v_x_1201_, lean_object* v_x_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
if (lean_obj_tag(v_x_1202_) == 0)
{
lean_object* v___x_1209_; 
lean_dec_ref(v_fn_1200_);
v___x_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1209_, 0, v_x_1201_);
return v___x_1209_;
}
else
{
lean_object* v_head_1210_; lean_object* v_tail_1211_; lean_object* v___y_1213_; lean_object* v_type_1216_; lean_object* v_ctors_1217_; lean_object* v___x_1218_; 
v_head_1210_ = lean_ctor_get(v_x_1202_, 0);
lean_inc(v_head_1210_);
v_tail_1211_ = lean_ctor_get(v_x_1202_, 1);
lean_inc(v_tail_1211_);
lean_dec_ref(v_x_1202_);
v_type_1216_ = lean_ctor_get(v_head_1210_, 1);
lean_inc_ref(v_type_1216_);
v_ctors_1217_ = lean_ctor_get(v_head_1210_, 2);
lean_inc(v_ctors_1217_);
lean_dec(v_head_1210_);
lean_inc_ref(v_fn_1200_);
v___x_1218_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1216_, v_fn_1200_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1220_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_a_1219_);
lean_dec_ref(v___x_1218_);
lean_inc_ref(v_fn_1200_);
v___x_1220_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1200_, v_a_1219_, v_ctors_1217_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
v___y_1213_ = v___x_1220_;
goto v___jp_1212_;
}
else
{
lean_dec(v_ctors_1217_);
v___y_1213_ = v___x_1218_;
goto v___jp_1212_;
}
v___jp_1212_:
{
if (lean_obj_tag(v___y_1213_) == 0)
{
lean_object* v_a_1214_; 
v_a_1214_ = lean_ctor_get(v___y_1213_, 0);
lean_inc(v_a_1214_);
lean_dec_ref(v___y_1213_);
v_x_1201_ = v_a_1214_;
v_x_1202_ = v_tail_1211_;
goto _start;
}
else
{
lean_dec(v_tail_1211_);
lean_dec_ref(v_fn_1200_);
return v___y_1213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6___boxed(lean_object* v_fn_1221_, lean_object* v_x_1222_, lean_object* v_x_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1221_, v_x_1222_, v_x_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(lean_object* v_fn_1231_, lean_object* v_x_1232_, lean_object* v_x_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
if (lean_obj_tag(v_x_1233_) == 0)
{
lean_object* v___x_1240_; 
lean_dec_ref(v_fn_1231_);
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v_x_1232_);
return v___x_1240_;
}
else
{
lean_object* v_head_1241_; lean_object* v_tail_1242_; lean_object* v___y_1244_; lean_object* v_toConstantVal_1247_; lean_object* v_value_1248_; lean_object* v_type_1249_; lean_object* v___x_1250_; 
v_head_1241_ = lean_ctor_get(v_x_1233_, 0);
lean_inc(v_head_1241_);
v_tail_1242_ = lean_ctor_get(v_x_1233_, 1);
lean_inc(v_tail_1242_);
lean_dec_ref(v_x_1233_);
v_toConstantVal_1247_ = lean_ctor_get(v_head_1241_, 0);
lean_inc_ref(v_toConstantVal_1247_);
v_value_1248_ = lean_ctor_get(v_head_1241_, 1);
lean_inc_ref(v_value_1248_);
lean_dec(v_head_1241_);
v_type_1249_ = lean_ctor_get(v_toConstantVal_1247_, 2);
lean_inc_ref(v_type_1249_);
lean_dec_ref(v_toConstantVal_1247_);
lean_inc_ref(v_fn_1231_);
v___x_1250_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1249_, v_fn_1231_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v___x_1251_; 
lean_dec_ref(v___x_1250_);
lean_inc_ref(v_fn_1231_);
v___x_1251_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1248_, v_fn_1231_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
v___y_1244_ = v___x_1251_;
goto v___jp_1243_;
}
else
{
lean_dec_ref(v_value_1248_);
v___y_1244_ = v___x_1250_;
goto v___jp_1243_;
}
v___jp_1243_:
{
if (lean_obj_tag(v___y_1244_) == 0)
{
lean_object* v_a_1245_; 
v_a_1245_ = lean_ctor_get(v___y_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref(v___y_1244_);
v_x_1232_ = v_a_1245_;
v_x_1233_ = v_tail_1242_;
goto _start;
}
else
{
lean_dec(v_tail_1242_);
lean_dec_ref(v_fn_1231_);
return v___y_1244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1252_, lean_object* v_x_1253_, lean_object* v_x_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1252_, v_x_1253_, v_x_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(lean_object* v_fn_1262_, lean_object* v_d_1263_, lean_object* v_a_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
switch(lean_obj_tag(v_d_1263_))
{
case 0:
{
lean_object* v_val_1271_; lean_object* v_toConstantVal_1272_; lean_object* v_type_1273_; lean_object* v___x_1274_; 
v_val_1271_ = lean_ctor_get(v_d_1263_, 0);
lean_inc_ref(v_val_1271_);
lean_dec_ref(v_d_1263_);
v_toConstantVal_1272_ = lean_ctor_get(v_val_1271_, 0);
lean_inc_ref(v_toConstantVal_1272_);
lean_dec_ref(v_val_1271_);
v_type_1273_ = lean_ctor_get(v_toConstantVal_1272_, 2);
lean_inc_ref(v_type_1273_);
lean_dec_ref(v_toConstantVal_1272_);
v___x_1274_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1273_, v_fn_1262_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
return v___x_1274_;
}
case 4:
{
lean_object* v___x_1275_; 
lean_dec_ref(v_fn_1262_);
v___x_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1275_, 0, v_a_1264_);
return v___x_1275_;
}
case 5:
{
lean_object* v_defns_1276_; lean_object* v___x_1277_; 
v_defns_1276_ = lean_ctor_get(v_d_1263_, 0);
lean_inc(v_defns_1276_);
lean_dec_ref(v_d_1263_);
v___x_1277_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1262_, v_a_1264_, v_defns_1276_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
return v___x_1277_;
}
case 6:
{
lean_object* v_types_1278_; lean_object* v___x_1279_; 
v_types_1278_ = lean_ctor_get(v_d_1263_, 2);
lean_inc(v_types_1278_);
lean_dec_ref(v_d_1263_);
v___x_1279_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1262_, v_a_1264_, v_types_1278_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
return v___x_1279_;
}
default: 
{
lean_object* v_val_1280_; lean_object* v_toConstantVal_1281_; lean_object* v_value_1282_; lean_object* v_type_1283_; lean_object* v___x_1284_; 
v_val_1280_ = lean_ctor_get(v_d_1263_, 0);
lean_inc_ref(v_val_1280_);
lean_dec(v_d_1263_);
v_toConstantVal_1281_ = lean_ctor_get(v_val_1280_, 0);
lean_inc_ref(v_toConstantVal_1281_);
v_value_1282_ = lean_ctor_get(v_val_1280_, 1);
lean_inc_ref(v_value_1282_);
lean_dec_ref(v_val_1280_);
v_type_1283_ = lean_ctor_get(v_toConstantVal_1281_, 2);
lean_inc_ref(v_type_1283_);
lean_dec_ref(v_toConstantVal_1281_);
lean_inc_ref(v_fn_1262_);
v___x_1284_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1283_, v_fn_1262_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v___x_1285_; 
lean_dec_ref(v___x_1284_);
v___x_1285_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1282_, v_fn_1262_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
return v___x_1285_;
}
else
{
lean_dec_ref(v_value_1282_);
lean_dec_ref(v_fn_1262_);
return v___x_1284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2___boxed(lean_object* v_fn_1286_, lean_object* v_d_1287_, lean_object* v_a_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1286_, v_d_1287_, v_a_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(lean_object* v_decl_1296_, lean_object* v_fn_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = lean_box(0);
v___x_1305_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1297_, v_decl_1296_, v___x_1304_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1___boxed(lean_object* v_decl_1306_, lean_object* v_fn_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1306_, v_fn_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
return v_res_1314_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__0(void){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1315_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__1(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__0, &l_Lean_warnIfUsesSorry___closed__0_once, _init_l_Lean_warnIfUsesSorry___closed__0);
v___x_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
return v___x_1317_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__2(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1318_ = lean_box(1);
v___x_1319_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_1320_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1321_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
lean_ctor_set(v___x_1321_, 1, v___x_1319_);
lean_ctor_set(v___x_1321_, 2, v___x_1318_);
return v___x_1321_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__4(void){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1324_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1325_ = lean_unsigned_to_nat(0u);
v___x_1326_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
lean_ctor_set(v___x_1326_, 1, v___x_1325_);
lean_ctor_set(v___x_1326_, 2, v___x_1325_);
lean_ctor_set(v___x_1326_, 3, v___x_1325_);
lean_ctor_set(v___x_1326_, 4, v___x_1324_);
lean_ctor_set(v___x_1326_, 5, v___x_1324_);
lean_ctor_set(v___x_1326_, 6, v___x_1324_);
lean_ctor_set(v___x_1326_, 7, v___x_1324_);
lean_ctor_set(v___x_1326_, 8, v___x_1324_);
lean_ctor_set(v___x_1326_, 9, v___x_1324_);
return v___x_1326_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__5(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1328_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
lean_ctor_set(v___x_1328_, 2, v___x_1327_);
lean_ctor_set(v___x_1328_, 3, v___x_1327_);
lean_ctor_set(v___x_1328_, 4, v___x_1327_);
lean_ctor_set(v___x_1328_, 5, v___x_1327_);
return v___x_1328_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__6(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
lean_ctor_set(v___x_1330_, 2, v___x_1329_);
lean_ctor_set(v___x_1330_, 3, v___x_1329_);
lean_ctor_set(v___x_1330_, 4, v___x_1329_);
return v___x_1330_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__7(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1331_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__6, &l_Lean_warnIfUsesSorry___closed__6_once, _init_l_Lean_warnIfUsesSorry___closed__6);
v___x_1332_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_1333_ = lean_box(1);
v___x_1334_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__5, &l_Lean_warnIfUsesSorry___closed__5_once, _init_l_Lean_warnIfUsesSorry___closed__5);
v___x_1335_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__4, &l_Lean_warnIfUsesSorry___closed__4_once, _init_l_Lean_warnIfUsesSorry___closed__4);
v___x_1336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
lean_ctor_set(v___x_1336_, 1, v___x_1334_);
lean_ctor_set(v___x_1336_, 2, v___x_1333_);
lean_ctor_set(v___x_1336_, 3, v___x_1332_);
lean_ctor_set(v___x_1336_, 4, v___x_1331_);
return v___x_1336_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__12(void){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__11));
v___x_1343_ = l_Lean_stringToMessageData(v___x_1342_);
return v___x_1343_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__14(void){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__13));
v___x_1346_ = l_Lean_stringToMessageData(v___x_1345_);
return v___x_1346_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__16(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__15));
v___x_1349_ = l_Lean_stringToMessageData(v___x_1348_);
return v___x_1349_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__17(void){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1350_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__16, &l_Lean_warnIfUsesSorry___closed__16_once, _init_l_Lean_warnIfUsesSorry___closed__16);
v___x_1351_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__10));
v___x_1352_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
lean_ctor_set(v___x_1352_, 1, v___x_1350_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry(lean_object* v_decl_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_){
_start:
{
lean_object* v_options_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; 
v_options_1360_ = lean_ctor_get(v_a_1357_, 2);
v___x_1361_ = l_Lean_warn_sorry;
v___x_1362_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_1360_, v___x_1361_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
lean_dec(v_decl_1356_);
v___x_1363_ = lean_box(0);
v___x_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
return v___x_1364_;
}
else
{
lean_object* v___x_1365_; lean_object* v_messages_1369_; uint8_t v___x_1370_; 
v___x_1365_ = lean_st_ref_get(v_a_1358_);
v_messages_1369_ = lean_ctor_get(v___x_1365_, 6);
lean_inc_ref(v_messages_1369_);
lean_dec(v___x_1365_);
v___x_1370_ = l_Lean_MessageLog_hasErrors(v_messages_1369_);
lean_dec_ref(v_messages_1369_);
if (v___x_1370_ == 0)
{
if (v___x_1362_ == 0)
{
lean_dec(v_decl_1356_);
goto v___jp_1366_;
}
else
{
uint8_t v___x_1371_; 
v___x_1371_ = l_Lean_Declaration_hasSorry(v_decl_1356_);
if (v___x_1371_ == 0)
{
lean_dec(v_decl_1356_);
goto v___jp_1366_;
}
else
{
uint8_t v___x_1372_; uint8_t v___x_1373_; uint8_t v___x_1374_; lean_object* v___x_1375_; uint64_t v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___f_1387_; lean_object* v___x_1388_; 
v___x_1372_ = 1;
v___x_1373_ = 0;
v___x_1374_ = 2;
v___x_1375_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_1375_, 0, v___x_1370_);
lean_ctor_set_uint8(v___x_1375_, 1, v___x_1370_);
lean_ctor_set_uint8(v___x_1375_, 2, v___x_1370_);
lean_ctor_set_uint8(v___x_1375_, 3, v___x_1370_);
lean_ctor_set_uint8(v___x_1375_, 4, v___x_1370_);
lean_ctor_set_uint8(v___x_1375_, 5, v___x_1371_);
lean_ctor_set_uint8(v___x_1375_, 6, v___x_1371_);
lean_ctor_set_uint8(v___x_1375_, 7, v___x_1370_);
lean_ctor_set_uint8(v___x_1375_, 8, v___x_1371_);
lean_ctor_set_uint8(v___x_1375_, 9, v___x_1372_);
lean_ctor_set_uint8(v___x_1375_, 10, v___x_1373_);
lean_ctor_set_uint8(v___x_1375_, 11, v___x_1371_);
lean_ctor_set_uint8(v___x_1375_, 12, v___x_1371_);
lean_ctor_set_uint8(v___x_1375_, 13, v___x_1371_);
lean_ctor_set_uint8(v___x_1375_, 14, v___x_1374_);
lean_ctor_set_uint8(v___x_1375_, 15, v___x_1371_);
lean_ctor_set_uint8(v___x_1375_, 16, v___x_1371_);
lean_ctor_set_uint8(v___x_1375_, 17, v___x_1371_);
lean_ctor_set_uint8(v___x_1375_, 18, v___x_1371_);
v___x_1376_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1375_);
v___x_1377_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1377_, 0, v___x_1375_);
lean_ctor_set_uint64(v___x_1377_, sizeof(void*)*1, v___x_1376_);
v___x_1378_ = lean_box(1);
v___x_1379_ = lean_unsigned_to_nat(0u);
v___x_1380_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1381_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__3));
v___x_1382_ = lean_box(0);
v___x_1383_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1383_, 0, v___x_1377_);
lean_ctor_set(v___x_1383_, 1, v___x_1378_);
lean_ctor_set(v___x_1383_, 2, v___x_1380_);
lean_ctor_set(v___x_1383_, 3, v___x_1381_);
lean_ctor_set(v___x_1383_, 4, v___x_1382_);
lean_ctor_set(v___x_1383_, 5, v___x_1379_);
lean_ctor_set(v___x_1383_, 6, v___x_1382_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*7, v___x_1370_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*7 + 1, v___x_1370_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*7 + 2, v___x_1370_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*7 + 3, v___x_1362_);
v___x_1384_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__7, &l_Lean_warnIfUsesSorry___closed__7_once, _init_l_Lean_warnIfUsesSorry___closed__7);
v___x_1385_ = lean_st_mk_ref(v___x_1384_);
v___x_1386_ = lean_st_mk_ref(v___x_1381_);
v___f_1387_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__8));
v___x_1388_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1356_, v___f_1387_, v___x_1386_, v___x_1383_, v___x_1385_, v_a_1357_, v_a_1358_);
lean_dec_ref(v___x_1383_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v_val_1392_; lean_object* v___x_1414_; size_t v_sz_1415_; size_t v___x_1416_; lean_object* v___x_1417_; lean_object* v_fst_1418_; 
lean_dec_ref(v___x_1388_);
v___x_1389_ = lean_st_ref_get(v___x_1386_);
lean_dec(v___x_1386_);
v___x_1390_ = lean_st_ref_get(v___x_1385_);
lean_dec(v___x_1385_);
lean_dec(v___x_1390_);
v___x_1414_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__18));
v_sz_1415_ = lean_array_size(v___x_1389_);
v___x_1416_ = ((size_t)0ULL);
v___x_1417_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v___x_1389_, v_sz_1415_, v___x_1416_, v___x_1414_);
v_fst_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_fst_1418_);
lean_dec_ref(v___x_1417_);
if (lean_obj_tag(v_fst_1418_) == 0)
{
goto v___jp_1408_;
}
else
{
lean_object* v_val_1419_; 
v_val_1419_ = lean_ctor_get(v_fst_1418_, 0);
lean_inc(v_val_1419_);
lean_dec_ref(v_fst_1418_);
if (lean_obj_tag(v_val_1419_) == 0)
{
goto v___jp_1408_;
}
else
{
lean_object* v_val_1420_; 
lean_dec(v___x_1389_);
v_val_1420_ = lean_ctor_get(v_val_1419_, 0);
lean_inc(v_val_1420_);
lean_dec_ref(v_val_1419_);
v_val_1392_ = v_val_1420_;
goto v___jp_1391_;
}
}
v___jp_1391_:
{
lean_object* v_snd_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1406_; 
v_snd_1393_ = lean_ctor_get(v_val_1392_, 1);
v_isSharedCheck_1406_ = !lean_is_exclusive(v_val_1392_);
if (v_isSharedCheck_1406_ == 0)
{
lean_object* v_unused_1407_; 
v_unused_1407_ = lean_ctor_get(v_val_1392_, 0);
lean_dec(v_unused_1407_);
v___x_1395_ = v_val_1392_;
v_isShared_1396_ = v_isSharedCheck_1406_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_snd_1393_);
lean_dec(v_val_1392_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1406_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1400_; 
v___x_1397_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__10));
v___x_1398_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__12, &l_Lean_warnIfUsesSorry___closed__12_once, _init_l_Lean_warnIfUsesSorry___closed__12);
if (v_isShared_1396_ == 0)
{
lean_ctor_set_tag(v___x_1395_, 7);
lean_ctor_set(v___x_1395_, 0, v___x_1398_);
v___x_1400_ = v___x_1395_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1398_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v_snd_1393_);
v___x_1400_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1401_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__14, &l_Lean_warnIfUsesSorry___closed__14_once, _init_l_Lean_warnIfUsesSorry___closed__14);
v___x_1402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1400_);
lean_ctor_set(v___x_1402_, 1, v___x_1401_);
v___x_1403_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1397_);
lean_ctor_set(v___x_1403_, 1, v___x_1402_);
v___x_1404_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1403_, v_a_1357_, v_a_1358_);
return v___x_1404_;
}
}
}
v___jp_1408_:
{
lean_object* v___x_1409_; uint8_t v___x_1410_; 
v___x_1409_ = lean_array_get_size(v___x_1389_);
v___x_1410_ = lean_nat_dec_lt(v___x_1379_, v___x_1409_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
lean_dec(v___x_1389_);
v___x_1411_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__17, &l_Lean_warnIfUsesSorry___closed__17_once, _init_l_Lean_warnIfUsesSorry___closed__17);
v___x_1412_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1411_, v_a_1357_, v_a_1358_);
return v___x_1412_;
}
else
{
lean_object* v___x_1413_; 
v___x_1413_ = lean_array_fget(v___x_1389_, v___x_1379_);
lean_dec(v___x_1389_);
v_val_1392_ = v___x_1413_;
goto v___jp_1391_;
}
}
}
else
{
lean_dec(v___x_1386_);
lean_dec(v___x_1385_);
return v___x_1388_;
}
}
}
}
else
{
lean_dec(v_decl_1356_);
goto v___jp_1366_;
}
v___jp_1366_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = lean_box(0);
v___x_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
return v___x_1368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___boxed(lean_object* v_decl_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_warnIfUsesSorry(v_decl_1421_, v_a_1422_, v_a_1423_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1426_, lean_object* v_m_1427_, lean_object* v_a_1428_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1427_, v_a_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1430_, lean_object* v_m_1431_, lean_object* v_a_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(v_00_u03b2_1430_, v_m_1431_, v_a_1432_);
lean_dec_ref(v_a_1432_);
lean_dec_ref(v_m_1431_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_1434_, lean_object* v_m_1435_, lean_object* v_a_1436_, lean_object* v_b_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_m_1435_, v_a_1436_, v_b_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_1439_, lean_object* v_a_1440_, lean_object* v_x_1441_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1440_, v_x_1441_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1443_, lean_object* v_a_1444_, lean_object* v_x_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(v_00_u03b2_1443_, v_a_1444_, v_x_1445_);
lean_dec(v_x_1445_);
lean_dec_ref(v_a_1444_);
return v_res_1446_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(lean_object* v_00_u03b2_1447_, lean_object* v_a_1448_, lean_object* v_x_1449_){
_start:
{
uint8_t v___x_1450_; 
v___x_1450_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1448_, v_x_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___boxed(lean_object* v_00_u03b2_1451_, lean_object* v_a_1452_, lean_object* v_x_1453_){
_start:
{
uint8_t v_res_1454_; lean_object* v_r_1455_; 
v_res_1454_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(v_00_u03b2_1451_, v_a_1452_, v_x_1453_);
lean_dec(v_x_1453_);
lean_dec_ref(v_a_1452_);
v_r_1455_ = lean_box(v_res_1454_);
return v_r_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17(lean_object* v_00_u03b2_1456_, lean_object* v_data_1457_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_data_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18(lean_object* v_00_u03b2_1459_, lean_object* v_a_1460_, lean_object* v_b_1461_, lean_object* v_x_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1460_, v_b_1461_, v_x_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(lean_object* v_00_u03b1_1464_, lean_object* v_name_1465_, uint8_t v_bi_1466_, lean_object* v_type_1467_, lean_object* v_k_1468_, uint8_t v_kind_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v___x_1477_; 
v___x_1477_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_1465_, v_bi_1466_, v_type_1467_, v_k_1468_, v_kind_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___boxed(lean_object* v_00_u03b1_1478_, lean_object* v_name_1479_, lean_object* v_bi_1480_, lean_object* v_type_1481_, lean_object* v_k_1482_, lean_object* v_kind_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
uint8_t v_bi_boxed_1491_; uint8_t v_kind_boxed_1492_; lean_object* v_res_1493_; 
v_bi_boxed_1491_ = lean_unbox(v_bi_1480_);
v_kind_boxed_1492_ = lean_unbox(v_kind_1483_);
v_res_1493_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(v_00_u03b1_1478_, v_name_1479_, v_bi_boxed_1491_, v_type_1481_, v_k_1482_, v_kind_boxed_1492_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec(v___y_1484_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(lean_object* v_00_u03b1_1494_, lean_object* v_name_1495_, lean_object* v_type_1496_, lean_object* v_val_1497_, lean_object* v_k_1498_, uint8_t v_nondep_1499_, uint8_t v_kind_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_1495_, v_type_1496_, v_val_1497_, v_k_1498_, v_nondep_1499_, v_kind_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___boxed(lean_object* v_00_u03b1_1509_, lean_object* v_name_1510_, lean_object* v_type_1511_, lean_object* v_val_1512_, lean_object* v_k_1513_, lean_object* v_nondep_1514_, lean_object* v_kind_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
uint8_t v_nondep_boxed_1523_; uint8_t v_kind_boxed_1524_; lean_object* v_res_1525_; 
v_nondep_boxed_1523_ = lean_unbox(v_nondep_1514_);
v_kind_boxed_1524_ = lean_unbox(v_kind_1515_);
v_res_1525_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(v_00_u03b1_1509_, v_name_1510_, v_type_1511_, v_val_1512_, v_k_1513_, v_nondep_boxed_1523_, v_kind_boxed_1524_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec(v___y_1516_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18(lean_object* v_00_u03b2_1526_, lean_object* v_i_1527_, lean_object* v_source_1528_, lean_object* v_target_1529_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v_i_1527_, v_source_1528_, v_target_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22(lean_object* v_00_u03b2_1531_, lean_object* v_x_1532_, lean_object* v_x_1533_){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_x_1532_, v_x_1533_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1584_; uint8_t v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1584_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1585_ = 0;
v___x_1586_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__20_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1587_ = l_Lean_registerTraceClass(v___x_1584_, v___x_1585_, v___x_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2____boxed(lean_object* v_a_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_();
return v_res_1589_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1590_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__0);
v___x_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
return v___x_1592_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__1);
v___x_1594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(lean_object* v_env_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v___x_1598_; lean_object* v_nextMacroScope_1599_; lean_object* v_ngen_1600_; lean_object* v_auxDeclNGen_1601_; lean_object* v_traceState_1602_; lean_object* v_messages_1603_; lean_object* v_infoState_1604_; lean_object* v_snapshotTasks_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1616_; 
v___x_1598_ = lean_st_ref_take(v___y_1596_);
v_nextMacroScope_1599_ = lean_ctor_get(v___x_1598_, 1);
v_ngen_1600_ = lean_ctor_get(v___x_1598_, 2);
v_auxDeclNGen_1601_ = lean_ctor_get(v___x_1598_, 3);
v_traceState_1602_ = lean_ctor_get(v___x_1598_, 4);
v_messages_1603_ = lean_ctor_get(v___x_1598_, 6);
v_infoState_1604_ = lean_ctor_get(v___x_1598_, 7);
v_snapshotTasks_1605_ = lean_ctor_get(v___x_1598_, 8);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1616_ == 0)
{
lean_object* v_unused_1617_; lean_object* v_unused_1618_; 
v_unused_1617_ = lean_ctor_get(v___x_1598_, 5);
lean_dec(v_unused_1617_);
v_unused_1618_ = lean_ctor_get(v___x_1598_, 0);
lean_dec(v_unused_1618_);
v___x_1607_ = v___x_1598_;
v_isShared_1608_ = v_isSharedCheck_1616_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_snapshotTasks_1605_);
lean_inc(v_infoState_1604_);
lean_inc(v_messages_1603_);
lean_inc(v_traceState_1602_);
lean_inc(v_auxDeclNGen_1601_);
lean_inc(v_ngen_1600_);
lean_inc(v_nextMacroScope_1599_);
lean_dec(v___x_1598_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1616_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1609_; lean_object* v___x_1611_; 
v___x_1609_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 5, v___x_1609_);
lean_ctor_set(v___x_1607_, 0, v_env_1595_);
v___x_1611_ = v___x_1607_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_env_1595_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_nextMacroScope_1599_);
lean_ctor_set(v_reuseFailAlloc_1615_, 2, v_ngen_1600_);
lean_ctor_set(v_reuseFailAlloc_1615_, 3, v_auxDeclNGen_1601_);
lean_ctor_set(v_reuseFailAlloc_1615_, 4, v_traceState_1602_);
lean_ctor_set(v_reuseFailAlloc_1615_, 5, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1615_, 6, v_messages_1603_);
lean_ctor_set(v_reuseFailAlloc_1615_, 7, v_infoState_1604_);
lean_ctor_set(v_reuseFailAlloc_1615_, 8, v_snapshotTasks_1605_);
v___x_1611_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1612_ = lean_st_ref_set(v___y_1596_, v___x_1611_);
v___x_1613_ = lean_box(0);
v___x_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
return v___x_1614_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___boxed(lean_object* v_env_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_env_1619_, v___y_1620_);
lean_dec(v___y_1620_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1(lean_object* v_env_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_env_1623_, v___y_1625_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___boxed(lean_object* v_env_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1(v_env_1628_, v___y_1629_, v___y_1630_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2___redArg(lean_object* v_msg_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v_ref_1637_; lean_object* v___x_1638_; lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1647_; 
v_ref_1637_ = lean_ctor_get(v___y_1634_, 5);
v___x_1638_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_1633_, v___y_1634_, v___y_1635_);
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1641_ = v___x_1638_;
v_isShared_1642_ = v_isSharedCheck_1647_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1638_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1647_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1643_; lean_object* v___x_1645_; 
lean_inc(v_ref_1637_);
v___x_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1643_, 0, v_ref_1637_);
lean_ctor_set(v___x_1643_, 1, v_a_1639_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set_tag(v___x_1641_, 1);
lean_ctor_set(v___x_1641_, 0, v___x_1643_);
v___x_1645_ = v___x_1641_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msg_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_1648_, v___y_1649_, v___y_1650_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
return v_res_1652_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1653_ = lean_box(0);
v___x_1654_ = l_Lean_interruptExceptionId;
v___x_1655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
lean_ctor_set(v___x_1655_, 1, v___x_1653_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg(){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1657_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v___y_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(lean_object* v_ex_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v___y_1666_; lean_object* v___y_1667_; 
if (lean_obj_tag(v_ex_1661_) == 16)
{
lean_object* v___x_1671_; lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
v___x_1671_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg();
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1671_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1671_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
else
{
v___y_1666_ = v___y_1662_;
v___y_1667_ = v___y_1663_;
goto v___jp_1665_;
}
v___jp_1665_:
{
lean_object* v_options_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v_options_1668_ = lean_ctor_get(v___y_1666_, 2);
lean_inc_ref(v_options_1668_);
v___x_1669_ = l_Lean_Kernel_Exception_toMessageData(v_ex_1661_, v_options_1668_);
v___x_1670_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2___redArg(v___x_1669_, v___y_1666_, v___y_1667_);
return v___x_1670_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg___boxed(lean_object* v_ex_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(v_ex_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(lean_object* v_x_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
if (lean_obj_tag(v_x_1685_) == 0)
{
lean_object* v_a_1689_; lean_object* v___x_1690_; 
v_a_1689_ = lean_ctor_get(v_x_1685_, 0);
lean_inc(v_a_1689_);
lean_dec_ref(v_x_1685_);
v___x_1690_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(v_a_1689_, v___y_1686_, v___y_1687_);
return v___x_1690_;
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
v_a_1691_ = lean_ctor_get(v_x_1685_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_x_1685_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v_x_1685_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v_x_1685_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
lean_ctor_set_tag(v___x_1693_, 0);
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg___boxed(lean_object* v_x_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v_x_1699_, v___y_1700_, v___y_1701_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
return v_res_1703_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = lean_unsigned_to_nat(1u);
v___x_1705_ = l_Lean_Level_ofNat(v___x_1704_);
return v___x_1705_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1706_ = lean_box(0);
v___x_1707_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__0);
v___x_1708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
lean_ctor_set(v___x_1708_, 1, v___x_1706_);
return v___x_1708_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1715_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__1);
v___x_1716_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__4));
v___x_1717_ = l_Lean_mkConst(v___x_1716_, v___x_1715_);
return v___x_1717_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1718_ = lean_unsigned_to_nat(0u);
v___x_1719_ = l_Lean_Level_ofNat(v___x_1718_);
return v___x_1719_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1720_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__6);
v___x_1721_ = l_Lean_mkSort(v___x_1720_);
return v___x_1721_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__11(void){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1727_ = lean_box(0);
v___x_1728_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__10));
v___x_1729_ = l_Lean_mkConst(v___x_1728_, v___x_1727_);
return v___x_1729_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__12(void){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1730_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__11);
v___x_1731_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__7);
v___x_1732_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__5);
v___x_1733_ = l_Lean_mkAppB(v___x_1732_, v___x_1731_, v___x_1730_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg(lean_object* v_as_x27_1739_, lean_object* v_b_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
if (lean_obj_tag(v_as_x27_1739_) == 0)
{
lean_object* v___x_1744_; 
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v_b_1740_);
return v___x_1744_;
}
else
{
lean_object* v_head_1745_; lean_object* v_tail_1746_; lean_object* v___x_1747_; lean_object* v_env_1748_; lean_object* v_options_1749_; lean_object* v_cancelTk_x3f_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___y_1754_; uint8_t v___y_1755_; lean_object* v_a_1759_; lean_object* v___x_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
lean_dec_ref(v_b_1740_);
v_head_1745_ = lean_ctor_get(v_as_x27_1739_, 0);
v_tail_1746_ = lean_ctor_get(v_as_x27_1739_, 1);
v___x_1747_ = lean_st_ref_get(v___y_1742_);
v_env_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc_ref(v_env_1748_);
lean_dec(v___x_1747_);
v_options_1749_ = lean_ctor_get(v___y_1741_, 2);
v_cancelTk_x3f_1750_ = lean_ctor_get(v___y_1741_, 12);
v___x_1751_ = lean_box(0);
v___x_1752_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__2));
v___x_1762_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__12, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__12_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__12);
lean_inc(v_head_1745_);
v___x_1763_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1763_, 0, v_head_1745_);
lean_ctor_set(v___x_1763_, 1, v___x_1751_);
lean_ctor_set(v___x_1763_, 2, v___x_1762_);
v___x_1764_ = 0;
v___x_1765_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1765_, 0, v___x_1763_);
lean_ctor_set_uint8(v___x_1765_, sizeof(void*)*1, v___x_1764_);
v___x_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1765_);
v___x_1767_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_1748_, v_options_1749_, v___x_1766_, v_cancelTk_x3f_1750_);
lean_dec_ref(v___x_1766_);
v___x_1768_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_1767_, v___y_1741_, v___y_1742_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1778_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref(v___x_1768_);
v___x_1770_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_1769_, v___y_1742_);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1778_ == 0)
{
lean_object* v_unused_1779_; 
v_unused_1779_ = lean_ctor_get(v___x_1770_, 0);
lean_dec(v_unused_1779_);
v___x_1772_ = v___x_1770_;
v_isShared_1773_ = v_isSharedCheck_1778_;
goto v_resetjp_1771_;
}
else
{
lean_dec(v___x_1770_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1778_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1774_; lean_object* v___x_1776_; 
v___x_1774_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__14));
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v___x_1774_);
v___x_1776_ = v___x_1772_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1780_; 
v_a_1780_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1780_);
lean_dec_ref(v___x_1768_);
v_a_1759_ = v_a_1780_;
goto v___jp_1758_;
}
v___jp_1753_:
{
if (v___y_1755_ == 0)
{
lean_dec_ref(v___y_1754_);
v_as_x27_1739_ = v_tail_1746_;
v_b_1740_ = v___x_1752_;
goto _start;
}
else
{
lean_object* v___x_1757_; 
v___x_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1757_, 0, v___y_1754_);
return v___x_1757_;
}
}
v___jp_1758_:
{
uint8_t v___x_1760_; 
v___x_1760_ = l_Lean_Exception_isInterrupt(v_a_1759_);
if (v___x_1760_ == 0)
{
uint8_t v___x_1761_; 
lean_inc_ref(v_a_1759_);
v___x_1761_ = l_Lean_Exception_isRuntime(v_a_1759_);
v___y_1754_ = v_a_1759_;
v___y_1755_ = v___x_1761_;
goto v___jp_1753_;
}
else
{
v___y_1754_ = v_a_1759_;
v___y_1755_ = v___x_1760_;
goto v___jp_1753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___boxed(lean_object* v_as_x27_1781_, lean_object* v_b_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg(v_as_x27_1781_, v_b_1782_, v___y_1783_, v___y_1784_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v_as_x27_1781_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom(lean_object* v_decl_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_){
_start:
{
lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1820_; uint8_t v___y_1821_; lean_object* v_a_1824_; lean_object* v___y_1828_; uint8_t v___y_1829_; lean_object* v_a_1832_; 
switch(lean_obj_tag(v_decl_1787_))
{
case 1:
{
lean_object* v_val_1835_; lean_object* v___x_1836_; lean_object* v_toConstantVal_1837_; lean_object* v_env_1838_; lean_object* v_options_1839_; lean_object* v_cancelTk_x3f_1840_; uint8_t v___x_1841_; lean_object* v___x_1842_; lean_object* v_fallbackDecl_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v_val_1835_ = lean_ctor_get(v_decl_1787_, 0);
v___x_1836_ = lean_st_ref_get(v_a_1789_);
v_toConstantVal_1837_ = lean_ctor_get(v_val_1835_, 0);
v_env_1838_ = lean_ctor_get(v___x_1836_, 0);
lean_inc_ref(v_env_1838_);
lean_dec(v___x_1836_);
v_options_1839_ = lean_ctor_get(v_a_1788_, 2);
v_cancelTk_x3f_1840_ = lean_ctor_get(v_a_1788_, 12);
v___x_1841_ = 0;
lean_inc_ref(v_toConstantVal_1837_);
v___x_1842_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1842_, 0, v_toConstantVal_1837_);
lean_ctor_set_uint8(v___x_1842_, sizeof(void*)*1, v___x_1841_);
v_fallbackDecl_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_1843_, 0, v___x_1842_);
v___x_1844_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_1838_, v_options_1839_, v_fallbackDecl_1843_, v_cancelTk_x3f_1840_);
lean_dec_ref(v_fallbackDecl_1843_);
v___x_1845_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_1844_, v_a_1788_, v_a_1789_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1855_; 
lean_dec_ref(v_decl_1787_);
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1846_);
lean_dec_ref(v___x_1845_);
v___x_1847_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_1846_, v_a_1789_);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1855_ == 0)
{
lean_object* v_unused_1856_; 
v_unused_1856_ = lean_ctor_get(v___x_1847_, 0);
lean_dec(v_unused_1856_);
v___x_1849_ = v___x_1847_;
v_isShared_1850_ = v_isSharedCheck_1855_;
goto v_resetjp_1848_;
}
else
{
lean_dec(v___x_1847_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1855_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1851_; lean_object* v___x_1853_; 
v___x_1851_ = lean_box(0);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v___x_1851_);
v___x_1853_ = v___x_1849_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
else
{
lean_object* v_a_1857_; 
v_a_1857_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1857_);
lean_dec_ref(v___x_1845_);
v_a_1824_ = v_a_1857_;
goto v___jp_1823_;
}
}
case 2:
{
lean_object* v_val_1858_; lean_object* v___x_1859_; lean_object* v_toConstantVal_1860_; lean_object* v_env_1861_; lean_object* v_options_1862_; lean_object* v_cancelTk_x3f_1863_; uint8_t v___x_1864_; lean_object* v___x_1865_; lean_object* v_fallbackDecl_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v_val_1858_ = lean_ctor_get(v_decl_1787_, 0);
v___x_1859_ = lean_st_ref_get(v_a_1789_);
v_toConstantVal_1860_ = lean_ctor_get(v_val_1858_, 0);
v_env_1861_ = lean_ctor_get(v___x_1859_, 0);
lean_inc_ref(v_env_1861_);
lean_dec(v___x_1859_);
v_options_1862_ = lean_ctor_get(v_a_1788_, 2);
v_cancelTk_x3f_1863_ = lean_ctor_get(v_a_1788_, 12);
v___x_1864_ = 0;
lean_inc_ref(v_toConstantVal_1860_);
v___x_1865_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1865_, 0, v_toConstantVal_1860_);
lean_ctor_set_uint8(v___x_1865_, sizeof(void*)*1, v___x_1864_);
v_fallbackDecl_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_1866_, 0, v___x_1865_);
v___x_1867_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_1861_, v_options_1862_, v_fallbackDecl_1866_, v_cancelTk_x3f_1863_);
lean_dec_ref(v_fallbackDecl_1866_);
v___x_1868_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_1867_, v_a_1788_, v_a_1789_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1878_; 
lean_dec_ref(v_decl_1787_);
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_a_1869_);
lean_dec_ref(v___x_1868_);
v___x_1870_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_1869_, v_a_1789_);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1878_ == 0)
{
lean_object* v_unused_1879_; 
v_unused_1879_ = lean_ctor_get(v___x_1870_, 0);
lean_dec(v_unused_1879_);
v___x_1872_ = v___x_1870_;
v_isShared_1873_ = v_isSharedCheck_1878_;
goto v_resetjp_1871_;
}
else
{
lean_dec(v___x_1870_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1878_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1874_; lean_object* v___x_1876_; 
v___x_1874_ = lean_box(0);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v___x_1874_);
v___x_1876_ = v___x_1872_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
else
{
lean_object* v_a_1880_; 
v_a_1880_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_a_1880_);
lean_dec_ref(v___x_1868_);
v_a_1832_ = v_a_1880_;
goto v___jp_1831_;
}
}
default: 
{
v___y_1792_ = v_a_1788_;
v___y_1793_ = v_a_1789_;
goto v___jp_1791_;
}
}
v___jp_1791_:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1794_ = l_Lean_Declaration_getNames(v_decl_1787_);
v___x_1795_ = lean_box(0);
v___x_1796_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg___closed__2));
v___x_1797_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg(v___x_1794_, v___x_1796_, v___y_1792_, v___y_1793_);
lean_dec(v___x_1794_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1810_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1810_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1810_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v_fst_1802_; 
v_fst_1802_ = lean_ctor_get(v_a_1798_, 0);
lean_inc(v_fst_1802_);
lean_dec(v_a_1798_);
if (lean_obj_tag(v_fst_1802_) == 0)
{
lean_object* v___x_1804_; 
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1795_);
v___x_1804_ = v___x_1800_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1795_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
else
{
lean_object* v_val_1806_; lean_object* v___x_1808_; 
v_val_1806_ = lean_ctor_get(v_fst_1802_, 0);
lean_inc(v_val_1806_);
lean_dec_ref(v_fst_1802_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v_val_1806_);
v___x_1808_ = v___x_1800_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_val_1806_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
v_a_1811_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1797_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1797_);
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
if (v___y_1821_ == 0)
{
lean_dec_ref(v___y_1820_);
v___y_1792_ = v_a_1788_;
v___y_1793_ = v_a_1789_;
goto v___jp_1791_;
}
else
{
lean_object* v___x_1822_; 
lean_dec(v_decl_1787_);
v___x_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___y_1820_);
return v___x_1822_;
}
}
v___jp_1823_:
{
uint8_t v___x_1825_; 
v___x_1825_ = l_Lean_Exception_isInterrupt(v_a_1824_);
if (v___x_1825_ == 0)
{
uint8_t v___x_1826_; 
lean_inc_ref(v_a_1824_);
v___x_1826_ = l_Lean_Exception_isRuntime(v_a_1824_);
v___y_1820_ = v_a_1824_;
v___y_1821_ = v___x_1826_;
goto v___jp_1819_;
}
else
{
v___y_1820_ = v_a_1824_;
v___y_1821_ = v___x_1825_;
goto v___jp_1819_;
}
}
v___jp_1827_:
{
if (v___y_1829_ == 0)
{
lean_dec_ref(v___y_1828_);
v___y_1792_ = v_a_1788_;
v___y_1793_ = v_a_1789_;
goto v___jp_1791_;
}
else
{
lean_object* v___x_1830_; 
lean_dec(v_decl_1787_);
v___x_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1830_, 0, v___y_1828_);
return v___x_1830_;
}
}
v___jp_1831_:
{
uint8_t v___x_1833_; 
v___x_1833_ = l_Lean_Exception_isInterrupt(v_a_1832_);
if (v___x_1833_ == 0)
{
uint8_t v___x_1834_; 
lean_inc_ref(v_a_1832_);
v___x_1834_ = l_Lean_Exception_isRuntime(v_a_1832_);
v___y_1828_ = v_a_1832_;
v___y_1829_ = v___x_1834_;
goto v___jp_1827_;
}
else
{
v___y_1828_ = v_a_1832_;
v___y_1829_ = v___x_1833_;
goto v___jp_1827_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom___boxed(lean_object* v_decl_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom(v_decl_1881_, v_a_1882_, v_a_1883_);
lean_dec(v_a_1883_);
lean_dec_ref(v_a_1882_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0(lean_object* v_00_u03b1_1886_, lean_object* v_x_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v_x_1887_, v___y_1888_, v___y_1889_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___boxed(lean_object* v_00_u03b1_1892_, lean_object* v_x_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0(v_00_u03b1_1892_, v_x_1893_, v___y_1894_, v___y_1895_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2(lean_object* v_as_1898_, lean_object* v_as_x27_1899_, lean_object* v_b_1900_, lean_object* v_a_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___redArg(v_as_x27_1899_, v_b_1900_, v___y_1902_, v___y_1903_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2___boxed(lean_object* v_as_1906_, lean_object* v_as_x27_1907_, lean_object* v_b_1908_, lean_object* v_a_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__2(v_as_1906_, v_as_x27_1907_, v_b_1908_, v_a_1909_, v___y_1910_, v___y_1911_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v_as_x27_1907_);
lean_dec(v_as_1906_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__3(v_00_u03b1_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0(lean_object* v_00_u03b1_1924_, lean_object* v_ex_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v___x_1929_; 
v___x_1929_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(v_ex_1925_, v___y_1926_, v___y_1927_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1930_, lean_object* v_ex_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0(v_00_u03b1_1930_, v_ex_1931_, v___y_1932_, v___y_1933_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1936_, lean_object* v_msg_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_1937_, v___y_1938_, v___y_1939_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1942_, lean_object* v_msg_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__2(v_00_u03b1_1942_, v_msg_1943_, v___y_1944_, v___y_1945_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
return v_res_1947_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1948_ = lean_unsigned_to_nat(32u);
v___x_1949_ = lean_mk_empty_array_with_capacity(v___x_1948_);
v___x_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
return v___x_1950_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1951_ = ((size_t)5ULL);
v___x_1952_ = lean_unsigned_to_nat(0u);
v___x_1953_ = lean_unsigned_to_nat(32u);
v___x_1954_ = lean_mk_empty_array_with_capacity(v___x_1953_);
v___x_1955_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__0);
v___x_1956_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1956_, 0, v___x_1955_);
lean_ctor_set(v___x_1956_, 1, v___x_1954_);
lean_ctor_set(v___x_1956_, 2, v___x_1952_);
lean_ctor_set(v___x_1956_, 3, v___x_1952_);
lean_ctor_set_usize(v___x_1956_, 4, v___x_1951_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(lean_object* v___y_1957_){
_start:
{
lean_object* v___x_1959_; lean_object* v_traceState_1960_; lean_object* v_traces_1961_; lean_object* v___x_1962_; lean_object* v_traceState_1963_; lean_object* v_env_1964_; lean_object* v_nextMacroScope_1965_; lean_object* v_ngen_1966_; lean_object* v_auxDeclNGen_1967_; lean_object* v_cache_1968_; lean_object* v_messages_1969_; lean_object* v_infoState_1970_; lean_object* v_snapshotTasks_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1990_; 
v___x_1959_ = lean_st_ref_get(v___y_1957_);
v_traceState_1960_ = lean_ctor_get(v___x_1959_, 4);
lean_inc_ref(v_traceState_1960_);
lean_dec(v___x_1959_);
v_traces_1961_ = lean_ctor_get(v_traceState_1960_, 0);
lean_inc_ref(v_traces_1961_);
lean_dec_ref(v_traceState_1960_);
v___x_1962_ = lean_st_ref_take(v___y_1957_);
v_traceState_1963_ = lean_ctor_get(v___x_1962_, 4);
v_env_1964_ = lean_ctor_get(v___x_1962_, 0);
v_nextMacroScope_1965_ = lean_ctor_get(v___x_1962_, 1);
v_ngen_1966_ = lean_ctor_get(v___x_1962_, 2);
v_auxDeclNGen_1967_ = lean_ctor_get(v___x_1962_, 3);
v_cache_1968_ = lean_ctor_get(v___x_1962_, 5);
v_messages_1969_ = lean_ctor_get(v___x_1962_, 6);
v_infoState_1970_ = lean_ctor_get(v___x_1962_, 7);
v_snapshotTasks_1971_ = lean_ctor_get(v___x_1962_, 8);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1973_ = v___x_1962_;
v_isShared_1974_ = v_isSharedCheck_1990_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_snapshotTasks_1971_);
lean_inc(v_infoState_1970_);
lean_inc(v_messages_1969_);
lean_inc(v_cache_1968_);
lean_inc(v_traceState_1963_);
lean_inc(v_auxDeclNGen_1967_);
lean_inc(v_ngen_1966_);
lean_inc(v_nextMacroScope_1965_);
lean_inc(v_env_1964_);
lean_dec(v___x_1962_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1990_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
uint64_t v_tid_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1988_; 
v_tid_1975_ = lean_ctor_get_uint64(v_traceState_1963_, sizeof(void*)*1);
v_isSharedCheck_1988_ = !lean_is_exclusive(v_traceState_1963_);
if (v_isSharedCheck_1988_ == 0)
{
lean_object* v_unused_1989_; 
v_unused_1989_ = lean_ctor_get(v_traceState_1963_, 0);
lean_dec(v_unused_1989_);
v___x_1977_ = v_traceState_1963_;
v_isShared_1978_ = v_isSharedCheck_1988_;
goto v_resetjp_1976_;
}
else
{
lean_dec(v_traceState_1963_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1988_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; lean_object* v___x_1981_; 
v___x_1979_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___closed__1);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v___x_1979_);
v___x_1981_ = v___x_1977_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1979_);
lean_ctor_set_uint64(v_reuseFailAlloc_1987_, sizeof(void*)*1, v_tid_1975_);
v___x_1981_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
lean_object* v___x_1983_; 
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 4, v___x_1981_);
v___x_1983_ = v___x_1973_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_env_1964_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_nextMacroScope_1965_);
lean_ctor_set(v_reuseFailAlloc_1986_, 2, v_ngen_1966_);
lean_ctor_set(v_reuseFailAlloc_1986_, 3, v_auxDeclNGen_1967_);
lean_ctor_set(v_reuseFailAlloc_1986_, 4, v___x_1981_);
lean_ctor_set(v_reuseFailAlloc_1986_, 5, v_cache_1968_);
lean_ctor_set(v_reuseFailAlloc_1986_, 6, v_messages_1969_);
lean_ctor_set(v_reuseFailAlloc_1986_, 7, v_infoState_1970_);
lean_ctor_set(v_reuseFailAlloc_1986_, 8, v_snapshotTasks_1971_);
v___x_1983_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1984_ = lean_st_ref_set(v___y_1957_, v___x_1983_);
v___x_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1985_, 0, v_traces_1961_);
return v___x_1985_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg___boxed(lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v___y_1991_);
lean_dec(v___y_1991_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1(lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v___y_1995_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___boxed(lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1(v___y_1998_, v___y_1999_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___redArg(lean_object* v_category_2002_, lean_object* v_opts_2003_, lean_object* v_act_2004_, lean_object* v_decl_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
lean_inc(v___y_2007_);
lean_inc_ref(v___y_2006_);
v___x_2009_ = lean_apply_2(v_act_2004_, v___y_2006_, v___y_2007_);
v___x_2010_ = l_Lean_profileitIOUnsafe___redArg(v_category_2002_, v_opts_2003_, v___x_2009_, v_decl_2005_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___redArg___boxed(lean_object* v_category_2011_, lean_object* v_opts_2012_, lean_object* v_act_2013_, lean_object* v_decl_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___redArg(v_category_2011_, v_opts_2012_, v_act_2013_, v_decl_2014_, v___y_2015_, v___y_2016_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec_ref(v_opts_2012_);
lean_dec_ref(v_category_2011_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3(lean_object* v_00_u03b1_2019_, lean_object* v_category_2020_, lean_object* v_opts_2021_, lean_object* v_act_2022_, lean_object* v_decl_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v___x_2027_; 
v___x_2027_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___redArg(v_category_2020_, v_opts_2021_, v_act_2022_, v_decl_2023_, v___y_2024_, v___y_2025_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___boxed(lean_object* v_00_u03b1_2028_, lean_object* v_category_2029_, lean_object* v_opts_2030_, lean_object* v_act_2031_, lean_object* v_decl_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3(v_00_u03b1_2028_, v_category_2029_, v_opts_2030_, v_act_2031_, v_decl_2032_, v___y_2033_, v___y_2034_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec_ref(v_opts_2030_);
lean_dec_ref(v_category_2029_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__0(lean_object* v_a_2037_, lean_object* v_a_2038_){
_start:
{
if (lean_obj_tag(v_a_2037_) == 0)
{
lean_object* v___x_2039_; 
v___x_2039_ = l_List_reverse___redArg(v_a_2038_);
return v___x_2039_;
}
else
{
lean_object* v_head_2040_; lean_object* v_tail_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2050_; 
v_head_2040_ = lean_ctor_get(v_a_2037_, 0);
v_tail_2041_ = lean_ctor_get(v_a_2037_, 1);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_a_2037_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2043_ = v_a_2037_;
v_isShared_2044_ = v_isSharedCheck_2050_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_tail_2041_);
lean_inc(v_head_2040_);
lean_dec(v_a_2037_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2050_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; lean_object* v___x_2047_; 
v___x_2045_ = l_Lean_MessageData_ofName(v_head_2040_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 1, v_a_2038_);
lean_ctor_set(v___x_2043_, 0, v___x_2045_);
v___x_2047_ = v___x_2043_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2045_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_a_2038_);
v___x_2047_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
v_a_2037_ = v_tail_2041_;
v_a_2038_ = v___x_2047_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2052_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__0));
v___x_2053_ = l_Lean_stringToMessageData(v___x_2052_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0(lean_object* v_decl_2054_, lean_object* v_x_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2059_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__1, &l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___closed__1);
v___x_2060_ = l_Lean_Declaration_getTopLevelNames(v_decl_2054_);
v___x_2061_ = lean_box(0);
v___x_2062_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__0(v___x_2060_, v___x_2061_);
v___x_2063_ = l_Lean_MessageData_ofList(v___x_2062_);
v___x_2064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2059_);
lean_ctor_set(v___x_2064_, 1, v___x_2063_);
v___x_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___boxed(lean_object* v_decl_2066_, lean_object* v_x_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0(v_decl_2066_, v_x_2067_, v___y_2068_, v___y_2069_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec_ref(v_x_2067_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__5(lean_object* v_opts_2072_, lean_object* v_opt_2073_){
_start:
{
lean_object* v_name_2074_; lean_object* v_defValue_2075_; lean_object* v_map_2076_; lean_object* v___x_2077_; 
v_name_2074_ = lean_ctor_get(v_opt_2073_, 0);
v_defValue_2075_ = lean_ctor_get(v_opt_2073_, 1);
v_map_2076_ = lean_ctor_get(v_opts_2072_, 0);
v___x_2077_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2076_, v_name_2074_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_inc(v_defValue_2075_);
return v_defValue_2075_;
}
else
{
lean_object* v_val_2078_; 
v_val_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_val_2078_);
lean_dec_ref(v___x_2077_);
if (lean_obj_tag(v_val_2078_) == 3)
{
lean_object* v_v_2079_; 
v_v_2079_ = lean_ctor_get(v_val_2078_, 0);
lean_inc(v_v_2079_);
lean_dec_ref(v_val_2078_);
return v_v_2079_;
}
else
{
lean_dec(v_val_2078_);
lean_inc(v_defValue_2075_);
return v_defValue_2075_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__5___boxed(lean_object* v_opts_2080_, lean_object* v_opt_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__5(v_opts_2080_, v_opt_2081_);
lean_dec_ref(v_opt_2081_);
lean_dec_ref(v_opts_2080_);
return v_res_2082_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__2(lean_object* v_e_2083_){
_start:
{
if (lean_obj_tag(v_e_2083_) == 0)
{
uint8_t v___x_2084_; 
v___x_2084_ = 2;
return v___x_2084_;
}
else
{
uint8_t v___x_2085_; 
v___x_2085_ = 0;
return v___x_2085_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__2___boxed(lean_object* v_e_2086_){
_start:
{
uint8_t v_res_2087_; lean_object* v_r_2088_; 
v_res_2087_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__2(v_e_2086_);
lean_dec_ref(v_e_2086_);
v_r_2088_ = lean_box(v_res_2087_);
return v_r_2088_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4___redArg(lean_object* v_x_2089_){
_start:
{
if (lean_obj_tag(v_x_2089_) == 0)
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
v_a_2091_ = lean_ctor_get(v_x_2089_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_x_2089_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v_x_2089_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v_x_2089_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
lean_ctor_set_tag(v___x_2093_, 1);
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
v_a_2099_ = lean_ctor_get(v_x_2089_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v_x_2089_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v_x_2089_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v_x_2089_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
lean_ctor_set_tag(v___x_2101_, 0);
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4___redArg___boxed(lean_object* v_x_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4___redArg(v_x_2107_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__3_spec__5(size_t v_sz_2110_, size_t v_i_2111_, lean_object* v_bs_2112_){
_start:
{
uint8_t v___x_2113_; 
v___x_2113_ = lean_usize_dec_lt(v_i_2111_, v_sz_2110_);
if (v___x_2113_ == 0)
{
return v_bs_2112_;
}
else
{
lean_object* v_v_2114_; lean_object* v_msg_2115_; lean_object* v___x_2116_; lean_object* v_bs_x27_2117_; size_t v___x_2118_; size_t v___x_2119_; lean_object* v___x_2120_; 
v_v_2114_ = lean_array_uget_borrowed(v_bs_2112_, v_i_2111_);
v_msg_2115_ = lean_ctor_get(v_v_2114_, 1);
lean_inc_ref(v_msg_2115_);
v___x_2116_ = lean_unsigned_to_nat(0u);
v_bs_x27_2117_ = lean_array_uset(v_bs_2112_, v_i_2111_, v___x_2116_);
v___x_2118_ = ((size_t)1ULL);
v___x_2119_ = lean_usize_add(v_i_2111_, v___x_2118_);
v___x_2120_ = lean_array_uset(v_bs_x27_2117_, v_i_2111_, v_msg_2115_);
v_i_2111_ = v___x_2119_;
v_bs_2112_ = v___x_2120_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__3_spec__5___boxed(lean_object* v_sz_2122_, lean_object* v_i_2123_, lean_object* v_bs_2124_){
_start:
{
size_t v_sz_boxed_2125_; size_t v_i_boxed_2126_; lean_object* v_res_2127_; 
v_sz_boxed_2125_ = lean_unbox_usize(v_sz_2122_);
lean_dec(v_sz_2122_);
v_i_boxed_2126_ = lean_unbox_usize(v_i_2123_);
lean_dec(v_i_2123_);
v_res_2127_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__3_spec__5(v_sz_boxed_2125_, v_i_boxed_2126_, v_bs_2124_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__3(lean_object* v_oldTraces_2128_, lean_object* v_data_2129_, lean_object* v_ref_2130_, lean_object* v_msg_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
lean_object* v_fileName_2135_; lean_object* v_fileMap_2136_; lean_object* v_options_2137_; lean_object* v_currRecDepth_2138_; lean_object* v_maxRecDepth_2139_; lean_object* v_ref_2140_; lean_object* v_currNamespace_2141_; lean_object* v_openDecls_2142_; lean_object* v_initHeartbeats_2143_; lean_object* v_maxHeartbeats_2144_; lean_object* v_quotContext_2145_; lean_object* v_currMacroScope_2146_; uint8_t v_diag_2147_; lean_object* v_cancelTk_x3f_2148_; uint8_t v_suppressElabErrors_2149_; lean_object* v_inheritedTraceOptions_2150_; lean_object* v___x_2151_; lean_object* v_traceState_2152_; lean_object* v_traces_2153_; lean_object* v_ref_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; size_t v_sz_2157_; size_t v___x_2158_; lean_object* v___x_2159_; lean_object* v_msg_2160_; lean_object* v___x_2161_; lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2199_; 
v_fileName_2135_ = lean_ctor_get(v___y_2132_, 0);
v_fileMap_2136_ = lean_ctor_get(v___y_2132_, 1);
v_options_2137_ = lean_ctor_get(v___y_2132_, 2);
v_currRecDepth_2138_ = lean_ctor_get(v___y_2132_, 3);
v_maxRecDepth_2139_ = lean_ctor_get(v___y_2132_, 4);
v_ref_2140_ = lean_ctor_get(v___y_2132_, 5);
v_currNamespace_2141_ = lean_ctor_get(v___y_2132_, 6);
v_openDecls_2142_ = lean_ctor_get(v___y_2132_, 7);
v_initHeartbeats_2143_ = lean_ctor_get(v___y_2132_, 8);
v_maxHeartbeats_2144_ = lean_ctor_get(v___y_2132_, 9);
v_quotContext_2145_ = lean_ctor_get(v___y_2132_, 10);
v_currMacroScope_2146_ = lean_ctor_get(v___y_2132_, 11);
v_diag_2147_ = lean_ctor_get_uint8(v___y_2132_, sizeof(void*)*14);
v_cancelTk_x3f_2148_ = lean_ctor_get(v___y_2132_, 12);
v_suppressElabErrors_2149_ = lean_ctor_get_uint8(v___y_2132_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2150_ = lean_ctor_get(v___y_2132_, 13);
v___x_2151_ = lean_st_ref_get(v___y_2133_);
v_traceState_2152_ = lean_ctor_get(v___x_2151_, 4);
lean_inc_ref(v_traceState_2152_);
lean_dec(v___x_2151_);
v_traces_2153_ = lean_ctor_get(v_traceState_2152_, 0);
lean_inc_ref(v_traces_2153_);
lean_dec_ref(v_traceState_2152_);
v_ref_2154_ = l_Lean_replaceRef(v_ref_2130_, v_ref_2140_);
lean_inc_ref(v_inheritedTraceOptions_2150_);
lean_inc(v_cancelTk_x3f_2148_);
lean_inc(v_currMacroScope_2146_);
lean_inc(v_quotContext_2145_);
lean_inc(v_maxHeartbeats_2144_);
lean_inc(v_initHeartbeats_2143_);
lean_inc(v_openDecls_2142_);
lean_inc(v_currNamespace_2141_);
lean_inc(v_maxRecDepth_2139_);
lean_inc(v_currRecDepth_2138_);
lean_inc_ref(v_options_2137_);
lean_inc_ref(v_fileMap_2136_);
lean_inc_ref(v_fileName_2135_);
v___x_2155_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2155_, 0, v_fileName_2135_);
lean_ctor_set(v___x_2155_, 1, v_fileMap_2136_);
lean_ctor_set(v___x_2155_, 2, v_options_2137_);
lean_ctor_set(v___x_2155_, 3, v_currRecDepth_2138_);
lean_ctor_set(v___x_2155_, 4, v_maxRecDepth_2139_);
lean_ctor_set(v___x_2155_, 5, v_ref_2154_);
lean_ctor_set(v___x_2155_, 6, v_currNamespace_2141_);
lean_ctor_set(v___x_2155_, 7, v_openDecls_2142_);
lean_ctor_set(v___x_2155_, 8, v_initHeartbeats_2143_);
lean_ctor_set(v___x_2155_, 9, v_maxHeartbeats_2144_);
lean_ctor_set(v___x_2155_, 10, v_quotContext_2145_);
lean_ctor_set(v___x_2155_, 11, v_currMacroScope_2146_);
lean_ctor_set(v___x_2155_, 12, v_cancelTk_x3f_2148_);
lean_ctor_set(v___x_2155_, 13, v_inheritedTraceOptions_2150_);
lean_ctor_set_uint8(v___x_2155_, sizeof(void*)*14, v_diag_2147_);
lean_ctor_set_uint8(v___x_2155_, sizeof(void*)*14 + 1, v_suppressElabErrors_2149_);
v___x_2156_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2153_);
lean_dec_ref(v_traces_2153_);
v_sz_2157_ = lean_array_size(v___x_2156_);
v___x_2158_ = ((size_t)0ULL);
v___x_2159_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__3_spec__5(v_sz_2157_, v___x_2158_, v___x_2156_);
v_msg_2160_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2160_, 0, v_data_2129_);
lean_ctor_set(v_msg_2160_, 1, v_msg_2131_);
lean_ctor_set(v_msg_2160_, 2, v___x_2159_);
v___x_2161_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2160_, v___x_2155_, v___y_2133_);
lean_dec_ref(v___x_2155_);
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2164_ = v___x_2161_;
v_isShared_2165_ = v_isSharedCheck_2199_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2161_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2199_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2166_; lean_object* v_traceState_2167_; lean_object* v_env_2168_; lean_object* v_nextMacroScope_2169_; lean_object* v_ngen_2170_; lean_object* v_auxDeclNGen_2171_; lean_object* v_cache_2172_; lean_object* v_messages_2173_; lean_object* v_infoState_2174_; lean_object* v_snapshotTasks_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2198_; 
v___x_2166_ = lean_st_ref_take(v___y_2133_);
v_traceState_2167_ = lean_ctor_get(v___x_2166_, 4);
v_env_2168_ = lean_ctor_get(v___x_2166_, 0);
v_nextMacroScope_2169_ = lean_ctor_get(v___x_2166_, 1);
v_ngen_2170_ = lean_ctor_get(v___x_2166_, 2);
v_auxDeclNGen_2171_ = lean_ctor_get(v___x_2166_, 3);
v_cache_2172_ = lean_ctor_get(v___x_2166_, 5);
v_messages_2173_ = lean_ctor_get(v___x_2166_, 6);
v_infoState_2174_ = lean_ctor_get(v___x_2166_, 7);
v_snapshotTasks_2175_ = lean_ctor_get(v___x_2166_, 8);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2177_ = v___x_2166_;
v_isShared_2178_ = v_isSharedCheck_2198_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_snapshotTasks_2175_);
lean_inc(v_infoState_2174_);
lean_inc(v_messages_2173_);
lean_inc(v_cache_2172_);
lean_inc(v_traceState_2167_);
lean_inc(v_auxDeclNGen_2171_);
lean_inc(v_ngen_2170_);
lean_inc(v_nextMacroScope_2169_);
lean_inc(v_env_2168_);
lean_dec(v___x_2166_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2198_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
uint64_t v_tid_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2196_; 
v_tid_2179_ = lean_ctor_get_uint64(v_traceState_2167_, sizeof(void*)*1);
v_isSharedCheck_2196_ = !lean_is_exclusive(v_traceState_2167_);
if (v_isSharedCheck_2196_ == 0)
{
lean_object* v_unused_2197_; 
v_unused_2197_ = lean_ctor_get(v_traceState_2167_, 0);
lean_dec(v_unused_2197_);
v___x_2181_ = v_traceState_2167_;
v_isShared_2182_ = v_isSharedCheck_2196_;
goto v_resetjp_2180_;
}
else
{
lean_dec(v_traceState_2167_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2196_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2186_; 
v___x_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2183_, 0, v_ref_2130_);
lean_ctor_set(v___x_2183_, 1, v_a_2162_);
v___x_2184_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2128_, v___x_2183_);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 0, v___x_2184_);
v___x_2186_ = v___x_2181_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2184_);
lean_ctor_set_uint64(v_reuseFailAlloc_2195_, sizeof(void*)*1, v_tid_2179_);
v___x_2186_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
lean_object* v___x_2188_; 
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 4, v___x_2186_);
v___x_2188_ = v___x_2177_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_env_2168_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v_nextMacroScope_2169_);
lean_ctor_set(v_reuseFailAlloc_2194_, 2, v_ngen_2170_);
lean_ctor_set(v_reuseFailAlloc_2194_, 3, v_auxDeclNGen_2171_);
lean_ctor_set(v_reuseFailAlloc_2194_, 4, v___x_2186_);
lean_ctor_set(v_reuseFailAlloc_2194_, 5, v_cache_2172_);
lean_ctor_set(v_reuseFailAlloc_2194_, 6, v_messages_2173_);
lean_ctor_set(v_reuseFailAlloc_2194_, 7, v_infoState_2174_);
lean_ctor_set(v_reuseFailAlloc_2194_, 8, v_snapshotTasks_2175_);
v___x_2188_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2192_; 
v___x_2189_ = lean_st_ref_set(v___y_2133_, v___x_2188_);
v___x_2190_ = lean_box(0);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 0, v___x_2190_);
v___x_2192_ = v___x_2164_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2190_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__3___boxed(lean_object* v_oldTraces_2200_, lean_object* v_data_2201_, lean_object* v_ref_2202_, lean_object* v_msg_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__3(v_oldTraces_2200_, v_data_2201_, v_ref_2202_, v_msg_2203_, v___y_2204_, v___y_2205_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
return v_res_2207_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2209_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__0));
v___x_2210_ = l_Lean_stringToMessageData(v___x_2209_);
return v___x_2210_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__2(void){
_start:
{
lean_object* v___x_2211_; double v___x_2212_; 
v___x_2211_ = lean_unsigned_to_nat(0u);
v___x_2212_ = lean_float_of_nat(v___x_2211_);
return v___x_2212_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__4(void){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2214_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__3));
v___x_2215_ = l_Lean_stringToMessageData(v___x_2214_);
return v___x_2215_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__5(void){
_start:
{
lean_object* v___x_2216_; double v___x_2217_; 
v___x_2216_ = lean_unsigned_to_nat(1000u);
v___x_2217_ = lean_float_of_nat(v___x_2216_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2(lean_object* v_cls_2218_, uint8_t v_collapsed_2219_, lean_object* v_tag_2220_, lean_object* v_opts_2221_, uint8_t v_clsEnabled_2222_, lean_object* v_oldTraces_2223_, lean_object* v_msg_2224_, lean_object* v_resStartStop_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v_fst_2229_; lean_object* v_snd_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2320_; 
v_fst_2229_ = lean_ctor_get(v_resStartStop_2225_, 0);
v_snd_2230_ = lean_ctor_get(v_resStartStop_2225_, 1);
v_isSharedCheck_2320_ = !lean_is_exclusive(v_resStartStop_2225_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2232_ = v_resStartStop_2225_;
v_isShared_2233_ = v_isSharedCheck_2320_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_snd_2230_);
lean_inc(v_fst_2229_);
lean_dec(v_resStartStop_2225_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2320_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v_data_2237_; lean_object* v_fst_2240_; lean_object* v_snd_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2319_; 
v_fst_2240_ = lean_ctor_get(v_snd_2230_, 0);
v_snd_2241_ = lean_ctor_get(v_snd_2230_, 1);
v_isSharedCheck_2319_ = !lean_is_exclusive(v_snd_2230_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2243_ = v_snd_2230_;
v_isShared_2244_ = v_isSharedCheck_2319_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_snd_2241_);
lean_inc(v_fst_2240_);
lean_dec(v_snd_2230_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2319_;
goto v_resetjp_2242_;
}
v___jp_2234_:
{
lean_object* v___x_2238_; 
lean_inc(v___y_2235_);
v___x_2238_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__3(v_oldTraces_2223_, v_data_2237_, v___y_2235_, v___y_2236_, v___y_2226_, v___y_2227_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v___x_2239_; 
lean_dec_ref(v___x_2238_);
v___x_2239_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4___redArg(v_fst_2229_);
return v___x_2239_;
}
else
{
lean_dec(v_fst_2229_);
return v___x_2238_;
}
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; uint8_t v___x_2246_; lean_object* v___y_2248_; lean_object* v_a_2249_; uint8_t v___y_2273_; double v___y_2304_; 
v___x_2245_ = l_Lean_trace_profiler;
v___x_2246_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2221_, v___x_2245_);
if (v___x_2246_ == 0)
{
v___y_2273_ = v___x_2246_;
goto v___jp_2272_;
}
else
{
lean_object* v___x_2309_; uint8_t v___x_2310_; 
v___x_2309_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2310_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2221_, v___x_2309_);
if (v___x_2310_ == 0)
{
lean_object* v___x_2311_; lean_object* v___x_2312_; double v___x_2313_; double v___x_2314_; double v___x_2315_; 
v___x_2311_ = l_Lean_trace_profiler_threshold;
v___x_2312_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__5(v_opts_2221_, v___x_2311_);
v___x_2313_ = lean_float_of_nat(v___x_2312_);
v___x_2314_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__5);
v___x_2315_ = lean_float_div(v___x_2313_, v___x_2314_);
v___y_2304_ = v___x_2315_;
goto v___jp_2303_;
}
else
{
lean_object* v___x_2316_; lean_object* v___x_2317_; double v___x_2318_; 
v___x_2316_ = l_Lean_trace_profiler_threshold;
v___x_2317_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__5(v_opts_2221_, v___x_2316_);
v___x_2318_ = lean_float_of_nat(v___x_2317_);
v___y_2304_ = v___x_2318_;
goto v___jp_2303_;
}
}
v___jp_2247_:
{
uint8_t v_result_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2255_; 
v_result_2250_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__2(v_fst_2229_);
v___x_2251_ = l_Lean_TraceResult_toEmoji(v_result_2250_);
v___x_2252_ = l_Lean_stringToMessageData(v___x_2251_);
v___x_2253_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__1);
if (v_isShared_2244_ == 0)
{
lean_ctor_set_tag(v___x_2243_, 7);
lean_ctor_set(v___x_2243_, 1, v___x_2253_);
lean_ctor_set(v___x_2243_, 0, v___x_2252_);
v___x_2255_ = v___x_2243_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2252_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v___x_2253_);
v___x_2255_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
lean_object* v_m_2257_; 
if (v_isShared_2233_ == 0)
{
lean_ctor_set_tag(v___x_2232_, 7);
lean_ctor_set(v___x_2232_, 1, v_a_2249_);
lean_ctor_set(v___x_2232_, 0, v___x_2255_);
v_m_2257_ = v___x_2232_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2255_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v_a_2249_);
v_m_2257_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; double v___x_2260_; lean_object* v_data_2261_; 
v___x_2258_ = lean_box(v_result_2250_);
v___x_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
v___x_2260_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__2);
lean_inc_ref(v_tag_2220_);
lean_inc_ref(v___x_2259_);
lean_inc(v_cls_2218_);
v_data_2261_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2261_, 0, v_cls_2218_);
lean_ctor_set(v_data_2261_, 1, v___x_2259_);
lean_ctor_set(v_data_2261_, 2, v_tag_2220_);
lean_ctor_set_float(v_data_2261_, sizeof(void*)*3, v___x_2260_);
lean_ctor_set_float(v_data_2261_, sizeof(void*)*3 + 8, v___x_2260_);
lean_ctor_set_uint8(v_data_2261_, sizeof(void*)*3 + 16, v_collapsed_2219_);
if (v___x_2246_ == 0)
{
lean_dec_ref(v___x_2259_);
lean_dec(v_snd_2241_);
lean_dec(v_fst_2240_);
lean_dec_ref(v_tag_2220_);
lean_dec(v_cls_2218_);
v___y_2235_ = v___y_2248_;
v___y_2236_ = v_m_2257_;
v_data_2237_ = v_data_2261_;
goto v___jp_2234_;
}
else
{
lean_object* v_data_2262_; double v___x_2263_; double v___x_2264_; 
lean_dec_ref(v_data_2261_);
v_data_2262_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2262_, 0, v_cls_2218_);
lean_ctor_set(v_data_2262_, 1, v___x_2259_);
lean_ctor_set(v_data_2262_, 2, v_tag_2220_);
v___x_2263_ = lean_unbox_float(v_fst_2240_);
lean_dec(v_fst_2240_);
lean_ctor_set_float(v_data_2262_, sizeof(void*)*3, v___x_2263_);
v___x_2264_ = lean_unbox_float(v_snd_2241_);
lean_dec(v_snd_2241_);
lean_ctor_set_float(v_data_2262_, sizeof(void*)*3 + 8, v___x_2264_);
lean_ctor_set_uint8(v_data_2262_, sizeof(void*)*3 + 16, v_collapsed_2219_);
v___y_2235_ = v___y_2248_;
v___y_2236_ = v_m_2257_;
v_data_2237_ = v_data_2262_;
goto v___jp_2234_;
}
}
}
}
v___jp_2267_:
{
lean_object* v_ref_2268_; lean_object* v___x_2269_; 
v_ref_2268_ = lean_ctor_get(v___y_2226_, 5);
lean_inc(v___y_2227_);
lean_inc_ref(v___y_2226_);
lean_inc(v_fst_2229_);
v___x_2269_ = lean_apply_4(v_msg_2224_, v_fst_2229_, v___y_2226_, v___y_2227_, lean_box(0));
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_a_2270_);
lean_dec_ref(v___x_2269_);
v___y_2248_ = v_ref_2268_;
v_a_2249_ = v_a_2270_;
goto v___jp_2247_;
}
else
{
lean_object* v___x_2271_; 
lean_dec_ref(v___x_2269_);
v___x_2271_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__4);
v___y_2248_ = v_ref_2268_;
v_a_2249_ = v___x_2271_;
goto v___jp_2247_;
}
}
v___jp_2272_:
{
if (v_clsEnabled_2222_ == 0)
{
if (v___y_2273_ == 0)
{
lean_object* v___x_2274_; lean_object* v_traceState_2275_; lean_object* v_env_2276_; lean_object* v_nextMacroScope_2277_; lean_object* v_ngen_2278_; lean_object* v_auxDeclNGen_2279_; lean_object* v_cache_2280_; lean_object* v_messages_2281_; lean_object* v_infoState_2282_; lean_object* v_snapshotTasks_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2302_; 
lean_del_object(v___x_2243_);
lean_dec(v_snd_2241_);
lean_dec(v_fst_2240_);
lean_del_object(v___x_2232_);
lean_dec_ref(v_msg_2224_);
lean_dec_ref(v_tag_2220_);
lean_dec(v_cls_2218_);
v___x_2274_ = lean_st_ref_take(v___y_2227_);
v_traceState_2275_ = lean_ctor_get(v___x_2274_, 4);
v_env_2276_ = lean_ctor_get(v___x_2274_, 0);
v_nextMacroScope_2277_ = lean_ctor_get(v___x_2274_, 1);
v_ngen_2278_ = lean_ctor_get(v___x_2274_, 2);
v_auxDeclNGen_2279_ = lean_ctor_get(v___x_2274_, 3);
v_cache_2280_ = lean_ctor_get(v___x_2274_, 5);
v_messages_2281_ = lean_ctor_get(v___x_2274_, 6);
v_infoState_2282_ = lean_ctor_get(v___x_2274_, 7);
v_snapshotTasks_2283_ = lean_ctor_get(v___x_2274_, 8);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2285_ = v___x_2274_;
v_isShared_2286_ = v_isSharedCheck_2302_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_snapshotTasks_2283_);
lean_inc(v_infoState_2282_);
lean_inc(v_messages_2281_);
lean_inc(v_cache_2280_);
lean_inc(v_traceState_2275_);
lean_inc(v_auxDeclNGen_2279_);
lean_inc(v_ngen_2278_);
lean_inc(v_nextMacroScope_2277_);
lean_inc(v_env_2276_);
lean_dec(v___x_2274_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2302_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
uint64_t v_tid_2287_; lean_object* v_traces_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2301_; 
v_tid_2287_ = lean_ctor_get_uint64(v_traceState_2275_, sizeof(void*)*1);
v_traces_2288_ = lean_ctor_get(v_traceState_2275_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v_traceState_2275_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2290_ = v_traceState_2275_;
v_isShared_2291_ = v_isSharedCheck_2301_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_traces_2288_);
lean_dec(v_traceState_2275_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2301_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2292_; lean_object* v___x_2294_; 
v___x_2292_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2223_, v_traces_2288_);
lean_dec_ref(v_traces_2288_);
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 0, v___x_2292_);
v___x_2294_ = v___x_2290_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2292_);
lean_ctor_set_uint64(v_reuseFailAlloc_2300_, sizeof(void*)*1, v_tid_2287_);
v___x_2294_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
lean_object* v___x_2296_; 
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 4, v___x_2294_);
v___x_2296_ = v___x_2285_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_env_2276_);
lean_ctor_set(v_reuseFailAlloc_2299_, 1, v_nextMacroScope_2277_);
lean_ctor_set(v_reuseFailAlloc_2299_, 2, v_ngen_2278_);
lean_ctor_set(v_reuseFailAlloc_2299_, 3, v_auxDeclNGen_2279_);
lean_ctor_set(v_reuseFailAlloc_2299_, 4, v___x_2294_);
lean_ctor_set(v_reuseFailAlloc_2299_, 5, v_cache_2280_);
lean_ctor_set(v_reuseFailAlloc_2299_, 6, v_messages_2281_);
lean_ctor_set(v_reuseFailAlloc_2299_, 7, v_infoState_2282_);
lean_ctor_set(v_reuseFailAlloc_2299_, 8, v_snapshotTasks_2283_);
v___x_2296_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2297_ = lean_st_ref_set(v___y_2227_, v___x_2296_);
v___x_2298_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4___redArg(v_fst_2229_);
return v___x_2298_;
}
}
}
}
}
else
{
goto v___jp_2267_;
}
}
else
{
goto v___jp_2267_;
}
}
v___jp_2303_:
{
double v___x_2305_; double v___x_2306_; double v___x_2307_; uint8_t v___x_2308_; 
v___x_2305_ = lean_unbox_float(v_snd_2241_);
v___x_2306_ = lean_unbox_float(v_fst_2240_);
v___x_2307_ = lean_float_sub(v___x_2305_, v___x_2306_);
v___x_2308_ = lean_float_decLt(v___y_2304_, v___x_2307_);
v___y_2273_ = v___x_2308_;
goto v___jp_2272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___boxed(lean_object* v_cls_2321_, lean_object* v_collapsed_2322_, lean_object* v_tag_2323_, lean_object* v_opts_2324_, lean_object* v_clsEnabled_2325_, lean_object* v_oldTraces_2326_, lean_object* v_msg_2327_, lean_object* v_resStartStop_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
uint8_t v_collapsed_boxed_2332_; uint8_t v_clsEnabled_boxed_2333_; lean_object* v_res_2334_; 
v_collapsed_boxed_2332_ = lean_unbox(v_collapsed_2322_);
v_clsEnabled_boxed_2333_ = lean_unbox(v_clsEnabled_2325_);
v_res_2334_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2(v_cls_2321_, v_collapsed_boxed_2332_, v_tag_2323_, v_opts_2324_, v_clsEnabled_boxed_2333_, v_oldTraces_2326_, v_msg_2327_, v_resStartStop_2328_, v___y_2329_, v___y_2330_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec_ref(v_opts_2324_);
return v_res_2334_;
}
}
static double _init_l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2337_; double v___x_2338_; 
v___x_2337_ = lean_unsigned_to_nat(1000000000u);
v___x_2338_ = lean_float_of_nat(v___x_2337_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1(lean_object* v_decl_2339_, lean_object* v___x_2340_, uint8_t v___x_2341_, lean_object* v___x_2342_, lean_object* v___f_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v___y_2348_; lean_object* v___y_2349_; uint8_t v___y_2350_; lean_object* v___y_2361_; lean_object* v_a_2362_; lean_object* v___y_2366_; lean_object* v___y_2367_; uint8_t v___y_2368_; lean_object* v___y_2379_; lean_object* v_a_2380_; lean_object* v_options_2383_; uint8_t v_hasTrace_2384_; 
v_options_2383_ = lean_ctor_get(v___y_2344_, 2);
v_hasTrace_2384_ = lean_ctor_get_uint8(v_options_2383_, sizeof(void*)*1);
if (v_hasTrace_2384_ == 0)
{
lean_object* v_cancelTk_x3f_2385_; lean_object* v___x_2386_; 
lean_dec_ref(v___f_2343_);
lean_dec_ref(v___x_2342_);
lean_dec(v___x_2340_);
v_cancelTk_x3f_2385_ = lean_ctor_get(v___y_2344_, 12);
lean_inc(v_decl_2339_);
v___x_2386_ = l_Lean_warnIfUsesSorry(v_decl_2339_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v___x_2387_; lean_object* v_env_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
lean_dec_ref(v___x_2386_);
v___x_2387_ = lean_st_ref_get(v___y_2345_);
v_env_2388_ = lean_ctor_get(v___x_2387_, 0);
lean_inc_ref(v_env_2388_);
lean_dec(v___x_2387_);
v___x_2389_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2388_, v_options_2383_, v_decl_2339_, v_cancelTk_x3f_2385_);
v___x_2390_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_2389_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v___x_2392_; 
lean_dec(v_decl_2339_);
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2391_);
lean_dec_ref(v___x_2390_);
v___x_2392_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_2391_, v___y_2345_);
return v___x_2392_;
}
else
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
v_a_2393_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___x_2390_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2390_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
lean_inc(v_a_2393_);
if (v_isShared_2396_ == 0)
{
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2393_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
v___y_2379_ = v___x_2398_;
v_a_2380_ = v_a_2393_;
goto v___jp_2378_;
}
}
}
}
else
{
lean_dec(v_decl_2339_);
return v___x_2386_;
}
}
else
{
lean_object* v_cancelTk_x3f_2401_; lean_object* v_inheritedTraceOptions_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; uint8_t v___x_2405_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v_a_2409_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v_a_2424_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v_a_2429_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; uint8_t v___y_2441_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v_a_2446_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v_a_2452_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v_a_2464_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v_a_2469_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; uint8_t v___y_2481_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v_a_2486_; 
v_cancelTk_x3f_2401_ = lean_ctor_get(v___y_2344_, 12);
v_inheritedTraceOptions_2402_ = lean_ctor_get(v___y_2344_, 13);
v___x_2403_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v___x_2340_);
v___x_2404_ = l_Lean_Name_append(v___x_2403_, v___x_2340_);
v___x_2405_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2402_, v_options_2383_, v___x_2404_);
lean_dec(v___x_2404_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2514_; uint8_t v___x_2515_; 
v___x_2514_ = l_Lean_trace_profiler;
v___x_2515_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2383_, v___x_2514_);
if (v___x_2515_ == 0)
{
lean_object* v___x_2516_; 
lean_dec_ref(v___f_2343_);
lean_dec_ref(v___x_2342_);
lean_dec(v___x_2340_);
lean_inc(v_decl_2339_);
v___x_2516_ = l_Lean_warnIfUsesSorry(v_decl_2339_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v___x_2517_; lean_object* v_env_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
lean_dec_ref(v___x_2516_);
v___x_2517_ = lean_st_ref_get(v___y_2345_);
v_env_2518_ = lean_ctor_get(v___x_2517_, 0);
lean_inc_ref(v_env_2518_);
lean_dec(v___x_2517_);
v___x_2519_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2518_, v_options_2383_, v_decl_2339_, v_cancelTk_x3f_2401_);
v___x_2520_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_2519_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; lean_object* v___x_2522_; 
lean_dec(v_decl_2339_);
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2521_);
lean_dec_ref(v___x_2520_);
v___x_2522_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_2521_, v___y_2345_);
return v___x_2522_;
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
v_a_2523_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2520_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2520_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
lean_inc(v_a_2523_);
if (v_isShared_2526_ == 0)
{
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
v___y_2361_ = v___x_2528_;
v_a_2362_ = v_a_2523_;
goto v___jp_2360_;
}
}
}
}
else
{
lean_dec(v_decl_2339_);
return v___x_2516_;
}
}
else
{
goto v___jp_2489_;
}
}
else
{
goto v___jp_2489_;
}
v___jp_2406_:
{
lean_object* v___x_2410_; double v___x_2411_; double v___x_2412_; double v___x_2413_; double v___x_2414_; double v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2410_ = lean_io_mono_nanos_now();
v___x_2411_ = lean_float_of_nat(v___y_2407_);
v___x_2412_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__1);
v___x_2413_ = lean_float_div(v___x_2411_, v___x_2412_);
v___x_2414_ = lean_float_of_nat(v___x_2410_);
v___x_2415_ = lean_float_div(v___x_2414_, v___x_2412_);
v___x_2416_ = lean_box_float(v___x_2413_);
v___x_2417_ = lean_box_float(v___x_2415_);
v___x_2418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2416_);
lean_ctor_set(v___x_2418_, 1, v___x_2417_);
v___x_2419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2419_, 0, v_a_2409_);
lean_ctor_set(v___x_2419_, 1, v___x_2418_);
v___x_2420_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2(v___x_2340_, v___x_2341_, v___x_2342_, v_options_2383_, v___x_2405_, v___y_2408_, v___f_2343_, v___x_2419_, v___y_2344_, v___y_2345_);
return v___x_2420_;
}
v___jp_2421_:
{
lean_object* v___x_2425_; 
v___x_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2425_, 0, v_a_2424_);
v___y_2407_ = v___y_2422_;
v___y_2408_ = v___y_2423_;
v_a_2409_ = v___x_2425_;
goto v___jp_2406_;
}
v___jp_2426_:
{
lean_object* v___x_2430_; 
v___x_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2430_, 0, v_a_2429_);
v___y_2407_ = v___y_2427_;
v___y_2408_ = v___y_2428_;
v_a_2409_ = v___x_2430_;
goto v___jp_2406_;
}
v___jp_2431_:
{
if (lean_obj_tag(v___y_2434_) == 0)
{
lean_object* v_a_2435_; 
v_a_2435_ = lean_ctor_get(v___y_2434_, 0);
lean_inc(v_a_2435_);
lean_dec_ref(v___y_2434_);
v___y_2427_ = v___y_2432_;
v___y_2428_ = v___y_2433_;
v_a_2429_ = v_a_2435_;
goto v___jp_2426_;
}
else
{
lean_object* v_a_2436_; 
v_a_2436_ = lean_ctor_get(v___y_2434_, 0);
lean_inc(v_a_2436_);
lean_dec_ref(v___y_2434_);
v___y_2422_ = v___y_2432_;
v___y_2423_ = v___y_2433_;
v_a_2424_ = v_a_2436_;
goto v___jp_2421_;
}
}
v___jp_2437_:
{
if (v___y_2441_ == 0)
{
lean_object* v___x_2442_; 
v___x_2442_ = l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom(v_decl_2339_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_dec_ref(v___x_2442_);
v___y_2422_ = v___y_2438_;
v___y_2423_ = v___y_2440_;
v_a_2424_ = v___y_2439_;
goto v___jp_2421_;
}
else
{
lean_dec_ref(v___y_2439_);
v___y_2432_ = v___y_2438_;
v___y_2433_ = v___y_2440_;
v___y_2434_ = v___x_2442_;
goto v___jp_2431_;
}
}
else
{
lean_dec(v_decl_2339_);
v___y_2422_ = v___y_2438_;
v___y_2423_ = v___y_2440_;
v_a_2424_ = v___y_2439_;
goto v___jp_2421_;
}
}
v___jp_2443_:
{
uint8_t v___x_2447_; 
v___x_2447_ = l_Lean_Exception_isInterrupt(v_a_2446_);
if (v___x_2447_ == 0)
{
uint8_t v___x_2448_; 
lean_inc_ref(v_a_2446_);
v___x_2448_ = l_Lean_Exception_isRuntime(v_a_2446_);
v___y_2438_ = v___y_2444_;
v___y_2439_ = v_a_2446_;
v___y_2440_ = v___y_2445_;
v___y_2441_ = v___x_2448_;
goto v___jp_2437_;
}
else
{
v___y_2438_ = v___y_2444_;
v___y_2439_ = v_a_2446_;
v___y_2440_ = v___y_2445_;
v___y_2441_ = v___x_2447_;
goto v___jp_2437_;
}
}
v___jp_2449_:
{
lean_object* v___x_2453_; double v___x_2454_; double v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2453_ = lean_io_get_num_heartbeats();
v___x_2454_ = lean_float_of_nat(v___y_2450_);
v___x_2455_ = lean_float_of_nat(v___x_2453_);
v___x_2456_ = lean_box_float(v___x_2454_);
v___x_2457_ = lean_box_float(v___x_2455_);
v___x_2458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2456_);
lean_ctor_set(v___x_2458_, 1, v___x_2457_);
v___x_2459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2459_, 0, v_a_2452_);
lean_ctor_set(v___x_2459_, 1, v___x_2458_);
v___x_2460_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2(v___x_2340_, v___x_2341_, v___x_2342_, v_options_2383_, v___x_2405_, v___y_2451_, v___f_2343_, v___x_2459_, v___y_2344_, v___y_2345_);
return v___x_2460_;
}
v___jp_2461_:
{
lean_object* v___x_2465_; 
v___x_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2465_, 0, v_a_2464_);
v___y_2450_ = v___y_2462_;
v___y_2451_ = v___y_2463_;
v_a_2452_ = v___x_2465_;
goto v___jp_2449_;
}
v___jp_2466_:
{
lean_object* v___x_2470_; 
v___x_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2470_, 0, v_a_2469_);
v___y_2450_ = v___y_2467_;
v___y_2451_ = v___y_2468_;
v_a_2452_ = v___x_2470_;
goto v___jp_2449_;
}
v___jp_2471_:
{
if (lean_obj_tag(v___y_2474_) == 0)
{
lean_object* v_a_2475_; 
v_a_2475_ = lean_ctor_get(v___y_2474_, 0);
lean_inc(v_a_2475_);
lean_dec_ref(v___y_2474_);
v___y_2467_ = v___y_2472_;
v___y_2468_ = v___y_2473_;
v_a_2469_ = v_a_2475_;
goto v___jp_2466_;
}
else
{
lean_object* v_a_2476_; 
v_a_2476_ = lean_ctor_get(v___y_2474_, 0);
lean_inc(v_a_2476_);
lean_dec_ref(v___y_2474_);
v___y_2462_ = v___y_2472_;
v___y_2463_ = v___y_2473_;
v_a_2464_ = v_a_2476_;
goto v___jp_2461_;
}
}
v___jp_2477_:
{
if (v___y_2481_ == 0)
{
lean_object* v___x_2482_; 
v___x_2482_ = l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom(v_decl_2339_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_dec_ref(v___x_2482_);
v___y_2462_ = v___y_2478_;
v___y_2463_ = v___y_2480_;
v_a_2464_ = v___y_2479_;
goto v___jp_2461_;
}
else
{
lean_dec_ref(v___y_2479_);
v___y_2472_ = v___y_2478_;
v___y_2473_ = v___y_2480_;
v___y_2474_ = v___x_2482_;
goto v___jp_2471_;
}
}
else
{
lean_dec(v_decl_2339_);
v___y_2462_ = v___y_2478_;
v___y_2463_ = v___y_2480_;
v_a_2464_ = v___y_2479_;
goto v___jp_2461_;
}
}
v___jp_2483_:
{
uint8_t v___x_2487_; 
v___x_2487_ = l_Lean_Exception_isInterrupt(v_a_2486_);
if (v___x_2487_ == 0)
{
uint8_t v___x_2488_; 
lean_inc_ref(v_a_2486_);
v___x_2488_ = l_Lean_Exception_isRuntime(v_a_2486_);
v___y_2478_ = v___y_2484_;
v___y_2479_ = v_a_2486_;
v___y_2480_ = v___y_2485_;
v___y_2481_ = v___x_2488_;
goto v___jp_2477_;
}
else
{
v___y_2478_ = v___y_2484_;
v___y_2479_ = v_a_2486_;
v___y_2480_ = v___y_2485_;
v___y_2481_ = v___x_2487_;
goto v___jp_2477_;
}
}
v___jp_2489_:
{
lean_object* v___x_2490_; lean_object* v_a_2491_; lean_object* v___x_2492_; uint8_t v___x_2493_; 
v___x_2490_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v___y_2345_);
v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
lean_inc(v_a_2491_);
lean_dec_ref(v___x_2490_);
v___x_2492_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2493_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2383_, v___x_2492_);
if (v___x_2493_ == 0)
{
lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2494_ = lean_io_mono_nanos_now();
lean_inc(v_decl_2339_);
v___x_2495_ = l_Lean_warnIfUsesSorry(v_decl_2339_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v___x_2496_; lean_object* v_env_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
lean_dec_ref(v___x_2495_);
v___x_2496_ = lean_st_ref_get(v___y_2345_);
v_env_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc_ref(v_env_2497_);
lean_dec(v___x_2496_);
v___x_2498_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2497_, v_options_2383_, v_decl_2339_, v_cancelTk_x3f_2401_);
v___x_2499_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_2498_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; lean_object* v___x_2501_; lean_object* v_a_2502_; 
lean_dec(v_decl_2339_);
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_a_2500_);
lean_dec_ref(v___x_2499_);
v___x_2501_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_2500_, v___y_2345_);
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_a_2502_);
lean_dec_ref(v___x_2501_);
v___y_2427_ = v___x_2494_;
v___y_2428_ = v_a_2491_;
v_a_2429_ = v_a_2502_;
goto v___jp_2426_;
}
else
{
lean_object* v_a_2503_; 
v_a_2503_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_a_2503_);
lean_dec_ref(v___x_2499_);
v___y_2444_ = v___x_2494_;
v___y_2445_ = v_a_2491_;
v_a_2446_ = v_a_2503_;
goto v___jp_2443_;
}
}
else
{
lean_dec(v_decl_2339_);
v___y_2432_ = v___x_2494_;
v___y_2433_ = v_a_2491_;
v___y_2434_ = v___x_2495_;
goto v___jp_2431_;
}
}
else
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2504_ = lean_io_get_num_heartbeats();
lean_inc(v_decl_2339_);
v___x_2505_ = l_Lean_warnIfUsesSorry(v_decl_2339_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v___x_2506_; lean_object* v_env_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
lean_dec_ref(v___x_2505_);
v___x_2506_ = lean_st_ref_get(v___y_2345_);
v_env_2507_ = lean_ctor_get(v___x_2506_, 0);
lean_inc_ref(v_env_2507_);
lean_dec(v___x_2506_);
v___x_2508_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2507_, v_options_2383_, v_decl_2339_, v_cancelTk_x3f_2401_);
v___x_2509_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0___redArg(v___x_2508_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v_a_2510_; lean_object* v___x_2511_; lean_object* v_a_2512_; 
lean_dec(v_decl_2339_);
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_a_2510_);
lean_dec_ref(v___x_2509_);
v___x_2511_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_a_2510_, v___y_2345_);
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2512_);
lean_dec_ref(v___x_2511_);
v___y_2467_ = v___x_2504_;
v___y_2468_ = v_a_2491_;
v_a_2469_ = v_a_2512_;
goto v___jp_2466_;
}
else
{
lean_object* v_a_2513_; 
v_a_2513_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_a_2513_);
lean_dec_ref(v___x_2509_);
v___y_2484_ = v___x_2504_;
v___y_2485_ = v_a_2491_;
v_a_2486_ = v_a_2513_;
goto v___jp_2483_;
}
}
else
{
lean_dec(v_decl_2339_);
v___y_2472_ = v___x_2504_;
v___y_2473_ = v_a_2491_;
v___y_2474_ = v___x_2505_;
goto v___jp_2471_;
}
}
}
}
v___jp_2347_:
{
if (v___y_2350_ == 0)
{
lean_object* v___x_2351_; 
lean_dec_ref(v___y_2349_);
v___x_2351_ = l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom(v_decl_2339_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2358_ == 0)
{
lean_object* v_unused_2359_; 
v_unused_2359_ = lean_ctor_get(v___x_2351_, 0);
lean_dec(v_unused_2359_);
v___x_2353_ = v___x_2351_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_dec(v___x_2351_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
lean_ctor_set_tag(v___x_2353_, 1);
lean_ctor_set(v___x_2353_, 0, v___y_2348_);
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___y_2348_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
else
{
lean_dec_ref(v___y_2348_);
return v___x_2351_;
}
}
else
{
lean_dec_ref(v___y_2348_);
lean_dec(v_decl_2339_);
return v___y_2349_;
}
}
v___jp_2360_:
{
uint8_t v___x_2363_; 
v___x_2363_ = l_Lean_Exception_isInterrupt(v_a_2362_);
if (v___x_2363_ == 0)
{
uint8_t v___x_2364_; 
lean_inc_ref(v_a_2362_);
v___x_2364_ = l_Lean_Exception_isRuntime(v_a_2362_);
v___y_2348_ = v_a_2362_;
v___y_2349_ = v___y_2361_;
v___y_2350_ = v___x_2364_;
goto v___jp_2347_;
}
else
{
v___y_2348_ = v_a_2362_;
v___y_2349_ = v___y_2361_;
v___y_2350_ = v___x_2363_;
goto v___jp_2347_;
}
}
v___jp_2365_:
{
if (v___y_2368_ == 0)
{
lean_object* v___x_2369_; 
lean_dec_ref(v___y_2367_);
v___x_2369_ = l___private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom(v_decl_2339_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2376_ == 0)
{
lean_object* v_unused_2377_; 
v_unused_2377_ = lean_ctor_get(v___x_2369_, 0);
lean_dec(v_unused_2377_);
v___x_2371_ = v___x_2369_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_dec(v___x_2369_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
lean_ctor_set_tag(v___x_2371_, 1);
lean_ctor_set(v___x_2371_, 0, v___y_2366_);
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___y_2366_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
else
{
lean_dec_ref(v___y_2366_);
return v___x_2369_;
}
}
else
{
lean_dec_ref(v___y_2366_);
lean_dec(v_decl_2339_);
return v___y_2367_;
}
}
v___jp_2378_:
{
uint8_t v___x_2381_; 
v___x_2381_ = l_Lean_Exception_isInterrupt(v_a_2380_);
if (v___x_2381_ == 0)
{
uint8_t v___x_2382_; 
lean_inc_ref(v_a_2380_);
v___x_2382_ = l_Lean_Exception_isRuntime(v_a_2380_);
v___y_2366_ = v_a_2380_;
v___y_2367_ = v___y_2379_;
v___y_2368_ = v___x_2382_;
goto v___jp_2365_;
}
else
{
v___y_2366_ = v_a_2380_;
v___y_2367_ = v___y_2379_;
v___y_2368_ = v___x_2381_;
goto v___jp_2365_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___boxed(lean_object* v_decl_2531_, lean_object* v___x_2532_, lean_object* v___x_2533_, lean_object* v___x_2534_, lean_object* v___f_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
uint8_t v___x_8044__boxed_2539_; lean_object* v_res_2540_; 
v___x_8044__boxed_2539_ = lean_unbox(v___x_2533_);
v_res_2540_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1(v_decl_2531_, v___x_2532_, v___x_8044__boxed_2539_, v___x_2534_, v___f_2535_, v___y_2536_, v___y_2537_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(lean_object* v_decl_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_){
_start:
{
lean_object* v_options_2549_; lean_object* v___f_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; uint8_t v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___f_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v_options_2549_ = lean_ctor_get(v_a_2546_, 2);
lean_inc(v_decl_2545_);
v___f_2550_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2550_, 0, v_decl_2545_);
v___x_2551_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___closed__0));
v___x_2552_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___closed__2));
v___x_2553_ = 1;
v___x_2554_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2555_ = lean_box(v___x_2553_);
v___f_2556_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___boxed), 8, 5);
lean_closure_set(v___f_2556_, 0, v_decl_2545_);
lean_closure_set(v___f_2556_, 1, v___x_2552_);
lean_closure_set(v___f_2556_, 2, v___x_2555_);
lean_closure_set(v___f_2556_, 3, v___x_2554_);
lean_closure_set(v___f_2556_, 4, v___f_2550_);
v___x_2557_ = lean_box(0);
v___x_2558_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__3___redArg(v___x_2551_, v_options_2549_, v___f_2556_, v___x_2557_, v_a_2546_, v_a_2547_);
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___boxed(lean_object* v_decl_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_2559_, v_a_2560_, v_a_2561_);
lean_dec(v_a_2561_);
lean_dec_ref(v_a_2560_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4(lean_object* v_00_u03b1_2564_, lean_object* v_x_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v___x_2569_; 
v___x_2569_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4___redArg(v_x_2565_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2570_, lean_object* v_x_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2_spec__4(v_00_u03b1_2570_, v_x_2571_, v___y_2572_, v___y_2573_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__0(lean_object* v___y_2576_, lean_object* v_a_2577_, lean_object* v___y_2578_, lean_object* v_a_x3f_2579_){
_start:
{
lean_object* v___x_2581_; lean_object* v_env_2582_; lean_object* v___x_2583_; 
v___x_2581_ = lean_st_ref_get(v___y_2576_);
v_env_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc_ref(v_env_2582_);
lean_dec(v___x_2581_);
v___x_2583_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2577_, v_env_2582_);
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
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2604_; 
v_a_2592_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2594_ = v___x_2583_;
v_isShared_2595_ = v_isSharedCheck_2604_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2583_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2604_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v_ref_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2602_; 
v_ref_2596_ = lean_ctor_get(v___y_2578_, 5);
v___x_2597_ = lean_io_error_to_string(v_a_2592_);
v___x_2598_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2597_);
v___x_2599_ = l_Lean_MessageData_ofFormat(v___x_2598_);
lean_inc(v_ref_2596_);
v___x_2600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2600_, 0, v_ref_2596_);
lean_ctor_set(v___x_2600_, 1, v___x_2599_);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v___x_2600_);
v___x_2602_ = v___x_2594_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2600_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__0___boxed(lean_object* v___y_2605_, lean_object* v_a_2606_, lean_object* v___y_2607_, lean_object* v_a_x3f_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l_Lean_addDecl___lam__0(v___y_2605_, v_a_2606_, v___y_2607_, v_a_x3f_2608_);
lean_dec(v_a_x3f_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2605_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__2(lean_object* v_asyncEnv_2611_, lean_object* v_a_2612_, lean_object* v_decl_2613_, lean_object* v_x_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
lean_object* v___x_2618_; lean_object* v_r_2619_; 
v___x_2618_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v_asyncEnv_2611_, v___y_2616_);
lean_dec_ref(v___x_2618_);
v_r_2619_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_2613_, v___y_2615_, v___y_2616_);
if (lean_obj_tag(v_r_2619_) == 0)
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2636_; 
v_a_2620_ = lean_ctor_get(v_r_2619_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v_r_2619_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2622_ = v_r_2619_;
v_isShared_2623_ = v_isSharedCheck_2636_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v_r_2619_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2636_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
lean_inc(v_a_2620_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set_tag(v___x_2622_, 1);
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
lean_object* v___x_2626_; 
v___x_2626_ = l_Lean_addDecl___lam__0(v___y_2616_, v_a_2612_, v___y_2615_, v___x_2625_);
lean_dec_ref(v___x_2625_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2633_; 
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2633_ == 0)
{
lean_object* v_unused_2634_; 
v_unused_2634_ = lean_ctor_get(v___x_2626_, 0);
lean_dec(v_unused_2634_);
v___x_2628_ = v___x_2626_;
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
else
{
lean_dec(v___x_2626_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 0, v_a_2620_);
v___x_2631_ = v___x_2628_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2620_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
else
{
lean_dec(v_a_2620_);
return v___x_2626_;
}
}
}
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v_a_2637_ = lean_ctor_get(v_r_2619_, 0);
lean_inc(v_a_2637_);
lean_dec_ref(v_r_2619_);
v___x_2638_ = lean_box(0);
v___x_2639_ = l_Lean_addDecl___lam__0(v___y_2616_, v_a_2612_, v___y_2615_, v___x_2638_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2646_ == 0)
{
lean_object* v_unused_2647_; 
v_unused_2647_ = lean_ctor_get(v___x_2639_, 0);
lean_dec(v_unused_2647_);
v___x_2641_ = v___x_2639_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_dec(v___x_2639_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
lean_ctor_set_tag(v___x_2641_, 1);
lean_ctor_set(v___x_2641_, 0, v_a_2637_);
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2637_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
else
{
lean_dec(v_a_2637_);
return v___x_2639_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__2___boxed(lean_object* v_asyncEnv_2648_, lean_object* v_a_2649_, lean_object* v_decl_2650_, lean_object* v_x_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v_res_2655_; 
v_res_2655_ = l_Lean_addDecl___lam__2(v_asyncEnv_2648_, v_a_2649_, v_decl_2650_, v_x_2651_, v___y_2652_, v___y_2653_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec_ref(v_x_2651_);
return v_res_2655_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = ((lean_object*)(l_Lean_addDecl___lam__1___closed__0));
v___x_2658_ = l_Lean_stringToMessageData(v___x_2657_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__1(lean_object* v_decl_2659_, lean_object* v_x_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2664_ = lean_obj_once(&l_Lean_addDecl___lam__1___closed__1, &l_Lean_addDecl___lam__1___closed__1_once, _init_l_Lean_addDecl___lam__1___closed__1);
v___x_2665_ = l_Lean_Declaration_getNames(v_decl_2659_);
v___x_2666_ = lean_box(0);
v___x_2667_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__0(v___x_2665_, v___x_2666_);
v___x_2668_ = l_Lean_MessageData_ofList(v___x_2667_);
v___x_2669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2664_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
v___x_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__1___boxed(lean_object* v_decl_2671_, lean_object* v_x_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_Lean_addDecl___lam__1(v_decl_2671_, v_x_2672_, v___y_2673_, v___y_2674_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec_ref(v_x_2672_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_addDecl_spec__0(lean_object* v_cls_2679_, lean_object* v_msg_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
lean_object* v_ref_2684_; lean_object* v___x_2685_; lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2730_; 
v_ref_2684_ = lean_ctor_get(v___y_2681_, 5);
v___x_2685_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2680_, v___y_2681_, v___y_2682_);
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2688_ = v___x_2685_;
v_isShared_2689_ = v_isSharedCheck_2730_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2685_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2730_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2690_; lean_object* v_traceState_2691_; lean_object* v_env_2692_; lean_object* v_nextMacroScope_2693_; lean_object* v_ngen_2694_; lean_object* v_auxDeclNGen_2695_; lean_object* v_cache_2696_; lean_object* v_messages_2697_; lean_object* v_infoState_2698_; lean_object* v_snapshotTasks_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2729_; 
v___x_2690_ = lean_st_ref_take(v___y_2682_);
v_traceState_2691_ = lean_ctor_get(v___x_2690_, 4);
v_env_2692_ = lean_ctor_get(v___x_2690_, 0);
v_nextMacroScope_2693_ = lean_ctor_get(v___x_2690_, 1);
v_ngen_2694_ = lean_ctor_get(v___x_2690_, 2);
v_auxDeclNGen_2695_ = lean_ctor_get(v___x_2690_, 3);
v_cache_2696_ = lean_ctor_get(v___x_2690_, 5);
v_messages_2697_ = lean_ctor_get(v___x_2690_, 6);
v_infoState_2698_ = lean_ctor_get(v___x_2690_, 7);
v_snapshotTasks_2699_ = lean_ctor_get(v___x_2690_, 8);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2701_ = v___x_2690_;
v_isShared_2702_ = v_isSharedCheck_2729_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_snapshotTasks_2699_);
lean_inc(v_infoState_2698_);
lean_inc(v_messages_2697_);
lean_inc(v_cache_2696_);
lean_inc(v_traceState_2691_);
lean_inc(v_auxDeclNGen_2695_);
lean_inc(v_ngen_2694_);
lean_inc(v_nextMacroScope_2693_);
lean_inc(v_env_2692_);
lean_dec(v___x_2690_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2729_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
uint64_t v_tid_2703_; lean_object* v_traces_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2728_; 
v_tid_2703_ = lean_ctor_get_uint64(v_traceState_2691_, sizeof(void*)*1);
v_traces_2704_ = lean_ctor_get(v_traceState_2691_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v_traceState_2691_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2706_ = v_traceState_2691_;
v_isShared_2707_ = v_isSharedCheck_2728_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_traces_2704_);
lean_dec(v_traceState_2691_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2728_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2708_; double v___x_2709_; uint8_t v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2718_; 
v___x_2708_ = lean_box(0);
v___x_2709_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2___closed__2);
v___x_2710_ = 0;
v___x_2711_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2712_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2712_, 0, v_cls_2679_);
lean_ctor_set(v___x_2712_, 1, v___x_2708_);
lean_ctor_set(v___x_2712_, 2, v___x_2711_);
lean_ctor_set_float(v___x_2712_, sizeof(void*)*3, v___x_2709_);
lean_ctor_set_float(v___x_2712_, sizeof(void*)*3 + 8, v___x_2709_);
lean_ctor_set_uint8(v___x_2712_, sizeof(void*)*3 + 16, v___x_2710_);
v___x_2713_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_addDecl_spec__0___closed__0));
v___x_2714_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2712_);
lean_ctor_set(v___x_2714_, 1, v_a_2686_);
lean_ctor_set(v___x_2714_, 2, v___x_2713_);
lean_inc(v_ref_2684_);
v___x_2715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2715_, 0, v_ref_2684_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v___x_2716_ = l_Lean_PersistentArray_push___redArg(v_traces_2704_, v___x_2715_);
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 0, v___x_2716_);
v___x_2718_ = v___x_2706_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___x_2716_);
lean_ctor_set_uint64(v_reuseFailAlloc_2727_, sizeof(void*)*1, v_tid_2703_);
v___x_2718_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
lean_object* v___x_2720_; 
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 4, v___x_2718_);
v___x_2720_ = v___x_2701_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_env_2692_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v_nextMacroScope_2693_);
lean_ctor_set(v_reuseFailAlloc_2726_, 2, v_ngen_2694_);
lean_ctor_set(v_reuseFailAlloc_2726_, 3, v_auxDeclNGen_2695_);
lean_ctor_set(v_reuseFailAlloc_2726_, 4, v___x_2718_);
lean_ctor_set(v_reuseFailAlloc_2726_, 5, v_cache_2696_);
lean_ctor_set(v_reuseFailAlloc_2726_, 6, v_messages_2697_);
lean_ctor_set(v_reuseFailAlloc_2726_, 7, v_infoState_2698_);
lean_ctor_set(v_reuseFailAlloc_2726_, 8, v_snapshotTasks_2699_);
v___x_2720_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2724_; 
v___x_2721_ = lean_st_ref_set(v___y_2682_, v___x_2720_);
v___x_2722_ = lean_box(0);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2722_);
v___x_2724_ = v___x_2688_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2722_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_addDecl_spec__0___boxed(lean_object* v_cls_2731_, lean_object* v_msg_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_2731_, v_msg_2732_, v___y_2733_, v___y_2734_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
return v_res_2736_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2738_ = ((lean_object*)(l_Lean_addDecl___lam__3___closed__0));
v___x_2739_ = l_Lean_stringToMessageData(v___x_2738_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__3(lean_object* v_decl_2740_, lean_object* v_cls_2741_, lean_object* v_x_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
lean_object* v_options_2746_; uint8_t v_hasTrace_2747_; 
v_options_2746_ = lean_ctor_get(v___y_2743_, 2);
v_hasTrace_2747_ = lean_ctor_get_uint8(v_options_2746_, sizeof(void*)*1);
if (v_hasTrace_2747_ == 0)
{
lean_object* v___x_2748_; 
lean_dec(v_cls_2741_);
v___x_2748_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_2740_, v___y_2743_, v___y_2744_);
return v___x_2748_;
}
else
{
lean_object* v_inheritedTraceOptions_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; uint8_t v___x_2752_; 
v_inheritedTraceOptions_2749_ = lean_ctor_get(v___y_2743_, 13);
v___x_2750_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v_cls_2741_);
v___x_2751_ = l_Lean_Name_append(v___x_2750_, v_cls_2741_);
v___x_2752_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2749_, v_options_2746_, v___x_2751_);
lean_dec(v___x_2751_);
if (v___x_2752_ == 0)
{
lean_object* v___x_2753_; 
lean_dec(v_cls_2741_);
v___x_2753_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_2740_, v___y_2743_, v___y_2744_);
return v___x_2753_;
}
else
{
lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2754_ = lean_obj_once(&l_Lean_addDecl___lam__3___closed__1, &l_Lean_addDecl___lam__3___closed__1_once, _init_l_Lean_addDecl___lam__3___closed__1);
v___x_2755_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_2741_, v___x_2754_, v___y_2743_, v___y_2744_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v___x_2756_; 
lean_dec_ref(v___x_2755_);
v___x_2756_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_2740_, v___y_2743_, v___y_2744_);
return v___x_2756_;
}
else
{
lean_dec(v_decl_2740_);
return v___x_2755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__3___boxed(lean_object* v_decl_2757_, lean_object* v_cls_2758_, lean_object* v_x_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l_Lean_addDecl___lam__3(v_decl_2757_, v_cls_2758_, v_x_2759_, v___y_2760_, v___y_2761_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v_x_2759_);
return v_res_2763_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_addDecl_spec__2(lean_object* v_x_2764_){
_start:
{
if (lean_obj_tag(v_x_2764_) == 0)
{
uint8_t v___x_2765_; 
v___x_2765_ = 1;
return v___x_2765_;
}
else
{
lean_object* v_head_2766_; lean_object* v_tail_2767_; uint8_t v___x_2768_; 
v_head_2766_ = lean_ctor_get(v_x_2764_, 0);
v_tail_2767_ = lean_ctor_get(v_x_2764_, 1);
v___x_2768_ = l_Lean_isPrivateName(v_head_2766_);
if (v___x_2768_ == 0)
{
return v___x_2768_;
}
else
{
v_x_2764_ = v_tail_2767_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_addDecl_spec__2___boxed(lean_object* v_x_2770_){
_start:
{
uint8_t v_res_2771_; lean_object* v_r_2772_; 
v_res_2771_ = l_List_all___at___00Lean_addDecl_spec__2(v_x_2770_);
lean_dec(v_x_2770_);
v_r_2772_ = lean_box(v_res_2771_);
return v_r_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_addDecl_spec__3___redArg(lean_object* v_opt_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v_options_2776_; uint8_t v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
v_options_2776_ = lean_ctor_get(v___y_2774_, 2);
v___x_2777_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2776_, v_opt_2773_);
v___x_2778_ = lean_box(v___x_2777_);
v___x_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2778_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_addDecl_spec__3___redArg___boxed(lean_object* v_opt_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__3___redArg(v_opt_2780_, v___y_2781_);
lean_dec_ref(v___y_2781_);
lean_dec_ref(v_opt_2780_);
return v_res_2783_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__8___closed__1(void){
_start:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2785_ = ((lean_object*)(l_Lean_addDecl___lam__8___closed__0));
v___x_2786_ = l_Lean_stringToMessageData(v___x_2785_);
return v___x_2786_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__8___closed__3(void){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = ((lean_object*)(l_Lean_addDecl___lam__8___closed__2));
v___x_2789_ = l_Lean_stringToMessageData(v___x_2788_);
return v___x_2789_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__8___closed__5(void){
_start:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2791_ = ((lean_object*)(l_Lean_addDecl___lam__8___closed__4));
v___x_2792_ = l_Lean_stringToMessageData(v___x_2791_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__8(lean_object* v_decl_2793_, lean_object* v___x_2794_, uint8_t v_hasTrace_2795_, uint8_t v___x_2796_, lean_object* v___x_2797_, lean_object* v_cls_2798_, lean_object* v___x_2799_, lean_object* v_____x_2800_, lean_object* v_exportedInfo_x3f_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v_a_2808_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v_a_2821_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v_snd_2905_; lean_object* v_fst_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_3033_; 
v_snd_2905_ = lean_ctor_get(v_____x_2800_, 1);
v_fst_2906_ = lean_ctor_get(v_____x_2800_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v_____x_2800_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_2908_ = v_____x_2800_;
v_isShared_2909_ = v_isSharedCheck_3033_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_snd_2905_);
lean_inc(v_fst_2906_);
lean_dec(v_____x_2800_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_3033_;
goto v_resetjp_2907_;
}
v___jp_2805_:
{
lean_object* v___x_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
v___x_2809_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_2806_, v___y_2807_);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2816_ == 0)
{
lean_object* v_unused_2817_; 
v_unused_2817_ = lean_ctor_get(v___x_2809_, 0);
lean_dec(v_unused_2817_);
v___x_2811_ = v___x_2809_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_dec(v___x_2809_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
lean_ctor_set_tag(v___x_2811_, 1);
lean_ctor_set(v___x_2811_, 0, v_a_2808_);
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2808_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
v___jp_2818_:
{
lean_object* v___x_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
v___x_2822_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_2819_, v___y_2820_);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2829_ == 0)
{
lean_object* v_unused_2830_; 
v_unused_2830_ = lean_ctor_get(v___x_2822_, 0);
lean_dec(v_unused_2830_);
v___x_2824_ = v___x_2822_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_dec(v___x_2822_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 0, v_a_2821_);
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2821_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
v___jp_2831_:
{
lean_object* v___x_2842_; 
lean_inc_ref(v___y_2839_);
v___x_2842_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_2837_, v___y_2839_, v___y_2836_, v___y_2841_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v___x_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2890_; 
lean_dec_ref(v___x_2842_);
lean_inc_ref(v___y_2833_);
v___x_2843_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_2833_, v___y_2834_);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2890_ == 0)
{
lean_object* v_unused_2891_; 
v_unused_2891_ = lean_ctor_get(v___x_2843_, 0);
lean_dec(v_unused_2891_);
v___x_2845_ = v___x_2843_;
v_isShared_2846_ = v_isSharedCheck_2890_;
goto v_resetjp_2844_;
}
else
{
lean_dec(v___x_2843_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2890_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v_options_2847_; lean_object* v___x_2848_; uint8_t v___x_2849_; 
v_options_2847_ = lean_ctor_get(v___y_2832_, 2);
v___x_2848_ = l_Lean_Elab_async;
v___x_2849_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2847_, v___x_2848_);
if (v___x_2849_ == 0)
{
lean_object* v___x_2850_; lean_object* v_r_2851_; 
lean_del_object(v___x_2845_);
lean_dec_ref(v___y_2840_);
lean_dec_ref(v___y_2835_);
lean_dec_ref(v___x_2794_);
v___x_2850_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_2839_, v___y_2834_);
lean_dec_ref(v___x_2850_);
v_r_2851_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_2793_, v___y_2832_, v___y_2834_);
if (lean_obj_tag(v_r_2851_) == 0)
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2861_; 
v_a_2852_ = lean_ctor_get(v_r_2851_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v_r_2851_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2854_ = v_r_2851_;
v_isShared_2855_ = v_isSharedCheck_2861_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v_r_2851_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2861_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
lean_inc(v_a_2852_);
if (v_isShared_2855_ == 0)
{
lean_ctor_set_tag(v___x_2854_, 1);
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2852_);
v___x_2857_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
lean_object* v___x_2858_; 
v___x_2858_ = lean_apply_2(v___y_2838_, v___x_2857_, lean_box(0));
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_dec_ref(v___x_2858_);
v___y_2819_ = v___y_2833_;
v___y_2820_ = v___y_2834_;
v_a_2821_ = v_a_2852_;
goto v___jp_2818_;
}
else
{
lean_object* v_a_2859_; 
lean_dec(v_a_2852_);
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_a_2859_);
lean_dec_ref(v___x_2858_);
v___y_2806_ = v___y_2833_;
v___y_2807_ = v___y_2834_;
v_a_2808_ = v_a_2859_;
goto v___jp_2805_;
}
}
}
}
else
{
lean_object* v_a_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v_a_2862_ = lean_ctor_get(v_r_2851_, 0);
lean_inc(v_a_2862_);
lean_dec_ref(v_r_2851_);
v___x_2863_ = lean_box(0);
v___x_2864_ = lean_apply_2(v___y_2838_, v___x_2863_, lean_box(0));
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_dec_ref(v___x_2864_);
v___y_2806_ = v___y_2833_;
v___y_2807_ = v___y_2834_;
v_a_2808_ = v_a_2862_;
goto v___jp_2805_;
}
else
{
lean_object* v_a_2865_; 
lean_dec(v_a_2862_);
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2865_);
lean_dec_ref(v___x_2864_);
v___y_2806_ = v___y_2833_;
v___y_2807_ = v___y_2834_;
v_a_2808_ = v_a_2865_;
goto v___jp_2805_;
}
}
}
else
{
lean_object* v___x_2866_; lean_object* v___x_2868_; 
lean_dec_ref(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec_ref(v___y_2833_);
lean_dec(v_decl_2793_);
v___x_2866_ = l_IO_CancelToken_new();
if (v_isShared_2846_ == 0)
{
lean_ctor_set_tag(v___x_2845_, 1);
lean_ctor_set(v___x_2845_, 0, v___x_2866_);
v___x_2868_ = v___x_2845_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2866_);
v___x_2868_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2869_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__5_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_2870_ = l_Lean_Name_mkStr2(v___x_2869_, v___x_2794_);
v___x_2871_ = l_Lean_Name_toString(v___x_2870_, v_hasTrace_2795_);
lean_inc_ref(v___x_2868_);
v___x_2872_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_2840_, v___x_2868_, v___x_2871_, v___y_2832_, v___y_2834_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_a_2873_; lean_object* v_checked_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_a_2873_);
lean_dec_ref(v___x_2872_);
v_checked_2874_ = lean_ctor_get(v___y_2835_, 2);
lean_inc_ref(v_checked_2874_);
lean_dec_ref(v___y_2835_);
v___x_2875_ = lean_unsigned_to_nat(0u);
v___x_2876_ = lean_io_map_task(v_a_2873_, v_checked_2874_, v___x_2875_, v___x_2796_);
v___x_2877_ = lean_box(0);
v___x_2878_ = lean_box(2);
v___x_2879_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2877_);
lean_ctor_set(v___x_2879_, 1, v___x_2878_);
lean_ctor_set(v___x_2879_, 2, v___x_2868_);
lean_ctor_set(v___x_2879_, 3, v___x_2876_);
v___x_2880_ = l_Lean_Core_logSnapshotTask___redArg(v___x_2879_, v___y_2834_);
return v___x_2880_;
}
else
{
lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2888_; 
lean_dec_ref(v___x_2868_);
lean_dec_ref(v___y_2835_);
v_a_2881_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2883_ = v___x_2872_;
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_dec(v___x_2872_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2886_; 
if (v_isShared_2884_ == 0)
{
v___x_2886_ = v___x_2883_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2881_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2904_; 
lean_dec_ref(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec_ref(v___y_2835_);
lean_dec_ref(v___y_2833_);
lean_dec_ref(v___x_2794_);
lean_dec(v_decl_2793_);
v_a_2892_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2894_ = v___x_2842_;
v_isShared_2895_ = v_isSharedCheck_2904_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2842_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2904_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v_ref_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2902_; 
v_ref_2896_ = lean_ctor_get(v___y_2832_, 5);
v___x_2897_ = lean_io_error_to_string(v_a_2892_);
v___x_2898_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2897_);
v___x_2899_ = l_Lean_MessageData_ofFormat(v___x_2898_);
lean_inc(v_ref_2896_);
v___x_2900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2900_, 0, v_ref_2896_);
lean_ctor_set(v___x_2900_, 1, v___x_2899_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 0, v___x_2900_);
v___x_2902_ = v___x_2894_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v___x_2900_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
v_resetjp_2907_:
{
lean_object* v_fst_2910_; lean_object* v_snd_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_3032_; 
v_fst_2910_ = lean_ctor_get(v_snd_2905_, 0);
v_snd_2911_ = lean_ctor_get(v_snd_2905_, 1);
v_isSharedCheck_3032_ = !lean_is_exclusive(v_snd_2905_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_2913_ = v_snd_2905_;
v_isShared_2914_ = v_isSharedCheck_3032_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_snd_2911_);
lean_inc(v_fst_2910_);
lean_dec(v_snd_2905_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_3032_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v_exportedInfo_x3f_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___x_3022_; lean_object* v_env_3023_; uint8_t v___x_3024_; 
v___x_3022_ = lean_st_ref_get(v___y_2803_);
v_env_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc_ref(v_env_3023_);
lean_dec(v___x_3022_);
v___x_3024_ = l_Lean_Environment_containsOnBranch(v_env_3023_, v_fst_2906_);
lean_dec_ref(v_env_3023_);
if (v___x_3024_ == 0)
{
lean_del_object(v___x_2908_);
v___y_2990_ = v___y_2802_;
v___y_2991_ = v___y_2803_;
goto v___jp_2989_;
}
else
{
lean_object* v___x_3025_; lean_object* v_env_3026_; lean_object* v___x_3027_; lean_object* v___x_3029_; 
lean_del_object(v___x_2913_);
lean_dec(v_snd_2911_);
lean_dec(v_fst_2910_);
lean_dec(v_exportedInfo_x3f_2801_);
lean_dec(v___x_2799_);
lean_dec(v_cls_2798_);
lean_dec_ref(v___x_2797_);
lean_dec_ref(v___x_2794_);
lean_dec(v_decl_2793_);
v___x_3025_ = lean_st_ref_get(v___y_2803_);
v_env_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc_ref(v_env_3026_);
lean_dec(v___x_3025_);
v___x_3027_ = lean_elab_environment_to_kernel_env(v_env_3026_);
if (v_isShared_2909_ == 0)
{
lean_ctor_set_tag(v___x_2908_, 1);
lean_ctor_set(v___x_2908_, 1, v_fst_2906_);
lean_ctor_set(v___x_2908_, 0, v___x_3027_);
v___x_3029_ = v___x_2908_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v___x_3027_);
lean_ctor_set(v_reuseFailAlloc_3031_, 1, v_fst_2906_);
v___x_3029_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
lean_object* v___x_3030_; 
v___x_3030_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(v___x_3029_, v___y_2802_, v___y_2803_);
return v___x_3030_;
}
}
v___jp_2915_:
{
uint8_t v___x_2923_; lean_object* v___x_2924_; 
v___x_2923_ = lean_unbox(v_snd_2911_);
lean_dec(v_snd_2911_);
lean_inc_ref(v___y_2916_);
v___x_2924_ = l_Lean_Environment_addConstAsync(v___y_2916_, v_fst_2906_, v___x_2923_, v___y_2922_, v___x_2796_, v_hasTrace_2795_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v_mainEnv_2926_; lean_object* v_asyncEnv_2927_; lean_object* v___f_2928_; lean_object* v___f_2929_; lean_object* v___x_2930_; 
lean_del_object(v___x_2913_);
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
lean_inc_n(v_a_2925_, 3);
lean_dec_ref(v___x_2924_);
v_mainEnv_2926_ = lean_ctor_get(v_a_2925_, 0);
lean_inc_ref(v_mainEnv_2926_);
v_asyncEnv_2927_ = lean_ctor_get(v_a_2925_, 1);
lean_inc_ref_n(v_asyncEnv_2927_, 2);
lean_inc_ref(v___y_2917_);
lean_inc(v___y_2918_);
v___f_2928_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2928_, 0, v___y_2918_);
lean_closure_set(v___f_2928_, 1, v_a_2925_);
lean_closure_set(v___f_2928_, 2, v___y_2917_);
lean_inc(v_decl_2793_);
v___f_2929_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__2___boxed), 7, 3);
lean_closure_set(v___f_2929_, 0, v_asyncEnv_2927_);
lean_closure_set(v___f_2929_, 1, v_a_2925_);
lean_closure_set(v___f_2929_, 2, v_decl_2793_);
v___x_2930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2930_, 0, v_fst_2910_);
if (lean_obj_tag(v___y_2921_) == 0)
{
lean_inc_ref(v___x_2930_);
v___y_2832_ = v___y_2919_;
v___y_2833_ = v_mainEnv_2926_;
v___y_2834_ = v___y_2920_;
v___y_2835_ = v___y_2916_;
v___y_2836_ = v___x_2930_;
v___y_2837_ = v_a_2925_;
v___y_2838_ = v___f_2928_;
v___y_2839_ = v_asyncEnv_2927_;
v___y_2840_ = v___f_2929_;
v___y_2841_ = v___x_2930_;
goto v___jp_2831_;
}
else
{
v___y_2832_ = v___y_2919_;
v___y_2833_ = v_mainEnv_2926_;
v___y_2834_ = v___y_2920_;
v___y_2835_ = v___y_2916_;
v___y_2836_ = v___x_2930_;
v___y_2837_ = v_a_2925_;
v___y_2838_ = v___f_2928_;
v___y_2839_ = v_asyncEnv_2927_;
v___y_2840_ = v___f_2929_;
v___y_2841_ = v___y_2921_;
goto v___jp_2831_;
}
}
else
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2945_; 
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2916_);
lean_dec(v_fst_2910_);
lean_dec_ref(v___x_2794_);
lean_dec(v_decl_2793_);
v_a_2931_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2933_ = v___x_2924_;
v_isShared_2934_ = v_isSharedCheck_2945_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2924_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2945_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v_ref_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2940_; 
v_ref_2935_ = lean_ctor_get(v___y_2919_, 5);
v___x_2936_ = lean_io_error_to_string(v_a_2931_);
v___x_2937_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2936_);
v___x_2938_ = l_Lean_MessageData_ofFormat(v___x_2937_);
lean_inc(v_ref_2935_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 1, v___x_2938_);
lean_ctor_set(v___x_2913_, 0, v_ref_2935_);
v___x_2940_ = v___x_2913_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_ref_2935_);
lean_ctor_set(v_reuseFailAlloc_2944_, 1, v___x_2938_);
v___x_2940_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
lean_object* v___x_2942_; 
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 0, v___x_2940_);
v___x_2942_ = v___x_2933_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2940_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
}
v___jp_2946_:
{
lean_object* v___x_2950_; 
v___x_2950_ = lean_st_ref_get(v___y_2949_);
if (lean_obj_tag(v_exportedInfo_x3f_2947_) == 0)
{
lean_object* v_env_2951_; lean_object* v___x_2952_; 
v_env_2951_ = lean_ctor_get(v___x_2950_, 0);
lean_inc_ref(v_env_2951_);
lean_dec(v___x_2950_);
v___x_2952_ = lean_box(0);
v___y_2916_ = v_env_2951_;
v___y_2917_ = v___y_2948_;
v___y_2918_ = v___y_2949_;
v___y_2919_ = v___y_2948_;
v___y_2920_ = v___y_2949_;
v___y_2921_ = v_exportedInfo_x3f_2947_;
v___y_2922_ = v___x_2952_;
goto v___jp_2915_;
}
else
{
lean_object* v_env_2953_; lean_object* v_val_2954_; uint8_t v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
v_env_2953_ = lean_ctor_get(v___x_2950_, 0);
lean_inc_ref(v_env_2953_);
lean_dec(v___x_2950_);
v_val_2954_ = lean_ctor_get(v_exportedInfo_x3f_2947_, 0);
v___x_2955_ = l_Lean_ConstantKind_ofConstantInfo(v_val_2954_);
v___x_2956_ = lean_box(v___x_2955_);
v___x_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2956_);
v___y_2916_ = v_env_2953_;
v___y_2917_ = v___y_2948_;
v___y_2918_ = v___y_2949_;
v___y_2919_ = v___y_2948_;
v___y_2920_ = v___y_2949_;
v___y_2921_ = v_exportedInfo_x3f_2947_;
v___y_2922_ = v___x_2957_;
goto v___jp_2915_;
}
}
v___jp_2958_:
{
lean_object* v___x_2961_; 
lean_inc(v_fst_2910_);
v___x_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2961_, 0, v_fst_2910_);
v_exportedInfo_x3f_2947_ = v___x_2961_;
v___y_2948_ = v___y_2959_;
v___y_2949_ = v___y_2960_;
goto v___jp_2946_;
}
v___jp_2962_:
{
lean_object* v___x_2965_; 
lean_inc(v_fst_2910_);
v___x_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2965_, 0, v_fst_2910_);
v_exportedInfo_x3f_2947_ = v___x_2965_;
v___y_2948_ = v___y_2963_;
v___y_2949_ = v___y_2964_;
goto v___jp_2946_;
}
v___jp_2966_:
{
lean_object* v___x_2969_; lean_object* v_env_2970_; lean_object* v_nextMacroScope_2971_; lean_object* v_ngen_2972_; lean_object* v_auxDeclNGen_2973_; lean_object* v_traceState_2974_; lean_object* v_messages_2975_; lean_object* v_infoState_2976_; lean_object* v_snapshotTasks_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2987_; 
v___x_2969_ = lean_st_ref_take(v___y_2967_);
v_env_2970_ = lean_ctor_get(v___x_2969_, 0);
v_nextMacroScope_2971_ = lean_ctor_get(v___x_2969_, 1);
v_ngen_2972_ = lean_ctor_get(v___x_2969_, 2);
v_auxDeclNGen_2973_ = lean_ctor_get(v___x_2969_, 3);
v_traceState_2974_ = lean_ctor_get(v___x_2969_, 4);
v_messages_2975_ = lean_ctor_get(v___x_2969_, 6);
v_infoState_2976_ = lean_ctor_get(v___x_2969_, 7);
v_snapshotTasks_2977_ = lean_ctor_get(v___x_2969_, 8);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_2987_ == 0)
{
lean_object* v_unused_2988_; 
v_unused_2988_ = lean_ctor_get(v___x_2969_, 5);
lean_dec(v_unused_2988_);
v___x_2979_ = v___x_2969_;
v_isShared_2980_ = v_isSharedCheck_2987_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_snapshotTasks_2977_);
lean_inc(v_infoState_2976_);
lean_inc(v_messages_2975_);
lean_inc(v_traceState_2974_);
lean_inc(v_auxDeclNGen_2973_);
lean_inc(v_ngen_2972_);
lean_inc(v_nextMacroScope_2971_);
lean_inc(v_env_2970_);
lean_dec(v___x_2969_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2987_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2984_; 
v___x_2981_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_2911_);
lean_inc(v_fst_2906_);
v___x_2982_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2981_, v_env_2970_, v_fst_2906_, v_snd_2911_);
if (v_isShared_2980_ == 0)
{
lean_ctor_set(v___x_2979_, 5, v___x_2797_);
lean_ctor_set(v___x_2979_, 0, v___x_2982_);
v___x_2984_ = v___x_2979_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2982_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_nextMacroScope_2971_);
lean_ctor_set(v_reuseFailAlloc_2986_, 2, v_ngen_2972_);
lean_ctor_set(v_reuseFailAlloc_2986_, 3, v_auxDeclNGen_2973_);
lean_ctor_set(v_reuseFailAlloc_2986_, 4, v_traceState_2974_);
lean_ctor_set(v_reuseFailAlloc_2986_, 5, v___x_2797_);
lean_ctor_set(v_reuseFailAlloc_2986_, 6, v_messages_2975_);
lean_ctor_set(v_reuseFailAlloc_2986_, 7, v_infoState_2976_);
lean_ctor_set(v_reuseFailAlloc_2986_, 8, v_snapshotTasks_2977_);
v___x_2984_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
lean_object* v___x_2985_; 
v___x_2985_ = lean_st_ref_set(v___y_2967_, v___x_2984_);
v_exportedInfo_x3f_2947_ = v_exportedInfo_x3f_2801_;
v___y_2948_ = v___y_2968_;
v___y_2949_ = v___y_2967_;
goto v___jp_2946_;
}
}
}
v___jp_2989_:
{
lean_object* v___x_2992_; uint8_t v___x_2993_; 
lean_inc(v_decl_2793_);
v___x_2992_ = l_Lean_Declaration_getTopLevelNames(v_decl_2793_);
v___x_2993_ = l_List_all___at___00Lean_addDecl_spec__2(v___x_2992_);
lean_dec(v___x_2992_);
if (v___x_2993_ == 0)
{
lean_dec(v___x_2799_);
if (lean_obj_tag(v_exportedInfo_x3f_2801_) == 0)
{
if (v___x_2796_ == 0)
{
lean_object* v_options_2994_; uint8_t v_hasTrace_2995_; 
lean_dec_ref(v___x_2797_);
v_options_2994_ = lean_ctor_get(v___y_2990_, 2);
v_hasTrace_2995_ = lean_ctor_get_uint8(v_options_2994_, sizeof(void*)*1);
if (v_hasTrace_2995_ == 0)
{
lean_dec(v_cls_2798_);
v___y_2959_ = v___y_2990_;
v___y_2960_ = v___y_2991_;
goto v___jp_2958_;
}
else
{
lean_object* v_inheritedTraceOptions_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; uint8_t v___x_2999_; 
v_inheritedTraceOptions_2996_ = lean_ctor_get(v___y_2990_, 13);
v___x_2997_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v_cls_2798_);
v___x_2998_ = l_Lean_Name_append(v___x_2997_, v_cls_2798_);
v___x_2999_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2996_, v_options_2994_, v___x_2998_);
lean_dec(v___x_2998_);
if (v___x_2999_ == 0)
{
lean_dec(v_cls_2798_);
v___y_2959_ = v___y_2990_;
v___y_2960_ = v___y_2991_;
goto v___jp_2958_;
}
else
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_3000_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__1, &l_Lean_addDecl___lam__8___closed__1_once, _init_l_Lean_addDecl___lam__8___closed__1);
v___x_3001_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_2798_, v___x_3000_, v___y_2990_, v___y_2991_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_dec_ref(v___x_3001_);
v___y_2959_ = v___y_2990_;
v___y_2960_ = v___y_2991_;
goto v___jp_2958_;
}
else
{
lean_del_object(v___x_2913_);
lean_dec(v_snd_2911_);
lean_dec(v_fst_2910_);
lean_dec(v_fst_2906_);
lean_dec_ref(v___x_2794_);
lean_dec(v_decl_2793_);
return v___x_3001_;
}
}
}
}
else
{
lean_dec(v_cls_2798_);
v___y_2967_ = v___y_2991_;
v___y_2968_ = v___y_2990_;
goto v___jp_2966_;
}
}
else
{
lean_dec(v_cls_2798_);
v___y_2967_ = v___y_2991_;
v___y_2968_ = v___y_2990_;
goto v___jp_2966_;
}
}
else
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v_a_3004_; uint8_t v___x_3005_; 
lean_dec(v_exportedInfo_x3f_2801_);
lean_dec_ref(v___x_2797_);
v___x_3002_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3003_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__3___redArg(v___x_3002_, v___y_2990_);
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref(v___x_3003_);
v___x_3005_ = lean_unbox(v_a_3004_);
lean_dec(v_a_3004_);
if (v___x_3005_ == 0)
{
lean_object* v_options_3006_; uint8_t v_hasTrace_3007_; 
v_options_3006_ = lean_ctor_get(v___y_2990_, 2);
v_hasTrace_3007_ = lean_ctor_get_uint8(v_options_3006_, sizeof(void*)*1);
if (v_hasTrace_3007_ == 0)
{
lean_dec(v_cls_2798_);
v_exportedInfo_x3f_2947_ = v___x_2799_;
v___y_2948_ = v___y_2990_;
v___y_2949_ = v___y_2991_;
goto v___jp_2946_;
}
else
{
lean_object* v_inheritedTraceOptions_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; uint8_t v___x_3011_; 
v_inheritedTraceOptions_3008_ = lean_ctor_get(v___y_2990_, 13);
v___x_3009_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v_cls_2798_);
v___x_3010_ = l_Lean_Name_append(v___x_3009_, v_cls_2798_);
v___x_3011_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3008_, v_options_3006_, v___x_3010_);
lean_dec(v___x_3010_);
if (v___x_3011_ == 0)
{
lean_dec(v_cls_2798_);
v_exportedInfo_x3f_2947_ = v___x_2799_;
v___y_2948_ = v___y_2990_;
v___y_2949_ = v___y_2991_;
goto v___jp_2946_;
}
else
{
lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3012_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__3, &l_Lean_addDecl___lam__8___closed__3_once, _init_l_Lean_addDecl___lam__8___closed__3);
v___x_3013_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_2798_, v___x_3012_, v___y_2990_, v___y_2991_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_dec_ref(v___x_3013_);
v_exportedInfo_x3f_2947_ = v___x_2799_;
v___y_2948_ = v___y_2990_;
v___y_2949_ = v___y_2991_;
goto v___jp_2946_;
}
else
{
lean_del_object(v___x_2913_);
lean_dec(v_snd_2911_);
lean_dec(v_fst_2910_);
lean_dec(v_fst_2906_);
lean_dec(v___x_2799_);
lean_dec_ref(v___x_2794_);
lean_dec(v_decl_2793_);
return v___x_3013_;
}
}
}
}
else
{
lean_object* v_options_3014_; uint8_t v_hasTrace_3015_; 
lean_dec(v___x_2799_);
v_options_3014_ = lean_ctor_get(v___y_2990_, 2);
v_hasTrace_3015_ = lean_ctor_get_uint8(v_options_3014_, sizeof(void*)*1);
if (v_hasTrace_3015_ == 0)
{
lean_dec(v_cls_2798_);
v___y_2963_ = v___y_2990_;
v___y_2964_ = v___y_2991_;
goto v___jp_2962_;
}
else
{
lean_object* v_inheritedTraceOptions_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; uint8_t v___x_3019_; 
v_inheritedTraceOptions_3016_ = lean_ctor_get(v___y_2990_, 13);
v___x_3017_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v_cls_2798_);
v___x_3018_ = l_Lean_Name_append(v___x_3017_, v_cls_2798_);
v___x_3019_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3016_, v_options_3014_, v___x_3018_);
lean_dec(v___x_3018_);
if (v___x_3019_ == 0)
{
lean_dec(v_cls_2798_);
v___y_2963_ = v___y_2990_;
v___y_2964_ = v___y_2991_;
goto v___jp_2962_;
}
else
{
lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3020_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__5, &l_Lean_addDecl___lam__8___closed__5_once, _init_l_Lean_addDecl___lam__8___closed__5);
v___x_3021_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_2798_, v___x_3020_, v___y_2990_, v___y_2991_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_dec_ref(v___x_3021_);
v___y_2963_ = v___y_2990_;
v___y_2964_ = v___y_2991_;
goto v___jp_2962_;
}
else
{
lean_del_object(v___x_2913_);
lean_dec(v_snd_2911_);
lean_dec(v_fst_2910_);
lean_dec(v_fst_2906_);
lean_dec_ref(v___x_2794_);
lean_dec(v_decl_2793_);
return v___x_3021_;
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
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__8___boxed(lean_object* v_decl_3034_, lean_object* v___x_3035_, lean_object* v_hasTrace_3036_, lean_object* v___x_3037_, lean_object* v___x_3038_, lean_object* v_cls_3039_, lean_object* v___x_3040_, lean_object* v_____x_3041_, lean_object* v_exportedInfo_x3f_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
uint8_t v_hasTrace_boxed_3046_; uint8_t v___x_61844__boxed_3047_; lean_object* v_res_3048_; 
v_hasTrace_boxed_3046_ = lean_unbox(v_hasTrace_3036_);
v___x_61844__boxed_3047_ = lean_unbox(v___x_3037_);
v_res_3048_ = l_Lean_addDecl___lam__8(v_decl_3034_, v___x_3035_, v_hasTrace_boxed_3046_, v___x_61844__boxed_3047_, v___x_3038_, v_cls_3039_, v___x_3040_, v_____x_3041_, v_exportedInfo_x3f_3042_, v___y_3043_, v___y_3044_);
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
return v_res_3048_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__4___closed__1(void){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = ((lean_object*)(l_Lean_addDecl___lam__4___closed__0));
v___x_3051_ = l_Lean_stringToMessageData(v___x_3050_);
return v___x_3051_;
}
}
static lean_object* _init_l_Lean_addDecl___lam__4___closed__3(void){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3053_ = ((lean_object*)(l_Lean_addDecl___lam__4___closed__2));
v___x_3054_ = l_Lean_stringToMessageData(v___x_3053_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__4(lean_object* v___f_3055_, lean_object* v_cls_3056_, lean_object* v___x_3057_, uint8_t v___x_3058_, uint8_t v_forceExpose_3059_, lean_object* v_defn_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
lean_object* v_exportedInfo_x3f_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v_env_3103_; lean_object* v_env_3104_; 
v___x_3086_ = lean_st_ref_get(v___y_3062_);
v___x_3087_ = lean_st_ref_get(v___y_3062_);
v_env_3103_ = lean_ctor_get(v___x_3086_, 0);
lean_inc_ref(v_env_3103_);
lean_dec(v___x_3086_);
v_env_3104_ = lean_ctor_get(v___x_3087_, 0);
lean_inc_ref(v_env_3104_);
lean_dec(v___x_3087_);
if (v_forceExpose_3059_ == 0)
{
goto v___jp_3105_;
}
else
{
if (v___x_3058_ == 0)
{
lean_dec_ref(v_env_3104_);
lean_dec_ref(v_env_3103_);
lean_dec(v_cls_3056_);
v_exportedInfo_x3f_3065_ = v___x_3057_;
v___y_3066_ = v___y_3061_;
v___y_3067_ = v___y_3062_;
goto v___jp_3064_;
}
else
{
goto v___jp_3105_;
}
}
v___jp_3064_:
{
lean_object* v_toConstantVal_3068_; lean_object* v_name_3069_; lean_object* v___x_3070_; uint8_t v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v_toConstantVal_3068_ = lean_ctor_get(v_defn_3060_, 0);
v_name_3069_ = lean_ctor_get(v_toConstantVal_3068_, 0);
lean_inc(v_name_3069_);
v___x_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3070_, 0, v_defn_3060_);
v___x_3071_ = 0;
v___x_3072_ = lean_box(v___x_3071_);
v___x_3073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3070_);
lean_ctor_set(v___x_3073_, 1, v___x_3072_);
v___x_3074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3074_, 0, v_name_3069_);
lean_ctor_set(v___x_3074_, 1, v___x_3073_);
lean_inc(v___y_3067_);
lean_inc_ref(v___y_3066_);
v___x_3075_ = lean_apply_5(v___f_3055_, v___x_3074_, v_exportedInfo_x3f_3065_, v___y_3066_, v___y_3067_, lean_box(0));
return v___x_3075_;
}
v___jp_3076_:
{
lean_object* v_toConstantVal_3079_; uint8_t v_safety_3080_; uint8_t v___x_3081_; uint8_t v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v_toConstantVal_3079_ = lean_ctor_get(v_defn_3060_, 0);
v_safety_3080_ = lean_ctor_get_uint8(v_defn_3060_, sizeof(void*)*4);
v___x_3081_ = 0;
v___x_3082_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3080_, v___x_3081_);
lean_inc_ref(v_toConstantVal_3079_);
v___x_3083_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3083_, 0, v_toConstantVal_3079_);
lean_ctor_set_uint8(v___x_3083_, sizeof(void*)*1, v___x_3082_);
v___x_3084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3083_);
v___x_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
v_exportedInfo_x3f_3065_ = v___x_3085_;
v___y_3066_ = v___y_3077_;
v___y_3067_ = v___y_3078_;
goto v___jp_3064_;
}
v___jp_3088_:
{
lean_object* v_options_3089_; uint8_t v_hasTrace_3090_; 
v_options_3089_ = lean_ctor_get(v___y_3061_, 2);
v_hasTrace_3090_ = lean_ctor_get_uint8(v_options_3089_, sizeof(void*)*1);
if (v_hasTrace_3090_ == 0)
{
lean_dec(v_cls_3056_);
v___y_3077_ = v___y_3061_;
v___y_3078_ = v___y_3062_;
goto v___jp_3076_;
}
else
{
lean_object* v_inheritedTraceOptions_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; uint8_t v___x_3094_; 
v_inheritedTraceOptions_3091_ = lean_ctor_get(v___y_3061_, 13);
v___x_3092_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v_cls_3056_);
v___x_3093_ = l_Lean_Name_append(v___x_3092_, v_cls_3056_);
v___x_3094_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3091_, v_options_3089_, v___x_3093_);
lean_dec(v___x_3093_);
if (v___x_3094_ == 0)
{
lean_dec(v_cls_3056_);
v___y_3077_ = v___y_3061_;
v___y_3078_ = v___y_3062_;
goto v___jp_3076_;
}
else
{
lean_object* v_toConstantVal_3095_; lean_object* v_name_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v_toConstantVal_3095_ = lean_ctor_get(v_defn_3060_, 0);
v_name_3096_ = lean_ctor_get(v_toConstantVal_3095_, 0);
v___x_3097_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__1, &l_Lean_addDecl___lam__4___closed__1_once, _init_l_Lean_addDecl___lam__4___closed__1);
lean_inc(v_name_3096_);
v___x_3098_ = l_Lean_MessageData_ofName(v_name_3096_);
v___x_3099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3097_);
lean_ctor_set(v___x_3099_, 1, v___x_3098_);
v___x_3100_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_3101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3099_);
lean_ctor_set(v___x_3101_, 1, v___x_3100_);
v___x_3102_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3056_, v___x_3101_, v___y_3061_, v___y_3062_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_dec_ref(v___x_3102_);
v___y_3077_ = v___y_3061_;
v___y_3078_ = v___y_3062_;
goto v___jp_3076_;
}
else
{
lean_dec_ref(v_defn_3060_);
lean_dec_ref(v___f_3055_);
return v___x_3102_;
}
}
}
}
v___jp_3105_:
{
lean_object* v___x_3106_; uint8_t v_isModule_3107_; 
v___x_3106_ = l_Lean_Environment_header(v_env_3103_);
lean_dec_ref(v_env_3103_);
v_isModule_3107_ = lean_ctor_get_uint8(v___x_3106_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3106_);
if (v_isModule_3107_ == 0)
{
lean_dec_ref(v_env_3104_);
lean_dec(v_cls_3056_);
v_exportedInfo_x3f_3065_ = v___x_3057_;
v___y_3066_ = v___y_3061_;
v___y_3067_ = v___y_3062_;
goto v___jp_3064_;
}
else
{
uint8_t v_isExporting_3108_; 
v_isExporting_3108_ = lean_ctor_get_uint8(v_env_3104_, sizeof(void*)*8);
lean_dec_ref(v_env_3104_);
if (v_isExporting_3108_ == 0)
{
lean_dec(v___x_3057_);
goto v___jp_3088_;
}
else
{
if (v___x_3058_ == 0)
{
lean_dec(v_cls_3056_);
v_exportedInfo_x3f_3065_ = v___x_3057_;
v___y_3066_ = v___y_3061_;
v___y_3067_ = v___y_3062_;
goto v___jp_3064_;
}
else
{
lean_dec(v___x_3057_);
goto v___jp_3088_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__4___boxed(lean_object* v___f_3109_, lean_object* v_cls_3110_, lean_object* v___x_3111_, lean_object* v___x_3112_, lean_object* v_forceExpose_3113_, lean_object* v_defn_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
uint8_t v___x_62318__boxed_3118_; uint8_t v_forceExpose_boxed_3119_; lean_object* v_res_3120_; 
v___x_62318__boxed_3118_ = lean_unbox(v___x_3112_);
v_forceExpose_boxed_3119_ = lean_unbox(v_forceExpose_3113_);
v_res_3120_ = l_Lean_addDecl___lam__4(v___f_3109_, v_cls_3110_, v___x_3111_, v___x_62318__boxed_3118_, v_forceExpose_boxed_3119_, v_defn_3114_, v___y_3115_, v___y_3116_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__5(lean_object* v_val_3121_, lean_object* v___f_3122_, lean_object* v_____r_3123_, lean_object* v_exportedInfo_x3f_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_){
_start:
{
lean_object* v_toConstantVal_3128_; lean_object* v_name_3129_; lean_object* v___x_3130_; uint8_t v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v_toConstantVal_3128_ = lean_ctor_get(v_val_3121_, 0);
v_name_3129_ = lean_ctor_get(v_toConstantVal_3128_, 0);
lean_inc(v_name_3129_);
v___x_3130_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3130_, 0, v_val_3121_);
v___x_3131_ = 1;
v___x_3132_ = lean_box(v___x_3131_);
v___x_3133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3130_);
lean_ctor_set(v___x_3133_, 1, v___x_3132_);
v___x_3134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3134_, 0, v_name_3129_);
lean_ctor_set(v___x_3134_, 1, v___x_3133_);
lean_inc(v___y_3126_);
lean_inc_ref(v___y_3125_);
v___x_3135_ = lean_apply_5(v___f_3122_, v___x_3134_, v_exportedInfo_x3f_3124_, v___y_3125_, v___y_3126_, lean_box(0));
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__5___boxed(lean_object* v_val_3136_, lean_object* v___f_3137_, lean_object* v_____r_3138_, lean_object* v_exportedInfo_x3f_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l_Lean_addDecl___lam__5(v_val_3136_, v___f_3137_, v_____r_3138_, v_exportedInfo_x3f_3139_, v___y_3140_, v___y_3141_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__6(lean_object* v_val_3144_, uint8_t v___x_3145_, lean_object* v___f_3146_, lean_object* v_____r_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v_toConstantVal_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v_toConstantVal_3151_ = lean_ctor_get(v_val_3144_, 0);
lean_inc_ref(v_toConstantVal_3151_);
v___x_3152_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3152_, 0, v_toConstantVal_3151_);
lean_ctor_set_uint8(v___x_3152_, sizeof(void*)*1, v___x_3145_);
v___x_3153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3152_);
v___x_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3153_);
v___x_3155_ = lean_box(0);
lean_inc(v___y_3149_);
lean_inc_ref(v___y_3148_);
v___x_3156_ = lean_apply_5(v___f_3146_, v___x_3155_, v___x_3154_, v___y_3148_, v___y_3149_, lean_box(0));
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__6___boxed(lean_object* v_val_3157_, lean_object* v___x_3158_, lean_object* v___f_3159_, lean_object* v_____r_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
uint8_t v___x_62437__boxed_3164_; lean_object* v_res_3165_; 
v___x_62437__boxed_3164_ = lean_unbox(v___x_3158_);
v_res_3165_ = l_Lean_addDecl___lam__6(v_val_3157_, v___x_62437__boxed_3164_, v___f_3159_, v_____r_3160_, v___y_3161_, v___y_3162_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec_ref(v_val_3157_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__7(lean_object* v_val_3166_, lean_object* v___f_3167_, lean_object* v_____r_3168_, lean_object* v_exportedInfo_x3f_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v_toConstantVal_3173_; lean_object* v_name_3174_; lean_object* v___x_3175_; uint8_t v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v_toConstantVal_3173_ = lean_ctor_get(v_val_3166_, 0);
v_name_3174_ = lean_ctor_get(v_toConstantVal_3173_, 0);
lean_inc(v_name_3174_);
v___x_3175_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3175_, 0, v_val_3166_);
v___x_3176_ = 3;
v___x_3177_ = lean_box(v___x_3176_);
v___x_3178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3175_);
lean_ctor_set(v___x_3178_, 1, v___x_3177_);
v___x_3179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3179_, 0, v_name_3174_);
lean_ctor_set(v___x_3179_, 1, v___x_3178_);
lean_inc(v___y_3171_);
lean_inc_ref(v___y_3170_);
v___x_3180_ = lean_apply_5(v___f_3167_, v___x_3179_, v_exportedInfo_x3f_3169_, v___y_3170_, v___y_3171_, lean_box(0));
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__7___boxed(lean_object* v_val_3181_, lean_object* v___f_3182_, lean_object* v_____r_3183_, lean_object* v_exportedInfo_x3f_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l_Lean_addDecl___lam__7(v_val_3181_, v___f_3182_, v_____r_3183_, v_exportedInfo_x3f_3184_, v___y_3185_, v___y_3186_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__9(lean_object* v_val_3189_, lean_object* v___f_3190_, lean_object* v_____r_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
lean_object* v_toConstantVal_3195_; uint8_t v_isUnsafe_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; 
v_toConstantVal_3195_ = lean_ctor_get(v_val_3189_, 0);
v_isUnsafe_3196_ = lean_ctor_get_uint8(v_val_3189_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_3195_);
v___x_3197_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3197_, 0, v_toConstantVal_3195_);
lean_ctor_set_uint8(v___x_3197_, sizeof(void*)*1, v_isUnsafe_3196_);
v___x_3198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3197_);
v___x_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3199_, 0, v___x_3198_);
v___x_3200_ = lean_box(0);
lean_inc(v___y_3193_);
lean_inc_ref(v___y_3192_);
v___x_3201_ = lean_apply_5(v___f_3190_, v___x_3200_, v___x_3199_, v___y_3192_, v___y_3193_, lean_box(0));
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__9___boxed(lean_object* v_val_3202_, lean_object* v___f_3203_, lean_object* v_____r_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
lean_object* v_res_3208_; 
v_res_3208_ = l_Lean_addDecl___lam__9(v_val_3202_, v___f_3203_, v_____r_3204_, v___y_3205_, v___y_3206_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec_ref(v_val_3202_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__13(lean_object* v_decl_3209_, lean_object* v___x_3210_, uint8_t v___x_3211_, lean_object* v_cls_3212_, lean_object* v___x_3213_, lean_object* v___x_3214_, lean_object* v_____x_3215_, lean_object* v_exportedInfo_x3f_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v_a_3223_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v_a_3236_; uint8_t v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v_snd_3321_; lean_object* v_fst_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3451_; 
v_snd_3321_ = lean_ctor_get(v_____x_3215_, 1);
v_fst_3322_ = lean_ctor_get(v_____x_3215_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v_____x_3215_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3324_ = v_____x_3215_;
v_isShared_3325_ = v_isSharedCheck_3451_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_snd_3321_);
lean_inc(v_fst_3322_);
lean_dec(v_____x_3215_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3451_;
goto v_resetjp_3323_;
}
v___jp_3220_:
{
lean_object* v___x_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3231_; 
v___x_3224_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3221_, v___y_3222_);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3231_ == 0)
{
lean_object* v_unused_3232_; 
v_unused_3232_ = lean_ctor_get(v___x_3224_, 0);
lean_dec(v_unused_3232_);
v___x_3226_ = v___x_3224_;
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
else
{
lean_dec(v___x_3224_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
if (v_isShared_3227_ == 0)
{
lean_ctor_set_tag(v___x_3226_, 1);
lean_ctor_set(v___x_3226_, 0, v_a_3223_);
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3223_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
v___jp_3233_:
{
lean_object* v___x_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3244_; 
v___x_3237_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3234_, v___y_3235_);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3237_);
if (v_isSharedCheck_3244_ == 0)
{
lean_object* v_unused_3245_; 
v_unused_3245_ = lean_ctor_get(v___x_3237_, 0);
lean_dec(v_unused_3245_);
v___x_3239_ = v___x_3237_;
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
else
{
lean_dec(v___x_3237_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3242_; 
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 0, v_a_3236_);
v___x_3242_ = v___x_3239_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_a_3236_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
v___jp_3246_:
{
lean_object* v___x_3258_; 
lean_inc_ref(v___y_3250_);
v___x_3258_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3251_, v___y_3250_, v___y_3254_, v___y_3257_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v___x_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3306_; 
lean_dec_ref(v___x_3258_);
lean_inc_ref(v___y_3248_);
v___x_3259_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3248_, v___y_3252_);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3306_ == 0)
{
lean_object* v_unused_3307_; 
v_unused_3307_ = lean_ctor_get(v___x_3259_, 0);
lean_dec(v_unused_3307_);
v___x_3261_ = v___x_3259_;
v_isShared_3262_ = v_isSharedCheck_3306_;
goto v_resetjp_3260_;
}
else
{
lean_dec(v___x_3259_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3306_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v_options_3263_; lean_object* v___x_3264_; uint8_t v___x_3265_; 
v_options_3263_ = lean_ctor_get(v___y_3256_, 2);
v___x_3264_ = l_Lean_Elab_async;
v___x_3265_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3263_, v___x_3264_);
if (v___x_3265_ == 0)
{
lean_object* v___x_3266_; lean_object* v_r_3267_; 
lean_del_object(v___x_3261_);
lean_dec_ref(v___y_3253_);
lean_dec_ref(v___y_3249_);
lean_dec_ref(v___x_3210_);
v___x_3266_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3250_, v___y_3252_);
lean_dec_ref(v___x_3266_);
v_r_3267_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3209_, v___y_3256_, v___y_3252_);
if (lean_obj_tag(v_r_3267_) == 0)
{
lean_object* v_a_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3277_; 
v_a_3268_ = lean_ctor_get(v_r_3267_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v_r_3267_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3270_ = v_r_3267_;
v_isShared_3271_ = v_isSharedCheck_3277_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_a_3268_);
lean_dec(v_r_3267_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3277_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3273_; 
lean_inc(v_a_3268_);
if (v_isShared_3271_ == 0)
{
lean_ctor_set_tag(v___x_3270_, 1);
v___x_3273_ = v___x_3270_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3268_);
v___x_3273_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
lean_object* v___x_3274_; 
v___x_3274_ = lean_apply_2(v___y_3255_, v___x_3273_, lean_box(0));
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_dec_ref(v___x_3274_);
v___y_3234_ = v___y_3248_;
v___y_3235_ = v___y_3252_;
v_a_3236_ = v_a_3268_;
goto v___jp_3233_;
}
else
{
lean_object* v_a_3275_; 
lean_dec(v_a_3268_);
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref(v___x_3274_);
v___y_3221_ = v___y_3248_;
v___y_3222_ = v___y_3252_;
v_a_3223_ = v_a_3275_;
goto v___jp_3220_;
}
}
}
}
else
{
lean_object* v_a_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v_a_3278_ = lean_ctor_get(v_r_3267_, 0);
lean_inc(v_a_3278_);
lean_dec_ref(v_r_3267_);
v___x_3279_ = lean_box(0);
v___x_3280_ = lean_apply_2(v___y_3255_, v___x_3279_, lean_box(0));
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_dec_ref(v___x_3280_);
v___y_3221_ = v___y_3248_;
v___y_3222_ = v___y_3252_;
v_a_3223_ = v_a_3278_;
goto v___jp_3220_;
}
else
{
lean_object* v_a_3281_; 
lean_dec(v_a_3278_);
v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
lean_inc(v_a_3281_);
lean_dec_ref(v___x_3280_);
v___y_3221_ = v___y_3248_;
v___y_3222_ = v___y_3252_;
v_a_3223_ = v_a_3281_;
goto v___jp_3220_;
}
}
}
else
{
lean_object* v___x_3282_; lean_object* v___x_3284_; 
lean_dec_ref(v___y_3255_);
lean_dec_ref(v___y_3250_);
lean_dec_ref(v___y_3248_);
lean_dec(v_decl_3209_);
v___x_3282_ = l_IO_CancelToken_new();
if (v_isShared_3262_ == 0)
{
lean_ctor_set_tag(v___x_3261_, 1);
lean_ctor_set(v___x_3261_, 0, v___x_3282_);
v___x_3284_ = v___x_3261_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3282_);
v___x_3284_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; 
v___x_3285_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__5_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_3286_ = l_Lean_Name_mkStr2(v___x_3285_, v___x_3210_);
v___x_3287_ = l_Lean_Name_toString(v___x_3286_, v___x_3211_);
lean_inc_ref(v___x_3284_);
v___x_3288_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3249_, v___x_3284_, v___x_3287_, v___y_3256_, v___y_3252_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v_a_3289_; lean_object* v_checked_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
lean_inc(v_a_3289_);
lean_dec_ref(v___x_3288_);
v_checked_3290_ = lean_ctor_get(v___y_3253_, 2);
lean_inc_ref(v_checked_3290_);
lean_dec_ref(v___y_3253_);
v___x_3291_ = lean_unsigned_to_nat(0u);
v___x_3292_ = lean_io_map_task(v_a_3289_, v_checked_3290_, v___x_3291_, v___y_3247_);
v___x_3293_ = lean_box(0);
v___x_3294_ = lean_box(2);
v___x_3295_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3293_);
lean_ctor_set(v___x_3295_, 1, v___x_3294_);
lean_ctor_set(v___x_3295_, 2, v___x_3284_);
lean_ctor_set(v___x_3295_, 3, v___x_3292_);
v___x_3296_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3295_, v___y_3252_);
return v___x_3296_;
}
else
{
lean_object* v_a_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3304_; 
lean_dec_ref(v___x_3284_);
lean_dec_ref(v___y_3253_);
v_a_3297_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3299_ = v___x_3288_;
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_a_3297_);
lean_dec(v___x_3288_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v___x_3302_; 
if (v_isShared_3300_ == 0)
{
v___x_3302_ = v___x_3299_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3297_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3320_; 
lean_dec_ref(v___y_3255_);
lean_dec_ref(v___y_3253_);
lean_dec_ref(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec_ref(v___x_3210_);
lean_dec(v_decl_3209_);
v_a_3308_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3310_ = v___x_3258_;
v_isShared_3311_ = v_isSharedCheck_3320_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3258_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3320_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v_ref_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3318_; 
v_ref_3312_ = lean_ctor_get(v___y_3256_, 5);
v___x_3313_ = lean_io_error_to_string(v_a_3308_);
v___x_3314_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3313_);
v___x_3315_ = l_Lean_MessageData_ofFormat(v___x_3314_);
lean_inc(v_ref_3312_);
v___x_3316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3316_, 0, v_ref_3312_);
lean_ctor_set(v___x_3316_, 1, v___x_3315_);
if (v_isShared_3311_ == 0)
{
lean_ctor_set(v___x_3310_, 0, v___x_3316_);
v___x_3318_ = v___x_3310_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v___x_3316_);
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
v_resetjp_3323_:
{
lean_object* v_fst_3326_; lean_object* v_snd_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3450_; 
v_fst_3326_ = lean_ctor_get(v_snd_3321_, 0);
v_snd_3327_ = lean_ctor_get(v_snd_3321_, 1);
v_isSharedCheck_3450_ = !lean_is_exclusive(v_snd_3321_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3329_ = v_snd_3321_;
v_isShared_3330_ = v_isSharedCheck_3450_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_snd_3327_);
lean_inc(v_fst_3326_);
lean_dec(v_snd_3321_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3450_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v_exportedInfo_x3f_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3384_; lean_object* v___y_3385_; uint8_t v___y_3386_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___x_3440_; lean_object* v_env_3441_; uint8_t v___x_3442_; 
v___x_3440_ = lean_st_ref_get(v___y_3218_);
v_env_3441_ = lean_ctor_get(v___x_3440_, 0);
lean_inc_ref(v_env_3441_);
lean_dec(v___x_3440_);
v___x_3442_ = l_Lean_Environment_containsOnBranch(v_env_3441_, v_fst_3322_);
lean_dec_ref(v_env_3441_);
if (v___x_3442_ == 0)
{
lean_del_object(v___x_3324_);
v___y_3416_ = v___y_3217_;
v___y_3417_ = v___y_3218_;
goto v___jp_3415_;
}
else
{
lean_object* v___x_3443_; lean_object* v_env_3444_; lean_object* v___x_3445_; lean_object* v___x_3447_; 
lean_del_object(v___x_3329_);
lean_dec(v_snd_3327_);
lean_dec(v_fst_3326_);
lean_dec(v_exportedInfo_x3f_3216_);
lean_dec(v___x_3214_);
lean_dec_ref(v___x_3213_);
lean_dec(v_cls_3212_);
lean_dec_ref(v___x_3210_);
lean_dec(v_decl_3209_);
v___x_3443_ = lean_st_ref_get(v___y_3218_);
v_env_3444_ = lean_ctor_get(v___x_3443_, 0);
lean_inc_ref(v_env_3444_);
lean_dec(v___x_3443_);
v___x_3445_ = lean_elab_environment_to_kernel_env(v_env_3444_);
if (v_isShared_3325_ == 0)
{
lean_ctor_set_tag(v___x_3324_, 1);
lean_ctor_set(v___x_3324_, 1, v_fst_3322_);
lean_ctor_set(v___x_3324_, 0, v___x_3445_);
v___x_3447_ = v___x_3324_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3445_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v_fst_3322_);
v___x_3447_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
lean_object* v___x_3448_; 
v___x_3448_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(v___x_3447_, v___y_3217_, v___y_3218_);
return v___x_3448_;
}
}
v___jp_3331_:
{
uint8_t v___x_3339_; uint8_t v___x_3340_; lean_object* v___x_3341_; 
v___x_3339_ = 0;
v___x_3340_ = lean_unbox(v_snd_3327_);
lean_dec(v_snd_3327_);
lean_inc_ref(v___y_3334_);
v___x_3341_ = l_Lean_Environment_addConstAsync(v___y_3334_, v_fst_3322_, v___x_3340_, v___y_3338_, v___x_3339_, v___x_3211_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; lean_object* v_mainEnv_3343_; lean_object* v_asyncEnv_3344_; lean_object* v___f_3345_; lean_object* v___f_3346_; lean_object* v___x_3347_; 
lean_del_object(v___x_3329_);
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
lean_inc_n(v_a_3342_, 3);
lean_dec_ref(v___x_3341_);
v_mainEnv_3343_ = lean_ctor_get(v_a_3342_, 0);
lean_inc_ref(v_mainEnv_3343_);
v_asyncEnv_3344_ = lean_ctor_get(v_a_3342_, 1);
lean_inc_ref_n(v_asyncEnv_3344_, 2);
lean_inc_ref(v___y_3333_);
lean_inc(v___y_3332_);
v___f_3345_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3345_, 0, v___y_3332_);
lean_closure_set(v___f_3345_, 1, v_a_3342_);
lean_closure_set(v___f_3345_, 2, v___y_3333_);
lean_inc(v_decl_3209_);
v___f_3346_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3346_, 0, v_asyncEnv_3344_);
lean_closure_set(v___f_3346_, 1, v_a_3342_);
lean_closure_set(v___f_3346_, 2, v_decl_3209_);
v___x_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3347_, 0, v_fst_3326_);
if (lean_obj_tag(v___y_3335_) == 0)
{
lean_inc_ref(v___x_3347_);
v___y_3247_ = v___x_3339_;
v___y_3248_ = v_mainEnv_3343_;
v___y_3249_ = v___f_3346_;
v___y_3250_ = v_asyncEnv_3344_;
v___y_3251_ = v_a_3342_;
v___y_3252_ = v___y_3336_;
v___y_3253_ = v___y_3334_;
v___y_3254_ = v___x_3347_;
v___y_3255_ = v___f_3345_;
v___y_3256_ = v___y_3337_;
v___y_3257_ = v___x_3347_;
goto v___jp_3246_;
}
else
{
v___y_3247_ = v___x_3339_;
v___y_3248_ = v_mainEnv_3343_;
v___y_3249_ = v___f_3346_;
v___y_3250_ = v_asyncEnv_3344_;
v___y_3251_ = v_a_3342_;
v___y_3252_ = v___y_3336_;
v___y_3253_ = v___y_3334_;
v___y_3254_ = v___x_3347_;
v___y_3255_ = v___f_3345_;
v___y_3256_ = v___y_3337_;
v___y_3257_ = v___y_3335_;
goto v___jp_3246_;
}
}
else
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3362_; 
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v_fst_3326_);
lean_dec_ref(v___x_3210_);
lean_dec(v_decl_3209_);
v_a_3348_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3350_ = v___x_3341_;
v_isShared_3351_ = v_isSharedCheck_3362_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3341_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3362_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v_ref_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3357_; 
v_ref_3352_ = lean_ctor_get(v___y_3337_, 5);
v___x_3353_ = lean_io_error_to_string(v_a_3348_);
v___x_3354_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3353_);
v___x_3355_ = l_Lean_MessageData_ofFormat(v___x_3354_);
lean_inc(v_ref_3352_);
if (v_isShared_3330_ == 0)
{
lean_ctor_set(v___x_3329_, 1, v___x_3355_);
lean_ctor_set(v___x_3329_, 0, v_ref_3352_);
v___x_3357_ = v___x_3329_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_ref_3352_);
lean_ctor_set(v_reuseFailAlloc_3361_, 1, v___x_3355_);
v___x_3357_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
lean_object* v___x_3359_; 
if (v_isShared_3351_ == 0)
{
lean_ctor_set(v___x_3350_, 0, v___x_3357_);
v___x_3359_ = v___x_3350_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3357_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
}
}
v___jp_3363_:
{
lean_object* v___x_3367_; 
v___x_3367_ = lean_st_ref_get(v___y_3366_);
if (lean_obj_tag(v_exportedInfo_x3f_3364_) == 0)
{
lean_object* v_env_3368_; lean_object* v___x_3369_; 
v_env_3368_ = lean_ctor_get(v___x_3367_, 0);
lean_inc_ref(v_env_3368_);
lean_dec(v___x_3367_);
v___x_3369_ = lean_box(0);
v___y_3332_ = v___y_3366_;
v___y_3333_ = v___y_3365_;
v___y_3334_ = v_env_3368_;
v___y_3335_ = v_exportedInfo_x3f_3364_;
v___y_3336_ = v___y_3366_;
v___y_3337_ = v___y_3365_;
v___y_3338_ = v___x_3369_;
goto v___jp_3331_;
}
else
{
lean_object* v_env_3370_; lean_object* v_val_3371_; uint8_t v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v_env_3370_ = lean_ctor_get(v___x_3367_, 0);
lean_inc_ref(v_env_3370_);
lean_dec(v___x_3367_);
v_val_3371_ = lean_ctor_get(v_exportedInfo_x3f_3364_, 0);
v___x_3372_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3371_);
v___x_3373_ = lean_box(v___x_3372_);
v___x_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3373_);
v___y_3332_ = v___y_3366_;
v___y_3333_ = v___y_3365_;
v___y_3334_ = v_env_3370_;
v___y_3335_ = v_exportedInfo_x3f_3364_;
v___y_3336_ = v___y_3366_;
v___y_3337_ = v___y_3365_;
v___y_3338_ = v___x_3374_;
goto v___jp_3331_;
}
}
v___jp_3375_:
{
lean_object* v___x_3378_; 
lean_inc(v_fst_3326_);
v___x_3378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3378_, 0, v_fst_3326_);
v_exportedInfo_x3f_3364_ = v___x_3378_;
v___y_3365_ = v___y_3376_;
v___y_3366_ = v___y_3377_;
goto v___jp_3363_;
}
v___jp_3379_:
{
lean_object* v___x_3382_; 
lean_inc(v_fst_3326_);
v___x_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3382_, 0, v_fst_3326_);
v_exportedInfo_x3f_3364_ = v___x_3382_;
v___y_3365_ = v___y_3380_;
v___y_3366_ = v___y_3381_;
goto v___jp_3363_;
}
v___jp_3383_:
{
if (v___y_3386_ == 0)
{
lean_object* v_options_3387_; uint8_t v_hasTrace_3388_; 
lean_dec(v_exportedInfo_x3f_3216_);
lean_dec_ref(v___x_3213_);
v_options_3387_ = lean_ctor_get(v___y_3385_, 2);
v_hasTrace_3388_ = lean_ctor_get_uint8(v_options_3387_, sizeof(void*)*1);
if (v_hasTrace_3388_ == 0)
{
lean_dec(v_cls_3212_);
v___y_3376_ = v___y_3385_;
v___y_3377_ = v___y_3384_;
goto v___jp_3375_;
}
else
{
lean_object* v_inheritedTraceOptions_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; uint8_t v___x_3392_; 
v_inheritedTraceOptions_3389_ = lean_ctor_get(v___y_3385_, 13);
v___x_3390_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v_cls_3212_);
v___x_3391_ = l_Lean_Name_append(v___x_3390_, v_cls_3212_);
v___x_3392_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3389_, v_options_3387_, v___x_3391_);
lean_dec(v___x_3391_);
if (v___x_3392_ == 0)
{
lean_dec(v_cls_3212_);
v___y_3376_ = v___y_3385_;
v___y_3377_ = v___y_3384_;
goto v___jp_3375_;
}
else
{
lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3393_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__1, &l_Lean_addDecl___lam__8___closed__1_once, _init_l_Lean_addDecl___lam__8___closed__1);
v___x_3394_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3212_, v___x_3393_, v___y_3385_, v___y_3384_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_dec_ref(v___x_3394_);
v___y_3376_ = v___y_3385_;
v___y_3377_ = v___y_3384_;
goto v___jp_3375_;
}
else
{
lean_del_object(v___x_3329_);
lean_dec(v_snd_3327_);
lean_dec(v_fst_3326_);
lean_dec(v_fst_3322_);
lean_dec_ref(v___x_3210_);
lean_dec(v_decl_3209_);
return v___x_3394_;
}
}
}
}
else
{
lean_object* v___x_3395_; lean_object* v_env_3396_; lean_object* v_nextMacroScope_3397_; lean_object* v_ngen_3398_; lean_object* v_auxDeclNGen_3399_; lean_object* v_traceState_3400_; lean_object* v_messages_3401_; lean_object* v_infoState_3402_; lean_object* v_snapshotTasks_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3413_; 
lean_dec(v_cls_3212_);
v___x_3395_ = lean_st_ref_take(v___y_3384_);
v_env_3396_ = lean_ctor_get(v___x_3395_, 0);
v_nextMacroScope_3397_ = lean_ctor_get(v___x_3395_, 1);
v_ngen_3398_ = lean_ctor_get(v___x_3395_, 2);
v_auxDeclNGen_3399_ = lean_ctor_get(v___x_3395_, 3);
v_traceState_3400_ = lean_ctor_get(v___x_3395_, 4);
v_messages_3401_ = lean_ctor_get(v___x_3395_, 6);
v_infoState_3402_ = lean_ctor_get(v___x_3395_, 7);
v_snapshotTasks_3403_ = lean_ctor_get(v___x_3395_, 8);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3413_ == 0)
{
lean_object* v_unused_3414_; 
v_unused_3414_ = lean_ctor_get(v___x_3395_, 5);
lean_dec(v_unused_3414_);
v___x_3405_ = v___x_3395_;
v_isShared_3406_ = v_isSharedCheck_3413_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_snapshotTasks_3403_);
lean_inc(v_infoState_3402_);
lean_inc(v_messages_3401_);
lean_inc(v_traceState_3400_);
lean_inc(v_auxDeclNGen_3399_);
lean_inc(v_ngen_3398_);
lean_inc(v_nextMacroScope_3397_);
lean_inc(v_env_3396_);
lean_dec(v___x_3395_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3413_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3410_; 
v___x_3407_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3327_);
lean_inc(v_fst_3322_);
v___x_3408_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3407_, v_env_3396_, v_fst_3322_, v_snd_3327_);
if (v_isShared_3406_ == 0)
{
lean_ctor_set(v___x_3405_, 5, v___x_3213_);
lean_ctor_set(v___x_3405_, 0, v___x_3408_);
v___x_3410_ = v___x_3405_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v___x_3408_);
lean_ctor_set(v_reuseFailAlloc_3412_, 1, v_nextMacroScope_3397_);
lean_ctor_set(v_reuseFailAlloc_3412_, 2, v_ngen_3398_);
lean_ctor_set(v_reuseFailAlloc_3412_, 3, v_auxDeclNGen_3399_);
lean_ctor_set(v_reuseFailAlloc_3412_, 4, v_traceState_3400_);
lean_ctor_set(v_reuseFailAlloc_3412_, 5, v___x_3213_);
lean_ctor_set(v_reuseFailAlloc_3412_, 6, v_messages_3401_);
lean_ctor_set(v_reuseFailAlloc_3412_, 7, v_infoState_3402_);
lean_ctor_set(v_reuseFailAlloc_3412_, 8, v_snapshotTasks_3403_);
v___x_3410_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
lean_object* v___x_3411_; 
v___x_3411_ = lean_st_ref_set(v___y_3384_, v___x_3410_);
v_exportedInfo_x3f_3364_ = v_exportedInfo_x3f_3216_;
v___y_3365_ = v___y_3385_;
v___y_3366_ = v___y_3384_;
goto v___jp_3363_;
}
}
}
}
v___jp_3415_:
{
lean_object* v___x_3418_; uint8_t v___x_3419_; 
lean_inc(v_decl_3209_);
v___x_3418_ = l_Lean_Declaration_getTopLevelNames(v_decl_3209_);
v___x_3419_ = l_List_all___at___00Lean_addDecl_spec__2(v___x_3418_);
lean_dec(v___x_3418_);
if (v___x_3419_ == 0)
{
lean_dec(v___x_3214_);
if (lean_obj_tag(v_exportedInfo_x3f_3216_) == 0)
{
v___y_3384_ = v___y_3417_;
v___y_3385_ = v___y_3416_;
v___y_3386_ = v___x_3419_;
goto v___jp_3383_;
}
else
{
v___y_3384_ = v___y_3417_;
v___y_3385_ = v___y_3416_;
v___y_3386_ = v___x_3211_;
goto v___jp_3383_;
}
}
else
{
lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v_a_3422_; uint8_t v___x_3423_; 
lean_dec(v_exportedInfo_x3f_3216_);
lean_dec_ref(v___x_3213_);
v___x_3420_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3421_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__3___redArg(v___x_3420_, v___y_3416_);
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
lean_inc(v_a_3422_);
lean_dec_ref(v___x_3421_);
v___x_3423_ = lean_unbox(v_a_3422_);
lean_dec(v_a_3422_);
if (v___x_3423_ == 0)
{
lean_object* v_options_3424_; uint8_t v_hasTrace_3425_; 
v_options_3424_ = lean_ctor_get(v___y_3416_, 2);
v_hasTrace_3425_ = lean_ctor_get_uint8(v_options_3424_, sizeof(void*)*1);
if (v_hasTrace_3425_ == 0)
{
lean_dec(v_cls_3212_);
v_exportedInfo_x3f_3364_ = v___x_3214_;
v___y_3365_ = v___y_3416_;
v___y_3366_ = v___y_3417_;
goto v___jp_3363_;
}
else
{
lean_object* v_inheritedTraceOptions_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; uint8_t v___x_3429_; 
v_inheritedTraceOptions_3426_ = lean_ctor_get(v___y_3416_, 13);
v___x_3427_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v_cls_3212_);
v___x_3428_ = l_Lean_Name_append(v___x_3427_, v_cls_3212_);
v___x_3429_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3426_, v_options_3424_, v___x_3428_);
lean_dec(v___x_3428_);
if (v___x_3429_ == 0)
{
lean_dec(v_cls_3212_);
v_exportedInfo_x3f_3364_ = v___x_3214_;
v___y_3365_ = v___y_3416_;
v___y_3366_ = v___y_3417_;
goto v___jp_3363_;
}
else
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3430_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__3, &l_Lean_addDecl___lam__8___closed__3_once, _init_l_Lean_addDecl___lam__8___closed__3);
v___x_3431_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3212_, v___x_3430_, v___y_3416_, v___y_3417_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_dec_ref(v___x_3431_);
v_exportedInfo_x3f_3364_ = v___x_3214_;
v___y_3365_ = v___y_3416_;
v___y_3366_ = v___y_3417_;
goto v___jp_3363_;
}
else
{
lean_del_object(v___x_3329_);
lean_dec(v_snd_3327_);
lean_dec(v_fst_3326_);
lean_dec(v_fst_3322_);
lean_dec(v___x_3214_);
lean_dec_ref(v___x_3210_);
lean_dec(v_decl_3209_);
return v___x_3431_;
}
}
}
}
else
{
lean_object* v_options_3432_; uint8_t v_hasTrace_3433_; 
lean_dec(v___x_3214_);
v_options_3432_ = lean_ctor_get(v___y_3416_, 2);
v_hasTrace_3433_ = lean_ctor_get_uint8(v_options_3432_, sizeof(void*)*1);
if (v_hasTrace_3433_ == 0)
{
lean_dec(v_cls_3212_);
v___y_3380_ = v___y_3416_;
v___y_3381_ = v___y_3417_;
goto v___jp_3379_;
}
else
{
lean_object* v_inheritedTraceOptions_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; uint8_t v___x_3437_; 
v_inheritedTraceOptions_3434_ = lean_ctor_get(v___y_3416_, 13);
v___x_3435_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v_cls_3212_);
v___x_3436_ = l_Lean_Name_append(v___x_3435_, v_cls_3212_);
v___x_3437_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3434_, v_options_3432_, v___x_3436_);
lean_dec(v___x_3436_);
if (v___x_3437_ == 0)
{
lean_dec(v_cls_3212_);
v___y_3380_ = v___y_3416_;
v___y_3381_ = v___y_3417_;
goto v___jp_3379_;
}
else
{
lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3438_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__5, &l_Lean_addDecl___lam__8___closed__5_once, _init_l_Lean_addDecl___lam__8___closed__5);
v___x_3439_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3212_, v___x_3438_, v___y_3416_, v___y_3417_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_dec_ref(v___x_3439_);
v___y_3380_ = v___y_3416_;
v___y_3381_ = v___y_3417_;
goto v___jp_3379_;
}
else
{
lean_del_object(v___x_3329_);
lean_dec(v_snd_3327_);
lean_dec(v_fst_3326_);
lean_dec(v_fst_3322_);
lean_dec_ref(v___x_3210_);
lean_dec(v_decl_3209_);
return v___x_3439_;
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
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__13___boxed(lean_object* v_decl_3452_, lean_object* v___x_3453_, lean_object* v___x_3454_, lean_object* v_cls_3455_, lean_object* v___x_3456_, lean_object* v___x_3457_, lean_object* v_____x_3458_, lean_object* v_exportedInfo_x3f_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_){
_start:
{
uint8_t v___x_62548__boxed_3463_; lean_object* v_res_3464_; 
v___x_62548__boxed_3463_ = lean_unbox(v___x_3454_);
v_res_3464_ = l_Lean_addDecl___lam__13(v_decl_3452_, v___x_3453_, v___x_62548__boxed_3463_, v_cls_3455_, v___x_3456_, v___x_3457_, v_____x_3458_, v_exportedInfo_x3f_3459_, v___y_3460_, v___y_3461_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__10(lean_object* v___f_3465_, uint8_t v_forceExpose_3466_, uint8_t v___x_3467_, lean_object* v___x_3468_, lean_object* v_cls_3469_, lean_object* v_defn_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_){
_start:
{
lean_object* v_exportedInfo_x3f_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3496_ = lean_st_ref_get(v___y_3472_);
v___x_3497_ = lean_st_ref_get(v___y_3472_);
if (v_forceExpose_3466_ == 0)
{
if (v___x_3467_ == 0)
{
lean_dec(v___x_3497_);
lean_dec(v___x_3496_);
lean_dec(v_cls_3469_);
v_exportedInfo_x3f_3475_ = v___x_3468_;
v___y_3476_ = v___y_3471_;
v___y_3477_ = v___y_3472_;
goto v___jp_3474_;
}
else
{
lean_object* v_env_3498_; lean_object* v_env_3499_; lean_object* v___x_3500_; uint8_t v_isModule_3501_; 
v_env_3498_ = lean_ctor_get(v___x_3496_, 0);
lean_inc_ref(v_env_3498_);
lean_dec(v___x_3496_);
v_env_3499_ = lean_ctor_get(v___x_3497_, 0);
lean_inc_ref(v_env_3499_);
lean_dec(v___x_3497_);
v___x_3500_ = l_Lean_Environment_header(v_env_3498_);
lean_dec_ref(v_env_3498_);
v_isModule_3501_ = lean_ctor_get_uint8(v___x_3500_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3500_);
if (v_isModule_3501_ == 0)
{
lean_dec_ref(v_env_3499_);
lean_dec(v_cls_3469_);
v_exportedInfo_x3f_3475_ = v___x_3468_;
v___y_3476_ = v___y_3471_;
v___y_3477_ = v___y_3472_;
goto v___jp_3474_;
}
else
{
uint8_t v_isExporting_3502_; 
v_isExporting_3502_ = lean_ctor_get_uint8(v_env_3499_, sizeof(void*)*8);
lean_dec_ref(v_env_3499_);
if (v_isExporting_3502_ == 0)
{
lean_object* v_options_3503_; uint8_t v_hasTrace_3504_; 
lean_dec(v___x_3468_);
v_options_3503_ = lean_ctor_get(v___y_3471_, 2);
v_hasTrace_3504_ = lean_ctor_get_uint8(v_options_3503_, sizeof(void*)*1);
if (v_hasTrace_3504_ == 0)
{
lean_dec(v_cls_3469_);
v___y_3487_ = v___y_3471_;
v___y_3488_ = v___y_3472_;
goto v___jp_3486_;
}
else
{
lean_object* v_inheritedTraceOptions_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; uint8_t v___x_3508_; 
v_inheritedTraceOptions_3505_ = lean_ctor_get(v___y_3471_, 13);
v___x_3506_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
lean_inc(v_cls_3469_);
v___x_3507_ = l_Lean_Name_append(v___x_3506_, v_cls_3469_);
v___x_3508_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3505_, v_options_3503_, v___x_3507_);
lean_dec(v___x_3507_);
if (v___x_3508_ == 0)
{
lean_dec(v_cls_3469_);
v___y_3487_ = v___y_3471_;
v___y_3488_ = v___y_3472_;
goto v___jp_3486_;
}
else
{
lean_object* v_toConstantVal_3509_; lean_object* v_name_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
v_toConstantVal_3509_ = lean_ctor_get(v_defn_3470_, 0);
v_name_3510_ = lean_ctor_get(v_toConstantVal_3509_, 0);
v___x_3511_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__1, &l_Lean_addDecl___lam__4___closed__1_once, _init_l_Lean_addDecl___lam__4___closed__1);
lean_inc(v_name_3510_);
v___x_3512_ = l_Lean_MessageData_ofName(v_name_3510_);
v___x_3513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3513_, 0, v___x_3511_);
lean_ctor_set(v___x_3513_, 1, v___x_3512_);
v___x_3514_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_3515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3515_, 0, v___x_3513_);
lean_ctor_set(v___x_3515_, 1, v___x_3514_);
v___x_3516_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3469_, v___x_3515_, v___y_3471_, v___y_3472_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_dec_ref(v___x_3516_);
v___y_3487_ = v___y_3471_;
v___y_3488_ = v___y_3472_;
goto v___jp_3486_;
}
else
{
lean_dec_ref(v_defn_3470_);
lean_dec_ref(v___f_3465_);
return v___x_3516_;
}
}
}
}
else
{
lean_dec(v_cls_3469_);
v_exportedInfo_x3f_3475_ = v___x_3468_;
v___y_3476_ = v___y_3471_;
v___y_3477_ = v___y_3472_;
goto v___jp_3474_;
}
}
}
}
else
{
lean_dec(v___x_3497_);
lean_dec(v___x_3496_);
lean_dec(v_cls_3469_);
v_exportedInfo_x3f_3475_ = v___x_3468_;
v___y_3476_ = v___y_3471_;
v___y_3477_ = v___y_3472_;
goto v___jp_3474_;
}
v___jp_3474_:
{
lean_object* v_toConstantVal_3478_; lean_object* v_name_3479_; lean_object* v___x_3480_; uint8_t v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v_toConstantVal_3478_ = lean_ctor_get(v_defn_3470_, 0);
v_name_3479_ = lean_ctor_get(v_toConstantVal_3478_, 0);
lean_inc(v_name_3479_);
v___x_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3480_, 0, v_defn_3470_);
v___x_3481_ = 0;
v___x_3482_ = lean_box(v___x_3481_);
v___x_3483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3480_);
lean_ctor_set(v___x_3483_, 1, v___x_3482_);
v___x_3484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3484_, 0, v_name_3479_);
lean_ctor_set(v___x_3484_, 1, v___x_3483_);
lean_inc(v___y_3477_);
lean_inc_ref(v___y_3476_);
v___x_3485_ = lean_apply_5(v___f_3465_, v___x_3484_, v_exportedInfo_x3f_3475_, v___y_3476_, v___y_3477_, lean_box(0));
return v___x_3485_;
}
v___jp_3486_:
{
lean_object* v_toConstantVal_3489_; uint8_t v_safety_3490_; uint8_t v___x_3491_; uint8_t v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v_toConstantVal_3489_ = lean_ctor_get(v_defn_3470_, 0);
v_safety_3490_ = lean_ctor_get_uint8(v_defn_3470_, sizeof(void*)*4);
v___x_3491_ = 0;
v___x_3492_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3490_, v___x_3491_);
lean_inc_ref(v_toConstantVal_3489_);
v___x_3493_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3493_, 0, v_toConstantVal_3489_);
lean_ctor_set_uint8(v___x_3493_, sizeof(void*)*1, v___x_3492_);
v___x_3494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3493_);
v___x_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3494_);
v_exportedInfo_x3f_3475_ = v___x_3495_;
v___y_3476_ = v___y_3487_;
v___y_3477_ = v___y_3488_;
goto v___jp_3474_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__10___boxed(lean_object* v___f_3517_, lean_object* v_forceExpose_3518_, lean_object* v___x_3519_, lean_object* v___x_3520_, lean_object* v_cls_3521_, lean_object* v_defn_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_){
_start:
{
uint8_t v_forceExpose_boxed_3526_; uint8_t v___x_63017__boxed_3527_; lean_object* v_res_3528_; 
v_forceExpose_boxed_3526_ = lean_unbox(v_forceExpose_3518_);
v___x_63017__boxed_3527_ = lean_unbox(v___x_3519_);
v_res_3528_ = l_Lean_addDecl___lam__10(v___f_3517_, v_forceExpose_boxed_3526_, v___x_63017__boxed_3527_, v___x_3520_, v_cls_3521_, v_defn_3522_, v___y_3523_, v___y_3524_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
return v_res_3528_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__12(lean_object* v_val_3529_, uint8_t v_forceExpose_3530_, lean_object* v___f_3531_, lean_object* v_____r_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
lean_object* v_toConstantVal_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v_toConstantVal_3536_ = lean_ctor_get(v_val_3529_, 0);
lean_inc_ref(v_toConstantVal_3536_);
v___x_3537_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3537_, 0, v_toConstantVal_3536_);
lean_ctor_set_uint8(v___x_3537_, sizeof(void*)*1, v_forceExpose_3530_);
v___x_3538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3537_);
v___x_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3538_);
v___x_3540_ = lean_box(0);
lean_inc(v___y_3534_);
lean_inc_ref(v___y_3533_);
v___x_3541_ = lean_apply_5(v___f_3531_, v___x_3540_, v___x_3539_, v___y_3533_, v___y_3534_, lean_box(0));
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__12___boxed(lean_object* v_val_3542_, lean_object* v_forceExpose_3543_, lean_object* v___f_3544_, lean_object* v_____r_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
uint8_t v_forceExpose_boxed_3549_; lean_object* v_res_3550_; 
v_forceExpose_boxed_3549_ = lean_unbox(v_forceExpose_3543_);
v_res_3550_ = l_Lean_addDecl___lam__12(v_val_3542_, v_forceExpose_boxed_3549_, v___f_3544_, v_____r_3545_, v___y_3546_, v___y_3547_);
lean_dec(v___y_3547_);
lean_dec_ref(v___y_3546_);
lean_dec_ref(v_val_3542_);
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_addDecl_spec__1(lean_object* v_x_3551_, lean_object* v_x_3552_){
_start:
{
if (lean_obj_tag(v_x_3552_) == 0)
{
return v_x_3551_;
}
else
{
lean_object* v_head_3553_; lean_object* v_tail_3554_; lean_object* v___x_3555_; 
v_head_3553_ = lean_ctor_get(v_x_3552_, 0);
lean_inc(v_head_3553_);
v_tail_3554_ = lean_ctor_get(v_x_3552_, 1);
lean_inc(v_tail_3554_);
lean_dec_ref(v_x_3552_);
v___x_3555_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(v_x_3551_, v_head_3553_);
v_x_3551_ = v___x_3555_;
v_x_3552_ = v_tail_3554_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_addDecl___closed__1(void){
_start:
{
lean_object* v_cls_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v_cls_3560_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_3561_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__0));
v___x_3562_ = l_Lean_Name_append(v___x_3561_, v_cls_3560_);
return v___x_3562_;
}
}
static lean_object* _init_l_Lean_addDecl___closed__3(void){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3564_ = ((lean_object*)(l_Lean_addDecl___closed__2));
v___x_3565_ = l_Lean_stringToMessageData(v___x_3564_);
return v___x_3565_;
}
}
static lean_object* _init_l_Lean_addDecl___closed__5(void){
_start:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3567_ = ((lean_object*)(l_Lean_addDecl___closed__4));
v___x_3568_ = l_Lean_stringToMessageData(v___x_3567_);
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object* v_decl_3569_, uint8_t v_forceExpose_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_){
_start:
{
lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v_a_3577_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v_a_3590_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v_a_3603_; lean_object* v___y_3614_; lean_object* v___y_3615_; lean_object* v_a_3616_; lean_object* v_options_3626_; lean_object* v_inheritedTraceOptions_3627_; uint8_t v_hasTrace_3628_; lean_object* v___x_3629_; lean_object* v___y_3631_; uint8_t v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; uint8_t v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; uint8_t v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v_exportedInfo_x3f_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; uint8_t v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; uint8_t v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v_cls_3765_; 
v_options_3626_ = lean_ctor_get(v_a_3571_, 2);
v_inheritedTraceOptions_3627_ = lean_ctor_get(v_a_3571_, 13);
v_hasTrace_3628_ = lean_ctor_get_uint8(v_options_3626_, sizeof(void*)*1);
v___x_3629_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__0_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v_cls_3765_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
if (v_hasTrace_3628_ == 0)
{
lean_object* v___x_3766_; lean_object* v_env_3767_; lean_object* v_nextMacroScope_3768_; lean_object* v_ngen_3769_; lean_object* v_auxDeclNGen_3770_; lean_object* v_traceState_3771_; lean_object* v_messages_3772_; lean_object* v_infoState_3773_; lean_object* v_snapshotTasks_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3963_; 
v___x_3766_ = lean_st_ref_take(v_a_3572_);
v_env_3767_ = lean_ctor_get(v___x_3766_, 0);
v_nextMacroScope_3768_ = lean_ctor_get(v___x_3766_, 1);
v_ngen_3769_ = lean_ctor_get(v___x_3766_, 2);
v_auxDeclNGen_3770_ = lean_ctor_get(v___x_3766_, 3);
v_traceState_3771_ = lean_ctor_get(v___x_3766_, 4);
v_messages_3772_ = lean_ctor_get(v___x_3766_, 6);
v_infoState_3773_ = lean_ctor_get(v___x_3766_, 7);
v_snapshotTasks_3774_ = lean_ctor_get(v___x_3766_, 8);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3963_ == 0)
{
lean_object* v_unused_3964_; 
v_unused_3964_ = lean_ctor_get(v___x_3766_, 5);
lean_dec(v_unused_3964_);
v___x_3776_ = v___x_3766_;
v_isShared_3777_ = v_isSharedCheck_3963_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_snapshotTasks_3774_);
lean_inc(v_infoState_3773_);
lean_inc(v_messages_3772_);
lean_inc(v_traceState_3771_);
lean_inc(v_auxDeclNGen_3770_);
lean_inc(v_ngen_3769_);
lean_inc(v_nextMacroScope_3768_);
lean_inc(v_env_3767_);
lean_dec(v___x_3766_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3963_;
goto v_resetjp_3775_;
}
v_resetjp_3775_:
{
lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3782_; 
lean_inc(v_decl_3569_);
v___x_3778_ = l_Lean_Declaration_getNames(v_decl_3569_);
v___x_3779_ = l_List_foldl___at___00Lean_addDecl_spec__1(v_env_3767_, v___x_3778_);
v___x_3780_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2);
if (v_isShared_3777_ == 0)
{
lean_ctor_set(v___x_3776_, 5, v___x_3780_);
lean_ctor_set(v___x_3776_, 0, v___x_3779_);
v___x_3782_ = v___x_3776_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v___x_3779_);
lean_ctor_set(v_reuseFailAlloc_3962_, 1, v_nextMacroScope_3768_);
lean_ctor_set(v_reuseFailAlloc_3962_, 2, v_ngen_3769_);
lean_ctor_set(v_reuseFailAlloc_3962_, 3, v_auxDeclNGen_3770_);
lean_ctor_set(v_reuseFailAlloc_3962_, 4, v_traceState_3771_);
lean_ctor_set(v_reuseFailAlloc_3962_, 5, v___x_3780_);
lean_ctor_set(v_reuseFailAlloc_3962_, 6, v_messages_3772_);
lean_ctor_set(v_reuseFailAlloc_3962_, 7, v_infoState_3773_);
lean_ctor_set(v_reuseFailAlloc_3962_, 8, v_snapshotTasks_3774_);
v___x_3782_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___y_3786_; uint8_t v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v_fst_3841_; lean_object* v_fst_3842_; uint8_t v_snd_3843_; lean_object* v_exportedInfo_x3f_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3856_; lean_object* v_toConstantVal_3857_; lean_object* v_exportedInfo_x3f_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3865_; lean_object* v_exportedInfo_x3f_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3871_; lean_object* v_toConstantVal_3872_; uint8_t v_safety_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v_defn_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; 
v___x_3783_ = lean_st_ref_set(v_a_3572_, v___x_3782_);
v___x_3784_ = lean_box(0);
switch(lean_obj_tag(v_decl_3569_))
{
case 2:
{
lean_object* v_val_3912_; lean_object* v_exportedInfo_x3f_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___x_3921_; 
v_val_3912_ = lean_ctor_get(v_decl_3569_, 0);
v___x_3921_ = lean_st_ref_get(v_a_3572_);
if (v_forceExpose_3570_ == 0)
{
lean_object* v_env_3922_; lean_object* v___x_3923_; uint8_t v_isModule_3924_; 
v_env_3922_ = lean_ctor_get(v___x_3921_, 0);
lean_inc_ref(v_env_3922_);
lean_dec(v___x_3921_);
v___x_3923_ = l_Lean_Environment_header(v_env_3922_);
lean_dec_ref(v_env_3922_);
v_isModule_3924_ = lean_ctor_get_uint8(v___x_3923_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3923_);
if (v_isModule_3924_ == 0)
{
v_exportedInfo_x3f_3914_ = v___x_3784_;
v___y_3915_ = v_a_3571_;
v___y_3916_ = v_a_3572_;
goto v___jp_3913_;
}
else
{
lean_object* v_toConstantVal_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v_toConstantVal_3925_ = lean_ctor_get(v_val_3912_, 0);
lean_inc_ref(v_toConstantVal_3925_);
v___x_3926_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3926_, 0, v_toConstantVal_3925_);
lean_ctor_set_uint8(v___x_3926_, sizeof(void*)*1, v_hasTrace_3628_);
v___x_3927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3926_);
v___x_3928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3927_);
v_exportedInfo_x3f_3914_ = v___x_3928_;
v___y_3915_ = v_a_3571_;
v___y_3916_ = v_a_3572_;
goto v___jp_3913_;
}
}
else
{
lean_dec(v___x_3921_);
v_exportedInfo_x3f_3914_ = v___x_3784_;
v___y_3915_ = v_a_3571_;
v___y_3916_ = v_a_3572_;
goto v___jp_3913_;
}
v___jp_3913_:
{
lean_object* v_toConstantVal_3917_; lean_object* v_name_3918_; lean_object* v___x_3919_; uint8_t v___x_3920_; 
v_toConstantVal_3917_ = lean_ctor_get(v_val_3912_, 0);
v_name_3918_ = lean_ctor_get(v_toConstantVal_3917_, 0);
lean_inc_ref(v_val_3912_);
v___x_3919_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3919_, 0, v_val_3912_);
v___x_3920_ = 1;
lean_inc(v_name_3918_);
v_fst_3841_ = v_name_3918_;
v_fst_3842_ = v___x_3919_;
v_snd_3843_ = v___x_3920_;
v_exportedInfo_x3f_3844_ = v_exportedInfo_x3f_3914_;
v___y_3845_ = v___y_3915_;
v___y_3846_ = v___y_3916_;
goto v___jp_3840_;
}
}
case 1:
{
lean_object* v_val_3929_; 
v_val_3929_ = lean_ctor_get(v_decl_3569_, 0);
lean_inc_ref(v_val_3929_);
v_defn_3888_ = v_val_3929_;
v___y_3889_ = v_a_3571_;
v___y_3890_ = v_a_3572_;
goto v___jp_3887_;
}
case 5:
{
lean_object* v_defns_3930_; 
v_defns_3930_ = lean_ctor_get(v_decl_3569_, 0);
if (lean_obj_tag(v_defns_3930_) == 1)
{
lean_object* v_tail_3931_; 
v_tail_3931_ = lean_ctor_get(v_defns_3930_, 1);
if (lean_obj_tag(v_tail_3931_) == 0)
{
lean_object* v_head_3932_; 
v_head_3932_ = lean_ctor_get(v_defns_3930_, 0);
lean_inc(v_head_3932_);
v_defn_3888_ = v_head_3932_;
v___y_3889_ = v_a_3571_;
v___y_3890_ = v_a_3572_;
goto v___jp_3887_;
}
else
{
lean_object* v___x_3933_; 
v___x_3933_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3569_, v_a_3571_, v_a_3572_);
return v___x_3933_;
}
}
else
{
lean_object* v___x_3934_; 
v___x_3934_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3569_, v_a_3571_, v_a_3572_);
return v___x_3934_;
}
}
case 3:
{
lean_object* v_val_3935_; lean_object* v_exportedInfo_x3f_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v___x_3944_; lean_object* v___x_3945_; 
v_val_3935_ = lean_ctor_get(v_decl_3569_, 0);
v___x_3944_ = lean_st_ref_get(v_a_3572_);
v___x_3945_ = lean_st_ref_get(v_a_3572_);
if (v_forceExpose_3570_ == 0)
{
lean_object* v_env_3946_; lean_object* v_env_3947_; lean_object* v___x_3948_; uint8_t v_isModule_3949_; 
v_env_3946_ = lean_ctor_get(v___x_3944_, 0);
lean_inc_ref(v_env_3946_);
lean_dec(v___x_3944_);
v_env_3947_ = lean_ctor_get(v___x_3945_, 0);
lean_inc_ref(v_env_3947_);
lean_dec(v___x_3945_);
v___x_3948_ = l_Lean_Environment_header(v_env_3946_);
lean_dec_ref(v_env_3946_);
v_isModule_3949_ = lean_ctor_get_uint8(v___x_3948_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3948_);
if (v_isModule_3949_ == 0)
{
lean_dec_ref(v_env_3947_);
v_exportedInfo_x3f_3937_ = v___x_3784_;
v___y_3938_ = v_a_3571_;
v___y_3939_ = v_a_3572_;
goto v___jp_3936_;
}
else
{
uint8_t v_isExporting_3950_; 
v_isExporting_3950_ = lean_ctor_get_uint8(v_env_3947_, sizeof(void*)*8);
lean_dec_ref(v_env_3947_);
if (v_isExporting_3950_ == 0)
{
lean_object* v_toConstantVal_3951_; uint8_t v_isUnsafe_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v_toConstantVal_3951_ = lean_ctor_get(v_val_3935_, 0);
v_isUnsafe_3952_ = lean_ctor_get_uint8(v_val_3935_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_3951_);
v___x_3953_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3953_, 0, v_toConstantVal_3951_);
lean_ctor_set_uint8(v___x_3953_, sizeof(void*)*1, v_isUnsafe_3952_);
v___x_3954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3953_);
v___x_3955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3954_);
v_exportedInfo_x3f_3937_ = v___x_3955_;
v___y_3938_ = v_a_3571_;
v___y_3939_ = v_a_3572_;
goto v___jp_3936_;
}
else
{
v_exportedInfo_x3f_3937_ = v___x_3784_;
v___y_3938_ = v_a_3571_;
v___y_3939_ = v_a_3572_;
goto v___jp_3936_;
}
}
}
else
{
lean_dec(v___x_3945_);
lean_dec(v___x_3944_);
v_exportedInfo_x3f_3937_ = v___x_3784_;
v___y_3938_ = v_a_3571_;
v___y_3939_ = v_a_3572_;
goto v___jp_3936_;
}
v___jp_3936_:
{
lean_object* v_toConstantVal_3940_; lean_object* v_name_3941_; lean_object* v___x_3942_; uint8_t v___x_3943_; 
v_toConstantVal_3940_ = lean_ctor_get(v_val_3935_, 0);
v_name_3941_ = lean_ctor_get(v_toConstantVal_3940_, 0);
lean_inc_ref(v_val_3935_);
v___x_3942_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3942_, 0, v_val_3935_);
v___x_3943_ = 3;
lean_inc(v_name_3941_);
v_fst_3841_ = v_name_3941_;
v_fst_3842_ = v___x_3942_;
v_snd_3843_ = v___x_3943_;
v_exportedInfo_x3f_3844_ = v_exportedInfo_x3f_3937_;
v___y_3845_ = v___y_3938_;
v___y_3846_ = v___y_3939_;
goto v___jp_3840_;
}
}
case 0:
{
lean_object* v_val_3956_; lean_object* v_toConstantVal_3957_; lean_object* v_name_3958_; lean_object* v___x_3959_; uint8_t v___x_3960_; 
v_val_3956_ = lean_ctor_get(v_decl_3569_, 0);
v_toConstantVal_3957_ = lean_ctor_get(v_val_3956_, 0);
v_name_3958_ = lean_ctor_get(v_toConstantVal_3957_, 0);
lean_inc_ref(v_val_3956_);
v___x_3959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3959_, 0, v_val_3956_);
v___x_3960_ = 2;
lean_inc(v_name_3958_);
v_fst_3841_ = v_name_3958_;
v_fst_3842_ = v___x_3959_;
v_snd_3843_ = v___x_3960_;
v_exportedInfo_x3f_3844_ = v___x_3784_;
v___y_3845_ = v_a_3571_;
v___y_3846_ = v_a_3572_;
goto v___jp_3840_;
}
default: 
{
lean_object* v___x_3961_; 
v___x_3961_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3569_, v_a_3571_, v_a_3572_);
return v___x_3961_;
}
}
v___jp_3785_:
{
lean_object* v___x_3792_; uint8_t v___x_3793_; 
lean_inc(v_decl_3569_);
v___x_3792_ = l_Lean_Declaration_getTopLevelNames(v_decl_3569_);
v___x_3793_ = l_List_all___at___00Lean_addDecl_spec__2(v___x_3792_);
lean_dec(v___x_3792_);
if (v___x_3793_ == 0)
{
if (lean_obj_tag(v___y_3786_) == 0)
{
lean_object* v_options_3794_; uint8_t v_hasTrace_3795_; 
v_options_3794_ = lean_ctor_get(v___y_3790_, 2);
v_hasTrace_3795_ = lean_ctor_get_uint8(v_options_3794_, sizeof(void*)*1);
if (v_hasTrace_3795_ == 0)
{
v___y_3759_ = v___y_3787_;
v___y_3760_ = v___y_3788_;
v___y_3761_ = v___y_3789_;
v___y_3762_ = v___y_3790_;
v___y_3763_ = v___y_3791_;
goto v___jp_3758_;
}
else
{
lean_object* v_inheritedTraceOptions_3796_; lean_object* v___x_3797_; uint8_t v___x_3798_; 
v_inheritedTraceOptions_3796_ = lean_ctor_get(v___y_3790_, 13);
v___x_3797_ = lean_obj_once(&l_Lean_addDecl___closed__1, &l_Lean_addDecl___closed__1_once, _init_l_Lean_addDecl___closed__1);
v___x_3798_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3796_, v_options_3794_, v___x_3797_);
if (v___x_3798_ == 0)
{
v___y_3759_ = v___y_3787_;
v___y_3760_ = v___y_3788_;
v___y_3761_ = v___y_3789_;
v___y_3762_ = v___y_3790_;
v___y_3763_ = v___y_3791_;
goto v___jp_3758_;
}
else
{
lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3799_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__1, &l_Lean_addDecl___lam__8___closed__1_once, _init_l_Lean_addDecl___lam__8___closed__1);
v___x_3800_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3765_, v___x_3799_, v___y_3790_, v___y_3791_);
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_dec_ref(v___x_3800_);
v___y_3759_ = v___y_3787_;
v___y_3760_ = v___y_3788_;
v___y_3761_ = v___y_3789_;
v___y_3762_ = v___y_3790_;
v___y_3763_ = v___y_3791_;
goto v___jp_3758_;
}
else
{
lean_dec_ref(v___y_3789_);
lean_dec(v___y_3788_);
lean_dec(v_decl_3569_);
return v___x_3800_;
}
}
}
}
else
{
lean_object* v___x_3801_; lean_object* v_env_3802_; lean_object* v_nextMacroScope_3803_; lean_object* v_ngen_3804_; lean_object* v_auxDeclNGen_3805_; lean_object* v_traceState_3806_; lean_object* v_messages_3807_; lean_object* v_infoState_3808_; lean_object* v_snapshotTasks_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3820_; 
v___x_3801_ = lean_st_ref_take(v___y_3791_);
v_env_3802_ = lean_ctor_get(v___x_3801_, 0);
v_nextMacroScope_3803_ = lean_ctor_get(v___x_3801_, 1);
v_ngen_3804_ = lean_ctor_get(v___x_3801_, 2);
v_auxDeclNGen_3805_ = lean_ctor_get(v___x_3801_, 3);
v_traceState_3806_ = lean_ctor_get(v___x_3801_, 4);
v_messages_3807_ = lean_ctor_get(v___x_3801_, 6);
v_infoState_3808_ = lean_ctor_get(v___x_3801_, 7);
v_snapshotTasks_3809_ = lean_ctor_get(v___x_3801_, 8);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3820_ == 0)
{
lean_object* v_unused_3821_; 
v_unused_3821_ = lean_ctor_get(v___x_3801_, 5);
lean_dec(v_unused_3821_);
v___x_3811_ = v___x_3801_;
v_isShared_3812_ = v_isSharedCheck_3820_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_snapshotTasks_3809_);
lean_inc(v_infoState_3808_);
lean_inc(v_messages_3807_);
lean_inc(v_traceState_3806_);
lean_inc(v_auxDeclNGen_3805_);
lean_inc(v_ngen_3804_);
lean_inc(v_nextMacroScope_3803_);
lean_inc(v_env_3802_);
lean_dec(v___x_3801_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3820_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3817_; 
v___x_3813_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_3814_ = lean_box(v___y_3787_);
lean_inc(v___y_3788_);
v___x_3815_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3813_, v_env_3802_, v___y_3788_, v___x_3814_);
if (v_isShared_3812_ == 0)
{
lean_ctor_set(v___x_3811_, 5, v___x_3780_);
lean_ctor_set(v___x_3811_, 0, v___x_3815_);
v___x_3817_ = v___x_3811_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v___x_3815_);
lean_ctor_set(v_reuseFailAlloc_3819_, 1, v_nextMacroScope_3803_);
lean_ctor_set(v_reuseFailAlloc_3819_, 2, v_ngen_3804_);
lean_ctor_set(v_reuseFailAlloc_3819_, 3, v_auxDeclNGen_3805_);
lean_ctor_set(v_reuseFailAlloc_3819_, 4, v_traceState_3806_);
lean_ctor_set(v_reuseFailAlloc_3819_, 5, v___x_3780_);
lean_ctor_set(v_reuseFailAlloc_3819_, 6, v_messages_3807_);
lean_ctor_set(v_reuseFailAlloc_3819_, 7, v_infoState_3808_);
lean_ctor_set(v_reuseFailAlloc_3819_, 8, v_snapshotTasks_3809_);
v___x_3817_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
lean_object* v___x_3818_; 
v___x_3818_ = lean_st_ref_set(v___y_3791_, v___x_3817_);
v___y_3737_ = v___y_3787_;
v___y_3738_ = v___y_3788_;
v___y_3739_ = v___y_3789_;
v_exportedInfo_x3f_3740_ = v___y_3786_;
v___y_3741_ = v___y_3790_;
v___y_3742_ = v___y_3791_;
goto v___jp_3736_;
}
}
}
}
else
{
lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v_a_3824_; uint8_t v___x_3825_; 
lean_dec(v___y_3786_);
v___x_3822_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3823_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__3___redArg(v___x_3822_, v___y_3790_);
v_a_3824_ = lean_ctor_get(v___x_3823_, 0);
lean_inc(v_a_3824_);
lean_dec_ref(v___x_3823_);
v___x_3825_ = lean_unbox(v_a_3824_);
lean_dec(v_a_3824_);
if (v___x_3825_ == 0)
{
lean_object* v_options_3826_; uint8_t v_hasTrace_3827_; 
v_options_3826_ = lean_ctor_get(v___y_3790_, 2);
v_hasTrace_3827_ = lean_ctor_get_uint8(v_options_3826_, sizeof(void*)*1);
if (v_hasTrace_3827_ == 0)
{
v___y_3737_ = v___y_3787_;
v___y_3738_ = v___y_3788_;
v___y_3739_ = v___y_3789_;
v_exportedInfo_x3f_3740_ = v___x_3784_;
v___y_3741_ = v___y_3790_;
v___y_3742_ = v___y_3791_;
goto v___jp_3736_;
}
else
{
lean_object* v_inheritedTraceOptions_3828_; lean_object* v___x_3829_; uint8_t v___x_3830_; 
v_inheritedTraceOptions_3828_ = lean_ctor_get(v___y_3790_, 13);
v___x_3829_ = lean_obj_once(&l_Lean_addDecl___closed__1, &l_Lean_addDecl___closed__1_once, _init_l_Lean_addDecl___closed__1);
v___x_3830_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3828_, v_options_3826_, v___x_3829_);
if (v___x_3830_ == 0)
{
v___y_3737_ = v___y_3787_;
v___y_3738_ = v___y_3788_;
v___y_3739_ = v___y_3789_;
v_exportedInfo_x3f_3740_ = v___x_3784_;
v___y_3741_ = v___y_3790_;
v___y_3742_ = v___y_3791_;
goto v___jp_3736_;
}
else
{
lean_object* v___x_3831_; lean_object* v___x_3832_; 
v___x_3831_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__3, &l_Lean_addDecl___lam__8___closed__3_once, _init_l_Lean_addDecl___lam__8___closed__3);
v___x_3832_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3765_, v___x_3831_, v___y_3790_, v___y_3791_);
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_dec_ref(v___x_3832_);
v___y_3737_ = v___y_3787_;
v___y_3738_ = v___y_3788_;
v___y_3739_ = v___y_3789_;
v_exportedInfo_x3f_3740_ = v___x_3784_;
v___y_3741_ = v___y_3790_;
v___y_3742_ = v___y_3791_;
goto v___jp_3736_;
}
else
{
lean_dec_ref(v___y_3789_);
lean_dec(v___y_3788_);
lean_dec(v_decl_3569_);
return v___x_3832_;
}
}
}
}
else
{
lean_object* v_options_3833_; uint8_t v_hasTrace_3834_; 
v_options_3833_ = lean_ctor_get(v___y_3790_, 2);
v_hasTrace_3834_ = lean_ctor_get_uint8(v_options_3833_, sizeof(void*)*1);
if (v_hasTrace_3834_ == 0)
{
v___y_3752_ = v___y_3787_;
v___y_3753_ = v___y_3788_;
v___y_3754_ = v___y_3789_;
v___y_3755_ = v___y_3790_;
v___y_3756_ = v___y_3791_;
goto v___jp_3751_;
}
else
{
lean_object* v_inheritedTraceOptions_3835_; lean_object* v___x_3836_; uint8_t v___x_3837_; 
v_inheritedTraceOptions_3835_ = lean_ctor_get(v___y_3790_, 13);
v___x_3836_ = lean_obj_once(&l_Lean_addDecl___closed__1, &l_Lean_addDecl___closed__1_once, _init_l_Lean_addDecl___closed__1);
v___x_3837_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3835_, v_options_3833_, v___x_3836_);
if (v___x_3837_ == 0)
{
v___y_3752_ = v___y_3787_;
v___y_3753_ = v___y_3788_;
v___y_3754_ = v___y_3789_;
v___y_3755_ = v___y_3790_;
v___y_3756_ = v___y_3791_;
goto v___jp_3751_;
}
else
{
lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3838_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__5, &l_Lean_addDecl___lam__8___closed__5_once, _init_l_Lean_addDecl___lam__8___closed__5);
v___x_3839_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3765_, v___x_3838_, v___y_3790_, v___y_3791_);
if (lean_obj_tag(v___x_3839_) == 0)
{
lean_dec_ref(v___x_3839_);
v___y_3752_ = v___y_3787_;
v___y_3753_ = v___y_3788_;
v___y_3754_ = v___y_3789_;
v___y_3755_ = v___y_3790_;
v___y_3756_ = v___y_3791_;
goto v___jp_3751_;
}
else
{
lean_dec_ref(v___y_3789_);
lean_dec(v___y_3788_);
lean_dec(v_decl_3569_);
return v___x_3839_;
}
}
}
}
}
}
v___jp_3840_:
{
lean_object* v___x_3847_; lean_object* v_env_3848_; uint8_t v___x_3849_; 
v___x_3847_ = lean_st_ref_get(v___y_3846_);
v_env_3848_ = lean_ctor_get(v___x_3847_, 0);
lean_inc_ref(v_env_3848_);
lean_dec(v___x_3847_);
v___x_3849_ = l_Lean_Environment_containsOnBranch(v_env_3848_, v_fst_3841_);
lean_dec_ref(v_env_3848_);
if (v___x_3849_ == 0)
{
v___y_3786_ = v_exportedInfo_x3f_3844_;
v___y_3787_ = v_snd_3843_;
v___y_3788_ = v_fst_3841_;
v___y_3789_ = v_fst_3842_;
v___y_3790_ = v___y_3845_;
v___y_3791_ = v___y_3846_;
goto v___jp_3785_;
}
else
{
lean_object* v___x_3850_; lean_object* v_env_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
lean_dec(v_exportedInfo_x3f_3844_);
lean_dec_ref(v_fst_3842_);
lean_dec(v_decl_3569_);
v___x_3850_ = lean_st_ref_get(v___y_3846_);
v_env_3851_ = lean_ctor_get(v___x_3850_, 0);
lean_inc_ref(v_env_3851_);
lean_dec(v___x_3850_);
v___x_3852_ = lean_elab_environment_to_kernel_env(v_env_3851_);
v___x_3853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3852_);
lean_ctor_set(v___x_3853_, 1, v_fst_3841_);
v___x_3854_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(v___x_3853_, v___y_3845_, v___y_3846_);
return v___x_3854_;
}
}
v___jp_3855_:
{
lean_object* v_name_3861_; lean_object* v___x_3862_; uint8_t v___x_3863_; 
v_name_3861_ = lean_ctor_get(v_toConstantVal_3857_, 0);
lean_inc(v_name_3861_);
lean_dec_ref(v_toConstantVal_3857_);
v___x_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3862_, 0, v___y_3856_);
v___x_3863_ = 0;
v_fst_3841_ = v_name_3861_;
v_fst_3842_ = v___x_3862_;
v_snd_3843_ = v___x_3863_;
v_exportedInfo_x3f_3844_ = v_exportedInfo_x3f_3858_;
v___y_3845_ = v___y_3859_;
v___y_3846_ = v___y_3860_;
goto v___jp_3840_;
}
v___jp_3864_:
{
lean_object* v_toConstantVal_3869_; 
v_toConstantVal_3869_ = lean_ctor_get(v___y_3865_, 0);
lean_inc_ref(v_toConstantVal_3869_);
v___y_3856_ = v___y_3865_;
v_toConstantVal_3857_ = v_toConstantVal_3869_;
v_exportedInfo_x3f_3858_ = v_exportedInfo_x3f_3866_;
v___y_3859_ = v___y_3867_;
v___y_3860_ = v___y_3868_;
goto v___jp_3855_;
}
v___jp_3870_:
{
uint8_t v___x_3876_; uint8_t v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3876_ = 0;
v___x_3877_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3873_, v___x_3876_);
lean_inc_ref(v_toConstantVal_3872_);
v___x_3878_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3878_, 0, v_toConstantVal_3872_);
lean_ctor_set_uint8(v___x_3878_, sizeof(void*)*1, v___x_3877_);
v___x_3879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3878_);
v___x_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3879_);
v___y_3856_ = v___y_3871_;
v_toConstantVal_3857_ = v_toConstantVal_3872_;
v_exportedInfo_x3f_3858_ = v___x_3880_;
v___y_3859_ = v___y_3874_;
v___y_3860_ = v___y_3875_;
goto v___jp_3855_;
}
v___jp_3881_:
{
lean_object* v_toConstantVal_3885_; uint8_t v_safety_3886_; 
v_toConstantVal_3885_ = lean_ctor_get(v___y_3882_, 0);
lean_inc_ref(v_toConstantVal_3885_);
v_safety_3886_ = lean_ctor_get_uint8(v___y_3882_, sizeof(void*)*4);
v___y_3871_ = v___y_3882_;
v_toConstantVal_3872_ = v_toConstantVal_3885_;
v_safety_3873_ = v_safety_3886_;
v___y_3874_ = v___y_3883_;
v___y_3875_ = v___y_3884_;
goto v___jp_3870_;
}
v___jp_3887_:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3891_ = lean_st_ref_get(v___y_3890_);
v___x_3892_ = lean_st_ref_get(v___y_3890_);
if (v_forceExpose_3570_ == 0)
{
lean_object* v_env_3893_; lean_object* v_env_3894_; lean_object* v___x_3895_; uint8_t v_isModule_3896_; 
v_env_3893_ = lean_ctor_get(v___x_3891_, 0);
lean_inc_ref(v_env_3893_);
lean_dec(v___x_3891_);
v_env_3894_ = lean_ctor_get(v___x_3892_, 0);
lean_inc_ref(v_env_3894_);
lean_dec(v___x_3892_);
v___x_3895_ = l_Lean_Environment_header(v_env_3893_);
lean_dec_ref(v_env_3893_);
v_isModule_3896_ = lean_ctor_get_uint8(v___x_3895_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3895_);
if (v_isModule_3896_ == 0)
{
lean_dec_ref(v_env_3894_);
v___y_3865_ = v_defn_3888_;
v_exportedInfo_x3f_3866_ = v___x_3784_;
v___y_3867_ = v___y_3889_;
v___y_3868_ = v___y_3890_;
goto v___jp_3864_;
}
else
{
uint8_t v_isExporting_3897_; 
v_isExporting_3897_ = lean_ctor_get_uint8(v_env_3894_, sizeof(void*)*8);
lean_dec_ref(v_env_3894_);
if (v_isExporting_3897_ == 0)
{
lean_object* v_options_3898_; uint8_t v_hasTrace_3899_; 
v_options_3898_ = lean_ctor_get(v___y_3889_, 2);
v_hasTrace_3899_ = lean_ctor_get_uint8(v_options_3898_, sizeof(void*)*1);
if (v_hasTrace_3899_ == 0)
{
v___y_3882_ = v_defn_3888_;
v___y_3883_ = v___y_3889_;
v___y_3884_ = v___y_3890_;
goto v___jp_3881_;
}
else
{
lean_object* v_inheritedTraceOptions_3900_; lean_object* v___x_3901_; uint8_t v___x_3902_; 
v_inheritedTraceOptions_3900_ = lean_ctor_get(v___y_3889_, 13);
v___x_3901_ = lean_obj_once(&l_Lean_addDecl___closed__1, &l_Lean_addDecl___closed__1_once, _init_l_Lean_addDecl___closed__1);
v___x_3902_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3900_, v_options_3898_, v___x_3901_);
if (v___x_3902_ == 0)
{
v___y_3882_ = v_defn_3888_;
v___y_3883_ = v___y_3889_;
v___y_3884_ = v___y_3890_;
goto v___jp_3881_;
}
else
{
lean_object* v_toConstantVal_3903_; uint8_t v_safety_3904_; lean_object* v_name_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
v_toConstantVal_3903_ = lean_ctor_get(v_defn_3888_, 0);
lean_inc_ref(v_toConstantVal_3903_);
v_safety_3904_ = lean_ctor_get_uint8(v_defn_3888_, sizeof(void*)*4);
v_name_3905_ = lean_ctor_get(v_toConstantVal_3903_, 0);
v___x_3906_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__1, &l_Lean_addDecl___lam__4___closed__1_once, _init_l_Lean_addDecl___lam__4___closed__1);
lean_inc(v_name_3905_);
v___x_3907_ = l_Lean_MessageData_ofName(v_name_3905_);
v___x_3908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3906_);
lean_ctor_set(v___x_3908_, 1, v___x_3907_);
v___x_3909_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_3910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3908_);
lean_ctor_set(v___x_3910_, 1, v___x_3909_);
v___x_3911_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3765_, v___x_3910_, v___y_3889_, v___y_3890_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_dec_ref(v___x_3911_);
v___y_3871_ = v_defn_3888_;
v_toConstantVal_3872_ = v_toConstantVal_3903_;
v_safety_3873_ = v_safety_3904_;
v___y_3874_ = v___y_3889_;
v___y_3875_ = v___y_3890_;
goto v___jp_3870_;
}
else
{
lean_dec_ref(v_toConstantVal_3903_);
lean_dec_ref(v_defn_3888_);
lean_dec(v_decl_3569_);
return v___x_3911_;
}
}
}
}
else
{
v___y_3865_ = v_defn_3888_;
v_exportedInfo_x3f_3866_ = v___x_3784_;
v___y_3867_ = v___y_3889_;
v___y_3868_ = v___y_3890_;
goto v___jp_3864_;
}
}
}
else
{
lean_dec(v___x_3892_);
lean_dec(v___x_3891_);
v___y_3865_ = v_defn_3888_;
v_exportedInfo_x3f_3866_ = v___x_3784_;
v___y_3867_ = v___y_3889_;
v___y_3868_ = v___y_3890_;
goto v___jp_3864_;
}
}
}
}
}
else
{
lean_object* v___f_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; uint8_t v___x_3968_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v_a_3972_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v_a_4018_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4075_; lean_object* v___y_4076_; uint8_t v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; 
lean_inc(v_decl_3569_);
v___f_3965_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__1___boxed), 5, 1);
lean_closure_set(v___f_3965_, 0, v_decl_3569_);
v___x_3966_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_3967_ = lean_obj_once(&l_Lean_addDecl___closed__1, &l_Lean_addDecl___closed__1_once, _init_l_Lean_addDecl___closed__1);
v___x_3968_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3627_, v_options_3626_, v___x_3967_);
if (v___x_3968_ == 0)
{
lean_object* v___x_4268_; uint8_t v___x_4269_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; uint8_t v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4375_; uint8_t v___y_4376_; lean_object* v___y_4377_; lean_object* v_exportedInfo_x3f_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4390_; uint8_t v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4397_; uint8_t v___y_4398_; lean_object* v___y_4399_; lean_object* v___y_4400_; lean_object* v___y_4401_; 
v___x_4268_ = l_Lean_trace_profiler;
v___x_4269_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3626_, v___x_4268_);
if (v___x_4269_ == 0)
{
lean_object* v___x_4403_; lean_object* v_env_4404_; lean_object* v_nextMacroScope_4405_; lean_object* v_ngen_4406_; lean_object* v_auxDeclNGen_4407_; lean_object* v_traceState_4408_; lean_object* v_messages_4409_; lean_object* v_infoState_4410_; lean_object* v_snapshotTasks_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4647_; 
lean_dec_ref(v___f_3965_);
v___x_4403_ = lean_st_ref_take(v_a_3572_);
v_env_4404_ = lean_ctor_get(v___x_4403_, 0);
v_nextMacroScope_4405_ = lean_ctor_get(v___x_4403_, 1);
v_ngen_4406_ = lean_ctor_get(v___x_4403_, 2);
v_auxDeclNGen_4407_ = lean_ctor_get(v___x_4403_, 3);
v_traceState_4408_ = lean_ctor_get(v___x_4403_, 4);
v_messages_4409_ = lean_ctor_get(v___x_4403_, 6);
v_infoState_4410_ = lean_ctor_get(v___x_4403_, 7);
v_snapshotTasks_4411_ = lean_ctor_get(v___x_4403_, 8);
v_isSharedCheck_4647_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4647_ == 0)
{
lean_object* v_unused_4648_; 
v_unused_4648_ = lean_ctor_get(v___x_4403_, 5);
lean_dec(v_unused_4648_);
v___x_4413_ = v___x_4403_;
v_isShared_4414_ = v_isSharedCheck_4647_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_snapshotTasks_4411_);
lean_inc(v_infoState_4410_);
lean_inc(v_messages_4409_);
lean_inc(v_traceState_4408_);
lean_inc(v_auxDeclNGen_4407_);
lean_inc(v_ngen_4406_);
lean_inc(v_nextMacroScope_4405_);
lean_inc(v_env_4404_);
lean_dec(v___x_4403_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4647_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___y_4419_; lean_object* v___y_4420_; lean_object* v___y_4421_; uint8_t v___y_4422_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___x_4447_; 
lean_inc(v_decl_3569_);
v___x_4415_ = l_Lean_Declaration_getNames(v_decl_3569_);
v___x_4416_ = l_List_foldl___at___00Lean_addDecl_spec__1(v_env_4404_, v___x_4415_);
v___x_4417_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2);
if (v_isShared_4414_ == 0)
{
lean_ctor_set(v___x_4413_, 5, v___x_4417_);
lean_ctor_set(v___x_4413_, 0, v___x_4416_);
v___x_4447_ = v___x_4413_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v___x_4416_);
lean_ctor_set(v_reuseFailAlloc_4646_, 1, v_nextMacroScope_4405_);
lean_ctor_set(v_reuseFailAlloc_4646_, 2, v_ngen_4406_);
lean_ctor_set(v_reuseFailAlloc_4646_, 3, v_auxDeclNGen_4407_);
lean_ctor_set(v_reuseFailAlloc_4646_, 4, v_traceState_4408_);
lean_ctor_set(v_reuseFailAlloc_4646_, 5, v___x_4417_);
lean_ctor_set(v_reuseFailAlloc_4646_, 6, v_messages_4409_);
lean_ctor_set(v_reuseFailAlloc_4646_, 7, v_infoState_4410_);
lean_ctor_set(v_reuseFailAlloc_4646_, 8, v_snapshotTasks_4411_);
v___x_4447_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4446_;
}
v___jp_4418_:
{
lean_object* v___x_4425_; lean_object* v_env_4426_; lean_object* v_nextMacroScope_4427_; lean_object* v_ngen_4428_; lean_object* v_auxDeclNGen_4429_; lean_object* v_traceState_4430_; lean_object* v_messages_4431_; lean_object* v_infoState_4432_; lean_object* v_snapshotTasks_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4444_; 
v___x_4425_ = lean_st_ref_take(v___y_4423_);
v_env_4426_ = lean_ctor_get(v___x_4425_, 0);
v_nextMacroScope_4427_ = lean_ctor_get(v___x_4425_, 1);
v_ngen_4428_ = lean_ctor_get(v___x_4425_, 2);
v_auxDeclNGen_4429_ = lean_ctor_get(v___x_4425_, 3);
v_traceState_4430_ = lean_ctor_get(v___x_4425_, 4);
v_messages_4431_ = lean_ctor_get(v___x_4425_, 6);
v_infoState_4432_ = lean_ctor_get(v___x_4425_, 7);
v_snapshotTasks_4433_ = lean_ctor_get(v___x_4425_, 8);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4425_);
if (v_isSharedCheck_4444_ == 0)
{
lean_object* v_unused_4445_; 
v_unused_4445_ = lean_ctor_get(v___x_4425_, 5);
lean_dec(v_unused_4445_);
v___x_4435_ = v___x_4425_;
v_isShared_4436_ = v_isSharedCheck_4444_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_snapshotTasks_4433_);
lean_inc(v_infoState_4432_);
lean_inc(v_messages_4431_);
lean_inc(v_traceState_4430_);
lean_inc(v_auxDeclNGen_4429_);
lean_inc(v_ngen_4428_);
lean_inc(v_nextMacroScope_4427_);
lean_inc(v_env_4426_);
lean_dec(v___x_4425_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4444_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4441_; 
v___x_4437_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4438_ = lean_box(v___y_4422_);
lean_inc(v___y_4424_);
v___x_4439_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4437_, v_env_4426_, v___y_4424_, v___x_4438_);
if (v_isShared_4436_ == 0)
{
lean_ctor_set(v___x_4435_, 5, v___x_4417_);
lean_ctor_set(v___x_4435_, 0, v___x_4439_);
v___x_4441_ = v___x_4435_;
goto v_reusejp_4440_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v___x_4439_);
lean_ctor_set(v_reuseFailAlloc_4443_, 1, v_nextMacroScope_4427_);
lean_ctor_set(v_reuseFailAlloc_4443_, 2, v_ngen_4428_);
lean_ctor_set(v_reuseFailAlloc_4443_, 3, v_auxDeclNGen_4429_);
lean_ctor_set(v_reuseFailAlloc_4443_, 4, v_traceState_4430_);
lean_ctor_set(v_reuseFailAlloc_4443_, 5, v___x_4417_);
lean_ctor_set(v_reuseFailAlloc_4443_, 6, v_messages_4431_);
lean_ctor_set(v_reuseFailAlloc_4443_, 7, v_infoState_4432_);
lean_ctor_set(v_reuseFailAlloc_4443_, 8, v_snapshotTasks_4433_);
v___x_4441_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4440_;
}
v_reusejp_4440_:
{
lean_object* v___x_4442_; 
v___x_4442_ = lean_st_ref_set(v___y_4423_, v___x_4441_);
v___y_4375_ = v___y_4420_;
v___y_4376_ = v___y_4422_;
v___y_4377_ = v___y_4424_;
v_exportedInfo_x3f_4378_ = v___y_4419_;
v___y_4379_ = v___y_4421_;
v___y_4380_ = v___y_4423_;
goto v___jp_4374_;
}
}
}
v_reusejp_4446_:
{
lean_object* v___x_4448_; lean_object* v___y_4450_; lean_object* v_options_4451_; lean_object* v_inheritedTraceOptions_4452_; lean_object* v___y_4453_; lean_object* v___x_4459_; lean_object* v___y_4461_; lean_object* v___y_4462_; uint8_t v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v_fst_4492_; lean_object* v_fst_4493_; uint8_t v_snd_4494_; lean_object* v_exportedInfo_x3f_4495_; lean_object* v___y_4496_; lean_object* v___y_4497_; lean_object* v___y_4507_; lean_object* v_toConstantVal_4508_; lean_object* v_exportedInfo_x3f_4509_; lean_object* v___y_4510_; lean_object* v___y_4511_; lean_object* v___y_4516_; lean_object* v_toConstantVal_4517_; uint8_t v_safety_4518_; lean_object* v___y_4519_; lean_object* v___y_4520_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4550_; lean_object* v_exportedInfo_x3f_4551_; lean_object* v___y_4552_; lean_object* v___y_4553_; lean_object* v___y_4556_; lean_object* v___y_4557_; lean_object* v___y_4558_; lean_object* v___y_4559_; lean_object* v___y_4560_; lean_object* v_defn_4565_; lean_object* v___y_4566_; lean_object* v___y_4567_; 
v___x_4448_ = lean_st_ref_set(v_a_3572_, v___x_4447_);
v___x_4459_ = lean_box(0);
switch(lean_obj_tag(v_decl_3569_))
{
case 2:
{
lean_object* v_val_4574_; lean_object* v_exportedInfo_x3f_4576_; lean_object* v___y_4577_; lean_object* v___y_4578_; lean_object* v___y_4584_; lean_object* v___y_4585_; lean_object* v___x_4590_; lean_object* v_env_4591_; 
v_val_4574_ = lean_ctor_get(v_decl_3569_, 0);
v___x_4590_ = lean_st_ref_get(v_a_3572_);
v_env_4591_ = lean_ctor_get(v___x_4590_, 0);
lean_inc_ref(v_env_4591_);
lean_dec(v___x_4590_);
if (v_forceExpose_3570_ == 0)
{
goto v___jp_4592_;
}
else
{
if (v___x_4269_ == 0)
{
lean_dec_ref(v_env_4591_);
v_exportedInfo_x3f_4576_ = v___x_4459_;
v___y_4577_ = v_a_3571_;
v___y_4578_ = v_a_3572_;
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
lean_ctor_set_uint8(v___x_4587_, sizeof(void*)*1, v___x_4269_);
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
v_exportedInfo_x3f_4576_ = v___x_4459_;
v___y_4577_ = v_a_3571_;
v___y_4578_ = v_a_3572_;
goto v___jp_4575_;
}
else
{
if (v___x_3968_ == 0)
{
v___y_4584_ = v_a_3571_;
v___y_4585_ = v_a_3572_;
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
v___x_4602_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3765_, v___x_4601_, v_a_3571_, v_a_3572_);
if (lean_obj_tag(v___x_4602_) == 0)
{
lean_dec_ref(v___x_4602_);
v___y_4584_ = v_a_3571_;
v___y_4585_ = v_a_3572_;
goto v___jp_4583_;
}
else
{
lean_dec_ref(v_decl_3569_);
return v___x_4602_;
}
}
}
}
}
case 1:
{
lean_object* v_val_4603_; 
v_val_4603_ = lean_ctor_get(v_decl_3569_, 0);
lean_inc_ref(v_val_4603_);
v_defn_4565_ = v_val_4603_;
v___y_4566_ = v_a_3571_;
v___y_4567_ = v_a_3572_;
goto v___jp_4564_;
}
case 5:
{
lean_object* v_defns_4604_; 
v_defns_4604_ = lean_ctor_get(v_decl_3569_, 0);
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
v___y_4566_ = v_a_3571_;
v___y_4567_ = v_a_3572_;
goto v___jp_4564_;
}
else
{
v___y_4450_ = v_a_3571_;
v_options_4451_ = v_options_3626_;
v_inheritedTraceOptions_4452_ = v_inheritedTraceOptions_3627_;
v___y_4453_ = v_a_3572_;
goto v___jp_4449_;
}
}
else
{
v___y_4450_ = v_a_3571_;
v_options_4451_ = v_options_3626_;
v_inheritedTraceOptions_4452_ = v_inheritedTraceOptions_3627_;
v___y_4453_ = v_a_3572_;
goto v___jp_4449_;
}
}
case 3:
{
lean_object* v_val_4607_; lean_object* v_exportedInfo_x3f_4609_; lean_object* v___y_4610_; lean_object* v___y_4611_; lean_object* v___y_4617_; lean_object* v___y_4618_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v_env_4635_; lean_object* v_env_4636_; 
v_val_4607_ = lean_ctor_get(v_decl_3569_, 0);
v___x_4624_ = lean_st_ref_get(v_a_3572_);
v___x_4625_ = lean_st_ref_get(v_a_3572_);
v_env_4635_ = lean_ctor_get(v___x_4624_, 0);
lean_inc_ref(v_env_4635_);
lean_dec(v___x_4624_);
v_env_4636_ = lean_ctor_get(v___x_4625_, 0);
lean_inc_ref(v_env_4636_);
lean_dec(v___x_4625_);
if (v_forceExpose_3570_ == 0)
{
goto v___jp_4637_;
}
else
{
if (v___x_4269_ == 0)
{
lean_dec_ref(v_env_4636_);
lean_dec_ref(v_env_4635_);
v_exportedInfo_x3f_4609_ = v___x_4459_;
v___y_4610_ = v_a_3571_;
v___y_4611_ = v_a_3572_;
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
if (v___x_3968_ == 0)
{
v___y_4617_ = v_a_3571_;
v___y_4618_ = v_a_3572_;
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
v___x_4634_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3765_, v___x_4633_, v_a_3571_, v_a_3572_);
if (lean_obj_tag(v___x_4634_) == 0)
{
lean_dec_ref(v___x_4634_);
v___y_4617_ = v_a_3571_;
v___y_4618_ = v_a_3572_;
goto v___jp_4616_;
}
else
{
lean_dec_ref(v_decl_3569_);
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
v_exportedInfo_x3f_4609_ = v___x_4459_;
v___y_4610_ = v_a_3571_;
v___y_4611_ = v_a_3572_;
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
if (v___x_4269_ == 0)
{
v_exportedInfo_x3f_4609_ = v___x_4459_;
v___y_4610_ = v_a_3571_;
v___y_4611_ = v_a_3572_;
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
v_val_4641_ = lean_ctor_get(v_decl_3569_, 0);
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
v_exportedInfo_x3f_4495_ = v___x_4459_;
v___y_4496_ = v_a_3571_;
v___y_4497_ = v_a_3572_;
goto v___jp_4491_;
}
default: 
{
v___y_4450_ = v_a_3571_;
v_options_4451_ = v_options_3626_;
v_inheritedTraceOptions_4452_ = v_inheritedTraceOptions_3627_;
v___y_4453_ = v_a_3572_;
goto v___jp_4449_;
}
}
v___jp_4449_:
{
uint8_t v___x_4454_; 
v___x_4454_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4452_, v_options_4451_, v___x_3967_);
if (v___x_4454_ == 0)
{
lean_object* v___x_4455_; 
v___x_4455_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3569_, v___y_4450_, v___y_4453_);
return v___x_4455_;
}
else
{
lean_object* v___x_4456_; lean_object* v___x_4457_; 
v___x_4456_ = lean_obj_once(&l_Lean_addDecl___lam__3___closed__1, &l_Lean_addDecl___lam__3___closed__1_once, _init_l_Lean_addDecl___lam__3___closed__1);
v___x_4457_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3765_, v___x_4456_, v___y_4450_, v___y_4453_);
if (lean_obj_tag(v___x_4457_) == 0)
{
lean_object* v___x_4458_; 
lean_dec_ref(v___x_4457_);
v___x_4458_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3569_, v___y_4450_, v___y_4453_);
return v___x_4458_;
}
else
{
lean_dec(v_decl_3569_);
return v___x_4457_;
}
}
}
v___jp_4460_:
{
lean_object* v___x_4467_; uint8_t v___x_4468_; 
lean_inc(v_decl_3569_);
v___x_4467_ = l_Lean_Declaration_getTopLevelNames(v_decl_3569_);
v___x_4468_ = l_List_all___at___00Lean_addDecl_spec__2(v___x_4467_);
lean_dec(v___x_4467_);
if (v___x_4468_ == 0)
{
if (lean_obj_tag(v___y_4461_) == 0)
{
if (v___x_4269_ == 0)
{
lean_object* v_options_4469_; uint8_t v_hasTrace_4470_; 
v_options_4469_ = lean_ctor_get(v___y_4465_, 2);
v_hasTrace_4470_ = lean_ctor_get_uint8(v_options_4469_, sizeof(void*)*1);
if (v_hasTrace_4470_ == 0)
{
v___y_4390_ = v___y_4462_;
v___y_4391_ = v___y_4463_;
v___y_4392_ = v___y_4464_;
v___y_4393_ = v___y_4465_;
v___y_4394_ = v___y_4466_;
goto v___jp_4389_;
}
else
{
lean_object* v_inheritedTraceOptions_4471_; uint8_t v___x_4472_; 
v_inheritedTraceOptions_4471_ = lean_ctor_get(v___y_4465_, 13);
v___x_4472_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4471_, v_options_4469_, v___x_3967_);
if (v___x_4472_ == 0)
{
v___y_4390_ = v___y_4462_;
v___y_4391_ = v___y_4463_;
v___y_4392_ = v___y_4464_;
v___y_4393_ = v___y_4465_;
v___y_4394_ = v___y_4466_;
goto v___jp_4389_;
}
else
{
lean_object* v___x_4473_; lean_object* v___x_4474_; 
v___x_4473_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__1, &l_Lean_addDecl___lam__8___closed__1_once, _init_l_Lean_addDecl___lam__8___closed__1);
v___x_4474_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3765_, v___x_4473_, v___y_4465_, v___y_4466_);
if (lean_obj_tag(v___x_4474_) == 0)
{
lean_dec_ref(v___x_4474_);
v___y_4390_ = v___y_4462_;
v___y_4391_ = v___y_4463_;
v___y_4392_ = v___y_4464_;
v___y_4393_ = v___y_4465_;
v___y_4394_ = v___y_4466_;
goto v___jp_4389_;
}
else
{
lean_dec(v___y_4464_);
lean_dec_ref(v___y_4462_);
lean_dec(v_decl_3569_);
return v___x_4474_;
}
}
}
}
else
{
v___y_4419_ = v___y_4461_;
v___y_4420_ = v___y_4462_;
v___y_4421_ = v___y_4465_;
v___y_4422_ = v___y_4463_;
v___y_4423_ = v___y_4466_;
v___y_4424_ = v___y_4464_;
goto v___jp_4418_;
}
}
else
{
v___y_4419_ = v___y_4461_;
v___y_4420_ = v___y_4462_;
v___y_4421_ = v___y_4465_;
v___y_4422_ = v___y_4463_;
v___y_4423_ = v___y_4466_;
v___y_4424_ = v___y_4464_;
goto v___jp_4418_;
}
}
else
{
lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v_a_4477_; uint8_t v___x_4478_; 
lean_dec(v___y_4461_);
v___x_4475_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4476_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__3___redArg(v___x_4475_, v___y_4465_);
v_a_4477_ = lean_ctor_get(v___x_4476_, 0);
lean_inc(v_a_4477_);
lean_dec_ref(v___x_4476_);
v___x_4478_ = lean_unbox(v_a_4477_);
lean_dec(v_a_4477_);
if (v___x_4478_ == 0)
{
lean_object* v_options_4479_; uint8_t v_hasTrace_4480_; 
v_options_4479_ = lean_ctor_get(v___y_4465_, 2);
v_hasTrace_4480_ = lean_ctor_get_uint8(v_options_4479_, sizeof(void*)*1);
if (v_hasTrace_4480_ == 0)
{
v___y_4375_ = v___y_4462_;
v___y_4376_ = v___y_4463_;
v___y_4377_ = v___y_4464_;
v_exportedInfo_x3f_4378_ = v___x_4459_;
v___y_4379_ = v___y_4465_;
v___y_4380_ = v___y_4466_;
goto v___jp_4374_;
}
else
{
lean_object* v_inheritedTraceOptions_4481_; uint8_t v___x_4482_; 
v_inheritedTraceOptions_4481_ = lean_ctor_get(v___y_4465_, 13);
v___x_4482_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4481_, v_options_4479_, v___x_3967_);
if (v___x_4482_ == 0)
{
v___y_4375_ = v___y_4462_;
v___y_4376_ = v___y_4463_;
v___y_4377_ = v___y_4464_;
v_exportedInfo_x3f_4378_ = v___x_4459_;
v___y_4379_ = v___y_4465_;
v___y_4380_ = v___y_4466_;
goto v___jp_4374_;
}
else
{
lean_object* v___x_4483_; lean_object* v___x_4484_; 
v___x_4483_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__3, &l_Lean_addDecl___lam__8___closed__3_once, _init_l_Lean_addDecl___lam__8___closed__3);
v___x_4484_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3765_, v___x_4483_, v___y_4465_, v___y_4466_);
if (lean_obj_tag(v___x_4484_) == 0)
{
lean_dec_ref(v___x_4484_);
v___y_4375_ = v___y_4462_;
v___y_4376_ = v___y_4463_;
v___y_4377_ = v___y_4464_;
v_exportedInfo_x3f_4378_ = v___x_4459_;
v___y_4379_ = v___y_4465_;
v___y_4380_ = v___y_4466_;
goto v___jp_4374_;
}
else
{
lean_dec(v___y_4464_);
lean_dec_ref(v___y_4462_);
lean_dec(v_decl_3569_);
return v___x_4484_;
}
}
}
}
else
{
lean_object* v_options_4485_; uint8_t v_hasTrace_4486_; 
v_options_4485_ = lean_ctor_get(v___y_4465_, 2);
v_hasTrace_4486_ = lean_ctor_get_uint8(v_options_4485_, sizeof(void*)*1);
if (v_hasTrace_4486_ == 0)
{
v___y_4397_ = v___y_4462_;
v___y_4398_ = v___y_4463_;
v___y_4399_ = v___y_4464_;
v___y_4400_ = v___y_4465_;
v___y_4401_ = v___y_4466_;
goto v___jp_4396_;
}
else
{
lean_object* v_inheritedTraceOptions_4487_; uint8_t v___x_4488_; 
v_inheritedTraceOptions_4487_ = lean_ctor_get(v___y_4465_, 13);
v___x_4488_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4487_, v_options_4485_, v___x_3967_);
if (v___x_4488_ == 0)
{
v___y_4397_ = v___y_4462_;
v___y_4398_ = v___y_4463_;
v___y_4399_ = v___y_4464_;
v___y_4400_ = v___y_4465_;
v___y_4401_ = v___y_4466_;
goto v___jp_4396_;
}
else
{
lean_object* v___x_4489_; lean_object* v___x_4490_; 
v___x_4489_ = lean_obj_once(&l_Lean_addDecl___lam__8___closed__5, &l_Lean_addDecl___lam__8___closed__5_once, _init_l_Lean_addDecl___lam__8___closed__5);
v___x_4490_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3765_, v___x_4489_, v___y_4465_, v___y_4466_);
if (lean_obj_tag(v___x_4490_) == 0)
{
lean_dec_ref(v___x_4490_);
v___y_4397_ = v___y_4462_;
v___y_4398_ = v___y_4463_;
v___y_4399_ = v___y_4464_;
v___y_4400_ = v___y_4465_;
v___y_4401_ = v___y_4466_;
goto v___jp_4396_;
}
else
{
lean_dec(v___y_4464_);
lean_dec_ref(v___y_4462_);
lean_dec(v_decl_3569_);
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
v___y_4461_ = v_exportedInfo_x3f_4495_;
v___y_4462_ = v_fst_4493_;
v___y_4463_ = v_snd_4494_;
v___y_4464_ = v_fst_4492_;
v___y_4465_ = v___y_4496_;
v___y_4466_ = v___y_4497_;
goto v___jp_4460_;
}
else
{
lean_object* v___x_4501_; lean_object* v_env_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; 
lean_dec(v_exportedInfo_x3f_4495_);
lean_dec_ref(v_fst_4493_);
lean_dec(v_decl_3569_);
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
v_options_4536_ = lean_ctor_get(v___y_4535_, 2);
v_hasTrace_4537_ = lean_ctor_get_uint8(v_options_4536_, sizeof(void*)*1);
if (v_hasTrace_4537_ == 0)
{
v___y_4527_ = v___y_4533_;
v___y_4528_ = v___y_4535_;
v___y_4529_ = v___y_4534_;
goto v___jp_4526_;
}
else
{
lean_object* v_inheritedTraceOptions_4538_; uint8_t v___x_4539_; 
v_inheritedTraceOptions_4538_ = lean_ctor_get(v___y_4535_, 13);
v___x_4539_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4538_, v_options_4536_, v___x_3967_);
if (v___x_4539_ == 0)
{
v___y_4527_ = v___y_4533_;
v___y_4528_ = v___y_4535_;
v___y_4529_ = v___y_4534_;
goto v___jp_4526_;
}
else
{
lean_object* v_toConstantVal_4540_; uint8_t v_safety_4541_; lean_object* v_name_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; 
v_toConstantVal_4540_ = lean_ctor_get(v___y_4533_, 0);
lean_inc_ref(v_toConstantVal_4540_);
v_safety_4541_ = lean_ctor_get_uint8(v___y_4533_, sizeof(void*)*4);
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
v___x_4548_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3765_, v___x_4547_, v___y_4535_, v___y_4534_);
if (lean_obj_tag(v___x_4548_) == 0)
{
lean_dec_ref(v___x_4548_);
v___y_4516_ = v___y_4533_;
v_toConstantVal_4517_ = v_toConstantVal_4540_;
v_safety_4518_ = v_safety_4541_;
v___y_4519_ = v___y_4535_;
v___y_4520_ = v___y_4534_;
goto v___jp_4515_;
}
else
{
lean_dec_ref(v_toConstantVal_4540_);
lean_dec_ref(v___y_4533_);
lean_dec(v_decl_3569_);
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
v___x_4561_ = l_Lean_Environment_header(v___y_4560_);
lean_dec_ref(v___y_4560_);
v_isModule_4562_ = lean_ctor_get_uint8(v___x_4561_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4561_);
if (v_isModule_4562_ == 0)
{
lean_dec_ref(v___y_4559_);
v___y_4550_ = v___y_4556_;
v_exportedInfo_x3f_4551_ = v___x_4459_;
v___y_4552_ = v___y_4558_;
v___y_4553_ = v___y_4557_;
goto v___jp_4549_;
}
else
{
uint8_t v_isExporting_4563_; 
v_isExporting_4563_ = lean_ctor_get_uint8(v___y_4559_, sizeof(void*)*8);
lean_dec_ref(v___y_4559_);
if (v_isExporting_4563_ == 0)
{
v___y_4533_ = v___y_4556_;
v___y_4534_ = v___y_4557_;
v___y_4535_ = v___y_4558_;
goto v___jp_4532_;
}
else
{
if (v___x_4269_ == 0)
{
v___y_4550_ = v___y_4556_;
v_exportedInfo_x3f_4551_ = v___x_4459_;
v___y_4552_ = v___y_4558_;
v___y_4553_ = v___y_4557_;
goto v___jp_4549_;
}
else
{
v___y_4533_ = v___y_4556_;
v___y_4534_ = v___y_4557_;
v___y_4535_ = v___y_4558_;
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
if (v_forceExpose_3570_ == 0)
{
lean_object* v_env_4570_; lean_object* v_env_4571_; 
v_env_4570_ = lean_ctor_get(v___x_4568_, 0);
lean_inc_ref(v_env_4570_);
lean_dec(v___x_4568_);
v_env_4571_ = lean_ctor_get(v___x_4569_, 0);
lean_inc_ref(v_env_4571_);
lean_dec(v___x_4569_);
v___y_4556_ = v_defn_4565_;
v___y_4557_ = v___y_4567_;
v___y_4558_ = v___y_4566_;
v___y_4559_ = v_env_4571_;
v___y_4560_ = v_env_4570_;
goto v___jp_4555_;
}
else
{
if (v___x_4269_ == 0)
{
lean_dec(v___x_4569_);
lean_dec(v___x_4568_);
v___y_4550_ = v_defn_4565_;
v_exportedInfo_x3f_4551_ = v___x_4459_;
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
v___y_4556_ = v_defn_4565_;
v___y_4557_ = v___y_4567_;
v___y_4558_ = v___y_4566_;
v___y_4559_ = v_env_4573_;
v___y_4560_ = v_env_4572_;
goto v___jp_4555_;
}
}
}
}
}
}
else
{
goto v___jp_4116_;
}
v___jp_4270_:
{
lean_object* v___x_4281_; 
lean_inc_ref(v___y_4272_);
v___x_4281_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_4277_, v___y_4272_, v___y_4276_, v___y_4280_);
if (lean_obj_tag(v___x_4281_) == 0)
{
lean_object* v___x_4282_; lean_object* v___x_4284_; uint8_t v_isShared_4285_; uint8_t v_isSharedCheck_4328_; 
lean_dec_ref(v___x_4281_);
lean_inc_ref(v___y_4274_);
v___x_4282_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_4274_, v___y_4275_);
v_isSharedCheck_4328_ = !lean_is_exclusive(v___x_4282_);
if (v_isSharedCheck_4328_ == 0)
{
lean_object* v_unused_4329_; 
v_unused_4329_ = lean_ctor_get(v___x_4282_, 0);
lean_dec(v_unused_4329_);
v___x_4284_ = v___x_4282_;
v_isShared_4285_ = v_isSharedCheck_4328_;
goto v_resetjp_4283_;
}
else
{
lean_dec(v___x_4282_);
v___x_4284_ = lean_box(0);
v_isShared_4285_ = v_isSharedCheck_4328_;
goto v_resetjp_4283_;
}
v_resetjp_4283_:
{
lean_object* v_options_4286_; lean_object* v___x_4287_; uint8_t v___x_4288_; 
v_options_4286_ = lean_ctor_get(v___y_4278_, 2);
v___x_4287_ = l_Lean_Elab_async;
v___x_4288_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_4286_, v___x_4287_);
if (v___x_4288_ == 0)
{
lean_object* v___x_4289_; lean_object* v_r_4290_; 
lean_del_object(v___x_4284_);
lean_dec_ref(v___y_4279_);
lean_dec_ref(v___y_4271_);
v___x_4289_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_4272_, v___y_4275_);
lean_dec_ref(v___x_4289_);
v_r_4290_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3569_, v___y_4278_, v___y_4275_);
if (lean_obj_tag(v_r_4290_) == 0)
{
lean_object* v_a_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4300_; 
v_a_4291_ = lean_ctor_get(v_r_4290_, 0);
v_isSharedCheck_4300_ = !lean_is_exclusive(v_r_4290_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4293_ = v_r_4290_;
v_isShared_4294_ = v_isSharedCheck_4300_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_a_4291_);
lean_dec(v_r_4290_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4300_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v___x_4296_; 
lean_inc(v_a_4291_);
if (v_isShared_4294_ == 0)
{
lean_ctor_set_tag(v___x_4293_, 1);
v___x_4296_ = v___x_4293_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_a_4291_);
v___x_4296_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
lean_object* v___x_4297_; 
v___x_4297_ = lean_apply_2(v___y_4273_, v___x_4296_, lean_box(0));
if (lean_obj_tag(v___x_4297_) == 0)
{
lean_dec_ref(v___x_4297_);
v___y_3588_ = v___y_4275_;
v___y_3589_ = v___y_4274_;
v_a_3590_ = v_a_4291_;
goto v___jp_3587_;
}
else
{
lean_object* v_a_4298_; 
lean_dec(v_a_4291_);
v_a_4298_ = lean_ctor_get(v___x_4297_, 0);
lean_inc(v_a_4298_);
lean_dec_ref(v___x_4297_);
v___y_3575_ = v___y_4275_;
v___y_3576_ = v___y_4274_;
v_a_3577_ = v_a_4298_;
goto v___jp_3574_;
}
}
}
}
else
{
lean_object* v_a_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; 
v_a_4301_ = lean_ctor_get(v_r_4290_, 0);
lean_inc(v_a_4301_);
lean_dec_ref(v_r_4290_);
v___x_4302_ = lean_box(0);
v___x_4303_ = lean_apply_2(v___y_4273_, v___x_4302_, lean_box(0));
if (lean_obj_tag(v___x_4303_) == 0)
{
lean_dec_ref(v___x_4303_);
v___y_3575_ = v___y_4275_;
v___y_3576_ = v___y_4274_;
v_a_3577_ = v_a_4301_;
goto v___jp_3574_;
}
else
{
lean_object* v_a_4304_; 
lean_dec(v_a_4301_);
v_a_4304_ = lean_ctor_get(v___x_4303_, 0);
lean_inc(v_a_4304_);
lean_dec_ref(v___x_4303_);
v___y_3575_ = v___y_4275_;
v___y_3576_ = v___y_4274_;
v_a_3577_ = v_a_4304_;
goto v___jp_3574_;
}
}
}
else
{
lean_object* v___x_4305_; lean_object* v___x_4307_; 
lean_dec_ref(v___y_4274_);
lean_dec_ref(v___y_4273_);
lean_dec_ref(v___y_4272_);
lean_dec(v_decl_3569_);
v___x_4305_ = l_IO_CancelToken_new();
if (v_isShared_4285_ == 0)
{
lean_ctor_set_tag(v___x_4284_, 1);
lean_ctor_set(v___x_4284_, 0, v___x_4305_);
v___x_4307_ = v___x_4284_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4327_; 
v_reuseFailAlloc_4327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4327_, 0, v___x_4305_);
v___x_4307_ = v_reuseFailAlloc_4327_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; 
v___x_4308_ = ((lean_object*)(l_Lean_addDecl___closed__0));
v___x_4309_ = l_Lean_Name_toString(v___x_4308_, v_hasTrace_3628_);
lean_inc_ref(v___x_4307_);
v___x_4310_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_4271_, v___x_4307_, v___x_4309_, v___y_4278_, v___y_4275_);
if (lean_obj_tag(v___x_4310_) == 0)
{
lean_object* v_a_4311_; lean_object* v_checked_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; 
v_a_4311_ = lean_ctor_get(v___x_4310_, 0);
lean_inc(v_a_4311_);
lean_dec_ref(v___x_4310_);
v_checked_4312_ = lean_ctor_get(v___y_4279_, 2);
lean_inc_ref(v_checked_4312_);
lean_dec_ref(v___y_4279_);
v___x_4313_ = lean_unsigned_to_nat(0u);
v___x_4314_ = lean_io_map_task(v_a_4311_, v_checked_4312_, v___x_4313_, v___x_4269_);
v___x_4315_ = lean_box(0);
v___x_4316_ = lean_box(2);
v___x_4317_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4317_, 0, v___x_4315_);
lean_ctor_set(v___x_4317_, 1, v___x_4316_);
lean_ctor_set(v___x_4317_, 2, v___x_4307_);
lean_ctor_set(v___x_4317_, 3, v___x_4314_);
v___x_4318_ = l_Lean_Core_logSnapshotTask___redArg(v___x_4317_, v___y_4275_);
return v___x_4318_;
}
else
{
lean_object* v_a_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4326_; 
lean_dec_ref(v___x_4307_);
lean_dec_ref(v___y_4279_);
v_a_4319_ = lean_ctor_get(v___x_4310_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v___x_4310_);
if (v_isSharedCheck_4326_ == 0)
{
v___x_4321_ = v___x_4310_;
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_a_4319_);
lean_dec(v___x_4310_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
lean_object* v___x_4324_; 
if (v_isShared_4322_ == 0)
{
v___x_4324_ = v___x_4321_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_a_4319_);
v___x_4324_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
return v___x_4324_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4330_; lean_object* v___x_4332_; uint8_t v_isShared_4333_; uint8_t v_isSharedCheck_4342_; 
lean_dec_ref(v___y_4279_);
lean_dec_ref(v___y_4274_);
lean_dec_ref(v___y_4273_);
lean_dec_ref(v___y_4272_);
lean_dec_ref(v___y_4271_);
lean_dec(v_decl_3569_);
v_a_4330_ = lean_ctor_get(v___x_4281_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4281_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4332_ = v___x_4281_;
v_isShared_4333_ = v_isSharedCheck_4342_;
goto v_resetjp_4331_;
}
else
{
lean_inc(v_a_4330_);
lean_dec(v___x_4281_);
v___x_4332_ = lean_box(0);
v_isShared_4333_ = v_isSharedCheck_4342_;
goto v_resetjp_4331_;
}
v_resetjp_4331_:
{
lean_object* v_ref_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4340_; 
v_ref_4334_ = lean_ctor_get(v___y_4278_, 5);
v___x_4335_ = lean_io_error_to_string(v_a_4330_);
v___x_4336_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4336_, 0, v___x_4335_);
v___x_4337_ = l_Lean_MessageData_ofFormat(v___x_4336_);
lean_inc(v_ref_4334_);
v___x_4338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4338_, 0, v_ref_4334_);
lean_ctor_set(v___x_4338_, 1, v___x_4337_);
if (v_isShared_4333_ == 0)
{
lean_ctor_set(v___x_4332_, 0, v___x_4338_);
v___x_4340_ = v___x_4332_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v___x_4338_);
v___x_4340_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
return v___x_4340_;
}
}
}
}
v___jp_4343_:
{
lean_object* v___x_4354_; 
lean_inc_ref(v___y_4346_);
v___x_4354_ = l_Lean_Environment_addConstAsync(v___y_4346_, v___y_4352_, v___y_4349_, v___y_4353_, v___x_4269_, v_hasTrace_3628_);
if (lean_obj_tag(v___x_4354_) == 0)
{
lean_object* v_a_4355_; lean_object* v_mainEnv_4356_; lean_object* v_asyncEnv_4357_; lean_object* v___f_4358_; lean_object* v___f_4359_; lean_object* v___x_4360_; 
v_a_4355_ = lean_ctor_get(v___x_4354_, 0);
lean_inc_n(v_a_4355_, 3);
lean_dec_ref(v___x_4354_);
v_mainEnv_4356_ = lean_ctor_get(v_a_4355_, 0);
lean_inc_ref(v_mainEnv_4356_);
v_asyncEnv_4357_ = lean_ctor_get(v_a_4355_, 1);
lean_inc_ref_n(v_asyncEnv_4357_, 2);
lean_inc_ref(v___y_4345_);
lean_inc(v___y_4344_);
v___f_4358_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4358_, 0, v___y_4344_);
lean_closure_set(v___f_4358_, 1, v_a_4355_);
lean_closure_set(v___f_4358_, 2, v___y_4345_);
lean_inc(v_decl_3569_);
v___f_4359_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4359_, 0, v_asyncEnv_4357_);
lean_closure_set(v___f_4359_, 1, v_a_4355_);
lean_closure_set(v___f_4359_, 2, v_decl_3569_);
v___x_4360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4360_, 0, v___y_4347_);
if (lean_obj_tag(v___y_4351_) == 0)
{
lean_inc_ref(v___x_4360_);
v___y_4271_ = v___f_4359_;
v___y_4272_ = v_asyncEnv_4357_;
v___y_4273_ = v___f_4358_;
v___y_4274_ = v_mainEnv_4356_;
v___y_4275_ = v___y_4348_;
v___y_4276_ = v___x_4360_;
v___y_4277_ = v_a_4355_;
v___y_4278_ = v___y_4350_;
v___y_4279_ = v___y_4346_;
v___y_4280_ = v___x_4360_;
goto v___jp_4270_;
}
else
{
v___y_4271_ = v___f_4359_;
v___y_4272_ = v_asyncEnv_4357_;
v___y_4273_ = v___f_4358_;
v___y_4274_ = v_mainEnv_4356_;
v___y_4275_ = v___y_4348_;
v___y_4276_ = v___x_4360_;
v___y_4277_ = v_a_4355_;
v___y_4278_ = v___y_4350_;
v___y_4279_ = v___y_4346_;
v___y_4280_ = v___y_4351_;
goto v___jp_4270_;
}
}
else
{
lean_object* v_a_4361_; lean_object* v___x_4363_; uint8_t v_isShared_4364_; uint8_t v_isSharedCheck_4373_; 
lean_dec(v___y_4351_);
lean_dec_ref(v___y_4347_);
lean_dec_ref(v___y_4346_);
lean_dec(v_decl_3569_);
v_a_4361_ = lean_ctor_get(v___x_4354_, 0);
v_isSharedCheck_4373_ = !lean_is_exclusive(v___x_4354_);
if (v_isSharedCheck_4373_ == 0)
{
v___x_4363_ = v___x_4354_;
v_isShared_4364_ = v_isSharedCheck_4373_;
goto v_resetjp_4362_;
}
else
{
lean_inc(v_a_4361_);
lean_dec(v___x_4354_);
v___x_4363_ = lean_box(0);
v_isShared_4364_ = v_isSharedCheck_4373_;
goto v_resetjp_4362_;
}
v_resetjp_4362_:
{
lean_object* v_ref_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4371_; 
v_ref_4365_ = lean_ctor_get(v___y_4350_, 5);
v___x_4366_ = lean_io_error_to_string(v_a_4361_);
v___x_4367_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4367_, 0, v___x_4366_);
v___x_4368_ = l_Lean_MessageData_ofFormat(v___x_4367_);
lean_inc(v_ref_4365_);
v___x_4369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4369_, 0, v_ref_4365_);
lean_ctor_set(v___x_4369_, 1, v___x_4368_);
if (v_isShared_4364_ == 0)
{
lean_ctor_set(v___x_4363_, 0, v___x_4369_);
v___x_4371_ = v___x_4363_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v___x_4369_);
v___x_4371_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
return v___x_4371_;
}
}
}
}
v___jp_4374_:
{
lean_object* v___x_4381_; 
v___x_4381_ = lean_st_ref_get(v___y_4380_);
if (lean_obj_tag(v_exportedInfo_x3f_4378_) == 0)
{
lean_object* v_env_4382_; lean_object* v___x_4383_; 
v_env_4382_ = lean_ctor_get(v___x_4381_, 0);
lean_inc_ref(v_env_4382_);
lean_dec(v___x_4381_);
v___x_4383_ = lean_box(0);
v___y_4344_ = v___y_4380_;
v___y_4345_ = v___y_4379_;
v___y_4346_ = v_env_4382_;
v___y_4347_ = v___y_4375_;
v___y_4348_ = v___y_4380_;
v___y_4349_ = v___y_4376_;
v___y_4350_ = v___y_4379_;
v___y_4351_ = v_exportedInfo_x3f_4378_;
v___y_4352_ = v___y_4377_;
v___y_4353_ = v___x_4383_;
goto v___jp_4343_;
}
else
{
lean_object* v_env_4384_; lean_object* v_val_4385_; uint8_t v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; 
v_env_4384_ = lean_ctor_get(v___x_4381_, 0);
lean_inc_ref(v_env_4384_);
lean_dec(v___x_4381_);
v_val_4385_ = lean_ctor_get(v_exportedInfo_x3f_4378_, 0);
v___x_4386_ = l_Lean_ConstantKind_ofConstantInfo(v_val_4385_);
v___x_4387_ = lean_box(v___x_4386_);
v___x_4388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4388_, 0, v___x_4387_);
v___y_4344_ = v___y_4380_;
v___y_4345_ = v___y_4379_;
v___y_4346_ = v_env_4384_;
v___y_4347_ = v___y_4375_;
v___y_4348_ = v___y_4380_;
v___y_4349_ = v___y_4376_;
v___y_4350_ = v___y_4379_;
v___y_4351_ = v_exportedInfo_x3f_4378_;
v___y_4352_ = v___y_4377_;
v___y_4353_ = v___x_4388_;
goto v___jp_4343_;
}
}
v___jp_4389_:
{
lean_object* v___x_4395_; 
lean_inc_ref(v___y_4390_);
v___x_4395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4395_, 0, v___y_4390_);
v___y_4375_ = v___y_4390_;
v___y_4376_ = v___y_4391_;
v___y_4377_ = v___y_4392_;
v_exportedInfo_x3f_4378_ = v___x_4395_;
v___y_4379_ = v___y_4393_;
v___y_4380_ = v___y_4394_;
goto v___jp_4374_;
}
v___jp_4396_:
{
lean_object* v___x_4402_; 
lean_inc_ref(v___y_4397_);
v___x_4402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4402_, 0, v___y_4397_);
v___y_4375_ = v___y_4397_;
v___y_4376_ = v___y_4398_;
v___y_4377_ = v___y_4399_;
v_exportedInfo_x3f_4378_ = v___x_4402_;
v___y_4379_ = v___y_4400_;
v___y_4380_ = v___y_4401_;
goto v___jp_4374_;
}
}
else
{
goto v___jp_4116_;
}
v___jp_3969_:
{
lean_object* v___x_3973_; double v___x_3974_; double v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3973_ = lean_io_get_num_heartbeats();
v___x_3974_ = lean_float_of_nat(v___y_3970_);
v___x_3975_ = lean_float_of_nat(v___x_3973_);
v___x_3976_ = lean_box_float(v___x_3974_);
v___x_3977_ = lean_box_float(v___x_3975_);
v___x_3978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3978_, 0, v___x_3976_);
lean_ctor_set(v___x_3978_, 1, v___x_3977_);
v___x_3979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3979_, 0, v_a_3972_);
lean_ctor_set(v___x_3979_, 1, v___x_3978_);
v___x_3980_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2(v_cls_3765_, v_hasTrace_3628_, v___x_3966_, v_options_3626_, v___x_3968_, v___y_3971_, v___f_3965_, v___x_3979_, v_a_3571_, v_a_3572_);
return v___x_3980_;
}
v___jp_3981_:
{
if (lean_obj_tag(v___y_3984_) == 0)
{
lean_object* v_a_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_3992_; 
v_a_3985_ = lean_ctor_get(v___y_3984_, 0);
v_isSharedCheck_3992_ = !lean_is_exclusive(v___y_3984_);
if (v_isSharedCheck_3992_ == 0)
{
v___x_3987_ = v___y_3984_;
v_isShared_3988_ = v_isSharedCheck_3992_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_a_3985_);
lean_dec(v___y_3984_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_3992_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3990_; 
if (v_isShared_3988_ == 0)
{
lean_ctor_set_tag(v___x_3987_, 1);
v___x_3990_ = v___x_3987_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v_a_3985_);
v___x_3990_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
v___y_3970_ = v___y_3982_;
v___y_3971_ = v___y_3983_;
v_a_3972_ = v___x_3990_;
goto v___jp_3969_;
}
}
}
else
{
lean_object* v_a_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4000_; 
v_a_3993_ = lean_ctor_get(v___y_3984_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___y_3984_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3995_ = v___y_3984_;
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_a_3993_);
lean_dec(v___y_3984_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3998_; 
if (v_isShared_3996_ == 0)
{
lean_ctor_set_tag(v___x_3995_, 0);
v___x_3998_ = v___x_3995_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3993_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
v___y_3970_ = v___y_3982_;
v___y_3971_ = v___y_3983_;
v_a_3972_ = v___x_3998_;
goto v___jp_3969_;
}
}
}
}
v___jp_4001_:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_4006_ = lean_box(0);
lean_inc(v_a_3572_);
lean_inc_ref(v_a_3571_);
v___x_4007_ = lean_apply_5(v___y_4005_, v___x_4006_, v___y_4004_, v_a_3571_, v_a_3572_, lean_box(0));
v___y_3982_ = v___y_4002_;
v___y_3983_ = v___y_4003_;
v___y_3984_ = v___x_4007_;
goto v___jp_3981_;
}
v___jp_4008_:
{
lean_object* v___x_4013_; lean_object* v___x_4014_; 
v___x_4013_ = lean_box(0);
lean_inc(v_a_3572_);
lean_inc_ref(v_a_3571_);
v___x_4014_ = lean_apply_5(v___y_4011_, v___x_4013_, v___y_4012_, v_a_3571_, v_a_3572_, lean_box(0));
v___y_3982_ = v___y_4009_;
v___y_3983_ = v___y_4010_;
v___y_3984_ = v___x_4014_;
goto v___jp_3981_;
}
v___jp_4015_:
{
lean_object* v___x_4019_; double v___x_4020_; double v___x_4021_; double v___x_4022_; double v___x_4023_; double v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; 
v___x_4019_ = lean_io_mono_nanos_now();
v___x_4020_ = lean_float_of_nat(v___y_4017_);
v___x_4021_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDecl_doAdd___lam__1___closed__1);
v___x_4022_ = lean_float_div(v___x_4020_, v___x_4021_);
v___x_4023_ = lean_float_of_nat(v___x_4019_);
v___x_4024_ = lean_float_div(v___x_4023_, v___x_4021_);
v___x_4025_ = lean_box_float(v___x_4022_);
v___x_4026_ = lean_box_float(v___x_4024_);
v___x_4027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4027_, 0, v___x_4025_);
lean_ctor_set(v___x_4027_, 1, v___x_4026_);
v___x_4028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4028_, 0, v_a_4018_);
lean_ctor_set(v___x_4028_, 1, v___x_4027_);
v___x_4029_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__2(v_cls_3765_, v_hasTrace_3628_, v___x_3966_, v_options_3626_, v___x_3968_, v___y_4016_, v___f_3965_, v___x_4028_, v_a_3571_, v_a_3572_);
return v___x_4029_;
}
v___jp_4030_:
{
if (lean_obj_tag(v___y_4033_) == 0)
{
lean_object* v_a_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4041_; 
v_a_4034_ = lean_ctor_get(v___y_4033_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v___y_4033_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4036_ = v___y_4033_;
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_a_4034_);
lean_dec(v___y_4033_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v___x_4039_; 
if (v_isShared_4037_ == 0)
{
lean_ctor_set_tag(v___x_4036_, 1);
v___x_4039_ = v___x_4036_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_a_4034_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
v___y_4016_ = v___y_4031_;
v___y_4017_ = v___y_4032_;
v_a_4018_ = v___x_4039_;
goto v___jp_4015_;
}
}
}
else
{
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4049_; 
v_a_4042_ = lean_ctor_get(v___y_4033_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___y_4033_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4044_ = v___y_4033_;
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___y_4033_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4047_; 
if (v_isShared_4045_ == 0)
{
lean_ctor_set_tag(v___x_4044_, 0);
v___x_4047_ = v___x_4044_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_a_4042_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
v___y_4016_ = v___y_4031_;
v___y_4017_ = v___y_4032_;
v_a_4018_ = v___x_4047_;
goto v___jp_4015_;
}
}
}
}
v___jp_4050_:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; 
v___x_4055_ = lean_box(0);
lean_inc(v_a_3572_);
lean_inc_ref(v_a_3571_);
v___x_4056_ = lean_apply_5(v___y_4053_, v___x_4055_, v___y_4051_, v_a_3571_, v_a_3572_, lean_box(0));
v___y_4031_ = v___y_4052_;
v___y_4032_ = v___y_4054_;
v___y_4033_ = v___x_4056_;
goto v___jp_4030_;
}
v___jp_4057_:
{
if (v___x_3968_ == 0)
{
lean_object* v___x_4062_; lean_object* v___x_4063_; 
lean_dec_ref(v___y_4058_);
v___x_4062_ = lean_box(0);
lean_inc(v_a_3572_);
lean_inc_ref(v_a_3571_);
v___x_4063_ = lean_apply_4(v___y_4060_, v___x_4062_, v_a_3571_, v_a_3572_, lean_box(0));
v___y_4031_ = v___y_4059_;
v___y_4032_ = v___y_4061_;
v___y_4033_ = v___x_4063_;
goto v___jp_4030_;
}
else
{
lean_object* v_toConstantVal_4064_; lean_object* v_name_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
v_toConstantVal_4064_ = lean_ctor_get(v___y_4058_, 0);
lean_inc_ref(v_toConstantVal_4064_);
lean_dec_ref(v___y_4058_);
v_name_4065_ = lean_ctor_get(v_toConstantVal_4064_, 0);
lean_inc(v_name_4065_);
lean_dec_ref(v_toConstantVal_4064_);
v___x_4066_ = lean_obj_once(&l_Lean_addDecl___closed__3, &l_Lean_addDecl___closed__3_once, _init_l_Lean_addDecl___closed__3);
v___x_4067_ = l_Lean_MessageData_ofName(v_name_4065_);
v___x_4068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4066_);
lean_ctor_set(v___x_4068_, 1, v___x_4067_);
v___x_4069_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_4070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4068_);
lean_ctor_set(v___x_4070_, 1, v___x_4069_);
v___x_4071_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3765_, v___x_4070_, v_a_3571_, v_a_3572_);
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_object* v_a_4072_; lean_object* v___x_4073_; 
v_a_4072_ = lean_ctor_get(v___x_4071_, 0);
lean_inc(v_a_4072_);
lean_dec_ref(v___x_4071_);
lean_inc(v_a_3572_);
lean_inc_ref(v_a_3571_);
v___x_4073_ = lean_apply_4(v___y_4060_, v_a_4072_, v_a_3571_, v_a_3572_, lean_box(0));
v___y_4031_ = v___y_4059_;
v___y_4032_ = v___y_4061_;
v___y_4033_ = v___x_4073_;
goto v___jp_4030_;
}
else
{
lean_dec_ref(v___y_4060_);
v___y_4031_ = v___y_4059_;
v___y_4032_ = v___y_4061_;
v___y_4033_ = v___x_4071_;
goto v___jp_4030_;
}
}
}
v___jp_4074_:
{
lean_object* v___x_4084_; uint8_t v_isModule_4085_; 
v___x_4084_ = l_Lean_Environment_header(v___y_4081_);
lean_dec_ref(v___y_4081_);
v_isModule_4085_ = lean_ctor_get_uint8(v___x_4084_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4084_);
if (v_isModule_4085_ == 0)
{
lean_dec_ref(v___y_4082_);
lean_dec_ref(v___y_4080_);
lean_dec_ref(v___y_4076_);
v___y_4051_ = v___y_4075_;
v___y_4052_ = v___y_4079_;
v___y_4053_ = v___y_4078_;
v___y_4054_ = v___y_4083_;
goto v___jp_4050_;
}
else
{
uint8_t v_isExporting_4086_; 
v_isExporting_4086_ = lean_ctor_get_uint8(v___y_4082_, sizeof(void*)*8);
lean_dec_ref(v___y_4082_);
if (v_isExporting_4086_ == 0)
{
lean_dec_ref(v___y_4078_);
lean_dec(v___y_4075_);
v___y_4058_ = v___y_4076_;
v___y_4059_ = v___y_4079_;
v___y_4060_ = v___y_4080_;
v___y_4061_ = v___y_4083_;
goto v___jp_4057_;
}
else
{
if (v___y_4077_ == 0)
{
lean_dec_ref(v___y_4080_);
lean_dec_ref(v___y_4076_);
v___y_4051_ = v___y_4075_;
v___y_4052_ = v___y_4079_;
v___y_4053_ = v___y_4078_;
v___y_4054_ = v___y_4083_;
goto v___jp_4050_;
}
else
{
lean_dec_ref(v___y_4078_);
lean_dec(v___y_4075_);
v___y_4058_ = v___y_4076_;
v___y_4059_ = v___y_4079_;
v___y_4060_ = v___y_4080_;
v___y_4061_ = v___y_4083_;
goto v___jp_4057_;
}
}
}
}
v___jp_4087_:
{
lean_object* v___x_4092_; lean_object* v___x_4093_; 
v___x_4092_ = lean_box(0);
lean_inc(v_a_3572_);
lean_inc_ref(v_a_3571_);
v___x_4093_ = lean_apply_5(v___y_4090_, v___x_4092_, v___y_4088_, v_a_3571_, v_a_3572_, lean_box(0));
v___y_4031_ = v___y_4089_;
v___y_4032_ = v___y_4091_;
v___y_4033_ = v___x_4093_;
goto v___jp_4030_;
}
v___jp_4094_:
{
lean_object* v___x_4102_; uint8_t v_isModule_4103_; 
v___x_4102_ = l_Lean_Environment_header(v___y_4101_);
lean_dec_ref(v___y_4101_);
v_isModule_4103_ = lean_ctor_get_uint8(v___x_4102_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4102_);
if (v_isModule_4103_ == 0)
{
lean_dec_ref(v___y_4097_);
lean_dec_ref(v___y_4096_);
v___y_4088_ = v___y_4095_;
v___y_4089_ = v___y_4098_;
v___y_4090_ = v___y_4099_;
v___y_4091_ = v___y_4100_;
goto v___jp_4087_;
}
else
{
lean_dec_ref(v___y_4099_);
lean_dec(v___y_4095_);
if (v___x_3968_ == 0)
{
lean_object* v___x_4104_; lean_object* v___x_4105_; 
lean_dec_ref(v___y_4096_);
v___x_4104_ = lean_box(0);
lean_inc(v_a_3572_);
lean_inc_ref(v_a_3571_);
v___x_4105_ = lean_apply_4(v___y_4097_, v___x_4104_, v_a_3571_, v_a_3572_, lean_box(0));
v___y_4031_ = v___y_4098_;
v___y_4032_ = v___y_4100_;
v___y_4033_ = v___x_4105_;
goto v___jp_4030_;
}
else
{
lean_object* v_toConstantVal_4106_; lean_object* v_name_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; 
v_toConstantVal_4106_ = lean_ctor_get(v___y_4096_, 0);
lean_inc_ref(v_toConstantVal_4106_);
lean_dec_ref(v___y_4096_);
v_name_4107_ = lean_ctor_get(v_toConstantVal_4106_, 0);
lean_inc(v_name_4107_);
lean_dec_ref(v_toConstantVal_4106_);
v___x_4108_ = lean_obj_once(&l_Lean_addDecl___closed__5, &l_Lean_addDecl___closed__5_once, _init_l_Lean_addDecl___closed__5);
v___x_4109_ = l_Lean_MessageData_ofName(v_name_4107_);
v___x_4110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4108_);
lean_ctor_set(v___x_4110_, 1, v___x_4109_);
v___x_4111_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_4112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4112_, 0, v___x_4110_);
lean_ctor_set(v___x_4112_, 1, v___x_4111_);
v___x_4113_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3765_, v___x_4112_, v_a_3571_, v_a_3572_);
if (lean_obj_tag(v___x_4113_) == 0)
{
lean_object* v_a_4114_; lean_object* v___x_4115_; 
v_a_4114_ = lean_ctor_get(v___x_4113_, 0);
lean_inc(v_a_4114_);
lean_dec_ref(v___x_4113_);
lean_inc(v_a_3572_);
lean_inc_ref(v_a_3571_);
v___x_4115_ = lean_apply_4(v___y_4097_, v_a_4114_, v_a_3571_, v_a_3572_, lean_box(0));
v___y_4031_ = v___y_4098_;
v___y_4032_ = v___y_4100_;
v___y_4033_ = v___x_4115_;
goto v___jp_4030_;
}
else
{
lean_dec_ref(v___y_4097_);
v___y_4031_ = v___y_4098_;
v___y_4032_ = v___y_4100_;
v___y_4033_ = v___x_4113_;
goto v___jp_4030_;
}
}
}
}
v___jp_4116_:
{
lean_object* v___x_4117_; lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4267_; 
v___x_4117_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDecl_doAdd_spec__1___redArg(v_a_3572_);
v_a_4118_ = lean_ctor_get(v___x_4117_, 0);
v_isSharedCheck_4267_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4120_ = v___x_4117_;
v_isShared_4121_ = v_isSharedCheck_4267_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_a_4118_);
lean_dec(v___x_4117_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4267_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4122_; uint8_t v___x_4123_; 
v___x_4122_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4123_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3626_, v___x_4122_);
if (v___x_4123_ == 0)
{
lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v_env_4126_; lean_object* v_nextMacroScope_4127_; lean_object* v_ngen_4128_; lean_object* v_auxDeclNGen_4129_; lean_object* v_traceState_4130_; lean_object* v_messages_4131_; lean_object* v_infoState_4132_; lean_object* v_snapshotTasks_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4181_; 
v___x_4124_ = lean_io_mono_nanos_now();
v___x_4125_ = lean_st_ref_take(v_a_3572_);
v_env_4126_ = lean_ctor_get(v___x_4125_, 0);
v_nextMacroScope_4127_ = lean_ctor_get(v___x_4125_, 1);
v_ngen_4128_ = lean_ctor_get(v___x_4125_, 2);
v_auxDeclNGen_4129_ = lean_ctor_get(v___x_4125_, 3);
v_traceState_4130_ = lean_ctor_get(v___x_4125_, 4);
v_messages_4131_ = lean_ctor_get(v___x_4125_, 6);
v_infoState_4132_ = lean_ctor_get(v___x_4125_, 7);
v_snapshotTasks_4133_ = lean_ctor_get(v___x_4125_, 8);
v_isSharedCheck_4181_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4181_ == 0)
{
lean_object* v_unused_4182_; 
v_unused_4182_ = lean_ctor_get(v___x_4125_, 5);
lean_dec(v_unused_4182_);
v___x_4135_ = v___x_4125_;
v_isShared_4136_ = v_isSharedCheck_4181_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_snapshotTasks_4133_);
lean_inc(v_infoState_4132_);
lean_inc(v_messages_4131_);
lean_inc(v_traceState_4130_);
lean_inc(v_auxDeclNGen_4129_);
lean_inc(v_ngen_4128_);
lean_inc(v_nextMacroScope_4127_);
lean_inc(v_env_4126_);
lean_dec(v___x_4125_);
v___x_4135_ = lean_box(0);
v_isShared_4136_ = v_isSharedCheck_4181_;
goto v_resetjp_4134_;
}
v_resetjp_4134_:
{
lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4141_; 
lean_inc(v_decl_3569_);
v___x_4137_ = l_Lean_Declaration_getNames(v_decl_3569_);
v___x_4138_ = l_List_foldl___at___00Lean_addDecl_spec__1(v_env_4126_, v___x_4137_);
v___x_4139_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2);
if (v_isShared_4136_ == 0)
{
lean_ctor_set(v___x_4135_, 5, v___x_4139_);
lean_ctor_set(v___x_4135_, 0, v___x_4138_);
v___x_4141_ = v___x_4135_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v___x_4138_);
lean_ctor_set(v_reuseFailAlloc_4180_, 1, v_nextMacroScope_4127_);
lean_ctor_set(v_reuseFailAlloc_4180_, 2, v_ngen_4128_);
lean_ctor_set(v_reuseFailAlloc_4180_, 3, v_auxDeclNGen_4129_);
lean_ctor_set(v_reuseFailAlloc_4180_, 4, v_traceState_4130_);
lean_ctor_set(v_reuseFailAlloc_4180_, 5, v___x_4139_);
lean_ctor_set(v_reuseFailAlloc_4180_, 6, v_messages_4131_);
lean_ctor_set(v_reuseFailAlloc_4180_, 7, v_infoState_4132_);
lean_ctor_set(v_reuseFailAlloc_4180_, 8, v_snapshotTasks_4133_);
v___x_4141_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___f_4146_; 
v___x_4142_ = lean_st_ref_set(v_a_3572_, v___x_4141_);
v___x_4143_ = lean_box(0);
v___x_4144_ = lean_box(v_hasTrace_3628_);
v___x_4145_ = lean_box(v___x_4123_);
lean_inc(v_decl_3569_);
v___f_4146_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__8___boxed), 12, 7);
lean_closure_set(v___f_4146_, 0, v_decl_3569_);
lean_closure_set(v___f_4146_, 1, v___x_3629_);
lean_closure_set(v___f_4146_, 2, v___x_4144_);
lean_closure_set(v___f_4146_, 3, v___x_4145_);
lean_closure_set(v___f_4146_, 4, v___x_4139_);
lean_closure_set(v___f_4146_, 5, v_cls_3765_);
lean_closure_set(v___f_4146_, 6, v___x_4143_);
switch(lean_obj_tag(v_decl_3569_))
{
case 2:
{
lean_object* v_val_4147_; lean_object* v___x_4148_; lean_object* v_env_4149_; lean_object* v___f_4150_; lean_object* v___x_4151_; lean_object* v___f_4152_; 
lean_del_object(v___x_4120_);
v_val_4147_ = lean_ctor_get(v_decl_3569_, 0);
lean_inc_ref_n(v_val_4147_, 3);
lean_dec_ref(v_decl_3569_);
v___x_4148_ = lean_st_ref_get(v_a_3572_);
v_env_4149_ = lean_ctor_get(v___x_4148_, 0);
lean_inc_ref(v_env_4149_);
lean_dec(v___x_4148_);
v___f_4150_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__5___boxed), 7, 2);
lean_closure_set(v___f_4150_, 0, v_val_4147_);
lean_closure_set(v___f_4150_, 1, v___f_4146_);
v___x_4151_ = lean_box(v___x_4123_);
lean_inc_ref(v___f_4150_);
v___f_4152_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__6___boxed), 7, 3);
lean_closure_set(v___f_4152_, 0, v_val_4147_);
lean_closure_set(v___f_4152_, 1, v___x_4151_);
lean_closure_set(v___f_4152_, 2, v___f_4150_);
if (v_forceExpose_3570_ == 0)
{
v___y_4095_ = v___x_4143_;
v___y_4096_ = v_val_4147_;
v___y_4097_ = v___f_4152_;
v___y_4098_ = v_a_4118_;
v___y_4099_ = v___f_4150_;
v___y_4100_ = v___x_4124_;
v___y_4101_ = v_env_4149_;
goto v___jp_4094_;
}
else
{
if (v___x_4123_ == 0)
{
lean_dec_ref(v___f_4152_);
lean_dec_ref(v_env_4149_);
lean_dec_ref(v_val_4147_);
v___y_4088_ = v___x_4143_;
v___y_4089_ = v_a_4118_;
v___y_4090_ = v___f_4150_;
v___y_4091_ = v___x_4124_;
goto v___jp_4087_;
}
else
{
v___y_4095_ = v___x_4143_;
v___y_4096_ = v_val_4147_;
v___y_4097_ = v___f_4152_;
v___y_4098_ = v_a_4118_;
v___y_4099_ = v___f_4150_;
v___y_4100_ = v___x_4124_;
v___y_4101_ = v_env_4149_;
goto v___jp_4094_;
}
}
}
case 1:
{
lean_object* v_val_4153_; lean_object* v___x_4154_; 
lean_del_object(v___x_4120_);
v_val_4153_ = lean_ctor_get(v_decl_3569_, 0);
lean_inc_ref(v_val_4153_);
lean_dec_ref(v_decl_3569_);
v___x_4154_ = l_Lean_addDecl___lam__4(v___f_4146_, v_cls_3765_, v___x_4143_, v___x_4123_, v_forceExpose_3570_, v_val_4153_, v_a_3571_, v_a_3572_);
v___y_4031_ = v_a_4118_;
v___y_4032_ = v___x_4124_;
v___y_4033_ = v___x_4154_;
goto v___jp_4030_;
}
case 5:
{
lean_object* v_defns_4155_; 
lean_del_object(v___x_4120_);
v_defns_4155_ = lean_ctor_get(v_decl_3569_, 0);
if (lean_obj_tag(v_defns_4155_) == 1)
{
lean_object* v_tail_4156_; 
v_tail_4156_ = lean_ctor_get(v_defns_4155_, 1);
if (lean_obj_tag(v_tail_4156_) == 0)
{
lean_object* v_head_4157_; lean_object* v___x_4158_; 
lean_inc_ref(v_defns_4155_);
lean_dec_ref(v_decl_3569_);
v_head_4157_ = lean_ctor_get(v_defns_4155_, 0);
lean_inc(v_head_4157_);
lean_dec_ref(v_defns_4155_);
v___x_4158_ = l_Lean_addDecl___lam__4(v___f_4146_, v_cls_3765_, v___x_4143_, v___x_4123_, v_forceExpose_3570_, v_head_4157_, v_a_3571_, v_a_3572_);
v___y_4031_ = v_a_4118_;
v___y_4032_ = v___x_4124_;
v___y_4033_ = v___x_4158_;
goto v___jp_4030_;
}
else
{
lean_object* v___x_4159_; 
lean_dec_ref(v___f_4146_);
lean_inc_ref(v_decl_3569_);
v___x_4159_ = l_Lean_addDecl___lam__3(v_decl_3569_, v_cls_3765_, v_decl_3569_, v_a_3571_, v_a_3572_);
lean_dec_ref(v_decl_3569_);
v___y_4031_ = v_a_4118_;
v___y_4032_ = v___x_4124_;
v___y_4033_ = v___x_4159_;
goto v___jp_4030_;
}
}
else
{
lean_object* v___x_4160_; 
lean_dec_ref(v___f_4146_);
lean_inc_ref(v_decl_3569_);
v___x_4160_ = l_Lean_addDecl___lam__3(v_decl_3569_, v_cls_3765_, v_decl_3569_, v_a_3571_, v_a_3572_);
lean_dec_ref(v_decl_3569_);
v___y_4031_ = v_a_4118_;
v___y_4032_ = v___x_4124_;
v___y_4033_ = v___x_4160_;
goto v___jp_4030_;
}
}
case 3:
{
lean_object* v_val_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v_env_4164_; lean_object* v_env_4165_; lean_object* v___f_4166_; lean_object* v___f_4167_; 
lean_del_object(v___x_4120_);
v_val_4161_ = lean_ctor_get(v_decl_3569_, 0);
lean_inc_ref_n(v_val_4161_, 3);
lean_dec_ref(v_decl_3569_);
v___x_4162_ = lean_st_ref_get(v_a_3572_);
v___x_4163_ = lean_st_ref_get(v_a_3572_);
v_env_4164_ = lean_ctor_get(v___x_4162_, 0);
lean_inc_ref(v_env_4164_);
lean_dec(v___x_4162_);
v_env_4165_ = lean_ctor_get(v___x_4163_, 0);
lean_inc_ref(v_env_4165_);
lean_dec(v___x_4163_);
v___f_4166_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__7___boxed), 7, 2);
lean_closure_set(v___f_4166_, 0, v_val_4161_);
lean_closure_set(v___f_4166_, 1, v___f_4146_);
lean_inc_ref(v___f_4166_);
v___f_4167_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__9___boxed), 6, 2);
lean_closure_set(v___f_4167_, 0, v_val_4161_);
lean_closure_set(v___f_4167_, 1, v___f_4166_);
if (v_forceExpose_3570_ == 0)
{
v___y_4075_ = v___x_4143_;
v___y_4076_ = v_val_4161_;
v___y_4077_ = v___x_4123_;
v___y_4078_ = v___f_4166_;
v___y_4079_ = v_a_4118_;
v___y_4080_ = v___f_4167_;
v___y_4081_ = v_env_4164_;
v___y_4082_ = v_env_4165_;
v___y_4083_ = v___x_4124_;
goto v___jp_4074_;
}
else
{
if (v___x_4123_ == 0)
{
lean_dec_ref(v___f_4167_);
lean_dec_ref(v_env_4165_);
lean_dec_ref(v_env_4164_);
lean_dec_ref(v_val_4161_);
v___y_4051_ = v___x_4143_;
v___y_4052_ = v_a_4118_;
v___y_4053_ = v___f_4166_;
v___y_4054_ = v___x_4124_;
goto v___jp_4050_;
}
else
{
v___y_4075_ = v___x_4143_;
v___y_4076_ = v_val_4161_;
v___y_4077_ = v___x_4123_;
v___y_4078_ = v___f_4166_;
v___y_4079_ = v_a_4118_;
v___y_4080_ = v___f_4167_;
v___y_4081_ = v_env_4164_;
v___y_4082_ = v_env_4165_;
v___y_4083_ = v___x_4124_;
goto v___jp_4074_;
}
}
}
case 0:
{
lean_object* v_val_4168_; lean_object* v_toConstantVal_4169_; lean_object* v_name_4170_; lean_object* v___x_4172_; 
lean_dec_ref(v___f_4146_);
v_val_4168_ = lean_ctor_get(v_decl_3569_, 0);
v_toConstantVal_4169_ = lean_ctor_get(v_val_4168_, 0);
v_name_4170_ = lean_ctor_get(v_toConstantVal_4169_, 0);
lean_inc_ref(v_val_4168_);
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 0, v_val_4168_);
v___x_4172_ = v___x_4120_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v_val_4168_);
v___x_4172_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
uint8_t v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; 
v___x_4173_ = 2;
v___x_4174_ = lean_box(v___x_4173_);
v___x_4175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4172_);
lean_ctor_set(v___x_4175_, 1, v___x_4174_);
lean_inc(v_name_4170_);
v___x_4176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4176_, 0, v_name_4170_);
lean_ctor_set(v___x_4176_, 1, v___x_4175_);
v___x_4177_ = l_Lean_addDecl___lam__8(v_decl_3569_, v___x_3629_, v_hasTrace_3628_, v___x_4123_, v___x_4139_, v_cls_3765_, v___x_4143_, v___x_4176_, v___x_4143_, v_a_3571_, v_a_3572_);
v___y_4031_ = v_a_4118_;
v___y_4032_ = v___x_4124_;
v___y_4033_ = v___x_4177_;
goto v___jp_4030_;
}
}
default: 
{
lean_object* v___x_4179_; 
lean_dec_ref(v___f_4146_);
lean_del_object(v___x_4120_);
lean_inc(v_decl_3569_);
v___x_4179_ = l_Lean_addDecl___lam__3(v_decl_3569_, v_cls_3765_, v_decl_3569_, v_a_3571_, v_a_3572_);
lean_dec(v_decl_3569_);
v___y_4031_ = v_a_4118_;
v___y_4032_ = v___x_4124_;
v___y_4033_ = v___x_4179_;
goto v___jp_4030_;
}
}
}
}
}
else
{
lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v_env_4185_; lean_object* v_nextMacroScope_4186_; lean_object* v_ngen_4187_; lean_object* v_auxDeclNGen_4188_; lean_object* v_traceState_4189_; lean_object* v_messages_4190_; lean_object* v_infoState_4191_; lean_object* v_snapshotTasks_4192_; lean_object* v___x_4194_; uint8_t v_isShared_4195_; uint8_t v_isSharedCheck_4265_; 
v___x_4183_ = lean_io_get_num_heartbeats();
v___x_4184_ = lean_st_ref_take(v_a_3572_);
v_env_4185_ = lean_ctor_get(v___x_4184_, 0);
v_nextMacroScope_4186_ = lean_ctor_get(v___x_4184_, 1);
v_ngen_4187_ = lean_ctor_get(v___x_4184_, 2);
v_auxDeclNGen_4188_ = lean_ctor_get(v___x_4184_, 3);
v_traceState_4189_ = lean_ctor_get(v___x_4184_, 4);
v_messages_4190_ = lean_ctor_get(v___x_4184_, 6);
v_infoState_4191_ = lean_ctor_get(v___x_4184_, 7);
v_snapshotTasks_4192_ = lean_ctor_get(v___x_4184_, 8);
v_isSharedCheck_4265_ = !lean_is_exclusive(v___x_4184_);
if (v_isSharedCheck_4265_ == 0)
{
lean_object* v_unused_4266_; 
v_unused_4266_ = lean_ctor_get(v___x_4184_, 5);
lean_dec(v_unused_4266_);
v___x_4194_ = v___x_4184_;
v_isShared_4195_ = v_isSharedCheck_4265_;
goto v_resetjp_4193_;
}
else
{
lean_inc(v_snapshotTasks_4192_);
lean_inc(v_infoState_4191_);
lean_inc(v_messages_4190_);
lean_inc(v_traceState_4189_);
lean_inc(v_auxDeclNGen_4188_);
lean_inc(v_ngen_4187_);
lean_inc(v_nextMacroScope_4186_);
lean_inc(v_env_4185_);
lean_dec(v___x_4184_);
v___x_4194_ = lean_box(0);
v_isShared_4195_ = v_isSharedCheck_4265_;
goto v_resetjp_4193_;
}
v_resetjp_4193_:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4200_; 
lean_inc(v_decl_3569_);
v___x_4196_ = l_Lean_Declaration_getNames(v_decl_3569_);
v___x_4197_ = l_List_foldl___at___00Lean_addDecl_spec__1(v_env_4185_, v___x_4196_);
v___x_4198_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2);
if (v_isShared_4195_ == 0)
{
lean_ctor_set(v___x_4194_, 5, v___x_4198_);
lean_ctor_set(v___x_4194_, 0, v___x_4197_);
v___x_4200_ = v___x_4194_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v___x_4197_);
lean_ctor_set(v_reuseFailAlloc_4264_, 1, v_nextMacroScope_4186_);
lean_ctor_set(v_reuseFailAlloc_4264_, 2, v_ngen_4187_);
lean_ctor_set(v_reuseFailAlloc_4264_, 3, v_auxDeclNGen_4188_);
lean_ctor_set(v_reuseFailAlloc_4264_, 4, v_traceState_4189_);
lean_ctor_set(v_reuseFailAlloc_4264_, 5, v___x_4198_);
lean_ctor_set(v_reuseFailAlloc_4264_, 6, v_messages_4190_);
lean_ctor_set(v_reuseFailAlloc_4264_, 7, v_infoState_4191_);
lean_ctor_set(v_reuseFailAlloc_4264_, 8, v_snapshotTasks_4192_);
v___x_4200_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___f_4204_; 
v___x_4201_ = lean_st_ref_set(v_a_3572_, v___x_4200_);
v___x_4202_ = lean_box(0);
v___x_4203_ = lean_box(v___x_4123_);
lean_inc(v_decl_3569_);
v___f_4204_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__13___boxed), 11, 6);
lean_closure_set(v___f_4204_, 0, v_decl_3569_);
lean_closure_set(v___f_4204_, 1, v___x_3629_);
lean_closure_set(v___f_4204_, 2, v___x_4203_);
lean_closure_set(v___f_4204_, 3, v_cls_3765_);
lean_closure_set(v___f_4204_, 4, v___x_4198_);
lean_closure_set(v___f_4204_, 5, v___x_4202_);
switch(lean_obj_tag(v_decl_3569_))
{
case 2:
{
lean_object* v_val_4205_; lean_object* v___x_4206_; lean_object* v_env_4207_; lean_object* v___f_4208_; 
lean_del_object(v___x_4120_);
v_val_4205_ = lean_ctor_get(v_decl_3569_, 0);
lean_inc_ref_n(v_val_4205_, 2);
lean_dec_ref(v_decl_3569_);
v___x_4206_ = lean_st_ref_get(v_a_3572_);
v_env_4207_ = lean_ctor_get(v___x_4206_, 0);
lean_inc_ref(v_env_4207_);
lean_dec(v___x_4206_);
v___f_4208_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__5___boxed), 7, 2);
lean_closure_set(v___f_4208_, 0, v_val_4205_);
lean_closure_set(v___f_4208_, 1, v___f_4204_);
if (v_forceExpose_3570_ == 0)
{
if (v___x_4123_ == 0)
{
lean_dec_ref(v_env_4207_);
lean_dec_ref(v_val_4205_);
v___y_4002_ = v___x_4183_;
v___y_4003_ = v_a_4118_;
v___y_4004_ = v___x_4202_;
v___y_4005_ = v___f_4208_;
goto v___jp_4001_;
}
else
{
lean_object* v___x_4209_; uint8_t v_isModule_4210_; 
v___x_4209_ = l_Lean_Environment_header(v_env_4207_);
lean_dec_ref(v_env_4207_);
v_isModule_4210_ = lean_ctor_get_uint8(v___x_4209_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4209_);
if (v_isModule_4210_ == 0)
{
lean_dec_ref(v_val_4205_);
v___y_4002_ = v___x_4183_;
v___y_4003_ = v_a_4118_;
v___y_4004_ = v___x_4202_;
v___y_4005_ = v___f_4208_;
goto v___jp_4001_;
}
else
{
if (v___x_3968_ == 0)
{
lean_object* v___x_4211_; lean_object* v___x_4212_; 
v___x_4211_ = lean_box(0);
v___x_4212_ = l_Lean_addDecl___lam__12(v_val_4205_, v_forceExpose_3570_, v___f_4208_, v___x_4211_, v_a_3571_, v_a_3572_);
lean_dec_ref(v_val_4205_);
v___y_3982_ = v___x_4183_;
v___y_3983_ = v_a_4118_;
v___y_3984_ = v___x_4212_;
goto v___jp_3981_;
}
else
{
lean_object* v_toConstantVal_4213_; lean_object* v_name_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; 
v_toConstantVal_4213_ = lean_ctor_get(v_val_4205_, 0);
v_name_4214_ = lean_ctor_get(v_toConstantVal_4213_, 0);
v___x_4215_ = lean_obj_once(&l_Lean_addDecl___closed__5, &l_Lean_addDecl___closed__5_once, _init_l_Lean_addDecl___closed__5);
lean_inc(v_name_4214_);
v___x_4216_ = l_Lean_MessageData_ofName(v_name_4214_);
v___x_4217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4217_, 0, v___x_4215_);
lean_ctor_set(v___x_4217_, 1, v___x_4216_);
v___x_4218_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_4219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4219_, 0, v___x_4217_);
lean_ctor_set(v___x_4219_, 1, v___x_4218_);
v___x_4220_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3765_, v___x_4219_, v_a_3571_, v_a_3572_);
if (lean_obj_tag(v___x_4220_) == 0)
{
lean_object* v_a_4221_; lean_object* v___x_4222_; 
v_a_4221_ = lean_ctor_get(v___x_4220_, 0);
lean_inc(v_a_4221_);
lean_dec_ref(v___x_4220_);
v___x_4222_ = l_Lean_addDecl___lam__12(v_val_4205_, v_forceExpose_3570_, v___f_4208_, v_a_4221_, v_a_3571_, v_a_3572_);
lean_dec_ref(v_val_4205_);
v___y_3982_ = v___x_4183_;
v___y_3983_ = v_a_4118_;
v___y_3984_ = v___x_4222_;
goto v___jp_3981_;
}
else
{
lean_dec_ref(v___f_4208_);
lean_dec_ref(v_val_4205_);
v___y_3982_ = v___x_4183_;
v___y_3983_ = v_a_4118_;
v___y_3984_ = v___x_4220_;
goto v___jp_3981_;
}
}
}
}
}
else
{
lean_dec_ref(v_env_4207_);
lean_dec_ref(v_val_4205_);
v___y_4002_ = v___x_4183_;
v___y_4003_ = v_a_4118_;
v___y_4004_ = v___x_4202_;
v___y_4005_ = v___f_4208_;
goto v___jp_4001_;
}
}
case 1:
{
lean_object* v_val_4223_; lean_object* v___x_4224_; 
lean_del_object(v___x_4120_);
v_val_4223_ = lean_ctor_get(v_decl_3569_, 0);
lean_inc_ref(v_val_4223_);
lean_dec_ref(v_decl_3569_);
v___x_4224_ = l_Lean_addDecl___lam__10(v___f_4204_, v_forceExpose_3570_, v___x_4123_, v___x_4202_, v_cls_3765_, v_val_4223_, v_a_3571_, v_a_3572_);
v___y_3982_ = v___x_4183_;
v___y_3983_ = v_a_4118_;
v___y_3984_ = v___x_4224_;
goto v___jp_3981_;
}
case 5:
{
lean_object* v_defns_4225_; 
lean_del_object(v___x_4120_);
v_defns_4225_ = lean_ctor_get(v_decl_3569_, 0);
if (lean_obj_tag(v_defns_4225_) == 1)
{
lean_object* v_tail_4226_; 
v_tail_4226_ = lean_ctor_get(v_defns_4225_, 1);
if (lean_obj_tag(v_tail_4226_) == 0)
{
lean_object* v_head_4227_; lean_object* v___x_4228_; 
lean_inc_ref(v_defns_4225_);
lean_dec_ref(v_decl_3569_);
v_head_4227_ = lean_ctor_get(v_defns_4225_, 0);
lean_inc(v_head_4227_);
lean_dec_ref(v_defns_4225_);
v___x_4228_ = l_Lean_addDecl___lam__10(v___f_4204_, v_forceExpose_3570_, v___x_4123_, v___x_4202_, v_cls_3765_, v_head_4227_, v_a_3571_, v_a_3572_);
v___y_3982_ = v___x_4183_;
v___y_3983_ = v_a_4118_;
v___y_3984_ = v___x_4228_;
goto v___jp_3981_;
}
else
{
lean_object* v___x_4229_; 
lean_dec_ref(v___f_4204_);
lean_inc_ref(v_decl_3569_);
v___x_4229_ = l_Lean_addDecl___lam__3(v_decl_3569_, v_cls_3765_, v_decl_3569_, v_a_3571_, v_a_3572_);
lean_dec_ref(v_decl_3569_);
v___y_3982_ = v___x_4183_;
v___y_3983_ = v_a_4118_;
v___y_3984_ = v___x_4229_;
goto v___jp_3981_;
}
}
else
{
lean_object* v___x_4230_; 
lean_dec_ref(v___f_4204_);
lean_inc_ref(v_decl_3569_);
v___x_4230_ = l_Lean_addDecl___lam__3(v_decl_3569_, v_cls_3765_, v_decl_3569_, v_a_3571_, v_a_3572_);
lean_dec_ref(v_decl_3569_);
v___y_3982_ = v___x_4183_;
v___y_3983_ = v_a_4118_;
v___y_3984_ = v___x_4230_;
goto v___jp_3981_;
}
}
case 3:
{
lean_object* v_val_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v_env_4234_; lean_object* v_env_4235_; lean_object* v___f_4236_; 
lean_del_object(v___x_4120_);
v_val_4231_ = lean_ctor_get(v_decl_3569_, 0);
lean_inc_ref_n(v_val_4231_, 2);
lean_dec_ref(v_decl_3569_);
v___x_4232_ = lean_st_ref_get(v_a_3572_);
v___x_4233_ = lean_st_ref_get(v_a_3572_);
v_env_4234_ = lean_ctor_get(v___x_4232_, 0);
lean_inc_ref(v_env_4234_);
lean_dec(v___x_4232_);
v_env_4235_ = lean_ctor_get(v___x_4233_, 0);
lean_inc_ref(v_env_4235_);
lean_dec(v___x_4233_);
v___f_4236_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__7___boxed), 7, 2);
lean_closure_set(v___f_4236_, 0, v_val_4231_);
lean_closure_set(v___f_4236_, 1, v___f_4204_);
if (v_forceExpose_3570_ == 0)
{
if (v___x_4123_ == 0)
{
lean_dec_ref(v_env_4235_);
lean_dec_ref(v_env_4234_);
lean_dec_ref(v_val_4231_);
v___y_4009_ = v___x_4183_;
v___y_4010_ = v_a_4118_;
v___y_4011_ = v___f_4236_;
v___y_4012_ = v___x_4202_;
goto v___jp_4008_;
}
else
{
lean_object* v___x_4237_; uint8_t v_isModule_4238_; 
v___x_4237_ = l_Lean_Environment_header(v_env_4234_);
lean_dec_ref(v_env_4234_);
v_isModule_4238_ = lean_ctor_get_uint8(v___x_4237_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4237_);
if (v_isModule_4238_ == 0)
{
lean_dec_ref(v_env_4235_);
lean_dec_ref(v_val_4231_);
v___y_4009_ = v___x_4183_;
v___y_4010_ = v_a_4118_;
v___y_4011_ = v___f_4236_;
v___y_4012_ = v___x_4202_;
goto v___jp_4008_;
}
else
{
uint8_t v_isExporting_4239_; 
v_isExporting_4239_ = lean_ctor_get_uint8(v_env_4235_, sizeof(void*)*8);
lean_dec_ref(v_env_4235_);
if (v_isExporting_4239_ == 0)
{
if (v___x_3968_ == 0)
{
lean_object* v___x_4240_; lean_object* v___x_4241_; 
v___x_4240_ = lean_box(0);
v___x_4241_ = l_Lean_addDecl___lam__9(v_val_4231_, v___f_4236_, v___x_4240_, v_a_3571_, v_a_3572_);
lean_dec_ref(v_val_4231_);
v___y_3982_ = v___x_4183_;
v___y_3983_ = v_a_4118_;
v___y_3984_ = v___x_4241_;
goto v___jp_3981_;
}
else
{
lean_object* v_toConstantVal_4242_; lean_object* v_name_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; 
v_toConstantVal_4242_ = lean_ctor_get(v_val_4231_, 0);
v_name_4243_ = lean_ctor_get(v_toConstantVal_4242_, 0);
v___x_4244_ = lean_obj_once(&l_Lean_addDecl___closed__3, &l_Lean_addDecl___closed__3_once, _init_l_Lean_addDecl___closed__3);
lean_inc(v_name_4243_);
v___x_4245_ = l_Lean_MessageData_ofName(v_name_4243_);
v___x_4246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4244_);
lean_ctor_set(v___x_4246_, 1, v___x_4245_);
v___x_4247_ = lean_obj_once(&l_Lean_addDecl___lam__4___closed__3, &l_Lean_addDecl___lam__4___closed__3_once, _init_l_Lean_addDecl___lam__4___closed__3);
v___x_4248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4246_);
lean_ctor_set(v___x_4248_, 1, v___x_4247_);
v___x_4249_ = l_Lean_addTrace___at___00Lean_addDecl_spec__0(v_cls_3765_, v___x_4248_, v_a_3571_, v_a_3572_);
if (lean_obj_tag(v___x_4249_) == 0)
{
lean_object* v_a_4250_; lean_object* v___x_4251_; 
v_a_4250_ = lean_ctor_get(v___x_4249_, 0);
lean_inc(v_a_4250_);
lean_dec_ref(v___x_4249_);
v___x_4251_ = l_Lean_addDecl___lam__9(v_val_4231_, v___f_4236_, v_a_4250_, v_a_3571_, v_a_3572_);
lean_dec_ref(v_val_4231_);
v___y_3982_ = v___x_4183_;
v___y_3983_ = v_a_4118_;
v___y_3984_ = v___x_4251_;
goto v___jp_3981_;
}
else
{
lean_dec_ref(v___f_4236_);
lean_dec_ref(v_val_4231_);
v___y_3982_ = v___x_4183_;
v___y_3983_ = v_a_4118_;
v___y_3984_ = v___x_4249_;
goto v___jp_3981_;
}
}
}
else
{
lean_dec_ref(v_val_4231_);
v___y_4009_ = v___x_4183_;
v___y_4010_ = v_a_4118_;
v___y_4011_ = v___f_4236_;
v___y_4012_ = v___x_4202_;
goto v___jp_4008_;
}
}
}
}
else
{
lean_dec_ref(v_env_4235_);
lean_dec_ref(v_env_4234_);
lean_dec_ref(v_val_4231_);
v___y_4009_ = v___x_4183_;
v___y_4010_ = v_a_4118_;
v___y_4011_ = v___f_4236_;
v___y_4012_ = v___x_4202_;
goto v___jp_4008_;
}
}
case 0:
{
lean_object* v_val_4252_; lean_object* v_toConstantVal_4253_; lean_object* v_name_4254_; lean_object* v___x_4256_; 
lean_dec_ref(v___f_4204_);
v_val_4252_ = lean_ctor_get(v_decl_3569_, 0);
v_toConstantVal_4253_ = lean_ctor_get(v_val_4252_, 0);
v_name_4254_ = lean_ctor_get(v_toConstantVal_4253_, 0);
lean_inc_ref(v_val_4252_);
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 0, v_val_4252_);
v___x_4256_ = v___x_4120_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_val_4252_);
v___x_4256_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
uint8_t v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; 
v___x_4257_ = 2;
v___x_4258_ = lean_box(v___x_4257_);
v___x_4259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4259_, 0, v___x_4256_);
lean_ctor_set(v___x_4259_, 1, v___x_4258_);
lean_inc(v_name_4254_);
v___x_4260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4260_, 0, v_name_4254_);
lean_ctor_set(v___x_4260_, 1, v___x_4259_);
v___x_4261_ = l_Lean_addDecl___lam__13(v_decl_3569_, v___x_3629_, v___x_4123_, v_cls_3765_, v___x_4198_, v___x_4202_, v___x_4260_, v___x_4202_, v_a_3571_, v_a_3572_);
v___y_3982_ = v___x_4183_;
v___y_3983_ = v_a_4118_;
v___y_3984_ = v___x_4261_;
goto v___jp_3981_;
}
}
default: 
{
lean_object* v___x_4263_; 
lean_dec_ref(v___f_4204_);
lean_del_object(v___x_4120_);
lean_inc(v_decl_3569_);
v___x_4263_ = l_Lean_addDecl___lam__3(v_decl_3569_, v_cls_3765_, v_decl_3569_, v_a_3571_, v_a_3572_);
lean_dec(v_decl_3569_);
v___y_3982_ = v___x_4183_;
v___y_3983_ = v_a_4118_;
v___y_3984_ = v___x_4263_;
goto v___jp_3981_;
}
}
}
}
}
}
}
}
v___jp_3574_:
{
lean_object* v___x_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3585_; 
v___x_3578_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3576_, v___y_3575_);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3578_);
if (v_isSharedCheck_3585_ == 0)
{
lean_object* v_unused_3586_; 
v_unused_3586_ = lean_ctor_get(v___x_3578_, 0);
lean_dec(v_unused_3586_);
v___x_3580_ = v___x_3578_;
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
else
{
lean_dec(v___x_3578_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3583_; 
if (v_isShared_3581_ == 0)
{
lean_ctor_set_tag(v___x_3580_, 1);
lean_ctor_set(v___x_3580_, 0, v_a_3577_);
v___x_3583_ = v___x_3580_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_a_3577_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
v___jp_3587_:
{
lean_object* v___x_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3598_; 
v___x_3591_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3589_, v___y_3588_);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3598_ == 0)
{
lean_object* v_unused_3599_; 
v_unused_3599_ = lean_ctor_get(v___x_3591_, 0);
lean_dec(v_unused_3599_);
v___x_3593_ = v___x_3591_;
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
else
{
lean_dec(v___x_3591_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3596_; 
if (v_isShared_3594_ == 0)
{
lean_ctor_set(v___x_3593_, 0, v_a_3590_);
v___x_3596_ = v___x_3593_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_a_3590_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
v___jp_3600_:
{
lean_object* v___x_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3611_; 
v___x_3604_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3601_, v___y_3602_);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3611_ == 0)
{
lean_object* v_unused_3612_; 
v_unused_3612_ = lean_ctor_get(v___x_3604_, 0);
lean_dec(v_unused_3612_);
v___x_3606_ = v___x_3604_;
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
else
{
lean_dec(v___x_3604_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3609_; 
if (v_isShared_3607_ == 0)
{
lean_ctor_set(v___x_3606_, 0, v_a_3603_);
v___x_3609_ = v___x_3606_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_a_3603_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
v___jp_3613_:
{
lean_object* v___x_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
v___x_3617_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3614_, v___y_3615_);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3624_ == 0)
{
lean_object* v_unused_3625_; 
v_unused_3625_ = lean_ctor_get(v___x_3617_, 0);
lean_dec(v_unused_3625_);
v___x_3619_ = v___x_3617_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_dec(v___x_3617_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
lean_ctor_set_tag(v___x_3619_, 1);
lean_ctor_set(v___x_3619_, 0, v_a_3616_);
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3616_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
v___jp_3630_:
{
lean_object* v___x_3642_; 
lean_inc_ref(v___y_3640_);
v___x_3642_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3636_, v___y_3640_, v___y_3634_, v___y_3641_);
if (lean_obj_tag(v___x_3642_) == 0)
{
lean_object* v___x_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3689_; 
lean_dec_ref(v___x_3642_);
lean_inc_ref(v___y_3633_);
v___x_3643_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3633_, v___y_3638_);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3689_ == 0)
{
lean_object* v_unused_3690_; 
v_unused_3690_ = lean_ctor_get(v___x_3643_, 0);
lean_dec(v_unused_3690_);
v___x_3645_ = v___x_3643_;
v_isShared_3646_ = v_isSharedCheck_3689_;
goto v_resetjp_3644_;
}
else
{
lean_dec(v___x_3643_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3689_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v_options_3647_; lean_object* v___x_3648_; uint8_t v___x_3649_; 
v_options_3647_ = lean_ctor_get(v___y_3635_, 2);
v___x_3648_ = l_Lean_Elab_async;
v___x_3649_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3647_, v___x_3648_);
if (v___x_3649_ == 0)
{
lean_object* v___x_3650_; lean_object* v_r_3651_; 
lean_del_object(v___x_3645_);
lean_dec_ref(v___y_3637_);
lean_dec_ref(v___y_3631_);
v___x_3650_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg(v___y_3640_, v___y_3638_);
lean_dec_ref(v___x_3650_);
v_r_3651_ = l___private_Lean_AddDecl_0__Lean_addDecl_doAdd(v_decl_3569_, v___y_3635_, v___y_3638_);
if (lean_obj_tag(v_r_3651_) == 0)
{
lean_object* v_a_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3661_; 
v_a_3652_ = lean_ctor_get(v_r_3651_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v_r_3651_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3654_ = v_r_3651_;
v_isShared_3655_ = v_isSharedCheck_3661_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_a_3652_);
lean_dec(v_r_3651_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3661_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3657_; 
lean_inc(v_a_3652_);
if (v_isShared_3655_ == 0)
{
lean_ctor_set_tag(v___x_3654_, 1);
v___x_3657_ = v___x_3654_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_a_3652_);
v___x_3657_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
lean_object* v___x_3658_; 
v___x_3658_ = lean_apply_2(v___y_3639_, v___x_3657_, lean_box(0));
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_dec_ref(v___x_3658_);
v___y_3601_ = v___y_3633_;
v___y_3602_ = v___y_3638_;
v_a_3603_ = v_a_3652_;
goto v___jp_3600_;
}
else
{
lean_object* v_a_3659_; 
lean_dec(v_a_3652_);
v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
lean_inc(v_a_3659_);
lean_dec_ref(v___x_3658_);
v___y_3614_ = v___y_3633_;
v___y_3615_ = v___y_3638_;
v_a_3616_ = v_a_3659_;
goto v___jp_3613_;
}
}
}
}
else
{
lean_object* v_a_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v_a_3662_ = lean_ctor_get(v_r_3651_, 0);
lean_inc(v_a_3662_);
lean_dec_ref(v_r_3651_);
v___x_3663_ = lean_box(0);
v___x_3664_ = lean_apply_2(v___y_3639_, v___x_3663_, lean_box(0));
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_dec_ref(v___x_3664_);
v___y_3614_ = v___y_3633_;
v___y_3615_ = v___y_3638_;
v_a_3616_ = v_a_3662_;
goto v___jp_3613_;
}
else
{
lean_object* v_a_3665_; 
lean_dec(v_a_3662_);
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
lean_inc(v_a_3665_);
lean_dec_ref(v___x_3664_);
v___y_3614_ = v___y_3633_;
v___y_3615_ = v___y_3638_;
v_a_3616_ = v_a_3665_;
goto v___jp_3613_;
}
}
}
else
{
lean_object* v___x_3666_; lean_object* v___x_3668_; 
lean_dec_ref(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec_ref(v___y_3633_);
lean_dec(v_decl_3569_);
v___x_3666_ = l_IO_CancelToken_new();
if (v_isShared_3646_ == 0)
{
lean_ctor_set_tag(v___x_3645_, 1);
lean_ctor_set(v___x_3645_, 0, v___x_3666_);
v___x_3668_ = v___x_3645_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3666_);
v___x_3668_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3669_ = ((lean_object*)(l_Lean_addDecl___closed__0));
v___x_3670_ = l_Lean_Name_toString(v___x_3669_, v___y_3632_);
lean_inc_ref(v___x_3668_);
v___x_3671_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3631_, v___x_3668_, v___x_3670_, v___y_3635_, v___y_3638_);
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_object* v_a_3672_; lean_object* v_checked_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; 
v_a_3672_ = lean_ctor_get(v___x_3671_, 0);
lean_inc(v_a_3672_);
lean_dec_ref(v___x_3671_);
v_checked_3673_ = lean_ctor_get(v___y_3637_, 2);
lean_inc_ref(v_checked_3673_);
lean_dec_ref(v___y_3637_);
v___x_3674_ = lean_unsigned_to_nat(0u);
v___x_3675_ = lean_io_map_task(v_a_3672_, v_checked_3673_, v___x_3674_, v_hasTrace_3628_);
v___x_3676_ = lean_box(0);
v___x_3677_ = lean_box(2);
v___x_3678_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3678_, 0, v___x_3676_);
lean_ctor_set(v___x_3678_, 1, v___x_3677_);
lean_ctor_set(v___x_3678_, 2, v___x_3668_);
lean_ctor_set(v___x_3678_, 3, v___x_3675_);
v___x_3679_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3678_, v___y_3638_);
return v___x_3679_;
}
else
{
lean_object* v_a_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3687_; 
lean_dec_ref(v___x_3668_);
lean_dec_ref(v___y_3637_);
v_a_3680_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3682_ = v___x_3671_;
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_a_3680_);
lean_dec(v___x_3671_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3685_; 
if (v_isShared_3683_ == 0)
{
v___x_3685_ = v___x_3682_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3680_);
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
}
}
else
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3703_; 
lean_dec_ref(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec_ref(v___y_3637_);
lean_dec_ref(v___y_3633_);
lean_dec_ref(v___y_3631_);
lean_dec(v_decl_3569_);
v_a_3691_ = lean_ctor_get(v___x_3642_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3693_ = v___x_3642_;
v_isShared_3694_ = v_isSharedCheck_3703_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3642_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3703_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v_ref_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3701_; 
v_ref_3695_ = lean_ctor_get(v___y_3635_, 5);
v___x_3696_ = lean_io_error_to_string(v_a_3691_);
v___x_3697_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3696_);
v___x_3698_ = l_Lean_MessageData_ofFormat(v___x_3697_);
lean_inc(v_ref_3695_);
v___x_3699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3699_, 0, v_ref_3695_);
lean_ctor_set(v___x_3699_, 1, v___x_3698_);
if (v_isShared_3694_ == 0)
{
lean_ctor_set(v___x_3693_, 0, v___x_3699_);
v___x_3701_ = v___x_3693_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v___x_3699_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
v___jp_3704_:
{
uint8_t v___x_3715_; lean_object* v___x_3716_; 
v___x_3715_ = 1;
lean_inc_ref(v___y_3707_);
v___x_3716_ = l_Lean_Environment_addConstAsync(v___y_3707_, v___y_3710_, v___y_3709_, v___y_3714_, v_hasTrace_3628_, v___x_3715_);
if (lean_obj_tag(v___x_3716_) == 0)
{
lean_object* v_a_3717_; lean_object* v_mainEnv_3718_; lean_object* v_asyncEnv_3719_; lean_object* v___f_3720_; lean_object* v___f_3721_; lean_object* v___x_3722_; 
v_a_3717_ = lean_ctor_get(v___x_3716_, 0);
lean_inc_n(v_a_3717_, 3);
lean_dec_ref(v___x_3716_);
v_mainEnv_3718_ = lean_ctor_get(v_a_3717_, 0);
lean_inc_ref(v_mainEnv_3718_);
v_asyncEnv_3719_ = lean_ctor_get(v_a_3717_, 1);
lean_inc_ref_n(v_asyncEnv_3719_, 2);
lean_inc_ref(v___y_3705_);
lean_inc(v___y_3706_);
v___f_3720_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3720_, 0, v___y_3706_);
lean_closure_set(v___f_3720_, 1, v_a_3717_);
lean_closure_set(v___f_3720_, 2, v___y_3705_);
lean_inc(v_decl_3569_);
v___f_3721_ = lean_alloc_closure((void*)(l_Lean_addDecl___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3721_, 0, v_asyncEnv_3719_);
lean_closure_set(v___f_3721_, 1, v_a_3717_);
lean_closure_set(v___f_3721_, 2, v_decl_3569_);
v___x_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3722_, 0, v___y_3713_);
if (lean_obj_tag(v___y_3708_) == 0)
{
lean_inc_ref(v___x_3722_);
v___y_3631_ = v___f_3721_;
v___y_3632_ = v___x_3715_;
v___y_3633_ = v_mainEnv_3718_;
v___y_3634_ = v___x_3722_;
v___y_3635_ = v___y_3711_;
v___y_3636_ = v_a_3717_;
v___y_3637_ = v___y_3707_;
v___y_3638_ = v___y_3712_;
v___y_3639_ = v___f_3720_;
v___y_3640_ = v_asyncEnv_3719_;
v___y_3641_ = v___x_3722_;
goto v___jp_3630_;
}
else
{
v___y_3631_ = v___f_3721_;
v___y_3632_ = v___x_3715_;
v___y_3633_ = v_mainEnv_3718_;
v___y_3634_ = v___x_3722_;
v___y_3635_ = v___y_3711_;
v___y_3636_ = v_a_3717_;
v___y_3637_ = v___y_3707_;
v___y_3638_ = v___y_3712_;
v___y_3639_ = v___f_3720_;
v___y_3640_ = v_asyncEnv_3719_;
v___y_3641_ = v___y_3708_;
goto v___jp_3630_;
}
}
else
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3735_; 
lean_dec_ref(v___y_3713_);
lean_dec(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec(v_decl_3569_);
v_a_3723_ = lean_ctor_get(v___x_3716_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3716_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3725_ = v___x_3716_;
v_isShared_3726_ = v_isSharedCheck_3735_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3716_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3735_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v_ref_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3733_; 
v_ref_3727_ = lean_ctor_get(v___y_3711_, 5);
v___x_3728_ = lean_io_error_to_string(v_a_3723_);
v___x_3729_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3728_);
v___x_3730_ = l_Lean_MessageData_ofFormat(v___x_3729_);
lean_inc(v_ref_3727_);
v___x_3731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3731_, 0, v_ref_3727_);
lean_ctor_set(v___x_3731_, 1, v___x_3730_);
if (v_isShared_3726_ == 0)
{
lean_ctor_set(v___x_3725_, 0, v___x_3731_);
v___x_3733_ = v___x_3725_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___x_3731_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
}
v___jp_3736_:
{
lean_object* v___x_3743_; 
v___x_3743_ = lean_st_ref_get(v___y_3742_);
if (lean_obj_tag(v_exportedInfo_x3f_3740_) == 0)
{
lean_object* v_env_3744_; lean_object* v___x_3745_; 
v_env_3744_ = lean_ctor_get(v___x_3743_, 0);
lean_inc_ref(v_env_3744_);
lean_dec(v___x_3743_);
v___x_3745_ = lean_box(0);
v___y_3705_ = v___y_3741_;
v___y_3706_ = v___y_3742_;
v___y_3707_ = v_env_3744_;
v___y_3708_ = v_exportedInfo_x3f_3740_;
v___y_3709_ = v___y_3737_;
v___y_3710_ = v___y_3738_;
v___y_3711_ = v___y_3741_;
v___y_3712_ = v___y_3742_;
v___y_3713_ = v___y_3739_;
v___y_3714_ = v___x_3745_;
goto v___jp_3704_;
}
else
{
lean_object* v_env_3746_; lean_object* v_val_3747_; uint8_t v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
v_env_3746_ = lean_ctor_get(v___x_3743_, 0);
lean_inc_ref(v_env_3746_);
lean_dec(v___x_3743_);
v_val_3747_ = lean_ctor_get(v_exportedInfo_x3f_3740_, 0);
v___x_3748_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3747_);
v___x_3749_ = lean_box(v___x_3748_);
v___x_3750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3749_);
v___y_3705_ = v___y_3741_;
v___y_3706_ = v___y_3742_;
v___y_3707_ = v_env_3746_;
v___y_3708_ = v_exportedInfo_x3f_3740_;
v___y_3709_ = v___y_3737_;
v___y_3710_ = v___y_3738_;
v___y_3711_ = v___y_3741_;
v___y_3712_ = v___y_3742_;
v___y_3713_ = v___y_3739_;
v___y_3714_ = v___x_3750_;
goto v___jp_3704_;
}
}
v___jp_3751_:
{
lean_object* v___x_3757_; 
lean_inc_ref(v___y_3754_);
v___x_3757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3757_, 0, v___y_3754_);
v___y_3737_ = v___y_3752_;
v___y_3738_ = v___y_3753_;
v___y_3739_ = v___y_3754_;
v_exportedInfo_x3f_3740_ = v___x_3757_;
v___y_3741_ = v___y_3755_;
v___y_3742_ = v___y_3756_;
goto v___jp_3736_;
}
v___jp_3758_:
{
lean_object* v___x_3764_; 
lean_inc_ref(v___y_3761_);
v___x_3764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3764_, 0, v___y_3761_);
v___y_3737_ = v___y_3759_;
v___y_3738_ = v___y_3760_;
v___y_3739_ = v___y_3761_;
v_exportedInfo_x3f_3740_ = v___x_3764_;
v___y_3741_ = v___y_3762_;
v___y_3742_ = v___y_3763_;
goto v___jp_3736_;
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
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_addDecl_spec__3(lean_object* v_opt_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_){
_start:
{
lean_object* v___x_4660_; 
v___x_4660_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__3___redArg(v_opt_4656_, v___y_4657_);
return v___x_4660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_addDecl_spec__3___boxed(lean_object* v_opt_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_){
_start:
{
lean_object* v_res_4665_; 
v_res_4665_ = l_Lean_Option_getM___at___00Lean_addDecl_spec__3(v_opt_4661_, v___y_4662_, v___y_4663_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4662_);
lean_dec_ref(v_opt_4661_);
return v_res_4665_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(lean_object* v_as_x27_4666_, lean_object* v_b_4667_, lean_object* v___y_4668_){
_start:
{
if (lean_obj_tag(v_as_x27_4666_) == 0)
{
lean_object* v___x_4670_; 
v___x_4670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4670_, 0, v_b_4667_);
return v___x_4670_;
}
else
{
lean_object* v_head_4671_; lean_object* v_tail_4672_; lean_object* v___x_4673_; lean_object* v_env_4674_; lean_object* v_nextMacroScope_4675_; lean_object* v_ngen_4676_; lean_object* v_auxDeclNGen_4677_; lean_object* v_traceState_4678_; lean_object* v_messages_4679_; lean_object* v_infoState_4680_; lean_object* v_snapshotTasks_4681_; lean_object* v___x_4683_; uint8_t v_isShared_4684_; uint8_t v_isSharedCheck_4693_; 
v_head_4671_ = lean_ctor_get(v_as_x27_4666_, 0);
v_tail_4672_ = lean_ctor_get(v_as_x27_4666_, 1);
v___x_4673_ = lean_st_ref_take(v___y_4668_);
v_env_4674_ = lean_ctor_get(v___x_4673_, 0);
v_nextMacroScope_4675_ = lean_ctor_get(v___x_4673_, 1);
v_ngen_4676_ = lean_ctor_get(v___x_4673_, 2);
v_auxDeclNGen_4677_ = lean_ctor_get(v___x_4673_, 3);
v_traceState_4678_ = lean_ctor_get(v___x_4673_, 4);
v_messages_4679_ = lean_ctor_get(v___x_4673_, 6);
v_infoState_4680_ = lean_ctor_get(v___x_4673_, 7);
v_snapshotTasks_4681_ = lean_ctor_get(v___x_4673_, 8);
v_isSharedCheck_4693_ = !lean_is_exclusive(v___x_4673_);
if (v_isSharedCheck_4693_ == 0)
{
lean_object* v_unused_4694_; 
v_unused_4694_ = lean_ctor_get(v___x_4673_, 5);
lean_dec(v_unused_4694_);
v___x_4683_ = v___x_4673_;
v_isShared_4684_ = v_isSharedCheck_4693_;
goto v_resetjp_4682_;
}
else
{
lean_inc(v_snapshotTasks_4681_);
lean_inc(v_infoState_4680_);
lean_inc(v_messages_4679_);
lean_inc(v_traceState_4678_);
lean_inc(v_auxDeclNGen_4677_);
lean_inc(v_ngen_4676_);
lean_inc(v_nextMacroScope_4675_);
lean_inc(v_env_4674_);
lean_dec(v___x_4673_);
v___x_4683_ = lean_box(0);
v_isShared_4684_ = v_isSharedCheck_4693_;
goto v_resetjp_4682_;
}
v_resetjp_4682_:
{
lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4688_; 
lean_inc(v_head_4671_);
v___x_4685_ = l_Lean_markMeta(v_env_4674_, v_head_4671_);
v___x_4686_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDecl_addAsAxiom_spec__1___redArg___closed__2);
if (v_isShared_4684_ == 0)
{
lean_ctor_set(v___x_4683_, 5, v___x_4686_);
lean_ctor_set(v___x_4683_, 0, v___x_4685_);
v___x_4688_ = v___x_4683_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v___x_4685_);
lean_ctor_set(v_reuseFailAlloc_4692_, 1, v_nextMacroScope_4675_);
lean_ctor_set(v_reuseFailAlloc_4692_, 2, v_ngen_4676_);
lean_ctor_set(v_reuseFailAlloc_4692_, 3, v_auxDeclNGen_4677_);
lean_ctor_set(v_reuseFailAlloc_4692_, 4, v_traceState_4678_);
lean_ctor_set(v_reuseFailAlloc_4692_, 5, v___x_4686_);
lean_ctor_set(v_reuseFailAlloc_4692_, 6, v_messages_4679_);
lean_ctor_set(v_reuseFailAlloc_4692_, 7, v_infoState_4680_);
lean_ctor_set(v_reuseFailAlloc_4692_, 8, v_snapshotTasks_4681_);
v___x_4688_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
lean_object* v___x_4689_; lean_object* v___x_4690_; 
v___x_4689_ = lean_st_ref_set(v___y_4668_, v___x_4688_);
v___x_4690_ = lean_box(0);
v_as_x27_4666_ = v_tail_4672_;
v_b_4667_ = v___x_4690_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg___boxed(lean_object* v_as_x27_4695_, lean_object* v_b_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_){
_start:
{
lean_object* v_res_4699_; 
v_res_4699_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_4695_, v_b_4696_, v___y_4697_);
lean_dec(v___y_4697_);
lean_dec(v_as_x27_4695_);
return v_res_4699_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object* v_decl_4700_, uint8_t v_logCompileErrors_4701_, uint8_t v_markMeta_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_){
_start:
{
uint8_t v___x_4706_; lean_object* v___x_4707_; 
v___x_4706_ = 0;
lean_inc(v_decl_4700_);
v___x_4707_ = l_Lean_addDecl(v_decl_4700_, v___x_4706_, v_a_4703_, v_a_4704_);
if (lean_obj_tag(v___x_4707_) == 0)
{
lean_dec_ref(v___x_4707_);
if (v_markMeta_4702_ == 0)
{
lean_object* v___x_4708_; 
v___x_4708_ = l_Lean_compileDecl(v_decl_4700_, v_logCompileErrors_4701_, v_a_4703_, v_a_4704_);
return v___x_4708_;
}
else
{
lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; 
lean_inc(v_decl_4700_);
v___x_4709_ = l_Lean_Declaration_getNames(v_decl_4700_);
v___x_4710_ = lean_box(0);
v___x_4711_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v___x_4709_, v___x_4710_, v_a_4704_);
lean_dec(v___x_4709_);
lean_dec_ref(v___x_4711_);
v___x_4712_ = l_Lean_compileDecl(v_decl_4700_, v_logCompileErrors_4701_, v_a_4703_, v_a_4704_);
return v___x_4712_;
}
}
else
{
lean_dec(v_decl_4700_);
return v___x_4707_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___boxed(lean_object* v_decl_4713_, lean_object* v_logCompileErrors_4714_, lean_object* v_markMeta_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_){
_start:
{
uint8_t v_logCompileErrors_boxed_4719_; uint8_t v_markMeta_boxed_4720_; lean_object* v_res_4721_; 
v_logCompileErrors_boxed_4719_ = lean_unbox(v_logCompileErrors_4714_);
v_markMeta_boxed_4720_ = lean_unbox(v_markMeta_4715_);
v_res_4721_ = l_Lean_addAndCompile(v_decl_4713_, v_logCompileErrors_boxed_4719_, v_markMeta_boxed_4720_, v_a_4716_, v_a_4717_);
lean_dec(v_a_4717_);
lean_dec_ref(v_a_4716_);
return v_res_4721_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(lean_object* v_as_4722_, lean_object* v_as_x27_4723_, lean_object* v_b_4724_, lean_object* v_a_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_){
_start:
{
lean_object* v___x_4729_; 
v___x_4729_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_4723_, v_b_4724_, v___y_4727_);
return v___x_4729_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___boxed(lean_object* v_as_4730_, lean_object* v_as_x27_4731_, lean_object* v_b_4732_, lean_object* v_a_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_){
_start:
{
lean_object* v_res_4737_; 
v_res_4737_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(v_as_4730_, v_as_x27_4731_, v_b_4732_, v_a_4733_, v___y_4734_, v___y_4735_);
lean_dec(v___y_4735_);
lean_dec_ref(v___y_4734_);
lean_dec(v_as_x27_4731_);
lean_dec(v_as_4730_);
return v_res_4737_;
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
