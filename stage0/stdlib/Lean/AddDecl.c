// Lean compiler output
// Module: Lean.AddDecl
// Imports: public import Lean.Meta.Sorry public import Lean.Util.CollectAxioms public import Lean.OriginalConstKind public import Lean.AutoDecl import Lean.Linter.Init import Lean.Compiler.MetaAttr import Lean.Util.RecDepth import all Lean.OriginalConstKind
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
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getSorry_x3f(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Declaration_getTopLevelNames(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Declaration_getNames(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
extern lean_object* l_Lean_debug_skipKernelTC;
lean_object* l_Lean_Environment_addDeclCore(lean_object*, size_t, size_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
uint8_t l_Lean_Declaration_hasSorry(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t l_Lean_Expr_isSyntheticSorry(lean_object*);
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
lean_object* lean_array_fget(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqDefinitionSafety_beq(uint8_t, uint8_t);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Environment_registerNamespace(lean_object*, lean_object*);
lean_object* l_Lean_Environment_AddConstAsyncResult_commitConst(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_async;
lean_object* l_IO_CancelToken_new();
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Core_logSnapshotTask___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_addConstAsync(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t);
uint8_t l_Lean_ConstantKind_ofConstantInfo(lean_object*);
extern lean_object* l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic;
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
lean_object* lean_elab_environment_to_kernel_env(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* lean_add_decl(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_add_decl_without_checking(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_envLinterOptionsRef;
lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_envLinterSnapshotExt;
lean_object* l_Lean_markMeta(lean_object*, lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_snapshotEnvLinterOptions___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_snapshotEnvLinterOptions___closed__0;
static lean_once_cell_t l_Lean_snapshotEnvLinterOptions___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_snapshotEnvLinterOptions___closed__1;
static lean_once_cell_t l_Lean_snapshotEnvLinterOptions___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_snapshotEnvLinterOptions___closed__2;
LEAN_EXPORT lean_object* l_Lean_snapshotEnvLinterOptions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_snapshotEnvLinterOptions___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20_spec__22___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20_spec__22___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13_spec__24_spec__27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13_spec__24_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13_spec__24___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13_spec__24___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13___closed__0 = (const lean_object*)&l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20_spec__22___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__22___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__22___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__18_spec__19___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__18_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__18___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0;
static lean_once_cell_t l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1;
static lean_once_cell_t l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2;
static lean_once_cell_t l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__3;
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__18___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20_spec__22(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13_spec__24_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13_spec__24_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__18_spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__18_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "sorryAx"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(196, 190, 164, 146, 38, 179, 69, 72)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__8 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__8_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__9 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__9_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__10_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__10 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__10_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__13 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__13_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__14 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__14_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "typechecking declarations "};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__0 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "type checking"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__0 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__0_value;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Kernel"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__1 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__1_value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(213, 59, 86, 63, 192, 192, 9, 44)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__2 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "adding declarations "};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__0 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "no matching async adding rules, adding synchronously"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__0 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__0_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2___boxed(lean_object*);
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "addDeclCore"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__0 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__0_value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__8_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 15, 132, 113, 234, 47, 152, 164)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1_value;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "no matching exporting rules, exporting as is"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__2 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__2_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "not exporting private declaration at all"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__4 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__4_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "private decl under `privateInPublic`, exporting as is"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__6 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__6_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "exporting definition "};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__0 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__0_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " as axiom"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__2 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__2_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "exporting opaque "};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "exporting theorem "};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v___x_6_, 1);
if (lean_obj_tag(v_val_8_) == 1)
{
uint8_t v_v_9_; 
v_v_9_ = lean_ctor_get_uint8(v_val_8_, 0);
lean_dec_ref_known(v_val_8_, 0);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(lean_object* v_opts_15_, lean_object* v_opt_16_){
_start:
{
lean_object* v_name_17_; lean_object* v_defValue_18_; lean_object* v_map_19_; lean_object* v___x_20_; 
v_name_17_ = lean_ctor_get(v_opt_16_, 0);
v_defValue_18_ = lean_ctor_get(v_opt_16_, 1);
v_map_19_ = lean_ctor_get(v_opts_15_, 0);
v___x_20_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_19_, v_name_17_);
if (lean_obj_tag(v___x_20_) == 0)
{
lean_inc(v_defValue_18_);
return v_defValue_18_;
}
else
{
lean_object* v_val_21_; 
v_val_21_ = lean_ctor_get(v___x_20_, 0);
lean_inc(v_val_21_);
lean_dec_ref_known(v___x_20_, 1);
if (lean_obj_tag(v_val_21_) == 3)
{
lean_object* v_v_22_; 
v_v_22_ = lean_ctor_get(v_val_21_, 0);
lean_inc(v_v_22_);
lean_dec_ref_known(v_val_21_, 1);
return v_v_22_;
}
else
{
lean_dec(v_val_21_);
lean_inc(v_defValue_18_);
return v_defValue_18_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1___boxed(lean_object* v_opts_23_, lean_object* v_opt_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_23_, v_opt_24_);
lean_dec_ref(v_opt_24_);
lean_dec_ref(v_opts_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addDecl(lean_object* v_env_26_, lean_object* v_opts_27_, lean_object* v_decl_28_, lean_object* v_cancelTk_x3f_29_){
_start:
{
lean_object* v___x_30_; uint8_t v___x_31_; 
v___x_30_ = l_Lean_debug_skipKernelTC;
v___x_31_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_27_, v___x_30_);
if (v___x_31_ == 0)
{
lean_object* v___x_32_; size_t v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; size_t v___x_36_; lean_object* v___x_37_; 
v___x_32_ = l_Lean_Core_getMaxHeartbeats(v_opts_27_);
v___x_33_ = lean_usize_of_nat(v___x_32_);
lean_dec(v___x_32_);
v___x_34_ = l_Lean_maxRecDepth;
v___x_35_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_27_, v___x_34_);
v___x_36_ = lean_usize_of_nat(v___x_35_);
lean_dec(v___x_35_);
v___x_37_ = lean_add_decl(v_env_26_, v___x_33_, v___x_36_, v_decl_28_, v_cancelTk_x3f_29_);
return v___x_37_;
}
else
{
lean_object* v___x_38_; 
v___x_38_ = lean_add_decl_without_checking(v_env_26_, v_decl_28_);
return v___x_38_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addDecl___boxed(lean_object* v_env_39_, lean_object* v_opts_40_, lean_object* v_decl_41_, lean_object* v_cancelTk_x3f_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Kernel_Environment_addDecl(v_env_39_, v_opts_40_, v_decl_41_, v_cancelTk_x3f_42_);
lean_dec(v_cancelTk_x3f_42_);
lean_dec(v_decl_41_);
lean_dec_ref(v_opts_40_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(lean_object* v_env_44_, lean_object* v_opts_45_, lean_object* v_decl_46_, lean_object* v_cancelTk_x3f_47_){
_start:
{
lean_object* v___x_48_; size_t v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; size_t v___x_52_; lean_object* v___x_53_; uint8_t v___x_54_; 
v___x_48_ = l_Lean_Core_getMaxHeartbeats(v_opts_45_);
v___x_49_ = lean_usize_of_nat(v___x_48_);
lean_dec(v___x_48_);
v___x_50_ = l_Lean_maxRecDepth;
v___x_51_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_45_, v___x_50_);
v___x_52_ = lean_usize_of_nat(v___x_51_);
lean_dec(v___x_51_);
v___x_53_ = l_Lean_debug_skipKernelTC;
v___x_54_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_45_, v___x_53_);
if (v___x_54_ == 0)
{
uint8_t v___x_55_; lean_object* v___x_56_; 
v___x_55_ = 1;
v___x_56_ = l_Lean_Environment_addDeclCore(v_env_44_, v___x_49_, v___x_52_, v_decl_46_, v_cancelTk_x3f_47_, v___x_55_);
return v___x_56_;
}
else
{
uint8_t v___x_57_; lean_object* v___x_58_; 
v___x_57_ = 0;
v___x_58_ = l_Lean_Environment_addDeclCore(v_env_44_, v___x_49_, v___x_52_, v_decl_46_, v_cancelTk_x3f_47_, v___x_57_);
return v___x_58_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux___boxed(lean_object* v_env_59_, lean_object* v_opts_60_, lean_object* v_decl_61_, lean_object* v_cancelTk_x3f_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_59_, v_opts_60_, v_decl_61_, v_cancelTk_x3f_62_);
lean_dec(v_cancelTk_x3f_62_);
lean_dec(v_decl_61_);
lean_dec_ref(v_opts_60_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg(lean_object* v_a_64_, lean_object* v_as_65_, size_t v_sz_66_, size_t v_i_67_, lean_object* v_b_68_){
_start:
{
uint8_t v___x_70_; 
v___x_70_ = lean_usize_dec_lt(v_i_67_, v_sz_66_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; 
v___x_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_71_, 0, v_b_68_);
return v___x_71_;
}
else
{
lean_object* v_a_72_; lean_object* v_name_73_; uint8_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; size_t v___x_77_; size_t v___x_78_; 
v_a_72_ = lean_array_uget_borrowed(v_as_65_, v_i_67_);
v_name_73_ = lean_ctor_get(v_a_72_, 0);
v___x_74_ = l_Lean_Linter_getLinterValue(v_a_72_, v_a_64_);
v___x_75_ = lean_box(v___x_74_);
lean_inc(v_name_73_);
v___x_76_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_73_, v___x_75_, v_b_68_);
v___x_77_ = ((size_t)1ULL);
v___x_78_ = lean_usize_add(v_i_67_, v___x_77_);
v_i_67_ = v___x_78_;
v_b_68_ = v___x_76_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg___boxed(lean_object* v_a_80_, lean_object* v_as_81_, lean_object* v_sz_82_, lean_object* v_i_83_, lean_object* v_b_84_, lean_object* v___y_85_){
_start:
{
size_t v_sz_boxed_86_; size_t v_i_boxed_87_; lean_object* v_res_88_; 
v_sz_boxed_86_ = lean_unbox_usize(v_sz_82_);
lean_dec(v_sz_82_);
v_i_boxed_87_ = lean_unbox_usize(v_i_83_);
lean_dec(v_i_83_);
v_res_88_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg(v_a_80_, v_as_81_, v_sz_boxed_86_, v_i_boxed_87_, v_b_84_);
lean_dec_ref(v_as_81_);
lean_dec_ref(v_a_80_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(lean_object* v_o_89_, lean_object* v___y_90_){
_start:
{
lean_object* v___x_92_; lean_object* v_env_93_; lean_object* v___x_94_; lean_object* v_toEnvExtension_95_; lean_object* v_asyncMode_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v_merged_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_108_; 
v___x_92_ = lean_st_ref_get(v___y_90_);
v_env_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc_ref(v_env_93_);
lean_dec(v___x_92_);
v___x_94_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_95_ = lean_ctor_get(v___x_94_, 0);
v_asyncMode_96_ = lean_ctor_get(v_toEnvExtension_95_, 2);
v___x_97_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_98_ = lean_box(0);
v___x_99_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_97_, v___x_94_, v_env_93_, v_asyncMode_96_, v___x_98_);
v_merged_100_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_108_ == 0)
{
lean_object* v_unused_109_; 
v_unused_109_ = lean_ctor_get(v___x_99_, 1);
lean_dec(v_unused_109_);
v___x_102_ = v___x_99_;
v_isShared_103_ = v_isSharedCheck_108_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_merged_100_);
lean_dec(v___x_99_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_108_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_105_; 
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v_merged_100_);
lean_ctor_set(v___x_102_, 0, v_o_89_);
v___x_105_ = v___x_102_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_o_89_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v_merged_100_);
v___x_105_ = v_reuseFailAlloc_107_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
lean_object* v___x_106_; 
v___x_106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
return v___x_106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg___boxed(lean_object* v_o_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(v_o_110_, v___y_111_);
lean_dec(v___y_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0(lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_options_117_; lean_object* v___x_118_; 
v_options_117_ = lean_ctor_get(v___y_114_, 2);
lean_inc_ref(v_options_117_);
v___x_118_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(v_options_117_, v___y_115_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0___boxed(lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0(v___y_119_, v___y_120_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
return v_res_122_;
}
}
static lean_object* _init_l_Lean_snapshotEnvLinterOptions___closed__0(void){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_123_;
}
}
static lean_object* _init_l_Lean_snapshotEnvLinterOptions___closed__1(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__0, &l_Lean_snapshotEnvLinterOptions___closed__0_once, _init_l_Lean_snapshotEnvLinterOptions___closed__0);
v___x_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_snapshotEnvLinterOptions___closed__2(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__1, &l_Lean_snapshotEnvLinterOptions___closed__1_once, _init_l_Lean_snapshotEnvLinterOptions___closed__1);
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_snapshotEnvLinterOptions(lean_object* v_declName_128_, lean_object* v_a_129_, lean_object* v_a_130_){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_132_ = l_Lean_Linter_envLinterOptionsRef;
v___x_133_ = lean_st_ref_get(v___x_132_);
v___x_134_ = lean_array_get_size(v___x_133_);
v___x_135_ = lean_unsigned_to_nat(0u);
v___x_136_ = lean_nat_dec_eq(v___x_134_, v___x_135_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; lean_object* v_a_138_; lean_object* v___x_139_; 
v___x_137_ = l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0(v_a_129_, v_a_130_);
v_a_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_a_138_);
lean_dec_ref(v___x_137_);
lean_inc(v_declName_128_);
v___x_139_ = l_Lean_isAutoDeclOrPrivate__Internal___redArg(v_declName_128_, v_a_130_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_191_; 
v_a_140_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_191_ == 0)
{
v___x_142_ = v___x_139_;
v_isShared_143_ = v_isSharedCheck_191_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_139_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_191_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
uint8_t v___x_144_; 
v___x_144_ = lean_unbox(v_a_140_);
lean_dec(v_a_140_);
if (v___x_144_ == 0)
{
lean_object* v___x_145_; size_t v_sz_146_; size_t v___x_147_; lean_object* v___x_148_; 
lean_del_object(v___x_142_);
v___x_145_ = lean_box(1);
v_sz_146_ = lean_array_size(v___x_133_);
v___x_147_ = ((size_t)0ULL);
v___x_148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg(v_a_138_, v___x_133_, v_sz_146_, v___x_147_, v___x_145_);
lean_dec(v___x_133_);
lean_dec(v_a_138_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_178_; 
v_a_149_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_178_ == 0)
{
v___x_151_ = v___x_148_;
v_isShared_152_ = v_isSharedCheck_178_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_148_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_178_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_153_; lean_object* v_env_154_; lean_object* v_nextMacroScope_155_; lean_object* v_ngen_156_; lean_object* v_auxDeclNGen_157_; lean_object* v_traceState_158_; lean_object* v_messages_159_; lean_object* v_infoState_160_; lean_object* v_snapshotTasks_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_176_; 
v___x_153_ = lean_st_ref_take(v_a_130_);
v_env_154_ = lean_ctor_get(v___x_153_, 0);
v_nextMacroScope_155_ = lean_ctor_get(v___x_153_, 1);
v_ngen_156_ = lean_ctor_get(v___x_153_, 2);
v_auxDeclNGen_157_ = lean_ctor_get(v___x_153_, 3);
v_traceState_158_ = lean_ctor_get(v___x_153_, 4);
v_messages_159_ = lean_ctor_get(v___x_153_, 6);
v_infoState_160_ = lean_ctor_get(v___x_153_, 7);
v_snapshotTasks_161_ = lean_ctor_get(v___x_153_, 8);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_176_ == 0)
{
lean_object* v_unused_177_; 
v_unused_177_ = lean_ctor_get(v___x_153_, 5);
lean_dec(v_unused_177_);
v___x_163_ = v___x_153_;
v_isShared_164_ = v_isSharedCheck_176_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_snapshotTasks_161_);
lean_inc(v_infoState_160_);
lean_inc(v_messages_159_);
lean_inc(v_traceState_158_);
lean_inc(v_auxDeclNGen_157_);
lean_inc(v_ngen_156_);
lean_inc(v_nextMacroScope_155_);
lean_inc(v_env_154_);
lean_dec(v___x_153_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_176_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_169_; 
v___x_165_ = l_Lean_Linter_envLinterSnapshotExt;
v___x_166_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_165_, v_env_154_, v_declName_128_, v_a_149_);
v___x_167_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 5, v___x_167_);
lean_ctor_set(v___x_163_, 0, v___x_166_);
v___x_169_ = v___x_163_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_166_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_nextMacroScope_155_);
lean_ctor_set(v_reuseFailAlloc_175_, 2, v_ngen_156_);
lean_ctor_set(v_reuseFailAlloc_175_, 3, v_auxDeclNGen_157_);
lean_ctor_set(v_reuseFailAlloc_175_, 4, v_traceState_158_);
lean_ctor_set(v_reuseFailAlloc_175_, 5, v___x_167_);
lean_ctor_set(v_reuseFailAlloc_175_, 6, v_messages_159_);
lean_ctor_set(v_reuseFailAlloc_175_, 7, v_infoState_160_);
lean_ctor_set(v_reuseFailAlloc_175_, 8, v_snapshotTasks_161_);
v___x_169_ = v_reuseFailAlloc_175_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_173_; 
v___x_170_ = lean_st_ref_put(v_a_130_, v___x_169_);
v___x_171_ = lean_box(0);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 0, v___x_171_);
v___x_173_ = v___x_151_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
}
else
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
lean_dec(v_declName_128_);
v_a_179_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_148_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_148_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
else
{
lean_object* v___x_187_; lean_object* v___x_189_; 
lean_dec(v_a_138_);
lean_dec(v___x_133_);
lean_dec(v_declName_128_);
v___x_187_ = lean_box(0);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v___x_187_);
v___x_189_ = v___x_142_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
else
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
lean_dec(v_a_138_);
lean_dec(v___x_133_);
lean_dec(v_declName_128_);
v_a_192_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_139_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_139_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
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
else
{
lean_object* v___x_200_; lean_object* v___x_201_; 
lean_dec(v___x_133_);
lean_dec(v_declName_128_);
v___x_200_ = lean_box(0);
v___x_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
return v___x_201_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_snapshotEnvLinterOptions___boxed(lean_object* v_declName_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_snapshotEnvLinterOptions(v_declName_202_, v_a_203_, v_a_204_);
lean_dec(v_a_204_);
lean_dec_ref(v_a_203_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0(lean_object* v_o_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(v_o_207_, v___y_209_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___boxed(lean_object* v_o_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0(v_o_212_, v___y_213_, v___y_214_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1(lean_object* v_a_217_, lean_object* v_as_218_, size_t v_sz_219_, size_t v_i_220_, lean_object* v_b_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg(v_a_217_, v_as_218_, v_sz_219_, v_i_220_, v_b_221_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___boxed(lean_object* v_a_226_, lean_object* v_as_227_, lean_object* v_sz_228_, lean_object* v_i_229_, lean_object* v_b_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
size_t v_sz_boxed_234_; size_t v_i_boxed_235_; lean_object* v_res_236_; 
v_sz_boxed_234_ = lean_unbox_usize(v_sz_228_);
lean_dec(v_sz_228_);
v_i_boxed_235_ = lean_unbox_usize(v_i_229_);
lean_dec(v_i_229_);
v_res_236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1(v_a_226_, v_as_227_, v_sz_boxed_234_, v_i_boxed_235_, v_b_230_, v___y_231_, v___y_232_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec_ref(v_as_227_);
lean_dec_ref(v_a_226_);
return v_res_236_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_AddDecl_0__Lean_isNamespaceName(lean_object* v_x_237_){
_start:
{
if (lean_obj_tag(v_x_237_) == 1)
{
lean_object* v_pre_238_; 
v_pre_238_ = lean_ctor_get(v_x_237_, 0);
if (lean_obj_tag(v_pre_238_) == 0)
{
uint8_t v___x_239_; 
v___x_239_ = 1;
return v___x_239_;
}
else
{
v_x_237_ = v_pre_238_;
goto _start;
}
}
else
{
uint8_t v___x_241_; 
v___x_241_ = 0;
return v___x_241_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_isNamespaceName___boxed(lean_object* v_x_242_){
_start:
{
uint8_t v_res_243_; lean_object* v_r_244_; 
v_res_243_ = l___private_Lean_AddDecl_0__Lean_isNamespaceName(v_x_242_);
lean_dec(v_x_242_);
v_r_244_ = lean_box(v_res_243_);
return v_r_244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_registerNamePrefixes_go(lean_object* v_env_245_, lean_object* v_x_246_){
_start:
{
if (lean_obj_tag(v_x_246_) == 1)
{
lean_object* v_pre_247_; uint8_t v___x_248_; 
v_pre_247_ = lean_ctor_get(v_x_246_, 0);
lean_inc(v_pre_247_);
lean_dec_ref_known(v_x_246_, 2);
v___x_248_ = l___private_Lean_AddDecl_0__Lean_isNamespaceName(v_pre_247_);
if (v___x_248_ == 0)
{
lean_dec(v_pre_247_);
return v_env_245_;
}
else
{
lean_object* v___x_249_; 
lean_inc(v_pre_247_);
v___x_249_ = l_Lean_Environment_registerNamespace(v_env_245_, v_pre_247_);
v_env_245_ = v___x_249_;
v_x_246_ = v_pre_247_;
goto _start;
}
}
else
{
lean_dec(v_x_246_);
return v_env_245_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(lean_object* v_env_251_, lean_object* v_name_252_){
_start:
{
lean_object* v_name_253_; uint32_t v___y_255_; 
v_name_253_ = l_Lean_privateToUserName(v_name_252_);
if (lean_obj_tag(v_name_253_) == 1)
{
lean_object* v_str_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v_str_259_ = lean_ctor_get(v_name_253_, 1);
lean_inc_ref(v_str_259_);
v___x_260_ = lean_unsigned_to_nat(0u);
v___x_261_ = lean_string_utf8_byte_size(v_str_259_);
v___x_262_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_262_, 0, v_str_259_);
lean_ctor_set(v___x_262_, 1, v___x_260_);
lean_ctor_set(v___x_262_, 2, v___x_261_);
v___x_263_ = l_String_Slice_Pos_get_x3f(v___x_262_, v___x_260_);
lean_dec_ref_known(v___x_262_, 3);
if (lean_obj_tag(v___x_263_) == 0)
{
uint32_t v___x_264_; 
v___x_264_ = 65;
v___y_255_ = v___x_264_;
goto v___jp_254_;
}
else
{
lean_object* v_val_265_; uint32_t v___x_266_; 
v_val_265_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_val_265_);
lean_dec_ref_known(v___x_263_, 1);
v___x_266_ = lean_unbox_uint32(v_val_265_);
lean_dec(v_val_265_);
v___y_255_ = v___x_266_;
goto v___jp_254_;
}
}
else
{
lean_dec(v_name_253_);
return v_env_251_;
}
v___jp_254_:
{
uint32_t v___x_256_; uint8_t v___x_257_; 
v___x_256_ = 95;
v___x_257_ = lean_uint32_dec_eq(v___y_255_, v___x_256_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; 
v___x_258_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes_go(v_env_251_, v_name_253_);
return v___x_258_;
}
else
{
lean_dec(v_name_253_);
return v_env_251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(lean_object* v_name_267_, lean_object* v_decl_268_, lean_object* v_ref_269_){
_start:
{
lean_object* v_defValue_271_; lean_object* v_descr_272_; lean_object* v_deprecation_x3f_273_; lean_object* v___x_274_; uint8_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v_defValue_271_ = lean_ctor_get(v_decl_268_, 0);
v_descr_272_ = lean_ctor_get(v_decl_268_, 1);
v_deprecation_x3f_273_ = lean_ctor_get(v_decl_268_, 2);
v___x_274_ = lean_alloc_ctor(1, 0, 1);
v___x_275_ = lean_unbox(v_defValue_271_);
lean_ctor_set_uint8(v___x_274_, 0, v___x_275_);
lean_inc(v_deprecation_x3f_273_);
lean_inc_ref(v_descr_272_);
lean_inc_n(v_name_267_, 2);
v___x_276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_276_, 0, v_name_267_);
lean_ctor_set(v___x_276_, 1, v_ref_269_);
lean_ctor_set(v___x_276_, 2, v___x_274_);
lean_ctor_set(v___x_276_, 3, v_descr_272_);
lean_ctor_set(v___x_276_, 4, v_deprecation_x3f_273_);
v___x_277_ = lean_register_option(v_name_267_, v___x_276_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_285_; 
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_285_ == 0)
{
lean_object* v_unused_286_; 
v_unused_286_ = lean_ctor_get(v___x_277_, 0);
lean_dec(v_unused_286_);
v___x_279_ = v___x_277_;
v_isShared_280_ = v_isSharedCheck_285_;
goto v_resetjp_278_;
}
else
{
lean_dec(v___x_277_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_285_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_281_; lean_object* v___x_283_; 
lean_inc(v_defValue_271_);
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v_name_267_);
lean_ctor_set(v___x_281_, 1, v_defValue_271_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_281_);
v___x_283_ = v___x_279_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_281_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
lean_dec(v_name_267_);
v_a_287_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_277_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_277_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_295_, lean_object* v_decl_296_, lean_object* v_ref_297_, lean_object* v_a_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(v_name_295_, v_decl_296_, v_ref_297_);
lean_dec_ref(v_decl_296_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_317_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__2_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_318_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__4_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_319_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__6_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_320_ = l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(v___x_317_, v___x_318_, v___x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4____boxed(lean_object* v_a_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_();
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(lean_object* v_msgData_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v___x_329_; lean_object* v_env_330_; lean_object* v___x_331_; lean_object* v_mctx_332_; lean_object* v_lctx_333_; lean_object* v_options_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_329_ = lean_st_ref_get(v___y_327_);
v_env_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc_ref(v_env_330_);
lean_dec(v___x_329_);
v___x_331_ = lean_st_ref_get(v___y_325_);
v_mctx_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc_ref(v_mctx_332_);
lean_dec(v___x_331_);
v_lctx_333_ = lean_ctor_get(v___y_324_, 2);
v_options_334_ = lean_ctor_get(v___y_326_, 2);
lean_inc_ref(v_options_334_);
lean_inc_ref(v_lctx_333_);
v___x_335_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_335_, 0, v_env_330_);
lean_ctor_set(v___x_335_, 1, v_mctx_332_);
lean_ctor_set(v___x_335_, 2, v_lctx_333_);
lean_ctor_set(v___x_335_, 3, v_options_334_);
v___x_336_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v_msgData_323_);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0___boxed(lean_object* v_msgData_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(v_msgData_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___lam__0(lean_object* v_s_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_368_; 
lean_inc_ref(v_s_345_);
v___x_352_ = l_Lean_MessageData_ofExpr(v_s_345_);
v___x_353_ = l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(v___x_352_, v___y_347_, v___y_348_, v___y_349_, v___y_350_);
v_a_354_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_368_ == 0)
{
v___x_356_ = v___x_353_;
v_isShared_357_ = v_isSharedCheck_368_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_353_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_368_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_358_; uint8_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_358_ = lean_st_ref_take(v___y_346_);
v___x_359_ = l_Lean_Expr_isSyntheticSorry(v_s_345_);
lean_dec_ref(v_s_345_);
v___x_360_ = lean_box(v___x_359_);
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
lean_ctor_set(v___x_361_, 1, v_a_354_);
v___x_362_ = lean_array_push(v___x_358_, v___x_361_);
v___x_363_ = lean_st_ref_put(v___y_346_, v___x_362_);
v___x_364_ = lean_box(0);
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 0, v___x_364_);
v___x_366_ = v___x_356_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_364_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___lam__0___boxed(lean_object* v_s_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_warnIfUsesSorry___lam__0(v_s_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
return v_res_376_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(uint8_t v___y_385_, uint8_t v_suppressElabErrors_386_, lean_object* v_x_387_){
_start:
{
if (lean_obj_tag(v_x_387_) == 1)
{
lean_object* v_pre_388_; 
v_pre_388_ = lean_ctor_get(v_x_387_, 0);
switch(lean_obj_tag(v_pre_388_))
{
case 1:
{
lean_object* v_pre_389_; 
v_pre_389_ = lean_ctor_get(v_pre_388_, 0);
switch(lean_obj_tag(v_pre_389_))
{
case 0:
{
lean_object* v_str_390_; lean_object* v_str_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v_str_390_ = lean_ctor_get(v_x_387_, 1);
v_str_391_ = lean_ctor_get(v_pre_388_, 1);
v___x_392_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__0));
v___x_393_ = lean_string_dec_eq(v_str_391_, v___x_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_394_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__1));
v___x_395_ = lean_string_dec_eq(v_str_391_, v___x_394_);
if (v___x_395_ == 0)
{
return v___y_385_;
}
else
{
lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_396_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__2));
v___x_397_ = lean_string_dec_eq(v_str_390_, v___x_396_);
if (v___x_397_ == 0)
{
return v___y_385_;
}
else
{
return v_suppressElabErrors_386_;
}
}
}
else
{
lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_398_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__3));
v___x_399_ = lean_string_dec_eq(v_str_390_, v___x_398_);
if (v___x_399_ == 0)
{
return v___y_385_;
}
else
{
return v_suppressElabErrors_386_;
}
}
}
case 1:
{
lean_object* v_pre_400_; 
v_pre_400_ = lean_ctor_get(v_pre_389_, 0);
if (lean_obj_tag(v_pre_400_) == 0)
{
lean_object* v_str_401_; lean_object* v_str_402_; lean_object* v_str_403_; lean_object* v___x_404_; uint8_t v___x_405_; 
v_str_401_ = lean_ctor_get(v_x_387_, 1);
v_str_402_ = lean_ctor_get(v_pre_388_, 1);
v_str_403_ = lean_ctor_get(v_pre_389_, 1);
v___x_404_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__4));
v___x_405_ = lean_string_dec_eq(v_str_403_, v___x_404_);
if (v___x_405_ == 0)
{
return v___y_385_;
}
else
{
lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_406_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__5));
v___x_407_ = lean_string_dec_eq(v_str_402_, v___x_406_);
if (v___x_407_ == 0)
{
return v___y_385_;
}
else
{
lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_408_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__6));
v___x_409_ = lean_string_dec_eq(v_str_401_, v___x_408_);
if (v___x_409_ == 0)
{
return v___y_385_;
}
else
{
return v_suppressElabErrors_386_;
}
}
}
}
else
{
return v___y_385_;
}
}
default: 
{
return v___y_385_;
}
}
}
case 0:
{
lean_object* v_str_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v_str_410_ = lean_ctor_get(v_x_387_, 1);
v___x_411_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__7));
v___x_412_ = lean_string_dec_eq(v_str_410_, v___x_411_);
if (v___x_412_ == 0)
{
return v___y_385_;
}
else
{
return v_suppressElabErrors_386_;
}
}
default: 
{
return v___y_385_;
}
}
}
else
{
return v___y_385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed(lean_object* v___y_413_, lean_object* v_suppressElabErrors_414_, lean_object* v_x_415_){
_start:
{
uint8_t v___y_17487__boxed_416_; uint8_t v_suppressElabErrors_boxed_417_; uint8_t v_res_418_; lean_object* v_r_419_; 
v___y_17487__boxed_416_ = lean_unbox(v___y_413_);
v_suppressElabErrors_boxed_417_ = lean_unbox(v_suppressElabErrors_414_);
v_res_418_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(v___y_17487__boxed_416_, v_suppressElabErrors_boxed_417_, v_x_415_);
lean_dec(v_x_415_);
v_r_419_ = lean_box(v_res_418_);
return v_r_419_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0(void){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_420_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0);
v___x_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
return v___x_422_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_423_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1);
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
lean_ctor_set(v___x_425_, 2, v___x_424_);
lean_ctor_set(v___x_425_, 3, v___x_424_);
lean_ctor_set(v___x_425_, 4, v___x_423_);
lean_ctor_set(v___x_425_, 5, v___x_423_);
lean_ctor_set(v___x_425_, 6, v___x_423_);
lean_ctor_set(v___x_425_, 7, v___x_423_);
lean_ctor_set(v___x_425_, 8, v___x_423_);
lean_ctor_set(v___x_425_, 9, v___x_423_);
lean_ctor_set(v___x_425_, 10, v___x_423_);
return v___x_425_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_426_ = lean_unsigned_to_nat(32u);
v___x_427_ = lean_mk_empty_array_with_capacity(v___x_426_);
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
return v___x_428_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4(void){
_start:
{
size_t v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_429_ = ((size_t)5ULL);
v___x_430_ = lean_unsigned_to_nat(0u);
v___x_431_ = lean_unsigned_to_nat(32u);
v___x_432_ = lean_mk_empty_array_with_capacity(v___x_431_);
v___x_433_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3);
v___x_434_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_434_, 0, v___x_433_);
lean_ctor_set(v___x_434_, 1, v___x_432_);
lean_ctor_set(v___x_434_, 2, v___x_430_);
lean_ctor_set(v___x_434_, 3, v___x_430_);
lean_ctor_set_usize(v___x_434_, 4, v___x_429_);
return v___x_434_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_435_ = lean_box(1);
v___x_436_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_437_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1);
v___x_438_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v___x_436_);
lean_ctor_set(v___x_438_, 2, v___x_435_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(lean_object* v_msgData_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v___x_443_; lean_object* v_env_444_; lean_object* v_options_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_443_ = lean_st_ref_get(v___y_441_);
v_env_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc_ref(v_env_444_);
lean_dec(v___x_443_);
v_options_445_ = lean_ctor_get(v___y_440_, 2);
v___x_446_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2);
v___x_447_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5);
lean_inc_ref(v_options_445_);
v___x_448_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_448_, 0, v_env_444_);
lean_ctor_set(v___x_448_, 1, v___x_446_);
lean_ctor_set(v___x_448_, 2, v___x_447_);
lean_ctor_set(v___x_448_, 3, v_options_445_);
v___x_449_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
lean_ctor_set(v___x_449_, 1, v_msgData_439_);
v___x_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___boxed(lean_object* v_msgData_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msgData_451_, v___y_452_, v___y_453_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(lean_object* v_ref_457_, lean_object* v_msgData_458_, uint8_t v_severity_459_, uint8_t v_isSilent_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v___y_465_; lean_object* v___y_466_; uint8_t v___y_467_; uint8_t v___y_468_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_501_; uint8_t v___y_502_; uint8_t v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; uint8_t v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_526_; uint8_t v___y_527_; uint8_t v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; uint8_t v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_537_; uint8_t v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; uint8_t v___y_541_; lean_object* v___y_542_; uint8_t v___y_543_; uint8_t v___x_548_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; uint8_t v___y_553_; lean_object* v___y_554_; uint8_t v___y_555_; uint8_t v___y_556_; uint8_t v___y_558_; uint8_t v___x_573_; 
v___x_548_ = 2;
v___x_573_ = l_Lean_instBEqMessageSeverity_beq(v_severity_459_, v___x_548_);
if (v___x_573_ == 0)
{
v___y_558_ = v___x_573_;
goto v___jp_557_;
}
else
{
uint8_t v___x_574_; 
lean_inc_ref(v_msgData_458_);
v___x_574_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_458_);
v___y_558_ = v___x_574_;
goto v___jp_557_;
}
v___jp_464_:
{
lean_object* v___x_474_; lean_object* v_currNamespace_475_; lean_object* v_openDecls_476_; lean_object* v_env_477_; lean_object* v_nextMacroScope_478_; lean_object* v_ngen_479_; lean_object* v_auxDeclNGen_480_; lean_object* v_traceState_481_; lean_object* v_cache_482_; lean_object* v_messages_483_; lean_object* v_infoState_484_; lean_object* v_snapshotTasks_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_499_; 
v___x_474_ = lean_st_ref_take(v___y_473_);
v_currNamespace_475_ = lean_ctor_get(v___y_472_, 6);
v_openDecls_476_ = lean_ctor_get(v___y_472_, 7);
v_env_477_ = lean_ctor_get(v___x_474_, 0);
v_nextMacroScope_478_ = lean_ctor_get(v___x_474_, 1);
v_ngen_479_ = lean_ctor_get(v___x_474_, 2);
v_auxDeclNGen_480_ = lean_ctor_get(v___x_474_, 3);
v_traceState_481_ = lean_ctor_get(v___x_474_, 4);
v_cache_482_ = lean_ctor_get(v___x_474_, 5);
v_messages_483_ = lean_ctor_get(v___x_474_, 6);
v_infoState_484_ = lean_ctor_get(v___x_474_, 7);
v_snapshotTasks_485_ = lean_ctor_get(v___x_474_, 8);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_499_ == 0)
{
v___x_487_ = v___x_474_;
v_isShared_488_ = v_isSharedCheck_499_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_snapshotTasks_485_);
lean_inc(v_infoState_484_);
lean_inc(v_messages_483_);
lean_inc(v_cache_482_);
lean_inc(v_traceState_481_);
lean_inc(v_auxDeclNGen_480_);
lean_inc(v_ngen_479_);
lean_inc(v_nextMacroScope_478_);
lean_inc(v_env_477_);
lean_dec(v___x_474_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_499_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_494_; 
lean_inc(v_openDecls_476_);
lean_inc(v_currNamespace_475_);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v_currNamespace_475_);
lean_ctor_set(v___x_489_, 1, v_openDecls_476_);
v___x_490_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v___y_465_);
lean_inc_ref(v___y_470_);
lean_inc_ref(v___y_469_);
v___x_491_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_491_, 0, v___y_469_);
lean_ctor_set(v___x_491_, 1, v___y_471_);
lean_ctor_set(v___x_491_, 2, v___y_466_);
lean_ctor_set(v___x_491_, 3, v___y_470_);
lean_ctor_set(v___x_491_, 4, v___x_490_);
lean_ctor_set_uint8(v___x_491_, sizeof(void*)*5, v___y_467_);
lean_ctor_set_uint8(v___x_491_, sizeof(void*)*5 + 1, v___y_468_);
lean_ctor_set_uint8(v___x_491_, sizeof(void*)*5 + 2, v_isSilent_460_);
v___x_492_ = l_Lean_MessageLog_add(v___x_491_, v_messages_483_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 6, v___x_492_);
v___x_494_ = v___x_487_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_env_477_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_nextMacroScope_478_);
lean_ctor_set(v_reuseFailAlloc_498_, 2, v_ngen_479_);
lean_ctor_set(v_reuseFailAlloc_498_, 3, v_auxDeclNGen_480_);
lean_ctor_set(v_reuseFailAlloc_498_, 4, v_traceState_481_);
lean_ctor_set(v_reuseFailAlloc_498_, 5, v_cache_482_);
lean_ctor_set(v_reuseFailAlloc_498_, 6, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_498_, 7, v_infoState_484_);
lean_ctor_set(v_reuseFailAlloc_498_, 8, v_snapshotTasks_485_);
v___x_494_ = v_reuseFailAlloc_498_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = lean_st_ref_put(v___y_473_, v___x_494_);
v___x_496_ = lean_box(0);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
}
}
v___jp_500_:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_524_; 
v___x_509_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_458_);
v___x_510_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v___x_509_, v___y_461_, v___y_462_);
v_a_511_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_524_ == 0)
{
v___x_513_ = v___x_510_;
v_isShared_514_ = v_isSharedCheck_524_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_510_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_524_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
lean_inc_ref_n(v___y_507_, 2);
v___x_515_ = l_Lean_FileMap_toPosition(v___y_507_, v___y_505_);
lean_dec(v___y_505_);
v___x_516_ = l_Lean_FileMap_toPosition(v___y_507_, v___y_508_);
lean_dec(v___y_508_);
v___x_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
v___x_518_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
if (v___y_506_ == 0)
{
lean_del_object(v___x_513_);
lean_dec_ref(v___y_501_);
v___y_465_ = v_a_511_;
v___y_466_ = v___x_517_;
v___y_467_ = v___y_502_;
v___y_468_ = v___y_503_;
v___y_469_ = v___y_504_;
v___y_470_ = v___x_518_;
v___y_471_ = v___x_515_;
v___y_472_ = v___y_461_;
v___y_473_ = v___y_462_;
goto v___jp_464_;
}
else
{
uint8_t v___x_519_; 
lean_inc(v_a_511_);
v___x_519_ = l_Lean_MessageData_hasTag(v___y_501_, v_a_511_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_522_; 
lean_dec_ref_known(v___x_517_, 1);
lean_dec_ref(v___x_515_);
lean_dec(v_a_511_);
v___x_520_ = lean_box(0);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 0, v___x_520_);
v___x_522_ = v___x_513_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
else
{
lean_del_object(v___x_513_);
v___y_465_ = v_a_511_;
v___y_466_ = v___x_517_;
v___y_467_ = v___y_502_;
v___y_468_ = v___y_503_;
v___y_469_ = v___y_504_;
v___y_470_ = v___x_518_;
v___y_471_ = v___x_515_;
v___y_472_ = v___y_461_;
v___y_473_ = v___y_462_;
goto v___jp_464_;
}
}
}
}
v___jp_525_:
{
lean_object* v___x_534_; 
v___x_534_ = l_Lean_Syntax_getTailPos_x3f(v___y_529_, v___y_527_);
lean_dec(v___y_529_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_inc(v___y_533_);
v___y_501_ = v___y_526_;
v___y_502_ = v___y_527_;
v___y_503_ = v___y_528_;
v___y_504_ = v___y_530_;
v___y_505_ = v___y_533_;
v___y_506_ = v___y_531_;
v___y_507_ = v___y_532_;
v___y_508_ = v___y_533_;
goto v___jp_500_;
}
else
{
lean_object* v_val_535_; 
v_val_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_val_535_);
lean_dec_ref_known(v___x_534_, 1);
v___y_501_ = v___y_526_;
v___y_502_ = v___y_527_;
v___y_503_ = v___y_528_;
v___y_504_ = v___y_530_;
v___y_505_ = v___y_533_;
v___y_506_ = v___y_531_;
v___y_507_ = v___y_532_;
v___y_508_ = v_val_535_;
goto v___jp_500_;
}
}
v___jp_536_:
{
lean_object* v_ref_544_; lean_object* v___x_545_; 
v_ref_544_ = l_Lean_replaceRef(v_ref_457_, v___y_539_);
v___x_545_ = l_Lean_Syntax_getPos_x3f(v_ref_544_, v___y_538_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v___x_546_; 
v___x_546_ = lean_unsigned_to_nat(0u);
v___y_526_ = v___y_537_;
v___y_527_ = v___y_538_;
v___y_528_ = v___y_543_;
v___y_529_ = v_ref_544_;
v___y_530_ = v___y_540_;
v___y_531_ = v___y_541_;
v___y_532_ = v___y_542_;
v___y_533_ = v___x_546_;
goto v___jp_525_;
}
else
{
lean_object* v_val_547_; 
v_val_547_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_val_547_);
lean_dec_ref_known(v___x_545_, 1);
v___y_526_ = v___y_537_;
v___y_527_ = v___y_538_;
v___y_528_ = v___y_543_;
v___y_529_ = v_ref_544_;
v___y_530_ = v___y_540_;
v___y_531_ = v___y_541_;
v___y_532_ = v___y_542_;
v___y_533_ = v_val_547_;
goto v___jp_525_;
}
}
v___jp_549_:
{
if (v___y_556_ == 0)
{
v___y_537_ = v___y_550_;
v___y_538_ = v___y_555_;
v___y_539_ = v___y_551_;
v___y_540_ = v___y_552_;
v___y_541_ = v___y_553_;
v___y_542_ = v___y_554_;
v___y_543_ = v_severity_459_;
goto v___jp_536_;
}
else
{
v___y_537_ = v___y_550_;
v___y_538_ = v___y_555_;
v___y_539_ = v___y_551_;
v___y_540_ = v___y_552_;
v___y_541_ = v___y_553_;
v___y_542_ = v___y_554_;
v___y_543_ = v___x_548_;
goto v___jp_536_;
}
}
v___jp_557_:
{
if (v___y_558_ == 0)
{
lean_object* v_fileName_559_; lean_object* v_fileMap_560_; lean_object* v_options_561_; lean_object* v_ref_562_; uint8_t v_suppressElabErrors_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___f_566_; uint8_t v___x_567_; uint8_t v___x_568_; 
v_fileName_559_ = lean_ctor_get(v___y_461_, 0);
v_fileMap_560_ = lean_ctor_get(v___y_461_, 1);
v_options_561_ = lean_ctor_get(v___y_461_, 2);
v_ref_562_ = lean_ctor_get(v___y_461_, 5);
v_suppressElabErrors_563_ = lean_ctor_get_uint8(v___y_461_, sizeof(void*)*14 + 1);
v___x_564_ = lean_box(v___y_558_);
v___x_565_ = lean_box(v_suppressElabErrors_563_);
v___f_566_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed), 3, 2);
lean_closure_set(v___f_566_, 0, v___x_564_);
lean_closure_set(v___f_566_, 1, v___x_565_);
v___x_567_ = 1;
v___x_568_ = l_Lean_instBEqMessageSeverity_beq(v_severity_459_, v___x_567_);
if (v___x_568_ == 0)
{
v___y_550_ = v___f_566_;
v___y_551_ = v_ref_562_;
v___y_552_ = v_fileName_559_;
v___y_553_ = v_suppressElabErrors_563_;
v___y_554_ = v_fileMap_560_;
v___y_555_ = v___y_558_;
v___y_556_ = v___x_568_;
goto v___jp_549_;
}
else
{
lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_569_ = l_Lean_warningAsError;
v___x_570_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_561_, v___x_569_);
v___y_550_ = v___f_566_;
v___y_551_ = v_ref_562_;
v___y_552_ = v_fileName_559_;
v___y_553_ = v_suppressElabErrors_563_;
v___y_554_ = v_fileMap_560_;
v___y_555_ = v___y_558_;
v___y_556_ = v___x_570_;
goto v___jp_549_;
}
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec_ref(v_msgData_458_);
v___x_571_ = lean_box(0);
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___boxed(lean_object* v_ref_575_, lean_object* v_msgData_576_, lean_object* v_severity_577_, lean_object* v_isSilent_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
uint8_t v_severity_boxed_582_; uint8_t v_isSilent_boxed_583_; lean_object* v_res_584_; 
v_severity_boxed_582_ = lean_unbox(v_severity_577_);
v_isSilent_boxed_583_ = lean_unbox(v_isSilent_578_);
v_res_584_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_575_, v_msgData_576_, v_severity_boxed_582_, v_isSilent_boxed_583_, v___y_579_, v___y_580_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v_ref_575_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(lean_object* v_msgData_585_, uint8_t v_severity_586_, uint8_t v_isSilent_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v_ref_591_; lean_object* v___x_592_; 
v_ref_591_ = lean_ctor_get(v___y_588_, 5);
v___x_592_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_591_, v_msgData_585_, v_severity_586_, v_isSilent_587_, v___y_588_, v___y_589_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4___boxed(lean_object* v_msgData_593_, lean_object* v_severity_594_, lean_object* v_isSilent_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
uint8_t v_severity_boxed_599_; uint8_t v_isSilent_boxed_600_; lean_object* v_res_601_; 
v_severity_boxed_599_ = lean_unbox(v_severity_594_);
v_isSilent_boxed_600_ = lean_unbox(v_isSilent_595_);
v_res_601_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_593_, v_severity_boxed_599_, v_isSilent_boxed_600_, v___y_596_, v___y_597_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(lean_object* v_msgData_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
uint8_t v___x_606_; uint8_t v___x_607_; lean_object* v___x_608_; 
v___x_606_ = 1;
v___x_607_ = 0;
v___x_608_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_602_, v___x_606_, v___x_607_, v___y_603_, v___y_604_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2___boxed(lean_object* v_msgData_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v_msgData_609_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(lean_object* v_fn_614_, lean_object* v_e_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_Expr_getSorry_x3f(v_e_615_);
if (lean_obj_tag(v___x_622_) == 1)
{
lean_object* v_val_623_; lean_object* v___x_624_; 
v_val_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_val_623_);
lean_dec_ref_known(v___x_622_, 1);
lean_inc(v___y_620_);
lean_inc_ref(v___y_619_);
lean_inc(v___y_618_);
lean_inc_ref(v___y_617_);
lean_inc(v___y_616_);
v___x_624_ = lean_apply_7(v_fn_614_, v_val_623_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, lean_box(0));
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_633_; 
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_633_ == 0)
{
lean_object* v_unused_634_; 
v_unused_634_ = lean_ctor_get(v___x_624_, 0);
lean_dec(v_unused_634_);
v___x_626_ = v___x_624_;
v_isShared_627_ = v_isSharedCheck_633_;
goto v_resetjp_625_;
}
else
{
lean_dec(v___x_624_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_633_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
uint8_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_628_ = 0;
v___x_629_ = lean_box(v___x_628_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 0, v___x_629_);
v___x_631_ = v___x_626_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
else
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
v_a_635_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_624_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_624_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
else
{
uint8_t v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
lean_dec(v___x_622_);
lean_dec_ref(v_fn_614_);
v___x_643_ = 1;
v___x_644_ = lean_box(v___x_643_);
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
return v___x_645_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed(lean_object* v_fn_646_, lean_object* v_e_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(v_fn_646_, v_e_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v_e_647_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_object* v_00_u03b1_655_, lean_object* v_x_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = lean_apply_1(v_x_656_, lean_box(0));
v___x_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v_00_u03b1_665_, lean_object* v_x_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(v_00_u03b1_665_, v_x_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20_spec__22___redArg___lam__0(lean_object* v_k_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v_b_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v___x_683_; 
lean_inc(v___y_681_);
lean_inc_ref(v___y_680_);
lean_inc(v___y_679_);
lean_inc_ref(v___y_678_);
lean_inc(v___y_676_);
lean_inc(v___y_675_);
v___x_683_ = lean_apply_8(v_k_674_, v_b_677_, v___y_675_, v___y_676_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, lean_box(0));
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20_spec__22___redArg___lam__0___boxed(lean_object* v_k_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v_b_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20_spec__22___redArg___lam__0(v_k_684_, v___y_685_, v___y_686_, v_b_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_686_);
lean_dec(v___y_685_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13_spec__24_spec__27___redArg(lean_object* v_name_694_, lean_object* v_type_695_, lean_object* v_val_696_, lean_object* v_k_697_, uint8_t v_nondep_698_, uint8_t v_kind_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v___f_707_; lean_object* v___x_708_; 
lean_inc(v___y_701_);
lean_inc(v___y_700_);
v___f_707_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_707_, 0, v_k_697_);
lean_closure_set(v___f_707_, 1, v___y_700_);
lean_closure_set(v___f_707_, 2, v___y_701_);
v___x_708_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_694_, v_type_695_, v_val_696_, v___f_707_, v_nondep_698_, v_kind_699_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
if (lean_obj_tag(v___x_708_) == 0)
{
return v___x_708_;
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_708_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_708_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13_spec__24_spec__27___redArg___boxed(lean_object* v_name_717_, lean_object* v_type_718_, lean_object* v_val_719_, lean_object* v_k_720_, lean_object* v_nondep_721_, lean_object* v_kind_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
uint8_t v_nondep_boxed_730_; uint8_t v_kind_boxed_731_; lean_object* v_res_732_; 
v_nondep_boxed_730_ = lean_unbox(v_nondep_721_);
v_kind_boxed_731_ = lean_unbox(v_kind_722_);
v_res_732_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13_spec__24_spec__27___redArg(v_name_717_, v_type_718_, v_val_719_, v_k_720_, v_nondep_boxed_730_, v_kind_boxed_731_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec(v___y_723_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13_spec__24___lam__0___boxed(lean_object* v_fvars_733_, lean_object* v_f_734_, lean_object* v_body_735_, lean_object* v_x_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13_spec__24___lam__0(v_fvars_733_, v_f_734_, v_body_735_, v_x_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec(v___y_737_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13_spec__24(lean_object* v_f_745_, lean_object* v_fvars_746_, lean_object* v_a_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
if (lean_obj_tag(v_a_747_) == 8)
{
lean_object* v_declName_755_; lean_object* v_type_756_; lean_object* v_value_757_; lean_object* v_body_758_; lean_object* v_d_759_; lean_object* v___x_760_; 
v_declName_755_ = lean_ctor_get(v_a_747_, 0);
lean_inc(v_declName_755_);
v_type_756_ = lean_ctor_get(v_a_747_, 1);
lean_inc_ref(v_type_756_);
v_value_757_ = lean_ctor_get(v_a_747_, 2);
lean_inc_ref(v_value_757_);
v_body_758_ = lean_ctor_get(v_a_747_, 3);
lean_inc_ref(v_body_758_);
lean_dec_ref_known(v_a_747_, 4);
v_d_759_ = lean_expr_instantiate_rev(v_type_756_, v_fvars_746_);
lean_dec_ref(v_type_756_);
lean_inc_ref(v_f_745_);
lean_inc(v___y_753_);
lean_inc_ref(v___y_752_);
lean_inc(v___y_751_);
lean_inc_ref(v___y_750_);
lean_inc(v___y_749_);
lean_inc(v___y_748_);
lean_inc_ref(v_d_759_);
v___x_760_ = lean_apply_8(v_f_745_, v_d_759_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, lean_box(0));
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_v_761_; lean_object* v___x_762_; 
lean_dec_ref_known(v___x_760_, 1);
v_v_761_ = lean_expr_instantiate_rev(v_value_757_, v_fvars_746_);
lean_dec_ref(v_value_757_);
lean_inc_ref(v_f_745_);
lean_inc(v___y_753_);
lean_inc_ref(v___y_752_);
lean_inc(v___y_751_);
lean_inc_ref(v___y_750_);
lean_inc(v___y_749_);
lean_inc(v___y_748_);
lean_inc_ref(v_v_761_);
v___x_762_ = lean_apply_8(v_f_745_, v_v_761_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, lean_box(0));
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v___f_763_; uint8_t v___x_764_; uint8_t v___x_765_; lean_object* v___x_766_; 
lean_dec_ref_known(v___x_762_, 1);
v___f_763_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13_spec__24___lam__0___boxed), 11, 3);
lean_closure_set(v___f_763_, 0, v_fvars_746_);
lean_closure_set(v___f_763_, 1, v_f_745_);
lean_closure_set(v___f_763_, 2, v_body_758_);
v___x_764_ = 0;
v___x_765_ = 0;
v___x_766_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13_spec__24_spec__27___redArg(v_declName_755_, v_d_759_, v_v_761_, v___f_763_, v___x_764_, v___x_765_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
return v___x_766_;
}
else
{
lean_dec_ref(v_v_761_);
lean_dec_ref(v_d_759_);
lean_dec_ref(v_body_758_);
lean_dec(v_declName_755_);
lean_dec_ref(v_fvars_746_);
lean_dec_ref(v_f_745_);
return v___x_762_;
}
}
else
{
lean_dec_ref(v_d_759_);
lean_dec_ref(v_body_758_);
lean_dec_ref(v_value_757_);
lean_dec(v_declName_755_);
lean_dec_ref(v_fvars_746_);
lean_dec_ref(v_f_745_);
return v___x_760_;
}
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_expr_instantiate_rev(v_a_747_, v_fvars_746_);
lean_dec_ref(v_fvars_746_);
lean_dec_ref(v_a_747_);
lean_inc(v___y_753_);
lean_inc_ref(v___y_752_);
lean_inc(v___y_751_);
lean_inc_ref(v___y_750_);
lean_inc(v___y_749_);
lean_inc(v___y_748_);
v___x_768_ = lean_apply_8(v_f_745_, v___x_767_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, lean_box(0));
return v___x_768_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13_spec__24___lam__0(lean_object* v_fvars_769_, lean_object* v_f_770_, lean_object* v_body_771_, lean_object* v_x_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_array_push(v_fvars_769_, v_x_772_);
v___x_781_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13_spec__24(v_f_770_, v___x_780_, v_body_771_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13_spec__24___boxed(lean_object* v_f_782_, lean_object* v_fvars_783_, lean_object* v_a_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13_spec__24(v_f_782_, v_fvars_783_, v_a_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec(v___y_785_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13(lean_object* v_f_795_, lean_object* v_e_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13___closed__0));
v___x_805_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13_spec__24(v_f_795_, v___x_804_, v_e_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13___boxed(lean_object* v_f_806_, lean_object* v_e_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13(v_f_806_, v_e_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec(v___y_808_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(lean_object* v_m_816_, lean_object* v_query_817_, lean_object* v_x_818_, lean_object* v_x_819_, lean_object* v_x_820_){
_start:
{
lean_object* v_zero_821_; uint8_t v_isZero_822_; 
v_zero_821_ = lean_unsigned_to_nat(0u);
v_isZero_822_ = lean_nat_dec_eq(v_x_819_, v_zero_821_);
if (v_isZero_822_ == 1)
{
lean_dec(v_x_820_);
lean_dec(v_x_819_);
if (lean_obj_tag(v_x_818_) == 0)
{
lean_object* v___x_823_; 
v___x_823_ = lean_box(2);
return v___x_823_;
}
else
{
lean_object* v_val_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
v_val_824_ = lean_ctor_get(v_x_818_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v_x_818_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v_x_818_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_val_824_);
lean_dec(v_x_818_);
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
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_val_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
else
{
lean_object* v_keyArray_832_; lean_object* v_valueArray_833_; lean_object* v___x_834_; uint8_t v_isSome_835_; 
v_keyArray_832_ = lean_ctor_get(v_m_816_, 1);
v_valueArray_833_ = lean_ctor_get(v_m_816_, 2);
v___x_834_ = lean_array_fget_borrowed(v_keyArray_832_, v_x_820_);
v_isSome_835_ = lean_noption_is_some(v___x_834_);
if (v_isSome_835_ == 0)
{
lean_dec(v_x_819_);
if (lean_obj_tag(v_x_818_) == 0)
{
lean_object* v___x_836_; 
v___x_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_836_, 0, v_x_820_);
return v___x_836_;
}
else
{
lean_object* v_val_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_dec(v_x_820_);
v_val_837_ = lean_ctor_get(v_x_818_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v_x_818_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v_x_818_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_val_837_);
lean_dec(v_x_818_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_val_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
else
{
lean_object* v_one_845_; lean_object* v_n_846_; lean_object* v___y_848_; 
v_one_845_ = lean_unsigned_to_nat(1u);
v_n_846_ = lean_nat_sub(v_x_819_, v_one_845_);
lean_dec(v_x_819_);
if (v_isSome_835_ == 0)
{
goto v___jp_854_;
}
else
{
lean_object* v___x_856_; uint8_t v_isSome_857_; 
v___x_856_ = lean_array_fget_borrowed(v_valueArray_833_, v_x_820_);
v_isSome_857_ = lean_noption_is_some(v___x_856_);
if (v_isSome_857_ == 0)
{
goto v___jp_854_;
}
else
{
lean_object* v_val_858_; uint8_t v___x_859_; 
lean_inc(v___x_834_);
v_val_858_ = lean_noption_get(v___x_834_);
v___x_859_ = lean_expr_eqv(v_val_858_, v_query_817_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; lean_object* v___x_861_; uint8_t v___x_862_; 
lean_dec(v_val_858_);
v___x_860_ = lean_array_get_size(v_keyArray_832_);
v___x_861_ = lean_nat_add(v_x_820_, v_one_845_);
lean_dec(v_x_820_);
v___x_862_ = lean_nat_dec_lt(v___x_861_, v___x_860_);
if (v___x_862_ == 0)
{
lean_dec(v___x_861_);
v_x_819_ = v_n_846_;
v_x_820_ = v_zero_821_;
goto _start;
}
else
{
v_x_819_ = v_n_846_;
v_x_820_ = v___x_861_;
goto _start;
}
}
else
{
lean_object* v_val_865_; lean_object* v___x_866_; 
lean_dec(v_n_846_);
lean_dec(v_x_818_);
lean_inc(v___x_856_);
v_val_865_ = lean_noption_get(v___x_856_);
v___x_866_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_866_, 0, v_x_820_);
lean_ctor_set(v___x_866_, 1, v_val_858_);
lean_ctor_set(v___x_866_, 2, v_val_865_);
return v___x_866_;
}
}
}
v___jp_847_:
{
lean_object* v___x_849_; lean_object* v___x_850_; uint8_t v___x_851_; 
v___x_849_ = lean_array_get_size(v_keyArray_832_);
v___x_850_ = lean_nat_add(v_x_820_, v_one_845_);
lean_dec(v_x_820_);
v___x_851_ = lean_nat_dec_lt(v___x_850_, v___x_849_);
if (v___x_851_ == 0)
{
lean_dec(v___x_850_);
v_x_818_ = v___y_848_;
v_x_819_ = v_n_846_;
v_x_820_ = v_zero_821_;
goto _start;
}
else
{
v_x_818_ = v___y_848_;
v_x_819_ = v_n_846_;
v_x_820_ = v___x_850_;
goto _start;
}
}
v___jp_854_:
{
if (lean_obj_tag(v_x_818_) == 0)
{
lean_object* v___x_855_; 
lean_inc(v_x_820_);
v___x_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_855_, 0, v_x_820_);
v___y_848_ = v___x_855_;
goto v___jp_847_;
}
else
{
v___y_848_ = v_x_818_;
goto v___jp_847_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg___boxed(lean_object* v_m_867_, lean_object* v_query_868_, lean_object* v_x_869_, lean_object* v_x_870_, lean_object* v_x_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_m_867_, v_query_868_, v_x_869_, v_x_870_, v_x_871_);
lean_dec_ref(v_query_868_);
lean_dec_ref(v_m_867_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(lean_object* v_m_873_, lean_object* v_query_874_){
_start:
{
lean_object* v_keyArray_875_; lean_object* v___x_876_; uint64_t v___x_877_; uint64_t v___x_878_; uint64_t v___x_879_; uint64_t v_fold_880_; uint64_t v___x_881_; uint64_t v___x_882_; uint64_t v___x_883_; size_t v___x_884_; size_t v___x_885_; size_t v___x_886_; size_t v___x_887_; size_t v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v_keyArray_875_ = lean_ctor_get(v_m_873_, 1);
v___x_876_ = lean_array_get_size(v_keyArray_875_);
v___x_877_ = l_Lean_Expr_hash(v_query_874_);
v___x_878_ = 32ULL;
v___x_879_ = lean_uint64_shift_right(v___x_877_, v___x_878_);
v_fold_880_ = lean_uint64_xor(v___x_877_, v___x_879_);
v___x_881_ = 16ULL;
v___x_882_ = lean_uint64_shift_right(v_fold_880_, v___x_881_);
v___x_883_ = lean_uint64_xor(v_fold_880_, v___x_882_);
v___x_884_ = lean_uint64_to_usize(v___x_883_);
v___x_885_ = lean_usize_of_nat(v___x_876_);
v___x_886_ = ((size_t)1ULL);
v___x_887_ = lean_usize_sub(v___x_885_, v___x_886_);
v___x_888_ = lean_usize_land(v___x_884_, v___x_887_);
v___x_889_ = lean_usize_to_nat(v___x_888_);
v___x_890_ = lean_box(0);
v___x_891_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_m_873_, v_query_874_, v___x_890_, v___x_876_, v___x_889_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg___boxed(lean_object* v_m_892_, lean_object* v_query_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_m_892_, v_query_893_);
lean_dec_ref(v_query_893_);
lean_dec_ref(v_m_892_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(lean_object* v_m_895_, lean_object* v_query_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_m_895_, v_query_896_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_index_898_; lean_object* v_key_899_; lean_object* v_value_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
v_index_898_ = lean_ctor_get(v___x_897_, 0);
v_key_899_ = lean_ctor_get(v___x_897_, 1);
v_value_900_ = lean_ctor_get(v___x_897_, 2);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_897_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_value_900_);
lean_inc(v_key_899_);
lean_inc(v_index_898_);
lean_dec(v___x_897_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_index_898_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_key_899_);
lean_ctor_set(v_reuseFailAlloc_906_, 2, v_value_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
else
{
lean_object* v___x_908_; 
lean_dec(v___x_897_);
v___x_908_ = lean_box(1);
return v___x_908_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_m_909_, lean_object* v_query_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_m_909_, v_query_910_);
lean_dec_ref(v_query_910_);
lean_dec_ref(v_m_909_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_m_912_, lean_object* v_a_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_m_912_, v_a_913_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_value_915_; lean_object* v___x_916_; 
v_value_915_ = lean_ctor_get(v___x_914_, 2);
lean_inc(v_value_915_);
lean_dec_ref_known(v___x_914_, 3);
v___x_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_916_, 0, v_value_915_);
return v___x_916_;
}
else
{
lean_object* v___x_917_; 
v___x_917_ = lean_box(0);
return v___x_917_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_m_918_, lean_object* v_a_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_918_, v_a_919_);
lean_dec_ref(v_a_919_);
lean_dec_ref(v_m_918_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_object* v_00_u03b1_921_, lean_object* v_x_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = lean_apply_1(v_x_922_, lean_box(0));
v___x_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0___boxed(lean_object* v_00_u03b1_931_, lean_object* v_x_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(v_00_u03b1_931_, v_x_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20_spec__22___redArg(lean_object* v_name_940_, uint8_t v_bi_941_, lean_object* v_type_942_, lean_object* v_k_943_, uint8_t v_kind_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v___f_952_; lean_object* v___x_953_; 
lean_inc(v___y_946_);
lean_inc(v___y_945_);
v___f_952_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_952_, 0, v_k_943_);
lean_closure_set(v___f_952_, 1, v___y_945_);
lean_closure_set(v___f_952_, 2, v___y_946_);
v___x_953_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_940_, v_bi_941_, v_type_942_, v___f_952_, v_kind_944_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
if (lean_obj_tag(v___x_953_) == 0)
{
return v___x_953_;
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_953_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_953_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20_spec__22___redArg___boxed(lean_object* v_name_962_, lean_object* v_bi_963_, lean_object* v_type_964_, lean_object* v_k_965_, lean_object* v_kind_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
uint8_t v_bi_boxed_974_; uint8_t v_kind_boxed_975_; lean_object* v_res_976_; 
v_bi_boxed_974_ = lean_unbox(v_bi_963_);
v_kind_boxed_975_ = lean_unbox(v_kind_966_);
v_res_976_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20_spec__22___redArg(v_name_962_, v_bi_boxed_974_, v_type_964_, v_k_965_, v_kind_boxed_975_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec(v___y_967_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__22___lam__0___boxed(lean_object* v_fvars_977_, lean_object* v_f_978_, lean_object* v_body_979_, lean_object* v_x_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__22___lam__0(v_fvars_977_, v_f_978_, v_body_979_, v_x_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec(v___y_981_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__22(lean_object* v_f_989_, lean_object* v_fvars_990_, lean_object* v_a_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
if (lean_obj_tag(v_a_991_) == 6)
{
lean_object* v_binderName_999_; lean_object* v_binderType_1000_; lean_object* v_body_1001_; uint8_t v_binderInfo_1002_; lean_object* v_d_1003_; lean_object* v___x_1004_; 
v_binderName_999_ = lean_ctor_get(v_a_991_, 0);
lean_inc(v_binderName_999_);
v_binderType_1000_ = lean_ctor_get(v_a_991_, 1);
lean_inc_ref(v_binderType_1000_);
v_body_1001_ = lean_ctor_get(v_a_991_, 2);
lean_inc_ref(v_body_1001_);
v_binderInfo_1002_ = lean_ctor_get_uint8(v_a_991_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_991_, 3);
v_d_1003_ = lean_expr_instantiate_rev(v_binderType_1000_, v_fvars_990_);
lean_dec_ref(v_binderType_1000_);
lean_inc_ref(v_f_989_);
lean_inc(v___y_997_);
lean_inc_ref(v___y_996_);
lean_inc(v___y_995_);
lean_inc_ref(v___y_994_);
lean_inc(v___y_993_);
lean_inc(v___y_992_);
lean_inc_ref(v_d_1003_);
v___x_1004_ = lean_apply_8(v_f_989_, v_d_1003_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, lean_box(0));
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v___f_1005_; uint8_t v___x_1006_; lean_object* v___x_1007_; 
lean_dec_ref_known(v___x_1004_, 1);
v___f_1005_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__22___lam__0___boxed), 11, 3);
lean_closure_set(v___f_1005_, 0, v_fvars_990_);
lean_closure_set(v___f_1005_, 1, v_f_989_);
lean_closure_set(v___f_1005_, 2, v_body_1001_);
v___x_1006_ = 0;
v___x_1007_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20_spec__22___redArg(v_binderName_999_, v_binderInfo_1002_, v_d_1003_, v___f_1005_, v___x_1006_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
return v___x_1007_;
}
else
{
lean_dec_ref(v_d_1003_);
lean_dec_ref(v_body_1001_);
lean_dec(v_binderName_999_);
lean_dec_ref(v_fvars_990_);
lean_dec_ref(v_f_989_);
return v___x_1004_;
}
}
else
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = lean_expr_instantiate_rev(v_a_991_, v_fvars_990_);
lean_dec_ref(v_fvars_990_);
lean_dec_ref(v_a_991_);
lean_inc(v___y_997_);
lean_inc_ref(v___y_996_);
lean_inc(v___y_995_);
lean_inc_ref(v___y_994_);
lean_inc(v___y_993_);
lean_inc(v___y_992_);
v___x_1009_ = lean_apply_8(v_f_989_, v___x_1008_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, lean_box(0));
return v___x_1009_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__22___lam__0(lean_object* v_fvars_1010_, lean_object* v_f_1011_, lean_object* v_body_1012_, lean_object* v_x_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = lean_array_push(v_fvars_1010_, v_x_1013_);
v___x_1022_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__22(v_f_1011_, v___x_1021_, v_body_1012_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__22___boxed(lean_object* v_f_1023_, lean_object* v_fvars_1024_, lean_object* v_a_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__22(v_f_1023_, v_fvars_1024_, v_a_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec(v___y_1026_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(lean_object* v_f_1034_, lean_object* v_e_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13___closed__0));
v___x_1044_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__22(v_f_1034_, v___x_1043_, v_e_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___boxed(lean_object* v_f_1045_, lean_object* v_e_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v_f_1045_, v_e_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec(v___y_1047_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__18_spec__19___redArg(lean_object* v_b_1055_, lean_object* v_acc_1056_, lean_object* v_i_1057_){
_start:
{
lean_object* v___y_1059_; lean_object* v_keyArray_1067_; lean_object* v_valueArray_1068_; lean_object* v___x_1069_; uint8_t v___x_1070_; 
v_keyArray_1067_ = lean_ctor_get(v_b_1055_, 1);
v_valueArray_1068_ = lean_ctor_get(v_b_1055_, 2);
v___x_1069_ = lean_array_get_size(v_keyArray_1067_);
v___x_1070_ = lean_nat_dec_lt(v_i_1057_, v___x_1069_);
if (v___x_1070_ == 0)
{
lean_dec(v_i_1057_);
return v_acc_1056_;
}
else
{
lean_object* v___x_1071_; uint8_t v_isSome_1072_; 
v___x_1071_ = lean_array_fget_borrowed(v_keyArray_1067_, v_i_1057_);
v_isSome_1072_ = lean_noption_is_some(v___x_1071_);
if (v_isSome_1072_ == 0)
{
goto v___jp_1063_;
}
else
{
lean_object* v___x_1073_; uint8_t v_isSome_1074_; 
v___x_1073_ = lean_array_fget_borrowed(v_valueArray_1068_, v_i_1057_);
v_isSome_1074_ = lean_noption_is_some(v___x_1073_);
if (v_isSome_1074_ == 0)
{
goto v___jp_1063_;
}
else
{
lean_object* v_val_1075_; lean_object* v_val_1076_; lean_object* v_i_1078_; lean_object* v___x_1083_; 
lean_inc(v___x_1071_);
v_val_1075_ = lean_noption_get(v___x_1071_);
lean_inc(v___x_1073_);
v_val_1076_ = lean_noption_get(v___x_1073_);
v___x_1083_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_acc_1056_, v_val_1075_);
switch(lean_obj_tag(v___x_1083_))
{
case 0:
{
lean_object* v_index_1084_; lean_object* v_size_1085_; lean_object* v___x_1086_; 
v_index_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_index_1084_);
lean_dec_ref_known(v___x_1083_, 3);
v_size_1085_ = lean_ctor_get(v_acc_1056_, 0);
lean_inc(v_size_1085_);
v___x_1086_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1056_, v_size_1085_, v_index_1084_, v_val_1075_, v_val_1076_);
lean_dec(v_index_1084_);
v___y_1059_ = v___x_1086_;
goto v___jp_1058_;
}
case 1:
{
lean_object* v_index_1087_; 
v_index_1087_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_index_1087_);
lean_dec_ref_known(v___x_1083_, 1);
v_i_1078_ = v_index_1087_;
goto v___jp_1077_;
}
default: 
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = lean_unsigned_to_nat(0u);
v___x_1089_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1056_, v___x_1088_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_index_1090_; 
v_index_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_index_1090_);
lean_dec_ref_known(v___x_1089_, 1);
v_i_1078_ = v_index_1090_;
goto v___jp_1077_;
}
else
{
lean_dec(v_val_1076_);
lean_dec(v_val_1075_);
v___y_1059_ = v_acc_1056_;
goto v___jp_1058_;
}
}
}
v___jp_1077_:
{
lean_object* v_size_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v_size_1079_ = lean_ctor_get(v_acc_1056_, 0);
v___x_1080_ = lean_unsigned_to_nat(1u);
v___x_1081_ = lean_nat_add(v_size_1079_, v___x_1080_);
v___x_1082_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1056_, v___x_1081_, v_i_1078_, v_val_1075_, v_val_1076_);
lean_dec(v_i_1078_);
v___y_1059_ = v___x_1082_;
goto v___jp_1058_;
}
}
}
}
v___jp_1058_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_unsigned_to_nat(1u);
v___x_1061_ = lean_nat_add(v_i_1057_, v___x_1060_);
lean_dec(v_i_1057_);
v_acc_1056_ = v___y_1059_;
v_i_1057_ = v___x_1061_;
goto _start;
}
v___jp_1063_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_unsigned_to_nat(1u);
v___x_1065_ = lean_nat_add(v_i_1057_, v___x_1064_);
lean_dec(v_i_1057_);
v_i_1057_ = v___x_1065_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__18_spec__19___redArg___boxed(lean_object* v_b_1091_, lean_object* v_acc_1092_, lean_object* v_i_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__18_spec__19___redArg(v_b_1091_, v_acc_1092_, v_i_1093_);
lean_dec_ref(v_b_1091_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__18___redArg(lean_object* v_init_1095_, lean_object* v_b_1096_){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = lean_unsigned_to_nat(0u);
v___x_1098_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__18_spec__19___redArg(v_b_1096_, v_init_1095_, v___x_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__18___redArg___boxed(lean_object* v_init_1099_, lean_object* v_b_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__18___redArg(v_init_1099_, v_b_1100_);
lean_dec_ref(v_b_1100_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10___redArg(lean_object* v_m_1102_){
_start:
{
lean_object* v_keyArray_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v_cellCount_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v_target_1110_; lean_object* v___x_1111_; 
v_keyArray_1103_ = lean_ctor_get(v_m_1102_, 1);
v___x_1104_ = lean_array_get_size(v_keyArray_1103_);
v___x_1105_ = lean_unsigned_to_nat(2u);
v_cellCount_1106_ = lean_nat_mul(v___x_1104_, v___x_1105_);
v___x_1107_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1106_);
v___x_1108_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1106_);
v___x_1109_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1106_);
v_target_1110_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1110_, 0, v___x_1107_);
lean_ctor_set(v_target_1110_, 1, v___x_1108_);
lean_ctor_set(v_target_1110_, 2, v___x_1109_);
v___x_1111_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__18___redArg(v_target_1110_, v_m_1102_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10___redArg___boxed(lean_object* v_m_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10___redArg(v_m_1112_);
lean_dec_ref(v_m_1112_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(lean_object* v_a_1114_, lean_object* v_e_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___y_1121_; lean_object* v___y_1124_; lean_object* v_i_1125_; lean_object* v___y_1141_; lean_object* v_i_1142_; lean_object* v___y_1148_; lean_object* v___x_1157_; 
v___x_1118_ = lean_st_ref_take(v_a_1114_);
v___x_1119_ = lean_box(0);
v___x_1157_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v___x_1118_, v_e_1115_);
switch(lean_obj_tag(v___x_1157_))
{
case 0:
{
lean_object* v_index_1158_; lean_object* v_size_1159_; lean_object* v___x_1160_; 
v_index_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_index_1158_);
lean_dec_ref_known(v___x_1157_, 3);
v_size_1159_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_size_1159_);
v___x_1160_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1118_, v_size_1159_, v_index_1158_, v_e_1115_, v_a_1116_);
lean_dec(v_index_1158_);
v___y_1121_ = v___x_1160_;
goto v___jp_1120_;
}
case 1:
{
lean_object* v_index_1161_; lean_object* v_size_1162_; lean_object* v_keyArray_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; uint8_t v___x_1167_; 
v_index_1161_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_index_1161_);
lean_dec_ref_known(v___x_1157_, 1);
v_size_1162_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_size_1162_);
v_keyArray_1163_ = lean_ctor_get(v___x_1118_, 1);
lean_inc_ref(v_keyArray_1163_);
v___x_1164_ = lean_unsigned_to_nat(1u);
v___x_1165_ = lean_nat_add(v_size_1162_, v___x_1164_);
lean_dec(v_size_1162_);
v___x_1166_ = lean_array_get_size(v_keyArray_1163_);
lean_dec_ref(v_keyArray_1163_);
v___x_1167_ = lean_nat_dec_lt(v___x_1165_, v___x_1166_);
if (v___x_1167_ == 0)
{
lean_dec(v___x_1165_);
lean_dec(v_index_1161_);
goto v___jp_1130_;
}
else
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___x_1168_ = lean_unsigned_to_nat(4u);
v___x_1169_ = lean_nat_mul(v___x_1165_, v___x_1168_);
v___x_1170_ = lean_unsigned_to_nat(3u);
v___x_1171_ = lean_nat_mul(v___x_1166_, v___x_1170_);
v___x_1172_ = lean_nat_dec_le(v___x_1169_, v___x_1171_);
lean_dec(v___x_1171_);
lean_dec(v___x_1169_);
if (v___x_1172_ == 0)
{
lean_dec(v___x_1165_);
lean_dec(v_index_1161_);
goto v___jp_1130_;
}
else
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1118_, v___x_1165_, v_index_1161_, v_e_1115_, v_a_1116_);
lean_dec(v_index_1161_);
v___y_1121_ = v___x_1173_;
goto v___jp_1120_;
}
}
}
default: 
{
lean_object* v_size_1174_; lean_object* v_keyArray_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v_size_1174_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_size_1174_);
v_keyArray_1175_ = lean_ctor_get(v___x_1118_, 1);
lean_inc_ref(v_keyArray_1175_);
v___x_1176_ = lean_unsigned_to_nat(1u);
v___x_1177_ = lean_nat_add(v_size_1174_, v___x_1176_);
lean_dec(v_size_1174_);
v___x_1178_ = lean_array_get_size(v_keyArray_1175_);
lean_dec_ref(v_keyArray_1175_);
v___x_1179_ = lean_nat_dec_lt(v___x_1177_, v___x_1178_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; 
lean_dec(v___x_1177_);
v___x_1180_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10___redArg(v___x_1118_);
lean_dec(v___x_1118_);
v___y_1148_ = v___x_1180_;
goto v___jp_1147_;
}
else
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; uint8_t v___x_1185_; 
v___x_1181_ = lean_unsigned_to_nat(4u);
v___x_1182_ = lean_nat_mul(v___x_1177_, v___x_1181_);
lean_dec(v___x_1177_);
v___x_1183_ = lean_unsigned_to_nat(3u);
v___x_1184_ = lean_nat_mul(v___x_1178_, v___x_1183_);
v___x_1185_ = lean_nat_dec_le(v___x_1182_, v___x_1184_);
lean_dec(v___x_1184_);
lean_dec(v___x_1182_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10___redArg(v___x_1118_);
lean_dec(v___x_1118_);
v___y_1148_ = v___x_1186_;
goto v___jp_1147_;
}
else
{
v___y_1148_ = v___x_1118_;
goto v___jp_1147_;
}
}
}
}
v___jp_1120_:
{
lean_object* v___x_1122_; 
v___x_1122_ = lean_st_ref_put(v_a_1114_, v___y_1121_);
return v___x_1119_;
}
v___jp_1123_:
{
lean_object* v_size_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v_size_1126_ = lean_ctor_get(v___y_1124_, 0);
v___x_1127_ = lean_unsigned_to_nat(1u);
v___x_1128_ = lean_nat_add(v_size_1126_, v___x_1127_);
v___x_1129_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1124_, v___x_1128_, v_i_1125_, v_e_1115_, v_a_1116_);
lean_dec(v_i_1125_);
v___y_1121_ = v___x_1129_;
goto v___jp_1120_;
}
v___jp_1130_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10___redArg(v___x_1118_);
lean_dec(v___x_1118_);
v___x_1132_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v___x_1131_, v_e_1115_);
switch(lean_obj_tag(v___x_1132_))
{
case 0:
{
lean_object* v_index_1133_; lean_object* v_size_1134_; lean_object* v___x_1135_; 
v_index_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_index_1133_);
lean_dec_ref_known(v___x_1132_, 3);
v_size_1134_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_size_1134_);
v___x_1135_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1131_, v_size_1134_, v_index_1133_, v_e_1115_, v_a_1116_);
lean_dec(v_index_1133_);
v___y_1121_ = v___x_1135_;
goto v___jp_1120_;
}
case 1:
{
lean_object* v_index_1136_; 
v_index_1136_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_index_1136_);
lean_dec_ref_known(v___x_1132_, 1);
v___y_1124_ = v___x_1131_;
v_i_1125_ = v_index_1136_;
goto v___jp_1123_;
}
default: 
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = lean_unsigned_to_nat(0u);
v___x_1138_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1131_, v___x_1137_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_index_1139_; 
v_index_1139_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_index_1139_);
lean_dec_ref_known(v___x_1138_, 1);
v___y_1124_ = v___x_1131_;
v_i_1125_ = v_index_1139_;
goto v___jp_1123_;
}
else
{
lean_dec_ref(v_e_1115_);
v___y_1121_ = v___x_1131_;
goto v___jp_1120_;
}
}
}
}
v___jp_1140_:
{
lean_object* v_size_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v_size_1143_ = lean_ctor_get(v___y_1141_, 0);
v___x_1144_ = lean_unsigned_to_nat(1u);
v___x_1145_ = lean_nat_add(v_size_1143_, v___x_1144_);
v___x_1146_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1141_, v___x_1145_, v_i_1142_, v_e_1115_, v_a_1116_);
lean_dec(v_i_1142_);
v___y_1121_ = v___x_1146_;
goto v___jp_1120_;
}
v___jp_1147_:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v___y_1148_, v_e_1115_);
switch(lean_obj_tag(v___x_1149_))
{
case 0:
{
lean_object* v_index_1150_; lean_object* v_size_1151_; lean_object* v___x_1152_; 
v_index_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_index_1150_);
lean_dec_ref_known(v___x_1149_, 3);
v_size_1151_ = lean_ctor_get(v___y_1148_, 0);
lean_inc(v_size_1151_);
v___x_1152_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1148_, v_size_1151_, v_index_1150_, v_e_1115_, v_a_1116_);
lean_dec(v_index_1150_);
v___y_1121_ = v___x_1152_;
goto v___jp_1120_;
}
case 1:
{
lean_object* v_index_1153_; 
v_index_1153_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_index_1153_);
lean_dec_ref_known(v___x_1149_, 1);
v___y_1141_ = v___y_1148_;
v_i_1142_ = v_index_1153_;
goto v___jp_1140_;
}
default: 
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = lean_unsigned_to_nat(0u);
v___x_1155_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1148_, v___x_1154_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_index_1156_; 
v_index_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_index_1156_);
lean_dec_ref_known(v___x_1155_, 1);
v___y_1141_ = v___y_1148_;
v_i_1142_ = v_index_1156_;
goto v___jp_1140_;
}
else
{
lean_dec_ref(v_e_1115_);
v___y_1121_ = v___y_1148_;
goto v___jp_1120_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed(lean_object* v_a_1187_, lean_object* v_e_1188_, lean_object* v_a_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(v_a_1187_, v_e_1188_, v_a_1189_);
lean_dec(v_a_1187_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20___lam__0___boxed(lean_object* v_fvars_1192_, lean_object* v_f_1193_, lean_object* v_body_1194_, lean_object* v_x_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20___lam__0(v_fvars_1192_, v_f_1193_, v_body_1194_, v_x_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec(v___y_1196_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20(lean_object* v_f_1204_, lean_object* v_fvars_1205_, lean_object* v_a_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
if (lean_obj_tag(v_a_1206_) == 7)
{
lean_object* v_binderName_1214_; lean_object* v_binderType_1215_; lean_object* v_body_1216_; uint8_t v_binderInfo_1217_; lean_object* v_d_1218_; lean_object* v___x_1219_; 
v_binderName_1214_ = lean_ctor_get(v_a_1206_, 0);
lean_inc(v_binderName_1214_);
v_binderType_1215_ = lean_ctor_get(v_a_1206_, 1);
lean_inc_ref(v_binderType_1215_);
v_body_1216_ = lean_ctor_get(v_a_1206_, 2);
lean_inc_ref(v_body_1216_);
v_binderInfo_1217_ = lean_ctor_get_uint8(v_a_1206_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_1206_, 3);
v_d_1218_ = lean_expr_instantiate_rev(v_binderType_1215_, v_fvars_1205_);
lean_dec_ref(v_binderType_1215_);
lean_inc_ref(v_f_1204_);
lean_inc(v___y_1212_);
lean_inc_ref(v___y_1211_);
lean_inc(v___y_1210_);
lean_inc_ref(v___y_1209_);
lean_inc(v___y_1208_);
lean_inc(v___y_1207_);
lean_inc_ref(v_d_1218_);
v___x_1219_ = lean_apply_8(v_f_1204_, v_d_1218_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, lean_box(0));
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v___f_1220_; uint8_t v___x_1221_; lean_object* v___x_1222_; 
lean_dec_ref_known(v___x_1219_, 1);
v___f_1220_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20___lam__0___boxed), 11, 3);
lean_closure_set(v___f_1220_, 0, v_fvars_1205_);
lean_closure_set(v___f_1220_, 1, v_f_1204_);
lean_closure_set(v___f_1220_, 2, v_body_1216_);
v___x_1221_ = 0;
v___x_1222_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20_spec__22___redArg(v_binderName_1214_, v_binderInfo_1217_, v_d_1218_, v___f_1220_, v___x_1221_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
return v___x_1222_;
}
else
{
lean_dec_ref(v_d_1218_);
lean_dec_ref(v_body_1216_);
lean_dec(v_binderName_1214_);
lean_dec_ref(v_fvars_1205_);
lean_dec_ref(v_f_1204_);
return v___x_1219_;
}
}
else
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_expr_instantiate_rev(v_a_1206_, v_fvars_1205_);
lean_dec_ref(v_fvars_1205_);
lean_dec_ref(v_a_1206_);
lean_inc(v___y_1212_);
lean_inc_ref(v___y_1211_);
lean_inc(v___y_1210_);
lean_inc_ref(v___y_1209_);
lean_inc(v___y_1208_);
lean_inc(v___y_1207_);
v___x_1224_ = lean_apply_8(v_f_1204_, v___x_1223_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, lean_box(0));
return v___x_1224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20___lam__0(lean_object* v_fvars_1225_, lean_object* v_f_1226_, lean_object* v_body_1227_, lean_object* v_x_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = lean_array_push(v_fvars_1225_, v_x_1228_);
v___x_1237_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20(v_f_1226_, v___x_1236_, v_body_1227_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20___boxed(lean_object* v_f_1238_, lean_object* v_fvars_1239_, lean_object* v_a_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20(v_f_1238_, v_fvars_1239_, v_a_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec(v___y_1241_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(lean_object* v_f_1249_, lean_object* v_e_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13___closed__0));
v___x_1259_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20(v_f_1249_, v___x_1258_, v_e_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11___boxed(lean_object* v_f_1260_, lean_object* v_e_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v_f_1260_, v_e_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec(v___y_1262_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1270_, lean_object* v_e_1271_, lean_object* v_a_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1270_, v_e_1271_, v_a_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec(v_a_1272_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(lean_object* v_fn_1280_, lean_object* v_e_1281_, lean_object* v_a_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v_a_1290_; lean_object* v___y_1302_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
lean_inc(v_a_1282_);
v___x_1304_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1304_, 0, lean_box(0));
lean_closure_set(v___x_1304_, 1, lean_box(0));
lean_closure_set(v___x_1304_, 2, v_a_1282_);
v___x_1305_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___x_1304_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1342_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1308_ = v___x_1305_;
v_isShared_1309_ = v_isSharedCheck_1342_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1305_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1342_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_a_1306_, v_e_1281_);
lean_dec(v_a_1306_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v___x_1311_; 
lean_del_object(v___x_1308_);
lean_inc_ref(v_fn_1280_);
lean_inc(v___y_1287_);
lean_inc_ref(v___y_1286_);
lean_inc(v___y_1285_);
lean_inc_ref(v___y_1284_);
lean_inc(v___y_1283_);
lean_inc_ref(v_e_1281_);
v___x_1311_ = lean_apply_7(v_fn_1280_, v_e_1281_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, lean_box(0));
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; uint8_t v___x_1313_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1312_);
lean_dec_ref_known(v___x_1311_, 1);
v___x_1313_ = lean_unbox(v_a_1312_);
lean_dec(v_a_1312_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; 
lean_dec_ref(v_fn_1280_);
v___x_1314_ = lean_box(0);
v_a_1290_ = v___x_1314_;
goto v___jp_1289_;
}
else
{
switch(lean_obj_tag(v_e_1281_))
{
case 7:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1315_, 0, v_fn_1280_);
lean_inc_ref(v_e_1281_);
v___x_1316_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v___x_1315_, v_e_1281_, v_a_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
v___y_1302_ = v___x_1316_;
goto v___jp_1301_;
}
case 6:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1317_, 0, v_fn_1280_);
lean_inc_ref(v_e_1281_);
v___x_1318_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v___x_1317_, v_e_1281_, v_a_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
v___y_1302_ = v___x_1318_;
goto v___jp_1301_;
}
case 8:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1319_, 0, v_fn_1280_);
lean_inc_ref(v_e_1281_);
v___x_1320_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13(v___x_1319_, v_e_1281_, v_a_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
v___y_1302_ = v___x_1320_;
goto v___jp_1301_;
}
case 5:
{
lean_object* v_fn_1321_; lean_object* v_arg_1322_; lean_object* v___x_1323_; 
v_fn_1321_ = lean_ctor_get(v_e_1281_, 0);
v_arg_1322_ = lean_ctor_get(v_e_1281_, 1);
lean_inc_ref(v_fn_1321_);
lean_inc_ref(v_fn_1280_);
v___x_1323_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1280_, v_fn_1321_, v_a_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v___x_1324_; 
lean_dec_ref_known(v___x_1323_, 1);
lean_inc_ref(v_arg_1322_);
v___x_1324_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1280_, v_arg_1322_, v_a_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
v___y_1302_ = v___x_1324_;
goto v___jp_1301_;
}
else
{
lean_dec_ref(v_fn_1280_);
v___y_1302_ = v___x_1323_;
goto v___jp_1301_;
}
}
case 10:
{
lean_object* v_expr_1325_; lean_object* v___x_1326_; 
v_expr_1325_ = lean_ctor_get(v_e_1281_, 1);
lean_inc_ref(v_expr_1325_);
v___x_1326_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1280_, v_expr_1325_, v_a_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
v___y_1302_ = v___x_1326_;
goto v___jp_1301_;
}
case 11:
{
lean_object* v_struct_1327_; lean_object* v___x_1328_; 
v_struct_1327_ = lean_ctor_get(v_e_1281_, 2);
lean_inc_ref(v_struct_1327_);
v___x_1328_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1280_, v_struct_1327_, v_a_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
v___y_1302_ = v___x_1328_;
goto v___jp_1301_;
}
default: 
{
lean_object* v___x_1329_; 
lean_dec_ref(v_fn_1280_);
v___x_1329_ = lean_box(0);
v_a_1290_ = v___x_1329_;
goto v___jp_1289_;
}
}
}
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_dec_ref(v_e_1281_);
lean_dec_ref(v_fn_1280_);
v_a_1330_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1311_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1311_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
else
{
lean_object* v_val_1338_; lean_object* v___x_1340_; 
lean_dec_ref(v_e_1281_);
lean_dec_ref(v_fn_1280_);
v_val_1338_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_val_1338_);
lean_dec_ref_known(v___x_1310_, 1);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v_val_1338_);
v___x_1340_ = v___x_1308_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_val_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_dec_ref(v_e_1281_);
lean_dec_ref(v_fn_1280_);
v_a_1343_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1305_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1305_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
v___jp_1289_:
{
lean_object* v___f_1291_; lean_object* v___x_1292_; 
lean_inc(v_a_1282_);
v___f_1291_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1291_, 0, v_a_1282_);
lean_closure_set(v___f_1291_, 1, v_e_1281_);
lean_closure_set(v___f_1291_, 2, v_a_1290_);
v___x_1292_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___f_1291_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1299_ == 0)
{
lean_object* v_unused_1300_; 
v_unused_1300_ = lean_ctor_get(v___x_1292_, 0);
lean_dec(v_unused_1300_);
v___x_1294_ = v___x_1292_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_dec(v___x_1292_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 0, v_a_1290_);
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1290_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
else
{
return v___x_1292_;
}
}
v___jp_1301_:
{
if (lean_obj_tag(v___y_1302_) == 0)
{
lean_object* v_a_1303_; 
v_a_1303_ = lean_ctor_get(v___y_1302_, 0);
lean_inc(v_a_1303_);
lean_dec_ref_known(v___y_1302_, 1);
v_a_1290_ = v_a_1303_;
goto v___jp_1289_;
}
else
{
lean_dec_ref(v_e_1281_);
return v___y_1302_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v_cellCount_1351_; lean_object* v___x_1352_; 
v_cellCount_1351_ = lean_unsigned_to_nat(16u);
v___x_1352_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1351_);
return v___x_1352_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v_cellCount_1353_; lean_object* v___x_1354_; 
v_cellCount_1353_ = lean_unsigned_to_nat(16u);
v___x_1354_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1353_);
return v___x_1354_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1355_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1);
v___x_1356_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0);
v___x_1357_ = lean_unsigned_to_nat(0u);
v___x_1358_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
lean_ctor_set(v___x_1358_, 1, v___x_1356_);
lean_ctor_set(v___x_1358_, 2, v___x_1355_);
return v___x_1358_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1359_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2);
v___x_1360_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1360_, 0, lean_box(0));
lean_closure_set(v___x_1360_, 1, lean_box(0));
lean_closure_set(v___x_1360_, 2, v___x_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(lean_object* v_input_1361_, lean_object* v_fn_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v_a_1371_; lean_object* v___x_1372_; 
v___x_1369_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__3, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__3_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__3);
v___x_1370_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1369_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc(v_a_1371_);
lean_dec_ref(v___x_1370_);
v___x_1372_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1362_, v_input_1361_, v_a_1371_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1373_);
lean_dec_ref_known(v___x_1372_, 1);
v___x_1374_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1374_, 0, lean_box(0));
lean_closure_set(v___x_1374_, 1, lean_box(0));
lean_closure_set(v___x_1374_, 2, v_a_1371_);
v___x_1375_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1374_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1382_ == 0)
{
lean_object* v_unused_1383_; 
v_unused_1383_ = lean_ctor_get(v___x_1375_, 0);
lean_dec(v_unused_1383_);
v___x_1377_ = v___x_1375_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_dec(v___x_1375_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 0, v_a_1373_);
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1373_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
else
{
lean_dec(v_a_1371_);
return v___x_1372_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___boxed(lean_object* v_input_1384_, lean_object* v_fn_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1384_, v_fn_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(lean_object* v_input_1393_, lean_object* v_fn_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v___f_1401_; lean_object* v___x_1402_; 
v___f_1401_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1401_, 0, v_fn_1394_);
v___x_1402_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1393_, v___f_1401_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___boxed(lean_object* v_input_1403_, lean_object* v_fn_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_input_1403_, v_fn_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(lean_object* v_fn_1412_, lean_object* v_x_1413_, lean_object* v_x_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
if (lean_obj_tag(v_x_1414_) == 0)
{
lean_object* v___x_1421_; 
lean_dec_ref(v_fn_1412_);
v___x_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1421_, 0, v_x_1413_);
return v___x_1421_;
}
else
{
lean_object* v_head_1422_; lean_object* v_tail_1423_; lean_object* v_type_1424_; lean_object* v___x_1425_; 
v_head_1422_ = lean_ctor_get(v_x_1414_, 0);
lean_inc(v_head_1422_);
v_tail_1423_ = lean_ctor_get(v_x_1414_, 1);
lean_inc(v_tail_1423_);
lean_dec_ref_known(v_x_1414_, 2);
v_type_1424_ = lean_ctor_get(v_head_1422_, 1);
lean_inc_ref(v_type_1424_);
lean_dec(v_head_1422_);
lean_inc_ref(v_fn_1412_);
v___x_1425_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1424_, v_fn_1412_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1426_);
lean_dec_ref_known(v___x_1425_, 1);
v_x_1413_ = v_a_1426_;
v_x_1414_ = v_tail_1423_;
goto _start;
}
else
{
lean_dec(v_tail_1423_);
lean_dec_ref(v_fn_1412_);
return v___x_1425_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4___boxed(lean_object* v_fn_1428_, lean_object* v_x_1429_, lean_object* v_x_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1428_, v_x_1429_, v_x_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(lean_object* v_fn_1438_, lean_object* v_x_1439_, lean_object* v_x_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
if (lean_obj_tag(v_x_1440_) == 0)
{
lean_object* v___x_1447_; 
lean_dec_ref(v_fn_1438_);
v___x_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1447_, 0, v_x_1439_);
return v___x_1447_;
}
else
{
lean_object* v_head_1448_; lean_object* v_tail_1449_; lean_object* v___y_1451_; lean_object* v_type_1454_; lean_object* v_ctors_1455_; lean_object* v___x_1456_; 
v_head_1448_ = lean_ctor_get(v_x_1440_, 0);
lean_inc(v_head_1448_);
v_tail_1449_ = lean_ctor_get(v_x_1440_, 1);
lean_inc(v_tail_1449_);
lean_dec_ref_known(v_x_1440_, 2);
v_type_1454_ = lean_ctor_get(v_head_1448_, 1);
lean_inc_ref(v_type_1454_);
v_ctors_1455_ = lean_ctor_get(v_head_1448_, 2);
lean_inc(v_ctors_1455_);
lean_dec(v_head_1448_);
lean_inc_ref(v_fn_1438_);
v___x_1456_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1454_, v_fn_1438_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1458_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref_known(v___x_1456_, 1);
lean_inc_ref(v_fn_1438_);
v___x_1458_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1438_, v_a_1457_, v_ctors_1455_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
v___y_1451_ = v___x_1458_;
goto v___jp_1450_;
}
else
{
lean_dec(v_ctors_1455_);
v___y_1451_ = v___x_1456_;
goto v___jp_1450_;
}
v___jp_1450_:
{
if (lean_obj_tag(v___y_1451_) == 0)
{
lean_object* v_a_1452_; 
v_a_1452_ = lean_ctor_get(v___y_1451_, 0);
lean_inc(v_a_1452_);
lean_dec_ref_known(v___y_1451_, 1);
v_x_1439_ = v_a_1452_;
v_x_1440_ = v_tail_1449_;
goto _start;
}
else
{
lean_dec(v_tail_1449_);
lean_dec_ref(v_fn_1438_);
return v___y_1451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6___boxed(lean_object* v_fn_1459_, lean_object* v_x_1460_, lean_object* v_x_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1459_, v_x_1460_, v_x_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(lean_object* v_fn_1469_, lean_object* v_x_1470_, lean_object* v_x_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
if (lean_obj_tag(v_x_1471_) == 0)
{
lean_object* v___x_1478_; 
lean_dec_ref(v_fn_1469_);
v___x_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1478_, 0, v_x_1470_);
return v___x_1478_;
}
else
{
lean_object* v_head_1479_; lean_object* v_tail_1480_; lean_object* v___y_1482_; lean_object* v_toConstantVal_1485_; lean_object* v_value_1486_; lean_object* v_type_1487_; lean_object* v___x_1488_; 
v_head_1479_ = lean_ctor_get(v_x_1471_, 0);
lean_inc(v_head_1479_);
v_tail_1480_ = lean_ctor_get(v_x_1471_, 1);
lean_inc(v_tail_1480_);
lean_dec_ref_known(v_x_1471_, 2);
v_toConstantVal_1485_ = lean_ctor_get(v_head_1479_, 0);
lean_inc_ref(v_toConstantVal_1485_);
v_value_1486_ = lean_ctor_get(v_head_1479_, 1);
lean_inc_ref(v_value_1486_);
lean_dec(v_head_1479_);
v_type_1487_ = lean_ctor_get(v_toConstantVal_1485_, 2);
lean_inc_ref(v_type_1487_);
lean_dec_ref(v_toConstantVal_1485_);
lean_inc_ref(v_fn_1469_);
v___x_1488_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1487_, v_fn_1469_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v___x_1489_; 
lean_dec_ref_known(v___x_1488_, 1);
lean_inc_ref(v_fn_1469_);
v___x_1489_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1486_, v_fn_1469_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
v___y_1482_ = v___x_1489_;
goto v___jp_1481_;
}
else
{
lean_dec_ref(v_value_1486_);
v___y_1482_ = v___x_1488_;
goto v___jp_1481_;
}
v___jp_1481_:
{
if (lean_obj_tag(v___y_1482_) == 0)
{
lean_object* v_a_1483_; 
v_a_1483_ = lean_ctor_get(v___y_1482_, 0);
lean_inc(v_a_1483_);
lean_dec_ref_known(v___y_1482_, 1);
v_x_1470_ = v_a_1483_;
v_x_1471_ = v_tail_1480_;
goto _start;
}
else
{
lean_dec(v_tail_1480_);
lean_dec_ref(v_fn_1469_);
return v___y_1482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1490_, lean_object* v_x_1491_, lean_object* v_x_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1490_, v_x_1491_, v_x_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(lean_object* v_fn_1500_, lean_object* v_d_1501_, lean_object* v_a_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
switch(lean_obj_tag(v_d_1501_))
{
case 0:
{
lean_object* v_val_1509_; lean_object* v_toConstantVal_1510_; lean_object* v_type_1511_; lean_object* v___x_1512_; 
v_val_1509_ = lean_ctor_get(v_d_1501_, 0);
lean_inc_ref(v_val_1509_);
lean_dec_ref_known(v_d_1501_, 1);
v_toConstantVal_1510_ = lean_ctor_get(v_val_1509_, 0);
lean_inc_ref(v_toConstantVal_1510_);
lean_dec_ref(v_val_1509_);
v_type_1511_ = lean_ctor_get(v_toConstantVal_1510_, 2);
lean_inc_ref(v_type_1511_);
lean_dec_ref(v_toConstantVal_1510_);
v___x_1512_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1511_, v_fn_1500_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
return v___x_1512_;
}
case 4:
{
lean_object* v___x_1513_; 
lean_dec_ref(v_fn_1500_);
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v_a_1502_);
return v___x_1513_;
}
case 5:
{
lean_object* v_defns_1514_; lean_object* v___x_1515_; 
v_defns_1514_ = lean_ctor_get(v_d_1501_, 0);
lean_inc(v_defns_1514_);
lean_dec_ref_known(v_d_1501_, 1);
v___x_1515_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1500_, v_a_1502_, v_defns_1514_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
return v___x_1515_;
}
case 6:
{
lean_object* v_types_1516_; lean_object* v___x_1517_; 
v_types_1516_ = lean_ctor_get(v_d_1501_, 2);
lean_inc(v_types_1516_);
lean_dec_ref_known(v_d_1501_, 3);
v___x_1517_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1500_, v_a_1502_, v_types_1516_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
return v___x_1517_;
}
default: 
{
lean_object* v_val_1518_; lean_object* v_toConstantVal_1519_; lean_object* v_value_1520_; lean_object* v_type_1521_; lean_object* v___x_1522_; 
v_val_1518_ = lean_ctor_get(v_d_1501_, 0);
lean_inc_ref(v_val_1518_);
lean_dec(v_d_1501_);
v_toConstantVal_1519_ = lean_ctor_get(v_val_1518_, 0);
lean_inc_ref(v_toConstantVal_1519_);
v_value_1520_ = lean_ctor_get(v_val_1518_, 1);
lean_inc_ref(v_value_1520_);
lean_dec_ref(v_val_1518_);
v_type_1521_ = lean_ctor_get(v_toConstantVal_1519_, 2);
lean_inc_ref(v_type_1521_);
lean_dec_ref(v_toConstantVal_1519_);
lean_inc_ref(v_fn_1500_);
v___x_1522_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1521_, v_fn_1500_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v___x_1523_; 
lean_dec_ref_known(v___x_1522_, 1);
v___x_1523_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1520_, v_fn_1500_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
return v___x_1523_;
}
else
{
lean_dec_ref(v_value_1520_);
lean_dec_ref(v_fn_1500_);
return v___x_1522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2___boxed(lean_object* v_fn_1524_, lean_object* v_d_1525_, lean_object* v_a_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1524_, v_d_1525_, v_a_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(lean_object* v_decl_1534_, lean_object* v_fn_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = lean_box(0);
v___x_1543_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1535_, v_decl_1534_, v___x_1542_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1___boxed(lean_object* v_decl_1544_, lean_object* v_fn_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1544_, v_fn_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v___y_1546_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(lean_object* v_as_1556_, size_t v_sz_1557_, size_t v_i_1558_, lean_object* v_b_1559_){
_start:
{
uint8_t v___x_1560_; 
v___x_1560_ = lean_usize_dec_lt(v_i_1558_, v_sz_1557_);
if (v___x_1560_ == 0)
{
lean_inc_ref(v_b_1559_);
return v_b_1559_;
}
else
{
lean_object* v_a_1561_; lean_object* v_fst_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v_a_1561_ = lean_array_uget_borrowed(v_as_1556_, v_i_1558_);
v_fst_1562_ = lean_ctor_get(v_a_1561_, 0);
v___x_1563_ = lean_box(0);
v___x_1564_ = lean_unbox(v_fst_1562_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; size_t v___x_1566_; size_t v___x_1567_; 
v___x_1565_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___closed__0));
v___x_1566_ = ((size_t)1ULL);
v___x_1567_ = lean_usize_add(v_i_1558_, v___x_1566_);
v_i_1558_ = v___x_1567_;
v_b_1559_ = v___x_1565_;
goto _start;
}
else
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
lean_inc(v_a_1561_);
v___x_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1569_, 0, v_a_1561_);
v___x_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
lean_ctor_set(v___x_1571_, 1, v___x_1563_);
return v___x_1571_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___boxed(lean_object* v_as_1572_, lean_object* v_sz_1573_, lean_object* v_i_1574_, lean_object* v_b_1575_){
_start:
{
size_t v_sz_boxed_1576_; size_t v_i_boxed_1577_; lean_object* v_res_1578_; 
v_sz_boxed_1576_ = lean_unbox_usize(v_sz_1573_);
lean_dec(v_sz_1573_);
v_i_boxed_1577_ = lean_unbox_usize(v_i_1574_);
lean_dec(v_i_1574_);
v_res_1578_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v_as_1572_, v_sz_boxed_1576_, v_i_boxed_1577_, v_b_1575_);
lean_dec_ref(v_b_1575_);
lean_dec_ref(v_as_1572_);
return v_res_1578_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__0(void){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1579_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__1(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__0, &l_Lean_warnIfUsesSorry___closed__0_once, _init_l_Lean_warnIfUsesSorry___closed__0);
v___x_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
return v___x_1581_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__2(void){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1582_ = lean_box(1);
v___x_1583_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_1584_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1585_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
lean_ctor_set(v___x_1585_, 1, v___x_1583_);
lean_ctor_set(v___x_1585_, 2, v___x_1582_);
return v___x_1585_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__4(void){
_start:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1588_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1589_ = lean_unsigned_to_nat(0u);
v___x_1590_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
lean_ctor_set(v___x_1590_, 2, v___x_1589_);
lean_ctor_set(v___x_1590_, 3, v___x_1589_);
lean_ctor_set(v___x_1590_, 4, v___x_1588_);
lean_ctor_set(v___x_1590_, 5, v___x_1588_);
lean_ctor_set(v___x_1590_, 6, v___x_1588_);
lean_ctor_set(v___x_1590_, 7, v___x_1588_);
lean_ctor_set(v___x_1590_, 8, v___x_1588_);
lean_ctor_set(v___x_1590_, 9, v___x_1588_);
lean_ctor_set(v___x_1590_, 10, v___x_1588_);
return v___x_1590_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__5(void){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1592_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
lean_ctor_set(v___x_1592_, 2, v___x_1591_);
lean_ctor_set(v___x_1592_, 3, v___x_1591_);
lean_ctor_set(v___x_1592_, 4, v___x_1591_);
lean_ctor_set(v___x_1592_, 5, v___x_1591_);
return v___x_1592_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__6(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
lean_ctor_set(v___x_1594_, 2, v___x_1593_);
lean_ctor_set(v___x_1594_, 3, v___x_1593_);
lean_ctor_set(v___x_1594_, 4, v___x_1593_);
return v___x_1594_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__7(void){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1595_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__6, &l_Lean_warnIfUsesSorry___closed__6_once, _init_l_Lean_warnIfUsesSorry___closed__6);
v___x_1596_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_1597_ = lean_box(1);
v___x_1598_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__5, &l_Lean_warnIfUsesSorry___closed__5_once, _init_l_Lean_warnIfUsesSorry___closed__5);
v___x_1599_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__4, &l_Lean_warnIfUsesSorry___closed__4_once, _init_l_Lean_warnIfUsesSorry___closed__4);
v___x_1600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
lean_ctor_set(v___x_1600_, 1, v___x_1598_);
lean_ctor_set(v___x_1600_, 2, v___x_1597_);
lean_ctor_set(v___x_1600_, 3, v___x_1596_);
lean_ctor_set(v___x_1600_, 4, v___x_1595_);
return v___x_1600_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__12(void){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__11));
v___x_1607_ = l_Lean_stringToMessageData(v___x_1606_);
return v___x_1607_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__14(void){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__13));
v___x_1610_ = l_Lean_stringToMessageData(v___x_1609_);
return v___x_1610_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__16(void){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__15));
v___x_1613_ = l_Lean_stringToMessageData(v___x_1612_);
return v___x_1613_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__17(void){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1614_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__16, &l_Lean_warnIfUsesSorry___closed__16_once, _init_l_Lean_warnIfUsesSorry___closed__16);
v___x_1615_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__10));
v___x_1616_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
lean_ctor_set(v___x_1616_, 1, v___x_1614_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry(lean_object* v_decl_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_){
_start:
{
lean_object* v_options_1624_; lean_object* v___x_1625_; uint8_t v___x_1626_; 
v_options_1624_ = lean_ctor_get(v_a_1621_, 2);
v___x_1625_ = l_Lean_warn_sorry;
v___x_1626_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_1624_, v___x_1625_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
lean_dec(v_decl_1620_);
v___x_1627_ = lean_box(0);
v___x_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
return v___x_1628_;
}
else
{
lean_object* v___x_1629_; lean_object* v_messages_1633_; uint8_t v___x_1634_; 
v___x_1629_ = lean_st_ref_get(v_a_1622_);
v_messages_1633_ = lean_ctor_get(v___x_1629_, 6);
lean_inc_ref(v_messages_1633_);
lean_dec(v___x_1629_);
v___x_1634_ = l_Lean_MessageLog_hasErrors(v_messages_1633_);
lean_dec_ref(v_messages_1633_);
if (v___x_1634_ == 0)
{
if (v___x_1626_ == 0)
{
lean_dec(v_decl_1620_);
goto v___jp_1630_;
}
else
{
uint8_t v___x_1635_; 
v___x_1635_ = l_Lean_Declaration_hasSorry(v_decl_1620_);
if (v___x_1635_ == 0)
{
lean_dec(v_decl_1620_);
goto v___jp_1630_;
}
else
{
uint8_t v___x_1636_; uint8_t v___x_1637_; uint8_t v___x_1638_; lean_object* v___x_1639_; uint64_t v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___f_1651_; lean_object* v___x_1652_; 
v___x_1636_ = 1;
v___x_1637_ = 0;
v___x_1638_ = 2;
v___x_1639_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_1639_, 0, v___x_1634_);
lean_ctor_set_uint8(v___x_1639_, 1, v___x_1634_);
lean_ctor_set_uint8(v___x_1639_, 2, v___x_1634_);
lean_ctor_set_uint8(v___x_1639_, 3, v___x_1634_);
lean_ctor_set_uint8(v___x_1639_, 4, v___x_1634_);
lean_ctor_set_uint8(v___x_1639_, 5, v___x_1635_);
lean_ctor_set_uint8(v___x_1639_, 6, v___x_1635_);
lean_ctor_set_uint8(v___x_1639_, 7, v___x_1634_);
lean_ctor_set_uint8(v___x_1639_, 8, v___x_1635_);
lean_ctor_set_uint8(v___x_1639_, 9, v___x_1636_);
lean_ctor_set_uint8(v___x_1639_, 10, v___x_1637_);
lean_ctor_set_uint8(v___x_1639_, 11, v___x_1635_);
lean_ctor_set_uint8(v___x_1639_, 12, v___x_1635_);
lean_ctor_set_uint8(v___x_1639_, 13, v___x_1635_);
lean_ctor_set_uint8(v___x_1639_, 14, v___x_1638_);
lean_ctor_set_uint8(v___x_1639_, 15, v___x_1635_);
lean_ctor_set_uint8(v___x_1639_, 16, v___x_1635_);
lean_ctor_set_uint8(v___x_1639_, 17, v___x_1635_);
lean_ctor_set_uint8(v___x_1639_, 18, v___x_1635_);
lean_ctor_set_uint8(v___x_1639_, 19, v___x_1634_);
v___x_1640_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1639_);
v___x_1641_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1641_, 0, v___x_1639_);
lean_ctor_set_uint64(v___x_1641_, sizeof(void*)*1, v___x_1640_);
v___x_1642_ = lean_box(1);
v___x_1643_ = lean_unsigned_to_nat(0u);
v___x_1644_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1645_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__3));
v___x_1646_ = lean_box(0);
v___x_1647_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1647_, 0, v___x_1641_);
lean_ctor_set(v___x_1647_, 1, v___x_1642_);
lean_ctor_set(v___x_1647_, 2, v___x_1644_);
lean_ctor_set(v___x_1647_, 3, v___x_1645_);
lean_ctor_set(v___x_1647_, 4, v___x_1646_);
lean_ctor_set(v___x_1647_, 5, v___x_1643_);
lean_ctor_set(v___x_1647_, 6, v___x_1646_);
lean_ctor_set_uint8(v___x_1647_, sizeof(void*)*7, v___x_1634_);
lean_ctor_set_uint8(v___x_1647_, sizeof(void*)*7 + 1, v___x_1634_);
lean_ctor_set_uint8(v___x_1647_, sizeof(void*)*7 + 2, v___x_1634_);
lean_ctor_set_uint8(v___x_1647_, sizeof(void*)*7 + 3, v___x_1626_);
v___x_1648_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__7, &l_Lean_warnIfUsesSorry___closed__7_once, _init_l_Lean_warnIfUsesSorry___closed__7);
v___x_1649_ = lean_st_mk_ref(v___x_1648_);
v___x_1650_ = lean_st_mk_ref(v___x_1645_);
v___f_1651_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__8));
v___x_1652_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1620_, v___f_1651_, v___x_1650_, v___x_1647_, v___x_1649_, v_a_1621_, v_a_1622_);
lean_dec_ref_known(v___x_1647_, 7);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v_val_1656_; lean_object* v___x_1678_; size_t v_sz_1679_; size_t v___x_1680_; lean_object* v___x_1681_; lean_object* v_fst_1682_; 
lean_dec_ref_known(v___x_1652_, 1);
v___x_1653_ = lean_st_ref_get(v___x_1650_);
lean_dec(v___x_1650_);
v___x_1654_ = lean_st_ref_get(v___x_1649_);
lean_dec(v___x_1649_);
lean_dec(v___x_1654_);
v___x_1678_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__18));
v_sz_1679_ = lean_array_size(v___x_1653_);
v___x_1680_ = ((size_t)0ULL);
v___x_1681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v___x_1653_, v_sz_1679_, v___x_1680_, v___x_1678_);
v_fst_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_fst_1682_);
lean_dec_ref(v___x_1681_);
if (lean_obj_tag(v_fst_1682_) == 0)
{
goto v___jp_1672_;
}
else
{
lean_object* v_val_1683_; 
v_val_1683_ = lean_ctor_get(v_fst_1682_, 0);
lean_inc(v_val_1683_);
lean_dec_ref_known(v_fst_1682_, 1);
if (lean_obj_tag(v_val_1683_) == 0)
{
goto v___jp_1672_;
}
else
{
lean_object* v_val_1684_; 
lean_dec(v___x_1653_);
v_val_1684_ = lean_ctor_get(v_val_1683_, 0);
lean_inc(v_val_1684_);
lean_dec_ref_known(v_val_1683_, 1);
v_val_1656_ = v_val_1684_;
goto v___jp_1655_;
}
}
v___jp_1655_:
{
lean_object* v_snd_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1670_; 
v_snd_1657_ = lean_ctor_get(v_val_1656_, 1);
v_isSharedCheck_1670_ = !lean_is_exclusive(v_val_1656_);
if (v_isSharedCheck_1670_ == 0)
{
lean_object* v_unused_1671_; 
v_unused_1671_ = lean_ctor_get(v_val_1656_, 0);
lean_dec(v_unused_1671_);
v___x_1659_ = v_val_1656_;
v_isShared_1660_ = v_isSharedCheck_1670_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_snd_1657_);
lean_dec(v_val_1656_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1670_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1664_; 
v___x_1661_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__10));
v___x_1662_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__12, &l_Lean_warnIfUsesSorry___closed__12_once, _init_l_Lean_warnIfUsesSorry___closed__12);
if (v_isShared_1660_ == 0)
{
lean_ctor_set_tag(v___x_1659_, 7);
lean_ctor_set(v___x_1659_, 0, v___x_1662_);
v___x_1664_ = v___x_1659_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1662_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_snd_1657_);
v___x_1664_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1665_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__14, &l_Lean_warnIfUsesSorry___closed__14_once, _init_l_Lean_warnIfUsesSorry___closed__14);
v___x_1666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1664_);
lean_ctor_set(v___x_1666_, 1, v___x_1665_);
v___x_1667_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1661_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1667_, v_a_1621_, v_a_1622_);
return v___x_1668_;
}
}
}
v___jp_1672_:
{
lean_object* v___x_1673_; uint8_t v___x_1674_; 
v___x_1673_ = lean_array_get_size(v___x_1653_);
v___x_1674_ = lean_nat_dec_lt(v___x_1643_, v___x_1673_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
lean_dec(v___x_1653_);
v___x_1675_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__17, &l_Lean_warnIfUsesSorry___closed__17_once, _init_l_Lean_warnIfUsesSorry___closed__17);
v___x_1676_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1675_, v_a_1621_, v_a_1622_);
return v___x_1676_;
}
else
{
lean_object* v___x_1677_; 
v___x_1677_ = lean_array_fget(v___x_1653_, v___x_1643_);
lean_dec(v___x_1653_);
v_val_1656_ = v___x_1677_;
goto v___jp_1655_;
}
}
}
else
{
lean_dec(v___x_1650_);
lean_dec(v___x_1649_);
return v___x_1652_;
}
}
}
}
else
{
lean_dec(v_decl_1620_);
goto v___jp_1630_;
}
v___jp_1630_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = lean_box(0);
v___x_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
return v___x_1632_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___boxed(lean_object* v_decl_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Lean_warnIfUsesSorry(v_decl_1685_, v_a_1686_, v_a_1687_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1690_, lean_object* v_m_1691_, lean_object* v_a_1692_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1691_, v_a_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1694_, lean_object* v_m_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(v_00_u03b2_1694_, v_m_1695_, v_a_1696_);
lean_dec_ref(v_a_1696_);
lean_dec_ref(v_m_1695_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_1698_, lean_object* v_m_1699_, lean_object* v_query_1700_){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_m_1699_, v_query_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1702_, lean_object* v_m_1703_, lean_object* v_query_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9(v_00_u03b2_1702_, v_m_1703_, v_query_1704_);
lean_dec_ref(v_query_1704_);
lean_dec_ref(v_m_1703_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(lean_object* v_00_u03b2_1706_, lean_object* v_m_1707_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10___redArg(v_m_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10___boxed(lean_object* v_00_u03b2_1709_, lean_object* v_m_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v_00_u03b2_1709_, v_m_1710_);
lean_dec_ref(v_m_1710_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_1712_, lean_object* v_m_1713_, lean_object* v_query_1714_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_m_1713_, v_query_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1716_, lean_object* v_m_1717_, lean_object* v_query_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(v_00_u03b2_1716_, v_m_1717_, v_query_1718_);
lean_dec_ref(v_query_1718_);
lean_dec_ref(v_m_1717_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(lean_object* v_00_u03b2_1720_, lean_object* v_m_1721_, lean_object* v_query_1722_, lean_object* v_x_1723_, lean_object* v_x_1724_, lean_object* v_x_1725_, lean_object* v_x_1726_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_m_1721_, v_query_1722_, v_x_1723_, v_x_1724_, v_x_1725_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___boxed(lean_object* v_00_u03b2_1728_, lean_object* v_m_1729_, lean_object* v_query_1730_, lean_object* v_x_1731_, lean_object* v_x_1732_, lean_object* v_x_1733_, lean_object* v_x_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(v_00_u03b2_1728_, v_m_1729_, v_query_1730_, v_x_1731_, v_x_1732_, v_x_1733_, v_x_1734_);
lean_dec_ref(v_query_1730_);
lean_dec_ref(v_m_1729_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__18(lean_object* v_00_u03b2_1736_, lean_object* v_init_1737_, lean_object* v_b_1738_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__18___redArg(v_init_1737_, v_b_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__18___boxed(lean_object* v_00_u03b2_1740_, lean_object* v_init_1741_, lean_object* v_b_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__18(v_00_u03b2_1740_, v_init_1741_, v_b_1742_);
lean_dec_ref(v_b_1742_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20_spec__22(lean_object* v_00_u03b1_1744_, lean_object* v_name_1745_, uint8_t v_bi_1746_, lean_object* v_type_1747_, lean_object* v_k_1748_, uint8_t v_kind_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20_spec__22___redArg(v_name_1745_, v_bi_1746_, v_type_1747_, v_k_1748_, v_kind_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20_spec__22___boxed(lean_object* v_00_u03b1_1758_, lean_object* v_name_1759_, lean_object* v_bi_1760_, lean_object* v_type_1761_, lean_object* v_k_1762_, lean_object* v_kind_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
uint8_t v_bi_boxed_1771_; uint8_t v_kind_boxed_1772_; lean_object* v_res_1773_; 
v_bi_boxed_1771_ = lean_unbox(v_bi_1760_);
v_kind_boxed_1772_ = lean_unbox(v_kind_1763_);
v_res_1773_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__20_spec__22(v_00_u03b1_1758_, v_name_1759_, v_bi_boxed_1771_, v_type_1761_, v_k_1762_, v_kind_boxed_1772_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec(v___y_1764_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13_spec__24_spec__27(lean_object* v_00_u03b1_1774_, lean_object* v_name_1775_, lean_object* v_type_1776_, lean_object* v_val_1777_, lean_object* v_k_1778_, uint8_t v_nondep_1779_, uint8_t v_kind_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13_spec__24_spec__27___redArg(v_name_1775_, v_type_1776_, v_val_1777_, v_k_1778_, v_nondep_1779_, v_kind_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13_spec__24_spec__27___boxed(lean_object* v_00_u03b1_1789_, lean_object* v_name_1790_, lean_object* v_type_1791_, lean_object* v_val_1792_, lean_object* v_k_1793_, lean_object* v_nondep_1794_, lean_object* v_kind_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
uint8_t v_nondep_boxed_1803_; uint8_t v_kind_boxed_1804_; lean_object* v_res_1805_; 
v_nondep_boxed_1803_ = lean_unbox(v_nondep_1794_);
v_kind_boxed_1804_ = lean_unbox(v_kind_1795_);
v_res_1805_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__13_spec__24_spec__27(v_00_u03b1_1789_, v_name_1790_, v_type_1791_, v_val_1792_, v_k_1793_, v_nondep_boxed_1803_, v_kind_boxed_1804_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec(v___y_1796_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__18_spec__19(lean_object* v_00_u03b2_1806_, lean_object* v_b_1807_, lean_object* v_acc_1808_, lean_object* v_i_1809_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__18_spec__19___redArg(v_b_1807_, v_acc_1808_, v_i_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__18_spec__19___boxed(lean_object* v_00_u03b2_1811_, lean_object* v_b_1812_, lean_object* v_acc_1813_, lean_object* v_i_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__18_spec__19(v_00_u03b2_1811_, v_b_1812_, v_acc_1813_, v_i_1814_);
lean_dec_ref(v_b_1812_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1865_; uint8_t v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1865_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1866_ = 0;
v___x_1867_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__20_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1868_ = l_Lean_registerTraceClass(v___x_1865_, v___x_1866_, v___x_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2____boxed(lean_object* v_a_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_();
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(lean_object* v_env_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v___x_1874_; lean_object* v_nextMacroScope_1875_; lean_object* v_ngen_1876_; lean_object* v_auxDeclNGen_1877_; lean_object* v_traceState_1878_; lean_object* v_messages_1879_; lean_object* v_infoState_1880_; lean_object* v_snapshotTasks_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1892_; 
v___x_1874_ = lean_st_ref_take(v___y_1872_);
v_nextMacroScope_1875_ = lean_ctor_get(v___x_1874_, 1);
v_ngen_1876_ = lean_ctor_get(v___x_1874_, 2);
v_auxDeclNGen_1877_ = lean_ctor_get(v___x_1874_, 3);
v_traceState_1878_ = lean_ctor_get(v___x_1874_, 4);
v_messages_1879_ = lean_ctor_get(v___x_1874_, 6);
v_infoState_1880_ = lean_ctor_get(v___x_1874_, 7);
v_snapshotTasks_1881_ = lean_ctor_get(v___x_1874_, 8);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1892_ == 0)
{
lean_object* v_unused_1893_; lean_object* v_unused_1894_; 
v_unused_1893_ = lean_ctor_get(v___x_1874_, 5);
lean_dec(v_unused_1893_);
v_unused_1894_ = lean_ctor_get(v___x_1874_, 0);
lean_dec(v_unused_1894_);
v___x_1883_ = v___x_1874_;
v_isShared_1884_ = v_isSharedCheck_1892_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_snapshotTasks_1881_);
lean_inc(v_infoState_1880_);
lean_inc(v_messages_1879_);
lean_inc(v_traceState_1878_);
lean_inc(v_auxDeclNGen_1877_);
lean_inc(v_ngen_1876_);
lean_inc(v_nextMacroScope_1875_);
lean_dec(v___x_1874_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1892_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; lean_object* v___x_1887_; 
v___x_1885_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 5, v___x_1885_);
lean_ctor_set(v___x_1883_, 0, v_env_1871_);
v___x_1887_ = v___x_1883_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_env_1871_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_nextMacroScope_1875_);
lean_ctor_set(v_reuseFailAlloc_1891_, 2, v_ngen_1876_);
lean_ctor_set(v_reuseFailAlloc_1891_, 3, v_auxDeclNGen_1877_);
lean_ctor_set(v_reuseFailAlloc_1891_, 4, v_traceState_1878_);
lean_ctor_set(v_reuseFailAlloc_1891_, 5, v___x_1885_);
lean_ctor_set(v_reuseFailAlloc_1891_, 6, v_messages_1879_);
lean_ctor_set(v_reuseFailAlloc_1891_, 7, v_infoState_1880_);
lean_ctor_set(v_reuseFailAlloc_1891_, 8, v_snapshotTasks_1881_);
v___x_1887_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1888_ = lean_st_ref_put(v___y_1872_, v___x_1887_);
v___x_1889_ = lean_box(0);
v___x_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
return v___x_1890_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg___boxed(lean_object* v_env_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1895_, v___y_1896_);
lean_dec(v___y_1896_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(lean_object* v_env_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1899_, v___y_1901_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___boxed(lean_object* v_env_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(v_env_1904_, v___y_1905_, v___y_1906_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
return v_res_1908_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1909_ = lean_box(0);
v___x_1910_ = l_Lean_interruptExceptionId;
v___x_1911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1910_);
lean_ctor_set(v___x_1911_, 1, v___x_1909_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg(){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1913_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v___y_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(lean_object* v_msg_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v_ref_1921_; lean_object* v___x_1922_; lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1931_; 
v_ref_1921_ = lean_ctor_get(v___y_1918_, 5);
v___x_1922_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_1917_, v___y_1918_, v___y_1919_);
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1925_ = v___x_1922_;
v_isShared_1926_ = v_isSharedCheck_1931_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1922_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1931_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1927_; lean_object* v___x_1929_; 
lean_inc(v_ref_1921_);
v___x_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1927_, 0, v_ref_1921_);
lean_ctor_set(v___x_1927_, 1, v_a_1923_);
if (v_isShared_1926_ == 0)
{
lean_ctor_set_tag(v___x_1925_, 1);
lean_ctor_set(v___x_1925_, 0, v___x_1927_);
v___x_1929_ = v___x_1925_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msg_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_1932_, v___y_1933_, v___y_1934_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(lean_object* v_ex_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v___y_1942_; lean_object* v___y_1943_; 
if (lean_obj_tag(v_ex_1937_) == 16)
{
lean_object* v___x_1947_; lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
v___x_1947_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1947_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1947_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
else
{
v___y_1942_ = v___y_1938_;
v___y_1943_ = v___y_1939_;
goto v___jp_1941_;
}
v___jp_1941_:
{
lean_object* v_options_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v_options_1944_ = lean_ctor_get(v___y_1942_, 2);
lean_inc_ref(v_options_1944_);
v___x_1945_ = l_Lean_Kernel_Exception_toMessageData(v_ex_1937_, v_options_1944_);
v___x_1946_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v___x_1945_, v___y_1942_, v___y_1943_);
return v___x_1946_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg___boxed(lean_object* v_ex_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_1956_, v___y_1957_, v___y_1958_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(lean_object* v_x_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
if (lean_obj_tag(v_x_1961_) == 0)
{
lean_object* v_a_1965_; lean_object* v___x_1966_; 
v_a_1965_ = lean_ctor_get(v_x_1961_, 0);
lean_inc(v_a_1965_);
lean_dec_ref_known(v_x_1961_, 1);
v___x_1966_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_a_1965_, v___y_1962_, v___y_1963_);
return v___x_1966_;
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
v_a_1967_ = lean_ctor_get(v_x_1961_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_x_1961_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v_x_1961_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v_x_1961_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
lean_ctor_set_tag(v___x_1969_, 0);
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg___boxed(lean_object* v_x_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_1975_, v___y_1976_, v___y_1977_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
return v_res_1979_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = lean_unsigned_to_nat(1u);
v___x_1981_ = l_Lean_Level_ofNat(v___x_1980_);
return v___x_1981_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1982_ = lean_box(0);
v___x_1983_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0);
v___x_1984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
lean_ctor_set(v___x_1984_, 1, v___x_1982_);
return v___x_1984_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1991_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1);
v___x_1992_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4));
v___x_1993_ = l_Lean_mkConst(v___x_1992_, v___x_1991_);
return v___x_1993_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1994_ = lean_unsigned_to_nat(0u);
v___x_1995_ = l_Lean_Level_ofNat(v___x_1994_);
return v___x_1995_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6);
v___x_1997_ = l_Lean_mkSort(v___x_1996_);
return v___x_1997_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11(void){
_start:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2003_ = lean_box(0);
v___x_2004_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__10));
v___x_2005_ = l_Lean_mkConst(v___x_2004_, v___x_2003_);
return v___x_2005_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12(void){
_start:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2006_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11);
v___x_2007_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7);
v___x_2008_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5);
v___x_2009_ = l_Lean_mkAppB(v___x_2008_, v___x_2007_, v___x_2006_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(lean_object* v_as_x27_2015_, lean_object* v_b_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
if (lean_obj_tag(v_as_x27_2015_) == 0)
{
lean_object* v___x_2020_; 
v___x_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2020_, 0, v_b_2016_);
return v___x_2020_;
}
else
{
lean_object* v_head_2021_; lean_object* v_tail_2022_; lean_object* v___x_2023_; lean_object* v_env_2024_; lean_object* v_options_2025_; lean_object* v_cancelTk_x3f_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___y_2030_; uint8_t v___y_2031_; lean_object* v_a_2035_; lean_object* v___x_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
lean_dec_ref(v_b_2016_);
v_head_2021_ = lean_ctor_get(v_as_x27_2015_, 0);
v_tail_2022_ = lean_ctor_get(v_as_x27_2015_, 1);
v___x_2023_ = lean_st_ref_get(v___y_2018_);
v_env_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc_ref(v_env_2024_);
lean_dec(v___x_2023_);
v_options_2025_ = lean_ctor_get(v___y_2017_, 2);
v_cancelTk_x3f_2026_ = lean_ctor_get(v___y_2017_, 12);
v___x_2027_ = lean_box(0);
v___x_2028_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2));
v___x_2038_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12);
lean_inc(v_head_2021_);
v___x_2039_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2039_, 0, v_head_2021_);
lean_ctor_set(v___x_2039_, 1, v___x_2027_);
lean_ctor_set(v___x_2039_, 2, v___x_2038_);
v___x_2040_ = 0;
v___x_2041_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2041_, 0, v___x_2039_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*1, v___x_2040_);
v___x_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2041_);
v___x_2043_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2024_, v_options_2025_, v___x_2042_, v_cancelTk_x3f_2026_);
lean_dec_ref_known(v___x_2042_, 1);
v___x_2044_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2043_, v___y_2017_, v___y_2018_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; lean_object* v___x_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2054_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2045_);
lean_dec_ref_known(v___x_2044_, 1);
v___x_2046_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2045_, v___y_2018_);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2054_ == 0)
{
lean_object* v_unused_2055_; 
v_unused_2055_ = lean_ctor_get(v___x_2046_, 0);
lean_dec(v_unused_2055_);
v___x_2048_ = v___x_2046_;
v_isShared_2049_ = v_isSharedCheck_2054_;
goto v_resetjp_2047_;
}
else
{
lean_dec(v___x_2046_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2054_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2050_; lean_object* v___x_2052_; 
v___x_2050_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__14));
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 0, v___x_2050_);
v___x_2052_ = v___x_2048_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
else
{
lean_object* v_a_2056_; 
v_a_2056_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2056_);
lean_dec_ref_known(v___x_2044_, 1);
v_a_2035_ = v_a_2056_;
goto v___jp_2034_;
}
v___jp_2029_:
{
if (v___y_2031_ == 0)
{
lean_dec_ref(v___y_2030_);
v_as_x27_2015_ = v_tail_2022_;
v_b_2016_ = v___x_2028_;
goto _start;
}
else
{
lean_object* v___x_2033_; 
v___x_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2033_, 0, v___y_2030_);
return v___x_2033_;
}
}
v___jp_2034_:
{
uint8_t v___x_2036_; 
v___x_2036_ = l_Lean_Exception_isInterrupt(v_a_2035_);
if (v___x_2036_ == 0)
{
uint8_t v___x_2037_; 
lean_inc_ref(v_a_2035_);
v___x_2037_ = l_Lean_Exception_isRuntime(v_a_2035_);
v___y_2030_ = v_a_2035_;
v___y_2031_ = v___x_2037_;
goto v___jp_2029_;
}
else
{
v___y_2030_ = v_a_2035_;
v___y_2031_ = v___x_2036_;
goto v___jp_2029_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___boxed(lean_object* v_as_x27_2057_, lean_object* v_b_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_2057_, v_b_2058_, v___y_2059_, v___y_2060_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec(v_as_x27_2057_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(lean_object* v_decl_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2096_; uint8_t v___y_2097_; lean_object* v_a_2100_; lean_object* v___y_2104_; uint8_t v___y_2105_; lean_object* v_a_2108_; 
switch(lean_obj_tag(v_decl_2063_))
{
case 1:
{
lean_object* v_val_2111_; lean_object* v___x_2112_; lean_object* v_toConstantVal_2113_; lean_object* v_env_2114_; lean_object* v_options_2115_; lean_object* v_cancelTk_x3f_2116_; uint8_t v___x_2117_; lean_object* v___x_2118_; lean_object* v_fallbackDecl_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v_val_2111_ = lean_ctor_get(v_decl_2063_, 0);
v___x_2112_ = lean_st_ref_get(v_a_2065_);
v_toConstantVal_2113_ = lean_ctor_get(v_val_2111_, 0);
v_env_2114_ = lean_ctor_get(v___x_2112_, 0);
lean_inc_ref(v_env_2114_);
lean_dec(v___x_2112_);
v_options_2115_ = lean_ctor_get(v_a_2064_, 2);
v_cancelTk_x3f_2116_ = lean_ctor_get(v_a_2064_, 12);
v___x_2117_ = 0;
lean_inc_ref(v_toConstantVal_2113_);
v___x_2118_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2118_, 0, v_toConstantVal_2113_);
lean_ctor_set_uint8(v___x_2118_, sizeof(void*)*1, v___x_2117_);
v_fallbackDecl_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2119_, 0, v___x_2118_);
v___x_2120_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2114_, v_options_2115_, v_fallbackDecl_2119_, v_cancelTk_x3f_2116_);
lean_dec_ref_known(v_fallbackDecl_2119_, 1);
v___x_2121_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2120_, v_a_2064_, v_a_2065_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2131_; 
lean_dec_ref_known(v_decl_2063_, 1);
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref_known(v___x_2121_, 1);
v___x_2123_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2122_, v_a_2065_);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2131_ == 0)
{
lean_object* v_unused_2132_; 
v_unused_2132_ = lean_ctor_get(v___x_2123_, 0);
lean_dec(v_unused_2132_);
v___x_2125_ = v___x_2123_;
v_isShared_2126_ = v_isSharedCheck_2131_;
goto v_resetjp_2124_;
}
else
{
lean_dec(v___x_2123_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2131_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2127_; lean_object* v___x_2129_; 
v___x_2127_ = lean_box(0);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 0, v___x_2127_);
v___x_2129_ = v___x_2125_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2127_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
else
{
lean_object* v_a_2133_; 
v_a_2133_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2121_, 1);
v_a_2100_ = v_a_2133_;
goto v___jp_2099_;
}
}
case 2:
{
lean_object* v_val_2134_; lean_object* v___x_2135_; lean_object* v_toConstantVal_2136_; lean_object* v_env_2137_; lean_object* v_options_2138_; lean_object* v_cancelTk_x3f_2139_; uint8_t v___x_2140_; lean_object* v___x_2141_; lean_object* v_fallbackDecl_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v_val_2134_ = lean_ctor_get(v_decl_2063_, 0);
v___x_2135_ = lean_st_ref_get(v_a_2065_);
v_toConstantVal_2136_ = lean_ctor_get(v_val_2134_, 0);
v_env_2137_ = lean_ctor_get(v___x_2135_, 0);
lean_inc_ref(v_env_2137_);
lean_dec(v___x_2135_);
v_options_2138_ = lean_ctor_get(v_a_2064_, 2);
v_cancelTk_x3f_2139_ = lean_ctor_get(v_a_2064_, 12);
v___x_2140_ = 0;
lean_inc_ref(v_toConstantVal_2136_);
v___x_2141_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2141_, 0, v_toConstantVal_2136_);
lean_ctor_set_uint8(v___x_2141_, sizeof(void*)*1, v___x_2140_);
v_fallbackDecl_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2142_, 0, v___x_2141_);
v___x_2143_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2137_, v_options_2138_, v_fallbackDecl_2142_, v_cancelTk_x3f_2139_);
lean_dec_ref_known(v_fallbackDecl_2142_, 1);
v___x_2144_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2143_, v_a_2064_, v_a_2065_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2154_; 
lean_dec_ref_known(v_decl_2063_, 1);
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v___x_2146_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2145_, v_a_2065_);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2154_ == 0)
{
lean_object* v_unused_2155_; 
v_unused_2155_ = lean_ctor_get(v___x_2146_, 0);
lean_dec(v_unused_2155_);
v___x_2148_ = v___x_2146_;
v_isShared_2149_ = v_isSharedCheck_2154_;
goto v_resetjp_2147_;
}
else
{
lean_dec(v___x_2146_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2154_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2150_; lean_object* v___x_2152_; 
v___x_2150_ = lean_box(0);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 0, v___x_2150_);
v___x_2152_ = v___x_2148_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
else
{
lean_object* v_a_2156_; 
v_a_2156_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2156_);
lean_dec_ref_known(v___x_2144_, 1);
v_a_2108_ = v_a_2156_;
goto v___jp_2107_;
}
}
default: 
{
v___y_2068_ = v_a_2064_;
v___y_2069_ = v_a_2065_;
goto v___jp_2067_;
}
}
v___jp_2067_:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2070_ = l_Lean_Declaration_getNames(v_decl_2063_);
v___x_2071_ = lean_box(0);
v___x_2072_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2));
v___x_2073_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v___x_2070_, v___x_2072_, v___y_2068_, v___y_2069_);
lean_dec(v___x_2070_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2086_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2076_ = v___x_2073_;
v_isShared_2077_ = v_isSharedCheck_2086_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2073_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2086_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v_fst_2078_; 
v_fst_2078_ = lean_ctor_get(v_a_2074_, 0);
lean_inc(v_fst_2078_);
lean_dec(v_a_2074_);
if (lean_obj_tag(v_fst_2078_) == 0)
{
lean_object* v___x_2080_; 
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 0, v___x_2071_);
v___x_2080_ = v___x_2076_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2071_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
else
{
lean_object* v_val_2082_; lean_object* v___x_2084_; 
v_val_2082_ = lean_ctor_get(v_fst_2078_, 0);
lean_inc(v_val_2082_);
lean_dec_ref_known(v_fst_2078_, 1);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 0, v_val_2082_);
v___x_2084_ = v___x_2076_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_val_2082_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
v_a_2087_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2073_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2073_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
v___jp_2095_:
{
if (v___y_2097_ == 0)
{
lean_dec_ref(v___y_2096_);
v___y_2068_ = v_a_2064_;
v___y_2069_ = v_a_2065_;
goto v___jp_2067_;
}
else
{
lean_object* v___x_2098_; 
lean_dec(v_decl_2063_);
v___x_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2098_, 0, v___y_2096_);
return v___x_2098_;
}
}
v___jp_2099_:
{
uint8_t v___x_2101_; 
v___x_2101_ = l_Lean_Exception_isInterrupt(v_a_2100_);
if (v___x_2101_ == 0)
{
uint8_t v___x_2102_; 
lean_inc_ref(v_a_2100_);
v___x_2102_ = l_Lean_Exception_isRuntime(v_a_2100_);
v___y_2096_ = v_a_2100_;
v___y_2097_ = v___x_2102_;
goto v___jp_2095_;
}
else
{
v___y_2096_ = v_a_2100_;
v___y_2097_ = v___x_2101_;
goto v___jp_2095_;
}
}
v___jp_2103_:
{
if (v___y_2105_ == 0)
{
lean_dec_ref(v___y_2104_);
v___y_2068_ = v_a_2064_;
v___y_2069_ = v_a_2065_;
goto v___jp_2067_;
}
else
{
lean_object* v___x_2106_; 
lean_dec(v_decl_2063_);
v___x_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2106_, 0, v___y_2104_);
return v___x_2106_;
}
}
v___jp_2107_:
{
uint8_t v___x_2109_; 
v___x_2109_ = l_Lean_Exception_isInterrupt(v_a_2108_);
if (v___x_2109_ == 0)
{
uint8_t v___x_2110_; 
lean_inc_ref(v_a_2108_);
v___x_2110_ = l_Lean_Exception_isRuntime(v_a_2108_);
v___y_2104_ = v_a_2108_;
v___y_2105_ = v___x_2110_;
goto v___jp_2103_;
}
else
{
v___y_2104_ = v_a_2108_;
v___y_2105_ = v___x_2109_;
goto v___jp_2103_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom___boxed(lean_object* v_decl_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2157_, v_a_2158_, v_a_2159_);
lean_dec(v_a_2159_);
lean_dec_ref(v_a_2158_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(lean_object* v_00_u03b1_2162_, lean_object* v_x_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v___x_2167_; 
v___x_2167_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_2163_, v___y_2164_, v___y_2165_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___boxed(lean_object* v_00_u03b1_2168_, lean_object* v_x_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
lean_object* v_res_2173_; 
v_res_2173_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(v_00_u03b1_2168_, v_x_2169_, v___y_2170_, v___y_2171_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(lean_object* v_as_2174_, lean_object* v_as_x27_2175_, lean_object* v_b_2176_, lean_object* v_a_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v___x_2181_; 
v___x_2181_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_2175_, v_b_2176_, v___y_2178_, v___y_2179_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___boxed(lean_object* v_as_2182_, lean_object* v_as_x27_2183_, lean_object* v_b_2184_, lean_object* v_a_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(v_as_2182_, v_as_x27_2183_, v_b_2184_, v_a_2185_, v___y_2186_, v___y_2187_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v_as_x27_2183_);
lean_dec(v_as_2182_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(v_00_u03b1_2195_, v___y_2196_, v___y_2197_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(lean_object* v_00_u03b1_2200_, lean_object* v_ex_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v___x_2205_; 
v___x_2205_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_2201_, v___y_2202_, v___y_2203_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2206_, lean_object* v_ex_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(v_00_u03b1_2206_, v_ex_2207_, v___y_2208_, v___y_2209_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2212_, lean_object* v_msg_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_2213_, v___y_2214_, v___y_2215_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2218_, lean_object* v_msg_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(v_00_u03b1_2218_, v_msg_2219_, v___y_2220_, v___y_2221_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
return v_res_2223_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2224_ = lean_unsigned_to_nat(32u);
v___x_2225_ = lean_mk_empty_array_with_capacity(v___x_2224_);
v___x_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
return v___x_2226_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2227_ = ((size_t)5ULL);
v___x_2228_ = lean_unsigned_to_nat(0u);
v___x_2229_ = lean_unsigned_to_nat(32u);
v___x_2230_ = lean_mk_empty_array_with_capacity(v___x_2229_);
v___x_2231_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0);
v___x_2232_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
lean_ctor_set(v___x_2232_, 1, v___x_2230_);
lean_ctor_set(v___x_2232_, 2, v___x_2228_);
lean_ctor_set(v___x_2232_, 3, v___x_2228_);
lean_ctor_set_usize(v___x_2232_, 4, v___x_2227_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(lean_object* v___y_2233_){
_start:
{
lean_object* v___x_2235_; lean_object* v_traceState_2236_; lean_object* v_traces_2237_; lean_object* v___x_2238_; lean_object* v_traceState_2239_; lean_object* v_env_2240_; lean_object* v_nextMacroScope_2241_; lean_object* v_ngen_2242_; lean_object* v_auxDeclNGen_2243_; lean_object* v_cache_2244_; lean_object* v_messages_2245_; lean_object* v_infoState_2246_; lean_object* v_snapshotTasks_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2266_; 
v___x_2235_ = lean_st_ref_get(v___y_2233_);
v_traceState_2236_ = lean_ctor_get(v___x_2235_, 4);
lean_inc_ref(v_traceState_2236_);
lean_dec(v___x_2235_);
v_traces_2237_ = lean_ctor_get(v_traceState_2236_, 0);
lean_inc_ref(v_traces_2237_);
lean_dec_ref(v_traceState_2236_);
v___x_2238_ = lean_st_ref_take(v___y_2233_);
v_traceState_2239_ = lean_ctor_get(v___x_2238_, 4);
v_env_2240_ = lean_ctor_get(v___x_2238_, 0);
v_nextMacroScope_2241_ = lean_ctor_get(v___x_2238_, 1);
v_ngen_2242_ = lean_ctor_get(v___x_2238_, 2);
v_auxDeclNGen_2243_ = lean_ctor_get(v___x_2238_, 3);
v_cache_2244_ = lean_ctor_get(v___x_2238_, 5);
v_messages_2245_ = lean_ctor_get(v___x_2238_, 6);
v_infoState_2246_ = lean_ctor_get(v___x_2238_, 7);
v_snapshotTasks_2247_ = lean_ctor_get(v___x_2238_, 8);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2249_ = v___x_2238_;
v_isShared_2250_ = v_isSharedCheck_2266_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_snapshotTasks_2247_);
lean_inc(v_infoState_2246_);
lean_inc(v_messages_2245_);
lean_inc(v_cache_2244_);
lean_inc(v_traceState_2239_);
lean_inc(v_auxDeclNGen_2243_);
lean_inc(v_ngen_2242_);
lean_inc(v_nextMacroScope_2241_);
lean_inc(v_env_2240_);
lean_dec(v___x_2238_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2266_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
uint64_t v_tid_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2264_; 
v_tid_2251_ = lean_ctor_get_uint64(v_traceState_2239_, sizeof(void*)*1);
v_isSharedCheck_2264_ = !lean_is_exclusive(v_traceState_2239_);
if (v_isSharedCheck_2264_ == 0)
{
lean_object* v_unused_2265_; 
v_unused_2265_ = lean_ctor_get(v_traceState_2239_, 0);
lean_dec(v_unused_2265_);
v___x_2253_ = v_traceState_2239_;
v_isShared_2254_ = v_isSharedCheck_2264_;
goto v_resetjp_2252_;
}
else
{
lean_dec(v_traceState_2239_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2264_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2255_; lean_object* v___x_2257_; 
v___x_2255_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1);
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 0, v___x_2255_);
v___x_2257_ = v___x_2253_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2255_);
lean_ctor_set_uint64(v_reuseFailAlloc_2263_, sizeof(void*)*1, v_tid_2251_);
v___x_2257_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
lean_object* v___x_2259_; 
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 4, v___x_2257_);
v___x_2259_ = v___x_2249_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_env_2240_);
lean_ctor_set(v_reuseFailAlloc_2262_, 1, v_nextMacroScope_2241_);
lean_ctor_set(v_reuseFailAlloc_2262_, 2, v_ngen_2242_);
lean_ctor_set(v_reuseFailAlloc_2262_, 3, v_auxDeclNGen_2243_);
lean_ctor_set(v_reuseFailAlloc_2262_, 4, v___x_2257_);
lean_ctor_set(v_reuseFailAlloc_2262_, 5, v_cache_2244_);
lean_ctor_set(v_reuseFailAlloc_2262_, 6, v_messages_2245_);
lean_ctor_set(v_reuseFailAlloc_2262_, 7, v_infoState_2246_);
lean_ctor_set(v_reuseFailAlloc_2262_, 8, v_snapshotTasks_2247_);
v___x_2259_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2260_ = lean_st_ref_put(v___y_2233_, v___x_2259_);
v___x_2261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2261_, 0, v_traces_2237_);
return v___x_2261_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___boxed(lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2267_);
lean_dec(v___y_2267_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v___x_2273_; 
v___x_2273_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2271_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___boxed(lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(v___y_2274_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(lean_object* v_category_2278_, lean_object* v_opts_2279_, lean_object* v_act_2280_, lean_object* v_decl_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
lean_inc(v___y_2283_);
lean_inc_ref(v___y_2282_);
v___x_2285_ = lean_apply_2(v_act_2280_, v___y_2282_, v___y_2283_);
v___x_2286_ = l_Lean_profileitIOUnsafe___redArg(v_category_2278_, v_opts_2279_, v___x_2285_, v_decl_2281_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg___boxed(lean_object* v_category_2287_, lean_object* v_opts_2288_, lean_object* v_act_2289_, lean_object* v_decl_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v_category_2287_, v_opts_2288_, v_act_2289_, v_decl_2290_, v___y_2291_, v___y_2292_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec_ref(v_opts_2288_);
lean_dec_ref(v_category_2287_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(lean_object* v_00_u03b1_2295_, lean_object* v_category_2296_, lean_object* v_opts_2297_, lean_object* v_act_2298_, lean_object* v_decl_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v_category_2296_, v_opts_2297_, v_act_2298_, v_decl_2299_, v___y_2300_, v___y_2301_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___boxed(lean_object* v_00_u03b1_2304_, lean_object* v_category_2305_, lean_object* v_opts_2306_, lean_object* v_act_2307_, lean_object* v_decl_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(v_00_u03b1_2304_, v_category_2305_, v_opts_2306_, v_act_2307_, v_decl_2308_, v___y_2309_, v___y_2310_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec_ref(v_opts_2306_);
lean_dec_ref(v_category_2305_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(lean_object* v_a_2313_, lean_object* v_a_2314_){
_start:
{
if (lean_obj_tag(v_a_2313_) == 0)
{
lean_object* v___x_2315_; 
v___x_2315_ = l_List_reverse___redArg(v_a_2314_);
return v___x_2315_;
}
else
{
lean_object* v_head_2316_; lean_object* v_tail_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2326_; 
v_head_2316_ = lean_ctor_get(v_a_2313_, 0);
v_tail_2317_ = lean_ctor_get(v_a_2313_, 1);
v_isSharedCheck_2326_ = !lean_is_exclusive(v_a_2313_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2319_ = v_a_2313_;
v_isShared_2320_ = v_isSharedCheck_2326_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_tail_2317_);
lean_inc(v_head_2316_);
lean_dec(v_a_2313_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2326_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2321_; lean_object* v___x_2323_; 
v___x_2321_ = l_Lean_MessageData_ofName(v_head_2316_);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 1, v_a_2314_);
lean_ctor_set(v___x_2319_, 0, v___x_2321_);
v___x_2323_ = v___x_2319_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v___x_2321_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v_a_2314_);
v___x_2323_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
v_a_2313_ = v_tail_2317_;
v_a_2314_ = v___x_2323_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__0));
v___x_2329_ = l_Lean_stringToMessageData(v___x_2328_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(lean_object* v_decl_2330_, lean_object* v_x_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2335_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1);
v___x_2336_ = l_Lean_Declaration_getTopLevelNames(v_decl_2330_);
v___x_2337_ = lean_box(0);
v___x_2338_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2336_, v___x_2337_);
v___x_2339_ = l_Lean_MessageData_ofList(v___x_2338_);
v___x_2340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2335_);
lean_ctor_set(v___x_2340_, 1, v___x_2339_);
v___x_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2340_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed(lean_object* v_decl_2342_, lean_object* v_x_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(v_decl_2342_, v_x_2343_, v___y_2344_, v___y_2345_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec_ref(v_x_2343_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(size_t v_sz_2348_, size_t v_i_2349_, lean_object* v_bs_2350_){
_start:
{
uint8_t v___x_2351_; 
v___x_2351_ = lean_usize_dec_lt(v_i_2349_, v_sz_2348_);
if (v___x_2351_ == 0)
{
return v_bs_2350_;
}
else
{
lean_object* v_v_2352_; lean_object* v_msg_2353_; lean_object* v___x_2354_; lean_object* v_bs_x27_2355_; size_t v___x_2356_; size_t v___x_2357_; lean_object* v___x_2358_; 
v_v_2352_ = lean_array_uget_borrowed(v_bs_2350_, v_i_2349_);
v_msg_2353_ = lean_ctor_get(v_v_2352_, 1);
lean_inc_ref(v_msg_2353_);
v___x_2354_ = lean_unsigned_to_nat(0u);
v_bs_x27_2355_ = lean_array_uset(v_bs_2350_, v_i_2349_, v___x_2354_);
v___x_2356_ = ((size_t)1ULL);
v___x_2357_ = lean_usize_add(v_i_2349_, v___x_2356_);
v___x_2358_ = lean_array_uset(v_bs_x27_2355_, v_i_2349_, v_msg_2353_);
v_i_2349_ = v___x_2357_;
v_bs_2350_ = v___x_2358_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4___boxed(lean_object* v_sz_2360_, lean_object* v_i_2361_, lean_object* v_bs_2362_){
_start:
{
size_t v_sz_boxed_2363_; size_t v_i_boxed_2364_; lean_object* v_res_2365_; 
v_sz_boxed_2363_ = lean_unbox_usize(v_sz_2360_);
lean_dec(v_sz_2360_);
v_i_boxed_2364_ = lean_unbox_usize(v_i_2361_);
lean_dec(v_i_2361_);
v_res_2365_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(v_sz_boxed_2363_, v_i_boxed_2364_, v_bs_2362_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(lean_object* v_oldTraces_2366_, lean_object* v_data_2367_, lean_object* v_ref_2368_, lean_object* v_msg_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v_fileName_2373_; lean_object* v_fileMap_2374_; lean_object* v_options_2375_; lean_object* v_currRecDepth_2376_; lean_object* v_maxRecDepth_2377_; lean_object* v_ref_2378_; lean_object* v_currNamespace_2379_; lean_object* v_openDecls_2380_; lean_object* v_initHeartbeats_2381_; lean_object* v_maxHeartbeats_2382_; lean_object* v_quotContext_2383_; lean_object* v_currMacroScope_2384_; uint8_t v_diag_2385_; lean_object* v_cancelTk_x3f_2386_; uint8_t v_suppressElabErrors_2387_; lean_object* v_inheritedTraceOptions_2388_; lean_object* v___x_2389_; lean_object* v_traceState_2390_; lean_object* v_traces_2391_; lean_object* v_ref_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; size_t v_sz_2395_; size_t v___x_2396_; lean_object* v___x_2397_; lean_object* v_msg_2398_; lean_object* v___x_2399_; lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2437_; 
v_fileName_2373_ = lean_ctor_get(v___y_2370_, 0);
v_fileMap_2374_ = lean_ctor_get(v___y_2370_, 1);
v_options_2375_ = lean_ctor_get(v___y_2370_, 2);
v_currRecDepth_2376_ = lean_ctor_get(v___y_2370_, 3);
v_maxRecDepth_2377_ = lean_ctor_get(v___y_2370_, 4);
v_ref_2378_ = lean_ctor_get(v___y_2370_, 5);
v_currNamespace_2379_ = lean_ctor_get(v___y_2370_, 6);
v_openDecls_2380_ = lean_ctor_get(v___y_2370_, 7);
v_initHeartbeats_2381_ = lean_ctor_get(v___y_2370_, 8);
v_maxHeartbeats_2382_ = lean_ctor_get(v___y_2370_, 9);
v_quotContext_2383_ = lean_ctor_get(v___y_2370_, 10);
v_currMacroScope_2384_ = lean_ctor_get(v___y_2370_, 11);
v_diag_2385_ = lean_ctor_get_uint8(v___y_2370_, sizeof(void*)*14);
v_cancelTk_x3f_2386_ = lean_ctor_get(v___y_2370_, 12);
v_suppressElabErrors_2387_ = lean_ctor_get_uint8(v___y_2370_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2388_ = lean_ctor_get(v___y_2370_, 13);
v___x_2389_ = lean_st_ref_get(v___y_2371_);
v_traceState_2390_ = lean_ctor_get(v___x_2389_, 4);
lean_inc_ref(v_traceState_2390_);
lean_dec(v___x_2389_);
v_traces_2391_ = lean_ctor_get(v_traceState_2390_, 0);
lean_inc_ref(v_traces_2391_);
lean_dec_ref(v_traceState_2390_);
v_ref_2392_ = l_Lean_replaceRef(v_ref_2368_, v_ref_2378_);
lean_inc_ref(v_inheritedTraceOptions_2388_);
lean_inc(v_cancelTk_x3f_2386_);
lean_inc(v_currMacroScope_2384_);
lean_inc(v_quotContext_2383_);
lean_inc(v_maxHeartbeats_2382_);
lean_inc(v_initHeartbeats_2381_);
lean_inc(v_openDecls_2380_);
lean_inc(v_currNamespace_2379_);
lean_inc(v_maxRecDepth_2377_);
lean_inc(v_currRecDepth_2376_);
lean_inc_ref(v_options_2375_);
lean_inc_ref(v_fileMap_2374_);
lean_inc_ref(v_fileName_2373_);
v___x_2393_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2393_, 0, v_fileName_2373_);
lean_ctor_set(v___x_2393_, 1, v_fileMap_2374_);
lean_ctor_set(v___x_2393_, 2, v_options_2375_);
lean_ctor_set(v___x_2393_, 3, v_currRecDepth_2376_);
lean_ctor_set(v___x_2393_, 4, v_maxRecDepth_2377_);
lean_ctor_set(v___x_2393_, 5, v_ref_2392_);
lean_ctor_set(v___x_2393_, 6, v_currNamespace_2379_);
lean_ctor_set(v___x_2393_, 7, v_openDecls_2380_);
lean_ctor_set(v___x_2393_, 8, v_initHeartbeats_2381_);
lean_ctor_set(v___x_2393_, 9, v_maxHeartbeats_2382_);
lean_ctor_set(v___x_2393_, 10, v_quotContext_2383_);
lean_ctor_set(v___x_2393_, 11, v_currMacroScope_2384_);
lean_ctor_set(v___x_2393_, 12, v_cancelTk_x3f_2386_);
lean_ctor_set(v___x_2393_, 13, v_inheritedTraceOptions_2388_);
lean_ctor_set_uint8(v___x_2393_, sizeof(void*)*14, v_diag_2385_);
lean_ctor_set_uint8(v___x_2393_, sizeof(void*)*14 + 1, v_suppressElabErrors_2387_);
v___x_2394_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2391_);
lean_dec_ref(v_traces_2391_);
v_sz_2395_ = lean_array_size(v___x_2394_);
v___x_2396_ = ((size_t)0ULL);
v___x_2397_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(v_sz_2395_, v___x_2396_, v___x_2394_);
v_msg_2398_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2398_, 0, v_data_2367_);
lean_ctor_set(v_msg_2398_, 1, v_msg_2369_);
lean_ctor_set(v_msg_2398_, 2, v___x_2397_);
v___x_2399_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2398_, v___x_2393_, v___y_2371_);
lean_dec_ref_known(v___x_2393_, 14);
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2402_ = v___x_2399_;
v_isShared_2403_ = v_isSharedCheck_2437_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2399_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2437_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2404_; lean_object* v_traceState_2405_; lean_object* v_env_2406_; lean_object* v_nextMacroScope_2407_; lean_object* v_ngen_2408_; lean_object* v_auxDeclNGen_2409_; lean_object* v_cache_2410_; lean_object* v_messages_2411_; lean_object* v_infoState_2412_; lean_object* v_snapshotTasks_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2436_; 
v___x_2404_ = lean_st_ref_take(v___y_2371_);
v_traceState_2405_ = lean_ctor_get(v___x_2404_, 4);
v_env_2406_ = lean_ctor_get(v___x_2404_, 0);
v_nextMacroScope_2407_ = lean_ctor_get(v___x_2404_, 1);
v_ngen_2408_ = lean_ctor_get(v___x_2404_, 2);
v_auxDeclNGen_2409_ = lean_ctor_get(v___x_2404_, 3);
v_cache_2410_ = lean_ctor_get(v___x_2404_, 5);
v_messages_2411_ = lean_ctor_get(v___x_2404_, 6);
v_infoState_2412_ = lean_ctor_get(v___x_2404_, 7);
v_snapshotTasks_2413_ = lean_ctor_get(v___x_2404_, 8);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2415_ = v___x_2404_;
v_isShared_2416_ = v_isSharedCheck_2436_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_snapshotTasks_2413_);
lean_inc(v_infoState_2412_);
lean_inc(v_messages_2411_);
lean_inc(v_cache_2410_);
lean_inc(v_traceState_2405_);
lean_inc(v_auxDeclNGen_2409_);
lean_inc(v_ngen_2408_);
lean_inc(v_nextMacroScope_2407_);
lean_inc(v_env_2406_);
lean_dec(v___x_2404_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2436_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
uint64_t v_tid_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2434_; 
v_tid_2417_ = lean_ctor_get_uint64(v_traceState_2405_, sizeof(void*)*1);
v_isSharedCheck_2434_ = !lean_is_exclusive(v_traceState_2405_);
if (v_isSharedCheck_2434_ == 0)
{
lean_object* v_unused_2435_; 
v_unused_2435_ = lean_ctor_get(v_traceState_2405_, 0);
lean_dec(v_unused_2435_);
v___x_2419_ = v_traceState_2405_;
v_isShared_2420_ = v_isSharedCheck_2434_;
goto v_resetjp_2418_;
}
else
{
lean_dec(v_traceState_2405_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2434_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2424_; 
v___x_2421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2421_, 0, v_ref_2368_);
lean_ctor_set(v___x_2421_, 1, v_a_2400_);
v___x_2422_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2366_, v___x_2421_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 0, v___x_2422_);
v___x_2424_ = v___x_2419_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___x_2422_);
lean_ctor_set_uint64(v_reuseFailAlloc_2433_, sizeof(void*)*1, v_tid_2417_);
v___x_2424_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2426_; 
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 4, v___x_2424_);
v___x_2426_ = v___x_2415_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_env_2406_);
lean_ctor_set(v_reuseFailAlloc_2432_, 1, v_nextMacroScope_2407_);
lean_ctor_set(v_reuseFailAlloc_2432_, 2, v_ngen_2408_);
lean_ctor_set(v_reuseFailAlloc_2432_, 3, v_auxDeclNGen_2409_);
lean_ctor_set(v_reuseFailAlloc_2432_, 4, v___x_2424_);
lean_ctor_set(v_reuseFailAlloc_2432_, 5, v_cache_2410_);
lean_ctor_set(v_reuseFailAlloc_2432_, 6, v_messages_2411_);
lean_ctor_set(v_reuseFailAlloc_2432_, 7, v_infoState_2412_);
lean_ctor_set(v_reuseFailAlloc_2432_, 8, v_snapshotTasks_2413_);
v___x_2426_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2430_; 
v___x_2427_ = lean_st_ref_put(v___y_2371_, v___x_2426_);
v___x_2428_ = lean_box(0);
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 0, v___x_2428_);
v___x_2430_ = v___x_2402_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2428_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2___boxed(lean_object* v_oldTraces_2438_, lean_object* v_data_2439_, lean_object* v_ref_2440_, lean_object* v_msg_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_oldTraces_2438_, v_data_2439_, v_ref_2440_, v_msg_2441_, v___y_2442_, v___y_2443_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(lean_object* v_x_2446_){
_start:
{
if (lean_obj_tag(v_x_2446_) == 0)
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
v_a_2448_ = lean_ctor_get(v_x_2446_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v_x_2446_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v_x_2446_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v_x_2446_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
lean_ctor_set_tag(v___x_2450_, 1);
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
else
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
v_a_2456_ = lean_ctor_get(v_x_2446_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v_x_2446_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v_x_2446_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v_x_2446_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
lean_ctor_set_tag(v___x_2458_, 0);
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg___boxed(lean_object* v_x_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_x_2464_);
return v_res_2466_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(lean_object* v_e_2467_){
_start:
{
if (lean_obj_tag(v_e_2467_) == 0)
{
uint8_t v___x_2468_; 
v___x_2468_ = 2;
return v___x_2468_;
}
else
{
uint8_t v___x_2469_; 
v___x_2469_ = 0;
return v___x_2469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4___boxed(lean_object* v_e_2470_){
_start:
{
uint8_t v_res_2471_; lean_object* v_r_2472_; 
v_res_2471_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(v_e_2470_);
lean_dec_ref(v_e_2470_);
v_r_2472_ = lean_box(v_res_2471_);
return v_r_2472_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2473_; double v___x_2474_; 
v___x_2473_ = lean_unsigned_to_nat(0u);
v___x_2474_ = lean_float_of_nat(v___x_2473_);
return v___x_2474_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2(void){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__1));
v___x_2477_ = l_Lean_stringToMessageData(v___x_2476_);
return v___x_2477_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2478_; double v___x_2479_; 
v___x_2478_ = lean_unsigned_to_nat(1000u);
v___x_2479_ = lean_float_of_nat(v___x_2478_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(lean_object* v_cls_2480_, uint8_t v_collapsed_2481_, lean_object* v_tag_2482_, lean_object* v_opts_2483_, uint8_t v_clsEnabled_2484_, lean_object* v_oldTraces_2485_, lean_object* v_msg_2486_, lean_object* v_resStartStop_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v_fst_2491_; lean_object* v_snd_2492_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v_data_2496_; lean_object* v_fst_2499_; lean_object* v_snd_2500_; lean_object* v___x_2501_; uint8_t v___x_2502_; lean_object* v___y_2504_; lean_object* v_a_2505_; uint8_t v___y_2520_; double v___y_2551_; 
v_fst_2491_ = lean_ctor_get(v_resStartStop_2487_, 0);
lean_inc(v_fst_2491_);
v_snd_2492_ = lean_ctor_get(v_resStartStop_2487_, 1);
lean_inc(v_snd_2492_);
lean_dec_ref(v_resStartStop_2487_);
v_fst_2499_ = lean_ctor_get(v_snd_2492_, 0);
lean_inc(v_fst_2499_);
v_snd_2500_ = lean_ctor_get(v_snd_2492_, 1);
lean_inc(v_snd_2500_);
lean_dec(v_snd_2492_);
v___x_2501_ = l_Lean_trace_profiler;
v___x_2502_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2483_, v___x_2501_);
if (v___x_2502_ == 0)
{
v___y_2520_ = v___x_2502_;
goto v___jp_2519_;
}
else
{
lean_object* v___x_2556_; uint8_t v___x_2557_; 
v___x_2556_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2557_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2483_, v___x_2556_);
if (v___x_2557_ == 0)
{
lean_object* v___x_2558_; lean_object* v___x_2559_; double v___x_2560_; double v___x_2561_; double v___x_2562_; 
v___x_2558_ = l_Lean_trace_profiler_threshold;
v___x_2559_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_2483_, v___x_2558_);
v___x_2560_ = lean_float_of_nat(v___x_2559_);
v___x_2561_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3);
v___x_2562_ = lean_float_div(v___x_2560_, v___x_2561_);
v___y_2551_ = v___x_2562_;
goto v___jp_2550_;
}
else
{
lean_object* v___x_2563_; lean_object* v___x_2564_; double v___x_2565_; 
v___x_2563_ = l_Lean_trace_profiler_threshold;
v___x_2564_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_2483_, v___x_2563_);
v___x_2565_ = lean_float_of_nat(v___x_2564_);
v___y_2551_ = v___x_2565_;
goto v___jp_2550_;
}
}
v___jp_2493_:
{
lean_object* v___x_2497_; 
lean_inc(v___y_2495_);
v___x_2497_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_oldTraces_2485_, v_data_2496_, v___y_2495_, v___y_2494_, v___y_2488_, v___y_2489_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v___x_2498_; 
lean_dec_ref_known(v___x_2497_, 1);
v___x_2498_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_fst_2491_);
return v___x_2498_;
}
else
{
lean_dec(v_fst_2491_);
return v___x_2497_;
}
}
v___jp_2503_:
{
uint8_t v_result_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; double v___x_2509_; lean_object* v_data_2510_; 
v_result_2506_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(v_fst_2491_);
v___x_2507_ = lean_box(v_result_2506_);
v___x_2508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2507_);
v___x_2509_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0);
lean_inc_ref(v_tag_2482_);
lean_inc_ref(v___x_2508_);
lean_inc(v_cls_2480_);
v_data_2510_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2510_, 0, v_cls_2480_);
lean_ctor_set(v_data_2510_, 1, v___x_2508_);
lean_ctor_set(v_data_2510_, 2, v_tag_2482_);
lean_ctor_set_float(v_data_2510_, sizeof(void*)*3, v___x_2509_);
lean_ctor_set_float(v_data_2510_, sizeof(void*)*3 + 8, v___x_2509_);
lean_ctor_set_uint8(v_data_2510_, sizeof(void*)*3 + 16, v_collapsed_2481_);
if (v___x_2502_ == 0)
{
lean_dec_ref_known(v___x_2508_, 1);
lean_dec(v_snd_2500_);
lean_dec(v_fst_2499_);
lean_dec_ref(v_tag_2482_);
lean_dec(v_cls_2480_);
v___y_2494_ = v_a_2505_;
v___y_2495_ = v___y_2504_;
v_data_2496_ = v_data_2510_;
goto v___jp_2493_;
}
else
{
lean_object* v_data_2511_; double v___x_2512_; double v___x_2513_; 
lean_dec_ref_known(v_data_2510_, 3);
v_data_2511_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2511_, 0, v_cls_2480_);
lean_ctor_set(v_data_2511_, 1, v___x_2508_);
lean_ctor_set(v_data_2511_, 2, v_tag_2482_);
v___x_2512_ = lean_unbox_float(v_fst_2499_);
lean_dec(v_fst_2499_);
lean_ctor_set_float(v_data_2511_, sizeof(void*)*3, v___x_2512_);
v___x_2513_ = lean_unbox_float(v_snd_2500_);
lean_dec(v_snd_2500_);
lean_ctor_set_float(v_data_2511_, sizeof(void*)*3 + 8, v___x_2513_);
lean_ctor_set_uint8(v_data_2511_, sizeof(void*)*3 + 16, v_collapsed_2481_);
v___y_2494_ = v_a_2505_;
v___y_2495_ = v___y_2504_;
v_data_2496_ = v_data_2511_;
goto v___jp_2493_;
}
}
v___jp_2514_:
{
lean_object* v_ref_2515_; lean_object* v___x_2516_; 
v_ref_2515_ = lean_ctor_get(v___y_2488_, 5);
lean_inc(v___y_2489_);
lean_inc_ref(v___y_2488_);
lean_inc(v_fst_2491_);
v___x_2516_ = lean_apply_4(v_msg_2486_, v_fst_2491_, v___y_2488_, v___y_2489_, lean_box(0));
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2517_; 
v_a_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_a_2517_);
lean_dec_ref_known(v___x_2516_, 1);
v___y_2504_ = v_ref_2515_;
v_a_2505_ = v_a_2517_;
goto v___jp_2503_;
}
else
{
lean_object* v___x_2518_; 
lean_dec_ref_known(v___x_2516_, 1);
v___x_2518_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2);
v___y_2504_ = v_ref_2515_;
v_a_2505_ = v___x_2518_;
goto v___jp_2503_;
}
}
v___jp_2519_:
{
if (v_clsEnabled_2484_ == 0)
{
if (v___y_2520_ == 0)
{
lean_object* v___x_2521_; lean_object* v_traceState_2522_; lean_object* v_env_2523_; lean_object* v_nextMacroScope_2524_; lean_object* v_ngen_2525_; lean_object* v_auxDeclNGen_2526_; lean_object* v_cache_2527_; lean_object* v_messages_2528_; lean_object* v_infoState_2529_; lean_object* v_snapshotTasks_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2549_; 
lean_dec(v_snd_2500_);
lean_dec(v_fst_2499_);
lean_dec_ref(v_msg_2486_);
lean_dec_ref(v_tag_2482_);
lean_dec(v_cls_2480_);
v___x_2521_ = lean_st_ref_take(v___y_2489_);
v_traceState_2522_ = lean_ctor_get(v___x_2521_, 4);
v_env_2523_ = lean_ctor_get(v___x_2521_, 0);
v_nextMacroScope_2524_ = lean_ctor_get(v___x_2521_, 1);
v_ngen_2525_ = lean_ctor_get(v___x_2521_, 2);
v_auxDeclNGen_2526_ = lean_ctor_get(v___x_2521_, 3);
v_cache_2527_ = lean_ctor_get(v___x_2521_, 5);
v_messages_2528_ = lean_ctor_get(v___x_2521_, 6);
v_infoState_2529_ = lean_ctor_get(v___x_2521_, 7);
v_snapshotTasks_2530_ = lean_ctor_get(v___x_2521_, 8);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2532_ = v___x_2521_;
v_isShared_2533_ = v_isSharedCheck_2549_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_snapshotTasks_2530_);
lean_inc(v_infoState_2529_);
lean_inc(v_messages_2528_);
lean_inc(v_cache_2527_);
lean_inc(v_traceState_2522_);
lean_inc(v_auxDeclNGen_2526_);
lean_inc(v_ngen_2525_);
lean_inc(v_nextMacroScope_2524_);
lean_inc(v_env_2523_);
lean_dec(v___x_2521_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2549_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
uint64_t v_tid_2534_; lean_object* v_traces_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2548_; 
v_tid_2534_ = lean_ctor_get_uint64(v_traceState_2522_, sizeof(void*)*1);
v_traces_2535_ = lean_ctor_get(v_traceState_2522_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v_traceState_2522_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2537_ = v_traceState_2522_;
v_isShared_2538_ = v_isSharedCheck_2548_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_traces_2535_);
lean_dec(v_traceState_2522_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2548_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2539_; lean_object* v___x_2541_; 
v___x_2539_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2485_, v_traces_2535_);
lean_dec_ref(v_traces_2535_);
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 0, v___x_2539_);
v___x_2541_ = v___x_2537_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v___x_2539_);
lean_ctor_set_uint64(v_reuseFailAlloc_2547_, sizeof(void*)*1, v_tid_2534_);
v___x_2541_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
lean_object* v___x_2543_; 
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 4, v___x_2541_);
v___x_2543_ = v___x_2532_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_env_2523_);
lean_ctor_set(v_reuseFailAlloc_2546_, 1, v_nextMacroScope_2524_);
lean_ctor_set(v_reuseFailAlloc_2546_, 2, v_ngen_2525_);
lean_ctor_set(v_reuseFailAlloc_2546_, 3, v_auxDeclNGen_2526_);
lean_ctor_set(v_reuseFailAlloc_2546_, 4, v___x_2541_);
lean_ctor_set(v_reuseFailAlloc_2546_, 5, v_cache_2527_);
lean_ctor_set(v_reuseFailAlloc_2546_, 6, v_messages_2528_);
lean_ctor_set(v_reuseFailAlloc_2546_, 7, v_infoState_2529_);
lean_ctor_set(v_reuseFailAlloc_2546_, 8, v_snapshotTasks_2530_);
v___x_2543_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2544_ = lean_st_ref_put(v___y_2489_, v___x_2543_);
v___x_2545_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_fst_2491_);
return v___x_2545_;
}
}
}
}
}
else
{
goto v___jp_2514_;
}
}
else
{
goto v___jp_2514_;
}
}
v___jp_2550_:
{
double v___x_2552_; double v___x_2553_; double v___x_2554_; uint8_t v___x_2555_; 
v___x_2552_ = lean_unbox_float(v_snd_2500_);
v___x_2553_ = lean_unbox_float(v_fst_2499_);
v___x_2554_ = lean_float_sub(v___x_2552_, v___x_2553_);
v___x_2555_ = lean_float_decLt(v___y_2551_, v___x_2554_);
v___y_2520_ = v___x_2555_;
goto v___jp_2519_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___boxed(lean_object* v_cls_2566_, lean_object* v_collapsed_2567_, lean_object* v_tag_2568_, lean_object* v_opts_2569_, lean_object* v_clsEnabled_2570_, lean_object* v_oldTraces_2571_, lean_object* v_msg_2572_, lean_object* v_resStartStop_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
uint8_t v_collapsed_boxed_2577_; uint8_t v_clsEnabled_boxed_2578_; lean_object* v_res_2579_; 
v_collapsed_boxed_2577_ = lean_unbox(v_collapsed_2567_);
v_clsEnabled_boxed_2578_ = lean_unbox(v_clsEnabled_2570_);
v_res_2579_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_2566_, v_collapsed_boxed_2577_, v_tag_2568_, v_opts_2569_, v_clsEnabled_boxed_2578_, v_oldTraces_2571_, v_msg_2572_, v_resStartStop_2573_, v___y_2574_, v___y_2575_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec_ref(v_opts_2569_);
return v_res_2579_;
}
}
static double _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2582_; double v___x_2583_; 
v___x_2582_ = lean_unsigned_to_nat(1000000000u);
v___x_2583_ = lean_float_of_nat(v___x_2582_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(lean_object* v_decl_2584_, lean_object* v___x_2585_, uint8_t v___x_2586_, lean_object* v___x_2587_, lean_object* v___f_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v___y_2593_; lean_object* v___y_2594_; uint8_t v___y_2595_; lean_object* v___y_2606_; lean_object* v_a_2607_; lean_object* v___y_2611_; lean_object* v___y_2612_; uint8_t v___y_2613_; lean_object* v___y_2624_; lean_object* v_a_2625_; lean_object* v_options_2628_; uint8_t v_hasTrace_2629_; 
v_options_2628_ = lean_ctor_get(v___y_2589_, 2);
v_hasTrace_2629_ = lean_ctor_get_uint8(v_options_2628_, sizeof(void*)*1);
if (v_hasTrace_2629_ == 0)
{
lean_object* v_cancelTk_x3f_2630_; lean_object* v___x_2631_; 
lean_dec_ref(v___f_2588_);
lean_dec_ref(v___x_2587_);
lean_dec(v___x_2585_);
v_cancelTk_x3f_2630_ = lean_ctor_get(v___y_2589_, 12);
lean_inc(v_decl_2584_);
v___x_2631_ = l_Lean_warnIfUsesSorry(v_decl_2584_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v___x_2632_; lean_object* v_env_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
lean_dec_ref_known(v___x_2631_, 1);
v___x_2632_ = lean_st_ref_get(v___y_2590_);
v_env_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc_ref(v_env_2633_);
lean_dec(v___x_2632_);
v___x_2634_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2633_, v_options_2628_, v_decl_2584_, v_cancelTk_x3f_2630_);
v___x_2635_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2634_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v_a_2636_; lean_object* v___x_2637_; 
lean_dec(v_decl_2584_);
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_a_2636_);
lean_dec_ref_known(v___x_2635_, 1);
v___x_2637_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2636_, v___y_2590_);
return v___x_2637_;
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
v_a_2638_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2635_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2635_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
lean_inc(v_a_2638_);
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
v___y_2624_ = v___x_2643_;
v_a_2625_ = v_a_2638_;
goto v___jp_2623_;
}
}
}
}
else
{
lean_dec(v_decl_2584_);
return v___x_2631_;
}
}
else
{
lean_object* v_cancelTk_x3f_2646_; lean_object* v_inheritedTraceOptions_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; uint8_t v___x_2650_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v_a_2654_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v_a_2669_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v_a_2674_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; uint8_t v___y_2686_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v_a_2691_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v_a_2697_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v_a_2709_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v_a_2714_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; uint8_t v___y_2726_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v_a_2731_; 
v_cancelTk_x3f_2646_ = lean_ctor_get(v___y_2589_, 12);
v_inheritedTraceOptions_2647_ = lean_ctor_get(v___y_2589_, 13);
v___x_2648_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v___x_2585_);
v___x_2649_ = l_Lean_Name_append(v___x_2648_, v___x_2585_);
v___x_2650_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2647_, v_options_2628_, v___x_2649_);
lean_dec(v___x_2649_);
if (v___x_2650_ == 0)
{
lean_object* v___x_2759_; uint8_t v___x_2760_; 
v___x_2759_ = l_Lean_trace_profiler;
v___x_2760_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2628_, v___x_2759_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; 
lean_dec_ref(v___f_2588_);
lean_dec_ref(v___x_2587_);
lean_dec(v___x_2585_);
lean_inc(v_decl_2584_);
v___x_2761_ = l_Lean_warnIfUsesSorry(v_decl_2584_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v___x_2762_; lean_object* v_env_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
lean_dec_ref_known(v___x_2761_, 1);
v___x_2762_ = lean_st_ref_get(v___y_2590_);
v_env_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc_ref(v_env_2763_);
lean_dec(v___x_2762_);
v___x_2764_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2763_, v_options_2628_, v_decl_2584_, v_cancelTk_x3f_2646_);
v___x_2765_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2764_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_a_2766_; lean_object* v___x_2767_; 
lean_dec(v_decl_2584_);
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_a_2766_);
lean_dec_ref_known(v___x_2765_, 1);
v___x_2767_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2766_, v___y_2590_);
return v___x_2767_;
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
v_a_2768_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2765_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2765_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
lean_inc(v_a_2768_);
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
v___y_2606_ = v___x_2773_;
v_a_2607_ = v_a_2768_;
goto v___jp_2605_;
}
}
}
}
else
{
lean_dec(v_decl_2584_);
return v___x_2761_;
}
}
else
{
goto v___jp_2734_;
}
}
else
{
goto v___jp_2734_;
}
v___jp_2651_:
{
lean_object* v___x_2655_; double v___x_2656_; double v___x_2657_; double v___x_2658_; double v___x_2659_; double v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2655_ = lean_io_mono_nanos_now();
v___x_2656_ = lean_float_of_nat(v___y_2653_);
v___x_2657_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_2658_ = lean_float_div(v___x_2656_, v___x_2657_);
v___x_2659_ = lean_float_of_nat(v___x_2655_);
v___x_2660_ = lean_float_div(v___x_2659_, v___x_2657_);
v___x_2661_ = lean_box_float(v___x_2658_);
v___x_2662_ = lean_box_float(v___x_2660_);
v___x_2663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2661_);
lean_ctor_set(v___x_2663_, 1, v___x_2662_);
v___x_2664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2664_, 0, v_a_2654_);
lean_ctor_set(v___x_2664_, 1, v___x_2663_);
v___x_2665_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2585_, v___x_2586_, v___x_2587_, v_options_2628_, v___x_2650_, v___y_2652_, v___f_2588_, v___x_2664_, v___y_2589_, v___y_2590_);
return v___x_2665_;
}
v___jp_2666_:
{
lean_object* v___x_2670_; 
v___x_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2670_, 0, v_a_2669_);
v___y_2652_ = v___y_2667_;
v___y_2653_ = v___y_2668_;
v_a_2654_ = v___x_2670_;
goto v___jp_2651_;
}
v___jp_2671_:
{
lean_object* v___x_2675_; 
v___x_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2675_, 0, v_a_2674_);
v___y_2652_ = v___y_2672_;
v___y_2653_ = v___y_2673_;
v_a_2654_ = v___x_2675_;
goto v___jp_2651_;
}
v___jp_2676_:
{
if (lean_obj_tag(v___y_2679_) == 0)
{
lean_object* v_a_2680_; 
v_a_2680_ = lean_ctor_get(v___y_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v___y_2679_, 1);
v___y_2672_ = v___y_2677_;
v___y_2673_ = v___y_2678_;
v_a_2674_ = v_a_2680_;
goto v___jp_2671_;
}
else
{
lean_object* v_a_2681_; 
v_a_2681_ = lean_ctor_get(v___y_2679_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___y_2679_, 1);
v___y_2667_ = v___y_2677_;
v___y_2668_ = v___y_2678_;
v_a_2669_ = v_a_2681_;
goto v___jp_2666_;
}
}
v___jp_2682_:
{
if (v___y_2686_ == 0)
{
lean_object* v___x_2687_; 
v___x_2687_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2584_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_dec_ref_known(v___x_2687_, 1);
v___y_2667_ = v___y_2683_;
v___y_2668_ = v___y_2684_;
v_a_2669_ = v___y_2685_;
goto v___jp_2666_;
}
else
{
lean_dec_ref(v___y_2685_);
v___y_2677_ = v___y_2683_;
v___y_2678_ = v___y_2684_;
v___y_2679_ = v___x_2687_;
goto v___jp_2676_;
}
}
else
{
lean_dec(v_decl_2584_);
v___y_2667_ = v___y_2683_;
v___y_2668_ = v___y_2684_;
v_a_2669_ = v___y_2685_;
goto v___jp_2666_;
}
}
v___jp_2688_:
{
uint8_t v___x_2692_; 
v___x_2692_ = l_Lean_Exception_isInterrupt(v_a_2691_);
if (v___x_2692_ == 0)
{
uint8_t v___x_2693_; 
lean_inc_ref(v_a_2691_);
v___x_2693_ = l_Lean_Exception_isRuntime(v_a_2691_);
v___y_2683_ = v___y_2689_;
v___y_2684_ = v___y_2690_;
v___y_2685_ = v_a_2691_;
v___y_2686_ = v___x_2693_;
goto v___jp_2682_;
}
else
{
v___y_2683_ = v___y_2689_;
v___y_2684_ = v___y_2690_;
v___y_2685_ = v_a_2691_;
v___y_2686_ = v___x_2692_;
goto v___jp_2682_;
}
}
v___jp_2694_:
{
lean_object* v___x_2698_; double v___x_2699_; double v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2698_ = lean_io_get_num_heartbeats();
v___x_2699_ = lean_float_of_nat(v___y_2696_);
v___x_2700_ = lean_float_of_nat(v___x_2698_);
v___x_2701_ = lean_box_float(v___x_2699_);
v___x_2702_ = lean_box_float(v___x_2700_);
v___x_2703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2701_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2704_, 0, v_a_2697_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
v___x_2705_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2585_, v___x_2586_, v___x_2587_, v_options_2628_, v___x_2650_, v___y_2695_, v___f_2588_, v___x_2704_, v___y_2589_, v___y_2590_);
return v___x_2705_;
}
v___jp_2706_:
{
lean_object* v___x_2710_; 
v___x_2710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2710_, 0, v_a_2709_);
v___y_2695_ = v___y_2707_;
v___y_2696_ = v___y_2708_;
v_a_2697_ = v___x_2710_;
goto v___jp_2694_;
}
v___jp_2711_:
{
lean_object* v___x_2715_; 
v___x_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2715_, 0, v_a_2714_);
v___y_2695_ = v___y_2712_;
v___y_2696_ = v___y_2713_;
v_a_2697_ = v___x_2715_;
goto v___jp_2694_;
}
v___jp_2716_:
{
if (lean_obj_tag(v___y_2719_) == 0)
{
lean_object* v_a_2720_; 
v_a_2720_ = lean_ctor_get(v___y_2719_, 0);
lean_inc(v_a_2720_);
lean_dec_ref_known(v___y_2719_, 1);
v___y_2712_ = v___y_2717_;
v___y_2713_ = v___y_2718_;
v_a_2714_ = v_a_2720_;
goto v___jp_2711_;
}
else
{
lean_object* v_a_2721_; 
v_a_2721_ = lean_ctor_get(v___y_2719_, 0);
lean_inc(v_a_2721_);
lean_dec_ref_known(v___y_2719_, 1);
v___y_2707_ = v___y_2717_;
v___y_2708_ = v___y_2718_;
v_a_2709_ = v_a_2721_;
goto v___jp_2706_;
}
}
v___jp_2722_:
{
if (v___y_2726_ == 0)
{
lean_object* v___x_2727_; 
v___x_2727_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2584_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_dec_ref_known(v___x_2727_, 1);
v___y_2707_ = v___y_2724_;
v___y_2708_ = v___y_2725_;
v_a_2709_ = v___y_2723_;
goto v___jp_2706_;
}
else
{
lean_dec_ref(v___y_2723_);
v___y_2717_ = v___y_2724_;
v___y_2718_ = v___y_2725_;
v___y_2719_ = v___x_2727_;
goto v___jp_2716_;
}
}
else
{
lean_dec(v_decl_2584_);
v___y_2707_ = v___y_2724_;
v___y_2708_ = v___y_2725_;
v_a_2709_ = v___y_2723_;
goto v___jp_2706_;
}
}
v___jp_2728_:
{
uint8_t v___x_2732_; 
v___x_2732_ = l_Lean_Exception_isInterrupt(v_a_2731_);
if (v___x_2732_ == 0)
{
uint8_t v___x_2733_; 
lean_inc_ref(v_a_2731_);
v___x_2733_ = l_Lean_Exception_isRuntime(v_a_2731_);
v___y_2723_ = v_a_2731_;
v___y_2724_ = v___y_2729_;
v___y_2725_ = v___y_2730_;
v___y_2726_ = v___x_2733_;
goto v___jp_2722_;
}
else
{
v___y_2723_ = v_a_2731_;
v___y_2724_ = v___y_2729_;
v___y_2725_ = v___y_2730_;
v___y_2726_ = v___x_2732_;
goto v___jp_2722_;
}
}
v___jp_2734_:
{
lean_object* v___x_2735_; lean_object* v_a_2736_; lean_object* v___x_2737_; uint8_t v___x_2738_; 
v___x_2735_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2590_);
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2736_);
lean_dec_ref(v___x_2735_);
v___x_2737_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2738_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2628_, v___x_2737_);
if (v___x_2738_ == 0)
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2739_ = lean_io_mono_nanos_now();
lean_inc(v_decl_2584_);
v___x_2740_ = l_Lean_warnIfUsesSorry(v_decl_2584_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v___x_2741_; lean_object* v_env_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
lean_dec_ref_known(v___x_2740_, 1);
v___x_2741_ = lean_st_ref_get(v___y_2590_);
v_env_2742_ = lean_ctor_get(v___x_2741_, 0);
lean_inc_ref(v_env_2742_);
lean_dec(v___x_2741_);
v___x_2743_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2742_, v_options_2628_, v_decl_2584_, v_cancelTk_x3f_2646_);
v___x_2744_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2743_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2746_; lean_object* v_a_2747_; 
lean_dec(v_decl_2584_);
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2745_);
lean_dec_ref_known(v___x_2744_, 1);
v___x_2746_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2745_, v___y_2590_);
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2747_);
lean_dec_ref(v___x_2746_);
v___y_2672_ = v_a_2736_;
v___y_2673_ = v___x_2739_;
v_a_2674_ = v_a_2747_;
goto v___jp_2671_;
}
else
{
lean_object* v_a_2748_; 
v_a_2748_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2748_);
lean_dec_ref_known(v___x_2744_, 1);
v___y_2689_ = v_a_2736_;
v___y_2690_ = v___x_2739_;
v_a_2691_ = v_a_2748_;
goto v___jp_2688_;
}
}
else
{
lean_dec(v_decl_2584_);
v___y_2677_ = v_a_2736_;
v___y_2678_ = v___x_2739_;
v___y_2679_ = v___x_2740_;
goto v___jp_2676_;
}
}
else
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2749_ = lean_io_get_num_heartbeats();
lean_inc(v_decl_2584_);
v___x_2750_ = l_Lean_warnIfUsesSorry(v_decl_2584_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v___x_2751_; lean_object* v_env_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
lean_dec_ref_known(v___x_2750_, 1);
v___x_2751_ = lean_st_ref_get(v___y_2590_);
v_env_2752_ = lean_ctor_get(v___x_2751_, 0);
lean_inc_ref(v_env_2752_);
lean_dec(v___x_2751_);
v___x_2753_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2752_, v_options_2628_, v_decl_2584_, v_cancelTk_x3f_2646_);
v___x_2754_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2753_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; lean_object* v___x_2756_; lean_object* v_a_2757_; 
lean_dec(v_decl_2584_);
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_a_2755_);
lean_dec_ref_known(v___x_2754_, 1);
v___x_2756_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2755_, v___y_2590_);
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2757_);
lean_dec_ref(v___x_2756_);
v___y_2712_ = v_a_2736_;
v___y_2713_ = v___x_2749_;
v_a_2714_ = v_a_2757_;
goto v___jp_2711_;
}
else
{
lean_object* v_a_2758_; 
v_a_2758_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_a_2758_);
lean_dec_ref_known(v___x_2754_, 1);
v___y_2729_ = v_a_2736_;
v___y_2730_ = v___x_2749_;
v_a_2731_ = v_a_2758_;
goto v___jp_2728_;
}
}
else
{
lean_dec(v_decl_2584_);
v___y_2717_ = v_a_2736_;
v___y_2718_ = v___x_2749_;
v___y_2719_ = v___x_2750_;
goto v___jp_2716_;
}
}
}
}
v___jp_2592_:
{
if (v___y_2595_ == 0)
{
lean_object* v___x_2596_; 
lean_dec_ref(v___y_2594_);
v___x_2596_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2584_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2603_ == 0)
{
lean_object* v_unused_2604_; 
v_unused_2604_ = lean_ctor_get(v___x_2596_, 0);
lean_dec(v_unused_2604_);
v___x_2598_ = v___x_2596_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_dec(v___x_2596_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
lean_ctor_set_tag(v___x_2598_, 1);
lean_ctor_set(v___x_2598_, 0, v___y_2593_);
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___y_2593_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
else
{
lean_dec_ref(v___y_2593_);
return v___x_2596_;
}
}
else
{
lean_dec_ref(v___y_2593_);
lean_dec(v_decl_2584_);
return v___y_2594_;
}
}
v___jp_2605_:
{
uint8_t v___x_2608_; 
v___x_2608_ = l_Lean_Exception_isInterrupt(v_a_2607_);
if (v___x_2608_ == 0)
{
uint8_t v___x_2609_; 
lean_inc_ref(v_a_2607_);
v___x_2609_ = l_Lean_Exception_isRuntime(v_a_2607_);
v___y_2593_ = v_a_2607_;
v___y_2594_ = v___y_2606_;
v___y_2595_ = v___x_2609_;
goto v___jp_2592_;
}
else
{
v___y_2593_ = v_a_2607_;
v___y_2594_ = v___y_2606_;
v___y_2595_ = v___x_2608_;
goto v___jp_2592_;
}
}
v___jp_2610_:
{
if (v___y_2613_ == 0)
{
lean_object* v___x_2614_; 
lean_dec_ref(v___y_2611_);
v___x_2614_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2584_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2621_ == 0)
{
lean_object* v_unused_2622_; 
v_unused_2622_ = lean_ctor_get(v___x_2614_, 0);
lean_dec(v_unused_2622_);
v___x_2616_ = v___x_2614_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_dec(v___x_2614_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
lean_ctor_set_tag(v___x_2616_, 1);
lean_ctor_set(v___x_2616_, 0, v___y_2612_);
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v___y_2612_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
else
{
lean_dec_ref(v___y_2612_);
return v___x_2614_;
}
}
else
{
lean_dec_ref(v___y_2612_);
lean_dec(v_decl_2584_);
return v___y_2611_;
}
}
v___jp_2623_:
{
uint8_t v___x_2626_; 
v___x_2626_ = l_Lean_Exception_isInterrupt(v_a_2625_);
if (v___x_2626_ == 0)
{
uint8_t v___x_2627_; 
lean_inc_ref(v_a_2625_);
v___x_2627_ = l_Lean_Exception_isRuntime(v_a_2625_);
v___y_2611_ = v___y_2624_;
v___y_2612_ = v_a_2625_;
v___y_2613_ = v___x_2627_;
goto v___jp_2610_;
}
else
{
v___y_2611_ = v___y_2624_;
v___y_2612_ = v_a_2625_;
v___y_2613_ = v___x_2626_;
goto v___jp_2610_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed(lean_object* v_decl_2776_, lean_object* v___x_2777_, lean_object* v___x_2778_, lean_object* v___x_2779_, lean_object* v___f_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
uint8_t v___x_7927__boxed_2784_; lean_object* v_res_2785_; 
v___x_7927__boxed_2784_ = lean_unbox(v___x_2778_);
v_res_2785_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(v_decl_2776_, v___x_2777_, v___x_7927__boxed_2784_, v___x_2779_, v___f_2780_, v___y_2781_, v___y_2782_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(lean_object* v_decl_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_){
_start:
{
lean_object* v_options_2794_; lean_object* v___f_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; uint8_t v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___f_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v_options_2794_ = lean_ctor_get(v_a_2791_, 2);
lean_inc(v_decl_2790_);
v___f_2795_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2795_, 0, v_decl_2790_);
v___x_2796_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__0));
v___x_2797_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__2));
v___x_2798_ = 1;
v___x_2799_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2800_ = lean_box(v___x_2798_);
v___f_2801_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed), 8, 5);
lean_closure_set(v___f_2801_, 0, v_decl_2790_);
lean_closure_set(v___f_2801_, 1, v___x_2797_);
lean_closure_set(v___f_2801_, 2, v___x_2800_);
lean_closure_set(v___f_2801_, 3, v___x_2799_);
lean_closure_set(v___f_2801_, 4, v___f_2795_);
v___x_2802_ = lean_box(0);
v___x_2803_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v___x_2796_, v_options_2794_, v___f_2801_, v___x_2802_, v_a_2791_, v_a_2792_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___boxed(lean_object* v_decl_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2804_, v_a_2805_, v_a_2806_);
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2805_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(lean_object* v_00_u03b1_2809_, lean_object* v_x_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v___x_2814_; 
v___x_2814_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_x_2810_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2815_, lean_object* v_x_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(v_00_u03b1_2815_, v_x_2816_, v___y_2817_, v___y_2818_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(lean_object* v___y_2821_, lean_object* v_a_2822_, lean_object* v___y_2823_, lean_object* v_a_x3f_2824_){
_start:
{
lean_object* v___x_2826_; lean_object* v_env_2827_; lean_object* v___x_2828_; 
v___x_2826_ = lean_st_ref_get(v___y_2821_);
v_env_2827_ = lean_ctor_get(v___x_2826_, 0);
lean_inc_ref(v_env_2827_);
lean_dec(v___x_2826_);
v___x_2828_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2822_, v_env_2827_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2836_; 
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2831_ = v___x_2828_;
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2828_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2834_; 
if (v_isShared_2832_ == 0)
{
v___x_2834_ = v___x_2831_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
else
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2849_; 
v_a_2837_ = lean_ctor_get(v___x_2828_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2839_ = v___x_2828_;
v_isShared_2840_ = v_isSharedCheck_2849_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2828_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2849_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v_ref_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2847_; 
v_ref_2841_ = lean_ctor_get(v___y_2823_, 5);
v___x_2842_ = lean_io_error_to_string(v_a_2837_);
v___x_2843_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2842_);
v___x_2844_ = l_Lean_MessageData_ofFormat(v___x_2843_);
lean_inc(v_ref_2841_);
v___x_2845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2845_, 0, v_ref_2841_);
lean_ctor_set(v___x_2845_, 1, v___x_2844_);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 0, v___x_2845_);
v___x_2847_ = v___x_2839_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2845_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed(lean_object* v___y_2850_, lean_object* v_a_2851_, lean_object* v___y_2852_, lean_object* v_a_x3f_2853_, lean_object* v___y_2854_){
_start:
{
lean_object* v_res_2855_; 
v_res_2855_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2850_, v_a_2851_, v___y_2852_, v_a_x3f_2853_);
lean_dec(v_a_x3f_2853_);
lean_dec_ref(v___y_2852_);
lean_dec(v___y_2850_);
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(lean_object* v_asyncEnv_2856_, lean_object* v_a_2857_, lean_object* v_decl_2858_, lean_object* v_x_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v___x_2863_; lean_object* v_r_2864_; 
v___x_2863_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_asyncEnv_2856_, v___y_2861_);
lean_dec_ref(v___x_2863_);
v_r_2864_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2858_, v___y_2860_, v___y_2861_);
if (lean_obj_tag(v_r_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2881_; 
v_a_2865_ = lean_ctor_get(v_r_2864_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v_r_2864_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2867_ = v_r_2864_;
v_isShared_2868_ = v_isSharedCheck_2881_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v_r_2864_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2881_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
lean_inc(v_a_2865_);
if (v_isShared_2868_ == 0)
{
lean_ctor_set_tag(v___x_2867_, 1);
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2865_);
v___x_2870_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
lean_object* v___x_2871_; 
v___x_2871_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2861_, v_a_2857_, v___y_2860_, v___x_2870_);
lean_dec_ref(v___x_2870_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2878_ == 0)
{
lean_object* v_unused_2879_; 
v_unused_2879_ = lean_ctor_get(v___x_2871_, 0);
lean_dec(v_unused_2879_);
v___x_2873_ = v___x_2871_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_dec(v___x_2871_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
lean_ctor_set(v___x_2873_, 0, v_a_2865_);
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2865_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
else
{
lean_dec(v_a_2865_);
return v___x_2871_;
}
}
}
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v_a_2882_ = lean_ctor_get(v_r_2864_, 0);
lean_inc(v_a_2882_);
lean_dec_ref_known(v_r_2864_, 1);
v___x_2883_ = lean_box(0);
v___x_2884_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2861_, v_a_2857_, v___y_2860_, v___x_2883_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2891_ == 0)
{
lean_object* v_unused_2892_; 
v_unused_2892_ = lean_ctor_get(v___x_2884_, 0);
lean_dec(v_unused_2892_);
v___x_2886_ = v___x_2884_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_dec(v___x_2884_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
lean_ctor_set_tag(v___x_2886_, 1);
lean_ctor_set(v___x_2886_, 0, v_a_2882_);
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2882_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
else
{
lean_dec(v_a_2882_);
return v___x_2884_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed(lean_object* v_asyncEnv_2893_, lean_object* v_a_2894_, lean_object* v_decl_2895_, lean_object* v_x_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(v_asyncEnv_2893_, v_a_2894_, v_decl_2895_, v_x_2896_, v___y_2897_, v___y_2898_);
lean_dec(v___y_2898_);
lean_dec_ref(v___y_2897_);
lean_dec_ref(v_x_2896_);
return v_res_2900_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2902_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__0));
v___x_2903_ = l_Lean_stringToMessageData(v___x_2902_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(lean_object* v_decl_2904_, lean_object* v_x_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_){
_start:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2909_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1);
v___x_2910_ = l_Lean_Declaration_getNames(v_decl_2904_);
v___x_2911_ = lean_box(0);
v___x_2912_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2910_, v___x_2911_);
v___x_2913_ = l_Lean_MessageData_ofList(v___x_2912_);
v___x_2914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2909_);
lean_ctor_set(v___x_2914_, 1, v___x_2913_);
v___x_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2914_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___boxed(lean_object* v_decl_2916_, lean_object* v_x_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v_decl_2916_, v_x_2917_, v___y_2918_, v___y_2919_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec_ref(v_x_2917_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(lean_object* v_cls_2924_, lean_object* v_msg_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v_ref_2929_; lean_object* v___x_2930_; lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2975_; 
v_ref_2929_ = lean_ctor_get(v___y_2926_, 5);
v___x_2930_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2925_, v___y_2926_, v___y_2927_);
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2933_ = v___x_2930_;
v_isShared_2934_ = v_isSharedCheck_2975_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2930_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2975_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2935_; lean_object* v_traceState_2936_; lean_object* v_env_2937_; lean_object* v_nextMacroScope_2938_; lean_object* v_ngen_2939_; lean_object* v_auxDeclNGen_2940_; lean_object* v_cache_2941_; lean_object* v_messages_2942_; lean_object* v_infoState_2943_; lean_object* v_snapshotTasks_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2974_; 
v___x_2935_ = lean_st_ref_take(v___y_2927_);
v_traceState_2936_ = lean_ctor_get(v___x_2935_, 4);
v_env_2937_ = lean_ctor_get(v___x_2935_, 0);
v_nextMacroScope_2938_ = lean_ctor_get(v___x_2935_, 1);
v_ngen_2939_ = lean_ctor_get(v___x_2935_, 2);
v_auxDeclNGen_2940_ = lean_ctor_get(v___x_2935_, 3);
v_cache_2941_ = lean_ctor_get(v___x_2935_, 5);
v_messages_2942_ = lean_ctor_get(v___x_2935_, 6);
v_infoState_2943_ = lean_ctor_get(v___x_2935_, 7);
v_snapshotTasks_2944_ = lean_ctor_get(v___x_2935_, 8);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2946_ = v___x_2935_;
v_isShared_2947_ = v_isSharedCheck_2974_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_snapshotTasks_2944_);
lean_inc(v_infoState_2943_);
lean_inc(v_messages_2942_);
lean_inc(v_cache_2941_);
lean_inc(v_traceState_2936_);
lean_inc(v_auxDeclNGen_2940_);
lean_inc(v_ngen_2939_);
lean_inc(v_nextMacroScope_2938_);
lean_inc(v_env_2937_);
lean_dec(v___x_2935_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2974_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
uint64_t v_tid_2948_; lean_object* v_traces_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2973_; 
v_tid_2948_ = lean_ctor_get_uint64(v_traceState_2936_, sizeof(void*)*1);
v_traces_2949_ = lean_ctor_get(v_traceState_2936_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v_traceState_2936_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2951_ = v_traceState_2936_;
v_isShared_2952_ = v_isSharedCheck_2973_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_traces_2949_);
lean_dec(v_traceState_2936_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2973_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2953_; double v___x_2954_; uint8_t v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2963_; 
v___x_2953_ = lean_box(0);
v___x_2954_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0);
v___x_2955_ = 0;
v___x_2956_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2957_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2957_, 0, v_cls_2924_);
lean_ctor_set(v___x_2957_, 1, v___x_2953_);
lean_ctor_set(v___x_2957_, 2, v___x_2956_);
lean_ctor_set_float(v___x_2957_, sizeof(void*)*3, v___x_2954_);
lean_ctor_set_float(v___x_2957_, sizeof(void*)*3 + 8, v___x_2954_);
lean_ctor_set_uint8(v___x_2957_, sizeof(void*)*3 + 16, v___x_2955_);
v___x_2958_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___closed__0));
v___x_2959_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2957_);
lean_ctor_set(v___x_2959_, 1, v_a_2931_);
lean_ctor_set(v___x_2959_, 2, v___x_2958_);
lean_inc(v_ref_2929_);
v___x_2960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2960_, 0, v_ref_2929_);
lean_ctor_set(v___x_2960_, 1, v___x_2959_);
v___x_2961_ = l_Lean_PersistentArray_push___redArg(v_traces_2949_, v___x_2960_);
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 0, v___x_2961_);
v___x_2963_ = v___x_2951_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v___x_2961_);
lean_ctor_set_uint64(v_reuseFailAlloc_2972_, sizeof(void*)*1, v_tid_2948_);
v___x_2963_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
lean_object* v___x_2965_; 
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 4, v___x_2963_);
v___x_2965_ = v___x_2946_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_env_2937_);
lean_ctor_set(v_reuseFailAlloc_2971_, 1, v_nextMacroScope_2938_);
lean_ctor_set(v_reuseFailAlloc_2971_, 2, v_ngen_2939_);
lean_ctor_set(v_reuseFailAlloc_2971_, 3, v_auxDeclNGen_2940_);
lean_ctor_set(v_reuseFailAlloc_2971_, 4, v___x_2963_);
lean_ctor_set(v_reuseFailAlloc_2971_, 5, v_cache_2941_);
lean_ctor_set(v_reuseFailAlloc_2971_, 6, v_messages_2942_);
lean_ctor_set(v_reuseFailAlloc_2971_, 7, v_infoState_2943_);
lean_ctor_set(v_reuseFailAlloc_2971_, 8, v_snapshotTasks_2944_);
v___x_2965_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2969_; 
v___x_2966_ = lean_st_ref_put(v___y_2927_, v___x_2965_);
v___x_2967_ = lean_box(0);
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 0, v___x_2967_);
v___x_2969_ = v___x_2933_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___boxed(lean_object* v_cls_2976_, lean_object* v_msg_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2976_, v_msg_2977_, v___y_2978_, v___y_2979_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
return v_res_2981_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2983_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__0));
v___x_2984_ = l_Lean_stringToMessageData(v___x_2983_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(lean_object* v_decl_2985_, lean_object* v_cls_2986_, lean_object* v_x_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_){
_start:
{
lean_object* v_options_2991_; uint8_t v_hasTrace_2992_; 
v_options_2991_ = lean_ctor_get(v___y_2988_, 2);
v_hasTrace_2992_ = lean_ctor_get_uint8(v_options_2991_, sizeof(void*)*1);
if (v_hasTrace_2992_ == 0)
{
lean_object* v___x_2993_; 
lean_dec(v_cls_2986_);
v___x_2993_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2985_, v___y_2988_, v___y_2989_);
return v___x_2993_;
}
else
{
lean_object* v_inheritedTraceOptions_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; uint8_t v___x_2997_; 
v_inheritedTraceOptions_2994_ = lean_ctor_get(v___y_2988_, 13);
v___x_2995_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2986_);
v___x_2996_ = l_Lean_Name_append(v___x_2995_, v_cls_2986_);
v___x_2997_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2994_, v_options_2991_, v___x_2996_);
lean_dec(v___x_2996_);
if (v___x_2997_ == 0)
{
lean_object* v___x_2998_; 
lean_dec(v_cls_2986_);
v___x_2998_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2985_, v___y_2988_, v___y_2989_);
return v___x_2998_;
}
else
{
lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2999_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1);
v___x_3000_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2986_, v___x_2999_, v___y_2988_, v___y_2989_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v___x_3001_; 
lean_dec_ref_known(v___x_3000_, 1);
v___x_3001_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2985_, v___y_2988_, v___y_2989_);
return v___x_3001_;
}
else
{
lean_dec(v_decl_2985_);
return v___x_3000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed(lean_object* v_decl_3002_, lean_object* v_cls_3003_, lean_object* v_x_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_){
_start:
{
lean_object* v_res_3008_; 
v_res_3008_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3002_, v_cls_3003_, v_x_3004_, v___y_3005_, v___y_3006_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
lean_dec(v_x_3004_);
return v_res_3008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(lean_object* v_opt_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v_options_3012_; uint8_t v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v_options_3012_ = lean_ctor_get(v___y_3010_, 2);
v___x_3013_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3012_, v_opt_3009_);
v___x_3014_ = lean_box(v___x_3013_);
v___x_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3014_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg___boxed(lean_object* v_opt_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_3016_, v___y_3017_);
lean_dec_ref(v___y_3017_);
lean_dec_ref(v_opt_3016_);
return v_res_3019_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(lean_object* v_x_3020_){
_start:
{
if (lean_obj_tag(v_x_3020_) == 0)
{
uint8_t v___x_3021_; 
v___x_3021_ = 1;
return v___x_3021_;
}
else
{
lean_object* v_head_3022_; lean_object* v_tail_3023_; uint8_t v___x_3024_; 
v_head_3022_ = lean_ctor_get(v_x_3020_, 0);
v_tail_3023_ = lean_ctor_get(v_x_3020_, 1);
v___x_3024_ = l_Lean_isPrivateName(v_head_3022_);
if (v___x_3024_ == 0)
{
return v___x_3024_;
}
else
{
v_x_3020_ = v_tail_3023_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2___boxed(lean_object* v_x_3026_){
_start:
{
uint8_t v_res_3027_; lean_object* v_r_3028_; 
v_res_3027_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v_x_3026_);
lean_dec(v_x_3026_);
v_r_3028_ = lean_box(v_res_3027_);
return v_r_3028_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3(void){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3034_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__2));
v___x_3035_ = l_Lean_stringToMessageData(v___x_3034_);
return v___x_3035_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5(void){
_start:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3037_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__4));
v___x_3038_ = l_Lean_stringToMessageData(v___x_3037_);
return v___x_3038_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7(void){
_start:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3040_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__6));
v___x_3041_ = l_Lean_stringToMessageData(v___x_3040_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(lean_object* v_decl_3042_, uint8_t v_hasTrace_3043_, uint8_t v___x_3044_, lean_object* v___x_3045_, lean_object* v_cls_3046_, lean_object* v___x_3047_, lean_object* v_____x_3048_, lean_object* v_exportedInfo_x3f_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v_a_3056_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v_a_3069_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v_snd_3152_; lean_object* v_fst_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3280_; 
v_snd_3152_ = lean_ctor_get(v_____x_3048_, 1);
v_fst_3153_ = lean_ctor_get(v_____x_3048_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v_____x_3048_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3155_ = v_____x_3048_;
v_isShared_3156_ = v_isSharedCheck_3280_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_snd_3152_);
lean_inc(v_fst_3153_);
lean_dec(v_____x_3048_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3280_;
goto v_resetjp_3154_;
}
v___jp_3053_:
{
lean_object* v___x_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3064_; 
v___x_3057_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3055_, v___y_3054_);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3064_ == 0)
{
lean_object* v_unused_3065_; 
v_unused_3065_ = lean_ctor_get(v___x_3057_, 0);
lean_dec(v_unused_3065_);
v___x_3059_ = v___x_3057_;
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
else
{
lean_dec(v___x_3057_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3062_; 
if (v_isShared_3060_ == 0)
{
lean_ctor_set_tag(v___x_3059_, 1);
lean_ctor_set(v___x_3059_, 0, v_a_3056_);
v___x_3062_ = v___x_3059_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_a_3056_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
v___jp_3066_:
{
lean_object* v___x_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3077_; 
v___x_3070_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3068_, v___y_3067_);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3077_ == 0)
{
lean_object* v_unused_3078_; 
v_unused_3078_ = lean_ctor_get(v___x_3070_, 0);
lean_dec(v_unused_3078_);
v___x_3072_ = v___x_3070_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_dec(v___x_3070_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3075_; 
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 0, v_a_3069_);
v___x_3075_ = v___x_3072_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_a_3069_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
v___jp_3079_:
{
lean_object* v___x_3090_; 
lean_inc_ref(v___y_3080_);
v___x_3090_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3082_, v___y_3080_, v___y_3081_, v___y_3089_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v___x_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3137_; 
lean_dec_ref_known(v___x_3090_, 1);
lean_inc_ref(v___y_3087_);
v___x_3091_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3087_, v___y_3085_);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3137_ == 0)
{
lean_object* v_unused_3138_; 
v_unused_3138_ = lean_ctor_get(v___x_3091_, 0);
lean_dec(v_unused_3138_);
v___x_3093_ = v___x_3091_;
v_isShared_3094_ = v_isSharedCheck_3137_;
goto v_resetjp_3092_;
}
else
{
lean_dec(v___x_3091_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3137_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v_options_3095_; lean_object* v___x_3096_; uint8_t v___x_3097_; 
v_options_3095_ = lean_ctor_get(v___y_3083_, 2);
v___x_3096_ = l_Lean_Elab_async;
v___x_3097_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3095_, v___x_3096_);
if (v___x_3097_ == 0)
{
lean_object* v___x_3098_; lean_object* v_r_3099_; 
lean_del_object(v___x_3093_);
lean_dec_ref(v___y_3088_);
lean_dec_ref(v___y_3086_);
v___x_3098_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3080_, v___y_3085_);
lean_dec_ref(v___x_3098_);
v_r_3099_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3042_, v___y_3083_, v___y_3085_);
if (lean_obj_tag(v_r_3099_) == 0)
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3109_; 
v_a_3100_ = lean_ctor_get(v_r_3099_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v_r_3099_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3102_ = v_r_3099_;
v_isShared_3103_ = v_isSharedCheck_3109_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v_r_3099_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3109_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3105_; 
lean_inc(v_a_3100_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set_tag(v___x_3102_, 1);
v___x_3105_ = v___x_3102_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_a_3100_);
v___x_3105_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
lean_object* v___x_3106_; 
v___x_3106_ = lean_apply_2(v___y_3084_, v___x_3105_, lean_box(0));
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_dec_ref_known(v___x_3106_, 1);
v___y_3067_ = v___y_3085_;
v___y_3068_ = v___y_3087_;
v_a_3069_ = v_a_3100_;
goto v___jp_3066_;
}
else
{
lean_object* v_a_3107_; 
lean_dec(v_a_3100_);
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_a_3107_);
lean_dec_ref_known(v___x_3106_, 1);
v___y_3054_ = v___y_3085_;
v___y_3055_ = v___y_3087_;
v_a_3056_ = v_a_3107_;
goto v___jp_3053_;
}
}
}
}
else
{
lean_object* v_a_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v_a_3110_ = lean_ctor_get(v_r_3099_, 0);
lean_inc(v_a_3110_);
lean_dec_ref_known(v_r_3099_, 1);
v___x_3111_ = lean_box(0);
v___x_3112_ = lean_apply_2(v___y_3084_, v___x_3111_, lean_box(0));
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_dec_ref_known(v___x_3112_, 1);
v___y_3054_ = v___y_3085_;
v___y_3055_ = v___y_3087_;
v_a_3056_ = v_a_3110_;
goto v___jp_3053_;
}
else
{
lean_object* v_a_3113_; 
lean_dec(v_a_3110_);
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
lean_inc(v_a_3113_);
lean_dec_ref_known(v___x_3112_, 1);
v___y_3054_ = v___y_3085_;
v___y_3055_ = v___y_3087_;
v_a_3056_ = v_a_3113_;
goto v___jp_3053_;
}
}
}
else
{
lean_object* v___x_3114_; lean_object* v___x_3116_; 
lean_dec_ref(v___y_3087_);
lean_dec_ref(v___y_3084_);
lean_dec_ref(v___y_3080_);
lean_dec(v_decl_3042_);
v___x_3114_ = l_IO_CancelToken_new();
if (v_isShared_3094_ == 0)
{
lean_ctor_set_tag(v___x_3093_, 1);
lean_ctor_set(v___x_3093_, 0, v___x_3114_);
v___x_3116_ = v___x_3093_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v___x_3114_);
v___x_3116_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3117_ = lean_unsigned_to_nat(0u);
v___x_3118_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_3119_ = l_Lean_Name_toString(v___x_3118_, v_hasTrace_3043_);
lean_inc_ref(v___x_3116_);
v___x_3120_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3086_, v___x_3116_, v___x_3119_, v___y_3083_, v___y_3085_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v_a_3121_; lean_object* v_checked_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_a_3121_);
lean_dec_ref_known(v___x_3120_, 1);
v_checked_3122_ = lean_ctor_get(v___y_3088_, 2);
lean_inc_ref(v_checked_3122_);
lean_dec_ref(v___y_3088_);
v___x_3123_ = lean_io_map_task(v_a_3121_, v_checked_3122_, v___x_3117_, v___x_3044_);
v___x_3124_ = lean_box(0);
v___x_3125_ = lean_box(2);
v___x_3126_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3124_);
lean_ctor_set(v___x_3126_, 1, v___x_3125_);
lean_ctor_set(v___x_3126_, 2, v___x_3116_);
lean_ctor_set(v___x_3126_, 3, v___x_3123_);
v___x_3127_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3126_, v___y_3085_);
return v___x_3127_;
}
else
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3135_; 
lean_dec_ref(v___x_3116_);
lean_dec_ref(v___y_3088_);
v_a_3128_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3130_ = v___x_3120_;
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3120_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3133_; 
if (v_isShared_3131_ == 0)
{
v___x_3133_ = v___x_3130_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_a_3128_);
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
}
}
}
else
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3151_; 
lean_dec_ref(v___y_3088_);
lean_dec_ref(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec_ref(v___y_3084_);
lean_dec_ref(v___y_3080_);
lean_dec(v_decl_3042_);
v_a_3139_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3141_ = v___x_3090_;
v_isShared_3142_ = v_isSharedCheck_3151_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3090_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3151_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v_ref_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3149_; 
v_ref_3143_ = lean_ctor_get(v___y_3083_, 5);
v___x_3144_ = lean_io_error_to_string(v_a_3139_);
v___x_3145_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3144_);
v___x_3146_ = l_Lean_MessageData_ofFormat(v___x_3145_);
lean_inc(v_ref_3143_);
v___x_3147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3147_, 0, v_ref_3143_);
lean_ctor_set(v___x_3147_, 1, v___x_3146_);
if (v_isShared_3142_ == 0)
{
lean_ctor_set(v___x_3141_, 0, v___x_3147_);
v___x_3149_ = v___x_3141_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3147_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
v_resetjp_3154_:
{
lean_object* v_fst_3157_; lean_object* v_snd_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3279_; 
v_fst_3157_ = lean_ctor_get(v_snd_3152_, 0);
v_snd_3158_ = lean_ctor_get(v_snd_3152_, 1);
v_isSharedCheck_3279_ = !lean_is_exclusive(v_snd_3152_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3160_ = v_snd_3152_;
v_isShared_3161_ = v_isSharedCheck_3279_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_snd_3158_);
lean_inc(v_fst_3157_);
lean_dec(v_snd_3152_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3279_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v_exportedInfo_x3f_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___x_3269_; lean_object* v_env_3270_; uint8_t v___x_3271_; 
v___x_3269_ = lean_st_ref_get(v___y_3051_);
v_env_3270_ = lean_ctor_get(v___x_3269_, 0);
lean_inc_ref(v_env_3270_);
lean_dec(v___x_3269_);
v___x_3271_ = l_Lean_Environment_containsOnBranch(v_env_3270_, v_fst_3153_);
lean_dec_ref(v_env_3270_);
if (v___x_3271_ == 0)
{
lean_del_object(v___x_3155_);
v___y_3237_ = v___y_3050_;
v___y_3238_ = v___y_3051_;
goto v___jp_3236_;
}
else
{
lean_object* v___x_3272_; lean_object* v_env_3273_; lean_object* v___x_3274_; lean_object* v___x_3276_; 
lean_del_object(v___x_3160_);
lean_dec(v_snd_3158_);
lean_dec(v_fst_3157_);
lean_dec(v_exportedInfo_x3f_3049_);
lean_dec(v___x_3047_);
lean_dec(v_cls_3046_);
lean_dec_ref(v___x_3045_);
lean_dec(v_decl_3042_);
v___x_3272_ = lean_st_ref_get(v___y_3051_);
v_env_3273_ = lean_ctor_get(v___x_3272_, 0);
lean_inc_ref(v_env_3273_);
lean_dec(v___x_3272_);
v___x_3274_ = lean_elab_environment_to_kernel_env(v_env_3273_);
if (v_isShared_3156_ == 0)
{
lean_ctor_set_tag(v___x_3155_, 1);
lean_ctor_set(v___x_3155_, 1, v_fst_3153_);
lean_ctor_set(v___x_3155_, 0, v___x_3274_);
v___x_3276_ = v___x_3155_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v___x_3274_);
lean_ctor_set(v_reuseFailAlloc_3278_, 1, v_fst_3153_);
v___x_3276_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
lean_object* v___x_3277_; 
v___x_3277_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3276_, v___y_3050_, v___y_3051_);
return v___x_3277_;
}
}
v___jp_3162_:
{
uint8_t v___x_3170_; lean_object* v___x_3171_; 
v___x_3170_ = lean_unbox(v_snd_3158_);
lean_dec(v_snd_3158_);
lean_inc_ref(v___y_3165_);
v___x_3171_ = l_Lean_Environment_addConstAsync(v___y_3165_, v_fst_3153_, v___x_3170_, v___y_3169_, v___x_3044_, v_hasTrace_3043_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v_a_3172_; lean_object* v_mainEnv_3173_; lean_object* v_asyncEnv_3174_; lean_object* v___f_3175_; lean_object* v___f_3176_; lean_object* v___x_3177_; 
lean_del_object(v___x_3160_);
v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
lean_inc_n(v_a_3172_, 3);
lean_dec_ref_known(v___x_3171_, 1);
v_mainEnv_3173_ = lean_ctor_get(v_a_3172_, 0);
lean_inc_ref(v_mainEnv_3173_);
v_asyncEnv_3174_ = lean_ctor_get(v_a_3172_, 1);
lean_inc_ref_n(v_asyncEnv_3174_, 2);
lean_inc_ref(v___y_3163_);
lean_inc(v___y_3164_);
v___f_3175_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3175_, 0, v___y_3164_);
lean_closure_set(v___f_3175_, 1, v_a_3172_);
lean_closure_set(v___f_3175_, 2, v___y_3163_);
lean_inc(v_decl_3042_);
v___f_3176_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3176_, 0, v_asyncEnv_3174_);
lean_closure_set(v___f_3176_, 1, v_a_3172_);
lean_closure_set(v___f_3176_, 2, v_decl_3042_);
v___x_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3177_, 0, v_fst_3157_);
if (lean_obj_tag(v___y_3168_) == 0)
{
lean_inc_ref(v___x_3177_);
v___y_3080_ = v_asyncEnv_3174_;
v___y_3081_ = v___x_3177_;
v___y_3082_ = v_a_3172_;
v___y_3083_ = v___y_3166_;
v___y_3084_ = v___f_3175_;
v___y_3085_ = v___y_3167_;
v___y_3086_ = v___f_3176_;
v___y_3087_ = v_mainEnv_3173_;
v___y_3088_ = v___y_3165_;
v___y_3089_ = v___x_3177_;
goto v___jp_3079_;
}
else
{
v___y_3080_ = v_asyncEnv_3174_;
v___y_3081_ = v___x_3177_;
v___y_3082_ = v_a_3172_;
v___y_3083_ = v___y_3166_;
v___y_3084_ = v___f_3175_;
v___y_3085_ = v___y_3167_;
v___y_3086_ = v___f_3176_;
v___y_3087_ = v_mainEnv_3173_;
v___y_3088_ = v___y_3165_;
v___y_3089_ = v___y_3168_;
goto v___jp_3079_;
}
}
else
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3192_; 
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3165_);
lean_dec(v_fst_3157_);
lean_dec(v_decl_3042_);
v_a_3178_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3180_ = v___x_3171_;
v_isShared_3181_ = v_isSharedCheck_3192_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3171_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3192_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v_ref_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3187_; 
v_ref_3182_ = lean_ctor_get(v___y_3166_, 5);
v___x_3183_ = lean_io_error_to_string(v_a_3178_);
v___x_3184_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3183_);
v___x_3185_ = l_Lean_MessageData_ofFormat(v___x_3184_);
lean_inc(v_ref_3182_);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 1, v___x_3185_);
lean_ctor_set(v___x_3160_, 0, v_ref_3182_);
v___x_3187_ = v___x_3160_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_ref_3182_);
lean_ctor_set(v_reuseFailAlloc_3191_, 1, v___x_3185_);
v___x_3187_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
lean_object* v___x_3189_; 
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 0, v___x_3187_);
v___x_3189_ = v___x_3180_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3187_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
}
}
v___jp_3193_:
{
lean_object* v___x_3197_; 
v___x_3197_ = lean_st_ref_get(v___y_3196_);
if (lean_obj_tag(v_exportedInfo_x3f_3194_) == 0)
{
lean_object* v_env_3198_; lean_object* v___x_3199_; 
v_env_3198_ = lean_ctor_get(v___x_3197_, 0);
lean_inc_ref(v_env_3198_);
lean_dec(v___x_3197_);
v___x_3199_ = lean_box(0);
v___y_3163_ = v___y_3195_;
v___y_3164_ = v___y_3196_;
v___y_3165_ = v_env_3198_;
v___y_3166_ = v___y_3195_;
v___y_3167_ = v___y_3196_;
v___y_3168_ = v_exportedInfo_x3f_3194_;
v___y_3169_ = v___x_3199_;
goto v___jp_3162_;
}
else
{
lean_object* v_env_3200_; lean_object* v_val_3201_; uint8_t v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v_env_3200_ = lean_ctor_get(v___x_3197_, 0);
lean_inc_ref(v_env_3200_);
lean_dec(v___x_3197_);
v_val_3201_ = lean_ctor_get(v_exportedInfo_x3f_3194_, 0);
v___x_3202_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3201_);
v___x_3203_ = lean_box(v___x_3202_);
v___x_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
v___y_3163_ = v___y_3195_;
v___y_3164_ = v___y_3196_;
v___y_3165_ = v_env_3200_;
v___y_3166_ = v___y_3195_;
v___y_3167_ = v___y_3196_;
v___y_3168_ = v_exportedInfo_x3f_3194_;
v___y_3169_ = v___x_3204_;
goto v___jp_3162_;
}
}
v___jp_3205_:
{
lean_object* v___x_3208_; 
lean_inc(v_fst_3157_);
v___x_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3208_, 0, v_fst_3157_);
v_exportedInfo_x3f_3194_ = v___x_3208_;
v___y_3195_ = v___y_3206_;
v___y_3196_ = v___y_3207_;
goto v___jp_3193_;
}
v___jp_3209_:
{
lean_object* v___x_3212_; 
lean_inc(v_fst_3157_);
v___x_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3212_, 0, v_fst_3157_);
v_exportedInfo_x3f_3194_ = v___x_3212_;
v___y_3195_ = v___y_3210_;
v___y_3196_ = v___y_3211_;
goto v___jp_3193_;
}
v___jp_3213_:
{
lean_object* v___x_3216_; lean_object* v_env_3217_; lean_object* v_nextMacroScope_3218_; lean_object* v_ngen_3219_; lean_object* v_auxDeclNGen_3220_; lean_object* v_traceState_3221_; lean_object* v_messages_3222_; lean_object* v_infoState_3223_; lean_object* v_snapshotTasks_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3234_; 
v___x_3216_ = lean_st_ref_take(v___y_3215_);
v_env_3217_ = lean_ctor_get(v___x_3216_, 0);
v_nextMacroScope_3218_ = lean_ctor_get(v___x_3216_, 1);
v_ngen_3219_ = lean_ctor_get(v___x_3216_, 2);
v_auxDeclNGen_3220_ = lean_ctor_get(v___x_3216_, 3);
v_traceState_3221_ = lean_ctor_get(v___x_3216_, 4);
v_messages_3222_ = lean_ctor_get(v___x_3216_, 6);
v_infoState_3223_ = lean_ctor_get(v___x_3216_, 7);
v_snapshotTasks_3224_ = lean_ctor_get(v___x_3216_, 8);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3234_ == 0)
{
lean_object* v_unused_3235_; 
v_unused_3235_ = lean_ctor_get(v___x_3216_, 5);
lean_dec(v_unused_3235_);
v___x_3226_ = v___x_3216_;
v_isShared_3227_ = v_isSharedCheck_3234_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_snapshotTasks_3224_);
lean_inc(v_infoState_3223_);
lean_inc(v_messages_3222_);
lean_inc(v_traceState_3221_);
lean_inc(v_auxDeclNGen_3220_);
lean_inc(v_ngen_3219_);
lean_inc(v_nextMacroScope_3218_);
lean_inc(v_env_3217_);
lean_dec(v___x_3216_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3234_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3231_; 
v___x_3228_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3158_);
lean_inc(v_fst_3153_);
v___x_3229_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3228_, v_env_3217_, v_fst_3153_, v_snd_3158_);
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 5, v___x_3045_);
lean_ctor_set(v___x_3226_, 0, v___x_3229_);
v___x_3231_ = v___x_3226_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3229_);
lean_ctor_set(v_reuseFailAlloc_3233_, 1, v_nextMacroScope_3218_);
lean_ctor_set(v_reuseFailAlloc_3233_, 2, v_ngen_3219_);
lean_ctor_set(v_reuseFailAlloc_3233_, 3, v_auxDeclNGen_3220_);
lean_ctor_set(v_reuseFailAlloc_3233_, 4, v_traceState_3221_);
lean_ctor_set(v_reuseFailAlloc_3233_, 5, v___x_3045_);
lean_ctor_set(v_reuseFailAlloc_3233_, 6, v_messages_3222_);
lean_ctor_set(v_reuseFailAlloc_3233_, 7, v_infoState_3223_);
lean_ctor_set(v_reuseFailAlloc_3233_, 8, v_snapshotTasks_3224_);
v___x_3231_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
lean_object* v___x_3232_; 
v___x_3232_ = lean_st_ref_put(v___y_3215_, v___x_3231_);
v_exportedInfo_x3f_3194_ = v_exportedInfo_x3f_3049_;
v___y_3195_ = v___y_3214_;
v___y_3196_ = v___y_3215_;
goto v___jp_3193_;
}
}
}
v___jp_3236_:
{
lean_object* v___x_3239_; uint8_t v___x_3240_; 
lean_inc(v_decl_3042_);
v___x_3239_ = l_Lean_Declaration_getTopLevelNames(v_decl_3042_);
v___x_3240_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3239_);
lean_dec(v___x_3239_);
if (v___x_3240_ == 0)
{
lean_dec(v___x_3047_);
if (lean_obj_tag(v_exportedInfo_x3f_3049_) == 0)
{
if (v___x_3044_ == 0)
{
lean_object* v_options_3241_; uint8_t v_hasTrace_3242_; 
lean_dec_ref(v___x_3045_);
v_options_3241_ = lean_ctor_get(v___y_3237_, 2);
v_hasTrace_3242_ = lean_ctor_get_uint8(v_options_3241_, sizeof(void*)*1);
if (v_hasTrace_3242_ == 0)
{
lean_dec(v_cls_3046_);
v___y_3206_ = v___y_3237_;
v___y_3207_ = v___y_3238_;
goto v___jp_3205_;
}
else
{
lean_object* v_inheritedTraceOptions_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; uint8_t v___x_3246_; 
v_inheritedTraceOptions_3243_ = lean_ctor_get(v___y_3237_, 13);
v___x_3244_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3046_);
v___x_3245_ = l_Lean_Name_append(v___x_3244_, v_cls_3046_);
v___x_3246_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3243_, v_options_3241_, v___x_3245_);
lean_dec(v___x_3245_);
if (v___x_3246_ == 0)
{
lean_dec(v_cls_3046_);
v___y_3206_ = v___y_3237_;
v___y_3207_ = v___y_3238_;
goto v___jp_3205_;
}
else
{
lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3247_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_3248_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3046_, v___x_3247_, v___y_3237_, v___y_3238_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_dec_ref_known(v___x_3248_, 1);
v___y_3206_ = v___y_3237_;
v___y_3207_ = v___y_3238_;
goto v___jp_3205_;
}
else
{
lean_del_object(v___x_3160_);
lean_dec(v_snd_3158_);
lean_dec(v_fst_3157_);
lean_dec(v_fst_3153_);
lean_dec(v_decl_3042_);
return v___x_3248_;
}
}
}
}
else
{
lean_dec(v_cls_3046_);
v___y_3214_ = v___y_3237_;
v___y_3215_ = v___y_3238_;
goto v___jp_3213_;
}
}
else
{
lean_dec(v_cls_3046_);
v___y_3214_ = v___y_3237_;
v___y_3215_ = v___y_3238_;
goto v___jp_3213_;
}
}
else
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v_a_3251_; uint8_t v___x_3252_; 
lean_dec(v_exportedInfo_x3f_3049_);
lean_dec_ref(v___x_3045_);
v___x_3249_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3250_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3249_, v___y_3237_);
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_a_3251_);
lean_dec_ref(v___x_3250_);
v___x_3252_ = lean_unbox(v_a_3251_);
lean_dec(v_a_3251_);
if (v___x_3252_ == 0)
{
lean_object* v_options_3253_; uint8_t v_hasTrace_3254_; 
v_options_3253_ = lean_ctor_get(v___y_3237_, 2);
v_hasTrace_3254_ = lean_ctor_get_uint8(v_options_3253_, sizeof(void*)*1);
if (v_hasTrace_3254_ == 0)
{
lean_dec(v_cls_3046_);
v_exportedInfo_x3f_3194_ = v___x_3047_;
v___y_3195_ = v___y_3237_;
v___y_3196_ = v___y_3238_;
goto v___jp_3193_;
}
else
{
lean_object* v_inheritedTraceOptions_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; uint8_t v___x_3258_; 
v_inheritedTraceOptions_3255_ = lean_ctor_get(v___y_3237_, 13);
v___x_3256_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3046_);
v___x_3257_ = l_Lean_Name_append(v___x_3256_, v_cls_3046_);
v___x_3258_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3255_, v_options_3253_, v___x_3257_);
lean_dec(v___x_3257_);
if (v___x_3258_ == 0)
{
lean_dec(v_cls_3046_);
v_exportedInfo_x3f_3194_ = v___x_3047_;
v___y_3195_ = v___y_3237_;
v___y_3196_ = v___y_3238_;
goto v___jp_3193_;
}
else
{
lean_object* v___x_3259_; lean_object* v___x_3260_; 
v___x_3259_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_3260_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3046_, v___x_3259_, v___y_3237_, v___y_3238_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_dec_ref_known(v___x_3260_, 1);
v_exportedInfo_x3f_3194_ = v___x_3047_;
v___y_3195_ = v___y_3237_;
v___y_3196_ = v___y_3238_;
goto v___jp_3193_;
}
else
{
lean_del_object(v___x_3160_);
lean_dec(v_snd_3158_);
lean_dec(v_fst_3157_);
lean_dec(v_fst_3153_);
lean_dec(v___x_3047_);
lean_dec(v_decl_3042_);
return v___x_3260_;
}
}
}
}
else
{
lean_object* v_options_3261_; uint8_t v_hasTrace_3262_; 
lean_dec(v___x_3047_);
v_options_3261_ = lean_ctor_get(v___y_3237_, 2);
v_hasTrace_3262_ = lean_ctor_get_uint8(v_options_3261_, sizeof(void*)*1);
if (v_hasTrace_3262_ == 0)
{
lean_dec(v_cls_3046_);
v___y_3210_ = v___y_3237_;
v___y_3211_ = v___y_3238_;
goto v___jp_3209_;
}
else
{
lean_object* v_inheritedTraceOptions_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; uint8_t v___x_3266_; 
v_inheritedTraceOptions_3263_ = lean_ctor_get(v___y_3237_, 13);
v___x_3264_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3046_);
v___x_3265_ = l_Lean_Name_append(v___x_3264_, v_cls_3046_);
v___x_3266_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3263_, v_options_3261_, v___x_3265_);
lean_dec(v___x_3265_);
if (v___x_3266_ == 0)
{
lean_dec(v_cls_3046_);
v___y_3210_ = v___y_3237_;
v___y_3211_ = v___y_3238_;
goto v___jp_3209_;
}
else
{
lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3267_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_3268_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3046_, v___x_3267_, v___y_3237_, v___y_3238_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_dec_ref_known(v___x_3268_, 1);
v___y_3210_ = v___y_3237_;
v___y_3211_ = v___y_3238_;
goto v___jp_3209_;
}
else
{
lean_del_object(v___x_3160_);
lean_dec(v_snd_3158_);
lean_dec(v_fst_3157_);
lean_dec(v_fst_3153_);
lean_dec(v_decl_3042_);
return v___x_3268_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed(lean_object* v_decl_3281_, lean_object* v_hasTrace_3282_, lean_object* v___x_3283_, lean_object* v___x_3284_, lean_object* v_cls_3285_, lean_object* v___x_3286_, lean_object* v_____x_3287_, lean_object* v_exportedInfo_x3f_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_){
_start:
{
uint8_t v_hasTrace_boxed_3292_; uint8_t v___x_62998__boxed_3293_; lean_object* v_res_3294_; 
v_hasTrace_boxed_3292_ = lean_unbox(v_hasTrace_3282_);
v___x_62998__boxed_3293_ = lean_unbox(v___x_3283_);
v_res_3294_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(v_decl_3281_, v_hasTrace_boxed_3292_, v___x_62998__boxed_3293_, v___x_3284_, v_cls_3285_, v___x_3286_, v_____x_3287_, v_exportedInfo_x3f_3288_, v___y_3289_, v___y_3290_);
lean_dec(v___y_3290_);
lean_dec_ref(v___y_3289_);
return v_res_3294_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1(void){
_start:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3296_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__0));
v___x_3297_ = l_Lean_stringToMessageData(v___x_3296_);
return v___x_3297_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3(void){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3299_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__2));
v___x_3300_ = l_Lean_stringToMessageData(v___x_3299_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(lean_object* v___f_3301_, uint8_t v_hasTrace_3302_, uint8_t v___x_3303_, lean_object* v_cls_3304_, lean_object* v___x_3305_, uint8_t v_forceExpose_3306_, lean_object* v_defn_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v_exportedInfo_x3f_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; uint8_t v___y_3327_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v_env_3355_; lean_object* v_env_3356_; 
v___x_3338_ = lean_st_ref_get(v___y_3309_);
v___x_3339_ = lean_st_ref_get(v___y_3309_);
v_env_3355_ = lean_ctor_get(v___x_3338_, 0);
lean_inc_ref(v_env_3355_);
lean_dec(v___x_3338_);
v_env_3356_ = lean_ctor_get(v___x_3339_, 0);
lean_inc_ref(v_env_3356_);
lean_dec(v___x_3339_);
if (v_forceExpose_3306_ == 0)
{
goto v___jp_3357_;
}
else
{
if (v___x_3303_ == 0)
{
lean_dec_ref(v_env_3356_);
lean_dec_ref(v_env_3355_);
lean_dec(v_cls_3304_);
v_exportedInfo_x3f_3312_ = v___x_3305_;
v___y_3313_ = v___y_3308_;
v___y_3314_ = v___y_3309_;
goto v___jp_3311_;
}
else
{
goto v___jp_3357_;
}
}
v___jp_3311_:
{
lean_object* v_toConstantVal_3315_; lean_object* v_name_3316_; lean_object* v___x_3317_; uint8_t v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v_toConstantVal_3315_ = lean_ctor_get(v_defn_3307_, 0);
v_name_3316_ = lean_ctor_get(v_toConstantVal_3315_, 0);
lean_inc(v_name_3316_);
v___x_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3317_, 0, v_defn_3307_);
v___x_3318_ = 0;
v___x_3319_ = lean_box(v___x_3318_);
v___x_3320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3317_);
lean_ctor_set(v___x_3320_, 1, v___x_3319_);
v___x_3321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3321_, 0, v_name_3316_);
lean_ctor_set(v___x_3321_, 1, v___x_3320_);
lean_inc(v___y_3314_);
lean_inc_ref(v___y_3313_);
v___x_3322_ = lean_apply_5(v___f_3301_, v___x_3321_, v_exportedInfo_x3f_3312_, v___y_3313_, v___y_3314_, lean_box(0));
return v___x_3322_;
}
v___jp_3323_:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3328_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3328_, 0, v___y_3326_);
lean_ctor_set_uint8(v___x_3328_, sizeof(void*)*1, v___y_3327_);
v___x_3329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3328_);
v___x_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3329_);
v_exportedInfo_x3f_3312_ = v___x_3330_;
v___y_3313_ = v___y_3324_;
v___y_3314_ = v___y_3325_;
goto v___jp_3311_;
}
v___jp_3331_:
{
lean_object* v_toConstantVal_3334_; uint8_t v_safety_3335_; uint8_t v___x_3336_; uint8_t v___x_3337_; 
v_toConstantVal_3334_ = lean_ctor_get(v_defn_3307_, 0);
v_safety_3335_ = lean_ctor_get_uint8(v_defn_3307_, sizeof(void*)*4);
v___x_3336_ = 1;
v___x_3337_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3335_, v___x_3336_);
if (v___x_3337_ == 0)
{
lean_inc_ref(v_toConstantVal_3334_);
v___y_3324_ = v___y_3332_;
v___y_3325_ = v___y_3333_;
v___y_3326_ = v_toConstantVal_3334_;
v___y_3327_ = v_hasTrace_3302_;
goto v___jp_3323_;
}
else
{
lean_inc_ref(v_toConstantVal_3334_);
v___y_3324_ = v___y_3332_;
v___y_3325_ = v___y_3333_;
v___y_3326_ = v_toConstantVal_3334_;
v___y_3327_ = v___x_3303_;
goto v___jp_3323_;
}
}
v___jp_3340_:
{
lean_object* v_options_3341_; uint8_t v_hasTrace_3342_; 
v_options_3341_ = lean_ctor_get(v___y_3308_, 2);
v_hasTrace_3342_ = lean_ctor_get_uint8(v_options_3341_, sizeof(void*)*1);
if (v_hasTrace_3342_ == 0)
{
lean_dec(v_cls_3304_);
v___y_3332_ = v___y_3308_;
v___y_3333_ = v___y_3309_;
goto v___jp_3331_;
}
else
{
lean_object* v_inheritedTraceOptions_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; uint8_t v___x_3346_; 
v_inheritedTraceOptions_3343_ = lean_ctor_get(v___y_3308_, 13);
v___x_3344_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3304_);
v___x_3345_ = l_Lean_Name_append(v___x_3344_, v_cls_3304_);
v___x_3346_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3343_, v_options_3341_, v___x_3345_);
lean_dec(v___x_3345_);
if (v___x_3346_ == 0)
{
lean_dec(v_cls_3304_);
v___y_3332_ = v___y_3308_;
v___y_3333_ = v___y_3309_;
goto v___jp_3331_;
}
else
{
lean_object* v_toConstantVal_3347_; lean_object* v_name_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
v_toConstantVal_3347_ = lean_ctor_get(v_defn_3307_, 0);
v_name_3348_ = lean_ctor_get(v_toConstantVal_3347_, 0);
v___x_3349_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_3348_);
v___x_3350_ = l_Lean_MessageData_ofName(v_name_3348_);
v___x_3351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3349_);
lean_ctor_set(v___x_3351_, 1, v___x_3350_);
v___x_3352_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_3353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3351_);
lean_ctor_set(v___x_3353_, 1, v___x_3352_);
v___x_3354_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3304_, v___x_3353_, v___y_3308_, v___y_3309_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_dec_ref_known(v___x_3354_, 1);
v___y_3332_ = v___y_3308_;
v___y_3333_ = v___y_3309_;
goto v___jp_3331_;
}
else
{
lean_dec_ref(v_defn_3307_);
lean_dec_ref(v___f_3301_);
return v___x_3354_;
}
}
}
}
v___jp_3357_:
{
lean_object* v___x_3358_; uint8_t v_isModule_3359_; 
v___x_3358_ = l_Lean_Environment_header(v_env_3355_);
lean_dec_ref(v_env_3355_);
v_isModule_3359_ = lean_ctor_get_uint8(v___x_3358_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3358_);
if (v_isModule_3359_ == 0)
{
lean_dec_ref(v_env_3356_);
lean_dec(v_cls_3304_);
v_exportedInfo_x3f_3312_ = v___x_3305_;
v___y_3313_ = v___y_3308_;
v___y_3314_ = v___y_3309_;
goto v___jp_3311_;
}
else
{
uint8_t v_isExporting_3360_; 
v_isExporting_3360_ = lean_ctor_get_uint8(v_env_3356_, sizeof(void*)*8);
lean_dec_ref(v_env_3356_);
if (v_isExporting_3360_ == 0)
{
lean_dec(v___x_3305_);
goto v___jp_3340_;
}
else
{
if (v___x_3303_ == 0)
{
lean_dec(v_cls_3304_);
v_exportedInfo_x3f_3312_ = v___x_3305_;
v___y_3313_ = v___y_3308_;
v___y_3314_ = v___y_3309_;
goto v___jp_3311_;
}
else
{
lean_dec(v___x_3305_);
goto v___jp_3340_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___boxed(lean_object* v___f_3361_, lean_object* v_hasTrace_3362_, lean_object* v___x_3363_, lean_object* v_cls_3364_, lean_object* v___x_3365_, lean_object* v_forceExpose_3366_, lean_object* v_defn_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_){
_start:
{
uint8_t v_hasTrace_boxed_3371_; uint8_t v___x_63470__boxed_3372_; uint8_t v_forceExpose_boxed_3373_; lean_object* v_res_3374_; 
v_hasTrace_boxed_3371_ = lean_unbox(v_hasTrace_3362_);
v___x_63470__boxed_3372_ = lean_unbox(v___x_3363_);
v_forceExpose_boxed_3373_ = lean_unbox(v_forceExpose_3366_);
v_res_3374_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v___f_3361_, v_hasTrace_boxed_3371_, v___x_63470__boxed_3372_, v_cls_3364_, v___x_3365_, v_forceExpose_boxed_3373_, v_defn_3367_, v___y_3368_, v___y_3369_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(lean_object* v_val_3375_, lean_object* v___f_3376_, lean_object* v_____r_3377_, lean_object* v_exportedInfo_x3f_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v_toConstantVal_3382_; lean_object* v_name_3383_; lean_object* v___x_3384_; uint8_t v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v_toConstantVal_3382_ = lean_ctor_get(v_val_3375_, 0);
v_name_3383_ = lean_ctor_get(v_toConstantVal_3382_, 0);
lean_inc(v_name_3383_);
v___x_3384_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3384_, 0, v_val_3375_);
v___x_3385_ = 1;
v___x_3386_ = lean_box(v___x_3385_);
v___x_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3384_);
lean_ctor_set(v___x_3387_, 1, v___x_3386_);
v___x_3388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3388_, 0, v_name_3383_);
lean_ctor_set(v___x_3388_, 1, v___x_3387_);
lean_inc(v___y_3380_);
lean_inc_ref(v___y_3379_);
v___x_3389_ = lean_apply_5(v___f_3376_, v___x_3388_, v_exportedInfo_x3f_3378_, v___y_3379_, v___y_3380_, lean_box(0));
return v___x_3389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed(lean_object* v_val_3390_, lean_object* v___f_3391_, lean_object* v_____r_3392_, lean_object* v_exportedInfo_x3f_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_){
_start:
{
lean_object* v_res_3397_; 
v_res_3397_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v_val_3390_, v___f_3391_, v_____r_3392_, v_exportedInfo_x3f_3393_, v___y_3394_, v___y_3395_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(lean_object* v_val_3398_, uint8_t v___x_3399_, lean_object* v___f_3400_, lean_object* v_____r_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_){
_start:
{
lean_object* v_toConstantVal_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v_toConstantVal_3405_ = lean_ctor_get(v_val_3398_, 0);
lean_inc_ref(v_toConstantVal_3405_);
v___x_3406_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3406_, 0, v_toConstantVal_3405_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*1, v___x_3399_);
v___x_3407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3406_);
v___x_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3407_);
v___x_3409_ = lean_box(0);
lean_inc(v___y_3403_);
lean_inc_ref(v___y_3402_);
v___x_3410_ = lean_apply_5(v___f_3400_, v___x_3409_, v___x_3408_, v___y_3402_, v___y_3403_, lean_box(0));
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed(lean_object* v_val_3411_, lean_object* v___x_3412_, lean_object* v___f_3413_, lean_object* v_____r_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
uint8_t v___x_63601__boxed_3418_; lean_object* v_res_3419_; 
v___x_63601__boxed_3418_ = lean_unbox(v___x_3412_);
v_res_3419_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(v_val_3411_, v___x_63601__boxed_3418_, v___f_3413_, v_____r_3414_, v___y_3415_, v___y_3416_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec_ref(v_val_3411_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(lean_object* v_val_3420_, lean_object* v___f_3421_, lean_object* v_____r_3422_, lean_object* v_exportedInfo_x3f_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
lean_object* v_toConstantVal_3427_; lean_object* v_name_3428_; lean_object* v___x_3429_; uint8_t v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v_toConstantVal_3427_ = lean_ctor_get(v_val_3420_, 0);
v_name_3428_ = lean_ctor_get(v_toConstantVal_3427_, 0);
lean_inc(v_name_3428_);
v___x_3429_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3429_, 0, v_val_3420_);
v___x_3430_ = 3;
v___x_3431_ = lean_box(v___x_3430_);
v___x_3432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3429_);
lean_ctor_set(v___x_3432_, 1, v___x_3431_);
v___x_3433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3433_, 0, v_name_3428_);
lean_ctor_set(v___x_3433_, 1, v___x_3432_);
lean_inc(v___y_3425_);
lean_inc_ref(v___y_3424_);
v___x_3434_ = lean_apply_5(v___f_3421_, v___x_3433_, v_exportedInfo_x3f_3423_, v___y_3424_, v___y_3425_, lean_box(0));
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed(lean_object* v_val_3435_, lean_object* v___f_3436_, lean_object* v_____r_3437_, lean_object* v_exportedInfo_x3f_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(v_val_3435_, v___f_3436_, v_____r_3437_, v_exportedInfo_x3f_3438_, v___y_3439_, v___y_3440_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(lean_object* v_val_3443_, lean_object* v___f_3444_, lean_object* v_____r_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_){
_start:
{
lean_object* v_toConstantVal_3449_; uint8_t v_isUnsafe_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; 
v_toConstantVal_3449_ = lean_ctor_get(v_val_3443_, 0);
v_isUnsafe_3450_ = lean_ctor_get_uint8(v_val_3443_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_3449_);
v___x_3451_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3451_, 0, v_toConstantVal_3449_);
lean_ctor_set_uint8(v___x_3451_, sizeof(void*)*1, v_isUnsafe_3450_);
v___x_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3451_);
v___x_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3452_);
v___x_3454_ = lean_box(0);
lean_inc(v___y_3447_);
lean_inc_ref(v___y_3446_);
v___x_3455_ = lean_apply_5(v___f_3444_, v___x_3454_, v___x_3453_, v___y_3446_, v___y_3447_, lean_box(0));
return v___x_3455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed(lean_object* v_val_3456_, lean_object* v___f_3457_, lean_object* v_____r_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_){
_start:
{
lean_object* v_res_3462_; 
v_res_3462_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_val_3456_, v___f_3457_, v_____r_3458_, v___y_3459_, v___y_3460_);
lean_dec(v___y_3460_);
lean_dec_ref(v___y_3459_);
lean_dec_ref(v_val_3456_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(lean_object* v_decl_3463_, uint8_t v___x_3464_, lean_object* v_cls_3465_, lean_object* v___x_3466_, lean_object* v___x_3467_, lean_object* v_____x_3468_, lean_object* v_exportedInfo_x3f_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_){
_start:
{
lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v_a_3476_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v_a_3489_; lean_object* v___y_3500_; lean_object* v___y_3501_; uint8_t v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v_snd_3573_; lean_object* v_fst_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3703_; 
v_snd_3573_ = lean_ctor_get(v_____x_3468_, 1);
v_fst_3574_ = lean_ctor_get(v_____x_3468_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v_____x_3468_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3576_ = v_____x_3468_;
v_isShared_3577_ = v_isSharedCheck_3703_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_snd_3573_);
lean_inc(v_fst_3574_);
lean_dec(v_____x_3468_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3703_;
goto v_resetjp_3575_;
}
v___jp_3473_:
{
lean_object* v___x_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3484_; 
v___x_3477_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3474_, v___y_3475_);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3484_ == 0)
{
lean_object* v_unused_3485_; 
v_unused_3485_ = lean_ctor_get(v___x_3477_, 0);
lean_dec(v_unused_3485_);
v___x_3479_ = v___x_3477_;
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
else
{
lean_dec(v___x_3477_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3482_; 
if (v_isShared_3480_ == 0)
{
lean_ctor_set_tag(v___x_3479_, 1);
lean_ctor_set(v___x_3479_, 0, v_a_3476_);
v___x_3482_ = v___x_3479_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_a_3476_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
v___jp_3486_:
{
lean_object* v___x_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3497_; 
v___x_3490_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3487_, v___y_3488_);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3497_ == 0)
{
lean_object* v_unused_3498_; 
v_unused_3498_ = lean_ctor_get(v___x_3490_, 0);
lean_dec(v_unused_3498_);
v___x_3492_ = v___x_3490_;
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
else
{
lean_dec(v___x_3490_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3495_; 
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 0, v_a_3489_);
v___x_3495_ = v___x_3492_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3489_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
v___jp_3499_:
{
lean_object* v___x_3511_; 
lean_inc_ref(v___y_3504_);
v___x_3511_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3500_, v___y_3504_, v___y_3506_, v___y_3510_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v___x_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3558_; 
lean_dec_ref_known(v___x_3511_, 1);
lean_inc_ref(v___y_3501_);
v___x_3512_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3501_, v___y_3508_);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3558_ == 0)
{
lean_object* v_unused_3559_; 
v_unused_3559_ = lean_ctor_get(v___x_3512_, 0);
lean_dec(v_unused_3559_);
v___x_3514_ = v___x_3512_;
v_isShared_3515_ = v_isSharedCheck_3558_;
goto v_resetjp_3513_;
}
else
{
lean_dec(v___x_3512_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3558_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v_options_3516_; lean_object* v___x_3517_; uint8_t v___x_3518_; 
v_options_3516_ = lean_ctor_get(v___y_3509_, 2);
v___x_3517_ = l_Lean_Elab_async;
v___x_3518_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3516_, v___x_3517_);
if (v___x_3518_ == 0)
{
lean_object* v___x_3519_; lean_object* v_r_3520_; 
lean_del_object(v___x_3514_);
lean_dec_ref(v___y_3507_);
lean_dec_ref(v___y_3503_);
v___x_3519_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3504_, v___y_3508_);
lean_dec_ref(v___x_3519_);
v_r_3520_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3463_, v___y_3509_, v___y_3508_);
if (lean_obj_tag(v_r_3520_) == 0)
{
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3530_; 
v_a_3521_ = lean_ctor_get(v_r_3520_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v_r_3520_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3523_ = v_r_3520_;
v_isShared_3524_ = v_isSharedCheck_3530_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v_r_3520_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3530_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3526_; 
lean_inc(v_a_3521_);
if (v_isShared_3524_ == 0)
{
lean_ctor_set_tag(v___x_3523_, 1);
v___x_3526_ = v___x_3523_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3521_);
v___x_3526_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
lean_object* v___x_3527_; 
v___x_3527_ = lean_apply_2(v___y_3505_, v___x_3526_, lean_box(0));
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_dec_ref_known(v___x_3527_, 1);
v___y_3487_ = v___y_3501_;
v___y_3488_ = v___y_3508_;
v_a_3489_ = v_a_3521_;
goto v___jp_3486_;
}
else
{
lean_object* v_a_3528_; 
lean_dec(v_a_3521_);
v_a_3528_ = lean_ctor_get(v___x_3527_, 0);
lean_inc(v_a_3528_);
lean_dec_ref_known(v___x_3527_, 1);
v___y_3474_ = v___y_3501_;
v___y_3475_ = v___y_3508_;
v_a_3476_ = v_a_3528_;
goto v___jp_3473_;
}
}
}
}
else
{
lean_object* v_a_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
v_a_3531_ = lean_ctor_get(v_r_3520_, 0);
lean_inc(v_a_3531_);
lean_dec_ref_known(v_r_3520_, 1);
v___x_3532_ = lean_box(0);
v___x_3533_ = lean_apply_2(v___y_3505_, v___x_3532_, lean_box(0));
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_dec_ref_known(v___x_3533_, 1);
v___y_3474_ = v___y_3501_;
v___y_3475_ = v___y_3508_;
v_a_3476_ = v_a_3531_;
goto v___jp_3473_;
}
else
{
lean_object* v_a_3534_; 
lean_dec(v_a_3531_);
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
lean_inc(v_a_3534_);
lean_dec_ref_known(v___x_3533_, 1);
v___y_3474_ = v___y_3501_;
v___y_3475_ = v___y_3508_;
v_a_3476_ = v_a_3534_;
goto v___jp_3473_;
}
}
}
else
{
lean_object* v___x_3535_; lean_object* v___x_3537_; 
lean_dec_ref(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec_ref(v___y_3501_);
lean_dec(v_decl_3463_);
v___x_3535_ = l_IO_CancelToken_new();
if (v_isShared_3515_ == 0)
{
lean_ctor_set_tag(v___x_3514_, 1);
lean_ctor_set(v___x_3514_, 0, v___x_3535_);
v___x_3537_ = v___x_3514_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3535_);
v___x_3537_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3538_ = lean_unsigned_to_nat(0u);
v___x_3539_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_3540_ = l_Lean_Name_toString(v___x_3539_, v___x_3464_);
lean_inc_ref(v___x_3537_);
v___x_3541_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3503_, v___x_3537_, v___x_3540_, v___y_3509_, v___y_3508_);
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_object* v_a_3542_; lean_object* v_checked_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_a_3542_);
lean_dec_ref_known(v___x_3541_, 1);
v_checked_3543_ = lean_ctor_get(v___y_3507_, 2);
lean_inc_ref(v_checked_3543_);
lean_dec_ref(v___y_3507_);
v___x_3544_ = lean_io_map_task(v_a_3542_, v_checked_3543_, v___x_3538_, v___y_3502_);
v___x_3545_ = lean_box(0);
v___x_3546_ = lean_box(2);
v___x_3547_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3545_);
lean_ctor_set(v___x_3547_, 1, v___x_3546_);
lean_ctor_set(v___x_3547_, 2, v___x_3537_);
lean_ctor_set(v___x_3547_, 3, v___x_3544_);
v___x_3548_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3547_, v___y_3508_);
return v___x_3548_;
}
else
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3556_; 
lean_dec_ref(v___x_3537_);
lean_dec_ref(v___y_3507_);
v_a_3549_ = lean_ctor_get(v___x_3541_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3551_ = v___x_3541_;
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3541_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3554_; 
if (v_isShared_3552_ == 0)
{
v___x_3554_ = v___x_3551_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_a_3549_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3572_; 
lean_dec_ref(v___y_3507_);
lean_dec_ref(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec_ref(v___y_3501_);
lean_dec(v_decl_3463_);
v_a_3560_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3562_ = v___x_3511_;
v_isShared_3563_ = v_isSharedCheck_3572_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_a_3560_);
lean_dec(v___x_3511_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3572_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v_ref_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3570_; 
v_ref_3564_ = lean_ctor_get(v___y_3509_, 5);
v___x_3565_ = lean_io_error_to_string(v_a_3560_);
v___x_3566_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3565_);
v___x_3567_ = l_Lean_MessageData_ofFormat(v___x_3566_);
lean_inc(v_ref_3564_);
v___x_3568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3568_, 0, v_ref_3564_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
if (v_isShared_3563_ == 0)
{
lean_ctor_set(v___x_3562_, 0, v___x_3568_);
v___x_3570_ = v___x_3562_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v___x_3568_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
return v___x_3570_;
}
}
}
}
v_resetjp_3575_:
{
lean_object* v_fst_3578_; lean_object* v_snd_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3702_; 
v_fst_3578_ = lean_ctor_get(v_snd_3573_, 0);
v_snd_3579_ = lean_ctor_get(v_snd_3573_, 1);
v_isSharedCheck_3702_ = !lean_is_exclusive(v_snd_3573_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3581_ = v_snd_3573_;
v_isShared_3582_ = v_isSharedCheck_3702_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_snd_3579_);
lean_inc(v_fst_3578_);
lean_dec(v_snd_3573_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3702_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v_exportedInfo_x3f_3616_; lean_object* v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3636_; lean_object* v___y_3637_; uint8_t v___y_3638_; lean_object* v___y_3668_; lean_object* v___y_3669_; lean_object* v___x_3692_; lean_object* v_env_3693_; uint8_t v___x_3694_; 
v___x_3692_ = lean_st_ref_get(v___y_3471_);
v_env_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc_ref(v_env_3693_);
lean_dec(v___x_3692_);
v___x_3694_ = l_Lean_Environment_containsOnBranch(v_env_3693_, v_fst_3574_);
lean_dec_ref(v_env_3693_);
if (v___x_3694_ == 0)
{
lean_del_object(v___x_3576_);
v___y_3668_ = v___y_3470_;
v___y_3669_ = v___y_3471_;
goto v___jp_3667_;
}
else
{
lean_object* v___x_3695_; lean_object* v_env_3696_; lean_object* v___x_3697_; lean_object* v___x_3699_; 
lean_del_object(v___x_3581_);
lean_dec(v_snd_3579_);
lean_dec(v_fst_3578_);
lean_dec(v_exportedInfo_x3f_3469_);
lean_dec(v___x_3467_);
lean_dec_ref(v___x_3466_);
lean_dec(v_cls_3465_);
lean_dec(v_decl_3463_);
v___x_3695_ = lean_st_ref_get(v___y_3471_);
v_env_3696_ = lean_ctor_get(v___x_3695_, 0);
lean_inc_ref(v_env_3696_);
lean_dec(v___x_3695_);
v___x_3697_ = lean_elab_environment_to_kernel_env(v_env_3696_);
if (v_isShared_3577_ == 0)
{
lean_ctor_set_tag(v___x_3576_, 1);
lean_ctor_set(v___x_3576_, 1, v_fst_3574_);
lean_ctor_set(v___x_3576_, 0, v___x_3697_);
v___x_3699_ = v___x_3576_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v___x_3697_);
lean_ctor_set(v_reuseFailAlloc_3701_, 1, v_fst_3574_);
v___x_3699_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
lean_object* v___x_3700_; 
v___x_3700_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3699_, v___y_3470_, v___y_3471_);
return v___x_3700_;
}
}
v___jp_3583_:
{
uint8_t v___x_3591_; uint8_t v___x_3592_; lean_object* v___x_3593_; 
v___x_3591_ = 0;
v___x_3592_ = lean_unbox(v_snd_3579_);
lean_dec(v_snd_3579_);
lean_inc_ref(v___y_3585_);
v___x_3593_ = l_Lean_Environment_addConstAsync(v___y_3585_, v_fst_3574_, v___x_3592_, v___y_3590_, v___x_3591_, v___x_3464_);
if (lean_obj_tag(v___x_3593_) == 0)
{
lean_object* v_a_3594_; lean_object* v_mainEnv_3595_; lean_object* v_asyncEnv_3596_; lean_object* v___f_3597_; lean_object* v___f_3598_; lean_object* v___x_3599_; 
lean_del_object(v___x_3581_);
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc_n(v_a_3594_, 3);
lean_dec_ref_known(v___x_3593_, 1);
v_mainEnv_3595_ = lean_ctor_get(v_a_3594_, 0);
lean_inc_ref(v_mainEnv_3595_);
v_asyncEnv_3596_ = lean_ctor_get(v_a_3594_, 1);
lean_inc_ref_n(v_asyncEnv_3596_, 2);
lean_inc_ref(v___y_3586_);
lean_inc(v___y_3584_);
v___f_3597_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3597_, 0, v___y_3584_);
lean_closure_set(v___f_3597_, 1, v_a_3594_);
lean_closure_set(v___f_3597_, 2, v___y_3586_);
lean_inc(v_decl_3463_);
v___f_3598_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3598_, 0, v_asyncEnv_3596_);
lean_closure_set(v___f_3598_, 1, v_a_3594_);
lean_closure_set(v___f_3598_, 2, v_decl_3463_);
v___x_3599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3599_, 0, v_fst_3578_);
if (lean_obj_tag(v___y_3587_) == 0)
{
lean_inc_ref(v___x_3599_);
v___y_3500_ = v_a_3594_;
v___y_3501_ = v_mainEnv_3595_;
v___y_3502_ = v___x_3591_;
v___y_3503_ = v___f_3598_;
v___y_3504_ = v_asyncEnv_3596_;
v___y_3505_ = v___f_3597_;
v___y_3506_ = v___x_3599_;
v___y_3507_ = v___y_3585_;
v___y_3508_ = v___y_3588_;
v___y_3509_ = v___y_3589_;
v___y_3510_ = v___x_3599_;
goto v___jp_3499_;
}
else
{
v___y_3500_ = v_a_3594_;
v___y_3501_ = v_mainEnv_3595_;
v___y_3502_ = v___x_3591_;
v___y_3503_ = v___f_3598_;
v___y_3504_ = v_asyncEnv_3596_;
v___y_3505_ = v___f_3597_;
v___y_3506_ = v___x_3599_;
v___y_3507_ = v___y_3585_;
v___y_3508_ = v___y_3588_;
v___y_3509_ = v___y_3589_;
v___y_3510_ = v___y_3587_;
goto v___jp_3499_;
}
}
else
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3614_; 
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3585_);
lean_dec(v_fst_3578_);
lean_dec(v_decl_3463_);
v_a_3600_ = lean_ctor_get(v___x_3593_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3593_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3602_ = v___x_3593_;
v_isShared_3603_ = v_isSharedCheck_3614_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3593_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3614_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v_ref_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3609_; 
v_ref_3604_ = lean_ctor_get(v___y_3589_, 5);
v___x_3605_ = lean_io_error_to_string(v_a_3600_);
v___x_3606_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3605_);
v___x_3607_ = l_Lean_MessageData_ofFormat(v___x_3606_);
lean_inc(v_ref_3604_);
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 1, v___x_3607_);
lean_ctor_set(v___x_3581_, 0, v_ref_3604_);
v___x_3609_ = v___x_3581_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_ref_3604_);
lean_ctor_set(v_reuseFailAlloc_3613_, 1, v___x_3607_);
v___x_3609_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
lean_object* v___x_3611_; 
if (v_isShared_3603_ == 0)
{
lean_ctor_set(v___x_3602_, 0, v___x_3609_);
v___x_3611_ = v___x_3602_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v___x_3609_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
}
}
v___jp_3615_:
{
lean_object* v___x_3619_; 
v___x_3619_ = lean_st_ref_get(v___y_3618_);
if (lean_obj_tag(v_exportedInfo_x3f_3616_) == 0)
{
lean_object* v_env_3620_; lean_object* v___x_3621_; 
v_env_3620_ = lean_ctor_get(v___x_3619_, 0);
lean_inc_ref(v_env_3620_);
lean_dec(v___x_3619_);
v___x_3621_ = lean_box(0);
v___y_3584_ = v___y_3618_;
v___y_3585_ = v_env_3620_;
v___y_3586_ = v___y_3617_;
v___y_3587_ = v_exportedInfo_x3f_3616_;
v___y_3588_ = v___y_3618_;
v___y_3589_ = v___y_3617_;
v___y_3590_ = v___x_3621_;
goto v___jp_3583_;
}
else
{
lean_object* v_env_3622_; lean_object* v_val_3623_; uint8_t v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
v_env_3622_ = lean_ctor_get(v___x_3619_, 0);
lean_inc_ref(v_env_3622_);
lean_dec(v___x_3619_);
v_val_3623_ = lean_ctor_get(v_exportedInfo_x3f_3616_, 0);
v___x_3624_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3623_);
v___x_3625_ = lean_box(v___x_3624_);
v___x_3626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3625_);
v___y_3584_ = v___y_3618_;
v___y_3585_ = v_env_3622_;
v___y_3586_ = v___y_3617_;
v___y_3587_ = v_exportedInfo_x3f_3616_;
v___y_3588_ = v___y_3618_;
v___y_3589_ = v___y_3617_;
v___y_3590_ = v___x_3626_;
goto v___jp_3583_;
}
}
v___jp_3627_:
{
lean_object* v___x_3630_; 
lean_inc(v_fst_3578_);
v___x_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3630_, 0, v_fst_3578_);
v_exportedInfo_x3f_3616_ = v___x_3630_;
v___y_3617_ = v___y_3628_;
v___y_3618_ = v___y_3629_;
goto v___jp_3615_;
}
v___jp_3631_:
{
lean_object* v___x_3634_; 
lean_inc(v_fst_3578_);
v___x_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3634_, 0, v_fst_3578_);
v_exportedInfo_x3f_3616_ = v___x_3634_;
v___y_3617_ = v___y_3632_;
v___y_3618_ = v___y_3633_;
goto v___jp_3615_;
}
v___jp_3635_:
{
if (v___y_3638_ == 0)
{
lean_object* v_options_3639_; uint8_t v_hasTrace_3640_; 
lean_dec(v_exportedInfo_x3f_3469_);
lean_dec_ref(v___x_3466_);
v_options_3639_ = lean_ctor_get(v___y_3637_, 2);
v_hasTrace_3640_ = lean_ctor_get_uint8(v_options_3639_, sizeof(void*)*1);
if (v_hasTrace_3640_ == 0)
{
lean_dec(v_cls_3465_);
v___y_3628_ = v___y_3637_;
v___y_3629_ = v___y_3636_;
goto v___jp_3627_;
}
else
{
lean_object* v_inheritedTraceOptions_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; uint8_t v___x_3644_; 
v_inheritedTraceOptions_3641_ = lean_ctor_get(v___y_3637_, 13);
v___x_3642_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3465_);
v___x_3643_ = l_Lean_Name_append(v___x_3642_, v_cls_3465_);
v___x_3644_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3641_, v_options_3639_, v___x_3643_);
lean_dec(v___x_3643_);
if (v___x_3644_ == 0)
{
lean_dec(v_cls_3465_);
v___y_3628_ = v___y_3637_;
v___y_3629_ = v___y_3636_;
goto v___jp_3627_;
}
else
{
lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3645_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_3646_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3465_, v___x_3645_, v___y_3637_, v___y_3636_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_dec_ref_known(v___x_3646_, 1);
v___y_3628_ = v___y_3637_;
v___y_3629_ = v___y_3636_;
goto v___jp_3627_;
}
else
{
lean_del_object(v___x_3581_);
lean_dec(v_snd_3579_);
lean_dec(v_fst_3578_);
lean_dec(v_fst_3574_);
lean_dec(v_decl_3463_);
return v___x_3646_;
}
}
}
}
else
{
lean_object* v___x_3647_; lean_object* v_env_3648_; lean_object* v_nextMacroScope_3649_; lean_object* v_ngen_3650_; lean_object* v_auxDeclNGen_3651_; lean_object* v_traceState_3652_; lean_object* v_messages_3653_; lean_object* v_infoState_3654_; lean_object* v_snapshotTasks_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3665_; 
lean_dec(v_cls_3465_);
v___x_3647_ = lean_st_ref_take(v___y_3636_);
v_env_3648_ = lean_ctor_get(v___x_3647_, 0);
v_nextMacroScope_3649_ = lean_ctor_get(v___x_3647_, 1);
v_ngen_3650_ = lean_ctor_get(v___x_3647_, 2);
v_auxDeclNGen_3651_ = lean_ctor_get(v___x_3647_, 3);
v_traceState_3652_ = lean_ctor_get(v___x_3647_, 4);
v_messages_3653_ = lean_ctor_get(v___x_3647_, 6);
v_infoState_3654_ = lean_ctor_get(v___x_3647_, 7);
v_snapshotTasks_3655_ = lean_ctor_get(v___x_3647_, 8);
v_isSharedCheck_3665_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3665_ == 0)
{
lean_object* v_unused_3666_; 
v_unused_3666_ = lean_ctor_get(v___x_3647_, 5);
lean_dec(v_unused_3666_);
v___x_3657_ = v___x_3647_;
v_isShared_3658_ = v_isSharedCheck_3665_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_snapshotTasks_3655_);
lean_inc(v_infoState_3654_);
lean_inc(v_messages_3653_);
lean_inc(v_traceState_3652_);
lean_inc(v_auxDeclNGen_3651_);
lean_inc(v_ngen_3650_);
lean_inc(v_nextMacroScope_3649_);
lean_inc(v_env_3648_);
lean_dec(v___x_3647_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3665_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3662_; 
v___x_3659_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3579_);
lean_inc(v_fst_3574_);
v___x_3660_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3659_, v_env_3648_, v_fst_3574_, v_snd_3579_);
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 5, v___x_3466_);
lean_ctor_set(v___x_3657_, 0, v___x_3660_);
v___x_3662_ = v___x_3657_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v___x_3660_);
lean_ctor_set(v_reuseFailAlloc_3664_, 1, v_nextMacroScope_3649_);
lean_ctor_set(v_reuseFailAlloc_3664_, 2, v_ngen_3650_);
lean_ctor_set(v_reuseFailAlloc_3664_, 3, v_auxDeclNGen_3651_);
lean_ctor_set(v_reuseFailAlloc_3664_, 4, v_traceState_3652_);
lean_ctor_set(v_reuseFailAlloc_3664_, 5, v___x_3466_);
lean_ctor_set(v_reuseFailAlloc_3664_, 6, v_messages_3653_);
lean_ctor_set(v_reuseFailAlloc_3664_, 7, v_infoState_3654_);
lean_ctor_set(v_reuseFailAlloc_3664_, 8, v_snapshotTasks_3655_);
v___x_3662_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
lean_object* v___x_3663_; 
v___x_3663_ = lean_st_ref_put(v___y_3636_, v___x_3662_);
v_exportedInfo_x3f_3616_ = v_exportedInfo_x3f_3469_;
v___y_3617_ = v___y_3637_;
v___y_3618_ = v___y_3636_;
goto v___jp_3615_;
}
}
}
}
v___jp_3667_:
{
lean_object* v___x_3670_; uint8_t v___x_3671_; 
lean_inc(v_decl_3463_);
v___x_3670_ = l_Lean_Declaration_getTopLevelNames(v_decl_3463_);
v___x_3671_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3670_);
lean_dec(v___x_3670_);
if (v___x_3671_ == 0)
{
lean_dec(v___x_3467_);
if (lean_obj_tag(v_exportedInfo_x3f_3469_) == 0)
{
v___y_3636_ = v___y_3669_;
v___y_3637_ = v___y_3668_;
v___y_3638_ = v___x_3671_;
goto v___jp_3635_;
}
else
{
v___y_3636_ = v___y_3669_;
v___y_3637_ = v___y_3668_;
v___y_3638_ = v___x_3464_;
goto v___jp_3635_;
}
}
else
{
lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v_a_3674_; uint8_t v___x_3675_; 
lean_dec(v_exportedInfo_x3f_3469_);
lean_dec_ref(v___x_3466_);
v___x_3672_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3673_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3672_, v___y_3668_);
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
lean_inc(v_a_3674_);
lean_dec_ref(v___x_3673_);
v___x_3675_ = lean_unbox(v_a_3674_);
lean_dec(v_a_3674_);
if (v___x_3675_ == 0)
{
lean_object* v_options_3676_; uint8_t v_hasTrace_3677_; 
v_options_3676_ = lean_ctor_get(v___y_3668_, 2);
v_hasTrace_3677_ = lean_ctor_get_uint8(v_options_3676_, sizeof(void*)*1);
if (v_hasTrace_3677_ == 0)
{
lean_dec(v_cls_3465_);
v_exportedInfo_x3f_3616_ = v___x_3467_;
v___y_3617_ = v___y_3668_;
v___y_3618_ = v___y_3669_;
goto v___jp_3615_;
}
else
{
lean_object* v_inheritedTraceOptions_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; uint8_t v___x_3681_; 
v_inheritedTraceOptions_3678_ = lean_ctor_get(v___y_3668_, 13);
v___x_3679_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3465_);
v___x_3680_ = l_Lean_Name_append(v___x_3679_, v_cls_3465_);
v___x_3681_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3678_, v_options_3676_, v___x_3680_);
lean_dec(v___x_3680_);
if (v___x_3681_ == 0)
{
lean_dec(v_cls_3465_);
v_exportedInfo_x3f_3616_ = v___x_3467_;
v___y_3617_ = v___y_3668_;
v___y_3618_ = v___y_3669_;
goto v___jp_3615_;
}
else
{
lean_object* v___x_3682_; lean_object* v___x_3683_; 
v___x_3682_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_3683_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3465_, v___x_3682_, v___y_3668_, v___y_3669_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_dec_ref_known(v___x_3683_, 1);
v_exportedInfo_x3f_3616_ = v___x_3467_;
v___y_3617_ = v___y_3668_;
v___y_3618_ = v___y_3669_;
goto v___jp_3615_;
}
else
{
lean_del_object(v___x_3581_);
lean_dec(v_snd_3579_);
lean_dec(v_fst_3578_);
lean_dec(v_fst_3574_);
lean_dec(v___x_3467_);
lean_dec(v_decl_3463_);
return v___x_3683_;
}
}
}
}
else
{
lean_object* v_options_3684_; uint8_t v_hasTrace_3685_; 
lean_dec(v___x_3467_);
v_options_3684_ = lean_ctor_get(v___y_3668_, 2);
v_hasTrace_3685_ = lean_ctor_get_uint8(v_options_3684_, sizeof(void*)*1);
if (v_hasTrace_3685_ == 0)
{
lean_dec(v_cls_3465_);
v___y_3632_ = v___y_3668_;
v___y_3633_ = v___y_3669_;
goto v___jp_3631_;
}
else
{
lean_object* v_inheritedTraceOptions_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; uint8_t v___x_3689_; 
v_inheritedTraceOptions_3686_ = lean_ctor_get(v___y_3668_, 13);
v___x_3687_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3465_);
v___x_3688_ = l_Lean_Name_append(v___x_3687_, v_cls_3465_);
v___x_3689_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3686_, v_options_3684_, v___x_3688_);
lean_dec(v___x_3688_);
if (v___x_3689_ == 0)
{
lean_dec(v_cls_3465_);
v___y_3632_ = v___y_3668_;
v___y_3633_ = v___y_3669_;
goto v___jp_3631_;
}
else
{
lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___x_3690_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_3691_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3465_, v___x_3690_, v___y_3668_, v___y_3669_);
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_dec_ref_known(v___x_3691_, 1);
v___y_3632_ = v___y_3668_;
v___y_3633_ = v___y_3669_;
goto v___jp_3631_;
}
else
{
lean_del_object(v___x_3581_);
lean_dec(v_snd_3579_);
lean_dec(v_fst_3578_);
lean_dec(v_fst_3574_);
lean_dec(v_decl_3463_);
return v___x_3691_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed(lean_object* v_decl_3704_, lean_object* v___x_3705_, lean_object* v_cls_3706_, lean_object* v___x_3707_, lean_object* v___x_3708_, lean_object* v_____x_3709_, lean_object* v_exportedInfo_x3f_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_){
_start:
{
uint8_t v___x_63732__boxed_3714_; lean_object* v_res_3715_; 
v___x_63732__boxed_3714_ = lean_unbox(v___x_3705_);
v_res_3715_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_decl_3704_, v___x_63732__boxed_3714_, v_cls_3706_, v___x_3707_, v___x_3708_, v_____x_3709_, v_exportedInfo_x3f_3710_, v___y_3711_, v___y_3712_);
lean_dec(v___y_3712_);
lean_dec_ref(v___y_3711_);
return v_res_3715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(lean_object* v___f_3716_, uint8_t v_forceExpose_3717_, uint8_t v___x_3718_, lean_object* v___x_3719_, lean_object* v_cls_3720_, lean_object* v_defn_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_){
_start:
{
lean_object* v_exportedInfo_x3f_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; uint8_t v___y_3741_; lean_object* v___x_3745_; lean_object* v___x_3746_; 
v___x_3745_ = lean_st_ref_get(v___y_3723_);
v___x_3746_ = lean_st_ref_get(v___y_3723_);
if (v_forceExpose_3717_ == 0)
{
if (v___x_3718_ == 0)
{
lean_dec(v___x_3746_);
lean_dec(v___x_3745_);
lean_dec(v_cls_3720_);
v_exportedInfo_x3f_3726_ = v___x_3719_;
v___y_3727_ = v___y_3722_;
v___y_3728_ = v___y_3723_;
goto v___jp_3725_;
}
else
{
lean_object* v_env_3747_; lean_object* v_env_3748_; lean_object* v___x_3749_; uint8_t v_isModule_3750_; 
v_env_3747_ = lean_ctor_get(v___x_3745_, 0);
lean_inc_ref(v_env_3747_);
lean_dec(v___x_3745_);
v_env_3748_ = lean_ctor_get(v___x_3746_, 0);
lean_inc_ref(v_env_3748_);
lean_dec(v___x_3746_);
v___x_3749_ = l_Lean_Environment_header(v_env_3747_);
lean_dec_ref(v_env_3747_);
v_isModule_3750_ = lean_ctor_get_uint8(v___x_3749_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3749_);
if (v_isModule_3750_ == 0)
{
lean_dec_ref(v_env_3748_);
lean_dec(v_cls_3720_);
v_exportedInfo_x3f_3726_ = v___x_3719_;
v___y_3727_ = v___y_3722_;
v___y_3728_ = v___y_3723_;
goto v___jp_3725_;
}
else
{
uint8_t v_isExporting_3751_; lean_object* v___y_3753_; lean_object* v___y_3754_; 
v_isExporting_3751_ = lean_ctor_get_uint8(v_env_3748_, sizeof(void*)*8);
lean_dec_ref(v_env_3748_);
if (v_isExporting_3751_ == 0)
{
lean_object* v_options_3759_; uint8_t v_hasTrace_3760_; 
lean_dec(v___x_3719_);
v_options_3759_ = lean_ctor_get(v___y_3722_, 2);
v_hasTrace_3760_ = lean_ctor_get_uint8(v_options_3759_, sizeof(void*)*1);
if (v_hasTrace_3760_ == 0)
{
lean_dec(v_cls_3720_);
v___y_3753_ = v___y_3722_;
v___y_3754_ = v___y_3723_;
goto v___jp_3752_;
}
else
{
lean_object* v_inheritedTraceOptions_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; uint8_t v___x_3764_; 
v_inheritedTraceOptions_3761_ = lean_ctor_get(v___y_3722_, 13);
v___x_3762_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3720_);
v___x_3763_ = l_Lean_Name_append(v___x_3762_, v_cls_3720_);
v___x_3764_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3761_, v_options_3759_, v___x_3763_);
lean_dec(v___x_3763_);
if (v___x_3764_ == 0)
{
lean_dec(v_cls_3720_);
v___y_3753_ = v___y_3722_;
v___y_3754_ = v___y_3723_;
goto v___jp_3752_;
}
else
{
lean_object* v_toConstantVal_3765_; lean_object* v_name_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; 
v_toConstantVal_3765_ = lean_ctor_get(v_defn_3721_, 0);
v_name_3766_ = lean_ctor_get(v_toConstantVal_3765_, 0);
v___x_3767_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_3766_);
v___x_3768_ = l_Lean_MessageData_ofName(v_name_3766_);
v___x_3769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3767_);
lean_ctor_set(v___x_3769_, 1, v___x_3768_);
v___x_3770_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_3771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3769_);
lean_ctor_set(v___x_3771_, 1, v___x_3770_);
v___x_3772_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3720_, v___x_3771_, v___y_3722_, v___y_3723_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_dec_ref_known(v___x_3772_, 1);
v___y_3753_ = v___y_3722_;
v___y_3754_ = v___y_3723_;
goto v___jp_3752_;
}
else
{
lean_dec_ref(v_defn_3721_);
lean_dec_ref(v___f_3716_);
return v___x_3772_;
}
}
}
}
else
{
lean_dec(v_cls_3720_);
v_exportedInfo_x3f_3726_ = v___x_3719_;
v___y_3727_ = v___y_3722_;
v___y_3728_ = v___y_3723_;
goto v___jp_3725_;
}
v___jp_3752_:
{
lean_object* v_toConstantVal_3755_; uint8_t v_safety_3756_; uint8_t v___x_3757_; uint8_t v___x_3758_; 
v_toConstantVal_3755_ = lean_ctor_get(v_defn_3721_, 0);
v_safety_3756_ = lean_ctor_get_uint8(v_defn_3721_, sizeof(void*)*4);
v___x_3757_ = 1;
v___x_3758_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3756_, v___x_3757_);
if (v___x_3758_ == 0)
{
lean_inc_ref(v_toConstantVal_3755_);
v___y_3738_ = v___y_3754_;
v___y_3739_ = v_toConstantVal_3755_;
v___y_3740_ = v___y_3753_;
v___y_3741_ = v___x_3718_;
goto v___jp_3737_;
}
else
{
lean_inc_ref(v_toConstantVal_3755_);
v___y_3738_ = v___y_3754_;
v___y_3739_ = v_toConstantVal_3755_;
v___y_3740_ = v___y_3753_;
v___y_3741_ = v_isExporting_3751_;
goto v___jp_3737_;
}
}
}
}
}
else
{
lean_dec(v___x_3746_);
lean_dec(v___x_3745_);
lean_dec(v_cls_3720_);
v_exportedInfo_x3f_3726_ = v___x_3719_;
v___y_3727_ = v___y_3722_;
v___y_3728_ = v___y_3723_;
goto v___jp_3725_;
}
v___jp_3725_:
{
lean_object* v_toConstantVal_3729_; lean_object* v_name_3730_; lean_object* v___x_3731_; uint8_t v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
v_toConstantVal_3729_ = lean_ctor_get(v_defn_3721_, 0);
v_name_3730_ = lean_ctor_get(v_toConstantVal_3729_, 0);
lean_inc(v_name_3730_);
v___x_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3731_, 0, v_defn_3721_);
v___x_3732_ = 0;
v___x_3733_ = lean_box(v___x_3732_);
v___x_3734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3731_);
lean_ctor_set(v___x_3734_, 1, v___x_3733_);
v___x_3735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3735_, 0, v_name_3730_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
lean_inc(v___y_3728_);
lean_inc_ref(v___y_3727_);
v___x_3736_ = lean_apply_5(v___f_3716_, v___x_3735_, v_exportedInfo_x3f_3726_, v___y_3727_, v___y_3728_, lean_box(0));
return v___x_3736_;
}
v___jp_3737_:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
v___x_3742_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3742_, 0, v___y_3739_);
lean_ctor_set_uint8(v___x_3742_, sizeof(void*)*1, v___y_3741_);
v___x_3743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3742_);
v___x_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3743_);
v_exportedInfo_x3f_3726_ = v___x_3744_;
v___y_3727_ = v___y_3740_;
v___y_3728_ = v___y_3738_;
goto v___jp_3725_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10___boxed(lean_object* v___f_3773_, lean_object* v_forceExpose_3774_, lean_object* v___x_3775_, lean_object* v___x_3776_, lean_object* v_cls_3777_, lean_object* v_defn_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_){
_start:
{
uint8_t v_forceExpose_boxed_3782_; uint8_t v___x_64207__boxed_3783_; lean_object* v_res_3784_; 
v_forceExpose_boxed_3782_ = lean_unbox(v_forceExpose_3774_);
v___x_64207__boxed_3783_ = lean_unbox(v___x_3775_);
v_res_3784_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v___f_3773_, v_forceExpose_boxed_3782_, v___x_64207__boxed_3783_, v___x_3776_, v_cls_3777_, v_defn_3778_, v___y_3779_, v___y_3780_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
return v_res_3784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(lean_object* v_val_3785_, uint8_t v_forceExpose_3786_, lean_object* v___f_3787_, lean_object* v_____r_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_){
_start:
{
lean_object* v_toConstantVal_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v_toConstantVal_3792_ = lean_ctor_get(v_val_3785_, 0);
lean_inc_ref(v_toConstantVal_3792_);
v___x_3793_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3793_, 0, v_toConstantVal_3792_);
lean_ctor_set_uint8(v___x_3793_, sizeof(void*)*1, v_forceExpose_3786_);
v___x_3794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3793_);
v___x_3795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3794_);
v___x_3796_ = lean_box(0);
lean_inc(v___y_3790_);
lean_inc_ref(v___y_3789_);
v___x_3797_ = lean_apply_5(v___f_3787_, v___x_3796_, v___x_3795_, v___y_3789_, v___y_3790_, lean_box(0));
return v___x_3797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12___boxed(lean_object* v_val_3798_, lean_object* v_forceExpose_3799_, lean_object* v___f_3800_, lean_object* v_____r_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
uint8_t v_forceExpose_boxed_3805_; lean_object* v_res_3806_; 
v_forceExpose_boxed_3805_ = lean_unbox(v_forceExpose_3799_);
v_res_3806_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(v_val_3798_, v_forceExpose_boxed_3805_, v___f_3800_, v_____r_3801_, v___y_3802_, v___y_3803_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
lean_dec_ref(v_val_3798_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(lean_object* v_x_3807_, lean_object* v_x_3808_){
_start:
{
if (lean_obj_tag(v_x_3808_) == 0)
{
return v_x_3807_;
}
else
{
lean_object* v_head_3809_; lean_object* v_tail_3810_; lean_object* v___x_3811_; 
v_head_3809_ = lean_ctor_get(v_x_3808_, 0);
lean_inc(v_head_3809_);
v_tail_3810_ = lean_ctor_get(v_x_3808_, 1);
lean_inc(v_tail_3810_);
lean_dec_ref_known(v_x_3808_, 2);
v___x_3811_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(v_x_3807_, v_head_3809_);
v_x_3807_ = v___x_3811_;
v_x_3808_ = v_tail_3810_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0(void){
_start:
{
lean_object* v_cls_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; 
v_cls_3813_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_3814_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
v___x_3815_ = l_Lean_Name_append(v___x_3814_, v_cls_3813_);
return v___x_3815_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2(void){
_start:
{
lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3817_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1));
v___x_3818_ = l_Lean_stringToMessageData(v___x_3817_);
return v___x_3818_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4(void){
_start:
{
lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3820_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3));
v___x_3821_ = l_Lean_stringToMessageData(v___x_3820_);
return v___x_3821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore(lean_object* v_decl_3822_, uint8_t v_forceExpose_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_){
_start:
{
lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v_a_3830_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v_a_3843_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v_a_3856_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v_a_3869_; lean_object* v_options_3879_; lean_object* v_inheritedTraceOptions_3880_; uint8_t v_hasTrace_3881_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; uint8_t v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; uint8_t v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; uint8_t v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v_exportedInfo_x3f_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; uint8_t v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; uint8_t v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v_cls_4017_; 
v_options_3879_ = lean_ctor_get(v_a_3824_, 2);
v_inheritedTraceOptions_3880_ = lean_ctor_get(v_a_3824_, 13);
v_hasTrace_3881_ = lean_ctor_get_uint8(v_options_3879_, sizeof(void*)*1);
v_cls_4017_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
if (v_hasTrace_3881_ == 0)
{
lean_object* v___x_4018_; lean_object* v_env_4019_; lean_object* v_nextMacroScope_4020_; lean_object* v_ngen_4021_; lean_object* v_auxDeclNGen_4022_; lean_object* v_traceState_4023_; lean_object* v_messages_4024_; lean_object* v_infoState_4025_; lean_object* v_snapshotTasks_4026_; lean_object* v___x_4028_; uint8_t v_isShared_4029_; uint8_t v_isSharedCheck_4217_; 
v___x_4018_ = lean_st_ref_take(v_a_3825_);
v_env_4019_ = lean_ctor_get(v___x_4018_, 0);
v_nextMacroScope_4020_ = lean_ctor_get(v___x_4018_, 1);
v_ngen_4021_ = lean_ctor_get(v___x_4018_, 2);
v_auxDeclNGen_4022_ = lean_ctor_get(v___x_4018_, 3);
v_traceState_4023_ = lean_ctor_get(v___x_4018_, 4);
v_messages_4024_ = lean_ctor_get(v___x_4018_, 6);
v_infoState_4025_ = lean_ctor_get(v___x_4018_, 7);
v_snapshotTasks_4026_ = lean_ctor_get(v___x_4018_, 8);
v_isSharedCheck_4217_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4217_ == 0)
{
lean_object* v_unused_4218_; 
v_unused_4218_ = lean_ctor_get(v___x_4018_, 5);
lean_dec(v_unused_4218_);
v___x_4028_ = v___x_4018_;
v_isShared_4029_ = v_isSharedCheck_4217_;
goto v_resetjp_4027_;
}
else
{
lean_inc(v_snapshotTasks_4026_);
lean_inc(v_infoState_4025_);
lean_inc(v_messages_4024_);
lean_inc(v_traceState_4023_);
lean_inc(v_auxDeclNGen_4022_);
lean_inc(v_ngen_4021_);
lean_inc(v_nextMacroScope_4020_);
lean_inc(v_env_4019_);
lean_dec(v___x_4018_);
v___x_4028_ = lean_box(0);
v_isShared_4029_ = v_isSharedCheck_4217_;
goto v_resetjp_4027_;
}
v_resetjp_4027_:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4034_; 
lean_inc(v_decl_3822_);
v___x_4030_ = l_Lean_Declaration_getNames(v_decl_3822_);
v___x_4031_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4019_, v___x_4030_);
v___x_4032_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4029_ == 0)
{
lean_ctor_set(v___x_4028_, 5, v___x_4032_);
lean_ctor_set(v___x_4028_, 0, v___x_4031_);
v___x_4034_ = v___x_4028_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v___x_4031_);
lean_ctor_set(v_reuseFailAlloc_4216_, 1, v_nextMacroScope_4020_);
lean_ctor_set(v_reuseFailAlloc_4216_, 2, v_ngen_4021_);
lean_ctor_set(v_reuseFailAlloc_4216_, 3, v_auxDeclNGen_4022_);
lean_ctor_set(v_reuseFailAlloc_4216_, 4, v_traceState_4023_);
lean_ctor_set(v_reuseFailAlloc_4216_, 5, v___x_4032_);
lean_ctor_set(v_reuseFailAlloc_4216_, 6, v_messages_4024_);
lean_ctor_set(v_reuseFailAlloc_4216_, 7, v_infoState_4025_);
lean_ctor_set(v_reuseFailAlloc_4216_, 8, v_snapshotTasks_4026_);
v___x_4034_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
lean_object* v___x_4035_; lean_object* v___x_4036_; uint8_t v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v_fst_4093_; lean_object* v_fst_4094_; uint8_t v_snd_4095_; lean_object* v_exportedInfo_x3f_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4108_; lean_object* v_exportedInfo_x3f_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; uint8_t v___y_4121_; uint8_t v___y_4126_; lean_object* v___y_4127_; lean_object* v_toConstantVal_4128_; uint8_t v_safety_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; uint8_t v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v_defn_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; 
v___x_4035_ = lean_st_ref_put(v_a_3825_, v___x_4034_);
v___x_4036_ = lean_box(0);
switch(lean_obj_tag(v_decl_3822_))
{
case 2:
{
lean_object* v_val_4166_; lean_object* v_exportedInfo_x3f_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___x_4175_; 
v_val_4166_ = lean_ctor_get(v_decl_3822_, 0);
v___x_4175_ = lean_st_ref_get(v_a_3825_);
if (v_forceExpose_3823_ == 0)
{
lean_object* v_env_4176_; lean_object* v___x_4177_; uint8_t v_isModule_4178_; 
v_env_4176_ = lean_ctor_get(v___x_4175_, 0);
lean_inc_ref(v_env_4176_);
lean_dec(v___x_4175_);
v___x_4177_ = l_Lean_Environment_header(v_env_4176_);
lean_dec_ref(v_env_4176_);
v_isModule_4178_ = lean_ctor_get_uint8(v___x_4177_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4177_);
if (v_isModule_4178_ == 0)
{
v_exportedInfo_x3f_4168_ = v___x_4036_;
v___y_4169_ = v_a_3824_;
v___y_4170_ = v_a_3825_;
goto v___jp_4167_;
}
else
{
lean_object* v_toConstantVal_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; 
v_toConstantVal_4179_ = lean_ctor_get(v_val_4166_, 0);
lean_inc_ref(v_toConstantVal_4179_);
v___x_4180_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4180_, 0, v_toConstantVal_4179_);
lean_ctor_set_uint8(v___x_4180_, sizeof(void*)*1, v_hasTrace_3881_);
v___x_4181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4180_);
v___x_4182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4182_, 0, v___x_4181_);
v_exportedInfo_x3f_4168_ = v___x_4182_;
v___y_4169_ = v_a_3824_;
v___y_4170_ = v_a_3825_;
goto v___jp_4167_;
}
}
else
{
lean_dec(v___x_4175_);
v_exportedInfo_x3f_4168_ = v___x_4036_;
v___y_4169_ = v_a_3824_;
v___y_4170_ = v_a_3825_;
goto v___jp_4167_;
}
v___jp_4167_:
{
lean_object* v_toConstantVal_4171_; lean_object* v_name_4172_; lean_object* v___x_4173_; uint8_t v___x_4174_; 
v_toConstantVal_4171_ = lean_ctor_get(v_val_4166_, 0);
v_name_4172_ = lean_ctor_get(v_toConstantVal_4171_, 0);
lean_inc_ref(v_val_4166_);
v___x_4173_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4173_, 0, v_val_4166_);
v___x_4174_ = 1;
lean_inc(v_name_4172_);
v_fst_4093_ = v_name_4172_;
v_fst_4094_ = v___x_4173_;
v_snd_4095_ = v___x_4174_;
v_exportedInfo_x3f_4096_ = v_exportedInfo_x3f_4168_;
v___y_4097_ = v___y_4169_;
v___y_4098_ = v___y_4170_;
goto v___jp_4092_;
}
}
case 1:
{
lean_object* v_val_4183_; 
v_val_4183_ = lean_ctor_get(v_decl_3822_, 0);
lean_inc_ref(v_val_4183_);
v_defn_4142_ = v_val_4183_;
v___y_4143_ = v_a_3824_;
v___y_4144_ = v_a_3825_;
goto v___jp_4141_;
}
case 5:
{
lean_object* v_defns_4184_; 
v_defns_4184_ = lean_ctor_get(v_decl_3822_, 0);
if (lean_obj_tag(v_defns_4184_) == 1)
{
lean_object* v_tail_4185_; 
v_tail_4185_ = lean_ctor_get(v_defns_4184_, 1);
if (lean_obj_tag(v_tail_4185_) == 0)
{
lean_object* v_head_4186_; 
v_head_4186_ = lean_ctor_get(v_defns_4184_, 0);
lean_inc(v_head_4186_);
v_defn_4142_ = v_head_4186_;
v___y_4143_ = v_a_3824_;
v___y_4144_ = v_a_3825_;
goto v___jp_4141_;
}
else
{
lean_object* v___x_4187_; 
v___x_4187_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3822_, v_a_3824_, v_a_3825_);
return v___x_4187_;
}
}
else
{
lean_object* v___x_4188_; 
v___x_4188_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3822_, v_a_3824_, v_a_3825_);
return v___x_4188_;
}
}
case 3:
{
lean_object* v_val_4189_; lean_object* v_exportedInfo_x3f_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___x_4198_; lean_object* v___x_4199_; 
v_val_4189_ = lean_ctor_get(v_decl_3822_, 0);
v___x_4198_ = lean_st_ref_get(v_a_3825_);
v___x_4199_ = lean_st_ref_get(v_a_3825_);
if (v_forceExpose_3823_ == 0)
{
lean_object* v_env_4200_; lean_object* v_env_4201_; lean_object* v___x_4202_; uint8_t v_isModule_4203_; 
v_env_4200_ = lean_ctor_get(v___x_4198_, 0);
lean_inc_ref(v_env_4200_);
lean_dec(v___x_4198_);
v_env_4201_ = lean_ctor_get(v___x_4199_, 0);
lean_inc_ref(v_env_4201_);
lean_dec(v___x_4199_);
v___x_4202_ = l_Lean_Environment_header(v_env_4200_);
lean_dec_ref(v_env_4200_);
v_isModule_4203_ = lean_ctor_get_uint8(v___x_4202_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4202_);
if (v_isModule_4203_ == 0)
{
lean_dec_ref(v_env_4201_);
v_exportedInfo_x3f_4191_ = v___x_4036_;
v___y_4192_ = v_a_3824_;
v___y_4193_ = v_a_3825_;
goto v___jp_4190_;
}
else
{
uint8_t v_isExporting_4204_; 
v_isExporting_4204_ = lean_ctor_get_uint8(v_env_4201_, sizeof(void*)*8);
lean_dec_ref(v_env_4201_);
if (v_isExporting_4204_ == 0)
{
lean_object* v_toConstantVal_4205_; uint8_t v_isUnsafe_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; 
v_toConstantVal_4205_ = lean_ctor_get(v_val_4189_, 0);
v_isUnsafe_4206_ = lean_ctor_get_uint8(v_val_4189_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4205_);
v___x_4207_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4207_, 0, v_toConstantVal_4205_);
lean_ctor_set_uint8(v___x_4207_, sizeof(void*)*1, v_isUnsafe_4206_);
v___x_4208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4208_, 0, v___x_4207_);
v___x_4209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4208_);
v_exportedInfo_x3f_4191_ = v___x_4209_;
v___y_4192_ = v_a_3824_;
v___y_4193_ = v_a_3825_;
goto v___jp_4190_;
}
else
{
v_exportedInfo_x3f_4191_ = v___x_4036_;
v___y_4192_ = v_a_3824_;
v___y_4193_ = v_a_3825_;
goto v___jp_4190_;
}
}
}
else
{
lean_dec(v___x_4199_);
lean_dec(v___x_4198_);
v_exportedInfo_x3f_4191_ = v___x_4036_;
v___y_4192_ = v_a_3824_;
v___y_4193_ = v_a_3825_;
goto v___jp_4190_;
}
v___jp_4190_:
{
lean_object* v_toConstantVal_4194_; lean_object* v_name_4195_; lean_object* v___x_4196_; uint8_t v___x_4197_; 
v_toConstantVal_4194_ = lean_ctor_get(v_val_4189_, 0);
v_name_4195_ = lean_ctor_get(v_toConstantVal_4194_, 0);
lean_inc_ref(v_val_4189_);
v___x_4196_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4196_, 0, v_val_4189_);
v___x_4197_ = 3;
lean_inc(v_name_4195_);
v_fst_4093_ = v_name_4195_;
v_fst_4094_ = v___x_4196_;
v_snd_4095_ = v___x_4197_;
v_exportedInfo_x3f_4096_ = v_exportedInfo_x3f_4191_;
v___y_4097_ = v___y_4192_;
v___y_4098_ = v___y_4193_;
goto v___jp_4092_;
}
}
case 0:
{
lean_object* v_val_4210_; lean_object* v_toConstantVal_4211_; lean_object* v_name_4212_; lean_object* v___x_4213_; uint8_t v___x_4214_; 
v_val_4210_ = lean_ctor_get(v_decl_3822_, 0);
v_toConstantVal_4211_ = lean_ctor_get(v_val_4210_, 0);
v_name_4212_ = lean_ctor_get(v_toConstantVal_4211_, 0);
lean_inc_ref(v_val_4210_);
v___x_4213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4213_, 0, v_val_4210_);
v___x_4214_ = 2;
lean_inc(v_name_4212_);
v_fst_4093_ = v_name_4212_;
v_fst_4094_ = v___x_4213_;
v_snd_4095_ = v___x_4214_;
v_exportedInfo_x3f_4096_ = v___x_4036_;
v___y_4097_ = v_a_3824_;
v___y_4098_ = v_a_3825_;
goto v___jp_4092_;
}
default: 
{
lean_object* v___x_4215_; 
v___x_4215_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3822_, v_a_3824_, v_a_3825_);
return v___x_4215_;
}
}
v___jp_4037_:
{
lean_object* v___x_4044_; uint8_t v___x_4045_; 
lean_inc(v_decl_3822_);
v___x_4044_ = l_Lean_Declaration_getTopLevelNames(v_decl_3822_);
v___x_4045_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_4044_);
lean_dec(v___x_4044_);
if (v___x_4045_ == 0)
{
if (lean_obj_tag(v___y_4041_) == 0)
{
lean_object* v_options_4046_; uint8_t v_hasTrace_4047_; 
v_options_4046_ = lean_ctor_get(v___y_4042_, 2);
v_hasTrace_4047_ = lean_ctor_get_uint8(v_options_4046_, sizeof(void*)*1);
if (v_hasTrace_4047_ == 0)
{
v___y_4011_ = v___y_4038_;
v___y_4012_ = v___y_4039_;
v___y_4013_ = v___y_4040_;
v___y_4014_ = v___y_4042_;
v___y_4015_ = v___y_4043_;
goto v___jp_4010_;
}
else
{
lean_object* v_inheritedTraceOptions_4048_; lean_object* v___x_4049_; uint8_t v___x_4050_; 
v_inheritedTraceOptions_4048_ = lean_ctor_get(v___y_4042_, 13);
v___x_4049_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4050_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4048_, v_options_4046_, v___x_4049_);
if (v___x_4050_ == 0)
{
v___y_4011_ = v___y_4038_;
v___y_4012_ = v___y_4039_;
v___y_4013_ = v___y_4040_;
v___y_4014_ = v___y_4042_;
v___y_4015_ = v___y_4043_;
goto v___jp_4010_;
}
else
{
lean_object* v___x_4051_; lean_object* v___x_4052_; 
v___x_4051_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_4052_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4017_, v___x_4051_, v___y_4042_, v___y_4043_);
if (lean_obj_tag(v___x_4052_) == 0)
{
lean_dec_ref_known(v___x_4052_, 1);
v___y_4011_ = v___y_4038_;
v___y_4012_ = v___y_4039_;
v___y_4013_ = v___y_4040_;
v___y_4014_ = v___y_4042_;
v___y_4015_ = v___y_4043_;
goto v___jp_4010_;
}
else
{
lean_dec_ref(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec(v_decl_3822_);
return v___x_4052_;
}
}
}
}
else
{
lean_object* v___x_4053_; lean_object* v_env_4054_; lean_object* v_nextMacroScope_4055_; lean_object* v_ngen_4056_; lean_object* v_auxDeclNGen_4057_; lean_object* v_traceState_4058_; lean_object* v_messages_4059_; lean_object* v_infoState_4060_; lean_object* v_snapshotTasks_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4072_; 
v___x_4053_ = lean_st_ref_take(v___y_4043_);
v_env_4054_ = lean_ctor_get(v___x_4053_, 0);
v_nextMacroScope_4055_ = lean_ctor_get(v___x_4053_, 1);
v_ngen_4056_ = lean_ctor_get(v___x_4053_, 2);
v_auxDeclNGen_4057_ = lean_ctor_get(v___x_4053_, 3);
v_traceState_4058_ = lean_ctor_get(v___x_4053_, 4);
v_messages_4059_ = lean_ctor_get(v___x_4053_, 6);
v_infoState_4060_ = lean_ctor_get(v___x_4053_, 7);
v_snapshotTasks_4061_ = lean_ctor_get(v___x_4053_, 8);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4072_ == 0)
{
lean_object* v_unused_4073_; 
v_unused_4073_ = lean_ctor_get(v___x_4053_, 5);
lean_dec(v_unused_4073_);
v___x_4063_ = v___x_4053_;
v_isShared_4064_ = v_isSharedCheck_4072_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_snapshotTasks_4061_);
lean_inc(v_infoState_4060_);
lean_inc(v_messages_4059_);
lean_inc(v_traceState_4058_);
lean_inc(v_auxDeclNGen_4057_);
lean_inc(v_ngen_4056_);
lean_inc(v_nextMacroScope_4055_);
lean_inc(v_env_4054_);
lean_dec(v___x_4053_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4072_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4069_; 
v___x_4065_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4066_ = lean_box(v___y_4038_);
lean_inc(v___y_4039_);
v___x_4067_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4065_, v_env_4054_, v___y_4039_, v___x_4066_);
if (v_isShared_4064_ == 0)
{
lean_ctor_set(v___x_4063_, 5, v___x_4032_);
lean_ctor_set(v___x_4063_, 0, v___x_4067_);
v___x_4069_ = v___x_4063_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v___x_4067_);
lean_ctor_set(v_reuseFailAlloc_4071_, 1, v_nextMacroScope_4055_);
lean_ctor_set(v_reuseFailAlloc_4071_, 2, v_ngen_4056_);
lean_ctor_set(v_reuseFailAlloc_4071_, 3, v_auxDeclNGen_4057_);
lean_ctor_set(v_reuseFailAlloc_4071_, 4, v_traceState_4058_);
lean_ctor_set(v_reuseFailAlloc_4071_, 5, v___x_4032_);
lean_ctor_set(v_reuseFailAlloc_4071_, 6, v_messages_4059_);
lean_ctor_set(v_reuseFailAlloc_4071_, 7, v_infoState_4060_);
lean_ctor_set(v_reuseFailAlloc_4071_, 8, v_snapshotTasks_4061_);
v___x_4069_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
lean_object* v___x_4070_; 
v___x_4070_ = lean_st_ref_put(v___y_4043_, v___x_4069_);
v___y_3989_ = v___y_4038_;
v___y_3990_ = v___y_4039_;
v___y_3991_ = v___y_4040_;
v_exportedInfo_x3f_3992_ = v___y_4041_;
v___y_3993_ = v___y_4042_;
v___y_3994_ = v___y_4043_;
goto v___jp_3988_;
}
}
}
}
else
{
lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v_a_4076_; uint8_t v___x_4077_; 
lean_dec(v___y_4041_);
v___x_4074_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4075_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4074_, v___y_4042_);
v_a_4076_ = lean_ctor_get(v___x_4075_, 0);
lean_inc(v_a_4076_);
lean_dec_ref(v___x_4075_);
v___x_4077_ = lean_unbox(v_a_4076_);
lean_dec(v_a_4076_);
if (v___x_4077_ == 0)
{
lean_object* v_options_4078_; uint8_t v_hasTrace_4079_; 
v_options_4078_ = lean_ctor_get(v___y_4042_, 2);
v_hasTrace_4079_ = lean_ctor_get_uint8(v_options_4078_, sizeof(void*)*1);
if (v_hasTrace_4079_ == 0)
{
v___y_3989_ = v___y_4038_;
v___y_3990_ = v___y_4039_;
v___y_3991_ = v___y_4040_;
v_exportedInfo_x3f_3992_ = v___x_4036_;
v___y_3993_ = v___y_4042_;
v___y_3994_ = v___y_4043_;
goto v___jp_3988_;
}
else
{
lean_object* v_inheritedTraceOptions_4080_; lean_object* v___x_4081_; uint8_t v___x_4082_; 
v_inheritedTraceOptions_4080_ = lean_ctor_get(v___y_4042_, 13);
v___x_4081_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4082_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4080_, v_options_4078_, v___x_4081_);
if (v___x_4082_ == 0)
{
v___y_3989_ = v___y_4038_;
v___y_3990_ = v___y_4039_;
v___y_3991_ = v___y_4040_;
v_exportedInfo_x3f_3992_ = v___x_4036_;
v___y_3993_ = v___y_4042_;
v___y_3994_ = v___y_4043_;
goto v___jp_3988_;
}
else
{
lean_object* v___x_4083_; lean_object* v___x_4084_; 
v___x_4083_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_4084_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4017_, v___x_4083_, v___y_4042_, v___y_4043_);
if (lean_obj_tag(v___x_4084_) == 0)
{
lean_dec_ref_known(v___x_4084_, 1);
v___y_3989_ = v___y_4038_;
v___y_3990_ = v___y_4039_;
v___y_3991_ = v___y_4040_;
v_exportedInfo_x3f_3992_ = v___x_4036_;
v___y_3993_ = v___y_4042_;
v___y_3994_ = v___y_4043_;
goto v___jp_3988_;
}
else
{
lean_dec_ref(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec(v_decl_3822_);
return v___x_4084_;
}
}
}
}
else
{
lean_object* v_options_4085_; uint8_t v_hasTrace_4086_; 
v_options_4085_ = lean_ctor_get(v___y_4042_, 2);
v_hasTrace_4086_ = lean_ctor_get_uint8(v_options_4085_, sizeof(void*)*1);
if (v_hasTrace_4086_ == 0)
{
v___y_4004_ = v___y_4038_;
v___y_4005_ = v___y_4039_;
v___y_4006_ = v___y_4040_;
v___y_4007_ = v___y_4042_;
v___y_4008_ = v___y_4043_;
goto v___jp_4003_;
}
else
{
lean_object* v_inheritedTraceOptions_4087_; lean_object* v___x_4088_; uint8_t v___x_4089_; 
v_inheritedTraceOptions_4087_ = lean_ctor_get(v___y_4042_, 13);
v___x_4088_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4089_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4087_, v_options_4085_, v___x_4088_);
if (v___x_4089_ == 0)
{
v___y_4004_ = v___y_4038_;
v___y_4005_ = v___y_4039_;
v___y_4006_ = v___y_4040_;
v___y_4007_ = v___y_4042_;
v___y_4008_ = v___y_4043_;
goto v___jp_4003_;
}
else
{
lean_object* v___x_4090_; lean_object* v___x_4091_; 
v___x_4090_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_4091_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4017_, v___x_4090_, v___y_4042_, v___y_4043_);
if (lean_obj_tag(v___x_4091_) == 0)
{
lean_dec_ref_known(v___x_4091_, 1);
v___y_4004_ = v___y_4038_;
v___y_4005_ = v___y_4039_;
v___y_4006_ = v___y_4040_;
v___y_4007_ = v___y_4042_;
v___y_4008_ = v___y_4043_;
goto v___jp_4003_;
}
else
{
lean_dec_ref(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec(v_decl_3822_);
return v___x_4091_;
}
}
}
}
}
}
v___jp_4092_:
{
lean_object* v___x_4099_; lean_object* v_env_4100_; uint8_t v___x_4101_; 
v___x_4099_ = lean_st_ref_get(v___y_4098_);
v_env_4100_ = lean_ctor_get(v___x_4099_, 0);
lean_inc_ref(v_env_4100_);
lean_dec(v___x_4099_);
v___x_4101_ = l_Lean_Environment_containsOnBranch(v_env_4100_, v_fst_4093_);
lean_dec_ref(v_env_4100_);
if (v___x_4101_ == 0)
{
v___y_4038_ = v_snd_4095_;
v___y_4039_ = v_fst_4093_;
v___y_4040_ = v_fst_4094_;
v___y_4041_ = v_exportedInfo_x3f_4096_;
v___y_4042_ = v___y_4097_;
v___y_4043_ = v___y_4098_;
goto v___jp_4037_;
}
else
{
lean_object* v___x_4102_; lean_object* v_env_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; 
lean_dec(v_exportedInfo_x3f_4096_);
lean_dec_ref(v_fst_4094_);
lean_dec(v_decl_3822_);
v___x_4102_ = lean_st_ref_get(v___y_4098_);
v_env_4103_ = lean_ctor_get(v___x_4102_, 0);
lean_inc_ref(v_env_4103_);
lean_dec(v___x_4102_);
v___x_4104_ = lean_elab_environment_to_kernel_env(v_env_4103_);
v___x_4105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4105_, 0, v___x_4104_);
lean_ctor_set(v___x_4105_, 1, v_fst_4093_);
v___x_4106_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4105_, v___y_4097_, v___y_4098_);
return v___x_4106_;
}
}
v___jp_4107_:
{
lean_object* v_toConstantVal_4112_; lean_object* v_name_4113_; lean_object* v___x_4114_; uint8_t v___x_4115_; 
v_toConstantVal_4112_ = lean_ctor_get(v___y_4108_, 0);
v_name_4113_ = lean_ctor_get(v_toConstantVal_4112_, 0);
lean_inc(v_name_4113_);
v___x_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4114_, 0, v___y_4108_);
v___x_4115_ = 0;
v_fst_4093_ = v_name_4113_;
v_fst_4094_ = v___x_4114_;
v_snd_4095_ = v___x_4115_;
v_exportedInfo_x3f_4096_ = v_exportedInfo_x3f_4109_;
v___y_4097_ = v___y_4110_;
v___y_4098_ = v___y_4111_;
goto v___jp_4092_;
}
v___jp_4116_:
{
lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4122_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4122_, 0, v___y_4117_);
lean_ctor_set_uint8(v___x_4122_, sizeof(void*)*1, v___y_4121_);
v___x_4123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4123_, 0, v___x_4122_);
v___x_4124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4123_);
v___y_4108_ = v___y_4120_;
v_exportedInfo_x3f_4109_ = v___x_4124_;
v___y_4110_ = v___y_4118_;
v___y_4111_ = v___y_4119_;
goto v___jp_4107_;
}
v___jp_4125_:
{
uint8_t v___x_4132_; uint8_t v___x_4133_; 
v___x_4132_ = 1;
v___x_4133_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4129_, v___x_4132_);
if (v___x_4133_ == 0)
{
v___y_4117_ = v_toConstantVal_4128_;
v___y_4118_ = v___y_4130_;
v___y_4119_ = v___y_4131_;
v___y_4120_ = v___y_4127_;
v___y_4121_ = v___y_4126_;
goto v___jp_4116_;
}
else
{
v___y_4117_ = v_toConstantVal_4128_;
v___y_4118_ = v___y_4130_;
v___y_4119_ = v___y_4131_;
v___y_4120_ = v___y_4127_;
v___y_4121_ = v_hasTrace_3881_;
goto v___jp_4116_;
}
}
v___jp_4134_:
{
lean_object* v_toConstantVal_4139_; uint8_t v_safety_4140_; 
v_toConstantVal_4139_ = lean_ctor_get(v___y_4136_, 0);
lean_inc_ref(v_toConstantVal_4139_);
v_safety_4140_ = lean_ctor_get_uint8(v___y_4136_, sizeof(void*)*4);
v___y_4126_ = v___y_4135_;
v___y_4127_ = v___y_4136_;
v_toConstantVal_4128_ = v_toConstantVal_4139_;
v_safety_4129_ = v_safety_4140_;
v___y_4130_ = v___y_4137_;
v___y_4131_ = v___y_4138_;
goto v___jp_4125_;
}
v___jp_4141_:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; 
v___x_4145_ = lean_st_ref_get(v___y_4144_);
v___x_4146_ = lean_st_ref_get(v___y_4144_);
if (v_forceExpose_3823_ == 0)
{
lean_object* v_env_4147_; lean_object* v_env_4148_; lean_object* v___x_4149_; uint8_t v_isModule_4150_; 
v_env_4147_ = lean_ctor_get(v___x_4145_, 0);
lean_inc_ref(v_env_4147_);
lean_dec(v___x_4145_);
v_env_4148_ = lean_ctor_get(v___x_4146_, 0);
lean_inc_ref(v_env_4148_);
lean_dec(v___x_4146_);
v___x_4149_ = l_Lean_Environment_header(v_env_4147_);
lean_dec_ref(v_env_4147_);
v_isModule_4150_ = lean_ctor_get_uint8(v___x_4149_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4149_);
if (v_isModule_4150_ == 0)
{
lean_dec_ref(v_env_4148_);
v___y_4108_ = v_defn_4142_;
v_exportedInfo_x3f_4109_ = v___x_4036_;
v___y_4110_ = v___y_4143_;
v___y_4111_ = v___y_4144_;
goto v___jp_4107_;
}
else
{
uint8_t v_isExporting_4151_; 
v_isExporting_4151_ = lean_ctor_get_uint8(v_env_4148_, sizeof(void*)*8);
lean_dec_ref(v_env_4148_);
if (v_isExporting_4151_ == 0)
{
lean_object* v_options_4152_; uint8_t v_hasTrace_4153_; 
v_options_4152_ = lean_ctor_get(v___y_4143_, 2);
v_hasTrace_4153_ = lean_ctor_get_uint8(v_options_4152_, sizeof(void*)*1);
if (v_hasTrace_4153_ == 0)
{
v___y_4135_ = v_isModule_4150_;
v___y_4136_ = v_defn_4142_;
v___y_4137_ = v___y_4143_;
v___y_4138_ = v___y_4144_;
goto v___jp_4134_;
}
else
{
lean_object* v_inheritedTraceOptions_4154_; lean_object* v___x_4155_; uint8_t v___x_4156_; 
v_inheritedTraceOptions_4154_ = lean_ctor_get(v___y_4143_, 13);
v___x_4155_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4156_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4154_, v_options_4152_, v___x_4155_);
if (v___x_4156_ == 0)
{
v___y_4135_ = v_isModule_4150_;
v___y_4136_ = v_defn_4142_;
v___y_4137_ = v___y_4143_;
v___y_4138_ = v___y_4144_;
goto v___jp_4134_;
}
else
{
lean_object* v_toConstantVal_4157_; uint8_t v_safety_4158_; lean_object* v_name_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
v_toConstantVal_4157_ = lean_ctor_get(v_defn_4142_, 0);
lean_inc_ref(v_toConstantVal_4157_);
v_safety_4158_ = lean_ctor_get_uint8(v_defn_4142_, sizeof(void*)*4);
v_name_4159_ = lean_ctor_get(v_toConstantVal_4157_, 0);
v___x_4160_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_4159_);
v___x_4161_ = l_Lean_MessageData_ofName(v_name_4159_);
v___x_4162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4162_, 0, v___x_4160_);
lean_ctor_set(v___x_4162_, 1, v___x_4161_);
v___x_4163_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4162_);
lean_ctor_set(v___x_4164_, 1, v___x_4163_);
v___x_4165_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4017_, v___x_4164_, v___y_4143_, v___y_4144_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_dec_ref_known(v___x_4165_, 1);
v___y_4126_ = v_isModule_4150_;
v___y_4127_ = v_defn_4142_;
v_toConstantVal_4128_ = v_toConstantVal_4157_;
v_safety_4129_ = v_safety_4158_;
v___y_4130_ = v___y_4143_;
v___y_4131_ = v___y_4144_;
goto v___jp_4125_;
}
else
{
lean_dec_ref(v_toConstantVal_4157_);
lean_dec_ref(v_defn_4142_);
lean_dec(v_decl_3822_);
return v___x_4165_;
}
}
}
}
else
{
v___y_4108_ = v_defn_4142_;
v_exportedInfo_x3f_4109_ = v___x_4036_;
v___y_4110_ = v___y_4143_;
v___y_4111_ = v___y_4144_;
goto v___jp_4107_;
}
}
}
else
{
lean_dec(v___x_4146_);
lean_dec(v___x_4145_);
v___y_4108_ = v_defn_4142_;
v_exportedInfo_x3f_4109_ = v___x_4036_;
v___y_4110_ = v___y_4143_;
v___y_4111_ = v___y_4144_;
goto v___jp_4107_;
}
}
}
}
}
else
{
lean_object* v___f_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; uint8_t v___x_4222_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v_a_4226_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v_a_4272_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; uint8_t v___y_4337_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___y_4355_; 
lean_inc(v_decl_3822_);
v___f_4219_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___boxed), 5, 1);
lean_closure_set(v___f_4219_, 0, v_decl_3822_);
v___x_4220_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_4221_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4222_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3880_, v_options_3879_, v___x_4221_);
if (v___x_4222_ == 0)
{
lean_object* v___x_4522_; uint8_t v___x_4523_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4598_; lean_object* v___y_4599_; lean_object* v___y_4600_; uint8_t v___y_4601_; lean_object* v___y_4602_; lean_object* v___y_4603_; lean_object* v___y_4604_; lean_object* v___y_4605_; lean_object* v___y_4606_; lean_object* v___y_4607_; uint8_t v___y_4629_; lean_object* v___y_4630_; lean_object* v___y_4631_; lean_object* v_exportedInfo_x3f_4632_; lean_object* v___y_4633_; lean_object* v___y_4634_; uint8_t v___y_4644_; lean_object* v___y_4645_; lean_object* v___y_4646_; lean_object* v___y_4647_; lean_object* v___y_4648_; uint8_t v___y_4651_; lean_object* v___y_4652_; lean_object* v___y_4653_; lean_object* v___y_4654_; lean_object* v___y_4655_; 
v___x_4522_ = l_Lean_trace_profiler;
v___x_4523_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3879_, v___x_4522_);
if (v___x_4523_ == 0)
{
lean_object* v___x_4657_; lean_object* v_env_4658_; lean_object* v_nextMacroScope_4659_; lean_object* v_ngen_4660_; lean_object* v_auxDeclNGen_4661_; lean_object* v_traceState_4662_; lean_object* v_messages_4663_; lean_object* v_infoState_4664_; lean_object* v_snapshotTasks_4665_; lean_object* v___x_4667_; uint8_t v_isShared_4668_; uint8_t v_isSharedCheck_4901_; 
lean_dec_ref(v___f_4219_);
v___x_4657_ = lean_st_ref_take(v_a_3825_);
v_env_4658_ = lean_ctor_get(v___x_4657_, 0);
v_nextMacroScope_4659_ = lean_ctor_get(v___x_4657_, 1);
v_ngen_4660_ = lean_ctor_get(v___x_4657_, 2);
v_auxDeclNGen_4661_ = lean_ctor_get(v___x_4657_, 3);
v_traceState_4662_ = lean_ctor_get(v___x_4657_, 4);
v_messages_4663_ = lean_ctor_get(v___x_4657_, 6);
v_infoState_4664_ = lean_ctor_get(v___x_4657_, 7);
v_snapshotTasks_4665_ = lean_ctor_get(v___x_4657_, 8);
v_isSharedCheck_4901_ = !lean_is_exclusive(v___x_4657_);
if (v_isSharedCheck_4901_ == 0)
{
lean_object* v_unused_4902_; 
v_unused_4902_ = lean_ctor_get(v___x_4657_, 5);
lean_dec(v_unused_4902_);
v___x_4667_ = v___x_4657_;
v_isShared_4668_ = v_isSharedCheck_4901_;
goto v_resetjp_4666_;
}
else
{
lean_inc(v_snapshotTasks_4665_);
lean_inc(v_infoState_4664_);
lean_inc(v_messages_4663_);
lean_inc(v_traceState_4662_);
lean_inc(v_auxDeclNGen_4661_);
lean_inc(v_ngen_4660_);
lean_inc(v_nextMacroScope_4659_);
lean_inc(v_env_4658_);
lean_dec(v___x_4657_);
v___x_4667_ = lean_box(0);
v_isShared_4668_ = v_isSharedCheck_4901_;
goto v_resetjp_4666_;
}
v_resetjp_4666_:
{
lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; uint8_t v___y_4673_; lean_object* v___y_4674_; lean_object* v___y_4675_; lean_object* v___y_4676_; lean_object* v___y_4677_; lean_object* v___y_4678_; lean_object* v___x_4701_; 
lean_inc(v_decl_3822_);
v___x_4669_ = l_Lean_Declaration_getNames(v_decl_3822_);
v___x_4670_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4658_, v___x_4669_);
v___x_4671_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4668_ == 0)
{
lean_ctor_set(v___x_4667_, 5, v___x_4671_);
lean_ctor_set(v___x_4667_, 0, v___x_4670_);
v___x_4701_ = v___x_4667_;
goto v_reusejp_4700_;
}
else
{
lean_object* v_reuseFailAlloc_4900_; 
v_reuseFailAlloc_4900_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4900_, 0, v___x_4670_);
lean_ctor_set(v_reuseFailAlloc_4900_, 1, v_nextMacroScope_4659_);
lean_ctor_set(v_reuseFailAlloc_4900_, 2, v_ngen_4660_);
lean_ctor_set(v_reuseFailAlloc_4900_, 3, v_auxDeclNGen_4661_);
lean_ctor_set(v_reuseFailAlloc_4900_, 4, v_traceState_4662_);
lean_ctor_set(v_reuseFailAlloc_4900_, 5, v___x_4671_);
lean_ctor_set(v_reuseFailAlloc_4900_, 6, v_messages_4663_);
lean_ctor_set(v_reuseFailAlloc_4900_, 7, v_infoState_4664_);
lean_ctor_set(v_reuseFailAlloc_4900_, 8, v_snapshotTasks_4665_);
v___x_4701_ = v_reuseFailAlloc_4900_;
goto v_reusejp_4700_;
}
v___jp_4672_:
{
lean_object* v___x_4679_; lean_object* v_env_4680_; lean_object* v_nextMacroScope_4681_; lean_object* v_ngen_4682_; lean_object* v_auxDeclNGen_4683_; lean_object* v_traceState_4684_; lean_object* v_messages_4685_; lean_object* v_infoState_4686_; lean_object* v_snapshotTasks_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4698_; 
v___x_4679_ = lean_st_ref_take(v___y_4678_);
v_env_4680_ = lean_ctor_get(v___x_4679_, 0);
v_nextMacroScope_4681_ = lean_ctor_get(v___x_4679_, 1);
v_ngen_4682_ = lean_ctor_get(v___x_4679_, 2);
v_auxDeclNGen_4683_ = lean_ctor_get(v___x_4679_, 3);
v_traceState_4684_ = lean_ctor_get(v___x_4679_, 4);
v_messages_4685_ = lean_ctor_get(v___x_4679_, 6);
v_infoState_4686_ = lean_ctor_get(v___x_4679_, 7);
v_snapshotTasks_4687_ = lean_ctor_get(v___x_4679_, 8);
v_isSharedCheck_4698_ = !lean_is_exclusive(v___x_4679_);
if (v_isSharedCheck_4698_ == 0)
{
lean_object* v_unused_4699_; 
v_unused_4699_ = lean_ctor_get(v___x_4679_, 5);
lean_dec(v_unused_4699_);
v___x_4689_ = v___x_4679_;
v_isShared_4690_ = v_isSharedCheck_4698_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_snapshotTasks_4687_);
lean_inc(v_infoState_4686_);
lean_inc(v_messages_4685_);
lean_inc(v_traceState_4684_);
lean_inc(v_auxDeclNGen_4683_);
lean_inc(v_ngen_4682_);
lean_inc(v_nextMacroScope_4681_);
lean_inc(v_env_4680_);
lean_dec(v___x_4679_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4698_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4695_; 
v___x_4691_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4692_ = lean_box(v___y_4673_);
lean_inc(v___y_4677_);
v___x_4693_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4691_, v_env_4680_, v___y_4677_, v___x_4692_);
if (v_isShared_4690_ == 0)
{
lean_ctor_set(v___x_4689_, 5, v___x_4671_);
lean_ctor_set(v___x_4689_, 0, v___x_4693_);
v___x_4695_ = v___x_4689_;
goto v_reusejp_4694_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v___x_4693_);
lean_ctor_set(v_reuseFailAlloc_4697_, 1, v_nextMacroScope_4681_);
lean_ctor_set(v_reuseFailAlloc_4697_, 2, v_ngen_4682_);
lean_ctor_set(v_reuseFailAlloc_4697_, 3, v_auxDeclNGen_4683_);
lean_ctor_set(v_reuseFailAlloc_4697_, 4, v_traceState_4684_);
lean_ctor_set(v_reuseFailAlloc_4697_, 5, v___x_4671_);
lean_ctor_set(v_reuseFailAlloc_4697_, 6, v_messages_4685_);
lean_ctor_set(v_reuseFailAlloc_4697_, 7, v_infoState_4686_);
lean_ctor_set(v_reuseFailAlloc_4697_, 8, v_snapshotTasks_4687_);
v___x_4695_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4694_;
}
v_reusejp_4694_:
{
lean_object* v___x_4696_; 
v___x_4696_ = lean_st_ref_put(v___y_4678_, v___x_4695_);
v___y_4629_ = v___y_4673_;
v___y_4630_ = v___y_4676_;
v___y_4631_ = v___y_4677_;
v_exportedInfo_x3f_4632_ = v___y_4674_;
v___y_4633_ = v___y_4675_;
v___y_4634_ = v___y_4678_;
goto v___jp_4628_;
}
}
}
v_reusejp_4700_:
{
lean_object* v___x_4702_; lean_object* v___y_4704_; lean_object* v_options_4705_; lean_object* v_inheritedTraceOptions_4706_; lean_object* v___y_4707_; lean_object* v___x_4713_; uint8_t v___y_4715_; lean_object* v___y_4716_; lean_object* v___y_4717_; lean_object* v___y_4718_; lean_object* v___y_4719_; lean_object* v___y_4720_; lean_object* v_fst_4746_; lean_object* v_fst_4747_; uint8_t v_snd_4748_; lean_object* v_exportedInfo_x3f_4749_; lean_object* v___y_4750_; lean_object* v___y_4751_; lean_object* v___y_4761_; lean_object* v_exportedInfo_x3f_4762_; lean_object* v___y_4763_; lean_object* v___y_4764_; lean_object* v___y_4770_; lean_object* v___y_4771_; lean_object* v___y_4772_; lean_object* v___y_4773_; uint8_t v___y_4774_; lean_object* v___y_4779_; lean_object* v_toConstantVal_4780_; uint8_t v_safety_4781_; lean_object* v___y_4782_; lean_object* v___y_4783_; lean_object* v___y_4787_; lean_object* v___y_4788_; lean_object* v___y_4789_; lean_object* v___y_4793_; lean_object* v___y_4794_; lean_object* v___y_4795_; lean_object* v___y_4810_; lean_object* v___y_4811_; lean_object* v___y_4812_; lean_object* v___y_4813_; lean_object* v___y_4814_; lean_object* v_defn_4819_; lean_object* v___y_4820_; lean_object* v___y_4821_; 
v___x_4702_ = lean_st_ref_put(v_a_3825_, v___x_4701_);
v___x_4713_ = lean_box(0);
switch(lean_obj_tag(v_decl_3822_))
{
case 2:
{
lean_object* v_val_4828_; lean_object* v_exportedInfo_x3f_4830_; lean_object* v___y_4831_; lean_object* v___y_4832_; lean_object* v___y_4838_; lean_object* v___y_4839_; lean_object* v___x_4844_; lean_object* v_env_4845_; 
v_val_4828_ = lean_ctor_get(v_decl_3822_, 0);
v___x_4844_ = lean_st_ref_get(v_a_3825_);
v_env_4845_ = lean_ctor_get(v___x_4844_, 0);
lean_inc_ref(v_env_4845_);
lean_dec(v___x_4844_);
if (v_forceExpose_3823_ == 0)
{
goto v___jp_4846_;
}
else
{
if (v___x_4523_ == 0)
{
lean_dec_ref(v_env_4845_);
v_exportedInfo_x3f_4830_ = v___x_4713_;
v___y_4831_ = v_a_3824_;
v___y_4832_ = v_a_3825_;
goto v___jp_4829_;
}
else
{
goto v___jp_4846_;
}
}
v___jp_4829_:
{
lean_object* v_toConstantVal_4833_; lean_object* v_name_4834_; lean_object* v___x_4835_; uint8_t v___x_4836_; 
v_toConstantVal_4833_ = lean_ctor_get(v_val_4828_, 0);
v_name_4834_ = lean_ctor_get(v_toConstantVal_4833_, 0);
lean_inc_ref(v_val_4828_);
v___x_4835_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4835_, 0, v_val_4828_);
v___x_4836_ = 1;
lean_inc(v_name_4834_);
v_fst_4746_ = v_name_4834_;
v_fst_4747_ = v___x_4835_;
v_snd_4748_ = v___x_4836_;
v_exportedInfo_x3f_4749_ = v_exportedInfo_x3f_4830_;
v___y_4750_ = v___y_4831_;
v___y_4751_ = v___y_4832_;
goto v___jp_4745_;
}
v___jp_4837_:
{
lean_object* v_toConstantVal_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; 
v_toConstantVal_4840_ = lean_ctor_get(v_val_4828_, 0);
lean_inc_ref(v_toConstantVal_4840_);
v___x_4841_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4841_, 0, v_toConstantVal_4840_);
lean_ctor_set_uint8(v___x_4841_, sizeof(void*)*1, v___x_4523_);
v___x_4842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4842_, 0, v___x_4841_);
v___x_4843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4843_, 0, v___x_4842_);
v_exportedInfo_x3f_4830_ = v___x_4843_;
v___y_4831_ = v___y_4838_;
v___y_4832_ = v___y_4839_;
goto v___jp_4829_;
}
v___jp_4846_:
{
lean_object* v___x_4847_; uint8_t v_isModule_4848_; 
v___x_4847_ = l_Lean_Environment_header(v_env_4845_);
lean_dec_ref(v_env_4845_);
v_isModule_4848_ = lean_ctor_get_uint8(v___x_4847_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4847_);
if (v_isModule_4848_ == 0)
{
v_exportedInfo_x3f_4830_ = v___x_4713_;
v___y_4831_ = v_a_3824_;
v___y_4832_ = v_a_3825_;
goto v___jp_4829_;
}
else
{
if (v___x_4222_ == 0)
{
v___y_4838_ = v_a_3824_;
v___y_4839_ = v_a_3825_;
goto v___jp_4837_;
}
else
{
lean_object* v_toConstantVal_4849_; lean_object* v_name_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; 
v_toConstantVal_4849_ = lean_ctor_get(v_val_4828_, 0);
v_name_4850_ = lean_ctor_get(v_toConstantVal_4849_, 0);
v___x_4851_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4850_);
v___x_4852_ = l_Lean_MessageData_ofName(v_name_4850_);
v___x_4853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4853_, 0, v___x_4851_);
lean_ctor_set(v___x_4853_, 1, v___x_4852_);
v___x_4854_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4855_, 0, v___x_4853_);
lean_ctor_set(v___x_4855_, 1, v___x_4854_);
v___x_4856_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4017_, v___x_4855_, v_a_3824_, v_a_3825_);
if (lean_obj_tag(v___x_4856_) == 0)
{
lean_dec_ref_known(v___x_4856_, 1);
v___y_4838_ = v_a_3824_;
v___y_4839_ = v_a_3825_;
goto v___jp_4837_;
}
else
{
lean_dec_ref_known(v_decl_3822_, 1);
return v___x_4856_;
}
}
}
}
}
case 1:
{
lean_object* v_val_4857_; 
v_val_4857_ = lean_ctor_get(v_decl_3822_, 0);
lean_inc_ref(v_val_4857_);
v_defn_4819_ = v_val_4857_;
v___y_4820_ = v_a_3824_;
v___y_4821_ = v_a_3825_;
goto v___jp_4818_;
}
case 5:
{
lean_object* v_defns_4858_; 
v_defns_4858_ = lean_ctor_get(v_decl_3822_, 0);
if (lean_obj_tag(v_defns_4858_) == 1)
{
lean_object* v_tail_4859_; 
v_tail_4859_ = lean_ctor_get(v_defns_4858_, 1);
if (lean_obj_tag(v_tail_4859_) == 0)
{
lean_object* v_head_4860_; 
v_head_4860_ = lean_ctor_get(v_defns_4858_, 0);
lean_inc(v_head_4860_);
v_defn_4819_ = v_head_4860_;
v___y_4820_ = v_a_3824_;
v___y_4821_ = v_a_3825_;
goto v___jp_4818_;
}
else
{
v___y_4704_ = v_a_3824_;
v_options_4705_ = v_options_3879_;
v_inheritedTraceOptions_4706_ = v_inheritedTraceOptions_3880_;
v___y_4707_ = v_a_3825_;
goto v___jp_4703_;
}
}
else
{
v___y_4704_ = v_a_3824_;
v_options_4705_ = v_options_3879_;
v_inheritedTraceOptions_4706_ = v_inheritedTraceOptions_3880_;
v___y_4707_ = v_a_3825_;
goto v___jp_4703_;
}
}
case 3:
{
lean_object* v_val_4861_; lean_object* v_exportedInfo_x3f_4863_; lean_object* v___y_4864_; lean_object* v___y_4865_; lean_object* v___y_4871_; lean_object* v___y_4872_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v_env_4889_; lean_object* v_env_4890_; 
v_val_4861_ = lean_ctor_get(v_decl_3822_, 0);
v___x_4878_ = lean_st_ref_get(v_a_3825_);
v___x_4879_ = lean_st_ref_get(v_a_3825_);
v_env_4889_ = lean_ctor_get(v___x_4878_, 0);
lean_inc_ref(v_env_4889_);
lean_dec(v___x_4878_);
v_env_4890_ = lean_ctor_get(v___x_4879_, 0);
lean_inc_ref(v_env_4890_);
lean_dec(v___x_4879_);
if (v_forceExpose_3823_ == 0)
{
goto v___jp_4891_;
}
else
{
if (v___x_4523_ == 0)
{
lean_dec_ref(v_env_4890_);
lean_dec_ref(v_env_4889_);
v_exportedInfo_x3f_4863_ = v___x_4713_;
v___y_4864_ = v_a_3824_;
v___y_4865_ = v_a_3825_;
goto v___jp_4862_;
}
else
{
goto v___jp_4891_;
}
}
v___jp_4862_:
{
lean_object* v_toConstantVal_4866_; lean_object* v_name_4867_; lean_object* v___x_4868_; uint8_t v___x_4869_; 
v_toConstantVal_4866_ = lean_ctor_get(v_val_4861_, 0);
v_name_4867_ = lean_ctor_get(v_toConstantVal_4866_, 0);
lean_inc_ref(v_val_4861_);
v___x_4868_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4868_, 0, v_val_4861_);
v___x_4869_ = 3;
lean_inc(v_name_4867_);
v_fst_4746_ = v_name_4867_;
v_fst_4747_ = v___x_4868_;
v_snd_4748_ = v___x_4869_;
v_exportedInfo_x3f_4749_ = v_exportedInfo_x3f_4863_;
v___y_4750_ = v___y_4864_;
v___y_4751_ = v___y_4865_;
goto v___jp_4745_;
}
v___jp_4870_:
{
lean_object* v_toConstantVal_4873_; uint8_t v_isUnsafe_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; 
v_toConstantVal_4873_ = lean_ctor_get(v_val_4861_, 0);
v_isUnsafe_4874_ = lean_ctor_get_uint8(v_val_4861_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4873_);
v___x_4875_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4875_, 0, v_toConstantVal_4873_);
lean_ctor_set_uint8(v___x_4875_, sizeof(void*)*1, v_isUnsafe_4874_);
v___x_4876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4876_, 0, v___x_4875_);
v___x_4877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4877_, 0, v___x_4876_);
v_exportedInfo_x3f_4863_ = v___x_4877_;
v___y_4864_ = v___y_4871_;
v___y_4865_ = v___y_4872_;
goto v___jp_4862_;
}
v___jp_4880_:
{
if (v___x_4222_ == 0)
{
v___y_4871_ = v_a_3824_;
v___y_4872_ = v_a_3825_;
goto v___jp_4870_;
}
else
{
lean_object* v_toConstantVal_4881_; lean_object* v_name_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; 
v_toConstantVal_4881_ = lean_ctor_get(v_val_4861_, 0);
v_name_4882_ = lean_ctor_get(v_toConstantVal_4881_, 0);
v___x_4883_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4882_);
v___x_4884_ = l_Lean_MessageData_ofName(v_name_4882_);
v___x_4885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4885_, 0, v___x_4883_);
lean_ctor_set(v___x_4885_, 1, v___x_4884_);
v___x_4886_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4887_, 0, v___x_4885_);
lean_ctor_set(v___x_4887_, 1, v___x_4886_);
v___x_4888_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4017_, v___x_4887_, v_a_3824_, v_a_3825_);
if (lean_obj_tag(v___x_4888_) == 0)
{
lean_dec_ref_known(v___x_4888_, 1);
v___y_4871_ = v_a_3824_;
v___y_4872_ = v_a_3825_;
goto v___jp_4870_;
}
else
{
lean_dec_ref_known(v_decl_3822_, 1);
return v___x_4888_;
}
}
}
v___jp_4891_:
{
lean_object* v___x_4892_; uint8_t v_isModule_4893_; 
v___x_4892_ = l_Lean_Environment_header(v_env_4889_);
lean_dec_ref(v_env_4889_);
v_isModule_4893_ = lean_ctor_get_uint8(v___x_4892_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4892_);
if (v_isModule_4893_ == 0)
{
lean_dec_ref(v_env_4890_);
v_exportedInfo_x3f_4863_ = v___x_4713_;
v___y_4864_ = v_a_3824_;
v___y_4865_ = v_a_3825_;
goto v___jp_4862_;
}
else
{
uint8_t v_isExporting_4894_; 
v_isExporting_4894_ = lean_ctor_get_uint8(v_env_4890_, sizeof(void*)*8);
lean_dec_ref(v_env_4890_);
if (v_isExporting_4894_ == 0)
{
goto v___jp_4880_;
}
else
{
if (v___x_4523_ == 0)
{
v_exportedInfo_x3f_4863_ = v___x_4713_;
v___y_4864_ = v_a_3824_;
v___y_4865_ = v_a_3825_;
goto v___jp_4862_;
}
else
{
goto v___jp_4880_;
}
}
}
}
}
case 0:
{
lean_object* v_val_4895_; lean_object* v_toConstantVal_4896_; lean_object* v_name_4897_; lean_object* v___x_4898_; uint8_t v___x_4899_; 
v_val_4895_ = lean_ctor_get(v_decl_3822_, 0);
v_toConstantVal_4896_ = lean_ctor_get(v_val_4895_, 0);
v_name_4897_ = lean_ctor_get(v_toConstantVal_4896_, 0);
lean_inc_ref(v_val_4895_);
v___x_4898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4898_, 0, v_val_4895_);
v___x_4899_ = 2;
lean_inc(v_name_4897_);
v_fst_4746_ = v_name_4897_;
v_fst_4747_ = v___x_4898_;
v_snd_4748_ = v___x_4899_;
v_exportedInfo_x3f_4749_ = v___x_4713_;
v___y_4750_ = v_a_3824_;
v___y_4751_ = v_a_3825_;
goto v___jp_4745_;
}
default: 
{
v___y_4704_ = v_a_3824_;
v_options_4705_ = v_options_3879_;
v_inheritedTraceOptions_4706_ = v_inheritedTraceOptions_3880_;
v___y_4707_ = v_a_3825_;
goto v___jp_4703_;
}
}
v___jp_4703_:
{
uint8_t v___x_4708_; 
v___x_4708_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4706_, v_options_4705_, v___x_4221_);
if (v___x_4708_ == 0)
{
lean_object* v___x_4709_; 
v___x_4709_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3822_, v___y_4704_, v___y_4707_);
return v___x_4709_;
}
else
{
lean_object* v___x_4710_; lean_object* v___x_4711_; 
v___x_4710_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1);
v___x_4711_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4017_, v___x_4710_, v___y_4704_, v___y_4707_);
if (lean_obj_tag(v___x_4711_) == 0)
{
lean_object* v___x_4712_; 
lean_dec_ref_known(v___x_4711_, 1);
v___x_4712_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3822_, v___y_4704_, v___y_4707_);
return v___x_4712_;
}
else
{
lean_dec(v_decl_3822_);
return v___x_4711_;
}
}
}
v___jp_4714_:
{
lean_object* v___x_4721_; uint8_t v___x_4722_; 
lean_inc(v_decl_3822_);
v___x_4721_ = l_Lean_Declaration_getTopLevelNames(v_decl_3822_);
v___x_4722_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_4721_);
lean_dec(v___x_4721_);
if (v___x_4722_ == 0)
{
if (lean_obj_tag(v___y_4716_) == 0)
{
if (v___x_4523_ == 0)
{
lean_object* v_options_4723_; uint8_t v_hasTrace_4724_; 
v_options_4723_ = lean_ctor_get(v___y_4719_, 2);
v_hasTrace_4724_ = lean_ctor_get_uint8(v_options_4723_, sizeof(void*)*1);
if (v_hasTrace_4724_ == 0)
{
v___y_4644_ = v___y_4715_;
v___y_4645_ = v___y_4717_;
v___y_4646_ = v___y_4718_;
v___y_4647_ = v___y_4719_;
v___y_4648_ = v___y_4720_;
goto v___jp_4643_;
}
else
{
lean_object* v_inheritedTraceOptions_4725_; uint8_t v___x_4726_; 
v_inheritedTraceOptions_4725_ = lean_ctor_get(v___y_4719_, 13);
v___x_4726_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4725_, v_options_4723_, v___x_4221_);
if (v___x_4726_ == 0)
{
v___y_4644_ = v___y_4715_;
v___y_4645_ = v___y_4717_;
v___y_4646_ = v___y_4718_;
v___y_4647_ = v___y_4719_;
v___y_4648_ = v___y_4720_;
goto v___jp_4643_;
}
else
{
lean_object* v___x_4727_; lean_object* v___x_4728_; 
v___x_4727_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_4728_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4017_, v___x_4727_, v___y_4719_, v___y_4720_);
if (lean_obj_tag(v___x_4728_) == 0)
{
lean_dec_ref_known(v___x_4728_, 1);
v___y_4644_ = v___y_4715_;
v___y_4645_ = v___y_4717_;
v___y_4646_ = v___y_4718_;
v___y_4647_ = v___y_4719_;
v___y_4648_ = v___y_4720_;
goto v___jp_4643_;
}
else
{
lean_dec(v___y_4718_);
lean_dec_ref(v___y_4717_);
lean_dec(v_decl_3822_);
return v___x_4728_;
}
}
}
}
else
{
v___y_4673_ = v___y_4715_;
v___y_4674_ = v___y_4716_;
v___y_4675_ = v___y_4719_;
v___y_4676_ = v___y_4717_;
v___y_4677_ = v___y_4718_;
v___y_4678_ = v___y_4720_;
goto v___jp_4672_;
}
}
else
{
v___y_4673_ = v___y_4715_;
v___y_4674_ = v___y_4716_;
v___y_4675_ = v___y_4719_;
v___y_4676_ = v___y_4717_;
v___y_4677_ = v___y_4718_;
v___y_4678_ = v___y_4720_;
goto v___jp_4672_;
}
}
else
{
lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v_a_4731_; uint8_t v___x_4732_; 
lean_dec(v___y_4716_);
v___x_4729_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4730_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4729_, v___y_4719_);
v_a_4731_ = lean_ctor_get(v___x_4730_, 0);
lean_inc(v_a_4731_);
lean_dec_ref(v___x_4730_);
v___x_4732_ = lean_unbox(v_a_4731_);
lean_dec(v_a_4731_);
if (v___x_4732_ == 0)
{
lean_object* v_options_4733_; uint8_t v_hasTrace_4734_; 
v_options_4733_ = lean_ctor_get(v___y_4719_, 2);
v_hasTrace_4734_ = lean_ctor_get_uint8(v_options_4733_, sizeof(void*)*1);
if (v_hasTrace_4734_ == 0)
{
v___y_4629_ = v___y_4715_;
v___y_4630_ = v___y_4717_;
v___y_4631_ = v___y_4718_;
v_exportedInfo_x3f_4632_ = v___x_4713_;
v___y_4633_ = v___y_4719_;
v___y_4634_ = v___y_4720_;
goto v___jp_4628_;
}
else
{
lean_object* v_inheritedTraceOptions_4735_; uint8_t v___x_4736_; 
v_inheritedTraceOptions_4735_ = lean_ctor_get(v___y_4719_, 13);
v___x_4736_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4735_, v_options_4733_, v___x_4221_);
if (v___x_4736_ == 0)
{
v___y_4629_ = v___y_4715_;
v___y_4630_ = v___y_4717_;
v___y_4631_ = v___y_4718_;
v_exportedInfo_x3f_4632_ = v___x_4713_;
v___y_4633_ = v___y_4719_;
v___y_4634_ = v___y_4720_;
goto v___jp_4628_;
}
else
{
lean_object* v___x_4737_; lean_object* v___x_4738_; 
v___x_4737_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_4738_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4017_, v___x_4737_, v___y_4719_, v___y_4720_);
if (lean_obj_tag(v___x_4738_) == 0)
{
lean_dec_ref_known(v___x_4738_, 1);
v___y_4629_ = v___y_4715_;
v___y_4630_ = v___y_4717_;
v___y_4631_ = v___y_4718_;
v_exportedInfo_x3f_4632_ = v___x_4713_;
v___y_4633_ = v___y_4719_;
v___y_4634_ = v___y_4720_;
goto v___jp_4628_;
}
else
{
lean_dec(v___y_4718_);
lean_dec_ref(v___y_4717_);
lean_dec(v_decl_3822_);
return v___x_4738_;
}
}
}
}
else
{
lean_object* v_options_4739_; uint8_t v_hasTrace_4740_; 
v_options_4739_ = lean_ctor_get(v___y_4719_, 2);
v_hasTrace_4740_ = lean_ctor_get_uint8(v_options_4739_, sizeof(void*)*1);
if (v_hasTrace_4740_ == 0)
{
v___y_4651_ = v___y_4715_;
v___y_4652_ = v___y_4717_;
v___y_4653_ = v___y_4718_;
v___y_4654_ = v___y_4719_;
v___y_4655_ = v___y_4720_;
goto v___jp_4650_;
}
else
{
lean_object* v_inheritedTraceOptions_4741_; uint8_t v___x_4742_; 
v_inheritedTraceOptions_4741_ = lean_ctor_get(v___y_4719_, 13);
v___x_4742_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4741_, v_options_4739_, v___x_4221_);
if (v___x_4742_ == 0)
{
v___y_4651_ = v___y_4715_;
v___y_4652_ = v___y_4717_;
v___y_4653_ = v___y_4718_;
v___y_4654_ = v___y_4719_;
v___y_4655_ = v___y_4720_;
goto v___jp_4650_;
}
else
{
lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4743_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_4744_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4017_, v___x_4743_, v___y_4719_, v___y_4720_);
if (lean_obj_tag(v___x_4744_) == 0)
{
lean_dec_ref_known(v___x_4744_, 1);
v___y_4651_ = v___y_4715_;
v___y_4652_ = v___y_4717_;
v___y_4653_ = v___y_4718_;
v___y_4654_ = v___y_4719_;
v___y_4655_ = v___y_4720_;
goto v___jp_4650_;
}
else
{
lean_dec(v___y_4718_);
lean_dec_ref(v___y_4717_);
lean_dec(v_decl_3822_);
return v___x_4744_;
}
}
}
}
}
}
v___jp_4745_:
{
lean_object* v___x_4752_; lean_object* v_env_4753_; uint8_t v___x_4754_; 
v___x_4752_ = lean_st_ref_get(v___y_4751_);
v_env_4753_ = lean_ctor_get(v___x_4752_, 0);
lean_inc_ref(v_env_4753_);
lean_dec(v___x_4752_);
v___x_4754_ = l_Lean_Environment_containsOnBranch(v_env_4753_, v_fst_4746_);
lean_dec_ref(v_env_4753_);
if (v___x_4754_ == 0)
{
v___y_4715_ = v_snd_4748_;
v___y_4716_ = v_exportedInfo_x3f_4749_;
v___y_4717_ = v_fst_4747_;
v___y_4718_ = v_fst_4746_;
v___y_4719_ = v___y_4750_;
v___y_4720_ = v___y_4751_;
goto v___jp_4714_;
}
else
{
lean_object* v___x_4755_; lean_object* v_env_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; 
lean_dec(v_exportedInfo_x3f_4749_);
lean_dec_ref(v_fst_4747_);
lean_dec(v_decl_3822_);
v___x_4755_ = lean_st_ref_get(v___y_4751_);
v_env_4756_ = lean_ctor_get(v___x_4755_, 0);
lean_inc_ref(v_env_4756_);
lean_dec(v___x_4755_);
v___x_4757_ = lean_elab_environment_to_kernel_env(v_env_4756_);
v___x_4758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4758_, 0, v___x_4757_);
lean_ctor_set(v___x_4758_, 1, v_fst_4746_);
v___x_4759_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4758_, v___y_4750_, v___y_4751_);
return v___x_4759_;
}
}
v___jp_4760_:
{
lean_object* v_toConstantVal_4765_; lean_object* v_name_4766_; lean_object* v___x_4767_; uint8_t v___x_4768_; 
v_toConstantVal_4765_ = lean_ctor_get(v___y_4761_, 0);
v_name_4766_ = lean_ctor_get(v_toConstantVal_4765_, 0);
lean_inc(v_name_4766_);
v___x_4767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4767_, 0, v___y_4761_);
v___x_4768_ = 0;
v_fst_4746_ = v_name_4766_;
v_fst_4747_ = v___x_4767_;
v_snd_4748_ = v___x_4768_;
v_exportedInfo_x3f_4749_ = v_exportedInfo_x3f_4762_;
v___y_4750_ = v___y_4763_;
v___y_4751_ = v___y_4764_;
goto v___jp_4745_;
}
v___jp_4769_:
{
lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; 
v___x_4775_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4775_, 0, v___y_4772_);
lean_ctor_set_uint8(v___x_4775_, sizeof(void*)*1, v___y_4774_);
v___x_4776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4776_, 0, v___x_4775_);
v___x_4777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4777_, 0, v___x_4776_);
v___y_4761_ = v___y_4773_;
v_exportedInfo_x3f_4762_ = v___x_4777_;
v___y_4763_ = v___y_4770_;
v___y_4764_ = v___y_4771_;
goto v___jp_4760_;
}
v___jp_4778_:
{
uint8_t v___x_4784_; uint8_t v___x_4785_; 
v___x_4784_ = 1;
v___x_4785_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4781_, v___x_4784_);
if (v___x_4785_ == 0)
{
v___y_4770_ = v___y_4782_;
v___y_4771_ = v___y_4783_;
v___y_4772_ = v_toConstantVal_4780_;
v___y_4773_ = v___y_4779_;
v___y_4774_ = v_hasTrace_3881_;
goto v___jp_4769_;
}
else
{
v___y_4770_ = v___y_4782_;
v___y_4771_ = v___y_4783_;
v___y_4772_ = v_toConstantVal_4780_;
v___y_4773_ = v___y_4779_;
v___y_4774_ = v___x_4523_;
goto v___jp_4769_;
}
}
v___jp_4786_:
{
lean_object* v_toConstantVal_4790_; uint8_t v_safety_4791_; 
v_toConstantVal_4790_ = lean_ctor_get(v___y_4787_, 0);
lean_inc_ref(v_toConstantVal_4790_);
v_safety_4791_ = lean_ctor_get_uint8(v___y_4787_, sizeof(void*)*4);
v___y_4779_ = v___y_4787_;
v_toConstantVal_4780_ = v_toConstantVal_4790_;
v_safety_4781_ = v_safety_4791_;
v___y_4782_ = v___y_4788_;
v___y_4783_ = v___y_4789_;
goto v___jp_4778_;
}
v___jp_4792_:
{
lean_object* v_options_4796_; uint8_t v_hasTrace_4797_; 
v_options_4796_ = lean_ctor_get(v___y_4793_, 2);
v_hasTrace_4797_ = lean_ctor_get_uint8(v_options_4796_, sizeof(void*)*1);
if (v_hasTrace_4797_ == 0)
{
v___y_4787_ = v___y_4794_;
v___y_4788_ = v___y_4793_;
v___y_4789_ = v___y_4795_;
goto v___jp_4786_;
}
else
{
lean_object* v_inheritedTraceOptions_4798_; uint8_t v___x_4799_; 
v_inheritedTraceOptions_4798_ = lean_ctor_get(v___y_4793_, 13);
v___x_4799_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4798_, v_options_4796_, v___x_4221_);
if (v___x_4799_ == 0)
{
v___y_4787_ = v___y_4794_;
v___y_4788_ = v___y_4793_;
v___y_4789_ = v___y_4795_;
goto v___jp_4786_;
}
else
{
lean_object* v_toConstantVal_4800_; uint8_t v_safety_4801_; lean_object* v_name_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; 
v_toConstantVal_4800_ = lean_ctor_get(v___y_4794_, 0);
lean_inc_ref(v_toConstantVal_4800_);
v_safety_4801_ = lean_ctor_get_uint8(v___y_4794_, sizeof(void*)*4);
v_name_4802_ = lean_ctor_get(v_toConstantVal_4800_, 0);
v___x_4803_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_4802_);
v___x_4804_ = l_Lean_MessageData_ofName(v_name_4802_);
v___x_4805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4805_, 0, v___x_4803_);
lean_ctor_set(v___x_4805_, 1, v___x_4804_);
v___x_4806_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4807_, 0, v___x_4805_);
lean_ctor_set(v___x_4807_, 1, v___x_4806_);
v___x_4808_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4017_, v___x_4807_, v___y_4793_, v___y_4795_);
if (lean_obj_tag(v___x_4808_) == 0)
{
lean_dec_ref_known(v___x_4808_, 1);
v___y_4779_ = v___y_4794_;
v_toConstantVal_4780_ = v_toConstantVal_4800_;
v_safety_4781_ = v_safety_4801_;
v___y_4782_ = v___y_4793_;
v___y_4783_ = v___y_4795_;
goto v___jp_4778_;
}
else
{
lean_dec_ref(v_toConstantVal_4800_);
lean_dec_ref(v___y_4794_);
lean_dec(v_decl_3822_);
return v___x_4808_;
}
}
}
}
v___jp_4809_:
{
lean_object* v___x_4815_; uint8_t v_isModule_4816_; 
v___x_4815_ = l_Lean_Environment_header(v___y_4814_);
lean_dec_ref(v___y_4814_);
v_isModule_4816_ = lean_ctor_get_uint8(v___x_4815_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4815_);
if (v_isModule_4816_ == 0)
{
lean_dec_ref(v___y_4813_);
v___y_4761_ = v___y_4812_;
v_exportedInfo_x3f_4762_ = v___x_4713_;
v___y_4763_ = v___y_4811_;
v___y_4764_ = v___y_4810_;
goto v___jp_4760_;
}
else
{
uint8_t v_isExporting_4817_; 
v_isExporting_4817_ = lean_ctor_get_uint8(v___y_4813_, sizeof(void*)*8);
lean_dec_ref(v___y_4813_);
if (v_isExporting_4817_ == 0)
{
v___y_4793_ = v___y_4811_;
v___y_4794_ = v___y_4812_;
v___y_4795_ = v___y_4810_;
goto v___jp_4792_;
}
else
{
if (v___x_4523_ == 0)
{
v___y_4761_ = v___y_4812_;
v_exportedInfo_x3f_4762_ = v___x_4713_;
v___y_4763_ = v___y_4811_;
v___y_4764_ = v___y_4810_;
goto v___jp_4760_;
}
else
{
v___y_4793_ = v___y_4811_;
v___y_4794_ = v___y_4812_;
v___y_4795_ = v___y_4810_;
goto v___jp_4792_;
}
}
}
}
v___jp_4818_:
{
lean_object* v___x_4822_; lean_object* v___x_4823_; 
v___x_4822_ = lean_st_ref_get(v___y_4821_);
v___x_4823_ = lean_st_ref_get(v___y_4821_);
if (v_forceExpose_3823_ == 0)
{
lean_object* v_env_4824_; lean_object* v_env_4825_; 
v_env_4824_ = lean_ctor_get(v___x_4822_, 0);
lean_inc_ref(v_env_4824_);
lean_dec(v___x_4822_);
v_env_4825_ = lean_ctor_get(v___x_4823_, 0);
lean_inc_ref(v_env_4825_);
lean_dec(v___x_4823_);
v___y_4810_ = v___y_4821_;
v___y_4811_ = v___y_4820_;
v___y_4812_ = v_defn_4819_;
v___y_4813_ = v_env_4825_;
v___y_4814_ = v_env_4824_;
goto v___jp_4809_;
}
else
{
if (v___x_4523_ == 0)
{
lean_dec(v___x_4823_);
lean_dec(v___x_4822_);
v___y_4761_ = v_defn_4819_;
v_exportedInfo_x3f_4762_ = v___x_4713_;
v___y_4763_ = v___y_4820_;
v___y_4764_ = v___y_4821_;
goto v___jp_4760_;
}
else
{
lean_object* v_env_4826_; lean_object* v_env_4827_; 
v_env_4826_ = lean_ctor_get(v___x_4822_, 0);
lean_inc_ref(v_env_4826_);
lean_dec(v___x_4822_);
v_env_4827_ = lean_ctor_get(v___x_4823_, 0);
lean_inc_ref(v_env_4827_);
lean_dec(v___x_4823_);
v___y_4810_ = v___y_4821_;
v___y_4811_ = v___y_4820_;
v___y_4812_ = v_defn_4819_;
v___y_4813_ = v_env_4827_;
v___y_4814_ = v_env_4826_;
goto v___jp_4809_;
}
}
}
}
}
}
else
{
goto v___jp_4370_;
}
v___jp_4524_:
{
lean_object* v___x_4535_; 
lean_inc_ref(v___y_4531_);
v___x_4535_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_4525_, v___y_4531_, v___y_4529_, v___y_4534_);
if (lean_obj_tag(v___x_4535_) == 0)
{
lean_object* v___x_4536_; lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4582_; 
lean_dec_ref_known(v___x_4535_, 1);
lean_inc_ref(v___y_4527_);
v___x_4536_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4527_, v___y_4528_);
v_isSharedCheck_4582_ = !lean_is_exclusive(v___x_4536_);
if (v_isSharedCheck_4582_ == 0)
{
lean_object* v_unused_4583_; 
v_unused_4583_ = lean_ctor_get(v___x_4536_, 0);
lean_dec(v_unused_4583_);
v___x_4538_ = v___x_4536_;
v_isShared_4539_ = v_isSharedCheck_4582_;
goto v_resetjp_4537_;
}
else
{
lean_dec(v___x_4536_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4582_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
lean_object* v_options_4540_; lean_object* v___x_4541_; uint8_t v___x_4542_; 
v_options_4540_ = lean_ctor_get(v___y_4526_, 2);
v___x_4541_ = l_Lean_Elab_async;
v___x_4542_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_4540_, v___x_4541_);
if (v___x_4542_ == 0)
{
lean_object* v___x_4543_; lean_object* v_r_4544_; 
lean_del_object(v___x_4538_);
lean_dec_ref(v___y_4533_);
lean_dec_ref(v___y_4532_);
v___x_4543_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4531_, v___y_4528_);
lean_dec_ref(v___x_4543_);
v_r_4544_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3822_, v___y_4526_, v___y_4528_);
if (lean_obj_tag(v_r_4544_) == 0)
{
lean_object* v_a_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4554_; 
v_a_4545_ = lean_ctor_get(v_r_4544_, 0);
v_isSharedCheck_4554_ = !lean_is_exclusive(v_r_4544_);
if (v_isSharedCheck_4554_ == 0)
{
v___x_4547_ = v_r_4544_;
v_isShared_4548_ = v_isSharedCheck_4554_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_a_4545_);
lean_dec(v_r_4544_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4554_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
lean_object* v___x_4550_; 
lean_inc(v_a_4545_);
if (v_isShared_4548_ == 0)
{
lean_ctor_set_tag(v___x_4547_, 1);
v___x_4550_ = v___x_4547_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v_a_4545_);
v___x_4550_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
lean_object* v___x_4551_; 
v___x_4551_ = lean_apply_2(v___y_4530_, v___x_4550_, lean_box(0));
if (lean_obj_tag(v___x_4551_) == 0)
{
lean_dec_ref_known(v___x_4551_, 1);
v___y_3828_ = v___y_4527_;
v___y_3829_ = v___y_4528_;
v_a_3830_ = v_a_4545_;
goto v___jp_3827_;
}
else
{
lean_object* v_a_4552_; 
lean_dec(v_a_4545_);
v_a_4552_ = lean_ctor_get(v___x_4551_, 0);
lean_inc(v_a_4552_);
lean_dec_ref_known(v___x_4551_, 1);
v___y_3841_ = v___y_4527_;
v___y_3842_ = v___y_4528_;
v_a_3843_ = v_a_4552_;
goto v___jp_3840_;
}
}
}
}
else
{
lean_object* v_a_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; 
v_a_4555_ = lean_ctor_get(v_r_4544_, 0);
lean_inc(v_a_4555_);
lean_dec_ref_known(v_r_4544_, 1);
v___x_4556_ = lean_box(0);
v___x_4557_ = lean_apply_2(v___y_4530_, v___x_4556_, lean_box(0));
if (lean_obj_tag(v___x_4557_) == 0)
{
lean_dec_ref_known(v___x_4557_, 1);
v___y_3841_ = v___y_4527_;
v___y_3842_ = v___y_4528_;
v_a_3843_ = v_a_4555_;
goto v___jp_3840_;
}
else
{
lean_object* v_a_4558_; 
lean_dec(v_a_4555_);
v_a_4558_ = lean_ctor_get(v___x_4557_, 0);
lean_inc(v_a_4558_);
lean_dec_ref_known(v___x_4557_, 1);
v___y_3841_ = v___y_4527_;
v___y_3842_ = v___y_4528_;
v_a_3843_ = v_a_4558_;
goto v___jp_3840_;
}
}
}
else
{
lean_object* v___x_4559_; lean_object* v___x_4561_; 
lean_dec_ref(v___y_4531_);
lean_dec_ref(v___y_4530_);
lean_dec_ref(v___y_4527_);
lean_dec(v_decl_3822_);
v___x_4559_ = l_IO_CancelToken_new();
if (v_isShared_4539_ == 0)
{
lean_ctor_set_tag(v___x_4538_, 1);
lean_ctor_set(v___x_4538_, 0, v___x_4559_);
v___x_4561_ = v___x_4538_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v___x_4559_);
v___x_4561_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; 
v___x_4562_ = lean_unsigned_to_nat(0u);
v___x_4563_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_4564_ = l_Lean_Name_toString(v___x_4563_, v_hasTrace_3881_);
lean_inc_ref(v___x_4561_);
v___x_4565_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_4533_, v___x_4561_, v___x_4564_, v___y_4526_, v___y_4528_);
if (lean_obj_tag(v___x_4565_) == 0)
{
lean_object* v_a_4566_; lean_object* v_checked_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; 
v_a_4566_ = lean_ctor_get(v___x_4565_, 0);
lean_inc(v_a_4566_);
lean_dec_ref_known(v___x_4565_, 1);
v_checked_4567_ = lean_ctor_get(v___y_4532_, 2);
lean_inc_ref(v_checked_4567_);
lean_dec_ref(v___y_4532_);
v___x_4568_ = lean_io_map_task(v_a_4566_, v_checked_4567_, v___x_4562_, v___x_4523_);
v___x_4569_ = lean_box(0);
v___x_4570_ = lean_box(2);
v___x_4571_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4571_, 0, v___x_4569_);
lean_ctor_set(v___x_4571_, 1, v___x_4570_);
lean_ctor_set(v___x_4571_, 2, v___x_4561_);
lean_ctor_set(v___x_4571_, 3, v___x_4568_);
v___x_4572_ = l_Lean_Core_logSnapshotTask___redArg(v___x_4571_, v___y_4528_);
return v___x_4572_;
}
else
{
lean_object* v_a_4573_; lean_object* v___x_4575_; uint8_t v_isShared_4576_; uint8_t v_isSharedCheck_4580_; 
lean_dec_ref(v___x_4561_);
lean_dec_ref(v___y_4532_);
v_a_4573_ = lean_ctor_get(v___x_4565_, 0);
v_isSharedCheck_4580_ = !lean_is_exclusive(v___x_4565_);
if (v_isSharedCheck_4580_ == 0)
{
v___x_4575_ = v___x_4565_;
v_isShared_4576_ = v_isSharedCheck_4580_;
goto v_resetjp_4574_;
}
else
{
lean_inc(v_a_4573_);
lean_dec(v___x_4565_);
v___x_4575_ = lean_box(0);
v_isShared_4576_ = v_isSharedCheck_4580_;
goto v_resetjp_4574_;
}
v_resetjp_4574_:
{
lean_object* v___x_4578_; 
if (v_isShared_4576_ == 0)
{
v___x_4578_ = v___x_4575_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4579_; 
v_reuseFailAlloc_4579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4579_, 0, v_a_4573_);
v___x_4578_ = v_reuseFailAlloc_4579_;
goto v_reusejp_4577_;
}
v_reusejp_4577_:
{
return v___x_4578_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4596_; 
lean_dec_ref(v___y_4533_);
lean_dec_ref(v___y_4532_);
lean_dec_ref(v___y_4531_);
lean_dec_ref(v___y_4530_);
lean_dec_ref(v___y_4527_);
lean_dec(v_decl_3822_);
v_a_4584_ = lean_ctor_get(v___x_4535_, 0);
v_isSharedCheck_4596_ = !lean_is_exclusive(v___x_4535_);
if (v_isSharedCheck_4596_ == 0)
{
v___x_4586_ = v___x_4535_;
v_isShared_4587_ = v_isSharedCheck_4596_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_a_4584_);
lean_dec(v___x_4535_);
v___x_4586_ = lean_box(0);
v_isShared_4587_ = v_isSharedCheck_4596_;
goto v_resetjp_4585_;
}
v_resetjp_4585_:
{
lean_object* v_ref_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4594_; 
v_ref_4588_ = lean_ctor_get(v___y_4526_, 5);
v___x_4589_ = lean_io_error_to_string(v_a_4584_);
v___x_4590_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4590_, 0, v___x_4589_);
v___x_4591_ = l_Lean_MessageData_ofFormat(v___x_4590_);
lean_inc(v_ref_4588_);
v___x_4592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4592_, 0, v_ref_4588_);
lean_ctor_set(v___x_4592_, 1, v___x_4591_);
if (v_isShared_4587_ == 0)
{
lean_ctor_set(v___x_4586_, 0, v___x_4592_);
v___x_4594_ = v___x_4586_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4595_; 
v_reuseFailAlloc_4595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4595_, 0, v___x_4592_);
v___x_4594_ = v_reuseFailAlloc_4595_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
return v___x_4594_;
}
}
}
}
v___jp_4597_:
{
lean_object* v___x_4608_; 
lean_inc_ref(v___y_4600_);
v___x_4608_ = l_Lean_Environment_addConstAsync(v___y_4600_, v___y_4605_, v___y_4601_, v___y_4607_, v___x_4523_, v_hasTrace_3881_);
if (lean_obj_tag(v___x_4608_) == 0)
{
lean_object* v_a_4609_; lean_object* v_mainEnv_4610_; lean_object* v_asyncEnv_4611_; lean_object* v___f_4612_; lean_object* v___f_4613_; lean_object* v___x_4614_; 
v_a_4609_ = lean_ctor_get(v___x_4608_, 0);
lean_inc_n(v_a_4609_, 3);
lean_dec_ref_known(v___x_4608_, 1);
v_mainEnv_4610_ = lean_ctor_get(v_a_4609_, 0);
lean_inc_ref(v_mainEnv_4610_);
v_asyncEnv_4611_ = lean_ctor_get(v_a_4609_, 1);
lean_inc_ref_n(v_asyncEnv_4611_, 2);
lean_inc_ref(v___y_4598_);
lean_inc(v___y_4599_);
v___f_4612_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4612_, 0, v___y_4599_);
lean_closure_set(v___f_4612_, 1, v_a_4609_);
lean_closure_set(v___f_4612_, 2, v___y_4598_);
lean_inc(v_decl_3822_);
v___f_4613_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4613_, 0, v_asyncEnv_4611_);
lean_closure_set(v___f_4613_, 1, v_a_4609_);
lean_closure_set(v___f_4613_, 2, v_decl_3822_);
v___x_4614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4614_, 0, v___y_4604_);
if (lean_obj_tag(v___y_4606_) == 0)
{
lean_inc_ref(v___x_4614_);
v___y_4525_ = v_a_4609_;
v___y_4526_ = v___y_4602_;
v___y_4527_ = v_mainEnv_4610_;
v___y_4528_ = v___y_4603_;
v___y_4529_ = v___x_4614_;
v___y_4530_ = v___f_4612_;
v___y_4531_ = v_asyncEnv_4611_;
v___y_4532_ = v___y_4600_;
v___y_4533_ = v___f_4613_;
v___y_4534_ = v___x_4614_;
goto v___jp_4524_;
}
else
{
v___y_4525_ = v_a_4609_;
v___y_4526_ = v___y_4602_;
v___y_4527_ = v_mainEnv_4610_;
v___y_4528_ = v___y_4603_;
v___y_4529_ = v___x_4614_;
v___y_4530_ = v___f_4612_;
v___y_4531_ = v_asyncEnv_4611_;
v___y_4532_ = v___y_4600_;
v___y_4533_ = v___f_4613_;
v___y_4534_ = v___y_4606_;
goto v___jp_4524_;
}
}
else
{
lean_object* v_a_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4627_; 
lean_dec(v___y_4606_);
lean_dec_ref(v___y_4604_);
lean_dec_ref(v___y_4600_);
lean_dec(v_decl_3822_);
v_a_4615_ = lean_ctor_get(v___x_4608_, 0);
v_isSharedCheck_4627_ = !lean_is_exclusive(v___x_4608_);
if (v_isSharedCheck_4627_ == 0)
{
v___x_4617_ = v___x_4608_;
v_isShared_4618_ = v_isSharedCheck_4627_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_a_4615_);
lean_dec(v___x_4608_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4627_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v_ref_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4625_; 
v_ref_4619_ = lean_ctor_get(v___y_4602_, 5);
v___x_4620_ = lean_io_error_to_string(v_a_4615_);
v___x_4621_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4621_, 0, v___x_4620_);
v___x_4622_ = l_Lean_MessageData_ofFormat(v___x_4621_);
lean_inc(v_ref_4619_);
v___x_4623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4623_, 0, v_ref_4619_);
lean_ctor_set(v___x_4623_, 1, v___x_4622_);
if (v_isShared_4618_ == 0)
{
lean_ctor_set(v___x_4617_, 0, v___x_4623_);
v___x_4625_ = v___x_4617_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v___x_4623_);
v___x_4625_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
return v___x_4625_;
}
}
}
}
v___jp_4628_:
{
lean_object* v___x_4635_; 
v___x_4635_ = lean_st_ref_get(v___y_4634_);
if (lean_obj_tag(v_exportedInfo_x3f_4632_) == 0)
{
lean_object* v_env_4636_; lean_object* v___x_4637_; 
v_env_4636_ = lean_ctor_get(v___x_4635_, 0);
lean_inc_ref(v_env_4636_);
lean_dec(v___x_4635_);
v___x_4637_ = lean_box(0);
v___y_4598_ = v___y_4633_;
v___y_4599_ = v___y_4634_;
v___y_4600_ = v_env_4636_;
v___y_4601_ = v___y_4629_;
v___y_4602_ = v___y_4633_;
v___y_4603_ = v___y_4634_;
v___y_4604_ = v___y_4630_;
v___y_4605_ = v___y_4631_;
v___y_4606_ = v_exportedInfo_x3f_4632_;
v___y_4607_ = v___x_4637_;
goto v___jp_4597_;
}
else
{
lean_object* v_env_4638_; lean_object* v_val_4639_; uint8_t v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; 
v_env_4638_ = lean_ctor_get(v___x_4635_, 0);
lean_inc_ref(v_env_4638_);
lean_dec(v___x_4635_);
v_val_4639_ = lean_ctor_get(v_exportedInfo_x3f_4632_, 0);
v___x_4640_ = l_Lean_ConstantKind_ofConstantInfo(v_val_4639_);
v___x_4641_ = lean_box(v___x_4640_);
v___x_4642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4642_, 0, v___x_4641_);
v___y_4598_ = v___y_4633_;
v___y_4599_ = v___y_4634_;
v___y_4600_ = v_env_4638_;
v___y_4601_ = v___y_4629_;
v___y_4602_ = v___y_4633_;
v___y_4603_ = v___y_4634_;
v___y_4604_ = v___y_4630_;
v___y_4605_ = v___y_4631_;
v___y_4606_ = v_exportedInfo_x3f_4632_;
v___y_4607_ = v___x_4642_;
goto v___jp_4597_;
}
}
v___jp_4643_:
{
lean_object* v___x_4649_; 
lean_inc_ref(v___y_4645_);
v___x_4649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4649_, 0, v___y_4645_);
v___y_4629_ = v___y_4644_;
v___y_4630_ = v___y_4645_;
v___y_4631_ = v___y_4646_;
v_exportedInfo_x3f_4632_ = v___x_4649_;
v___y_4633_ = v___y_4647_;
v___y_4634_ = v___y_4648_;
goto v___jp_4628_;
}
v___jp_4650_:
{
lean_object* v___x_4656_; 
lean_inc_ref(v___y_4652_);
v___x_4656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4656_, 0, v___y_4652_);
v___y_4629_ = v___y_4651_;
v___y_4630_ = v___y_4652_;
v___y_4631_ = v___y_4653_;
v_exportedInfo_x3f_4632_ = v___x_4656_;
v___y_4633_ = v___y_4654_;
v___y_4634_ = v___y_4655_;
goto v___jp_4628_;
}
}
else
{
goto v___jp_4370_;
}
v___jp_4223_:
{
lean_object* v___x_4227_; double v___x_4228_; double v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; 
v___x_4227_ = lean_io_get_num_heartbeats();
v___x_4228_ = lean_float_of_nat(v___y_4224_);
v___x_4229_ = lean_float_of_nat(v___x_4227_);
v___x_4230_ = lean_box_float(v___x_4228_);
v___x_4231_ = lean_box_float(v___x_4229_);
v___x_4232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4232_, 0, v___x_4230_);
lean_ctor_set(v___x_4232_, 1, v___x_4231_);
v___x_4233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4233_, 0, v_a_4226_);
lean_ctor_set(v___x_4233_, 1, v___x_4232_);
v___x_4234_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_4017_, v_hasTrace_3881_, v___x_4220_, v_options_3879_, v___x_4222_, v___y_4225_, v___f_4219_, v___x_4233_, v_a_3824_, v_a_3825_);
return v___x_4234_;
}
v___jp_4235_:
{
if (lean_obj_tag(v___y_4238_) == 0)
{
lean_object* v_a_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4246_; 
v_a_4239_ = lean_ctor_get(v___y_4238_, 0);
v_isSharedCheck_4246_ = !lean_is_exclusive(v___y_4238_);
if (v_isSharedCheck_4246_ == 0)
{
v___x_4241_ = v___y_4238_;
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_a_4239_);
lean_dec(v___y_4238_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
lean_object* v___x_4244_; 
if (v_isShared_4242_ == 0)
{
lean_ctor_set_tag(v___x_4241_, 1);
v___x_4244_ = v___x_4241_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_a_4239_);
v___x_4244_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
v___y_4224_ = v___y_4236_;
v___y_4225_ = v___y_4237_;
v_a_4226_ = v___x_4244_;
goto v___jp_4223_;
}
}
}
else
{
lean_object* v_a_4247_; lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4254_; 
v_a_4247_ = lean_ctor_get(v___y_4238_, 0);
v_isSharedCheck_4254_ = !lean_is_exclusive(v___y_4238_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4249_ = v___y_4238_;
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_a_4247_);
lean_dec(v___y_4238_);
v___x_4249_ = lean_box(0);
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
v_resetjp_4248_:
{
lean_object* v___x_4252_; 
if (v_isShared_4250_ == 0)
{
lean_ctor_set_tag(v___x_4249_, 0);
v___x_4252_ = v___x_4249_;
goto v_reusejp_4251_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_a_4247_);
v___x_4252_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4251_;
}
v_reusejp_4251_:
{
v___y_4224_ = v___y_4236_;
v___y_4225_ = v___y_4237_;
v_a_4226_ = v___x_4252_;
goto v___jp_4223_;
}
}
}
}
v___jp_4255_:
{
lean_object* v___x_4260_; lean_object* v___x_4261_; 
v___x_4260_ = lean_box(0);
lean_inc(v_a_3825_);
lean_inc_ref(v_a_3824_);
v___x_4261_ = lean_apply_5(v___y_4256_, v___x_4260_, v___y_4259_, v_a_3824_, v_a_3825_, lean_box(0));
v___y_4236_ = v___y_4257_;
v___y_4237_ = v___y_4258_;
v___y_4238_ = v___x_4261_;
goto v___jp_4235_;
}
v___jp_4262_:
{
lean_object* v___x_4267_; lean_object* v___x_4268_; 
v___x_4267_ = lean_box(0);
lean_inc(v_a_3825_);
lean_inc_ref(v_a_3824_);
v___x_4268_ = lean_apply_5(v___y_4265_, v___x_4267_, v___y_4266_, v_a_3824_, v_a_3825_, lean_box(0));
v___y_4236_ = v___y_4263_;
v___y_4237_ = v___y_4264_;
v___y_4238_ = v___x_4268_;
goto v___jp_4235_;
}
v___jp_4269_:
{
lean_object* v___x_4273_; double v___x_4274_; double v___x_4275_; double v___x_4276_; double v___x_4277_; double v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; 
v___x_4273_ = lean_io_mono_nanos_now();
v___x_4274_ = lean_float_of_nat(v___y_4270_);
v___x_4275_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_4276_ = lean_float_div(v___x_4274_, v___x_4275_);
v___x_4277_ = lean_float_of_nat(v___x_4273_);
v___x_4278_ = lean_float_div(v___x_4277_, v___x_4275_);
v___x_4279_ = lean_box_float(v___x_4276_);
v___x_4280_ = lean_box_float(v___x_4278_);
v___x_4281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4281_, 0, v___x_4279_);
lean_ctor_set(v___x_4281_, 1, v___x_4280_);
v___x_4282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4282_, 0, v_a_4272_);
lean_ctor_set(v___x_4282_, 1, v___x_4281_);
v___x_4283_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_4017_, v_hasTrace_3881_, v___x_4220_, v_options_3879_, v___x_4222_, v___y_4271_, v___f_4219_, v___x_4282_, v_a_3824_, v_a_3825_);
return v___x_4283_;
}
v___jp_4284_:
{
if (lean_obj_tag(v___y_4287_) == 0)
{
lean_object* v_a_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4295_; 
v_a_4288_ = lean_ctor_get(v___y_4287_, 0);
v_isSharedCheck_4295_ = !lean_is_exclusive(v___y_4287_);
if (v_isSharedCheck_4295_ == 0)
{
v___x_4290_ = v___y_4287_;
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_a_4288_);
lean_dec(v___y_4287_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
lean_object* v___x_4293_; 
if (v_isShared_4291_ == 0)
{
lean_ctor_set_tag(v___x_4290_, 1);
v___x_4293_ = v___x_4290_;
goto v_reusejp_4292_;
}
else
{
lean_object* v_reuseFailAlloc_4294_; 
v_reuseFailAlloc_4294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4294_, 0, v_a_4288_);
v___x_4293_ = v_reuseFailAlloc_4294_;
goto v_reusejp_4292_;
}
v_reusejp_4292_:
{
v___y_4270_ = v___y_4285_;
v___y_4271_ = v___y_4286_;
v_a_4272_ = v___x_4293_;
goto v___jp_4269_;
}
}
}
else
{
lean_object* v_a_4296_; lean_object* v___x_4298_; uint8_t v_isShared_4299_; uint8_t v_isSharedCheck_4303_; 
v_a_4296_ = lean_ctor_get(v___y_4287_, 0);
v_isSharedCheck_4303_ = !lean_is_exclusive(v___y_4287_);
if (v_isSharedCheck_4303_ == 0)
{
v___x_4298_ = v___y_4287_;
v_isShared_4299_ = v_isSharedCheck_4303_;
goto v_resetjp_4297_;
}
else
{
lean_inc(v_a_4296_);
lean_dec(v___y_4287_);
v___x_4298_ = lean_box(0);
v_isShared_4299_ = v_isSharedCheck_4303_;
goto v_resetjp_4297_;
}
v_resetjp_4297_:
{
lean_object* v___x_4301_; 
if (v_isShared_4299_ == 0)
{
lean_ctor_set_tag(v___x_4298_, 0);
v___x_4301_ = v___x_4298_;
goto v_reusejp_4300_;
}
else
{
lean_object* v_reuseFailAlloc_4302_; 
v_reuseFailAlloc_4302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4302_, 0, v_a_4296_);
v___x_4301_ = v_reuseFailAlloc_4302_;
goto v_reusejp_4300_;
}
v_reusejp_4300_:
{
v___y_4270_ = v___y_4285_;
v___y_4271_ = v___y_4286_;
v_a_4272_ = v___x_4301_;
goto v___jp_4269_;
}
}
}
}
v___jp_4304_:
{
lean_object* v___x_4309_; lean_object* v___x_4310_; 
v___x_4309_ = lean_box(0);
lean_inc(v_a_3825_);
lean_inc_ref(v_a_3824_);
v___x_4310_ = lean_apply_5(v___y_4305_, v___x_4309_, v___y_4307_, v_a_3824_, v_a_3825_, lean_box(0));
v___y_4285_ = v___y_4306_;
v___y_4286_ = v___y_4308_;
v___y_4287_ = v___x_4310_;
goto v___jp_4284_;
}
v___jp_4311_:
{
if (v___x_4222_ == 0)
{
lean_object* v___x_4316_; lean_object* v___x_4317_; 
lean_dec_ref(v___y_4313_);
v___x_4316_ = lean_box(0);
lean_inc(v_a_3825_);
lean_inc_ref(v_a_3824_);
v___x_4317_ = lean_apply_4(v___y_4314_, v___x_4316_, v_a_3824_, v_a_3825_, lean_box(0));
v___y_4285_ = v___y_4312_;
v___y_4286_ = v___y_4315_;
v___y_4287_ = v___x_4317_;
goto v___jp_4284_;
}
else
{
lean_object* v_toConstantVal_4318_; lean_object* v_name_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; 
v_toConstantVal_4318_ = lean_ctor_get(v___y_4313_, 0);
lean_inc_ref(v_toConstantVal_4318_);
lean_dec_ref(v___y_4313_);
v_name_4319_ = lean_ctor_get(v_toConstantVal_4318_, 0);
lean_inc(v_name_4319_);
lean_dec_ref(v_toConstantVal_4318_);
v___x_4320_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
v___x_4321_ = l_Lean_MessageData_ofName(v_name_4319_);
v___x_4322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4322_, 0, v___x_4320_);
lean_ctor_set(v___x_4322_, 1, v___x_4321_);
v___x_4323_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4324_, 0, v___x_4322_);
lean_ctor_set(v___x_4324_, 1, v___x_4323_);
v___x_4325_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4017_, v___x_4324_, v_a_3824_, v_a_3825_);
if (lean_obj_tag(v___x_4325_) == 0)
{
lean_object* v_a_4326_; lean_object* v___x_4327_; 
v_a_4326_ = lean_ctor_get(v___x_4325_, 0);
lean_inc(v_a_4326_);
lean_dec_ref_known(v___x_4325_, 1);
lean_inc(v_a_3825_);
lean_inc_ref(v_a_3824_);
v___x_4327_ = lean_apply_4(v___y_4314_, v_a_4326_, v_a_3824_, v_a_3825_, lean_box(0));
v___y_4285_ = v___y_4312_;
v___y_4286_ = v___y_4315_;
v___y_4287_ = v___x_4327_;
goto v___jp_4284_;
}
else
{
lean_dec_ref(v___y_4314_);
v___y_4285_ = v___y_4312_;
v___y_4286_ = v___y_4315_;
v___y_4287_ = v___x_4325_;
goto v___jp_4284_;
}
}
}
v___jp_4328_:
{
lean_object* v___x_4338_; uint8_t v_isModule_4339_; 
v___x_4338_ = l_Lean_Environment_header(v___y_4329_);
lean_dec_ref(v___y_4329_);
v_isModule_4339_ = lean_ctor_get_uint8(v___x_4338_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4338_);
if (v_isModule_4339_ == 0)
{
lean_dec_ref(v___y_4335_);
lean_dec_ref(v___y_4334_);
lean_dec_ref(v___y_4333_);
v___y_4305_ = v___y_4330_;
v___y_4306_ = v___y_4331_;
v___y_4307_ = v___y_4332_;
v___y_4308_ = v___y_4336_;
goto v___jp_4304_;
}
else
{
uint8_t v_isExporting_4340_; 
v_isExporting_4340_ = lean_ctor_get_uint8(v___y_4333_, sizeof(void*)*8);
lean_dec_ref(v___y_4333_);
if (v_isExporting_4340_ == 0)
{
lean_dec(v___y_4332_);
lean_dec_ref(v___y_4330_);
v___y_4312_ = v___y_4331_;
v___y_4313_ = v___y_4334_;
v___y_4314_ = v___y_4335_;
v___y_4315_ = v___y_4336_;
goto v___jp_4311_;
}
else
{
if (v___y_4337_ == 0)
{
lean_dec_ref(v___y_4335_);
lean_dec_ref(v___y_4334_);
v___y_4305_ = v___y_4330_;
v___y_4306_ = v___y_4331_;
v___y_4307_ = v___y_4332_;
v___y_4308_ = v___y_4336_;
goto v___jp_4304_;
}
else
{
lean_dec(v___y_4332_);
lean_dec_ref(v___y_4330_);
v___y_4312_ = v___y_4331_;
v___y_4313_ = v___y_4334_;
v___y_4314_ = v___y_4335_;
v___y_4315_ = v___y_4336_;
goto v___jp_4311_;
}
}
}
}
v___jp_4341_:
{
lean_object* v___x_4346_; lean_object* v___x_4347_; 
v___x_4346_ = lean_box(0);
lean_inc(v_a_3825_);
lean_inc_ref(v_a_3824_);
v___x_4347_ = lean_apply_5(v___y_4344_, v___x_4346_, v___y_4343_, v_a_3824_, v_a_3825_, lean_box(0));
v___y_4285_ = v___y_4342_;
v___y_4286_ = v___y_4345_;
v___y_4287_ = v___x_4347_;
goto v___jp_4284_;
}
v___jp_4348_:
{
lean_object* v___x_4356_; uint8_t v_isModule_4357_; 
v___x_4356_ = l_Lean_Environment_header(v___y_4352_);
lean_dec_ref(v___y_4352_);
v_isModule_4357_ = lean_ctor_get_uint8(v___x_4356_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4356_);
if (v_isModule_4357_ == 0)
{
lean_dec_ref(v___y_4355_);
lean_dec_ref(v___y_4349_);
v___y_4342_ = v___y_4350_;
v___y_4343_ = v___y_4351_;
v___y_4344_ = v___y_4353_;
v___y_4345_ = v___y_4354_;
goto v___jp_4341_;
}
else
{
lean_dec_ref(v___y_4353_);
lean_dec(v___y_4351_);
if (v___x_4222_ == 0)
{
lean_object* v___x_4358_; lean_object* v___x_4359_; 
lean_dec_ref(v___y_4355_);
v___x_4358_ = lean_box(0);
lean_inc(v_a_3825_);
lean_inc_ref(v_a_3824_);
v___x_4359_ = lean_apply_4(v___y_4349_, v___x_4358_, v_a_3824_, v_a_3825_, lean_box(0));
v___y_4285_ = v___y_4350_;
v___y_4286_ = v___y_4354_;
v___y_4287_ = v___x_4359_;
goto v___jp_4284_;
}
else
{
lean_object* v_toConstantVal_4360_; lean_object* v_name_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v_toConstantVal_4360_ = lean_ctor_get(v___y_4355_, 0);
lean_inc_ref(v_toConstantVal_4360_);
lean_dec_ref(v___y_4355_);
v_name_4361_ = lean_ctor_get(v_toConstantVal_4360_, 0);
lean_inc(v_name_4361_);
lean_dec_ref(v_toConstantVal_4360_);
v___x_4362_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
v___x_4363_ = l_Lean_MessageData_ofName(v_name_4361_);
v___x_4364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4364_, 0, v___x_4362_);
lean_ctor_set(v___x_4364_, 1, v___x_4363_);
v___x_4365_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4366_, 0, v___x_4364_);
lean_ctor_set(v___x_4366_, 1, v___x_4365_);
v___x_4367_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4017_, v___x_4366_, v_a_3824_, v_a_3825_);
if (lean_obj_tag(v___x_4367_) == 0)
{
lean_object* v_a_4368_; lean_object* v___x_4369_; 
v_a_4368_ = lean_ctor_get(v___x_4367_, 0);
lean_inc(v_a_4368_);
lean_dec_ref_known(v___x_4367_, 1);
lean_inc(v_a_3825_);
lean_inc_ref(v_a_3824_);
v___x_4369_ = lean_apply_4(v___y_4349_, v_a_4368_, v_a_3824_, v_a_3825_, lean_box(0));
v___y_4285_ = v___y_4350_;
v___y_4286_ = v___y_4354_;
v___y_4287_ = v___x_4369_;
goto v___jp_4284_;
}
else
{
lean_dec_ref(v___y_4349_);
v___y_4285_ = v___y_4350_;
v___y_4286_ = v___y_4354_;
v___y_4287_ = v___x_4367_;
goto v___jp_4284_;
}
}
}
}
v___jp_4370_:
{
lean_object* v___x_4371_; lean_object* v_a_4372_; lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4521_; 
v___x_4371_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v_a_3825_);
v_a_4372_ = lean_ctor_get(v___x_4371_, 0);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4371_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4374_ = v___x_4371_;
v_isShared_4375_ = v_isSharedCheck_4521_;
goto v_resetjp_4373_;
}
else
{
lean_inc(v_a_4372_);
lean_dec(v___x_4371_);
v___x_4374_ = lean_box(0);
v_isShared_4375_ = v_isSharedCheck_4521_;
goto v_resetjp_4373_;
}
v_resetjp_4373_:
{
lean_object* v___x_4376_; uint8_t v___x_4377_; 
v___x_4376_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4377_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3879_, v___x_4376_);
if (v___x_4377_ == 0)
{
lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v_env_4380_; lean_object* v_nextMacroScope_4381_; lean_object* v_ngen_4382_; lean_object* v_auxDeclNGen_4383_; lean_object* v_traceState_4384_; lean_object* v_messages_4385_; lean_object* v_infoState_4386_; lean_object* v_snapshotTasks_4387_; lean_object* v___x_4389_; uint8_t v_isShared_4390_; uint8_t v_isSharedCheck_4435_; 
v___x_4378_ = lean_io_mono_nanos_now();
v___x_4379_ = lean_st_ref_take(v_a_3825_);
v_env_4380_ = lean_ctor_get(v___x_4379_, 0);
v_nextMacroScope_4381_ = lean_ctor_get(v___x_4379_, 1);
v_ngen_4382_ = lean_ctor_get(v___x_4379_, 2);
v_auxDeclNGen_4383_ = lean_ctor_get(v___x_4379_, 3);
v_traceState_4384_ = lean_ctor_get(v___x_4379_, 4);
v_messages_4385_ = lean_ctor_get(v___x_4379_, 6);
v_infoState_4386_ = lean_ctor_get(v___x_4379_, 7);
v_snapshotTasks_4387_ = lean_ctor_get(v___x_4379_, 8);
v_isSharedCheck_4435_ = !lean_is_exclusive(v___x_4379_);
if (v_isSharedCheck_4435_ == 0)
{
lean_object* v_unused_4436_; 
v_unused_4436_ = lean_ctor_get(v___x_4379_, 5);
lean_dec(v_unused_4436_);
v___x_4389_ = v___x_4379_;
v_isShared_4390_ = v_isSharedCheck_4435_;
goto v_resetjp_4388_;
}
else
{
lean_inc(v_snapshotTasks_4387_);
lean_inc(v_infoState_4386_);
lean_inc(v_messages_4385_);
lean_inc(v_traceState_4384_);
lean_inc(v_auxDeclNGen_4383_);
lean_inc(v_ngen_4382_);
lean_inc(v_nextMacroScope_4381_);
lean_inc(v_env_4380_);
lean_dec(v___x_4379_);
v___x_4389_ = lean_box(0);
v_isShared_4390_ = v_isSharedCheck_4435_;
goto v_resetjp_4388_;
}
v_resetjp_4388_:
{
lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4395_; 
lean_inc(v_decl_3822_);
v___x_4391_ = l_Lean_Declaration_getNames(v_decl_3822_);
v___x_4392_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4380_, v___x_4391_);
v___x_4393_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4390_ == 0)
{
lean_ctor_set(v___x_4389_, 5, v___x_4393_);
lean_ctor_set(v___x_4389_, 0, v___x_4392_);
v___x_4395_ = v___x_4389_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4434_; 
v_reuseFailAlloc_4434_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4434_, 0, v___x_4392_);
lean_ctor_set(v_reuseFailAlloc_4434_, 1, v_nextMacroScope_4381_);
lean_ctor_set(v_reuseFailAlloc_4434_, 2, v_ngen_4382_);
lean_ctor_set(v_reuseFailAlloc_4434_, 3, v_auxDeclNGen_4383_);
lean_ctor_set(v_reuseFailAlloc_4434_, 4, v_traceState_4384_);
lean_ctor_set(v_reuseFailAlloc_4434_, 5, v___x_4393_);
lean_ctor_set(v_reuseFailAlloc_4434_, 6, v_messages_4385_);
lean_ctor_set(v_reuseFailAlloc_4434_, 7, v_infoState_4386_);
lean_ctor_set(v_reuseFailAlloc_4434_, 8, v_snapshotTasks_4387_);
v___x_4395_ = v_reuseFailAlloc_4434_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___f_4400_; 
v___x_4396_ = lean_st_ref_put(v_a_3825_, v___x_4395_);
v___x_4397_ = lean_box(0);
v___x_4398_ = lean_box(v_hasTrace_3881_);
v___x_4399_ = lean_box(v___x_4377_);
lean_inc(v_decl_3822_);
v___f_4400_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed), 11, 6);
lean_closure_set(v___f_4400_, 0, v_decl_3822_);
lean_closure_set(v___f_4400_, 1, v___x_4398_);
lean_closure_set(v___f_4400_, 2, v___x_4399_);
lean_closure_set(v___f_4400_, 3, v___x_4393_);
lean_closure_set(v___f_4400_, 4, v_cls_4017_);
lean_closure_set(v___f_4400_, 5, v___x_4397_);
switch(lean_obj_tag(v_decl_3822_))
{
case 2:
{
lean_object* v_val_4401_; lean_object* v___x_4402_; lean_object* v_env_4403_; lean_object* v___f_4404_; lean_object* v___x_4405_; lean_object* v___f_4406_; 
lean_del_object(v___x_4374_);
v_val_4401_ = lean_ctor_get(v_decl_3822_, 0);
lean_inc_ref_n(v_val_4401_, 3);
lean_dec_ref_known(v_decl_3822_, 1);
v___x_4402_ = lean_st_ref_get(v_a_3825_);
v_env_4403_ = lean_ctor_get(v___x_4402_, 0);
lean_inc_ref(v_env_4403_);
lean_dec(v___x_4402_);
v___f_4404_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed), 7, 2);
lean_closure_set(v___f_4404_, 0, v_val_4401_);
lean_closure_set(v___f_4404_, 1, v___f_4400_);
v___x_4405_ = lean_box(v___x_4377_);
lean_inc_ref(v___f_4404_);
v___f_4406_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed), 7, 3);
lean_closure_set(v___f_4406_, 0, v_val_4401_);
lean_closure_set(v___f_4406_, 1, v___x_4405_);
lean_closure_set(v___f_4406_, 2, v___f_4404_);
if (v_forceExpose_3823_ == 0)
{
v___y_4349_ = v___f_4406_;
v___y_4350_ = v___x_4378_;
v___y_4351_ = v___x_4397_;
v___y_4352_ = v_env_4403_;
v___y_4353_ = v___f_4404_;
v___y_4354_ = v_a_4372_;
v___y_4355_ = v_val_4401_;
goto v___jp_4348_;
}
else
{
if (v___x_4377_ == 0)
{
lean_dec_ref(v___f_4406_);
lean_dec_ref(v_env_4403_);
lean_dec_ref(v_val_4401_);
v___y_4342_ = v___x_4378_;
v___y_4343_ = v___x_4397_;
v___y_4344_ = v___f_4404_;
v___y_4345_ = v_a_4372_;
goto v___jp_4341_;
}
else
{
v___y_4349_ = v___f_4406_;
v___y_4350_ = v___x_4378_;
v___y_4351_ = v___x_4397_;
v___y_4352_ = v_env_4403_;
v___y_4353_ = v___f_4404_;
v___y_4354_ = v_a_4372_;
v___y_4355_ = v_val_4401_;
goto v___jp_4348_;
}
}
}
case 1:
{
lean_object* v_val_4407_; lean_object* v___x_4408_; 
lean_del_object(v___x_4374_);
v_val_4407_ = lean_ctor_get(v_decl_3822_, 0);
lean_inc_ref(v_val_4407_);
lean_dec_ref_known(v_decl_3822_, 1);
v___x_4408_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v___f_4400_, v_hasTrace_3881_, v___x_4377_, v_cls_4017_, v___x_4397_, v_forceExpose_3823_, v_val_4407_, v_a_3824_, v_a_3825_);
v___y_4285_ = v___x_4378_;
v___y_4286_ = v_a_4372_;
v___y_4287_ = v___x_4408_;
goto v___jp_4284_;
}
case 5:
{
lean_object* v_defns_4409_; 
lean_del_object(v___x_4374_);
v_defns_4409_ = lean_ctor_get(v_decl_3822_, 0);
if (lean_obj_tag(v_defns_4409_) == 1)
{
lean_object* v_tail_4410_; 
v_tail_4410_ = lean_ctor_get(v_defns_4409_, 1);
if (lean_obj_tag(v_tail_4410_) == 0)
{
lean_object* v_head_4411_; lean_object* v___x_4412_; 
lean_inc_ref(v_defns_4409_);
lean_dec_ref_known(v_decl_3822_, 1);
v_head_4411_ = lean_ctor_get(v_defns_4409_, 0);
lean_inc(v_head_4411_);
lean_dec_ref_known(v_defns_4409_, 2);
v___x_4412_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v___f_4400_, v_hasTrace_3881_, v___x_4377_, v_cls_4017_, v___x_4397_, v_forceExpose_3823_, v_head_4411_, v_a_3824_, v_a_3825_);
v___y_4285_ = v___x_4378_;
v___y_4286_ = v_a_4372_;
v___y_4287_ = v___x_4412_;
goto v___jp_4284_;
}
else
{
lean_object* v___x_4413_; 
lean_dec_ref(v___f_4400_);
lean_inc_ref(v_decl_3822_);
v___x_4413_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3822_, v_cls_4017_, v_decl_3822_, v_a_3824_, v_a_3825_);
lean_dec_ref_known(v_decl_3822_, 1);
v___y_4285_ = v___x_4378_;
v___y_4286_ = v_a_4372_;
v___y_4287_ = v___x_4413_;
goto v___jp_4284_;
}
}
else
{
lean_object* v___x_4414_; 
lean_dec_ref(v___f_4400_);
lean_inc_ref(v_decl_3822_);
v___x_4414_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3822_, v_cls_4017_, v_decl_3822_, v_a_3824_, v_a_3825_);
lean_dec_ref_known(v_decl_3822_, 1);
v___y_4285_ = v___x_4378_;
v___y_4286_ = v_a_4372_;
v___y_4287_ = v___x_4414_;
goto v___jp_4284_;
}
}
case 3:
{
lean_object* v_val_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v_env_4418_; lean_object* v_env_4419_; lean_object* v___f_4420_; lean_object* v___f_4421_; 
lean_del_object(v___x_4374_);
v_val_4415_ = lean_ctor_get(v_decl_3822_, 0);
lean_inc_ref_n(v_val_4415_, 3);
lean_dec_ref_known(v_decl_3822_, 1);
v___x_4416_ = lean_st_ref_get(v_a_3825_);
v___x_4417_ = lean_st_ref_get(v_a_3825_);
v_env_4418_ = lean_ctor_get(v___x_4416_, 0);
lean_inc_ref(v_env_4418_);
lean_dec(v___x_4416_);
v_env_4419_ = lean_ctor_get(v___x_4417_, 0);
lean_inc_ref(v_env_4419_);
lean_dec(v___x_4417_);
v___f_4420_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed), 7, 2);
lean_closure_set(v___f_4420_, 0, v_val_4415_);
lean_closure_set(v___f_4420_, 1, v___f_4400_);
lean_inc_ref(v___f_4420_);
v___f_4421_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed), 6, 2);
lean_closure_set(v___f_4421_, 0, v_val_4415_);
lean_closure_set(v___f_4421_, 1, v___f_4420_);
if (v_forceExpose_3823_ == 0)
{
v___y_4329_ = v_env_4418_;
v___y_4330_ = v___f_4420_;
v___y_4331_ = v___x_4378_;
v___y_4332_ = v___x_4397_;
v___y_4333_ = v_env_4419_;
v___y_4334_ = v_val_4415_;
v___y_4335_ = v___f_4421_;
v___y_4336_ = v_a_4372_;
v___y_4337_ = v___x_4377_;
goto v___jp_4328_;
}
else
{
if (v___x_4377_ == 0)
{
lean_dec_ref(v___f_4421_);
lean_dec_ref(v_env_4419_);
lean_dec_ref(v_env_4418_);
lean_dec_ref(v_val_4415_);
v___y_4305_ = v___f_4420_;
v___y_4306_ = v___x_4378_;
v___y_4307_ = v___x_4397_;
v___y_4308_ = v_a_4372_;
goto v___jp_4304_;
}
else
{
v___y_4329_ = v_env_4418_;
v___y_4330_ = v___f_4420_;
v___y_4331_ = v___x_4378_;
v___y_4332_ = v___x_4397_;
v___y_4333_ = v_env_4419_;
v___y_4334_ = v_val_4415_;
v___y_4335_ = v___f_4421_;
v___y_4336_ = v_a_4372_;
v___y_4337_ = v___x_4377_;
goto v___jp_4328_;
}
}
}
case 0:
{
lean_object* v_val_4422_; lean_object* v_toConstantVal_4423_; lean_object* v_name_4424_; lean_object* v___x_4426_; 
lean_dec_ref(v___f_4400_);
v_val_4422_ = lean_ctor_get(v_decl_3822_, 0);
v_toConstantVal_4423_ = lean_ctor_get(v_val_4422_, 0);
v_name_4424_ = lean_ctor_get(v_toConstantVal_4423_, 0);
lean_inc_ref(v_val_4422_);
if (v_isShared_4375_ == 0)
{
lean_ctor_set(v___x_4374_, 0, v_val_4422_);
v___x_4426_ = v___x_4374_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v_val_4422_);
v___x_4426_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
uint8_t v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; 
v___x_4427_ = 2;
v___x_4428_ = lean_box(v___x_4427_);
v___x_4429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4429_, 0, v___x_4426_);
lean_ctor_set(v___x_4429_, 1, v___x_4428_);
lean_inc(v_name_4424_);
v___x_4430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4430_, 0, v_name_4424_);
lean_ctor_set(v___x_4430_, 1, v___x_4429_);
v___x_4431_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(v_decl_3822_, v_hasTrace_3881_, v___x_4377_, v___x_4393_, v_cls_4017_, v___x_4397_, v___x_4430_, v___x_4397_, v_a_3824_, v_a_3825_);
v___y_4285_ = v___x_4378_;
v___y_4286_ = v_a_4372_;
v___y_4287_ = v___x_4431_;
goto v___jp_4284_;
}
}
default: 
{
lean_object* v___x_4433_; 
lean_dec_ref(v___f_4400_);
lean_del_object(v___x_4374_);
lean_inc(v_decl_3822_);
v___x_4433_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3822_, v_cls_4017_, v_decl_3822_, v_a_3824_, v_a_3825_);
lean_dec(v_decl_3822_);
v___y_4285_ = v___x_4378_;
v___y_4286_ = v_a_4372_;
v___y_4287_ = v___x_4433_;
goto v___jp_4284_;
}
}
}
}
}
else
{
lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v_env_4439_; lean_object* v_nextMacroScope_4440_; lean_object* v_ngen_4441_; lean_object* v_auxDeclNGen_4442_; lean_object* v_traceState_4443_; lean_object* v_messages_4444_; lean_object* v_infoState_4445_; lean_object* v_snapshotTasks_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4519_; 
v___x_4437_ = lean_io_get_num_heartbeats();
v___x_4438_ = lean_st_ref_take(v_a_3825_);
v_env_4439_ = lean_ctor_get(v___x_4438_, 0);
v_nextMacroScope_4440_ = lean_ctor_get(v___x_4438_, 1);
v_ngen_4441_ = lean_ctor_get(v___x_4438_, 2);
v_auxDeclNGen_4442_ = lean_ctor_get(v___x_4438_, 3);
v_traceState_4443_ = lean_ctor_get(v___x_4438_, 4);
v_messages_4444_ = lean_ctor_get(v___x_4438_, 6);
v_infoState_4445_ = lean_ctor_get(v___x_4438_, 7);
v_snapshotTasks_4446_ = lean_ctor_get(v___x_4438_, 8);
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4438_);
if (v_isSharedCheck_4519_ == 0)
{
lean_object* v_unused_4520_; 
v_unused_4520_ = lean_ctor_get(v___x_4438_, 5);
lean_dec(v_unused_4520_);
v___x_4448_ = v___x_4438_;
v_isShared_4449_ = v_isSharedCheck_4519_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_snapshotTasks_4446_);
lean_inc(v_infoState_4445_);
lean_inc(v_messages_4444_);
lean_inc(v_traceState_4443_);
lean_inc(v_auxDeclNGen_4442_);
lean_inc(v_ngen_4441_);
lean_inc(v_nextMacroScope_4440_);
lean_inc(v_env_4439_);
lean_dec(v___x_4438_);
v___x_4448_ = lean_box(0);
v_isShared_4449_ = v_isSharedCheck_4519_;
goto v_resetjp_4447_;
}
v_resetjp_4447_:
{
lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4454_; 
lean_inc(v_decl_3822_);
v___x_4450_ = l_Lean_Declaration_getNames(v_decl_3822_);
v___x_4451_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4439_, v___x_4450_);
v___x_4452_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4449_ == 0)
{
lean_ctor_set(v___x_4448_, 5, v___x_4452_);
lean_ctor_set(v___x_4448_, 0, v___x_4451_);
v___x_4454_ = v___x_4448_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v___x_4451_);
lean_ctor_set(v_reuseFailAlloc_4518_, 1, v_nextMacroScope_4440_);
lean_ctor_set(v_reuseFailAlloc_4518_, 2, v_ngen_4441_);
lean_ctor_set(v_reuseFailAlloc_4518_, 3, v_auxDeclNGen_4442_);
lean_ctor_set(v_reuseFailAlloc_4518_, 4, v_traceState_4443_);
lean_ctor_set(v_reuseFailAlloc_4518_, 5, v___x_4452_);
lean_ctor_set(v_reuseFailAlloc_4518_, 6, v_messages_4444_);
lean_ctor_set(v_reuseFailAlloc_4518_, 7, v_infoState_4445_);
lean_ctor_set(v_reuseFailAlloc_4518_, 8, v_snapshotTasks_4446_);
v___x_4454_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___f_4458_; 
v___x_4455_ = lean_st_ref_put(v_a_3825_, v___x_4454_);
v___x_4456_ = lean_box(0);
v___x_4457_ = lean_box(v___x_4377_);
lean_inc(v_decl_3822_);
v___f_4458_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed), 10, 5);
lean_closure_set(v___f_4458_, 0, v_decl_3822_);
lean_closure_set(v___f_4458_, 1, v___x_4457_);
lean_closure_set(v___f_4458_, 2, v_cls_4017_);
lean_closure_set(v___f_4458_, 3, v___x_4452_);
lean_closure_set(v___f_4458_, 4, v___x_4456_);
switch(lean_obj_tag(v_decl_3822_))
{
case 2:
{
lean_object* v_val_4459_; lean_object* v___x_4460_; lean_object* v_env_4461_; lean_object* v___f_4462_; 
lean_del_object(v___x_4374_);
v_val_4459_ = lean_ctor_get(v_decl_3822_, 0);
lean_inc_ref_n(v_val_4459_, 2);
lean_dec_ref_known(v_decl_3822_, 1);
v___x_4460_ = lean_st_ref_get(v_a_3825_);
v_env_4461_ = lean_ctor_get(v___x_4460_, 0);
lean_inc_ref(v_env_4461_);
lean_dec(v___x_4460_);
v___f_4462_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed), 7, 2);
lean_closure_set(v___f_4462_, 0, v_val_4459_);
lean_closure_set(v___f_4462_, 1, v___f_4458_);
if (v_forceExpose_3823_ == 0)
{
if (v___x_4377_ == 0)
{
lean_dec_ref(v_env_4461_);
lean_dec_ref(v_val_4459_);
v___y_4263_ = v___x_4437_;
v___y_4264_ = v_a_4372_;
v___y_4265_ = v___f_4462_;
v___y_4266_ = v___x_4456_;
goto v___jp_4262_;
}
else
{
lean_object* v___x_4463_; uint8_t v_isModule_4464_; 
v___x_4463_ = l_Lean_Environment_header(v_env_4461_);
lean_dec_ref(v_env_4461_);
v_isModule_4464_ = lean_ctor_get_uint8(v___x_4463_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4463_);
if (v_isModule_4464_ == 0)
{
lean_dec_ref(v_val_4459_);
v___y_4263_ = v___x_4437_;
v___y_4264_ = v_a_4372_;
v___y_4265_ = v___f_4462_;
v___y_4266_ = v___x_4456_;
goto v___jp_4262_;
}
else
{
if (v___x_4222_ == 0)
{
lean_object* v___x_4465_; lean_object* v___x_4466_; 
v___x_4465_ = lean_box(0);
v___x_4466_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(v_val_4459_, v_forceExpose_3823_, v___f_4462_, v___x_4465_, v_a_3824_, v_a_3825_);
lean_dec_ref(v_val_4459_);
v___y_4236_ = v___x_4437_;
v___y_4237_ = v_a_4372_;
v___y_4238_ = v___x_4466_;
goto v___jp_4235_;
}
else
{
lean_object* v_toConstantVal_4467_; lean_object* v_name_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; 
v_toConstantVal_4467_ = lean_ctor_get(v_val_4459_, 0);
v_name_4468_ = lean_ctor_get(v_toConstantVal_4467_, 0);
v___x_4469_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4468_);
v___x_4470_ = l_Lean_MessageData_ofName(v_name_4468_);
v___x_4471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4471_, 0, v___x_4469_);
lean_ctor_set(v___x_4471_, 1, v___x_4470_);
v___x_4472_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4473_, 0, v___x_4471_);
lean_ctor_set(v___x_4473_, 1, v___x_4472_);
v___x_4474_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4017_, v___x_4473_, v_a_3824_, v_a_3825_);
if (lean_obj_tag(v___x_4474_) == 0)
{
lean_object* v_a_4475_; lean_object* v___x_4476_; 
v_a_4475_ = lean_ctor_get(v___x_4474_, 0);
lean_inc(v_a_4475_);
lean_dec_ref_known(v___x_4474_, 1);
v___x_4476_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(v_val_4459_, v_forceExpose_3823_, v___f_4462_, v_a_4475_, v_a_3824_, v_a_3825_);
lean_dec_ref(v_val_4459_);
v___y_4236_ = v___x_4437_;
v___y_4237_ = v_a_4372_;
v___y_4238_ = v___x_4476_;
goto v___jp_4235_;
}
else
{
lean_dec_ref(v___f_4462_);
lean_dec_ref(v_val_4459_);
v___y_4236_ = v___x_4437_;
v___y_4237_ = v_a_4372_;
v___y_4238_ = v___x_4474_;
goto v___jp_4235_;
}
}
}
}
}
else
{
lean_dec_ref(v_env_4461_);
lean_dec_ref(v_val_4459_);
v___y_4263_ = v___x_4437_;
v___y_4264_ = v_a_4372_;
v___y_4265_ = v___f_4462_;
v___y_4266_ = v___x_4456_;
goto v___jp_4262_;
}
}
case 1:
{
lean_object* v_val_4477_; lean_object* v___x_4478_; 
lean_del_object(v___x_4374_);
v_val_4477_ = lean_ctor_get(v_decl_3822_, 0);
lean_inc_ref(v_val_4477_);
lean_dec_ref_known(v_decl_3822_, 1);
v___x_4478_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v___f_4458_, v_forceExpose_3823_, v___x_4377_, v___x_4456_, v_cls_4017_, v_val_4477_, v_a_3824_, v_a_3825_);
v___y_4236_ = v___x_4437_;
v___y_4237_ = v_a_4372_;
v___y_4238_ = v___x_4478_;
goto v___jp_4235_;
}
case 5:
{
lean_object* v_defns_4479_; 
lean_del_object(v___x_4374_);
v_defns_4479_ = lean_ctor_get(v_decl_3822_, 0);
if (lean_obj_tag(v_defns_4479_) == 1)
{
lean_object* v_tail_4480_; 
v_tail_4480_ = lean_ctor_get(v_defns_4479_, 1);
if (lean_obj_tag(v_tail_4480_) == 0)
{
lean_object* v_head_4481_; lean_object* v___x_4482_; 
lean_inc_ref(v_defns_4479_);
lean_dec_ref_known(v_decl_3822_, 1);
v_head_4481_ = lean_ctor_get(v_defns_4479_, 0);
lean_inc(v_head_4481_);
lean_dec_ref_known(v_defns_4479_, 2);
v___x_4482_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v___f_4458_, v_forceExpose_3823_, v___x_4377_, v___x_4456_, v_cls_4017_, v_head_4481_, v_a_3824_, v_a_3825_);
v___y_4236_ = v___x_4437_;
v___y_4237_ = v_a_4372_;
v___y_4238_ = v___x_4482_;
goto v___jp_4235_;
}
else
{
lean_object* v___x_4483_; 
lean_dec_ref(v___f_4458_);
lean_inc_ref(v_decl_3822_);
v___x_4483_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3822_, v_cls_4017_, v_decl_3822_, v_a_3824_, v_a_3825_);
lean_dec_ref_known(v_decl_3822_, 1);
v___y_4236_ = v___x_4437_;
v___y_4237_ = v_a_4372_;
v___y_4238_ = v___x_4483_;
goto v___jp_4235_;
}
}
else
{
lean_object* v___x_4484_; 
lean_dec_ref(v___f_4458_);
lean_inc_ref(v_decl_3822_);
v___x_4484_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3822_, v_cls_4017_, v_decl_3822_, v_a_3824_, v_a_3825_);
lean_dec_ref_known(v_decl_3822_, 1);
v___y_4236_ = v___x_4437_;
v___y_4237_ = v_a_4372_;
v___y_4238_ = v___x_4484_;
goto v___jp_4235_;
}
}
case 3:
{
lean_object* v_val_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v_env_4488_; lean_object* v_env_4489_; lean_object* v___f_4490_; 
lean_del_object(v___x_4374_);
v_val_4485_ = lean_ctor_get(v_decl_3822_, 0);
lean_inc_ref_n(v_val_4485_, 2);
lean_dec_ref_known(v_decl_3822_, 1);
v___x_4486_ = lean_st_ref_get(v_a_3825_);
v___x_4487_ = lean_st_ref_get(v_a_3825_);
v_env_4488_ = lean_ctor_get(v___x_4486_, 0);
lean_inc_ref(v_env_4488_);
lean_dec(v___x_4486_);
v_env_4489_ = lean_ctor_get(v___x_4487_, 0);
lean_inc_ref(v_env_4489_);
lean_dec(v___x_4487_);
v___f_4490_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed), 7, 2);
lean_closure_set(v___f_4490_, 0, v_val_4485_);
lean_closure_set(v___f_4490_, 1, v___f_4458_);
if (v_forceExpose_3823_ == 0)
{
if (v___x_4377_ == 0)
{
lean_dec_ref(v_env_4489_);
lean_dec_ref(v_env_4488_);
lean_dec_ref(v_val_4485_);
v___y_4256_ = v___f_4490_;
v___y_4257_ = v___x_4437_;
v___y_4258_ = v_a_4372_;
v___y_4259_ = v___x_4456_;
goto v___jp_4255_;
}
else
{
lean_object* v___x_4491_; uint8_t v_isModule_4492_; 
v___x_4491_ = l_Lean_Environment_header(v_env_4488_);
lean_dec_ref(v_env_4488_);
v_isModule_4492_ = lean_ctor_get_uint8(v___x_4491_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4491_);
if (v_isModule_4492_ == 0)
{
lean_dec_ref(v_env_4489_);
lean_dec_ref(v_val_4485_);
v___y_4256_ = v___f_4490_;
v___y_4257_ = v___x_4437_;
v___y_4258_ = v_a_4372_;
v___y_4259_ = v___x_4456_;
goto v___jp_4255_;
}
else
{
uint8_t v_isExporting_4493_; 
v_isExporting_4493_ = lean_ctor_get_uint8(v_env_4489_, sizeof(void*)*8);
lean_dec_ref(v_env_4489_);
if (v_isExporting_4493_ == 0)
{
if (v___x_4222_ == 0)
{
lean_object* v___x_4494_; lean_object* v___x_4495_; 
v___x_4494_ = lean_box(0);
v___x_4495_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_val_4485_, v___f_4490_, v___x_4494_, v_a_3824_, v_a_3825_);
lean_dec_ref(v_val_4485_);
v___y_4236_ = v___x_4437_;
v___y_4237_ = v_a_4372_;
v___y_4238_ = v___x_4495_;
goto v___jp_4235_;
}
else
{
lean_object* v_toConstantVal_4496_; lean_object* v_name_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; 
v_toConstantVal_4496_ = lean_ctor_get(v_val_4485_, 0);
v_name_4497_ = lean_ctor_get(v_toConstantVal_4496_, 0);
v___x_4498_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4497_);
v___x_4499_ = l_Lean_MessageData_ofName(v_name_4497_);
v___x_4500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4500_, 0, v___x_4498_);
lean_ctor_set(v___x_4500_, 1, v___x_4499_);
v___x_4501_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4502_, 0, v___x_4500_);
lean_ctor_set(v___x_4502_, 1, v___x_4501_);
v___x_4503_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4017_, v___x_4502_, v_a_3824_, v_a_3825_);
if (lean_obj_tag(v___x_4503_) == 0)
{
lean_object* v_a_4504_; lean_object* v___x_4505_; 
v_a_4504_ = lean_ctor_get(v___x_4503_, 0);
lean_inc(v_a_4504_);
lean_dec_ref_known(v___x_4503_, 1);
v___x_4505_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_val_4485_, v___f_4490_, v_a_4504_, v_a_3824_, v_a_3825_);
lean_dec_ref(v_val_4485_);
v___y_4236_ = v___x_4437_;
v___y_4237_ = v_a_4372_;
v___y_4238_ = v___x_4505_;
goto v___jp_4235_;
}
else
{
lean_dec_ref(v___f_4490_);
lean_dec_ref(v_val_4485_);
v___y_4236_ = v___x_4437_;
v___y_4237_ = v_a_4372_;
v___y_4238_ = v___x_4503_;
goto v___jp_4235_;
}
}
}
else
{
lean_dec_ref(v_val_4485_);
v___y_4256_ = v___f_4490_;
v___y_4257_ = v___x_4437_;
v___y_4258_ = v_a_4372_;
v___y_4259_ = v___x_4456_;
goto v___jp_4255_;
}
}
}
}
else
{
lean_dec_ref(v_env_4489_);
lean_dec_ref(v_env_4488_);
lean_dec_ref(v_val_4485_);
v___y_4256_ = v___f_4490_;
v___y_4257_ = v___x_4437_;
v___y_4258_ = v_a_4372_;
v___y_4259_ = v___x_4456_;
goto v___jp_4255_;
}
}
case 0:
{
lean_object* v_val_4506_; lean_object* v_toConstantVal_4507_; lean_object* v_name_4508_; lean_object* v___x_4510_; 
lean_dec_ref(v___f_4458_);
v_val_4506_ = lean_ctor_get(v_decl_3822_, 0);
v_toConstantVal_4507_ = lean_ctor_get(v_val_4506_, 0);
v_name_4508_ = lean_ctor_get(v_toConstantVal_4507_, 0);
lean_inc_ref(v_val_4506_);
if (v_isShared_4375_ == 0)
{
lean_ctor_set(v___x_4374_, 0, v_val_4506_);
v___x_4510_ = v___x_4374_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v_val_4506_);
v___x_4510_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
uint8_t v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; 
v___x_4511_ = 2;
v___x_4512_ = lean_box(v___x_4511_);
v___x_4513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4513_, 0, v___x_4510_);
lean_ctor_set(v___x_4513_, 1, v___x_4512_);
lean_inc(v_name_4508_);
v___x_4514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4514_, 0, v_name_4508_);
lean_ctor_set(v___x_4514_, 1, v___x_4513_);
v___x_4515_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_decl_3822_, v___x_4377_, v_cls_4017_, v___x_4452_, v___x_4456_, v___x_4514_, v___x_4456_, v_a_3824_, v_a_3825_);
v___y_4236_ = v___x_4437_;
v___y_4237_ = v_a_4372_;
v___y_4238_ = v___x_4515_;
goto v___jp_4235_;
}
}
default: 
{
lean_object* v___x_4517_; 
lean_dec_ref(v___f_4458_);
lean_del_object(v___x_4374_);
lean_inc(v_decl_3822_);
v___x_4517_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3822_, v_cls_4017_, v_decl_3822_, v_a_3824_, v_a_3825_);
lean_dec(v_decl_3822_);
v___y_4236_ = v___x_4437_;
v___y_4237_ = v_a_4372_;
v___y_4238_ = v___x_4517_;
goto v___jp_4235_;
}
}
}
}
}
}
}
}
v___jp_3827_:
{
lean_object* v___x_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3838_; 
v___x_3831_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3828_, v___y_3829_);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3838_ == 0)
{
lean_object* v_unused_3839_; 
v_unused_3839_ = lean_ctor_get(v___x_3831_, 0);
lean_dec(v_unused_3839_);
v___x_3833_ = v___x_3831_;
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
else
{
lean_dec(v___x_3831_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v___x_3836_; 
if (v_isShared_3834_ == 0)
{
lean_ctor_set(v___x_3833_, 0, v_a_3830_);
v___x_3836_ = v___x_3833_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_a_3830_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
}
v___jp_3840_:
{
lean_object* v___x_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3851_; 
v___x_3844_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3841_, v___y_3842_);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3844_);
if (v_isSharedCheck_3851_ == 0)
{
lean_object* v_unused_3852_; 
v_unused_3852_ = lean_ctor_get(v___x_3844_, 0);
lean_dec(v_unused_3852_);
v___x_3846_ = v___x_3844_;
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
else
{
lean_dec(v___x_3844_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3849_; 
if (v_isShared_3847_ == 0)
{
lean_ctor_set_tag(v___x_3846_, 1);
lean_ctor_set(v___x_3846_, 0, v_a_3843_);
v___x_3849_ = v___x_3846_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3843_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
v___jp_3853_:
{
lean_object* v___x_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3864_; 
v___x_3857_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3855_, v___y_3854_);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3864_ == 0)
{
lean_object* v_unused_3865_; 
v_unused_3865_ = lean_ctor_get(v___x_3857_, 0);
lean_dec(v_unused_3865_);
v___x_3859_ = v___x_3857_;
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
else
{
lean_dec(v___x_3857_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3862_; 
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 0, v_a_3856_);
v___x_3862_ = v___x_3859_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_a_3856_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
}
v___jp_3866_:
{
lean_object* v___x_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3877_; 
v___x_3870_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3868_, v___y_3867_);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3877_ == 0)
{
lean_object* v_unused_3878_; 
v_unused_3878_ = lean_ctor_get(v___x_3870_, 0);
lean_dec(v_unused_3878_);
v___x_3872_ = v___x_3870_;
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
else
{
lean_dec(v___x_3870_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3875_; 
if (v_isShared_3873_ == 0)
{
lean_ctor_set_tag(v___x_3872_, 1);
lean_ctor_set(v___x_3872_, 0, v_a_3869_);
v___x_3875_ = v___x_3872_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_a_3869_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
}
v___jp_3882_:
{
lean_object* v___x_3894_; 
lean_inc_ref(v___y_3885_);
v___x_3894_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3886_, v___y_3885_, v___y_3887_, v___y_3893_);
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_object* v___x_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3941_; 
lean_dec_ref_known(v___x_3894_, 1);
lean_inc_ref(v___y_3889_);
v___x_3895_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3889_, v___y_3884_);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_3941_ == 0)
{
lean_object* v_unused_3942_; 
v_unused_3942_ = lean_ctor_get(v___x_3895_, 0);
lean_dec(v_unused_3942_);
v___x_3897_ = v___x_3895_;
v_isShared_3898_ = v_isSharedCheck_3941_;
goto v_resetjp_3896_;
}
else
{
lean_dec(v___x_3895_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3941_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
lean_object* v_options_3899_; lean_object* v___x_3900_; uint8_t v___x_3901_; 
v_options_3899_ = lean_ctor_get(v___y_3892_, 2);
v___x_3900_ = l_Lean_Elab_async;
v___x_3901_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3899_, v___x_3900_);
if (v___x_3901_ == 0)
{
lean_object* v___x_3902_; lean_object* v_r_3903_; 
lean_del_object(v___x_3897_);
lean_dec_ref(v___y_3891_);
lean_dec_ref(v___y_3890_);
v___x_3902_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3885_, v___y_3884_);
lean_dec_ref(v___x_3902_);
v_r_3903_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3822_, v___y_3892_, v___y_3884_);
if (lean_obj_tag(v_r_3903_) == 0)
{
lean_object* v_a_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3913_; 
v_a_3904_ = lean_ctor_get(v_r_3903_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v_r_3903_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3906_ = v_r_3903_;
v_isShared_3907_ = v_isSharedCheck_3913_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_a_3904_);
lean_dec(v_r_3903_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3913_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___x_3909_; 
lean_inc(v_a_3904_);
if (v_isShared_3907_ == 0)
{
lean_ctor_set_tag(v___x_3906_, 1);
v___x_3909_ = v___x_3906_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3904_);
v___x_3909_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
lean_object* v___x_3910_; 
v___x_3910_ = lean_apply_2(v___y_3883_, v___x_3909_, lean_box(0));
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_dec_ref_known(v___x_3910_, 1);
v___y_3854_ = v___y_3884_;
v___y_3855_ = v___y_3889_;
v_a_3856_ = v_a_3904_;
goto v___jp_3853_;
}
else
{
lean_object* v_a_3911_; 
lean_dec(v_a_3904_);
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
lean_inc(v_a_3911_);
lean_dec_ref_known(v___x_3910_, 1);
v___y_3867_ = v___y_3884_;
v___y_3868_ = v___y_3889_;
v_a_3869_ = v_a_3911_;
goto v___jp_3866_;
}
}
}
}
else
{
lean_object* v_a_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v_a_3914_ = lean_ctor_get(v_r_3903_, 0);
lean_inc(v_a_3914_);
lean_dec_ref_known(v_r_3903_, 1);
v___x_3915_ = lean_box(0);
v___x_3916_ = lean_apply_2(v___y_3883_, v___x_3915_, lean_box(0));
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_dec_ref_known(v___x_3916_, 1);
v___y_3867_ = v___y_3884_;
v___y_3868_ = v___y_3889_;
v_a_3869_ = v_a_3914_;
goto v___jp_3866_;
}
else
{
lean_object* v_a_3917_; 
lean_dec(v_a_3914_);
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref_known(v___x_3916_, 1);
v___y_3867_ = v___y_3884_;
v___y_3868_ = v___y_3889_;
v_a_3869_ = v_a_3917_;
goto v___jp_3866_;
}
}
}
else
{
lean_object* v___x_3918_; lean_object* v___x_3920_; 
lean_dec_ref(v___y_3889_);
lean_dec_ref(v___y_3885_);
lean_dec_ref(v___y_3883_);
lean_dec(v_decl_3822_);
v___x_3918_ = l_IO_CancelToken_new();
if (v_isShared_3898_ == 0)
{
lean_ctor_set_tag(v___x_3897_, 1);
lean_ctor_set(v___x_3897_, 0, v___x_3918_);
v___x_3920_ = v___x_3897_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v___x_3918_);
v___x_3920_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3921_ = lean_unsigned_to_nat(0u);
v___x_3922_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_3923_ = l_Lean_Name_toString(v___x_3922_, v___y_3888_);
lean_inc_ref(v___x_3920_);
v___x_3924_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3891_, v___x_3920_, v___x_3923_, v___y_3892_, v___y_3884_);
if (lean_obj_tag(v___x_3924_) == 0)
{
lean_object* v_a_3925_; lean_object* v_checked_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
v_a_3925_ = lean_ctor_get(v___x_3924_, 0);
lean_inc(v_a_3925_);
lean_dec_ref_known(v___x_3924_, 1);
v_checked_3926_ = lean_ctor_get(v___y_3890_, 2);
lean_inc_ref(v_checked_3926_);
lean_dec_ref(v___y_3890_);
v___x_3927_ = lean_io_map_task(v_a_3925_, v_checked_3926_, v___x_3921_, v_hasTrace_3881_);
v___x_3928_ = lean_box(0);
v___x_3929_ = lean_box(2);
v___x_3930_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3928_);
lean_ctor_set(v___x_3930_, 1, v___x_3929_);
lean_ctor_set(v___x_3930_, 2, v___x_3920_);
lean_ctor_set(v___x_3930_, 3, v___x_3927_);
v___x_3931_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3930_, v___y_3884_);
return v___x_3931_;
}
else
{
lean_object* v_a_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3939_; 
lean_dec_ref(v___x_3920_);
lean_dec_ref(v___y_3890_);
v_a_3932_ = lean_ctor_get(v___x_3924_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3924_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3934_ = v___x_3924_;
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_a_3932_);
lean_dec(v___x_3924_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3937_; 
if (v_isShared_3935_ == 0)
{
v___x_3937_ = v___x_3934_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_a_3932_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3955_; 
lean_dec_ref(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_dec_ref(v___y_3885_);
lean_dec_ref(v___y_3883_);
lean_dec(v_decl_3822_);
v_a_3943_ = lean_ctor_get(v___x_3894_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3945_ = v___x_3894_;
v_isShared_3946_ = v_isSharedCheck_3955_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3894_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3955_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v_ref_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3953_; 
v_ref_3947_ = lean_ctor_get(v___y_3892_, 5);
v___x_3948_ = lean_io_error_to_string(v_a_3943_);
v___x_3949_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3948_);
v___x_3950_ = l_Lean_MessageData_ofFormat(v___x_3949_);
lean_inc(v_ref_3947_);
v___x_3951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3951_, 0, v_ref_3947_);
lean_ctor_set(v___x_3951_, 1, v___x_3950_);
if (v_isShared_3946_ == 0)
{
lean_ctor_set(v___x_3945_, 0, v___x_3951_);
v___x_3953_ = v___x_3945_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v___x_3951_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
return v___x_3953_;
}
}
}
}
v___jp_3956_:
{
uint8_t v___x_3967_; lean_object* v___x_3968_; 
v___x_3967_ = 1;
lean_inc_ref(v___y_3958_);
v___x_3968_ = l_Lean_Environment_addConstAsync(v___y_3958_, v___y_3964_, v___y_3960_, v___y_3966_, v_hasTrace_3881_, v___x_3967_);
if (lean_obj_tag(v___x_3968_) == 0)
{
lean_object* v_a_3969_; lean_object* v_mainEnv_3970_; lean_object* v_asyncEnv_3971_; lean_object* v___f_3972_; lean_object* v___f_3973_; lean_object* v___x_3974_; 
v_a_3969_ = lean_ctor_get(v___x_3968_, 0);
lean_inc_n(v_a_3969_, 3);
lean_dec_ref_known(v___x_3968_, 1);
v_mainEnv_3970_ = lean_ctor_get(v_a_3969_, 0);
lean_inc_ref(v_mainEnv_3970_);
v_asyncEnv_3971_ = lean_ctor_get(v_a_3969_, 1);
lean_inc_ref_n(v_asyncEnv_3971_, 2);
lean_inc_ref(v___y_3959_);
lean_inc(v___y_3957_);
v___f_3972_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3972_, 0, v___y_3957_);
lean_closure_set(v___f_3972_, 1, v_a_3969_);
lean_closure_set(v___f_3972_, 2, v___y_3959_);
lean_inc(v_decl_3822_);
v___f_3973_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3973_, 0, v_asyncEnv_3971_);
lean_closure_set(v___f_3973_, 1, v_a_3969_);
lean_closure_set(v___f_3973_, 2, v_decl_3822_);
v___x_3974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3974_, 0, v___y_3965_);
if (lean_obj_tag(v___y_3963_) == 0)
{
lean_inc_ref(v___x_3974_);
v___y_3883_ = v___f_3972_;
v___y_3884_ = v___y_3962_;
v___y_3885_ = v_asyncEnv_3971_;
v___y_3886_ = v_a_3969_;
v___y_3887_ = v___x_3974_;
v___y_3888_ = v___x_3967_;
v___y_3889_ = v_mainEnv_3970_;
v___y_3890_ = v___y_3958_;
v___y_3891_ = v___f_3973_;
v___y_3892_ = v___y_3961_;
v___y_3893_ = v___x_3974_;
goto v___jp_3882_;
}
else
{
v___y_3883_ = v___f_3972_;
v___y_3884_ = v___y_3962_;
v___y_3885_ = v_asyncEnv_3971_;
v___y_3886_ = v_a_3969_;
v___y_3887_ = v___x_3974_;
v___y_3888_ = v___x_3967_;
v___y_3889_ = v_mainEnv_3970_;
v___y_3890_ = v___y_3958_;
v___y_3891_ = v___f_3973_;
v___y_3892_ = v___y_3961_;
v___y_3893_ = v___y_3963_;
goto v___jp_3882_;
}
}
else
{
lean_object* v_a_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3987_; 
lean_dec_ref(v___y_3965_);
lean_dec(v___y_3963_);
lean_dec_ref(v___y_3958_);
lean_dec(v_decl_3822_);
v_a_3975_ = lean_ctor_get(v___x_3968_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3977_ = v___x_3968_;
v_isShared_3978_ = v_isSharedCheck_3987_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_a_3975_);
lean_dec(v___x_3968_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3987_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v_ref_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3985_; 
v_ref_3979_ = lean_ctor_get(v___y_3961_, 5);
v___x_3980_ = lean_io_error_to_string(v_a_3975_);
v___x_3981_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3981_, 0, v___x_3980_);
v___x_3982_ = l_Lean_MessageData_ofFormat(v___x_3981_);
lean_inc(v_ref_3979_);
v___x_3983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3983_, 0, v_ref_3979_);
lean_ctor_set(v___x_3983_, 1, v___x_3982_);
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 0, v___x_3983_);
v___x_3985_ = v___x_3977_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v___x_3983_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
}
v___jp_3988_:
{
lean_object* v___x_3995_; 
v___x_3995_ = lean_st_ref_get(v___y_3994_);
if (lean_obj_tag(v_exportedInfo_x3f_3992_) == 0)
{
lean_object* v_env_3996_; lean_object* v___x_3997_; 
v_env_3996_ = lean_ctor_get(v___x_3995_, 0);
lean_inc_ref(v_env_3996_);
lean_dec(v___x_3995_);
v___x_3997_ = lean_box(0);
v___y_3957_ = v___y_3994_;
v___y_3958_ = v_env_3996_;
v___y_3959_ = v___y_3993_;
v___y_3960_ = v___y_3989_;
v___y_3961_ = v___y_3993_;
v___y_3962_ = v___y_3994_;
v___y_3963_ = v_exportedInfo_x3f_3992_;
v___y_3964_ = v___y_3990_;
v___y_3965_ = v___y_3991_;
v___y_3966_ = v___x_3997_;
goto v___jp_3956_;
}
else
{
lean_object* v_env_3998_; lean_object* v_val_3999_; uint8_t v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
v_env_3998_ = lean_ctor_get(v___x_3995_, 0);
lean_inc_ref(v_env_3998_);
lean_dec(v___x_3995_);
v_val_3999_ = lean_ctor_get(v_exportedInfo_x3f_3992_, 0);
v___x_4000_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3999_);
v___x_4001_ = lean_box(v___x_4000_);
v___x_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4001_);
v___y_3957_ = v___y_3994_;
v___y_3958_ = v_env_3998_;
v___y_3959_ = v___y_3993_;
v___y_3960_ = v___y_3989_;
v___y_3961_ = v___y_3993_;
v___y_3962_ = v___y_3994_;
v___y_3963_ = v_exportedInfo_x3f_3992_;
v___y_3964_ = v___y_3990_;
v___y_3965_ = v___y_3991_;
v___y_3966_ = v___x_4002_;
goto v___jp_3956_;
}
}
v___jp_4003_:
{
lean_object* v___x_4009_; 
lean_inc_ref(v___y_4006_);
v___x_4009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4009_, 0, v___y_4006_);
v___y_3989_ = v___y_4004_;
v___y_3990_ = v___y_4005_;
v___y_3991_ = v___y_4006_;
v_exportedInfo_x3f_3992_ = v___x_4009_;
v___y_3993_ = v___y_4007_;
v___y_3994_ = v___y_4008_;
goto v___jp_3988_;
}
v___jp_4010_:
{
lean_object* v___x_4016_; 
lean_inc_ref(v___y_4013_);
v___x_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4016_, 0, v___y_4013_);
v___y_3989_ = v___y_4011_;
v___y_3990_ = v___y_4012_;
v___y_3991_ = v___y_4013_;
v_exportedInfo_x3f_3992_ = v___x_4016_;
v___y_3993_ = v___y_4014_;
v___y_3994_ = v___y_4015_;
goto v___jp_3988_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___boxed(lean_object* v_decl_4903_, lean_object* v_forceExpose_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_){
_start:
{
uint8_t v_forceExpose_boxed_4908_; lean_object* v_res_4909_; 
v_forceExpose_boxed_4908_ = lean_unbox(v_forceExpose_4904_);
v_res_4909_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4903_, v_forceExpose_boxed_4908_, v_a_4905_, v_a_4906_);
lean_dec(v_a_4906_);
lean_dec_ref(v_a_4905_);
return v_res_4909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(lean_object* v_opt_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_){
_start:
{
lean_object* v___x_4914_; 
v___x_4914_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_4910_, v___y_4911_);
return v___x_4914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___boxed(lean_object* v_opt_4915_, lean_object* v___y_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_){
_start:
{
lean_object* v_res_4919_; 
v_res_4919_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(v_opt_4915_, v___y_4916_, v___y_4917_);
lean_dec(v___y_4917_);
lean_dec_ref(v___y_4916_);
lean_dec_ref(v_opt_4915_);
return v_res_4919_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0(lean_object* v_x_4920_, lean_object* v_x_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_){
_start:
{
if (lean_obj_tag(v_x_4920_) == 0)
{
lean_object* v___x_4925_; lean_object* v___x_4926_; 
v___x_4925_ = l_List_reverse___redArg(v_x_4921_);
v___x_4926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4926_, 0, v___x_4925_);
return v___x_4926_;
}
else
{
lean_object* v_head_4927_; lean_object* v_tail_4928_; lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4946_; 
v_head_4927_ = lean_ctor_get(v_x_4920_, 0);
v_tail_4928_ = lean_ctor_get(v_x_4920_, 1);
v_isSharedCheck_4946_ = !lean_is_exclusive(v_x_4920_);
if (v_isSharedCheck_4946_ == 0)
{
v___x_4930_ = v_x_4920_;
v_isShared_4931_ = v_isSharedCheck_4946_;
goto v_resetjp_4929_;
}
else
{
lean_inc(v_tail_4928_);
lean_inc(v_head_4927_);
lean_dec(v_x_4920_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4946_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
lean_object* v___x_4932_; 
v___x_4932_ = l_Lean_snapshotEnvLinterOptions(v_head_4927_, v___y_4922_, v___y_4923_);
if (lean_obj_tag(v___x_4932_) == 0)
{
lean_object* v_a_4933_; lean_object* v___x_4935_; 
v_a_4933_ = lean_ctor_get(v___x_4932_, 0);
lean_inc(v_a_4933_);
lean_dec_ref_known(v___x_4932_, 1);
if (v_isShared_4931_ == 0)
{
lean_ctor_set(v___x_4930_, 1, v_x_4921_);
lean_ctor_set(v___x_4930_, 0, v_a_4933_);
v___x_4935_ = v___x_4930_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4937_; 
v_reuseFailAlloc_4937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4937_, 0, v_a_4933_);
lean_ctor_set(v_reuseFailAlloc_4937_, 1, v_x_4921_);
v___x_4935_ = v_reuseFailAlloc_4937_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
v_x_4920_ = v_tail_4928_;
v_x_4921_ = v___x_4935_;
goto _start;
}
}
else
{
lean_object* v_a_4938_; lean_object* v___x_4940_; uint8_t v_isShared_4941_; uint8_t v_isSharedCheck_4945_; 
lean_del_object(v___x_4930_);
lean_dec(v_tail_4928_);
lean_dec(v_x_4921_);
v_a_4938_ = lean_ctor_get(v___x_4932_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v___x_4932_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4940_ = v___x_4932_;
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
else
{
lean_inc(v_a_4938_);
lean_dec(v___x_4932_);
v___x_4940_ = lean_box(0);
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
v_resetjp_4939_:
{
lean_object* v___x_4943_; 
if (v_isShared_4941_ == 0)
{
v___x_4943_ = v___x_4940_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v_a_4938_);
v___x_4943_ = v_reuseFailAlloc_4944_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
return v___x_4943_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0___boxed(lean_object* v_x_4947_, lean_object* v_x_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_){
_start:
{
lean_object* v_res_4952_; 
v_res_4952_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v_x_4947_, v_x_4948_, v___y_4949_, v___y_4950_);
lean_dec(v___y_4950_);
lean_dec_ref(v___y_4949_);
return v_res_4952_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object* v_decl_4953_, uint8_t v_forceExpose_4954_, lean_object* v_a_4955_, lean_object* v_a_4956_){
_start:
{
lean_object* v___x_4958_; 
lean_inc(v_decl_4953_);
v___x_4958_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4953_, v_forceExpose_4954_, v_a_4955_, v_a_4956_);
if (lean_obj_tag(v___x_4958_) == 0)
{
lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; 
lean_dec_ref_known(v___x_4958_, 1);
v___x_4959_ = l_Lean_Declaration_getTopLevelNames(v_decl_4953_);
v___x_4960_ = lean_box(0);
v___x_4961_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v___x_4959_, v___x_4960_, v_a_4955_, v_a_4956_);
if (lean_obj_tag(v___x_4961_) == 0)
{
lean_object* v___x_4963_; uint8_t v_isShared_4964_; uint8_t v_isSharedCheck_4969_; 
v_isSharedCheck_4969_ = !lean_is_exclusive(v___x_4961_);
if (v_isSharedCheck_4969_ == 0)
{
lean_object* v_unused_4970_; 
v_unused_4970_ = lean_ctor_get(v___x_4961_, 0);
lean_dec(v_unused_4970_);
v___x_4963_ = v___x_4961_;
v_isShared_4964_ = v_isSharedCheck_4969_;
goto v_resetjp_4962_;
}
else
{
lean_dec(v___x_4961_);
v___x_4963_ = lean_box(0);
v_isShared_4964_ = v_isSharedCheck_4969_;
goto v_resetjp_4962_;
}
v_resetjp_4962_:
{
lean_object* v___x_4965_; lean_object* v___x_4967_; 
v___x_4965_ = lean_box(0);
if (v_isShared_4964_ == 0)
{
lean_ctor_set(v___x_4963_, 0, v___x_4965_);
v___x_4967_ = v___x_4963_;
goto v_reusejp_4966_;
}
else
{
lean_object* v_reuseFailAlloc_4968_; 
v_reuseFailAlloc_4968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4968_, 0, v___x_4965_);
v___x_4967_ = v_reuseFailAlloc_4968_;
goto v_reusejp_4966_;
}
v_reusejp_4966_:
{
return v___x_4967_;
}
}
}
else
{
lean_object* v_a_4971_; lean_object* v___x_4973_; uint8_t v_isShared_4974_; uint8_t v_isSharedCheck_4978_; 
v_a_4971_ = lean_ctor_get(v___x_4961_, 0);
v_isSharedCheck_4978_ = !lean_is_exclusive(v___x_4961_);
if (v_isSharedCheck_4978_ == 0)
{
v___x_4973_ = v___x_4961_;
v_isShared_4974_ = v_isSharedCheck_4978_;
goto v_resetjp_4972_;
}
else
{
lean_inc(v_a_4971_);
lean_dec(v___x_4961_);
v___x_4973_ = lean_box(0);
v_isShared_4974_ = v_isSharedCheck_4978_;
goto v_resetjp_4972_;
}
v_resetjp_4972_:
{
lean_object* v___x_4976_; 
if (v_isShared_4974_ == 0)
{
v___x_4976_ = v___x_4973_;
goto v_reusejp_4975_;
}
else
{
lean_object* v_reuseFailAlloc_4977_; 
v_reuseFailAlloc_4977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4977_, 0, v_a_4971_);
v___x_4976_ = v_reuseFailAlloc_4977_;
goto v_reusejp_4975_;
}
v_reusejp_4975_:
{
return v___x_4976_;
}
}
}
}
else
{
lean_dec(v_decl_4953_);
return v___x_4958_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___boxed(lean_object* v_decl_4979_, lean_object* v_forceExpose_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_){
_start:
{
uint8_t v_forceExpose_boxed_4984_; lean_object* v_res_4985_; 
v_forceExpose_boxed_4984_ = lean_unbox(v_forceExpose_4980_);
v_res_4985_ = l_Lean_addDecl(v_decl_4979_, v_forceExpose_boxed_4984_, v_a_4981_, v_a_4982_);
lean_dec(v_a_4982_);
lean_dec_ref(v_a_4981_);
return v_res_4985_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(lean_object* v_as_x27_4986_, lean_object* v_b_4987_, lean_object* v___y_4988_){
_start:
{
if (lean_obj_tag(v_as_x27_4986_) == 0)
{
lean_object* v___x_4990_; 
v___x_4990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4990_, 0, v_b_4987_);
return v___x_4990_;
}
else
{
lean_object* v_head_4991_; lean_object* v_tail_4992_; lean_object* v___x_4993_; lean_object* v_env_4994_; lean_object* v_nextMacroScope_4995_; lean_object* v_ngen_4996_; lean_object* v_auxDeclNGen_4997_; lean_object* v_traceState_4998_; lean_object* v_messages_4999_; lean_object* v_infoState_5000_; lean_object* v_snapshotTasks_5001_; lean_object* v___x_5003_; uint8_t v_isShared_5004_; uint8_t v_isSharedCheck_5013_; 
v_head_4991_ = lean_ctor_get(v_as_x27_4986_, 0);
v_tail_4992_ = lean_ctor_get(v_as_x27_4986_, 1);
v___x_4993_ = lean_st_ref_take(v___y_4988_);
v_env_4994_ = lean_ctor_get(v___x_4993_, 0);
v_nextMacroScope_4995_ = lean_ctor_get(v___x_4993_, 1);
v_ngen_4996_ = lean_ctor_get(v___x_4993_, 2);
v_auxDeclNGen_4997_ = lean_ctor_get(v___x_4993_, 3);
v_traceState_4998_ = lean_ctor_get(v___x_4993_, 4);
v_messages_4999_ = lean_ctor_get(v___x_4993_, 6);
v_infoState_5000_ = lean_ctor_get(v___x_4993_, 7);
v_snapshotTasks_5001_ = lean_ctor_get(v___x_4993_, 8);
v_isSharedCheck_5013_ = !lean_is_exclusive(v___x_4993_);
if (v_isSharedCheck_5013_ == 0)
{
lean_object* v_unused_5014_; 
v_unused_5014_ = lean_ctor_get(v___x_4993_, 5);
lean_dec(v_unused_5014_);
v___x_5003_ = v___x_4993_;
v_isShared_5004_ = v_isSharedCheck_5013_;
goto v_resetjp_5002_;
}
else
{
lean_inc(v_snapshotTasks_5001_);
lean_inc(v_infoState_5000_);
lean_inc(v_messages_4999_);
lean_inc(v_traceState_4998_);
lean_inc(v_auxDeclNGen_4997_);
lean_inc(v_ngen_4996_);
lean_inc(v_nextMacroScope_4995_);
lean_inc(v_env_4994_);
lean_dec(v___x_4993_);
v___x_5003_ = lean_box(0);
v_isShared_5004_ = v_isSharedCheck_5013_;
goto v_resetjp_5002_;
}
v_resetjp_5002_:
{
lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5008_; 
lean_inc(v_head_4991_);
v___x_5005_ = l_Lean_markMeta(v_env_4994_, v_head_4991_);
v___x_5006_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_5004_ == 0)
{
lean_ctor_set(v___x_5003_, 5, v___x_5006_);
lean_ctor_set(v___x_5003_, 0, v___x_5005_);
v___x_5008_ = v___x_5003_;
goto v_reusejp_5007_;
}
else
{
lean_object* v_reuseFailAlloc_5012_; 
v_reuseFailAlloc_5012_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5012_, 0, v___x_5005_);
lean_ctor_set(v_reuseFailAlloc_5012_, 1, v_nextMacroScope_4995_);
lean_ctor_set(v_reuseFailAlloc_5012_, 2, v_ngen_4996_);
lean_ctor_set(v_reuseFailAlloc_5012_, 3, v_auxDeclNGen_4997_);
lean_ctor_set(v_reuseFailAlloc_5012_, 4, v_traceState_4998_);
lean_ctor_set(v_reuseFailAlloc_5012_, 5, v___x_5006_);
lean_ctor_set(v_reuseFailAlloc_5012_, 6, v_messages_4999_);
lean_ctor_set(v_reuseFailAlloc_5012_, 7, v_infoState_5000_);
lean_ctor_set(v_reuseFailAlloc_5012_, 8, v_snapshotTasks_5001_);
v___x_5008_ = v_reuseFailAlloc_5012_;
goto v_reusejp_5007_;
}
v_reusejp_5007_:
{
lean_object* v___x_5009_; lean_object* v___x_5010_; 
v___x_5009_ = lean_st_ref_put(v___y_4988_, v___x_5008_);
v___x_5010_ = lean_box(0);
v_as_x27_4986_ = v_tail_4992_;
v_b_4987_ = v___x_5010_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg___boxed(lean_object* v_as_x27_5015_, lean_object* v_b_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_){
_start:
{
lean_object* v_res_5019_; 
v_res_5019_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_5015_, v_b_5016_, v___y_5017_);
lean_dec(v___y_5017_);
lean_dec(v_as_x27_5015_);
return v_res_5019_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object* v_decl_5020_, uint8_t v_logCompileErrors_5021_, uint8_t v_markMeta_5022_, lean_object* v_a_5023_, lean_object* v_a_5024_){
_start:
{
uint8_t v___x_5026_; lean_object* v___x_5027_; 
v___x_5026_ = 0;
lean_inc(v_decl_5020_);
v___x_5027_ = l_Lean_addDecl(v_decl_5020_, v___x_5026_, v_a_5023_, v_a_5024_);
if (lean_obj_tag(v___x_5027_) == 0)
{
lean_dec_ref_known(v___x_5027_, 1);
if (v_markMeta_5022_ == 0)
{
lean_object* v___x_5028_; 
v___x_5028_ = l_Lean_compileDecl(v_decl_5020_, v_logCompileErrors_5021_, v_a_5023_, v_a_5024_);
return v___x_5028_;
}
else
{
lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; 
lean_inc(v_decl_5020_);
v___x_5029_ = l_Lean_Declaration_getNames(v_decl_5020_);
v___x_5030_ = lean_box(0);
v___x_5031_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v___x_5029_, v___x_5030_, v_a_5024_);
lean_dec(v___x_5029_);
lean_dec_ref(v___x_5031_);
v___x_5032_ = l_Lean_compileDecl(v_decl_5020_, v_logCompileErrors_5021_, v_a_5023_, v_a_5024_);
return v___x_5032_;
}
}
else
{
lean_dec(v_decl_5020_);
return v___x_5027_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___boxed(lean_object* v_decl_5033_, lean_object* v_logCompileErrors_5034_, lean_object* v_markMeta_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_){
_start:
{
uint8_t v_logCompileErrors_boxed_5039_; uint8_t v_markMeta_boxed_5040_; lean_object* v_res_5041_; 
v_logCompileErrors_boxed_5039_ = lean_unbox(v_logCompileErrors_5034_);
v_markMeta_boxed_5040_ = lean_unbox(v_markMeta_5035_);
v_res_5041_ = l_Lean_addAndCompile(v_decl_5033_, v_logCompileErrors_boxed_5039_, v_markMeta_boxed_5040_, v_a_5036_, v_a_5037_);
lean_dec(v_a_5037_);
lean_dec_ref(v_a_5036_);
return v_res_5041_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(lean_object* v_as_5042_, lean_object* v_as_x27_5043_, lean_object* v_b_5044_, lean_object* v_a_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_){
_start:
{
lean_object* v___x_5049_; 
v___x_5049_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_5043_, v_b_5044_, v___y_5047_);
return v___x_5049_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___boxed(lean_object* v_as_5050_, lean_object* v_as_x27_5051_, lean_object* v_b_5052_, lean_object* v_a_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_){
_start:
{
lean_object* v_res_5057_; 
v_res_5057_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(v_as_5050_, v_as_x27_5051_, v_b_5052_, v_a_5053_, v___y_5054_, v___y_5055_);
lean_dec(v___y_5055_);
lean_dec_ref(v___y_5054_);
lean_dec(v_as_x27_5051_);
lean_dec(v_as_5050_);
return v_res_5057_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sorry(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectAxioms(uint8_t builtin);
lean_object* runtime_initialize_Lean_OriginalConstKind(uint8_t builtin);
lean_object* runtime_initialize_Lean_AutoDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_MetaAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_RecDepth(uint8_t builtin);
lean_object* runtime_initialize_Lean_OriginalConstKind(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sorry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectAxioms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_OriginalConstKind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_AutoDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_MetaAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_RecDepth(builtin);
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
lean_object* initialize_Lean_AutoDecl(uint8_t builtin);
lean_object* initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* initialize_Lean_Compiler_MetaAttr(uint8_t builtin);
lean_object* initialize_Lean_Util_RecDepth(uint8_t builtin);
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
res = initialize_Lean_AutoDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_MetaAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_RecDepth(builtin);
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
