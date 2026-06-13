// Lean compiler output
// Module: Lean.AddDecl
// Imports: public import Lean.Meta.Sorry public import Lean.Util.CollectAxioms public import Lean.OriginalConstKind public import Lean.AutoDecl import Lean.Linter.Init import Lean.Compiler.MetaAttr import all Lean.OriginalConstKind
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
lean_object* l_Lean_Expr_getSorry_x3f(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_debug_skipKernelTC;
lean_object* l_Lean_Environment_addDeclCore(lean_object*, size_t, lean_object*, lean_object*, uint8_t);
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
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* lean_add_decl(lean_object*, size_t, lean_object*, lean_object*);
lean_object* lean_add_decl_without_checking(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_envLinterOptionsRef;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_envLinterSnapshotExt;
lean_object* l_Lean_markMeta(lean_object*, lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__5;
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg(lean_object* v_a_47_, lean_object* v_as_48_, size_t v_sz_49_, size_t v_i_50_, lean_object* v_b_51_){
_start:
{
uint8_t v___x_53_; 
v___x_53_ = lean_usize_dec_lt(v_i_50_, v_sz_49_);
if (v___x_53_ == 0)
{
lean_object* v___x_54_; 
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v_b_51_);
return v___x_54_;
}
else
{
lean_object* v_a_55_; lean_object* v_name_56_; uint8_t v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; size_t v___x_60_; size_t v___x_61_; 
v_a_55_ = lean_array_uget_borrowed(v_as_48_, v_i_50_);
v_name_56_ = lean_ctor_get(v_a_55_, 0);
v___x_57_ = l_Lean_Linter_getLinterValue(v_a_55_, v_a_47_);
v___x_58_ = lean_box(v___x_57_);
lean_inc(v_name_56_);
v___x_59_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_56_, v___x_58_, v_b_51_);
v___x_60_ = ((size_t)1ULL);
v___x_61_ = lean_usize_add(v_i_50_, v___x_60_);
v_i_50_ = v___x_61_;
v_b_51_ = v___x_59_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg___boxed(lean_object* v_a_63_, lean_object* v_as_64_, lean_object* v_sz_65_, lean_object* v_i_66_, lean_object* v_b_67_, lean_object* v___y_68_){
_start:
{
size_t v_sz_boxed_69_; size_t v_i_boxed_70_; lean_object* v_res_71_; 
v_sz_boxed_69_ = lean_unbox_usize(v_sz_65_);
lean_dec(v_sz_65_);
v_i_boxed_70_ = lean_unbox_usize(v_i_66_);
lean_dec(v_i_66_);
v_res_71_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg(v_a_63_, v_as_64_, v_sz_boxed_69_, v_i_boxed_70_, v_b_67_);
lean_dec_ref(v_as_64_);
lean_dec_ref(v_a_63_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(lean_object* v_o_72_, lean_object* v___y_73_){
_start:
{
lean_object* v___x_75_; lean_object* v_env_76_; lean_object* v___x_77_; lean_object* v_toEnvExtension_78_; lean_object* v_asyncMode_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v_merged_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_91_; 
v___x_75_ = lean_st_ref_get(v___y_73_);
v_env_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc_ref(v_env_76_);
lean_dec(v___x_75_);
v___x_77_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_78_ = lean_ctor_get(v___x_77_, 0);
v_asyncMode_79_ = lean_ctor_get(v_toEnvExtension_78_, 2);
v___x_80_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_81_ = lean_box(0);
v___x_82_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_80_, v___x_77_, v_env_76_, v_asyncMode_79_, v___x_81_);
v_merged_83_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_91_ == 0)
{
lean_object* v_unused_92_; 
v_unused_92_ = lean_ctor_get(v___x_82_, 1);
lean_dec(v_unused_92_);
v___x_85_ = v___x_82_;
v_isShared_86_ = v_isSharedCheck_91_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_merged_83_);
lean_dec(v___x_82_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_91_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_88_; 
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 1, v_merged_83_);
lean_ctor_set(v___x_85_, 0, v_o_72_);
v___x_88_ = v___x_85_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_o_72_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v_merged_83_);
v___x_88_ = v_reuseFailAlloc_90_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
lean_object* v___x_89_; 
v___x_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
return v___x_89_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg___boxed(lean_object* v_o_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(v_o_93_, v___y_94_);
lean_dec(v___y_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0(lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_options_100_; lean_object* v___x_101_; 
v_options_100_ = lean_ctor_get(v___y_97_, 2);
lean_inc_ref(v_options_100_);
v___x_101_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(v_options_100_, v___y_98_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0___boxed(lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0(v___y_102_, v___y_103_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
return v_res_105_;
}
}
static lean_object* _init_l_Lean_snapshotEnvLinterOptions___closed__0(void){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_106_;
}
}
static lean_object* _init_l_Lean_snapshotEnvLinterOptions___closed__1(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__0, &l_Lean_snapshotEnvLinterOptions___closed__0_once, _init_l_Lean_snapshotEnvLinterOptions___closed__0);
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_snapshotEnvLinterOptions___closed__2(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__1, &l_Lean_snapshotEnvLinterOptions___closed__1_once, _init_l_Lean_snapshotEnvLinterOptions___closed__1);
v___x_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_snapshotEnvLinterOptions(lean_object* v_declName_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_115_ = l_Lean_Linter_envLinterOptionsRef;
v___x_116_ = lean_st_ref_get(v___x_115_);
v___x_117_ = lean_array_get_size(v___x_116_);
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = lean_nat_dec_eq(v___x_117_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v_a_121_; lean_object* v___x_122_; 
v___x_120_ = l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0(v_a_112_, v_a_113_);
v_a_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_a_121_);
lean_dec_ref(v___x_120_);
lean_inc(v_declName_111_);
v___x_122_ = l_Lean_isAutoDeclOrPrivate__Internal___redArg(v_declName_111_, v_a_113_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_174_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_174_ == 0)
{
v___x_125_ = v___x_122_;
v_isShared_126_ = v_isSharedCheck_174_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_122_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_174_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
uint8_t v___x_127_; 
v___x_127_ = lean_unbox(v_a_123_);
lean_dec(v_a_123_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; size_t v_sz_129_; size_t v___x_130_; lean_object* v___x_131_; 
lean_del_object(v___x_125_);
v___x_128_ = lean_box(1);
v_sz_129_ = lean_array_size(v___x_116_);
v___x_130_ = ((size_t)0ULL);
v___x_131_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg(v_a_121_, v___x_116_, v_sz_129_, v___x_130_, v___x_128_);
lean_dec(v___x_116_);
lean_dec(v_a_121_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_161_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_161_ == 0)
{
v___x_134_ = v___x_131_;
v_isShared_135_ = v_isSharedCheck_161_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_131_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_161_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; lean_object* v_env_137_; lean_object* v_nextMacroScope_138_; lean_object* v_ngen_139_; lean_object* v_auxDeclNGen_140_; lean_object* v_traceState_141_; lean_object* v_messages_142_; lean_object* v_infoState_143_; lean_object* v_snapshotTasks_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_159_; 
v___x_136_ = lean_st_ref_take(v_a_113_);
v_env_137_ = lean_ctor_get(v___x_136_, 0);
v_nextMacroScope_138_ = lean_ctor_get(v___x_136_, 1);
v_ngen_139_ = lean_ctor_get(v___x_136_, 2);
v_auxDeclNGen_140_ = lean_ctor_get(v___x_136_, 3);
v_traceState_141_ = lean_ctor_get(v___x_136_, 4);
v_messages_142_ = lean_ctor_get(v___x_136_, 6);
v_infoState_143_ = lean_ctor_get(v___x_136_, 7);
v_snapshotTasks_144_ = lean_ctor_get(v___x_136_, 8);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_159_ == 0)
{
lean_object* v_unused_160_; 
v_unused_160_ = lean_ctor_get(v___x_136_, 5);
lean_dec(v_unused_160_);
v___x_146_ = v___x_136_;
v_isShared_147_ = v_isSharedCheck_159_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_snapshotTasks_144_);
lean_inc(v_infoState_143_);
lean_inc(v_messages_142_);
lean_inc(v_traceState_141_);
lean_inc(v_auxDeclNGen_140_);
lean_inc(v_ngen_139_);
lean_inc(v_nextMacroScope_138_);
lean_inc(v_env_137_);
lean_dec(v___x_136_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_159_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_152_; 
v___x_148_ = l_Lean_Linter_envLinterSnapshotExt;
v___x_149_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_148_, v_env_137_, v_declName_111_, v_a_132_);
v___x_150_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 5, v___x_150_);
lean_ctor_set(v___x_146_, 0, v___x_149_);
v___x_152_ = v___x_146_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_149_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_nextMacroScope_138_);
lean_ctor_set(v_reuseFailAlloc_158_, 2, v_ngen_139_);
lean_ctor_set(v_reuseFailAlloc_158_, 3, v_auxDeclNGen_140_);
lean_ctor_set(v_reuseFailAlloc_158_, 4, v_traceState_141_);
lean_ctor_set(v_reuseFailAlloc_158_, 5, v___x_150_);
lean_ctor_set(v_reuseFailAlloc_158_, 6, v_messages_142_);
lean_ctor_set(v_reuseFailAlloc_158_, 7, v_infoState_143_);
lean_ctor_set(v_reuseFailAlloc_158_, 8, v_snapshotTasks_144_);
v___x_152_ = v_reuseFailAlloc_158_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_156_; 
v___x_153_ = lean_st_ref_set(v_a_113_, v___x_152_);
v___x_154_ = lean_box(0);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 0, v___x_154_);
v___x_156_ = v___x_134_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_154_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
}
else
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_169_; 
lean_dec(v_declName_111_);
v_a_162_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_169_ == 0)
{
v___x_164_ = v___x_131_;
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_131_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
if (v_isShared_165_ == 0)
{
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_a_162_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
else
{
lean_object* v___x_170_; lean_object* v___x_172_; 
lean_dec(v_a_121_);
lean_dec(v___x_116_);
lean_dec(v_declName_111_);
v___x_170_ = lean_box(0);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_170_);
v___x_172_ = v___x_125_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_170_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
else
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_182_; 
lean_dec(v_a_121_);
lean_dec(v___x_116_);
lean_dec(v_declName_111_);
v_a_175_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_182_ == 0)
{
v___x_177_ = v___x_122_;
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_122_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_180_; 
if (v_isShared_178_ == 0)
{
v___x_180_ = v___x_177_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_a_175_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v___x_116_);
lean_dec(v_declName_111_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_snapshotEnvLinterOptions___boxed(lean_object* v_declName_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_snapshotEnvLinterOptions(v_declName_185_, v_a_186_, v_a_187_);
lean_dec(v_a_187_);
lean_dec_ref(v_a_186_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0(lean_object* v_o_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(v_o_190_, v___y_192_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___boxed(lean_object* v_o_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0(v_o_195_, v___y_196_, v___y_197_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1(lean_object* v_a_200_, lean_object* v_as_201_, size_t v_sz_202_, size_t v_i_203_, lean_object* v_b_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg(v_a_200_, v_as_201_, v_sz_202_, v_i_203_, v_b_204_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___boxed(lean_object* v_a_209_, lean_object* v_as_210_, lean_object* v_sz_211_, lean_object* v_i_212_, lean_object* v_b_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
size_t v_sz_boxed_217_; size_t v_i_boxed_218_; lean_object* v_res_219_; 
v_sz_boxed_217_ = lean_unbox_usize(v_sz_211_);
lean_dec(v_sz_211_);
v_i_boxed_218_ = lean_unbox_usize(v_i_212_);
lean_dec(v_i_212_);
v_res_219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1(v_a_209_, v_as_210_, v_sz_boxed_217_, v_i_boxed_218_, v_b_213_, v___y_214_, v___y_215_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec_ref(v_as_210_);
lean_dec_ref(v_a_209_);
return v_res_219_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_AddDecl_0__Lean_isNamespaceName(lean_object* v_x_220_){
_start:
{
if (lean_obj_tag(v_x_220_) == 1)
{
lean_object* v_pre_221_; 
v_pre_221_ = lean_ctor_get(v_x_220_, 0);
if (lean_obj_tag(v_pre_221_) == 0)
{
uint8_t v___x_222_; 
v___x_222_ = 1;
return v___x_222_;
}
else
{
v_x_220_ = v_pre_221_;
goto _start;
}
}
else
{
uint8_t v___x_224_; 
v___x_224_ = 0;
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_isNamespaceName___boxed(lean_object* v_x_225_){
_start:
{
uint8_t v_res_226_; lean_object* v_r_227_; 
v_res_226_ = l___private_Lean_AddDecl_0__Lean_isNamespaceName(v_x_225_);
lean_dec(v_x_225_);
v_r_227_ = lean_box(v_res_226_);
return v_r_227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_registerNamePrefixes_go(lean_object* v_env_228_, lean_object* v_x_229_){
_start:
{
if (lean_obj_tag(v_x_229_) == 1)
{
lean_object* v_pre_230_; uint8_t v___x_231_; 
v_pre_230_ = lean_ctor_get(v_x_229_, 0);
lean_inc(v_pre_230_);
lean_dec_ref_known(v_x_229_, 2);
v___x_231_ = l___private_Lean_AddDecl_0__Lean_isNamespaceName(v_pre_230_);
if (v___x_231_ == 0)
{
lean_dec(v_pre_230_);
return v_env_228_;
}
else
{
lean_object* v___x_232_; 
lean_inc(v_pre_230_);
v___x_232_ = l_Lean_Environment_registerNamespace(v_env_228_, v_pre_230_);
v_env_228_ = v___x_232_;
v_x_229_ = v_pre_230_;
goto _start;
}
}
else
{
lean_dec(v_x_229_);
return v_env_228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(lean_object* v_env_234_, lean_object* v_name_235_){
_start:
{
uint32_t v___y_237_; 
if (lean_obj_tag(v_name_235_) == 1)
{
lean_object* v_str_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_str_241_ = lean_ctor_get(v_name_235_, 1);
v___x_242_ = lean_unsigned_to_nat(0u);
v___x_243_ = lean_string_utf8_byte_size(v_str_241_);
lean_inc_ref(v_str_241_);
v___x_244_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_244_, 0, v_str_241_);
lean_ctor_set(v___x_244_, 1, v___x_242_);
lean_ctor_set(v___x_244_, 2, v___x_243_);
v___x_245_ = l_String_Slice_Pos_get_x3f(v___x_244_, v___x_242_);
lean_dec_ref_known(v___x_244_, 3);
if (lean_obj_tag(v___x_245_) == 0)
{
uint32_t v___x_246_; 
v___x_246_ = 65;
v___y_237_ = v___x_246_;
goto v___jp_236_;
}
else
{
lean_object* v_val_247_; uint32_t v___x_248_; 
v_val_247_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_val_247_);
lean_dec_ref_known(v___x_245_, 1);
v___x_248_ = lean_unbox_uint32(v_val_247_);
lean_dec(v_val_247_);
v___y_237_ = v___x_248_;
goto v___jp_236_;
}
}
else
{
lean_dec(v_name_235_);
return v_env_234_;
}
v___jp_236_:
{
uint32_t v___x_238_; uint8_t v___x_239_; 
v___x_238_ = 95;
v___x_239_ = lean_uint32_dec_eq(v___y_237_, v___x_238_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; 
v___x_240_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes_go(v_env_234_, v_name_235_);
return v___x_240_;
}
else
{
lean_dec(v_name_235_);
return v_env_234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(lean_object* v_name_249_, lean_object* v_decl_250_, lean_object* v_ref_251_){
_start:
{
lean_object* v_defValue_253_; lean_object* v_descr_254_; lean_object* v_deprecation_x3f_255_; lean_object* v___x_256_; uint8_t v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v_defValue_253_ = lean_ctor_get(v_decl_250_, 0);
v_descr_254_ = lean_ctor_get(v_decl_250_, 1);
v_deprecation_x3f_255_ = lean_ctor_get(v_decl_250_, 2);
v___x_256_ = lean_alloc_ctor(1, 0, 1);
v___x_257_ = lean_unbox(v_defValue_253_);
lean_ctor_set_uint8(v___x_256_, 0, v___x_257_);
lean_inc(v_deprecation_x3f_255_);
lean_inc_ref(v_descr_254_);
lean_inc_n(v_name_249_, 2);
v___x_258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_258_, 0, v_name_249_);
lean_ctor_set(v___x_258_, 1, v_ref_251_);
lean_ctor_set(v___x_258_, 2, v___x_256_);
lean_ctor_set(v___x_258_, 3, v_descr_254_);
lean_ctor_set(v___x_258_, 4, v_deprecation_x3f_255_);
v___x_259_ = lean_register_option(v_name_249_, v___x_258_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_267_; 
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_267_ == 0)
{
lean_object* v_unused_268_; 
v_unused_268_ = lean_ctor_get(v___x_259_, 0);
lean_dec(v_unused_268_);
v___x_261_ = v___x_259_;
v_isShared_262_ = v_isSharedCheck_267_;
goto v_resetjp_260_;
}
else
{
lean_dec(v___x_259_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_267_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v___x_265_; 
lean_inc(v_defValue_253_);
v___x_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_263_, 0, v_name_249_);
lean_ctor_set(v___x_263_, 1, v_defValue_253_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_263_);
v___x_265_ = v___x_261_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec(v_name_249_);
v_a_269_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_259_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_259_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_277_, lean_object* v_decl_278_, lean_object* v_ref_279_, lean_object* v_a_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(v_name_277_, v_decl_278_, v_ref_279_);
lean_dec_ref(v_decl_278_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_299_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__2_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_300_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__4_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_301_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__6_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_302_ = l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(v___x_299_, v___x_300_, v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4____boxed(lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_();
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(lean_object* v_msgData_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___x_311_; lean_object* v_env_312_; lean_object* v___x_313_; lean_object* v_mctx_314_; lean_object* v_lctx_315_; lean_object* v_options_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_311_ = lean_st_ref_get(v___y_309_);
v_env_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc_ref(v_env_312_);
lean_dec(v___x_311_);
v___x_313_ = lean_st_ref_get(v___y_307_);
v_mctx_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc_ref(v_mctx_314_);
lean_dec(v___x_313_);
v_lctx_315_ = lean_ctor_get(v___y_306_, 2);
v_options_316_ = lean_ctor_get(v___y_308_, 2);
lean_inc_ref(v_options_316_);
lean_inc_ref(v_lctx_315_);
v___x_317_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_317_, 0, v_env_312_);
lean_ctor_set(v___x_317_, 1, v_mctx_314_);
lean_ctor_set(v___x_317_, 2, v_lctx_315_);
lean_ctor_set(v___x_317_, 3, v_options_316_);
v___x_318_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v_msgData_305_);
v___x_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0___boxed(lean_object* v_msgData_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(v_msgData_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___lam__0(lean_object* v_s_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_350_; 
lean_inc_ref(v_s_327_);
v___x_334_ = l_Lean_MessageData_ofExpr(v_s_327_);
v___x_335_ = l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(v___x_334_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
v_a_336_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_350_ == 0)
{
v___x_338_ = v___x_335_;
v_isShared_339_ = v_isSharedCheck_350_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_335_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_350_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; uint8_t v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_348_; 
v___x_340_ = lean_st_ref_take(v___y_328_);
v___x_341_ = l_Lean_Expr_isSyntheticSorry(v_s_327_);
lean_dec_ref(v_s_327_);
v___x_342_ = lean_box(v___x_341_);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v_a_336_);
v___x_344_ = lean_array_push(v___x_340_, v___x_343_);
v___x_345_ = lean_st_ref_set(v___y_328_, v___x_344_);
v___x_346_ = lean_box(0);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v___x_346_);
v___x_348_ = v___x_338_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___lam__0___boxed(lean_object* v_s_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_warnIfUsesSorry___lam__0(v_s_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
return v_res_358_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(uint8_t v___y_367_, uint8_t v_suppressElabErrors_368_, lean_object* v_x_369_){
_start:
{
if (lean_obj_tag(v_x_369_) == 1)
{
lean_object* v_pre_370_; 
v_pre_370_ = lean_ctor_get(v_x_369_, 0);
switch(lean_obj_tag(v_pre_370_))
{
case 1:
{
lean_object* v_pre_371_; 
v_pre_371_ = lean_ctor_get(v_pre_370_, 0);
switch(lean_obj_tag(v_pre_371_))
{
case 0:
{
lean_object* v_str_372_; lean_object* v_str_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v_str_372_ = lean_ctor_get(v_x_369_, 1);
v_str_373_ = lean_ctor_get(v_pre_370_, 1);
v___x_374_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__0));
v___x_375_ = lean_string_dec_eq(v_str_373_, v___x_374_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_376_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__1));
v___x_377_ = lean_string_dec_eq(v_str_373_, v___x_376_);
if (v___x_377_ == 0)
{
return v___y_367_;
}
else
{
lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__2));
v___x_379_ = lean_string_dec_eq(v_str_372_, v___x_378_);
if (v___x_379_ == 0)
{
return v___y_367_;
}
else
{
return v_suppressElabErrors_368_;
}
}
}
else
{
lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_380_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__3));
v___x_381_ = lean_string_dec_eq(v_str_372_, v___x_380_);
if (v___x_381_ == 0)
{
return v___y_367_;
}
else
{
return v_suppressElabErrors_368_;
}
}
}
case 1:
{
lean_object* v_pre_382_; 
v_pre_382_ = lean_ctor_get(v_pre_371_, 0);
if (lean_obj_tag(v_pre_382_) == 0)
{
lean_object* v_str_383_; lean_object* v_str_384_; lean_object* v_str_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
v_str_383_ = lean_ctor_get(v_x_369_, 1);
v_str_384_ = lean_ctor_get(v_pre_370_, 1);
v_str_385_ = lean_ctor_get(v_pre_371_, 1);
v___x_386_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__4));
v___x_387_ = lean_string_dec_eq(v_str_385_, v___x_386_);
if (v___x_387_ == 0)
{
return v___y_367_;
}
else
{
lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_388_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__5));
v___x_389_ = lean_string_dec_eq(v_str_384_, v___x_388_);
if (v___x_389_ == 0)
{
return v___y_367_;
}
else
{
lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_390_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__6));
v___x_391_ = lean_string_dec_eq(v_str_383_, v___x_390_);
if (v___x_391_ == 0)
{
return v___y_367_;
}
else
{
return v_suppressElabErrors_368_;
}
}
}
}
else
{
return v___y_367_;
}
}
default: 
{
return v___y_367_;
}
}
}
case 0:
{
lean_object* v_str_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v_str_392_ = lean_ctor_get(v_x_369_, 1);
v___x_393_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__7));
v___x_394_ = lean_string_dec_eq(v_str_392_, v___x_393_);
if (v___x_394_ == 0)
{
return v___y_367_;
}
else
{
return v_suppressElabErrors_368_;
}
}
default: 
{
return v___y_367_;
}
}
}
else
{
return v___y_367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed(lean_object* v___y_395_, lean_object* v_suppressElabErrors_396_, lean_object* v_x_397_){
_start:
{
uint8_t v___y_15938__boxed_398_; uint8_t v_suppressElabErrors_boxed_399_; uint8_t v_res_400_; lean_object* v_r_401_; 
v___y_15938__boxed_398_ = lean_unbox(v___y_395_);
v_suppressElabErrors_boxed_399_ = lean_unbox(v_suppressElabErrors_396_);
v_res_400_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(v___y_15938__boxed_398_, v_suppressElabErrors_boxed_399_, v_x_397_);
lean_dec(v_x_397_);
v_r_401_ = lean_box(v_res_400_);
return v_r_401_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0(void){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_402_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0);
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
return v___x_404_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1);
v___x_406_ = lean_unsigned_to_nat(0u);
v___x_407_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
lean_ctor_set(v___x_407_, 2, v___x_406_);
lean_ctor_set(v___x_407_, 3, v___x_406_);
lean_ctor_set(v___x_407_, 4, v___x_405_);
lean_ctor_set(v___x_407_, 5, v___x_405_);
lean_ctor_set(v___x_407_, 6, v___x_405_);
lean_ctor_set(v___x_407_, 7, v___x_405_);
lean_ctor_set(v___x_407_, 8, v___x_405_);
lean_ctor_set(v___x_407_, 9, v___x_405_);
return v___x_407_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_408_ = lean_unsigned_to_nat(32u);
v___x_409_ = lean_mk_empty_array_with_capacity(v___x_408_);
v___x_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
return v___x_410_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4(void){
_start:
{
size_t v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_411_ = ((size_t)5ULL);
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = lean_unsigned_to_nat(32u);
v___x_414_ = lean_mk_empty_array_with_capacity(v___x_413_);
v___x_415_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3);
v___x_416_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v___x_414_);
lean_ctor_set(v___x_416_, 2, v___x_412_);
lean_ctor_set(v___x_416_, 3, v___x_412_);
lean_ctor_set_usize(v___x_416_, 4, v___x_411_);
return v___x_416_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_417_ = lean_box(1);
v___x_418_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_419_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1);
v___x_420_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
lean_ctor_set(v___x_420_, 1, v___x_418_);
lean_ctor_set(v___x_420_, 2, v___x_417_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(lean_object* v_msgData_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v___x_425_; lean_object* v_env_426_; lean_object* v_options_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_425_ = lean_st_ref_get(v___y_423_);
v_env_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc_ref(v_env_426_);
lean_dec(v___x_425_);
v_options_427_ = lean_ctor_get(v___y_422_, 2);
v___x_428_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2);
v___x_429_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5);
lean_inc_ref(v_options_427_);
v___x_430_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_430_, 0, v_env_426_);
lean_ctor_set(v___x_430_, 1, v___x_428_);
lean_ctor_set(v___x_430_, 2, v___x_429_);
lean_ctor_set(v___x_430_, 3, v_options_427_);
v___x_431_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v_msgData_421_);
v___x_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___boxed(lean_object* v_msgData_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msgData_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(lean_object* v_ref_439_, lean_object* v_msgData_440_, uint8_t v_severity_441_, uint8_t v_isSilent_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v___y_447_; uint8_t v___y_448_; uint8_t v___y_449_; lean_object* v___y_450_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_483_; uint8_t v___y_484_; uint8_t v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; uint8_t v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_508_; uint8_t v___y_509_; uint8_t v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; uint8_t v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_519_; lean_object* v___y_520_; uint8_t v___y_521_; lean_object* v___y_522_; uint8_t v___y_523_; lean_object* v___y_524_; uint8_t v___y_525_; uint8_t v___x_530_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; uint8_t v___y_535_; lean_object* v___y_536_; uint8_t v___y_537_; uint8_t v___y_538_; uint8_t v___y_540_; uint8_t v___x_555_; 
v___x_530_ = 2;
v___x_555_ = l_Lean_instBEqMessageSeverity_beq(v_severity_441_, v___x_530_);
if (v___x_555_ == 0)
{
v___y_540_ = v___x_555_;
goto v___jp_539_;
}
else
{
uint8_t v___x_556_; 
lean_inc_ref(v_msgData_440_);
v___x_556_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_440_);
v___y_540_ = v___x_556_;
goto v___jp_539_;
}
v___jp_446_:
{
lean_object* v___x_456_; lean_object* v_currNamespace_457_; lean_object* v_openDecls_458_; lean_object* v_env_459_; lean_object* v_nextMacroScope_460_; lean_object* v_ngen_461_; lean_object* v_auxDeclNGen_462_; lean_object* v_traceState_463_; lean_object* v_cache_464_; lean_object* v_messages_465_; lean_object* v_infoState_466_; lean_object* v_snapshotTasks_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_481_; 
v___x_456_ = lean_st_ref_take(v___y_455_);
v_currNamespace_457_ = lean_ctor_get(v___y_454_, 6);
v_openDecls_458_ = lean_ctor_get(v___y_454_, 7);
v_env_459_ = lean_ctor_get(v___x_456_, 0);
v_nextMacroScope_460_ = lean_ctor_get(v___x_456_, 1);
v_ngen_461_ = lean_ctor_get(v___x_456_, 2);
v_auxDeclNGen_462_ = lean_ctor_get(v___x_456_, 3);
v_traceState_463_ = lean_ctor_get(v___x_456_, 4);
v_cache_464_ = lean_ctor_get(v___x_456_, 5);
v_messages_465_ = lean_ctor_get(v___x_456_, 6);
v_infoState_466_ = lean_ctor_get(v___x_456_, 7);
v_snapshotTasks_467_ = lean_ctor_get(v___x_456_, 8);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_481_ == 0)
{
v___x_469_ = v___x_456_;
v_isShared_470_ = v_isSharedCheck_481_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_snapshotTasks_467_);
lean_inc(v_infoState_466_);
lean_inc(v_messages_465_);
lean_inc(v_cache_464_);
lean_inc(v_traceState_463_);
lean_inc(v_auxDeclNGen_462_);
lean_inc(v_ngen_461_);
lean_inc(v_nextMacroScope_460_);
lean_inc(v_env_459_);
lean_dec(v___x_456_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_481_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_476_; 
lean_inc(v_openDecls_458_);
lean_inc(v_currNamespace_457_);
v___x_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_471_, 0, v_currNamespace_457_);
lean_ctor_set(v___x_471_, 1, v_openDecls_458_);
v___x_472_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
lean_ctor_set(v___x_472_, 1, v___y_447_);
lean_inc_ref(v___y_453_);
lean_inc_ref(v___y_451_);
v___x_473_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_473_, 0, v___y_451_);
lean_ctor_set(v___x_473_, 1, v___y_450_);
lean_ctor_set(v___x_473_, 2, v___y_452_);
lean_ctor_set(v___x_473_, 3, v___y_453_);
lean_ctor_set(v___x_473_, 4, v___x_472_);
lean_ctor_set_uint8(v___x_473_, sizeof(void*)*5, v___y_449_);
lean_ctor_set_uint8(v___x_473_, sizeof(void*)*5 + 1, v___y_448_);
lean_ctor_set_uint8(v___x_473_, sizeof(void*)*5 + 2, v_isSilent_442_);
v___x_474_ = l_Lean_MessageLog_add(v___x_473_, v_messages_465_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 6, v___x_474_);
v___x_476_ = v___x_469_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_env_459_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_nextMacroScope_460_);
lean_ctor_set(v_reuseFailAlloc_480_, 2, v_ngen_461_);
lean_ctor_set(v_reuseFailAlloc_480_, 3, v_auxDeclNGen_462_);
lean_ctor_set(v_reuseFailAlloc_480_, 4, v_traceState_463_);
lean_ctor_set(v_reuseFailAlloc_480_, 5, v_cache_464_);
lean_ctor_set(v_reuseFailAlloc_480_, 6, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_480_, 7, v_infoState_466_);
lean_ctor_set(v_reuseFailAlloc_480_, 8, v_snapshotTasks_467_);
v___x_476_ = v_reuseFailAlloc_480_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_477_ = lean_st_ref_set(v___y_455_, v___x_476_);
v___x_478_ = lean_box(0);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
}
}
v___jp_482_:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_506_; 
v___x_491_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_440_);
v___x_492_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v___x_491_, v___y_443_, v___y_444_);
v_a_493_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_506_ == 0)
{
v___x_495_ = v___x_492_;
v_isShared_496_ = v_isSharedCheck_506_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_492_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_506_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
lean_inc_ref_n(v___y_489_, 2);
v___x_497_ = l_Lean_FileMap_toPosition(v___y_489_, v___y_487_);
lean_dec(v___y_487_);
v___x_498_ = l_Lean_FileMap_toPosition(v___y_489_, v___y_490_);
lean_dec(v___y_490_);
v___x_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
v___x_500_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
if (v___y_488_ == 0)
{
lean_del_object(v___x_495_);
lean_dec_ref(v___y_483_);
v___y_447_ = v_a_493_;
v___y_448_ = v___y_485_;
v___y_449_ = v___y_484_;
v___y_450_ = v___x_497_;
v___y_451_ = v___y_486_;
v___y_452_ = v___x_499_;
v___y_453_ = v___x_500_;
v___y_454_ = v___y_443_;
v___y_455_ = v___y_444_;
goto v___jp_446_;
}
else
{
uint8_t v___x_501_; 
lean_inc(v_a_493_);
v___x_501_ = l_Lean_MessageData_hasTag(v___y_483_, v_a_493_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_504_; 
lean_dec_ref_known(v___x_499_, 1);
lean_dec_ref(v___x_497_);
lean_dec(v_a_493_);
v___x_502_ = lean_box(0);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_502_);
v___x_504_ = v___x_495_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
else
{
lean_del_object(v___x_495_);
v___y_447_ = v_a_493_;
v___y_448_ = v___y_485_;
v___y_449_ = v___y_484_;
v___y_450_ = v___x_497_;
v___y_451_ = v___y_486_;
v___y_452_ = v___x_499_;
v___y_453_ = v___x_500_;
v___y_454_ = v___y_443_;
v___y_455_ = v___y_444_;
goto v___jp_446_;
}
}
}
}
v___jp_507_:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_Syntax_getTailPos_x3f(v___y_512_, v___y_510_);
lean_dec(v___y_512_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_inc(v___y_515_);
v___y_483_ = v___y_508_;
v___y_484_ = v___y_510_;
v___y_485_ = v___y_509_;
v___y_486_ = v___y_511_;
v___y_487_ = v___y_515_;
v___y_488_ = v___y_513_;
v___y_489_ = v___y_514_;
v___y_490_ = v___y_515_;
goto v___jp_482_;
}
else
{
lean_object* v_val_517_; 
v_val_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_val_517_);
lean_dec_ref_known(v___x_516_, 1);
v___y_483_ = v___y_508_;
v___y_484_ = v___y_510_;
v___y_485_ = v___y_509_;
v___y_486_ = v___y_511_;
v___y_487_ = v___y_515_;
v___y_488_ = v___y_513_;
v___y_489_ = v___y_514_;
v___y_490_ = v_val_517_;
goto v___jp_482_;
}
}
v___jp_518_:
{
lean_object* v_ref_526_; lean_object* v___x_527_; 
v_ref_526_ = l_Lean_replaceRef(v_ref_439_, v___y_520_);
v___x_527_ = l_Lean_Syntax_getPos_x3f(v_ref_526_, v___y_521_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v___x_528_; 
v___x_528_ = lean_unsigned_to_nat(0u);
v___y_508_ = v___y_519_;
v___y_509_ = v___y_525_;
v___y_510_ = v___y_521_;
v___y_511_ = v___y_522_;
v___y_512_ = v_ref_526_;
v___y_513_ = v___y_523_;
v___y_514_ = v___y_524_;
v___y_515_ = v___x_528_;
goto v___jp_507_;
}
else
{
lean_object* v_val_529_; 
v_val_529_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_val_529_);
lean_dec_ref_known(v___x_527_, 1);
v___y_508_ = v___y_519_;
v___y_509_ = v___y_525_;
v___y_510_ = v___y_521_;
v___y_511_ = v___y_522_;
v___y_512_ = v_ref_526_;
v___y_513_ = v___y_523_;
v___y_514_ = v___y_524_;
v___y_515_ = v_val_529_;
goto v___jp_507_;
}
}
v___jp_531_:
{
if (v___y_538_ == 0)
{
v___y_519_ = v___y_534_;
v___y_520_ = v___y_532_;
v___y_521_ = v___y_537_;
v___y_522_ = v___y_533_;
v___y_523_ = v___y_535_;
v___y_524_ = v___y_536_;
v___y_525_ = v_severity_441_;
goto v___jp_518_;
}
else
{
v___y_519_ = v___y_534_;
v___y_520_ = v___y_532_;
v___y_521_ = v___y_537_;
v___y_522_ = v___y_533_;
v___y_523_ = v___y_535_;
v___y_524_ = v___y_536_;
v___y_525_ = v___x_530_;
goto v___jp_518_;
}
}
v___jp_539_:
{
if (v___y_540_ == 0)
{
lean_object* v_fileName_541_; lean_object* v_fileMap_542_; lean_object* v_options_543_; lean_object* v_ref_544_; uint8_t v_suppressElabErrors_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___f_548_; uint8_t v___x_549_; uint8_t v___x_550_; 
v_fileName_541_ = lean_ctor_get(v___y_443_, 0);
v_fileMap_542_ = lean_ctor_get(v___y_443_, 1);
v_options_543_ = lean_ctor_get(v___y_443_, 2);
v_ref_544_ = lean_ctor_get(v___y_443_, 5);
v_suppressElabErrors_545_ = lean_ctor_get_uint8(v___y_443_, sizeof(void*)*14 + 1);
v___x_546_ = lean_box(v___y_540_);
v___x_547_ = lean_box(v_suppressElabErrors_545_);
v___f_548_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed), 3, 2);
lean_closure_set(v___f_548_, 0, v___x_546_);
lean_closure_set(v___f_548_, 1, v___x_547_);
v___x_549_ = 1;
v___x_550_ = l_Lean_instBEqMessageSeverity_beq(v_severity_441_, v___x_549_);
if (v___x_550_ == 0)
{
v___y_532_ = v_ref_544_;
v___y_533_ = v_fileName_541_;
v___y_534_ = v___f_548_;
v___y_535_ = v_suppressElabErrors_545_;
v___y_536_ = v_fileMap_542_;
v___y_537_ = v___y_540_;
v___y_538_ = v___x_550_;
goto v___jp_531_;
}
else
{
lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_551_ = l_Lean_warningAsError;
v___x_552_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_543_, v___x_551_);
v___y_532_ = v_ref_544_;
v___y_533_ = v_fileName_541_;
v___y_534_ = v___f_548_;
v___y_535_ = v_suppressElabErrors_545_;
v___y_536_ = v_fileMap_542_;
v___y_537_ = v___y_540_;
v___y_538_ = v___x_552_;
goto v___jp_531_;
}
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; 
lean_dec_ref(v_msgData_440_);
v___x_553_ = lean_box(0);
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
return v___x_554_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___boxed(lean_object* v_ref_557_, lean_object* v_msgData_558_, lean_object* v_severity_559_, lean_object* v_isSilent_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
uint8_t v_severity_boxed_564_; uint8_t v_isSilent_boxed_565_; lean_object* v_res_566_; 
v_severity_boxed_564_ = lean_unbox(v_severity_559_);
v_isSilent_boxed_565_ = lean_unbox(v_isSilent_560_);
v_res_566_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_557_, v_msgData_558_, v_severity_boxed_564_, v_isSilent_boxed_565_, v___y_561_, v___y_562_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v_ref_557_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(lean_object* v_msgData_567_, uint8_t v_severity_568_, uint8_t v_isSilent_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_ref_573_; lean_object* v___x_574_; 
v_ref_573_ = lean_ctor_get(v___y_570_, 5);
v___x_574_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_573_, v_msgData_567_, v_severity_568_, v_isSilent_569_, v___y_570_, v___y_571_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4___boxed(lean_object* v_msgData_575_, lean_object* v_severity_576_, lean_object* v_isSilent_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
uint8_t v_severity_boxed_581_; uint8_t v_isSilent_boxed_582_; lean_object* v_res_583_; 
v_severity_boxed_581_ = lean_unbox(v_severity_576_);
v_isSilent_boxed_582_ = lean_unbox(v_isSilent_577_);
v_res_583_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_575_, v_severity_boxed_581_, v_isSilent_boxed_582_, v___y_578_, v___y_579_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(lean_object* v_msgData_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
uint8_t v___x_588_; uint8_t v___x_589_; lean_object* v___x_590_; 
v___x_588_ = 1;
v___x_589_ = 0;
v___x_590_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_584_, v___x_588_, v___x_589_, v___y_585_, v___y_586_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2___boxed(lean_object* v_msgData_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v_msgData_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(lean_object* v_as_599_, size_t v_sz_600_, size_t v_i_601_, lean_object* v_b_602_){
_start:
{
uint8_t v___x_603_; 
v___x_603_ = lean_usize_dec_lt(v_i_601_, v_sz_600_);
if (v___x_603_ == 0)
{
lean_inc_ref(v_b_602_);
return v_b_602_;
}
else
{
lean_object* v_a_604_; lean_object* v_fst_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v_a_604_ = lean_array_uget_borrowed(v_as_599_, v_i_601_);
v_fst_605_ = lean_ctor_get(v_a_604_, 0);
v___x_606_ = lean_box(0);
v___x_607_ = lean_unbox(v_fst_605_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; size_t v___x_609_; size_t v___x_610_; 
v___x_608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___closed__0));
v___x_609_ = ((size_t)1ULL);
v___x_610_ = lean_usize_add(v_i_601_, v___x_609_);
v_i_601_ = v___x_610_;
v_b_602_ = v___x_608_;
goto _start;
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
lean_inc(v_a_604_);
v___x_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_612_, 0, v_a_604_);
v___x_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v___x_606_);
return v___x_614_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___boxed(lean_object* v_as_615_, lean_object* v_sz_616_, lean_object* v_i_617_, lean_object* v_b_618_){
_start:
{
size_t v_sz_boxed_619_; size_t v_i_boxed_620_; lean_object* v_res_621_; 
v_sz_boxed_619_ = lean_unbox_usize(v_sz_616_);
lean_dec(v_sz_616_);
v_i_boxed_620_ = lean_unbox_usize(v_i_617_);
lean_dec(v_i_617_);
v_res_621_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v_as_615_, v_sz_boxed_619_, v_i_boxed_620_, v_b_618_);
lean_dec_ref(v_b_618_);
lean_dec_ref(v_as_615_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(lean_object* v_fn_622_, lean_object* v_e_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_Expr_getSorry_x3f(v_e_623_);
if (lean_obj_tag(v___x_630_) == 1)
{
lean_object* v_val_631_; lean_object* v___x_632_; 
v_val_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_val_631_);
lean_dec_ref_known(v___x_630_, 1);
lean_inc(v___y_628_);
lean_inc_ref(v___y_627_);
lean_inc(v___y_626_);
lean_inc_ref(v___y_625_);
lean_inc(v___y_624_);
v___x_632_ = lean_apply_7(v_fn_622_, v_val_631_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, lean_box(0));
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_641_; 
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_641_ == 0)
{
lean_object* v_unused_642_; 
v_unused_642_ = lean_ctor_get(v___x_632_, 0);
lean_dec(v_unused_642_);
v___x_634_ = v___x_632_;
v_isShared_635_ = v_isSharedCheck_641_;
goto v_resetjp_633_;
}
else
{
lean_dec(v___x_632_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_641_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
uint8_t v___x_636_; lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_636_ = 0;
v___x_637_ = lean_box(v___x_636_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v___x_637_);
v___x_639_ = v___x_634_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
v_a_643_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_632_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_632_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
else
{
uint8_t v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec(v___x_630_);
lean_dec_ref(v_fn_622_);
v___x_651_ = 1;
v___x_652_ = lean_box(v___x_651_);
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
return v___x_653_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed(lean_object* v_fn_654_, lean_object* v_e_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(v_fn_654_, v_e_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v_e_655_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_object* v_00_u03b1_663_, lean_object* v_x_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_apply_1(v_x_664_, lean_box(0));
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v_00_u03b1_673_, lean_object* v_x_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(v_00_u03b1_673_, v_x_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(lean_object* v_k_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v_b_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v___x_691_; 
lean_inc(v___y_689_);
lean_inc_ref(v___y_688_);
lean_inc(v___y_687_);
lean_inc_ref(v___y_686_);
lean_inc(v___y_684_);
lean_inc(v___y_683_);
v___x_691_ = lean_apply_8(v_k_682_, v_b_685_, v___y_683_, v___y_684_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, lean_box(0));
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed(lean_object* v_k_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v_b_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(v_k_692_, v___y_693_, v___y_694_, v_b_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_694_);
lean_dec(v___y_693_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(lean_object* v_name_702_, lean_object* v_type_703_, lean_object* v_val_704_, lean_object* v_k_705_, uint8_t v_nondep_706_, uint8_t v_kind_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v___f_715_; lean_object* v___x_716_; 
lean_inc(v___y_709_);
lean_inc(v___y_708_);
v___f_715_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_715_, 0, v_k_705_);
lean_closure_set(v___f_715_, 1, v___y_708_);
lean_closure_set(v___f_715_, 2, v___y_709_);
v___x_716_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_702_, v_type_703_, v_val_704_, v___f_715_, v_nondep_706_, v_kind_707_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
if (lean_obj_tag(v___x_716_) == 0)
{
return v___x_716_;
}
else
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v___x_716_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg___boxed(lean_object* v_name_725_, lean_object* v_type_726_, lean_object* v_val_727_, lean_object* v_k_728_, lean_object* v_nondep_729_, lean_object* v_kind_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
uint8_t v_nondep_boxed_738_; uint8_t v_kind_boxed_739_; lean_object* v_res_740_; 
v_nondep_boxed_738_ = lean_unbox(v_nondep_729_);
v_kind_boxed_739_ = lean_unbox(v_kind_730_);
v_res_740_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_725_, v_type_726_, v_val_727_, v_k_728_, v_nondep_boxed_738_, v_kind_boxed_739_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec(v___y_731_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed(lean_object* v_fvars_741_, lean_object* v_f_742_, lean_object* v_body_743_, lean_object* v_x_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(v_fvars_741_, v_f_742_, v_body_743_, v_x_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec(v___y_745_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(lean_object* v_f_753_, lean_object* v_fvars_754_, lean_object* v_a_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
if (lean_obj_tag(v_a_755_) == 8)
{
lean_object* v_declName_763_; lean_object* v_type_764_; lean_object* v_value_765_; lean_object* v_body_766_; lean_object* v_d_767_; lean_object* v___x_768_; 
v_declName_763_ = lean_ctor_get(v_a_755_, 0);
lean_inc(v_declName_763_);
v_type_764_ = lean_ctor_get(v_a_755_, 1);
lean_inc_ref(v_type_764_);
v_value_765_ = lean_ctor_get(v_a_755_, 2);
lean_inc_ref(v_value_765_);
v_body_766_ = lean_ctor_get(v_a_755_, 3);
lean_inc_ref(v_body_766_);
lean_dec_ref_known(v_a_755_, 4);
v_d_767_ = lean_expr_instantiate_rev(v_type_764_, v_fvars_754_);
lean_dec_ref(v_type_764_);
lean_inc_ref(v_f_753_);
lean_inc(v___y_761_);
lean_inc_ref(v___y_760_);
lean_inc(v___y_759_);
lean_inc_ref(v___y_758_);
lean_inc(v___y_757_);
lean_inc(v___y_756_);
lean_inc_ref(v_d_767_);
v___x_768_ = lean_apply_8(v_f_753_, v_d_767_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, lean_box(0));
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_v_769_; lean_object* v___x_770_; 
lean_dec_ref_known(v___x_768_, 1);
v_v_769_ = lean_expr_instantiate_rev(v_value_765_, v_fvars_754_);
lean_dec_ref(v_value_765_);
lean_inc_ref(v_f_753_);
lean_inc(v___y_761_);
lean_inc_ref(v___y_760_);
lean_inc(v___y_759_);
lean_inc_ref(v___y_758_);
lean_inc(v___y_757_);
lean_inc(v___y_756_);
lean_inc_ref(v_v_769_);
v___x_770_ = lean_apply_8(v_f_753_, v_v_769_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, lean_box(0));
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v___f_771_; uint8_t v___x_772_; uint8_t v___x_773_; lean_object* v___x_774_; 
lean_dec_ref_known(v___x_770_, 1);
v___f_771_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed), 11, 3);
lean_closure_set(v___f_771_, 0, v_fvars_754_);
lean_closure_set(v___f_771_, 1, v_f_753_);
lean_closure_set(v___f_771_, 2, v_body_766_);
v___x_772_ = 0;
v___x_773_ = 0;
v___x_774_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_declName_763_, v_d_767_, v_v_769_, v___f_771_, v___x_772_, v___x_773_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
return v___x_774_;
}
else
{
lean_dec_ref(v_v_769_);
lean_dec_ref(v_d_767_);
lean_dec_ref(v_body_766_);
lean_dec(v_declName_763_);
lean_dec_ref(v_fvars_754_);
lean_dec_ref(v_f_753_);
return v___x_770_;
}
}
else
{
lean_dec_ref(v_d_767_);
lean_dec_ref(v_body_766_);
lean_dec_ref(v_value_765_);
lean_dec(v_declName_763_);
lean_dec_ref(v_fvars_754_);
lean_dec_ref(v_f_753_);
return v___x_768_;
}
}
else
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = lean_expr_instantiate_rev(v_a_755_, v_fvars_754_);
lean_dec_ref(v_fvars_754_);
lean_dec_ref(v_a_755_);
lean_inc(v___y_761_);
lean_inc_ref(v___y_760_);
lean_inc(v___y_759_);
lean_inc_ref(v___y_758_);
lean_inc(v___y_757_);
lean_inc(v___y_756_);
v___x_776_ = lean_apply_8(v_f_753_, v___x_775_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, lean_box(0));
return v___x_776_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(lean_object* v_fvars_777_, lean_object* v_f_778_, lean_object* v_body_779_, lean_object* v_x_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = lean_array_push(v_fvars_777_, v_x_780_);
v___x_789_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_778_, v___x_788_, v_body_779_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___boxed(lean_object* v_f_790_, lean_object* v_fvars_791_, lean_object* v_a_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_790_, v_fvars_791_, v_a_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec(v___y_793_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(lean_object* v_f_803_, lean_object* v_e_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_813_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_803_, v___x_812_, v_e_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___boxed(lean_object* v_f_814_, lean_object* v_e_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v_f_814_, v_e_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___y_817_);
lean_dec(v___y_816_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(lean_object* v_name_824_, uint8_t v_bi_825_, lean_object* v_type_826_, lean_object* v_k_827_, uint8_t v_kind_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___f_836_; lean_object* v___x_837_; 
lean_inc(v___y_830_);
lean_inc(v___y_829_);
v___f_836_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_836_, 0, v_k_827_);
lean_closure_set(v___f_836_, 1, v___y_829_);
lean_closure_set(v___f_836_, 2, v___y_830_);
v___x_837_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_824_, v_bi_825_, v_type_826_, v___f_836_, v_kind_828_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
if (lean_obj_tag(v___x_837_) == 0)
{
return v___x_837_;
}
else
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_837_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_837_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___boxed(lean_object* v_name_846_, lean_object* v_bi_847_, lean_object* v_type_848_, lean_object* v_k_849_, lean_object* v_kind_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
uint8_t v_bi_boxed_858_; uint8_t v_kind_boxed_859_; lean_object* v_res_860_; 
v_bi_boxed_858_ = lean_unbox(v_bi_847_);
v_kind_boxed_859_ = lean_unbox(v_kind_850_);
v_res_860_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_846_, v_bi_boxed_858_, v_type_848_, v_k_849_, v_kind_boxed_859_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec(v___y_851_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed(lean_object* v_fvars_861_, lean_object* v_f_862_, lean_object* v_body_863_, lean_object* v_x_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(v_fvars_861_, v_f_862_, v_body_863_, v_x_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec(v___y_865_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(lean_object* v_f_873_, lean_object* v_fvars_874_, lean_object* v_a_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
if (lean_obj_tag(v_a_875_) == 7)
{
lean_object* v_binderName_883_; lean_object* v_binderType_884_; lean_object* v_body_885_; uint8_t v_binderInfo_886_; lean_object* v_d_887_; lean_object* v___x_888_; 
v_binderName_883_ = lean_ctor_get(v_a_875_, 0);
lean_inc(v_binderName_883_);
v_binderType_884_ = lean_ctor_get(v_a_875_, 1);
lean_inc_ref(v_binderType_884_);
v_body_885_ = lean_ctor_get(v_a_875_, 2);
lean_inc_ref(v_body_885_);
v_binderInfo_886_ = lean_ctor_get_uint8(v_a_875_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_875_, 3);
v_d_887_ = lean_expr_instantiate_rev(v_binderType_884_, v_fvars_874_);
lean_dec_ref(v_binderType_884_);
lean_inc_ref(v_f_873_);
lean_inc(v___y_881_);
lean_inc_ref(v___y_880_);
lean_inc(v___y_879_);
lean_inc_ref(v___y_878_);
lean_inc(v___y_877_);
lean_inc(v___y_876_);
lean_inc_ref(v_d_887_);
v___x_888_ = lean_apply_8(v_f_873_, v_d_887_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, lean_box(0));
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v___f_889_; uint8_t v___x_890_; lean_object* v___x_891_; 
lean_dec_ref_known(v___x_888_, 1);
v___f_889_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed), 11, 3);
lean_closure_set(v___f_889_, 0, v_fvars_874_);
lean_closure_set(v___f_889_, 1, v_f_873_);
lean_closure_set(v___f_889_, 2, v_body_885_);
v___x_890_ = 0;
v___x_891_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_883_, v_binderInfo_886_, v_d_887_, v___f_889_, v___x_890_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
return v___x_891_;
}
else
{
lean_dec_ref(v_d_887_);
lean_dec_ref(v_body_885_);
lean_dec(v_binderName_883_);
lean_dec_ref(v_fvars_874_);
lean_dec_ref(v_f_873_);
return v___x_888_;
}
}
else
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = lean_expr_instantiate_rev(v_a_875_, v_fvars_874_);
lean_dec_ref(v_fvars_874_);
lean_dec_ref(v_a_875_);
lean_inc(v___y_881_);
lean_inc_ref(v___y_880_);
lean_inc(v___y_879_);
lean_inc_ref(v___y_878_);
lean_inc(v___y_877_);
lean_inc(v___y_876_);
v___x_893_ = lean_apply_8(v_f_873_, v___x_892_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, lean_box(0));
return v___x_893_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(lean_object* v_fvars_894_, lean_object* v_f_895_, lean_object* v_body_896_, lean_object* v_x_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = lean_array_push(v_fvars_894_, v_x_897_);
v___x_906_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_895_, v___x_905_, v_body_896_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___boxed(lean_object* v_f_907_, lean_object* v_fvars_908_, lean_object* v_a_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_907_, v_fvars_908_, v_a_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec(v___y_910_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(lean_object* v_f_918_, lean_object* v_e_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_928_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_918_, v___x_927_, v_e_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10___boxed(lean_object* v_f_929_, lean_object* v_e_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v_f_929_, v_e_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec(v___y_931_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed(lean_object* v_fvars_939_, lean_object* v_f_940_, lean_object* v_body_941_, lean_object* v_x_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(v_fvars_939_, v_f_940_, v_body_941_, v_x_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec(v___y_943_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(lean_object* v_f_951_, lean_object* v_fvars_952_, lean_object* v_a_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
if (lean_obj_tag(v_a_953_) == 6)
{
lean_object* v_binderName_961_; lean_object* v_binderType_962_; lean_object* v_body_963_; uint8_t v_binderInfo_964_; lean_object* v_d_965_; lean_object* v___x_966_; 
v_binderName_961_ = lean_ctor_get(v_a_953_, 0);
lean_inc(v_binderName_961_);
v_binderType_962_ = lean_ctor_get(v_a_953_, 1);
lean_inc_ref(v_binderType_962_);
v_body_963_ = lean_ctor_get(v_a_953_, 2);
lean_inc_ref(v_body_963_);
v_binderInfo_964_ = lean_ctor_get_uint8(v_a_953_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_953_, 3);
v_d_965_ = lean_expr_instantiate_rev(v_binderType_962_, v_fvars_952_);
lean_dec_ref(v_binderType_962_);
lean_inc_ref(v_f_951_);
lean_inc(v___y_959_);
lean_inc_ref(v___y_958_);
lean_inc(v___y_957_);
lean_inc_ref(v___y_956_);
lean_inc(v___y_955_);
lean_inc(v___y_954_);
lean_inc_ref(v_d_965_);
v___x_966_ = lean_apply_8(v_f_951_, v_d_965_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, lean_box(0));
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v___f_967_; uint8_t v___x_968_; lean_object* v___x_969_; 
lean_dec_ref_known(v___x_966_, 1);
v___f_967_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed), 11, 3);
lean_closure_set(v___f_967_, 0, v_fvars_952_);
lean_closure_set(v___f_967_, 1, v_f_951_);
lean_closure_set(v___f_967_, 2, v_body_963_);
v___x_968_ = 0;
v___x_969_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_961_, v_binderInfo_964_, v_d_965_, v___f_967_, v___x_968_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
return v___x_969_;
}
else
{
lean_dec_ref(v_d_965_);
lean_dec_ref(v_body_963_);
lean_dec(v_binderName_961_);
lean_dec_ref(v_fvars_952_);
lean_dec_ref(v_f_951_);
return v___x_966_;
}
}
else
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_expr_instantiate_rev(v_a_953_, v_fvars_952_);
lean_dec_ref(v_fvars_952_);
lean_dec_ref(v_a_953_);
lean_inc(v___y_959_);
lean_inc_ref(v___y_958_);
lean_inc(v___y_957_);
lean_inc_ref(v___y_956_);
lean_inc(v___y_955_);
lean_inc(v___y_954_);
v___x_971_ = lean_apply_8(v_f_951_, v___x_970_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, lean_box(0));
return v___x_971_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(lean_object* v_fvars_972_, lean_object* v_f_973_, lean_object* v_body_974_, lean_object* v_x_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = lean_array_push(v_fvars_972_, v_x_975_);
v___x_984_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_973_, v___x_983_, v_body_974_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___boxed(lean_object* v_f_985_, lean_object* v_fvars_986_, lean_object* v_a_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_985_, v_fvars_986_, v_a_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec(v___y_988_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(lean_object* v_f_996_, lean_object* v_e_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_1006_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_996_, v___x_1005_, v_e_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11___boxed(lean_object* v_f_1007_, lean_object* v_e_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v_f_1007_, v_e_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec(v___y_1009_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(lean_object* v_a_1017_, lean_object* v_x_1018_){
_start:
{
if (lean_obj_tag(v_x_1018_) == 0)
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_box(0);
return v___x_1019_;
}
else
{
lean_object* v_key_1020_; lean_object* v_value_1021_; lean_object* v_tail_1022_; uint8_t v___x_1023_; 
v_key_1020_ = lean_ctor_get(v_x_1018_, 0);
v_value_1021_ = lean_ctor_get(v_x_1018_, 1);
v_tail_1022_ = lean_ctor_get(v_x_1018_, 2);
v___x_1023_ = lean_expr_eqv(v_key_1020_, v_a_1017_);
if (v___x_1023_ == 0)
{
v_x_1018_ = v_tail_1022_;
goto _start;
}
else
{
lean_object* v___x_1025_; 
lean_inc(v_value_1021_);
v___x_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1025_, 0, v_value_1021_);
return v___x_1025_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_a_1026_, lean_object* v_x_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1026_, v_x_1027_);
lean_dec(v_x_1027_);
lean_dec_ref(v_a_1026_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_m_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v_buckets_1031_; lean_object* v___x_1032_; uint64_t v___x_1033_; uint64_t v___x_1034_; uint64_t v___x_1035_; uint64_t v_fold_1036_; uint64_t v___x_1037_; uint64_t v___x_1038_; uint64_t v___x_1039_; size_t v___x_1040_; size_t v___x_1041_; size_t v___x_1042_; size_t v___x_1043_; size_t v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v_buckets_1031_ = lean_ctor_get(v_m_1029_, 1);
v___x_1032_ = lean_array_get_size(v_buckets_1031_);
v___x_1033_ = l_Lean_Expr_hash(v_a_1030_);
v___x_1034_ = 32ULL;
v___x_1035_ = lean_uint64_shift_right(v___x_1033_, v___x_1034_);
v_fold_1036_ = lean_uint64_xor(v___x_1033_, v___x_1035_);
v___x_1037_ = 16ULL;
v___x_1038_ = lean_uint64_shift_right(v_fold_1036_, v___x_1037_);
v___x_1039_ = lean_uint64_xor(v_fold_1036_, v___x_1038_);
v___x_1040_ = lean_uint64_to_usize(v___x_1039_);
v___x_1041_ = lean_usize_of_nat(v___x_1032_);
v___x_1042_ = ((size_t)1ULL);
v___x_1043_ = lean_usize_sub(v___x_1041_, v___x_1042_);
v___x_1044_ = lean_usize_land(v___x_1040_, v___x_1043_);
v___x_1045_ = lean_array_uget_borrowed(v_buckets_1031_, v___x_1044_);
v___x_1046_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1030_, v___x_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_m_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1047_, v_a_1048_);
lean_dec_ref(v_a_1048_);
lean_dec_ref(v_m_1047_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_object* v_00_u03b1_1050_, lean_object* v_x_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = lean_apply_1(v_x_1051_, lean_box(0));
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0___boxed(lean_object* v_00_u03b1_1060_, lean_object* v_x_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(v_00_u03b1_1060_, v_x_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(lean_object* v_x_1069_, lean_object* v_x_1070_){
_start:
{
if (lean_obj_tag(v_x_1070_) == 0)
{
return v_x_1069_;
}
else
{
lean_object* v_key_1071_; lean_object* v_value_1072_; lean_object* v_tail_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1096_; 
v_key_1071_ = lean_ctor_get(v_x_1070_, 0);
v_value_1072_ = lean_ctor_get(v_x_1070_, 1);
v_tail_1073_ = lean_ctor_get(v_x_1070_, 2);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_x_1070_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1075_ = v_x_1070_;
v_isShared_1076_ = v_isSharedCheck_1096_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_tail_1073_);
lean_inc(v_value_1072_);
lean_inc(v_key_1071_);
lean_dec(v_x_1070_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1096_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; uint64_t v___x_1078_; uint64_t v___x_1079_; uint64_t v___x_1080_; uint64_t v_fold_1081_; uint64_t v___x_1082_; uint64_t v___x_1083_; uint64_t v___x_1084_; size_t v___x_1085_; size_t v___x_1086_; size_t v___x_1087_; size_t v___x_1088_; size_t v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1077_ = lean_array_get_size(v_x_1069_);
v___x_1078_ = l_Lean_Expr_hash(v_key_1071_);
v___x_1079_ = 32ULL;
v___x_1080_ = lean_uint64_shift_right(v___x_1078_, v___x_1079_);
v_fold_1081_ = lean_uint64_xor(v___x_1078_, v___x_1080_);
v___x_1082_ = 16ULL;
v___x_1083_ = lean_uint64_shift_right(v_fold_1081_, v___x_1082_);
v___x_1084_ = lean_uint64_xor(v_fold_1081_, v___x_1083_);
v___x_1085_ = lean_uint64_to_usize(v___x_1084_);
v___x_1086_ = lean_usize_of_nat(v___x_1077_);
v___x_1087_ = ((size_t)1ULL);
v___x_1088_ = lean_usize_sub(v___x_1086_, v___x_1087_);
v___x_1089_ = lean_usize_land(v___x_1085_, v___x_1088_);
v___x_1090_ = lean_array_uget_borrowed(v_x_1069_, v___x_1089_);
lean_inc(v___x_1090_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 2, v___x_1090_);
v___x_1092_ = v___x_1075_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_key_1071_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_value_1072_);
lean_ctor_set(v_reuseFailAlloc_1095_, 2, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_array_uset(v_x_1069_, v___x_1089_, v___x_1092_);
v_x_1069_ = v___x_1093_;
v_x_1070_ = v_tail_1073_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(lean_object* v_i_1097_, lean_object* v_source_1098_, lean_object* v_target_1099_){
_start:
{
lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1100_ = lean_array_get_size(v_source_1098_);
v___x_1101_ = lean_nat_dec_lt(v_i_1097_, v___x_1100_);
if (v___x_1101_ == 0)
{
lean_dec_ref(v_source_1098_);
lean_dec(v_i_1097_);
return v_target_1099_;
}
else
{
lean_object* v_es_1102_; lean_object* v___x_1103_; lean_object* v_source_1104_; lean_object* v_target_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v_es_1102_ = lean_array_fget(v_source_1098_, v_i_1097_);
v___x_1103_ = lean_box(0);
v_source_1104_ = lean_array_fset(v_source_1098_, v_i_1097_, v___x_1103_);
v_target_1105_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_target_1099_, v_es_1102_);
v___x_1106_ = lean_unsigned_to_nat(1u);
v___x_1107_ = lean_nat_add(v_i_1097_, v___x_1106_);
lean_dec(v_i_1097_);
v_i_1097_ = v___x_1107_;
v_source_1098_ = v_source_1104_;
v_target_1099_ = v_target_1105_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(lean_object* v_data_1109_){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v_nbuckets_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1110_ = lean_array_get_size(v_data_1109_);
v___x_1111_ = lean_unsigned_to_nat(2u);
v_nbuckets_1112_ = lean_nat_mul(v___x_1110_, v___x_1111_);
v___x_1113_ = lean_unsigned_to_nat(0u);
v___x_1114_ = lean_box(0);
v___x_1115_ = lean_mk_array(v_nbuckets_1112_, v___x_1114_);
v___x_1116_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v___x_1113_, v_data_1109_, v___x_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(lean_object* v_a_1117_, lean_object* v_b_1118_, lean_object* v_x_1119_){
_start:
{
if (lean_obj_tag(v_x_1119_) == 0)
{
lean_dec(v_b_1118_);
lean_dec_ref(v_a_1117_);
return v_x_1119_;
}
else
{
lean_object* v_key_1120_; lean_object* v_value_1121_; lean_object* v_tail_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1134_; 
v_key_1120_ = lean_ctor_get(v_x_1119_, 0);
v_value_1121_ = lean_ctor_get(v_x_1119_, 1);
v_tail_1122_ = lean_ctor_get(v_x_1119_, 2);
v_isSharedCheck_1134_ = !lean_is_exclusive(v_x_1119_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1124_ = v_x_1119_;
v_isShared_1125_ = v_isSharedCheck_1134_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_tail_1122_);
lean_inc(v_value_1121_);
lean_inc(v_key_1120_);
lean_dec(v_x_1119_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1134_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
uint8_t v___x_1126_; 
v___x_1126_ = lean_expr_eqv(v_key_1120_, v_a_1117_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; lean_object* v___x_1129_; 
v___x_1127_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1117_, v_b_1118_, v_tail_1122_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 2, v___x_1127_);
v___x_1129_ = v___x_1124_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_key_1120_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_value_1121_);
lean_ctor_set(v_reuseFailAlloc_1130_, 2, v___x_1127_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
else
{
lean_object* v___x_1132_; 
lean_dec(v_value_1121_);
lean_dec(v_key_1120_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 1, v_b_1118_);
lean_ctor_set(v___x_1124_, 0, v_a_1117_);
v___x_1132_ = v___x_1124_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1117_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_b_1118_);
lean_ctor_set(v_reuseFailAlloc_1133_, 2, v_tail_1122_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(lean_object* v_a_1135_, lean_object* v_x_1136_){
_start:
{
if (lean_obj_tag(v_x_1136_) == 0)
{
uint8_t v___x_1137_; 
v___x_1137_ = 0;
return v___x_1137_;
}
else
{
lean_object* v_key_1138_; lean_object* v_tail_1139_; uint8_t v___x_1140_; 
v_key_1138_ = lean_ctor_get(v_x_1136_, 0);
v_tail_1139_ = lean_ctor_get(v_x_1136_, 2);
v___x_1140_ = lean_expr_eqv(v_key_1138_, v_a_1135_);
if (v___x_1140_ == 0)
{
v_x_1136_ = v_tail_1139_;
goto _start;
}
else
{
return v___x_1140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg___boxed(lean_object* v_a_1142_, lean_object* v_x_1143_){
_start:
{
uint8_t v_res_1144_; lean_object* v_r_1145_; 
v_res_1144_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1142_, v_x_1143_);
lean_dec(v_x_1143_);
lean_dec_ref(v_a_1142_);
v_r_1145_ = lean_box(v_res_1144_);
return v_r_1145_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(lean_object* v_m_1146_, lean_object* v_a_1147_, lean_object* v_b_1148_){
_start:
{
lean_object* v_size_1149_; lean_object* v_buckets_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1193_; 
v_size_1149_ = lean_ctor_get(v_m_1146_, 0);
v_buckets_1150_ = lean_ctor_get(v_m_1146_, 1);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_m_1146_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1152_ = v_m_1146_;
v_isShared_1153_ = v_isSharedCheck_1193_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_buckets_1150_);
lean_inc(v_size_1149_);
lean_dec(v_m_1146_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1193_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; uint64_t v___x_1155_; uint64_t v___x_1156_; uint64_t v___x_1157_; uint64_t v_fold_1158_; uint64_t v___x_1159_; uint64_t v___x_1160_; uint64_t v___x_1161_; size_t v___x_1162_; size_t v___x_1163_; size_t v___x_1164_; size_t v___x_1165_; size_t v___x_1166_; lean_object* v_bkt_1167_; uint8_t v___x_1168_; 
v___x_1154_ = lean_array_get_size(v_buckets_1150_);
v___x_1155_ = l_Lean_Expr_hash(v_a_1147_);
v___x_1156_ = 32ULL;
v___x_1157_ = lean_uint64_shift_right(v___x_1155_, v___x_1156_);
v_fold_1158_ = lean_uint64_xor(v___x_1155_, v___x_1157_);
v___x_1159_ = 16ULL;
v___x_1160_ = lean_uint64_shift_right(v_fold_1158_, v___x_1159_);
v___x_1161_ = lean_uint64_xor(v_fold_1158_, v___x_1160_);
v___x_1162_ = lean_uint64_to_usize(v___x_1161_);
v___x_1163_ = lean_usize_of_nat(v___x_1154_);
v___x_1164_ = ((size_t)1ULL);
v___x_1165_ = lean_usize_sub(v___x_1163_, v___x_1164_);
v___x_1166_ = lean_usize_land(v___x_1162_, v___x_1165_);
v_bkt_1167_ = lean_array_uget_borrowed(v_buckets_1150_, v___x_1166_);
v___x_1168_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1147_, v_bkt_1167_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; lean_object* v_size_x27_1170_; lean_object* v___x_1171_; lean_object* v_buckets_x27_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1169_ = lean_unsigned_to_nat(1u);
v_size_x27_1170_ = lean_nat_add(v_size_1149_, v___x_1169_);
lean_dec(v_size_1149_);
lean_inc(v_bkt_1167_);
v___x_1171_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1171_, 0, v_a_1147_);
lean_ctor_set(v___x_1171_, 1, v_b_1148_);
lean_ctor_set(v___x_1171_, 2, v_bkt_1167_);
v_buckets_x27_1172_ = lean_array_uset(v_buckets_1150_, v___x_1166_, v___x_1171_);
v___x_1173_ = lean_unsigned_to_nat(4u);
v___x_1174_ = lean_nat_mul(v_size_x27_1170_, v___x_1173_);
v___x_1175_ = lean_unsigned_to_nat(3u);
v___x_1176_ = lean_nat_div(v___x_1174_, v___x_1175_);
lean_dec(v___x_1174_);
v___x_1177_ = lean_array_get_size(v_buckets_x27_1172_);
v___x_1178_ = lean_nat_dec_le(v___x_1176_, v___x_1177_);
lean_dec(v___x_1176_);
if (v___x_1178_ == 0)
{
lean_object* v_val_1179_; lean_object* v___x_1181_; 
v_val_1179_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_buckets_x27_1172_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 1, v_val_1179_);
lean_ctor_set(v___x_1152_, 0, v_size_x27_1170_);
v___x_1181_ = v___x_1152_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_size_x27_1170_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v_val_1179_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
else
{
lean_object* v___x_1184_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 1, v_buckets_x27_1172_);
lean_ctor_set(v___x_1152_, 0, v_size_x27_1170_);
v___x_1184_ = v___x_1152_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_size_x27_1170_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v_buckets_x27_1172_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
else
{
lean_object* v___x_1186_; lean_object* v_buckets_x27_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1191_; 
lean_inc(v_bkt_1167_);
v___x_1186_ = lean_box(0);
v_buckets_x27_1187_ = lean_array_uset(v_buckets_1150_, v___x_1166_, v___x_1186_);
v___x_1188_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1147_, v_b_1148_, v_bkt_1167_);
v___x_1189_ = lean_array_uset(v_buckets_x27_1187_, v___x_1166_, v___x_1188_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 1, v___x_1189_);
v___x_1191_ = v___x_1152_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_size_1149_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(lean_object* v_a_1194_, lean_object* v_e_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1198_ = lean_st_ref_take(v_a_1194_);
v___x_1199_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v___x_1198_, v_e_1195_, v_a_1196_);
v___x_1200_ = lean_st_ref_set(v_a_1194_, v___x_1199_);
v___x_1201_ = lean_box(0);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed(lean_object* v_a_1202_, lean_object* v_e_1203_, lean_object* v_a_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(v_a_1202_, v_e_1203_, v_a_1204_);
lean_dec(v_a_1202_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1207_, lean_object* v_e_1208_, lean_object* v_a_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1207_, v_e_1208_, v_a_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec(v_a_1209_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(lean_object* v_fn_1217_, lean_object* v_e_1218_, lean_object* v_a_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v_a_1227_; lean_object* v___y_1239_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
lean_inc(v_a_1219_);
v___x_1241_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1241_, 0, lean_box(0));
lean_closure_set(v___x_1241_, 1, lean_box(0));
lean_closure_set(v___x_1241_, 2, v_a_1219_);
v___x_1242_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___x_1241_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1279_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1245_ = v___x_1242_;
v_isShared_1246_ = v_isSharedCheck_1279_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1242_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1279_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_a_1243_, v_e_1218_);
lean_dec(v_a_1243_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v___x_1248_; 
lean_del_object(v___x_1245_);
lean_inc_ref(v_fn_1217_);
lean_inc(v___y_1224_);
lean_inc_ref(v___y_1223_);
lean_inc(v___y_1222_);
lean_inc_ref(v___y_1221_);
lean_inc(v___y_1220_);
lean_inc_ref(v_e_1218_);
v___x_1248_ = lean_apply_7(v_fn_1217_, v_e_1218_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, lean_box(0));
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; uint8_t v___x_1250_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_a_1249_);
lean_dec_ref_known(v___x_1248_, 1);
v___x_1250_ = lean_unbox(v_a_1249_);
lean_dec(v_a_1249_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; 
lean_dec_ref(v_fn_1217_);
v___x_1251_ = lean_box(0);
v_a_1227_ = v___x_1251_;
goto v___jp_1226_;
}
else
{
switch(lean_obj_tag(v_e_1218_))
{
case 7:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1252_, 0, v_fn_1217_);
lean_inc_ref(v_e_1218_);
v___x_1253_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v___x_1252_, v_e_1218_, v_a_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
v___y_1239_ = v___x_1253_;
goto v___jp_1238_;
}
case 6:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1254_, 0, v_fn_1217_);
lean_inc_ref(v_e_1218_);
v___x_1255_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v___x_1254_, v_e_1218_, v_a_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
v___y_1239_ = v___x_1255_;
goto v___jp_1238_;
}
case 8:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1256_, 0, v_fn_1217_);
lean_inc_ref(v_e_1218_);
v___x_1257_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v___x_1256_, v_e_1218_, v_a_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
v___y_1239_ = v___x_1257_;
goto v___jp_1238_;
}
case 5:
{
lean_object* v_fn_1258_; lean_object* v_arg_1259_; lean_object* v___x_1260_; 
v_fn_1258_ = lean_ctor_get(v_e_1218_, 0);
v_arg_1259_ = lean_ctor_get(v_e_1218_, 1);
lean_inc_ref(v_fn_1258_);
lean_inc_ref(v_fn_1217_);
v___x_1260_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1217_, v_fn_1258_, v_a_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v___x_1261_; 
lean_dec_ref_known(v___x_1260_, 1);
lean_inc_ref(v_arg_1259_);
v___x_1261_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1217_, v_arg_1259_, v_a_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
v___y_1239_ = v___x_1261_;
goto v___jp_1238_;
}
else
{
lean_dec_ref(v_fn_1217_);
v___y_1239_ = v___x_1260_;
goto v___jp_1238_;
}
}
case 10:
{
lean_object* v_expr_1262_; lean_object* v___x_1263_; 
v_expr_1262_ = lean_ctor_get(v_e_1218_, 1);
lean_inc_ref(v_expr_1262_);
v___x_1263_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1217_, v_expr_1262_, v_a_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
v___y_1239_ = v___x_1263_;
goto v___jp_1238_;
}
case 11:
{
lean_object* v_struct_1264_; lean_object* v___x_1265_; 
v_struct_1264_ = lean_ctor_get(v_e_1218_, 2);
lean_inc_ref(v_struct_1264_);
v___x_1265_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1217_, v_struct_1264_, v_a_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
v___y_1239_ = v___x_1265_;
goto v___jp_1238_;
}
default: 
{
lean_object* v___x_1266_; 
lean_dec_ref(v_fn_1217_);
v___x_1266_ = lean_box(0);
v_a_1227_ = v___x_1266_;
goto v___jp_1226_;
}
}
}
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec_ref(v_e_1218_);
lean_dec_ref(v_fn_1217_);
v_a_1267_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1248_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1248_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
else
{
lean_object* v_val_1275_; lean_object* v___x_1277_; 
lean_dec_ref(v_e_1218_);
lean_dec_ref(v_fn_1217_);
v_val_1275_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_val_1275_);
lean_dec_ref_known(v___x_1247_, 1);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v_val_1275_);
v___x_1277_ = v___x_1245_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_val_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_dec_ref(v_e_1218_);
lean_dec_ref(v_fn_1217_);
v_a_1280_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1242_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1242_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
v___jp_1226_:
{
lean_object* v___f_1228_; lean_object* v___x_1229_; 
lean_inc(v_a_1219_);
v___f_1228_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1228_, 0, v_a_1219_);
lean_closure_set(v___f_1228_, 1, v_e_1218_);
lean_closure_set(v___f_1228_, 2, v_a_1227_);
v___x_1229_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___f_1228_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1236_ == 0)
{
lean_object* v_unused_1237_; 
v_unused_1237_ = lean_ctor_get(v___x_1229_, 0);
lean_dec(v_unused_1237_);
v___x_1231_ = v___x_1229_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_dec(v___x_1229_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v_a_1227_);
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1227_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
else
{
return v___x_1229_;
}
}
v___jp_1238_:
{
if (lean_obj_tag(v___y_1239_) == 0)
{
lean_object* v_a_1240_; 
v_a_1240_ = lean_ctor_get(v___y_1239_, 0);
lean_inc(v_a_1240_);
lean_dec_ref_known(v___y_1239_, 1);
v_a_1227_ = v_a_1240_;
goto v___jp_1226_;
}
else
{
lean_dec_ref(v_e_1218_);
return v___y_1239_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1288_ = lean_box(0);
v___x_1289_ = lean_unsigned_to_nat(16u);
v___x_1290_ = lean_mk_array(v___x_1289_, v___x_1288_);
return v___x_1290_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1291_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0);
v___x_1292_ = lean_unsigned_to_nat(0u);
v___x_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1292_);
lean_ctor_set(v___x_1293_, 1, v___x_1291_);
return v___x_1293_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1);
v___x_1295_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1295_, 0, lean_box(0));
lean_closure_set(v___x_1295_, 1, lean_box(0));
lean_closure_set(v___x_1295_, 2, v___x_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(lean_object* v_input_1296_, lean_object* v_fn_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v_a_1306_; lean_object* v___x_1307_; 
v___x_1304_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2);
v___x_1305_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1304_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1306_);
lean_dec_ref(v___x_1305_);
v___x_1307_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1297_, v_input_1296_, v_a_1306_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_a_1308_);
lean_dec_ref_known(v___x_1307_, 1);
v___x_1309_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1309_, 0, lean_box(0));
lean_closure_set(v___x_1309_, 1, lean_box(0));
lean_closure_set(v___x_1309_, 2, v_a_1306_);
v___x_1310_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1309_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1317_ == 0)
{
lean_object* v_unused_1318_; 
v_unused_1318_ = lean_ctor_get(v___x_1310_, 0);
lean_dec(v_unused_1318_);
v___x_1312_ = v___x_1310_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_dec(v___x_1310_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v_a_1308_);
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1308_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
else
{
lean_dec(v_a_1306_);
return v___x_1307_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___boxed(lean_object* v_input_1319_, lean_object* v_fn_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1319_, v_fn_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(lean_object* v_input_1328_, lean_object* v_fn_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v___f_1336_; lean_object* v___x_1337_; 
v___f_1336_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1336_, 0, v_fn_1329_);
v___x_1337_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1328_, v___f_1336_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___boxed(lean_object* v_input_1338_, lean_object* v_fn_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_input_1338_, v_fn_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(lean_object* v_fn_1347_, lean_object* v_x_1348_, lean_object* v_x_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
if (lean_obj_tag(v_x_1349_) == 0)
{
lean_object* v___x_1356_; 
lean_dec_ref(v_fn_1347_);
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v_x_1348_);
return v___x_1356_;
}
else
{
lean_object* v_head_1357_; lean_object* v_tail_1358_; lean_object* v_type_1359_; lean_object* v___x_1360_; 
v_head_1357_ = lean_ctor_get(v_x_1349_, 0);
lean_inc(v_head_1357_);
v_tail_1358_ = lean_ctor_get(v_x_1349_, 1);
lean_inc(v_tail_1358_);
lean_dec_ref_known(v_x_1349_, 2);
v_type_1359_ = lean_ctor_get(v_head_1357_, 1);
lean_inc_ref(v_type_1359_);
lean_dec(v_head_1357_);
lean_inc_ref(v_fn_1347_);
v___x_1360_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1359_, v_fn_1347_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
lean_dec_ref_known(v___x_1360_, 1);
v_x_1348_ = v_a_1361_;
v_x_1349_ = v_tail_1358_;
goto _start;
}
else
{
lean_dec(v_tail_1358_);
lean_dec_ref(v_fn_1347_);
return v___x_1360_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4___boxed(lean_object* v_fn_1363_, lean_object* v_x_1364_, lean_object* v_x_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1363_, v_x_1364_, v_x_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(lean_object* v_fn_1373_, lean_object* v_x_1374_, lean_object* v_x_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
if (lean_obj_tag(v_x_1375_) == 0)
{
lean_object* v___x_1382_; 
lean_dec_ref(v_fn_1373_);
v___x_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1382_, 0, v_x_1374_);
return v___x_1382_;
}
else
{
lean_object* v_head_1383_; lean_object* v_tail_1384_; lean_object* v___y_1386_; lean_object* v_type_1389_; lean_object* v_ctors_1390_; lean_object* v___x_1391_; 
v_head_1383_ = lean_ctor_get(v_x_1375_, 0);
lean_inc(v_head_1383_);
v_tail_1384_ = lean_ctor_get(v_x_1375_, 1);
lean_inc(v_tail_1384_);
lean_dec_ref_known(v_x_1375_, 2);
v_type_1389_ = lean_ctor_get(v_head_1383_, 1);
lean_inc_ref(v_type_1389_);
v_ctors_1390_ = lean_ctor_get(v_head_1383_, 2);
lean_inc(v_ctors_1390_);
lean_dec(v_head_1383_);
lean_inc_ref(v_fn_1373_);
v___x_1391_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1389_, v_fn_1373_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1393_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1391_, 1);
lean_inc_ref(v_fn_1373_);
v___x_1393_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1373_, v_a_1392_, v_ctors_1390_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
v___y_1386_ = v___x_1393_;
goto v___jp_1385_;
}
else
{
lean_dec(v_ctors_1390_);
v___y_1386_ = v___x_1391_;
goto v___jp_1385_;
}
v___jp_1385_:
{
if (lean_obj_tag(v___y_1386_) == 0)
{
lean_object* v_a_1387_; 
v_a_1387_ = lean_ctor_get(v___y_1386_, 0);
lean_inc(v_a_1387_);
lean_dec_ref_known(v___y_1386_, 1);
v_x_1374_ = v_a_1387_;
v_x_1375_ = v_tail_1384_;
goto _start;
}
else
{
lean_dec(v_tail_1384_);
lean_dec_ref(v_fn_1373_);
return v___y_1386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6___boxed(lean_object* v_fn_1394_, lean_object* v_x_1395_, lean_object* v_x_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1394_, v_x_1395_, v_x_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1397_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(lean_object* v_fn_1404_, lean_object* v_x_1405_, lean_object* v_x_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
if (lean_obj_tag(v_x_1406_) == 0)
{
lean_object* v___x_1413_; 
lean_dec_ref(v_fn_1404_);
v___x_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1413_, 0, v_x_1405_);
return v___x_1413_;
}
else
{
lean_object* v_head_1414_; lean_object* v_tail_1415_; lean_object* v___y_1417_; lean_object* v_toConstantVal_1420_; lean_object* v_value_1421_; lean_object* v_type_1422_; lean_object* v___x_1423_; 
v_head_1414_ = lean_ctor_get(v_x_1406_, 0);
lean_inc(v_head_1414_);
v_tail_1415_ = lean_ctor_get(v_x_1406_, 1);
lean_inc(v_tail_1415_);
lean_dec_ref_known(v_x_1406_, 2);
v_toConstantVal_1420_ = lean_ctor_get(v_head_1414_, 0);
lean_inc_ref(v_toConstantVal_1420_);
v_value_1421_ = lean_ctor_get(v_head_1414_, 1);
lean_inc_ref(v_value_1421_);
lean_dec(v_head_1414_);
v_type_1422_ = lean_ctor_get(v_toConstantVal_1420_, 2);
lean_inc_ref(v_type_1422_);
lean_dec_ref(v_toConstantVal_1420_);
lean_inc_ref(v_fn_1404_);
v___x_1423_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1422_, v_fn_1404_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v___x_1424_; 
lean_dec_ref_known(v___x_1423_, 1);
lean_inc_ref(v_fn_1404_);
v___x_1424_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1421_, v_fn_1404_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
v___y_1417_ = v___x_1424_;
goto v___jp_1416_;
}
else
{
lean_dec_ref(v_value_1421_);
v___y_1417_ = v___x_1423_;
goto v___jp_1416_;
}
v___jp_1416_:
{
if (lean_obj_tag(v___y_1417_) == 0)
{
lean_object* v_a_1418_; 
v_a_1418_ = lean_ctor_get(v___y_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref_known(v___y_1417_, 1);
v_x_1405_ = v_a_1418_;
v_x_1406_ = v_tail_1415_;
goto _start;
}
else
{
lean_dec(v_tail_1415_);
lean_dec_ref(v_fn_1404_);
return v___y_1417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1425_, lean_object* v_x_1426_, lean_object* v_x_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1425_, v_x_1426_, v_x_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(lean_object* v_fn_1435_, lean_object* v_d_1436_, lean_object* v_a_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
switch(lean_obj_tag(v_d_1436_))
{
case 0:
{
lean_object* v_val_1444_; lean_object* v_toConstantVal_1445_; lean_object* v_type_1446_; lean_object* v___x_1447_; 
v_val_1444_ = lean_ctor_get(v_d_1436_, 0);
lean_inc_ref(v_val_1444_);
lean_dec_ref_known(v_d_1436_, 1);
v_toConstantVal_1445_ = lean_ctor_get(v_val_1444_, 0);
lean_inc_ref(v_toConstantVal_1445_);
lean_dec_ref(v_val_1444_);
v_type_1446_ = lean_ctor_get(v_toConstantVal_1445_, 2);
lean_inc_ref(v_type_1446_);
lean_dec_ref(v_toConstantVal_1445_);
v___x_1447_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1446_, v_fn_1435_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
return v___x_1447_;
}
case 4:
{
lean_object* v___x_1448_; 
lean_dec_ref(v_fn_1435_);
v___x_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1448_, 0, v_a_1437_);
return v___x_1448_;
}
case 5:
{
lean_object* v_defns_1449_; lean_object* v___x_1450_; 
v_defns_1449_ = lean_ctor_get(v_d_1436_, 0);
lean_inc(v_defns_1449_);
lean_dec_ref_known(v_d_1436_, 1);
v___x_1450_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1435_, v_a_1437_, v_defns_1449_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
return v___x_1450_;
}
case 6:
{
lean_object* v_types_1451_; lean_object* v___x_1452_; 
v_types_1451_ = lean_ctor_get(v_d_1436_, 2);
lean_inc(v_types_1451_);
lean_dec_ref_known(v_d_1436_, 3);
v___x_1452_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1435_, v_a_1437_, v_types_1451_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
return v___x_1452_;
}
default: 
{
lean_object* v_val_1453_; lean_object* v_toConstantVal_1454_; lean_object* v_value_1455_; lean_object* v_type_1456_; lean_object* v___x_1457_; 
v_val_1453_ = lean_ctor_get(v_d_1436_, 0);
lean_inc_ref(v_val_1453_);
lean_dec(v_d_1436_);
v_toConstantVal_1454_ = lean_ctor_get(v_val_1453_, 0);
lean_inc_ref(v_toConstantVal_1454_);
v_value_1455_ = lean_ctor_get(v_val_1453_, 1);
lean_inc_ref(v_value_1455_);
lean_dec_ref(v_val_1453_);
v_type_1456_ = lean_ctor_get(v_toConstantVal_1454_, 2);
lean_inc_ref(v_type_1456_);
lean_dec_ref(v_toConstantVal_1454_);
lean_inc_ref(v_fn_1435_);
v___x_1457_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1456_, v_fn_1435_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v___x_1458_; 
lean_dec_ref_known(v___x_1457_, 1);
v___x_1458_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1455_, v_fn_1435_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
return v___x_1458_;
}
else
{
lean_dec_ref(v_value_1455_);
lean_dec_ref(v_fn_1435_);
return v___x_1457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2___boxed(lean_object* v_fn_1459_, lean_object* v_d_1460_, lean_object* v_a_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1459_, v_d_1460_, v_a_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(lean_object* v_decl_1469_, lean_object* v_fn_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = lean_box(0);
v___x_1478_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1470_, v_decl_1469_, v___x_1477_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1___boxed(lean_object* v_decl_1479_, lean_object* v_fn_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1479_, v_fn_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v___y_1481_);
return v_res_1487_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__0(void){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1488_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__1(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__0, &l_Lean_warnIfUsesSorry___closed__0_once, _init_l_Lean_warnIfUsesSorry___closed__0);
v___x_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
return v___x_1490_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__2(void){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1491_ = lean_box(1);
v___x_1492_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_1493_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1494_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
lean_ctor_set(v___x_1494_, 1, v___x_1492_);
lean_ctor_set(v___x_1494_, 2, v___x_1491_);
return v___x_1494_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__4(void){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1497_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1498_ = lean_unsigned_to_nat(0u);
v___x_1499_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
lean_ctor_set(v___x_1499_, 1, v___x_1498_);
lean_ctor_set(v___x_1499_, 2, v___x_1498_);
lean_ctor_set(v___x_1499_, 3, v___x_1498_);
lean_ctor_set(v___x_1499_, 4, v___x_1497_);
lean_ctor_set(v___x_1499_, 5, v___x_1497_);
lean_ctor_set(v___x_1499_, 6, v___x_1497_);
lean_ctor_set(v___x_1499_, 7, v___x_1497_);
lean_ctor_set(v___x_1499_, 8, v___x_1497_);
lean_ctor_set(v___x_1499_, 9, v___x_1497_);
return v___x_1499_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__5(void){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1501_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
lean_ctor_set(v___x_1501_, 1, v___x_1500_);
lean_ctor_set(v___x_1501_, 2, v___x_1500_);
lean_ctor_set(v___x_1501_, 3, v___x_1500_);
lean_ctor_set(v___x_1501_, 4, v___x_1500_);
lean_ctor_set(v___x_1501_, 5, v___x_1500_);
return v___x_1501_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__6(void){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1502_);
lean_ctor_set(v___x_1503_, 1, v___x_1502_);
lean_ctor_set(v___x_1503_, 2, v___x_1502_);
lean_ctor_set(v___x_1503_, 3, v___x_1502_);
lean_ctor_set(v___x_1503_, 4, v___x_1502_);
return v___x_1503_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__7(void){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1504_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__6, &l_Lean_warnIfUsesSorry___closed__6_once, _init_l_Lean_warnIfUsesSorry___closed__6);
v___x_1505_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_1506_ = lean_box(1);
v___x_1507_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__5, &l_Lean_warnIfUsesSorry___closed__5_once, _init_l_Lean_warnIfUsesSorry___closed__5);
v___x_1508_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__4, &l_Lean_warnIfUsesSorry___closed__4_once, _init_l_Lean_warnIfUsesSorry___closed__4);
v___x_1509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
lean_ctor_set(v___x_1509_, 1, v___x_1507_);
lean_ctor_set(v___x_1509_, 2, v___x_1506_);
lean_ctor_set(v___x_1509_, 3, v___x_1505_);
lean_ctor_set(v___x_1509_, 4, v___x_1504_);
return v___x_1509_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__12(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__11));
v___x_1516_ = l_Lean_stringToMessageData(v___x_1515_);
return v___x_1516_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__14(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__13));
v___x_1519_ = l_Lean_stringToMessageData(v___x_1518_);
return v___x_1519_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__16(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__15));
v___x_1522_ = l_Lean_stringToMessageData(v___x_1521_);
return v___x_1522_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__17(void){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1523_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__16, &l_Lean_warnIfUsesSorry___closed__16_once, _init_l_Lean_warnIfUsesSorry___closed__16);
v___x_1524_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__10));
v___x_1525_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
lean_ctor_set(v___x_1525_, 1, v___x_1523_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry(lean_object* v_decl_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_){
_start:
{
lean_object* v_options_1533_; lean_object* v___x_1534_; uint8_t v___x_1535_; 
v_options_1533_ = lean_ctor_get(v_a_1530_, 2);
v___x_1534_ = l_Lean_warn_sorry;
v___x_1535_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_1533_, v___x_1534_);
if (v___x_1535_ == 0)
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_dec(v_decl_1529_);
v___x_1536_ = lean_box(0);
v___x_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
return v___x_1537_;
}
else
{
lean_object* v___x_1538_; lean_object* v_messages_1542_; uint8_t v___x_1543_; 
v___x_1538_ = lean_st_ref_get(v_a_1531_);
v_messages_1542_ = lean_ctor_get(v___x_1538_, 6);
lean_inc_ref(v_messages_1542_);
lean_dec(v___x_1538_);
v___x_1543_ = l_Lean_MessageLog_hasErrors(v_messages_1542_);
lean_dec_ref(v_messages_1542_);
if (v___x_1543_ == 0)
{
if (v___x_1535_ == 0)
{
lean_dec(v_decl_1529_);
goto v___jp_1539_;
}
else
{
uint8_t v___x_1544_; 
v___x_1544_ = l_Lean_Declaration_hasSorry(v_decl_1529_);
if (v___x_1544_ == 0)
{
lean_dec(v_decl_1529_);
goto v___jp_1539_;
}
else
{
uint8_t v___x_1545_; uint8_t v___x_1546_; uint8_t v___x_1547_; lean_object* v___x_1548_; uint64_t v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___f_1560_; lean_object* v___x_1561_; 
v___x_1545_ = 1;
v___x_1546_ = 0;
v___x_1547_ = 2;
v___x_1548_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_1548_, 0, v___x_1543_);
lean_ctor_set_uint8(v___x_1548_, 1, v___x_1543_);
lean_ctor_set_uint8(v___x_1548_, 2, v___x_1543_);
lean_ctor_set_uint8(v___x_1548_, 3, v___x_1543_);
lean_ctor_set_uint8(v___x_1548_, 4, v___x_1543_);
lean_ctor_set_uint8(v___x_1548_, 5, v___x_1544_);
lean_ctor_set_uint8(v___x_1548_, 6, v___x_1544_);
lean_ctor_set_uint8(v___x_1548_, 7, v___x_1543_);
lean_ctor_set_uint8(v___x_1548_, 8, v___x_1544_);
lean_ctor_set_uint8(v___x_1548_, 9, v___x_1545_);
lean_ctor_set_uint8(v___x_1548_, 10, v___x_1546_);
lean_ctor_set_uint8(v___x_1548_, 11, v___x_1544_);
lean_ctor_set_uint8(v___x_1548_, 12, v___x_1544_);
lean_ctor_set_uint8(v___x_1548_, 13, v___x_1544_);
lean_ctor_set_uint8(v___x_1548_, 14, v___x_1547_);
lean_ctor_set_uint8(v___x_1548_, 15, v___x_1544_);
lean_ctor_set_uint8(v___x_1548_, 16, v___x_1544_);
lean_ctor_set_uint8(v___x_1548_, 17, v___x_1544_);
lean_ctor_set_uint8(v___x_1548_, 18, v___x_1544_);
v___x_1549_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1548_);
v___x_1550_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1550_, 0, v___x_1548_);
lean_ctor_set_uint64(v___x_1550_, sizeof(void*)*1, v___x_1549_);
v___x_1551_ = lean_box(1);
v___x_1552_ = lean_unsigned_to_nat(0u);
v___x_1553_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1554_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__3));
v___x_1555_ = lean_box(0);
v___x_1556_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1556_, 0, v___x_1550_);
lean_ctor_set(v___x_1556_, 1, v___x_1551_);
lean_ctor_set(v___x_1556_, 2, v___x_1553_);
lean_ctor_set(v___x_1556_, 3, v___x_1554_);
lean_ctor_set(v___x_1556_, 4, v___x_1555_);
lean_ctor_set(v___x_1556_, 5, v___x_1552_);
lean_ctor_set(v___x_1556_, 6, v___x_1555_);
lean_ctor_set_uint8(v___x_1556_, sizeof(void*)*7, v___x_1543_);
lean_ctor_set_uint8(v___x_1556_, sizeof(void*)*7 + 1, v___x_1543_);
lean_ctor_set_uint8(v___x_1556_, sizeof(void*)*7 + 2, v___x_1543_);
lean_ctor_set_uint8(v___x_1556_, sizeof(void*)*7 + 3, v___x_1535_);
v___x_1557_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__7, &l_Lean_warnIfUsesSorry___closed__7_once, _init_l_Lean_warnIfUsesSorry___closed__7);
v___x_1558_ = lean_st_mk_ref(v___x_1557_);
v___x_1559_ = lean_st_mk_ref(v___x_1554_);
v___f_1560_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__8));
v___x_1561_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1529_, v___f_1560_, v___x_1559_, v___x_1556_, v___x_1558_, v_a_1530_, v_a_1531_);
lean_dec_ref_known(v___x_1556_, 7);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v_val_1565_; lean_object* v___x_1587_; size_t v_sz_1588_; size_t v___x_1589_; lean_object* v___x_1590_; lean_object* v_fst_1591_; 
lean_dec_ref_known(v___x_1561_, 1);
v___x_1562_ = lean_st_ref_get(v___x_1559_);
lean_dec(v___x_1559_);
v___x_1563_ = lean_st_ref_get(v___x_1558_);
lean_dec(v___x_1558_);
lean_dec(v___x_1563_);
v___x_1587_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__18));
v_sz_1588_ = lean_array_size(v___x_1562_);
v___x_1589_ = ((size_t)0ULL);
v___x_1590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v___x_1562_, v_sz_1588_, v___x_1589_, v___x_1587_);
v_fst_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_fst_1591_);
lean_dec_ref(v___x_1590_);
if (lean_obj_tag(v_fst_1591_) == 0)
{
goto v___jp_1581_;
}
else
{
lean_object* v_val_1592_; 
v_val_1592_ = lean_ctor_get(v_fst_1591_, 0);
lean_inc(v_val_1592_);
lean_dec_ref_known(v_fst_1591_, 1);
if (lean_obj_tag(v_val_1592_) == 0)
{
goto v___jp_1581_;
}
else
{
lean_object* v_val_1593_; 
lean_dec(v___x_1562_);
v_val_1593_ = lean_ctor_get(v_val_1592_, 0);
lean_inc(v_val_1593_);
lean_dec_ref_known(v_val_1592_, 1);
v_val_1565_ = v_val_1593_;
goto v___jp_1564_;
}
}
v___jp_1564_:
{
lean_object* v_snd_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1579_; 
v_snd_1566_ = lean_ctor_get(v_val_1565_, 1);
v_isSharedCheck_1579_ = !lean_is_exclusive(v_val_1565_);
if (v_isSharedCheck_1579_ == 0)
{
lean_object* v_unused_1580_; 
v_unused_1580_ = lean_ctor_get(v_val_1565_, 0);
lean_dec(v_unused_1580_);
v___x_1568_ = v_val_1565_;
v_isShared_1569_ = v_isSharedCheck_1579_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_snd_1566_);
lean_dec(v_val_1565_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1579_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1570_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__10));
v___x_1571_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__12, &l_Lean_warnIfUsesSorry___closed__12_once, _init_l_Lean_warnIfUsesSorry___closed__12);
if (v_isShared_1569_ == 0)
{
lean_ctor_set_tag(v___x_1568_, 7);
lean_ctor_set(v___x_1568_, 0, v___x_1571_);
v___x_1573_ = v___x_1568_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_snd_1566_);
v___x_1573_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1574_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__14, &l_Lean_warnIfUsesSorry___closed__14_once, _init_l_Lean_warnIfUsesSorry___closed__14);
v___x_1575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1573_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
v___x_1576_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1570_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1576_, v_a_1530_, v_a_1531_);
return v___x_1577_;
}
}
}
v___jp_1581_:
{
lean_object* v___x_1582_; uint8_t v___x_1583_; 
v___x_1582_ = lean_array_get_size(v___x_1562_);
v___x_1583_ = lean_nat_dec_lt(v___x_1552_, v___x_1582_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
lean_dec(v___x_1562_);
v___x_1584_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__17, &l_Lean_warnIfUsesSorry___closed__17_once, _init_l_Lean_warnIfUsesSorry___closed__17);
v___x_1585_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1584_, v_a_1530_, v_a_1531_);
return v___x_1585_;
}
else
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_array_fget(v___x_1562_, v___x_1552_);
lean_dec(v___x_1562_);
v_val_1565_ = v___x_1586_;
goto v___jp_1564_;
}
}
}
else
{
lean_dec(v___x_1559_);
lean_dec(v___x_1558_);
return v___x_1561_;
}
}
}
}
else
{
lean_dec(v_decl_1529_);
goto v___jp_1539_;
}
v___jp_1539_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = lean_box(0);
v___x_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
return v___x_1541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___boxed(lean_object* v_decl_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_warnIfUsesSorry(v_decl_1594_, v_a_1595_, v_a_1596_);
lean_dec(v_a_1596_);
lean_dec_ref(v_a_1595_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1599_, lean_object* v_m_1600_, lean_object* v_a_1601_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1600_, v_a_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1603_, lean_object* v_m_1604_, lean_object* v_a_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(v_00_u03b2_1603_, v_m_1604_, v_a_1605_);
lean_dec_ref(v_a_1605_);
lean_dec_ref(v_m_1604_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_1607_, lean_object* v_m_1608_, lean_object* v_a_1609_, lean_object* v_b_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_m_1608_, v_a_1609_, v_b_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_1612_, lean_object* v_a_1613_, lean_object* v_x_1614_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1613_, v_x_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1616_, lean_object* v_a_1617_, lean_object* v_x_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(v_00_u03b2_1616_, v_a_1617_, v_x_1618_);
lean_dec(v_x_1618_);
lean_dec_ref(v_a_1617_);
return v_res_1619_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(lean_object* v_00_u03b2_1620_, lean_object* v_a_1621_, lean_object* v_x_1622_){
_start:
{
uint8_t v___x_1623_; 
v___x_1623_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1621_, v_x_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___boxed(lean_object* v_00_u03b2_1624_, lean_object* v_a_1625_, lean_object* v_x_1626_){
_start:
{
uint8_t v_res_1627_; lean_object* v_r_1628_; 
v_res_1627_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(v_00_u03b2_1624_, v_a_1625_, v_x_1626_);
lean_dec(v_x_1626_);
lean_dec_ref(v_a_1625_);
v_r_1628_ = lean_box(v_res_1627_);
return v_r_1628_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17(lean_object* v_00_u03b2_1629_, lean_object* v_data_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_data_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18(lean_object* v_00_u03b2_1632_, lean_object* v_a_1633_, lean_object* v_b_1634_, lean_object* v_x_1635_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1633_, v_b_1634_, v_x_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(lean_object* v_00_u03b1_1637_, lean_object* v_name_1638_, uint8_t v_bi_1639_, lean_object* v_type_1640_, lean_object* v_k_1641_, uint8_t v_kind_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_1638_, v_bi_1639_, v_type_1640_, v_k_1641_, v_kind_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___boxed(lean_object* v_00_u03b1_1651_, lean_object* v_name_1652_, lean_object* v_bi_1653_, lean_object* v_type_1654_, lean_object* v_k_1655_, lean_object* v_kind_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
uint8_t v_bi_boxed_1664_; uint8_t v_kind_boxed_1665_; lean_object* v_res_1666_; 
v_bi_boxed_1664_ = lean_unbox(v_bi_1653_);
v_kind_boxed_1665_ = lean_unbox(v_kind_1656_);
v_res_1666_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(v_00_u03b1_1651_, v_name_1652_, v_bi_boxed_1664_, v_type_1654_, v_k_1655_, v_kind_boxed_1665_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec(v___y_1657_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(lean_object* v_00_u03b1_1667_, lean_object* v_name_1668_, lean_object* v_type_1669_, lean_object* v_val_1670_, lean_object* v_k_1671_, uint8_t v_nondep_1672_, uint8_t v_kind_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_1668_, v_type_1669_, v_val_1670_, v_k_1671_, v_nondep_1672_, v_kind_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___boxed(lean_object* v_00_u03b1_1682_, lean_object* v_name_1683_, lean_object* v_type_1684_, lean_object* v_val_1685_, lean_object* v_k_1686_, lean_object* v_nondep_1687_, lean_object* v_kind_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
uint8_t v_nondep_boxed_1696_; uint8_t v_kind_boxed_1697_; lean_object* v_res_1698_; 
v_nondep_boxed_1696_ = lean_unbox(v_nondep_1687_);
v_kind_boxed_1697_ = lean_unbox(v_kind_1688_);
v_res_1698_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(v_00_u03b1_1682_, v_name_1683_, v_type_1684_, v_val_1685_, v_k_1686_, v_nondep_boxed_1696_, v_kind_boxed_1697_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec(v___y_1689_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18(lean_object* v_00_u03b2_1699_, lean_object* v_i_1700_, lean_object* v_source_1701_, lean_object* v_target_1702_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v_i_1700_, v_source_1701_, v_target_1702_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22(lean_object* v_00_u03b2_1704_, lean_object* v_x_1705_, lean_object* v_x_1706_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_x_1705_, v_x_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1757_; uint8_t v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1757_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1758_ = 0;
v___x_1759_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__20_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1760_ = l_Lean_registerTraceClass(v___x_1757_, v___x_1758_, v___x_1759_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2____boxed(lean_object* v_a_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_();
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(lean_object* v_env_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v___x_1766_; lean_object* v_nextMacroScope_1767_; lean_object* v_ngen_1768_; lean_object* v_auxDeclNGen_1769_; lean_object* v_traceState_1770_; lean_object* v_messages_1771_; lean_object* v_infoState_1772_; lean_object* v_snapshotTasks_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1784_; 
v___x_1766_ = lean_st_ref_take(v___y_1764_);
v_nextMacroScope_1767_ = lean_ctor_get(v___x_1766_, 1);
v_ngen_1768_ = lean_ctor_get(v___x_1766_, 2);
v_auxDeclNGen_1769_ = lean_ctor_get(v___x_1766_, 3);
v_traceState_1770_ = lean_ctor_get(v___x_1766_, 4);
v_messages_1771_ = lean_ctor_get(v___x_1766_, 6);
v_infoState_1772_ = lean_ctor_get(v___x_1766_, 7);
v_snapshotTasks_1773_ = lean_ctor_get(v___x_1766_, 8);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1784_ == 0)
{
lean_object* v_unused_1785_; lean_object* v_unused_1786_; 
v_unused_1785_ = lean_ctor_get(v___x_1766_, 5);
lean_dec(v_unused_1785_);
v_unused_1786_ = lean_ctor_get(v___x_1766_, 0);
lean_dec(v_unused_1786_);
v___x_1775_ = v___x_1766_;
v_isShared_1776_ = v_isSharedCheck_1784_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_snapshotTasks_1773_);
lean_inc(v_infoState_1772_);
lean_inc(v_messages_1771_);
lean_inc(v_traceState_1770_);
lean_inc(v_auxDeclNGen_1769_);
lean_inc(v_ngen_1768_);
lean_inc(v_nextMacroScope_1767_);
lean_dec(v___x_1766_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1784_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1777_; lean_object* v___x_1779_; 
v___x_1777_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 5, v___x_1777_);
lean_ctor_set(v___x_1775_, 0, v_env_1763_);
v___x_1779_ = v___x_1775_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_env_1763_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v_nextMacroScope_1767_);
lean_ctor_set(v_reuseFailAlloc_1783_, 2, v_ngen_1768_);
lean_ctor_set(v_reuseFailAlloc_1783_, 3, v_auxDeclNGen_1769_);
lean_ctor_set(v_reuseFailAlloc_1783_, 4, v_traceState_1770_);
lean_ctor_set(v_reuseFailAlloc_1783_, 5, v___x_1777_);
lean_ctor_set(v_reuseFailAlloc_1783_, 6, v_messages_1771_);
lean_ctor_set(v_reuseFailAlloc_1783_, 7, v_infoState_1772_);
lean_ctor_set(v_reuseFailAlloc_1783_, 8, v_snapshotTasks_1773_);
v___x_1779_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1780_ = lean_st_ref_set(v___y_1764_, v___x_1779_);
v___x_1781_ = lean_box(0);
v___x_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
return v___x_1782_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg___boxed(lean_object* v_env_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1787_, v___y_1788_);
lean_dec(v___y_1788_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(lean_object* v_env_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1791_, v___y_1793_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___boxed(lean_object* v_env_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(v_env_1796_, v___y_1797_, v___y_1798_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
return v_res_1800_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = lean_box(0);
v___x_1802_ = l_Lean_interruptExceptionId;
v___x_1803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
lean_ctor_set(v___x_1803_, 1, v___x_1801_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg(){
_start:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1805_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v___y_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(lean_object* v_msg_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v_ref_1813_; lean_object* v___x_1814_; lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1823_; 
v_ref_1813_ = lean_ctor_get(v___y_1810_, 5);
v___x_1814_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_1809_, v___y_1810_, v___y_1811_);
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_1823_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1823_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1819_; lean_object* v___x_1821_; 
lean_inc(v_ref_1813_);
v___x_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1819_, 0, v_ref_1813_);
lean_ctor_set(v___x_1819_, 1, v_a_1815_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set_tag(v___x_1817_, 1);
lean_ctor_set(v___x_1817_, 0, v___x_1819_);
v___x_1821_ = v___x_1817_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msg_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_1824_, v___y_1825_, v___y_1826_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(lean_object* v_ex_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v___y_1834_; lean_object* v___y_1835_; 
if (lean_obj_tag(v_ex_1829_) == 16)
{
lean_object* v___x_1839_; lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
v___x_1839_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1839_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
else
{
v___y_1834_ = v___y_1830_;
v___y_1835_ = v___y_1831_;
goto v___jp_1833_;
}
v___jp_1833_:
{
lean_object* v_options_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v_options_1836_ = lean_ctor_get(v___y_1834_, 2);
lean_inc_ref(v_options_1836_);
v___x_1837_ = l_Lean_Kernel_Exception_toMessageData(v_ex_1829_, v_options_1836_);
v___x_1838_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v___x_1837_, v___y_1834_, v___y_1835_);
return v___x_1838_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg___boxed(lean_object* v_ex_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_1848_, v___y_1849_, v___y_1850_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(lean_object* v_x_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
if (lean_obj_tag(v_x_1853_) == 0)
{
lean_object* v_a_1857_; lean_object* v___x_1858_; 
v_a_1857_ = lean_ctor_get(v_x_1853_, 0);
lean_inc(v_a_1857_);
lean_dec_ref_known(v_x_1853_, 1);
v___x_1858_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_a_1857_, v___y_1854_, v___y_1855_);
return v___x_1858_;
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
v_a_1859_ = lean_ctor_get(v_x_1853_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v_x_1853_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v_x_1853_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v_x_1853_);
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
return v___x_1864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg___boxed(lean_object* v_x_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_1867_, v___y_1868_, v___y_1869_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
return v_res_1871_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = lean_unsigned_to_nat(1u);
v___x_1873_ = l_Lean_Level_ofNat(v___x_1872_);
return v___x_1873_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1874_ = lean_box(0);
v___x_1875_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0);
v___x_1876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
lean_ctor_set(v___x_1876_, 1, v___x_1874_);
return v___x_1876_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1883_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1);
v___x_1884_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4));
v___x_1885_ = l_Lean_mkConst(v___x_1884_, v___x_1883_);
return v___x_1885_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = lean_unsigned_to_nat(0u);
v___x_1887_ = l_Lean_Level_ofNat(v___x_1886_);
return v___x_1887_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6);
v___x_1889_ = l_Lean_mkSort(v___x_1888_);
return v___x_1889_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11(void){
_start:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1895_ = lean_box(0);
v___x_1896_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__10));
v___x_1897_ = l_Lean_mkConst(v___x_1896_, v___x_1895_);
return v___x_1897_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12(void){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1898_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11);
v___x_1899_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7);
v___x_1900_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5);
v___x_1901_ = l_Lean_mkAppB(v___x_1900_, v___x_1899_, v___x_1898_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(lean_object* v_as_x27_1907_, lean_object* v_b_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
if (lean_obj_tag(v_as_x27_1907_) == 0)
{
lean_object* v___x_1912_; 
v___x_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1912_, 0, v_b_1908_);
return v___x_1912_;
}
else
{
lean_object* v_head_1913_; lean_object* v_tail_1914_; lean_object* v___x_1915_; lean_object* v_env_1916_; lean_object* v_options_1917_; lean_object* v_cancelTk_x3f_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___y_1922_; uint8_t v___y_1923_; lean_object* v_a_1927_; lean_object* v___x_1930_; lean_object* v___x_1931_; uint8_t v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
lean_dec_ref(v_b_1908_);
v_head_1913_ = lean_ctor_get(v_as_x27_1907_, 0);
v_tail_1914_ = lean_ctor_get(v_as_x27_1907_, 1);
v___x_1915_ = lean_st_ref_get(v___y_1910_);
v_env_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc_ref(v_env_1916_);
lean_dec(v___x_1915_);
v_options_1917_ = lean_ctor_get(v___y_1909_, 2);
v_cancelTk_x3f_1918_ = lean_ctor_get(v___y_1909_, 12);
v___x_1919_ = lean_box(0);
v___x_1920_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2));
v___x_1930_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12);
lean_inc(v_head_1913_);
v___x_1931_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1931_, 0, v_head_1913_);
lean_ctor_set(v___x_1931_, 1, v___x_1919_);
lean_ctor_set(v___x_1931_, 2, v___x_1930_);
v___x_1932_ = 0;
v___x_1933_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1933_, 0, v___x_1931_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*1, v___x_1932_);
v___x_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
v___x_1935_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_1916_, v_options_1917_, v___x_1934_, v_cancelTk_x3f_1918_);
lean_dec_ref_known(v___x_1934_, 1);
v___x_1936_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_1935_, v___y_1909_, v___y_1910_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1946_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_a_1937_);
lean_dec_ref_known(v___x_1936_, 1);
v___x_1938_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_1937_, v___y_1910_);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1946_ == 0)
{
lean_object* v_unused_1947_; 
v_unused_1947_ = lean_ctor_get(v___x_1938_, 0);
lean_dec(v_unused_1947_);
v___x_1940_ = v___x_1938_;
v_isShared_1941_ = v_isSharedCheck_1946_;
goto v_resetjp_1939_;
}
else
{
lean_dec(v___x_1938_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1946_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1942_; lean_object* v___x_1944_; 
v___x_1942_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__14));
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 0, v___x_1942_);
v___x_1944_ = v___x_1940_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1942_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
else
{
lean_object* v_a_1948_; 
v_a_1948_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_a_1948_);
lean_dec_ref_known(v___x_1936_, 1);
v_a_1927_ = v_a_1948_;
goto v___jp_1926_;
}
v___jp_1921_:
{
if (v___y_1923_ == 0)
{
lean_dec_ref(v___y_1922_);
v_as_x27_1907_ = v_tail_1914_;
v_b_1908_ = v___x_1920_;
goto _start;
}
else
{
lean_object* v___x_1925_; 
v___x_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1925_, 0, v___y_1922_);
return v___x_1925_;
}
}
v___jp_1926_:
{
uint8_t v___x_1928_; 
v___x_1928_ = l_Lean_Exception_isInterrupt(v_a_1927_);
if (v___x_1928_ == 0)
{
uint8_t v___x_1929_; 
lean_inc_ref(v_a_1927_);
v___x_1929_ = l_Lean_Exception_isRuntime(v_a_1927_);
v___y_1922_ = v_a_1927_;
v___y_1923_ = v___x_1929_;
goto v___jp_1921_;
}
else
{
v___y_1922_ = v_a_1927_;
v___y_1923_ = v___x_1928_;
goto v___jp_1921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___boxed(lean_object* v_as_x27_1949_, lean_object* v_b_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_1949_, v_b_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v_as_x27_1949_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(lean_object* v_decl_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1988_; uint8_t v___y_1989_; lean_object* v_a_1992_; lean_object* v___y_1996_; uint8_t v___y_1997_; lean_object* v_a_2000_; 
switch(lean_obj_tag(v_decl_1955_))
{
case 1:
{
lean_object* v_val_2003_; lean_object* v___x_2004_; lean_object* v_toConstantVal_2005_; lean_object* v_env_2006_; lean_object* v_options_2007_; lean_object* v_cancelTk_x3f_2008_; uint8_t v___x_2009_; lean_object* v___x_2010_; lean_object* v_fallbackDecl_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v_val_2003_ = lean_ctor_get(v_decl_1955_, 0);
v___x_2004_ = lean_st_ref_get(v_a_1957_);
v_toConstantVal_2005_ = lean_ctor_get(v_val_2003_, 0);
v_env_2006_ = lean_ctor_get(v___x_2004_, 0);
lean_inc_ref(v_env_2006_);
lean_dec(v___x_2004_);
v_options_2007_ = lean_ctor_get(v_a_1956_, 2);
v_cancelTk_x3f_2008_ = lean_ctor_get(v_a_1956_, 12);
v___x_2009_ = 0;
lean_inc_ref(v_toConstantVal_2005_);
v___x_2010_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2010_, 0, v_toConstantVal_2005_);
lean_ctor_set_uint8(v___x_2010_, sizeof(void*)*1, v___x_2009_);
v_fallbackDecl_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2011_, 0, v___x_2010_);
v___x_2012_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2006_, v_options_2007_, v_fallbackDecl_2011_, v_cancelTk_x3f_2008_);
lean_dec_ref_known(v_fallbackDecl_2011_, 1);
v___x_2013_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2012_, v_a_1956_, v_a_1957_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v___x_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2023_; 
lean_dec_ref_known(v_decl_1955_, 1);
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v___x_2013_, 1);
v___x_2015_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2014_, v_a_1957_);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2023_ == 0)
{
lean_object* v_unused_2024_; 
v_unused_2024_ = lean_ctor_get(v___x_2015_, 0);
lean_dec(v_unused_2024_);
v___x_2017_ = v___x_2015_;
v_isShared_2018_ = v_isSharedCheck_2023_;
goto v_resetjp_2016_;
}
else
{
lean_dec(v___x_2015_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2023_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v___x_2021_; 
v___x_2019_ = lean_box(0);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2019_);
v___x_2021_ = v___x_2017_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2019_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
else
{
lean_object* v_a_2025_; 
v_a_2025_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2025_);
lean_dec_ref_known(v___x_2013_, 1);
v_a_1992_ = v_a_2025_;
goto v___jp_1991_;
}
}
case 2:
{
lean_object* v_val_2026_; lean_object* v___x_2027_; lean_object* v_toConstantVal_2028_; lean_object* v_env_2029_; lean_object* v_options_2030_; lean_object* v_cancelTk_x3f_2031_; uint8_t v___x_2032_; lean_object* v___x_2033_; lean_object* v_fallbackDecl_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v_val_2026_ = lean_ctor_get(v_decl_1955_, 0);
v___x_2027_ = lean_st_ref_get(v_a_1957_);
v_toConstantVal_2028_ = lean_ctor_get(v_val_2026_, 0);
v_env_2029_ = lean_ctor_get(v___x_2027_, 0);
lean_inc_ref(v_env_2029_);
lean_dec(v___x_2027_);
v_options_2030_ = lean_ctor_get(v_a_1956_, 2);
v_cancelTk_x3f_2031_ = lean_ctor_get(v_a_1956_, 12);
v___x_2032_ = 0;
lean_inc_ref(v_toConstantVal_2028_);
v___x_2033_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2033_, 0, v_toConstantVal_2028_);
lean_ctor_set_uint8(v___x_2033_, sizeof(void*)*1, v___x_2032_);
v_fallbackDecl_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2034_, 0, v___x_2033_);
v___x_2035_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2029_, v_options_2030_, v_fallbackDecl_2034_, v_cancelTk_x3f_2031_);
lean_dec_ref_known(v_fallbackDecl_2034_, 1);
v___x_2036_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2035_, v_a_1956_, v_a_1957_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2046_; 
lean_dec_ref_known(v_decl_1955_, 1);
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2037_);
lean_dec_ref_known(v___x_2036_, 1);
v___x_2038_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2037_, v_a_1957_);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2046_ == 0)
{
lean_object* v_unused_2047_; 
v_unused_2047_ = lean_ctor_get(v___x_2038_, 0);
lean_dec(v_unused_2047_);
v___x_2040_ = v___x_2038_;
v_isShared_2041_ = v_isSharedCheck_2046_;
goto v_resetjp_2039_;
}
else
{
lean_dec(v___x_2038_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2046_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2042_ = lean_box(0);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 0, v___x_2042_);
v___x_2044_ = v___x_2040_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
else
{
lean_object* v_a_2048_; 
v_a_2048_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2048_);
lean_dec_ref_known(v___x_2036_, 1);
v_a_2000_ = v_a_2048_;
goto v___jp_1999_;
}
}
default: 
{
v___y_1960_ = v_a_1956_;
v___y_1961_ = v_a_1957_;
goto v___jp_1959_;
}
}
v___jp_1959_:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1962_ = l_Lean_Declaration_getNames(v_decl_1955_);
v___x_1963_ = lean_box(0);
v___x_1964_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2));
v___x_1965_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v___x_1962_, v___x_1964_, v___y_1960_, v___y_1961_);
lean_dec(v___x_1962_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1978_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1968_ = v___x_1965_;
v_isShared_1969_ = v_isSharedCheck_1978_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1965_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1978_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v_fst_1970_; 
v_fst_1970_ = lean_ctor_get(v_a_1966_, 0);
lean_inc(v_fst_1970_);
lean_dec(v_a_1966_);
if (lean_obj_tag(v_fst_1970_) == 0)
{
lean_object* v___x_1972_; 
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 0, v___x_1963_);
v___x_1972_ = v___x_1968_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1963_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
else
{
lean_object* v_val_1974_; lean_object* v___x_1976_; 
v_val_1974_ = lean_ctor_get(v_fst_1970_, 0);
lean_inc(v_val_1974_);
lean_dec_ref_known(v_fst_1970_, 1);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 0, v_val_1974_);
v___x_1976_ = v___x_1968_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_val_1974_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
else
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
v_a_1979_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1981_ = v___x_1965_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1965_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1979_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
v___jp_1987_:
{
if (v___y_1989_ == 0)
{
lean_dec_ref(v___y_1988_);
v___y_1960_ = v_a_1956_;
v___y_1961_ = v_a_1957_;
goto v___jp_1959_;
}
else
{
lean_object* v___x_1990_; 
lean_dec(v_decl_1955_);
v___x_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1990_, 0, v___y_1988_);
return v___x_1990_;
}
}
v___jp_1991_:
{
uint8_t v___x_1993_; 
v___x_1993_ = l_Lean_Exception_isInterrupt(v_a_1992_);
if (v___x_1993_ == 0)
{
uint8_t v___x_1994_; 
lean_inc_ref(v_a_1992_);
v___x_1994_ = l_Lean_Exception_isRuntime(v_a_1992_);
v___y_1988_ = v_a_1992_;
v___y_1989_ = v___x_1994_;
goto v___jp_1987_;
}
else
{
v___y_1988_ = v_a_1992_;
v___y_1989_ = v___x_1993_;
goto v___jp_1987_;
}
}
v___jp_1995_:
{
if (v___y_1997_ == 0)
{
lean_dec_ref(v___y_1996_);
v___y_1960_ = v_a_1956_;
v___y_1961_ = v_a_1957_;
goto v___jp_1959_;
}
else
{
lean_object* v___x_1998_; 
lean_dec(v_decl_1955_);
v___x_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1998_, 0, v___y_1996_);
return v___x_1998_;
}
}
v___jp_1999_:
{
uint8_t v___x_2001_; 
v___x_2001_ = l_Lean_Exception_isInterrupt(v_a_2000_);
if (v___x_2001_ == 0)
{
uint8_t v___x_2002_; 
lean_inc_ref(v_a_2000_);
v___x_2002_ = l_Lean_Exception_isRuntime(v_a_2000_);
v___y_1996_ = v_a_2000_;
v___y_1997_ = v___x_2002_;
goto v___jp_1995_;
}
else
{
v___y_1996_ = v_a_2000_;
v___y_1997_ = v___x_2001_;
goto v___jp_1995_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom___boxed(lean_object* v_decl_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2049_, v_a_2050_, v_a_2051_);
lean_dec(v_a_2051_);
lean_dec_ref(v_a_2050_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(lean_object* v_00_u03b1_2054_, lean_object* v_x_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_2055_, v___y_2056_, v___y_2057_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___boxed(lean_object* v_00_u03b1_2060_, lean_object* v_x_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(v_00_u03b1_2060_, v_x_2061_, v___y_2062_, v___y_2063_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(lean_object* v_as_2066_, lean_object* v_as_x27_2067_, lean_object* v_b_2068_, lean_object* v_a_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v___x_2073_; 
v___x_2073_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_2067_, v_b_2068_, v___y_2070_, v___y_2071_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___boxed(lean_object* v_as_2074_, lean_object* v_as_x27_2075_, lean_object* v_b_2076_, lean_object* v_a_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(v_as_2074_, v_as_x27_2075_, v_b_2076_, v_a_2077_, v___y_2078_, v___y_2079_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v_as_x27_2075_);
lean_dec(v_as_2074_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(v_00_u03b1_2087_, v___y_2088_, v___y_2089_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(lean_object* v_00_u03b1_2092_, lean_object* v_ex_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v___x_2097_; 
v___x_2097_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_2093_, v___y_2094_, v___y_2095_);
return v___x_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2098_, lean_object* v_ex_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(v_00_u03b1_2098_, v_ex_2099_, v___y_2100_, v___y_2101_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2104_, lean_object* v_msg_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v___x_2109_; 
v___x_2109_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_2105_, v___y_2106_, v___y_2107_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2110_, lean_object* v_msg_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(v_00_u03b1_2110_, v_msg_2111_, v___y_2112_, v___y_2113_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
return v_res_2115_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2116_ = lean_unsigned_to_nat(32u);
v___x_2117_ = lean_mk_empty_array_with_capacity(v___x_2116_);
v___x_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
return v___x_2118_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2119_ = ((size_t)5ULL);
v___x_2120_ = lean_unsigned_to_nat(0u);
v___x_2121_ = lean_unsigned_to_nat(32u);
v___x_2122_ = lean_mk_empty_array_with_capacity(v___x_2121_);
v___x_2123_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0);
v___x_2124_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
lean_ctor_set(v___x_2124_, 1, v___x_2122_);
lean_ctor_set(v___x_2124_, 2, v___x_2120_);
lean_ctor_set(v___x_2124_, 3, v___x_2120_);
lean_ctor_set_usize(v___x_2124_, 4, v___x_2119_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(lean_object* v___y_2125_){
_start:
{
lean_object* v___x_2127_; lean_object* v_traceState_2128_; lean_object* v_traces_2129_; lean_object* v___x_2130_; lean_object* v_traceState_2131_; lean_object* v_env_2132_; lean_object* v_nextMacroScope_2133_; lean_object* v_ngen_2134_; lean_object* v_auxDeclNGen_2135_; lean_object* v_cache_2136_; lean_object* v_messages_2137_; lean_object* v_infoState_2138_; lean_object* v_snapshotTasks_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2158_; 
v___x_2127_ = lean_st_ref_get(v___y_2125_);
v_traceState_2128_ = lean_ctor_get(v___x_2127_, 4);
lean_inc_ref(v_traceState_2128_);
lean_dec(v___x_2127_);
v_traces_2129_ = lean_ctor_get(v_traceState_2128_, 0);
lean_inc_ref(v_traces_2129_);
lean_dec_ref(v_traceState_2128_);
v___x_2130_ = lean_st_ref_take(v___y_2125_);
v_traceState_2131_ = lean_ctor_get(v___x_2130_, 4);
v_env_2132_ = lean_ctor_get(v___x_2130_, 0);
v_nextMacroScope_2133_ = lean_ctor_get(v___x_2130_, 1);
v_ngen_2134_ = lean_ctor_get(v___x_2130_, 2);
v_auxDeclNGen_2135_ = lean_ctor_get(v___x_2130_, 3);
v_cache_2136_ = lean_ctor_get(v___x_2130_, 5);
v_messages_2137_ = lean_ctor_get(v___x_2130_, 6);
v_infoState_2138_ = lean_ctor_get(v___x_2130_, 7);
v_snapshotTasks_2139_ = lean_ctor_get(v___x_2130_, 8);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2141_ = v___x_2130_;
v_isShared_2142_ = v_isSharedCheck_2158_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_snapshotTasks_2139_);
lean_inc(v_infoState_2138_);
lean_inc(v_messages_2137_);
lean_inc(v_cache_2136_);
lean_inc(v_traceState_2131_);
lean_inc(v_auxDeclNGen_2135_);
lean_inc(v_ngen_2134_);
lean_inc(v_nextMacroScope_2133_);
lean_inc(v_env_2132_);
lean_dec(v___x_2130_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2158_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
uint64_t v_tid_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2156_; 
v_tid_2143_ = lean_ctor_get_uint64(v_traceState_2131_, sizeof(void*)*1);
v_isSharedCheck_2156_ = !lean_is_exclusive(v_traceState_2131_);
if (v_isSharedCheck_2156_ == 0)
{
lean_object* v_unused_2157_; 
v_unused_2157_ = lean_ctor_get(v_traceState_2131_, 0);
lean_dec(v_unused_2157_);
v___x_2145_ = v_traceState_2131_;
v_isShared_2146_ = v_isSharedCheck_2156_;
goto v_resetjp_2144_;
}
else
{
lean_dec(v_traceState_2131_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2156_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2147_; lean_object* v___x_2149_; 
v___x_2147_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 0, v___x_2147_);
v___x_2149_ = v___x_2145_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2147_);
lean_ctor_set_uint64(v_reuseFailAlloc_2155_, sizeof(void*)*1, v_tid_2143_);
v___x_2149_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
lean_object* v___x_2151_; 
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 4, v___x_2149_);
v___x_2151_ = v___x_2141_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_env_2132_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_nextMacroScope_2133_);
lean_ctor_set(v_reuseFailAlloc_2154_, 2, v_ngen_2134_);
lean_ctor_set(v_reuseFailAlloc_2154_, 3, v_auxDeclNGen_2135_);
lean_ctor_set(v_reuseFailAlloc_2154_, 4, v___x_2149_);
lean_ctor_set(v_reuseFailAlloc_2154_, 5, v_cache_2136_);
lean_ctor_set(v_reuseFailAlloc_2154_, 6, v_messages_2137_);
lean_ctor_set(v_reuseFailAlloc_2154_, 7, v_infoState_2138_);
lean_ctor_set(v_reuseFailAlloc_2154_, 8, v_snapshotTasks_2139_);
v___x_2151_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2152_ = lean_st_ref_set(v___y_2125_, v___x_2151_);
v___x_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2153_, 0, v_traces_2129_);
return v___x_2153_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___boxed(lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2159_);
lean_dec(v___y_2159_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v___x_2165_; 
v___x_2165_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2163_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___boxed(lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(v___y_2166_, v___y_2167_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(lean_object* v_category_2170_, lean_object* v_opts_2171_, lean_object* v_act_2172_, lean_object* v_decl_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
lean_inc(v___y_2175_);
lean_inc_ref(v___y_2174_);
v___x_2177_ = lean_apply_2(v_act_2172_, v___y_2174_, v___y_2175_);
v___x_2178_ = l_Lean_profileitIOUnsafe___redArg(v_category_2170_, v_opts_2171_, v___x_2177_, v_decl_2173_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg___boxed(lean_object* v_category_2179_, lean_object* v_opts_2180_, lean_object* v_act_2181_, lean_object* v_decl_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v_category_2179_, v_opts_2180_, v_act_2181_, v_decl_2182_, v___y_2183_, v___y_2184_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec_ref(v_opts_2180_);
lean_dec_ref(v_category_2179_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(lean_object* v_00_u03b1_2187_, lean_object* v_category_2188_, lean_object* v_opts_2189_, lean_object* v_act_2190_, lean_object* v_decl_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v___x_2195_; 
v___x_2195_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v_category_2188_, v_opts_2189_, v_act_2190_, v_decl_2191_, v___y_2192_, v___y_2193_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___boxed(lean_object* v_00_u03b1_2196_, lean_object* v_category_2197_, lean_object* v_opts_2198_, lean_object* v_act_2199_, lean_object* v_decl_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(v_00_u03b1_2196_, v_category_2197_, v_opts_2198_, v_act_2199_, v_decl_2200_, v___y_2201_, v___y_2202_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec_ref(v_opts_2198_);
lean_dec_ref(v_category_2197_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(lean_object* v_a_2205_, lean_object* v_a_2206_){
_start:
{
if (lean_obj_tag(v_a_2205_) == 0)
{
lean_object* v___x_2207_; 
v___x_2207_ = l_List_reverse___redArg(v_a_2206_);
return v___x_2207_;
}
else
{
lean_object* v_head_2208_; lean_object* v_tail_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2218_; 
v_head_2208_ = lean_ctor_get(v_a_2205_, 0);
v_tail_2209_ = lean_ctor_get(v_a_2205_, 1);
v_isSharedCheck_2218_ = !lean_is_exclusive(v_a_2205_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2211_ = v_a_2205_;
v_isShared_2212_ = v_isSharedCheck_2218_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_tail_2209_);
lean_inc(v_head_2208_);
lean_dec(v_a_2205_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2218_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2213_; lean_object* v___x_2215_; 
v___x_2213_ = l_Lean_MessageData_ofName(v_head_2208_);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 1, v_a_2206_);
lean_ctor_set(v___x_2211_, 0, v___x_2213_);
v___x_2215_ = v___x_2211_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2213_);
lean_ctor_set(v_reuseFailAlloc_2217_, 1, v_a_2206_);
v___x_2215_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
v_a_2205_ = v_tail_2209_;
v_a_2206_ = v___x_2215_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2220_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__0));
v___x_2221_ = l_Lean_stringToMessageData(v___x_2220_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(lean_object* v_decl_2222_, lean_object* v_x_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2227_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1);
v___x_2228_ = l_Lean_Declaration_getTopLevelNames(v_decl_2222_);
v___x_2229_ = lean_box(0);
v___x_2230_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2228_, v___x_2229_);
v___x_2231_ = l_Lean_MessageData_ofList(v___x_2230_);
v___x_2232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2227_);
lean_ctor_set(v___x_2232_, 1, v___x_2231_);
v___x_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed(lean_object* v_decl_2234_, lean_object* v_x_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(v_decl_2234_, v_x_2235_, v___y_2236_, v___y_2237_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec_ref(v_x_2235_);
return v_res_2239_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(lean_object* v_e_2240_){
_start:
{
if (lean_obj_tag(v_e_2240_) == 0)
{
uint8_t v___x_2241_; 
v___x_2241_ = 2;
return v___x_2241_;
}
else
{
uint8_t v___x_2242_; 
v___x_2242_ = 0;
return v___x_2242_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2___boxed(lean_object* v_e_2243_){
_start:
{
uint8_t v_res_2244_; lean_object* v_r_2245_; 
v_res_2244_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_e_2243_);
lean_dec_ref(v_e_2243_);
v_r_2245_ = lean_box(v_res_2244_);
return v_r_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__5(lean_object* v_opts_2246_, lean_object* v_opt_2247_){
_start:
{
lean_object* v_name_2248_; lean_object* v_defValue_2249_; lean_object* v_map_2250_; lean_object* v___x_2251_; 
v_name_2248_ = lean_ctor_get(v_opt_2247_, 0);
v_defValue_2249_ = lean_ctor_get(v_opt_2247_, 1);
v_map_2250_ = lean_ctor_get(v_opts_2246_, 0);
v___x_2251_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2250_, v_name_2248_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_inc(v_defValue_2249_);
return v_defValue_2249_;
}
else
{
lean_object* v_val_2252_; 
v_val_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_val_2252_);
lean_dec_ref_known(v___x_2251_, 1);
if (lean_obj_tag(v_val_2252_) == 3)
{
lean_object* v_v_2253_; 
v_v_2253_ = lean_ctor_get(v_val_2252_, 0);
lean_inc(v_v_2253_);
lean_dec_ref_known(v_val_2252_, 1);
return v_v_2253_;
}
else
{
lean_dec(v_val_2252_);
lean_inc(v_defValue_2249_);
return v_defValue_2249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__5___boxed(lean_object* v_opts_2254_, lean_object* v_opt_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__5(v_opts_2254_, v_opt_2255_);
lean_dec_ref(v_opt_2255_);
lean_dec_ref(v_opts_2254_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4___redArg(lean_object* v_x_2257_){
_start:
{
if (lean_obj_tag(v_x_2257_) == 0)
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
v_a_2259_ = lean_ctor_get(v_x_2257_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v_x_2257_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v_x_2257_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v_x_2257_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
lean_ctor_set_tag(v___x_2261_, 1);
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
v_a_2267_ = lean_ctor_get(v_x_2257_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v_x_2257_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v_x_2257_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v_x_2257_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
lean_ctor_set_tag(v___x_2269_, 0);
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2267_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4___redArg___boxed(lean_object* v_x_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4___redArg(v_x_2275_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3_spec__5(size_t v_sz_2278_, size_t v_i_2279_, lean_object* v_bs_2280_){
_start:
{
uint8_t v___x_2281_; 
v___x_2281_ = lean_usize_dec_lt(v_i_2279_, v_sz_2278_);
if (v___x_2281_ == 0)
{
return v_bs_2280_;
}
else
{
lean_object* v_v_2282_; lean_object* v_msg_2283_; lean_object* v___x_2284_; lean_object* v_bs_x27_2285_; size_t v___x_2286_; size_t v___x_2287_; lean_object* v___x_2288_; 
v_v_2282_ = lean_array_uget_borrowed(v_bs_2280_, v_i_2279_);
v_msg_2283_ = lean_ctor_get(v_v_2282_, 1);
lean_inc_ref(v_msg_2283_);
v___x_2284_ = lean_unsigned_to_nat(0u);
v_bs_x27_2285_ = lean_array_uset(v_bs_2280_, v_i_2279_, v___x_2284_);
v___x_2286_ = ((size_t)1ULL);
v___x_2287_ = lean_usize_add(v_i_2279_, v___x_2286_);
v___x_2288_ = lean_array_uset(v_bs_x27_2285_, v_i_2279_, v_msg_2283_);
v_i_2279_ = v___x_2287_;
v_bs_2280_ = v___x_2288_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3_spec__5___boxed(lean_object* v_sz_2290_, lean_object* v_i_2291_, lean_object* v_bs_2292_){
_start:
{
size_t v_sz_boxed_2293_; size_t v_i_boxed_2294_; lean_object* v_res_2295_; 
v_sz_boxed_2293_ = lean_unbox_usize(v_sz_2290_);
lean_dec(v_sz_2290_);
v_i_boxed_2294_ = lean_unbox_usize(v_i_2291_);
lean_dec(v_i_2291_);
v_res_2295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3_spec__5(v_sz_boxed_2293_, v_i_boxed_2294_, v_bs_2292_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(lean_object* v_oldTraces_2296_, lean_object* v_data_2297_, lean_object* v_ref_2298_, lean_object* v_msg_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v_fileName_2303_; lean_object* v_fileMap_2304_; lean_object* v_options_2305_; lean_object* v_currRecDepth_2306_; lean_object* v_maxRecDepth_2307_; lean_object* v_ref_2308_; lean_object* v_currNamespace_2309_; lean_object* v_openDecls_2310_; lean_object* v_initHeartbeats_2311_; lean_object* v_maxHeartbeats_2312_; lean_object* v_quotContext_2313_; lean_object* v_currMacroScope_2314_; uint8_t v_diag_2315_; lean_object* v_cancelTk_x3f_2316_; uint8_t v_suppressElabErrors_2317_; lean_object* v_inheritedTraceOptions_2318_; lean_object* v___x_2319_; lean_object* v_traceState_2320_; lean_object* v_traces_2321_; lean_object* v_ref_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; size_t v_sz_2325_; size_t v___x_2326_; lean_object* v___x_2327_; lean_object* v_msg_2328_; lean_object* v___x_2329_; lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2367_; 
v_fileName_2303_ = lean_ctor_get(v___y_2300_, 0);
v_fileMap_2304_ = lean_ctor_get(v___y_2300_, 1);
v_options_2305_ = lean_ctor_get(v___y_2300_, 2);
v_currRecDepth_2306_ = lean_ctor_get(v___y_2300_, 3);
v_maxRecDepth_2307_ = lean_ctor_get(v___y_2300_, 4);
v_ref_2308_ = lean_ctor_get(v___y_2300_, 5);
v_currNamespace_2309_ = lean_ctor_get(v___y_2300_, 6);
v_openDecls_2310_ = lean_ctor_get(v___y_2300_, 7);
v_initHeartbeats_2311_ = lean_ctor_get(v___y_2300_, 8);
v_maxHeartbeats_2312_ = lean_ctor_get(v___y_2300_, 9);
v_quotContext_2313_ = lean_ctor_get(v___y_2300_, 10);
v_currMacroScope_2314_ = lean_ctor_get(v___y_2300_, 11);
v_diag_2315_ = lean_ctor_get_uint8(v___y_2300_, sizeof(void*)*14);
v_cancelTk_x3f_2316_ = lean_ctor_get(v___y_2300_, 12);
v_suppressElabErrors_2317_ = lean_ctor_get_uint8(v___y_2300_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2318_ = lean_ctor_get(v___y_2300_, 13);
v___x_2319_ = lean_st_ref_get(v___y_2301_);
v_traceState_2320_ = lean_ctor_get(v___x_2319_, 4);
lean_inc_ref(v_traceState_2320_);
lean_dec(v___x_2319_);
v_traces_2321_ = lean_ctor_get(v_traceState_2320_, 0);
lean_inc_ref(v_traces_2321_);
lean_dec_ref(v_traceState_2320_);
v_ref_2322_ = l_Lean_replaceRef(v_ref_2298_, v_ref_2308_);
lean_inc_ref(v_inheritedTraceOptions_2318_);
lean_inc(v_cancelTk_x3f_2316_);
lean_inc(v_currMacroScope_2314_);
lean_inc(v_quotContext_2313_);
lean_inc(v_maxHeartbeats_2312_);
lean_inc(v_initHeartbeats_2311_);
lean_inc(v_openDecls_2310_);
lean_inc(v_currNamespace_2309_);
lean_inc(v_maxRecDepth_2307_);
lean_inc(v_currRecDepth_2306_);
lean_inc_ref(v_options_2305_);
lean_inc_ref(v_fileMap_2304_);
lean_inc_ref(v_fileName_2303_);
v___x_2323_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2323_, 0, v_fileName_2303_);
lean_ctor_set(v___x_2323_, 1, v_fileMap_2304_);
lean_ctor_set(v___x_2323_, 2, v_options_2305_);
lean_ctor_set(v___x_2323_, 3, v_currRecDepth_2306_);
lean_ctor_set(v___x_2323_, 4, v_maxRecDepth_2307_);
lean_ctor_set(v___x_2323_, 5, v_ref_2322_);
lean_ctor_set(v___x_2323_, 6, v_currNamespace_2309_);
lean_ctor_set(v___x_2323_, 7, v_openDecls_2310_);
lean_ctor_set(v___x_2323_, 8, v_initHeartbeats_2311_);
lean_ctor_set(v___x_2323_, 9, v_maxHeartbeats_2312_);
lean_ctor_set(v___x_2323_, 10, v_quotContext_2313_);
lean_ctor_set(v___x_2323_, 11, v_currMacroScope_2314_);
lean_ctor_set(v___x_2323_, 12, v_cancelTk_x3f_2316_);
lean_ctor_set(v___x_2323_, 13, v_inheritedTraceOptions_2318_);
lean_ctor_set_uint8(v___x_2323_, sizeof(void*)*14, v_diag_2315_);
lean_ctor_set_uint8(v___x_2323_, sizeof(void*)*14 + 1, v_suppressElabErrors_2317_);
v___x_2324_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2321_);
lean_dec_ref(v_traces_2321_);
v_sz_2325_ = lean_array_size(v___x_2324_);
v___x_2326_ = ((size_t)0ULL);
v___x_2327_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3_spec__5(v_sz_2325_, v___x_2326_, v___x_2324_);
v_msg_2328_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2328_, 0, v_data_2297_);
lean_ctor_set(v_msg_2328_, 1, v_msg_2299_);
lean_ctor_set(v_msg_2328_, 2, v___x_2327_);
v___x_2329_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2328_, v___x_2323_, v___y_2301_);
lean_dec_ref_known(v___x_2323_, 14);
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2332_ = v___x_2329_;
v_isShared_2333_ = v_isSharedCheck_2367_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2329_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2367_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2334_; lean_object* v_traceState_2335_; lean_object* v_env_2336_; lean_object* v_nextMacroScope_2337_; lean_object* v_ngen_2338_; lean_object* v_auxDeclNGen_2339_; lean_object* v_cache_2340_; lean_object* v_messages_2341_; lean_object* v_infoState_2342_; lean_object* v_snapshotTasks_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2366_; 
v___x_2334_ = lean_st_ref_take(v___y_2301_);
v_traceState_2335_ = lean_ctor_get(v___x_2334_, 4);
v_env_2336_ = lean_ctor_get(v___x_2334_, 0);
v_nextMacroScope_2337_ = lean_ctor_get(v___x_2334_, 1);
v_ngen_2338_ = lean_ctor_get(v___x_2334_, 2);
v_auxDeclNGen_2339_ = lean_ctor_get(v___x_2334_, 3);
v_cache_2340_ = lean_ctor_get(v___x_2334_, 5);
v_messages_2341_ = lean_ctor_get(v___x_2334_, 6);
v_infoState_2342_ = lean_ctor_get(v___x_2334_, 7);
v_snapshotTasks_2343_ = lean_ctor_get(v___x_2334_, 8);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2345_ = v___x_2334_;
v_isShared_2346_ = v_isSharedCheck_2366_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_snapshotTasks_2343_);
lean_inc(v_infoState_2342_);
lean_inc(v_messages_2341_);
lean_inc(v_cache_2340_);
lean_inc(v_traceState_2335_);
lean_inc(v_auxDeclNGen_2339_);
lean_inc(v_ngen_2338_);
lean_inc(v_nextMacroScope_2337_);
lean_inc(v_env_2336_);
lean_dec(v___x_2334_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2366_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
uint64_t v_tid_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2364_; 
v_tid_2347_ = lean_ctor_get_uint64(v_traceState_2335_, sizeof(void*)*1);
v_isSharedCheck_2364_ = !lean_is_exclusive(v_traceState_2335_);
if (v_isSharedCheck_2364_ == 0)
{
lean_object* v_unused_2365_; 
v_unused_2365_ = lean_ctor_get(v_traceState_2335_, 0);
lean_dec(v_unused_2365_);
v___x_2349_ = v_traceState_2335_;
v_isShared_2350_ = v_isSharedCheck_2364_;
goto v_resetjp_2348_;
}
else
{
lean_dec(v_traceState_2335_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2364_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2354_; 
v___x_2351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2351_, 0, v_ref_2298_);
lean_ctor_set(v___x_2351_, 1, v_a_2330_);
v___x_2352_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2296_, v___x_2351_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 0, v___x_2352_);
v___x_2354_ = v___x_2349_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2352_);
lean_ctor_set_uint64(v_reuseFailAlloc_2363_, sizeof(void*)*1, v_tid_2347_);
v___x_2354_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
lean_object* v___x_2356_; 
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 4, v___x_2354_);
v___x_2356_ = v___x_2345_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_env_2336_);
lean_ctor_set(v_reuseFailAlloc_2362_, 1, v_nextMacroScope_2337_);
lean_ctor_set(v_reuseFailAlloc_2362_, 2, v_ngen_2338_);
lean_ctor_set(v_reuseFailAlloc_2362_, 3, v_auxDeclNGen_2339_);
lean_ctor_set(v_reuseFailAlloc_2362_, 4, v___x_2354_);
lean_ctor_set(v_reuseFailAlloc_2362_, 5, v_cache_2340_);
lean_ctor_set(v_reuseFailAlloc_2362_, 6, v_messages_2341_);
lean_ctor_set(v_reuseFailAlloc_2362_, 7, v_infoState_2342_);
lean_ctor_set(v_reuseFailAlloc_2362_, 8, v_snapshotTasks_2343_);
v___x_2356_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2360_; 
v___x_2357_ = lean_st_ref_set(v___y_2301_, v___x_2356_);
v___x_2358_ = lean_box(0);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v___x_2358_);
v___x_2360_ = v___x_2332_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2358_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___boxed(lean_object* v_oldTraces_2368_, lean_object* v_data_2369_, lean_object* v_ref_2370_, lean_object* v_msg_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(v_oldTraces_2368_, v_data_2369_, v_ref_2370_, v_msg_2371_, v___y_2372_, v___y_2373_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
return v_res_2375_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0));
v___x_2378_ = l_Lean_stringToMessageData(v___x_2377_);
return v___x_2378_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2(void){
_start:
{
lean_object* v___x_2379_; double v___x_2380_; 
v___x_2379_ = lean_unsigned_to_nat(0u);
v___x_2380_ = lean_float_of_nat(v___x_2379_);
return v___x_2380_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__4(void){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3));
v___x_2383_ = l_Lean_stringToMessageData(v___x_2382_);
return v___x_2383_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__5(void){
_start:
{
lean_object* v___x_2384_; double v___x_2385_; 
v___x_2384_ = lean_unsigned_to_nat(1000u);
v___x_2385_ = lean_float_of_nat(v___x_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(lean_object* v_cls_2386_, uint8_t v_collapsed_2387_, lean_object* v_tag_2388_, lean_object* v_opts_2389_, uint8_t v_clsEnabled_2390_, lean_object* v_oldTraces_2391_, lean_object* v_msg_2392_, lean_object* v_resStartStop_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v_fst_2397_; lean_object* v_snd_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2488_; 
v_fst_2397_ = lean_ctor_get(v_resStartStop_2393_, 0);
v_snd_2398_ = lean_ctor_get(v_resStartStop_2393_, 1);
v_isSharedCheck_2488_ = !lean_is_exclusive(v_resStartStop_2393_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2400_ = v_resStartStop_2393_;
v_isShared_2401_ = v_isSharedCheck_2488_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_snd_2398_);
lean_inc(v_fst_2397_);
lean_dec(v_resStartStop_2393_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2488_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v_data_2405_; lean_object* v_fst_2408_; lean_object* v_snd_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2487_; 
v_fst_2408_ = lean_ctor_get(v_snd_2398_, 0);
v_snd_2409_ = lean_ctor_get(v_snd_2398_, 1);
v_isSharedCheck_2487_ = !lean_is_exclusive(v_snd_2398_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2411_ = v_snd_2398_;
v_isShared_2412_ = v_isSharedCheck_2487_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_snd_2409_);
lean_inc(v_fst_2408_);
lean_dec(v_snd_2398_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2487_;
goto v_resetjp_2410_;
}
v___jp_2402_:
{
lean_object* v___x_2406_; 
lean_inc(v___y_2404_);
v___x_2406_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(v_oldTraces_2391_, v_data_2405_, v___y_2404_, v___y_2403_, v___y_2394_, v___y_2395_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v___x_2407_; 
lean_dec_ref_known(v___x_2406_, 1);
v___x_2407_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4___redArg(v_fst_2397_);
return v___x_2407_;
}
else
{
lean_dec(v_fst_2397_);
return v___x_2406_;
}
}
v_resetjp_2410_:
{
lean_object* v___x_2413_; uint8_t v___x_2414_; lean_object* v___y_2416_; lean_object* v_a_2417_; uint8_t v___y_2441_; double v___y_2472_; 
v___x_2413_ = l_Lean_trace_profiler;
v___x_2414_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2389_, v___x_2413_);
if (v___x_2414_ == 0)
{
v___y_2441_ = v___x_2414_;
goto v___jp_2440_;
}
else
{
lean_object* v___x_2477_; uint8_t v___x_2478_; 
v___x_2477_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2478_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2389_, v___x_2477_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2479_; lean_object* v___x_2480_; double v___x_2481_; double v___x_2482_; double v___x_2483_; 
v___x_2479_ = l_Lean_trace_profiler_threshold;
v___x_2480_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__5(v_opts_2389_, v___x_2479_);
v___x_2481_ = lean_float_of_nat(v___x_2480_);
v___x_2482_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__5);
v___x_2483_ = lean_float_div(v___x_2481_, v___x_2482_);
v___y_2472_ = v___x_2483_;
goto v___jp_2471_;
}
else
{
lean_object* v___x_2484_; lean_object* v___x_2485_; double v___x_2486_; 
v___x_2484_ = l_Lean_trace_profiler_threshold;
v___x_2485_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__5(v_opts_2389_, v___x_2484_);
v___x_2486_ = lean_float_of_nat(v___x_2485_);
v___y_2472_ = v___x_2486_;
goto v___jp_2471_;
}
}
v___jp_2415_:
{
uint8_t v_result_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2423_; 
v_result_2418_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_fst_2397_);
v___x_2419_ = l_Lean_TraceResult_toEmoji(v_result_2418_);
v___x_2420_ = l_Lean_stringToMessageData(v___x_2419_);
v___x_2421_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__1);
if (v_isShared_2412_ == 0)
{
lean_ctor_set_tag(v___x_2411_, 7);
lean_ctor_set(v___x_2411_, 1, v___x_2421_);
lean_ctor_set(v___x_2411_, 0, v___x_2420_);
v___x_2423_ = v___x_2411_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2420_);
lean_ctor_set(v_reuseFailAlloc_2434_, 1, v___x_2421_);
v___x_2423_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
lean_object* v_m_2425_; 
if (v_isShared_2401_ == 0)
{
lean_ctor_set_tag(v___x_2400_, 7);
lean_ctor_set(v___x_2400_, 1, v_a_2417_);
lean_ctor_set(v___x_2400_, 0, v___x_2423_);
v_m_2425_ = v___x_2400_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___x_2423_);
lean_ctor_set(v_reuseFailAlloc_2433_, 1, v_a_2417_);
v_m_2425_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; double v___x_2428_; lean_object* v_data_2429_; 
v___x_2426_ = lean_box(v_result_2418_);
v___x_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2426_);
v___x_2428_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2);
lean_inc_ref(v_tag_2388_);
lean_inc_ref(v___x_2427_);
lean_inc(v_cls_2386_);
v_data_2429_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2429_, 0, v_cls_2386_);
lean_ctor_set(v_data_2429_, 1, v___x_2427_);
lean_ctor_set(v_data_2429_, 2, v_tag_2388_);
lean_ctor_set_float(v_data_2429_, sizeof(void*)*3, v___x_2428_);
lean_ctor_set_float(v_data_2429_, sizeof(void*)*3 + 8, v___x_2428_);
lean_ctor_set_uint8(v_data_2429_, sizeof(void*)*3 + 16, v_collapsed_2387_);
if (v___x_2414_ == 0)
{
lean_dec_ref_known(v___x_2427_, 1);
lean_dec(v_snd_2409_);
lean_dec(v_fst_2408_);
lean_dec_ref(v_tag_2388_);
lean_dec(v_cls_2386_);
v___y_2403_ = v_m_2425_;
v___y_2404_ = v___y_2416_;
v_data_2405_ = v_data_2429_;
goto v___jp_2402_;
}
else
{
lean_object* v_data_2430_; double v___x_2431_; double v___x_2432_; 
lean_dec_ref_known(v_data_2429_, 3);
v_data_2430_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2430_, 0, v_cls_2386_);
lean_ctor_set(v_data_2430_, 1, v___x_2427_);
lean_ctor_set(v_data_2430_, 2, v_tag_2388_);
v___x_2431_ = lean_unbox_float(v_fst_2408_);
lean_dec(v_fst_2408_);
lean_ctor_set_float(v_data_2430_, sizeof(void*)*3, v___x_2431_);
v___x_2432_ = lean_unbox_float(v_snd_2409_);
lean_dec(v_snd_2409_);
lean_ctor_set_float(v_data_2430_, sizeof(void*)*3 + 8, v___x_2432_);
lean_ctor_set_uint8(v_data_2430_, sizeof(void*)*3 + 16, v_collapsed_2387_);
v___y_2403_ = v_m_2425_;
v___y_2404_ = v___y_2416_;
v_data_2405_ = v_data_2430_;
goto v___jp_2402_;
}
}
}
}
v___jp_2435_:
{
lean_object* v_ref_2436_; lean_object* v___x_2437_; 
v_ref_2436_ = lean_ctor_get(v___y_2394_, 5);
lean_inc(v___y_2395_);
lean_inc_ref(v___y_2394_);
lean_inc(v_fst_2397_);
v___x_2437_ = lean_apply_4(v_msg_2392_, v_fst_2397_, v___y_2394_, v___y_2395_, lean_box(0));
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
lean_dec_ref_known(v___x_2437_, 1);
v___y_2416_ = v_ref_2436_;
v_a_2417_ = v_a_2438_;
goto v___jp_2415_;
}
else
{
lean_object* v___x_2439_; 
lean_dec_ref_known(v___x_2437_, 1);
v___x_2439_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__4);
v___y_2416_ = v_ref_2436_;
v_a_2417_ = v___x_2439_;
goto v___jp_2415_;
}
}
v___jp_2440_:
{
if (v_clsEnabled_2390_ == 0)
{
if (v___y_2441_ == 0)
{
lean_object* v___x_2442_; lean_object* v_traceState_2443_; lean_object* v_env_2444_; lean_object* v_nextMacroScope_2445_; lean_object* v_ngen_2446_; lean_object* v_auxDeclNGen_2447_; lean_object* v_cache_2448_; lean_object* v_messages_2449_; lean_object* v_infoState_2450_; lean_object* v_snapshotTasks_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2470_; 
lean_del_object(v___x_2411_);
lean_dec(v_snd_2409_);
lean_dec(v_fst_2408_);
lean_del_object(v___x_2400_);
lean_dec_ref(v_msg_2392_);
lean_dec_ref(v_tag_2388_);
lean_dec(v_cls_2386_);
v___x_2442_ = lean_st_ref_take(v___y_2395_);
v_traceState_2443_ = lean_ctor_get(v___x_2442_, 4);
v_env_2444_ = lean_ctor_get(v___x_2442_, 0);
v_nextMacroScope_2445_ = lean_ctor_get(v___x_2442_, 1);
v_ngen_2446_ = lean_ctor_get(v___x_2442_, 2);
v_auxDeclNGen_2447_ = lean_ctor_get(v___x_2442_, 3);
v_cache_2448_ = lean_ctor_get(v___x_2442_, 5);
v_messages_2449_ = lean_ctor_get(v___x_2442_, 6);
v_infoState_2450_ = lean_ctor_get(v___x_2442_, 7);
v_snapshotTasks_2451_ = lean_ctor_get(v___x_2442_, 8);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2453_ = v___x_2442_;
v_isShared_2454_ = v_isSharedCheck_2470_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_snapshotTasks_2451_);
lean_inc(v_infoState_2450_);
lean_inc(v_messages_2449_);
lean_inc(v_cache_2448_);
lean_inc(v_traceState_2443_);
lean_inc(v_auxDeclNGen_2447_);
lean_inc(v_ngen_2446_);
lean_inc(v_nextMacroScope_2445_);
lean_inc(v_env_2444_);
lean_dec(v___x_2442_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2470_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
uint64_t v_tid_2455_; lean_object* v_traces_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2469_; 
v_tid_2455_ = lean_ctor_get_uint64(v_traceState_2443_, sizeof(void*)*1);
v_traces_2456_ = lean_ctor_get(v_traceState_2443_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v_traceState_2443_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2458_ = v_traceState_2443_;
v_isShared_2459_ = v_isSharedCheck_2469_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_traces_2456_);
lean_dec(v_traceState_2443_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2469_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2460_; lean_object* v___x_2462_; 
v___x_2460_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2391_, v_traces_2456_);
lean_dec_ref(v_traces_2456_);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 0, v___x_2460_);
v___x_2462_ = v___x_2458_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v___x_2460_);
lean_ctor_set_uint64(v_reuseFailAlloc_2468_, sizeof(void*)*1, v_tid_2455_);
v___x_2462_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
lean_object* v___x_2464_; 
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 4, v___x_2462_);
v___x_2464_ = v___x_2453_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_env_2444_);
lean_ctor_set(v_reuseFailAlloc_2467_, 1, v_nextMacroScope_2445_);
lean_ctor_set(v_reuseFailAlloc_2467_, 2, v_ngen_2446_);
lean_ctor_set(v_reuseFailAlloc_2467_, 3, v_auxDeclNGen_2447_);
lean_ctor_set(v_reuseFailAlloc_2467_, 4, v___x_2462_);
lean_ctor_set(v_reuseFailAlloc_2467_, 5, v_cache_2448_);
lean_ctor_set(v_reuseFailAlloc_2467_, 6, v_messages_2449_);
lean_ctor_set(v_reuseFailAlloc_2467_, 7, v_infoState_2450_);
lean_ctor_set(v_reuseFailAlloc_2467_, 8, v_snapshotTasks_2451_);
v___x_2464_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2465_ = lean_st_ref_set(v___y_2395_, v___x_2464_);
v___x_2466_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4___redArg(v_fst_2397_);
return v___x_2466_;
}
}
}
}
}
else
{
goto v___jp_2435_;
}
}
else
{
goto v___jp_2435_;
}
}
v___jp_2471_:
{
double v___x_2473_; double v___x_2474_; double v___x_2475_; uint8_t v___x_2476_; 
v___x_2473_ = lean_unbox_float(v_snd_2409_);
v___x_2474_ = lean_unbox_float(v_fst_2408_);
v___x_2475_ = lean_float_sub(v___x_2473_, v___x_2474_);
v___x_2476_ = lean_float_decLt(v___y_2472_, v___x_2475_);
v___y_2441_ = v___x_2476_;
goto v___jp_2440_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___boxed(lean_object* v_cls_2489_, lean_object* v_collapsed_2490_, lean_object* v_tag_2491_, lean_object* v_opts_2492_, lean_object* v_clsEnabled_2493_, lean_object* v_oldTraces_2494_, lean_object* v_msg_2495_, lean_object* v_resStartStop_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
uint8_t v_collapsed_boxed_2500_; uint8_t v_clsEnabled_boxed_2501_; lean_object* v_res_2502_; 
v_collapsed_boxed_2500_ = lean_unbox(v_collapsed_2490_);
v_clsEnabled_boxed_2501_ = lean_unbox(v_clsEnabled_2493_);
v_res_2502_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_2489_, v_collapsed_boxed_2500_, v_tag_2491_, v_opts_2492_, v_clsEnabled_boxed_2501_, v_oldTraces_2494_, v_msg_2495_, v_resStartStop_2496_, v___y_2497_, v___y_2498_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec_ref(v_opts_2492_);
return v_res_2502_;
}
}
static double _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2505_; double v___x_2506_; 
v___x_2505_ = lean_unsigned_to_nat(1000000000u);
v___x_2506_ = lean_float_of_nat(v___x_2505_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(lean_object* v_decl_2507_, lean_object* v___x_2508_, uint8_t v___x_2509_, lean_object* v___x_2510_, lean_object* v___f_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v___y_2516_; lean_object* v___y_2517_; uint8_t v___y_2518_; lean_object* v___y_2529_; lean_object* v_a_2530_; lean_object* v___y_2534_; lean_object* v___y_2535_; uint8_t v___y_2536_; lean_object* v___y_2547_; lean_object* v_a_2548_; lean_object* v_options_2551_; uint8_t v_hasTrace_2552_; 
v_options_2551_ = lean_ctor_get(v___y_2512_, 2);
v_hasTrace_2552_ = lean_ctor_get_uint8(v_options_2551_, sizeof(void*)*1);
if (v_hasTrace_2552_ == 0)
{
lean_object* v_cancelTk_x3f_2553_; lean_object* v___x_2554_; 
lean_dec_ref(v___f_2511_);
lean_dec_ref(v___x_2510_);
lean_dec(v___x_2508_);
v_cancelTk_x3f_2553_ = lean_ctor_get(v___y_2512_, 12);
lean_inc(v_decl_2507_);
v___x_2554_ = l_Lean_warnIfUsesSorry(v_decl_2507_, v___y_2512_, v___y_2513_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v___x_2555_; lean_object* v_env_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
lean_dec_ref_known(v___x_2554_, 1);
v___x_2555_ = lean_st_ref_get(v___y_2513_);
v_env_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc_ref(v_env_2556_);
lean_dec(v___x_2555_);
v___x_2557_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2556_, v_options_2551_, v_decl_2507_, v_cancelTk_x3f_2553_);
v___x_2558_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2557_, v___y_2512_, v___y_2513_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2560_; 
lean_dec(v_decl_2507_);
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_a_2559_);
lean_dec_ref_known(v___x_2558_, 1);
v___x_2560_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2559_, v___y_2513_);
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
v___y_2547_ = v___x_2566_;
v_a_2548_ = v_a_2561_;
goto v___jp_2546_;
}
}
}
}
else
{
lean_dec(v_decl_2507_);
return v___x_2554_;
}
}
else
{
lean_object* v_cancelTk_x3f_2569_; lean_object* v_inheritedTraceOptions_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v_a_2577_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v_a_2592_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v_a_2597_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; uint8_t v___y_2609_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v_a_2614_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v_a_2620_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v_a_2632_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v_a_2637_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; uint8_t v___y_2649_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v_a_2654_; 
v_cancelTk_x3f_2569_ = lean_ctor_get(v___y_2512_, 12);
v_inheritedTraceOptions_2570_ = lean_ctor_get(v___y_2512_, 13);
v___x_2571_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v___x_2508_);
v___x_2572_ = l_Lean_Name_append(v___x_2571_, v___x_2508_);
v___x_2573_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2570_, v_options_2551_, v___x_2572_);
lean_dec(v___x_2572_);
if (v___x_2573_ == 0)
{
lean_object* v___x_2682_; uint8_t v___x_2683_; 
v___x_2682_ = l_Lean_trace_profiler;
v___x_2683_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2551_, v___x_2682_);
if (v___x_2683_ == 0)
{
lean_object* v___x_2684_; 
lean_dec_ref(v___f_2511_);
lean_dec_ref(v___x_2510_);
lean_dec(v___x_2508_);
lean_inc(v_decl_2507_);
v___x_2684_ = l_Lean_warnIfUsesSorry(v_decl_2507_, v___y_2512_, v___y_2513_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v___x_2685_; lean_object* v_env_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
lean_dec_ref_known(v___x_2684_, 1);
v___x_2685_ = lean_st_ref_get(v___y_2513_);
v_env_2686_ = lean_ctor_get(v___x_2685_, 0);
lean_inc_ref(v_env_2686_);
lean_dec(v___x_2685_);
v___x_2687_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2686_, v_options_2551_, v_decl_2507_, v_cancelTk_x3f_2569_);
v___x_2688_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2687_, v___y_2512_, v___y_2513_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v_a_2689_; lean_object* v___x_2690_; 
lean_dec(v_decl_2507_);
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
lean_inc(v_a_2689_);
lean_dec_ref_known(v___x_2688_, 1);
v___x_2690_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2689_, v___y_2513_);
return v___x_2690_;
}
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
v_a_2691_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2688_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2688_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
lean_inc(v_a_2691_);
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2691_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
v___y_2529_ = v___x_2696_;
v_a_2530_ = v_a_2691_;
goto v___jp_2528_;
}
}
}
}
else
{
lean_dec(v_decl_2507_);
return v___x_2684_;
}
}
else
{
goto v___jp_2657_;
}
}
else
{
goto v___jp_2657_;
}
v___jp_2574_:
{
lean_object* v___x_2578_; double v___x_2579_; double v___x_2580_; double v___x_2581_; double v___x_2582_; double v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2578_ = lean_io_mono_nanos_now();
v___x_2579_ = lean_float_of_nat(v___y_2575_);
v___x_2580_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_2581_ = lean_float_div(v___x_2579_, v___x_2580_);
v___x_2582_ = lean_float_of_nat(v___x_2578_);
v___x_2583_ = lean_float_div(v___x_2582_, v___x_2580_);
v___x_2584_ = lean_box_float(v___x_2581_);
v___x_2585_ = lean_box_float(v___x_2583_);
v___x_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2584_);
lean_ctor_set(v___x_2586_, 1, v___x_2585_);
v___x_2587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2587_, 0, v_a_2577_);
lean_ctor_set(v___x_2587_, 1, v___x_2586_);
v___x_2588_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2508_, v___x_2509_, v___x_2510_, v_options_2551_, v___x_2573_, v___y_2576_, v___f_2511_, v___x_2587_, v___y_2512_, v___y_2513_);
return v___x_2588_;
}
v___jp_2589_:
{
lean_object* v___x_2593_; 
v___x_2593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2593_, 0, v_a_2592_);
v___y_2575_ = v___y_2590_;
v___y_2576_ = v___y_2591_;
v_a_2577_ = v___x_2593_;
goto v___jp_2574_;
}
v___jp_2594_:
{
lean_object* v___x_2598_; 
v___x_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2598_, 0, v_a_2597_);
v___y_2575_ = v___y_2595_;
v___y_2576_ = v___y_2596_;
v_a_2577_ = v___x_2598_;
goto v___jp_2574_;
}
v___jp_2599_:
{
if (lean_obj_tag(v___y_2602_) == 0)
{
lean_object* v_a_2603_; 
v_a_2603_ = lean_ctor_get(v___y_2602_, 0);
lean_inc(v_a_2603_);
lean_dec_ref_known(v___y_2602_, 1);
v___y_2595_ = v___y_2600_;
v___y_2596_ = v___y_2601_;
v_a_2597_ = v_a_2603_;
goto v___jp_2594_;
}
else
{
lean_object* v_a_2604_; 
v_a_2604_ = lean_ctor_get(v___y_2602_, 0);
lean_inc(v_a_2604_);
lean_dec_ref_known(v___y_2602_, 1);
v___y_2590_ = v___y_2600_;
v___y_2591_ = v___y_2601_;
v_a_2592_ = v_a_2604_;
goto v___jp_2589_;
}
}
v___jp_2605_:
{
if (v___y_2609_ == 0)
{
lean_object* v___x_2610_; 
v___x_2610_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2507_, v___y_2512_, v___y_2513_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_dec_ref_known(v___x_2610_, 1);
v___y_2590_ = v___y_2606_;
v___y_2591_ = v___y_2607_;
v_a_2592_ = v___y_2608_;
goto v___jp_2589_;
}
else
{
lean_dec_ref(v___y_2608_);
v___y_2600_ = v___y_2606_;
v___y_2601_ = v___y_2607_;
v___y_2602_ = v___x_2610_;
goto v___jp_2599_;
}
}
else
{
lean_dec(v_decl_2507_);
v___y_2590_ = v___y_2606_;
v___y_2591_ = v___y_2607_;
v_a_2592_ = v___y_2608_;
goto v___jp_2589_;
}
}
v___jp_2611_:
{
uint8_t v___x_2615_; 
v___x_2615_ = l_Lean_Exception_isInterrupt(v_a_2614_);
if (v___x_2615_ == 0)
{
uint8_t v___x_2616_; 
lean_inc_ref(v_a_2614_);
v___x_2616_ = l_Lean_Exception_isRuntime(v_a_2614_);
v___y_2606_ = v___y_2612_;
v___y_2607_ = v___y_2613_;
v___y_2608_ = v_a_2614_;
v___y_2609_ = v___x_2616_;
goto v___jp_2605_;
}
else
{
v___y_2606_ = v___y_2612_;
v___y_2607_ = v___y_2613_;
v___y_2608_ = v_a_2614_;
v___y_2609_ = v___x_2615_;
goto v___jp_2605_;
}
}
v___jp_2617_:
{
lean_object* v___x_2621_; double v___x_2622_; double v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2621_ = lean_io_get_num_heartbeats();
v___x_2622_ = lean_float_of_nat(v___y_2619_);
v___x_2623_ = lean_float_of_nat(v___x_2621_);
v___x_2624_ = lean_box_float(v___x_2622_);
v___x_2625_ = lean_box_float(v___x_2623_);
v___x_2626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2624_);
lean_ctor_set(v___x_2626_, 1, v___x_2625_);
v___x_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2627_, 0, v_a_2620_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
v___x_2628_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2508_, v___x_2509_, v___x_2510_, v_options_2551_, v___x_2573_, v___y_2618_, v___f_2511_, v___x_2627_, v___y_2512_, v___y_2513_);
return v___x_2628_;
}
v___jp_2629_:
{
lean_object* v___x_2633_; 
v___x_2633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2633_, 0, v_a_2632_);
v___y_2618_ = v___y_2630_;
v___y_2619_ = v___y_2631_;
v_a_2620_ = v___x_2633_;
goto v___jp_2617_;
}
v___jp_2634_:
{
lean_object* v___x_2638_; 
v___x_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2638_, 0, v_a_2637_);
v___y_2618_ = v___y_2635_;
v___y_2619_ = v___y_2636_;
v_a_2620_ = v___x_2638_;
goto v___jp_2617_;
}
v___jp_2639_:
{
if (lean_obj_tag(v___y_2642_) == 0)
{
lean_object* v_a_2643_; 
v_a_2643_ = lean_ctor_get(v___y_2642_, 0);
lean_inc(v_a_2643_);
lean_dec_ref_known(v___y_2642_, 1);
v___y_2635_ = v___y_2640_;
v___y_2636_ = v___y_2641_;
v_a_2637_ = v_a_2643_;
goto v___jp_2634_;
}
else
{
lean_object* v_a_2644_; 
v_a_2644_ = lean_ctor_get(v___y_2642_, 0);
lean_inc(v_a_2644_);
lean_dec_ref_known(v___y_2642_, 1);
v___y_2630_ = v___y_2640_;
v___y_2631_ = v___y_2641_;
v_a_2632_ = v_a_2644_;
goto v___jp_2629_;
}
}
v___jp_2645_:
{
if (v___y_2649_ == 0)
{
lean_object* v___x_2650_; 
v___x_2650_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2507_, v___y_2512_, v___y_2513_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_dec_ref_known(v___x_2650_, 1);
v___y_2630_ = v___y_2646_;
v___y_2631_ = v___y_2648_;
v_a_2632_ = v___y_2647_;
goto v___jp_2629_;
}
else
{
lean_dec_ref(v___y_2647_);
v___y_2640_ = v___y_2646_;
v___y_2641_ = v___y_2648_;
v___y_2642_ = v___x_2650_;
goto v___jp_2639_;
}
}
else
{
lean_dec(v_decl_2507_);
v___y_2630_ = v___y_2646_;
v___y_2631_ = v___y_2648_;
v_a_2632_ = v___y_2647_;
goto v___jp_2629_;
}
}
v___jp_2651_:
{
uint8_t v___x_2655_; 
v___x_2655_ = l_Lean_Exception_isInterrupt(v_a_2654_);
if (v___x_2655_ == 0)
{
uint8_t v___x_2656_; 
lean_inc_ref(v_a_2654_);
v___x_2656_ = l_Lean_Exception_isRuntime(v_a_2654_);
v___y_2646_ = v___y_2652_;
v___y_2647_ = v_a_2654_;
v___y_2648_ = v___y_2653_;
v___y_2649_ = v___x_2656_;
goto v___jp_2645_;
}
else
{
v___y_2646_ = v___y_2652_;
v___y_2647_ = v_a_2654_;
v___y_2648_ = v___y_2653_;
v___y_2649_ = v___x_2655_;
goto v___jp_2645_;
}
}
v___jp_2657_:
{
lean_object* v___x_2658_; lean_object* v_a_2659_; lean_object* v___x_2660_; uint8_t v___x_2661_; 
v___x_2658_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2513_);
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2659_);
lean_dec_ref(v___x_2658_);
v___x_2660_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2661_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2551_, v___x_2660_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2662_ = lean_io_mono_nanos_now();
lean_inc(v_decl_2507_);
v___x_2663_ = l_Lean_warnIfUsesSorry(v_decl_2507_, v___y_2512_, v___y_2513_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v___x_2664_; lean_object* v_env_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
lean_dec_ref_known(v___x_2663_, 1);
v___x_2664_ = lean_st_ref_get(v___y_2513_);
v_env_2665_ = lean_ctor_get(v___x_2664_, 0);
lean_inc_ref(v_env_2665_);
lean_dec(v___x_2664_);
v___x_2666_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2665_, v_options_2551_, v_decl_2507_, v_cancelTk_x3f_2569_);
v___x_2667_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2666_, v___y_2512_, v___y_2513_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; lean_object* v___x_2669_; lean_object* v_a_2670_; 
lean_dec(v_decl_2507_);
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
lean_inc(v_a_2668_);
lean_dec_ref_known(v___x_2667_, 1);
v___x_2669_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2668_, v___y_2513_);
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2670_);
lean_dec_ref(v___x_2669_);
v___y_2595_ = v___x_2662_;
v___y_2596_ = v_a_2659_;
v_a_2597_ = v_a_2670_;
goto v___jp_2594_;
}
else
{
lean_object* v_a_2671_; 
v_a_2671_ = lean_ctor_get(v___x_2667_, 0);
lean_inc(v_a_2671_);
lean_dec_ref_known(v___x_2667_, 1);
v___y_2612_ = v___x_2662_;
v___y_2613_ = v_a_2659_;
v_a_2614_ = v_a_2671_;
goto v___jp_2611_;
}
}
else
{
lean_dec(v_decl_2507_);
v___y_2600_ = v___x_2662_;
v___y_2601_ = v_a_2659_;
v___y_2602_ = v___x_2663_;
goto v___jp_2599_;
}
}
else
{
lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2672_ = lean_io_get_num_heartbeats();
lean_inc(v_decl_2507_);
v___x_2673_ = l_Lean_warnIfUsesSorry(v_decl_2507_, v___y_2512_, v___y_2513_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v___x_2674_; lean_object* v_env_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
lean_dec_ref_known(v___x_2673_, 1);
v___x_2674_ = lean_st_ref_get(v___y_2513_);
v_env_2675_ = lean_ctor_get(v___x_2674_, 0);
lean_inc_ref(v_env_2675_);
lean_dec(v___x_2674_);
v___x_2676_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2675_, v_options_2551_, v_decl_2507_, v_cancelTk_x3f_2569_);
v___x_2677_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2676_, v___y_2512_, v___y_2513_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_a_2678_; lean_object* v___x_2679_; lean_object* v_a_2680_; 
lean_dec(v_decl_2507_);
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2678_);
lean_dec_ref_known(v___x_2677_, 1);
v___x_2679_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2678_, v___y_2513_);
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref(v___x_2679_);
v___y_2635_ = v_a_2659_;
v___y_2636_ = v___x_2672_;
v_a_2637_ = v_a_2680_;
goto v___jp_2634_;
}
else
{
lean_object* v_a_2681_; 
v_a_2681_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2677_, 1);
v___y_2652_ = v_a_2659_;
v___y_2653_ = v___x_2672_;
v_a_2654_ = v_a_2681_;
goto v___jp_2651_;
}
}
else
{
lean_dec(v_decl_2507_);
v___y_2640_ = v_a_2659_;
v___y_2641_ = v___x_2672_;
v___y_2642_ = v___x_2673_;
goto v___jp_2639_;
}
}
}
}
v___jp_2515_:
{
if (v___y_2518_ == 0)
{
lean_object* v___x_2519_; 
lean_dec_ref(v___y_2517_);
v___x_2519_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2507_, v___y_2512_, v___y_2513_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2526_; 
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2526_ == 0)
{
lean_object* v_unused_2527_; 
v_unused_2527_ = lean_ctor_get(v___x_2519_, 0);
lean_dec(v_unused_2527_);
v___x_2521_ = v___x_2519_;
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
else
{
lean_dec(v___x_2519_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2524_; 
if (v_isShared_2522_ == 0)
{
lean_ctor_set_tag(v___x_2521_, 1);
lean_ctor_set(v___x_2521_, 0, v___y_2516_);
v___x_2524_ = v___x_2521_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___y_2516_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
else
{
lean_dec_ref(v___y_2516_);
return v___x_2519_;
}
}
else
{
lean_dec_ref(v___y_2516_);
lean_dec(v_decl_2507_);
return v___y_2517_;
}
}
v___jp_2528_:
{
uint8_t v___x_2531_; 
v___x_2531_ = l_Lean_Exception_isInterrupt(v_a_2530_);
if (v___x_2531_ == 0)
{
uint8_t v___x_2532_; 
lean_inc_ref(v_a_2530_);
v___x_2532_ = l_Lean_Exception_isRuntime(v_a_2530_);
v___y_2516_ = v_a_2530_;
v___y_2517_ = v___y_2529_;
v___y_2518_ = v___x_2532_;
goto v___jp_2515_;
}
else
{
v___y_2516_ = v_a_2530_;
v___y_2517_ = v___y_2529_;
v___y_2518_ = v___x_2531_;
goto v___jp_2515_;
}
}
v___jp_2533_:
{
if (v___y_2536_ == 0)
{
lean_object* v___x_2537_; 
lean_dec_ref(v___y_2534_);
v___x_2537_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2507_, v___y_2512_, v___y_2513_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2544_ == 0)
{
lean_object* v_unused_2545_; 
v_unused_2545_ = lean_ctor_get(v___x_2537_, 0);
lean_dec(v_unused_2545_);
v___x_2539_ = v___x_2537_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_dec(v___x_2537_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
lean_ctor_set_tag(v___x_2539_, 1);
lean_ctor_set(v___x_2539_, 0, v___y_2535_);
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___y_2535_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
else
{
lean_dec_ref(v___y_2535_);
return v___x_2537_;
}
}
else
{
lean_dec_ref(v___y_2535_);
lean_dec(v_decl_2507_);
return v___y_2534_;
}
}
v___jp_2546_:
{
uint8_t v___x_2549_; 
v___x_2549_ = l_Lean_Exception_isInterrupt(v_a_2548_);
if (v___x_2549_ == 0)
{
uint8_t v___x_2550_; 
lean_inc_ref(v_a_2548_);
v___x_2550_ = l_Lean_Exception_isRuntime(v_a_2548_);
v___y_2534_ = v___y_2547_;
v___y_2535_ = v_a_2548_;
v___y_2536_ = v___x_2550_;
goto v___jp_2533_;
}
else
{
v___y_2534_ = v___y_2547_;
v___y_2535_ = v_a_2548_;
v___y_2536_ = v___x_2549_;
goto v___jp_2533_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed(lean_object* v_decl_2699_, lean_object* v___x_2700_, lean_object* v___x_2701_, lean_object* v___x_2702_, lean_object* v___f_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
uint8_t v___x_8044__boxed_2707_; lean_object* v_res_2708_; 
v___x_8044__boxed_2707_ = lean_unbox(v___x_2701_);
v_res_2708_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(v_decl_2699_, v___x_2700_, v___x_8044__boxed_2707_, v___x_2702_, v___f_2703_, v___y_2704_, v___y_2705_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(lean_object* v_decl_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_){
_start:
{
lean_object* v_options_2717_; lean_object* v___f_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; uint8_t v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___f_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v_options_2717_ = lean_ctor_get(v_a_2714_, 2);
lean_inc(v_decl_2713_);
v___f_2718_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2718_, 0, v_decl_2713_);
v___x_2719_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__0));
v___x_2720_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__2));
v___x_2721_ = 1;
v___x_2722_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2723_ = lean_box(v___x_2721_);
v___f_2724_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed), 8, 5);
lean_closure_set(v___f_2724_, 0, v_decl_2713_);
lean_closure_set(v___f_2724_, 1, v___x_2720_);
lean_closure_set(v___f_2724_, 2, v___x_2723_);
lean_closure_set(v___f_2724_, 3, v___x_2722_);
lean_closure_set(v___f_2724_, 4, v___f_2718_);
v___x_2725_ = lean_box(0);
v___x_2726_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v___x_2719_, v_options_2717_, v___f_2724_, v___x_2725_, v_a_2714_, v_a_2715_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___boxed(lean_object* v_decl_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2727_, v_a_2728_, v_a_2729_);
lean_dec(v_a_2729_);
lean_dec_ref(v_a_2728_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(lean_object* v_00_u03b1_2732_, lean_object* v_x_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v___x_2737_; 
v___x_2737_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4___redArg(v_x_2733_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2738_, lean_object* v_x_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(v_00_u03b1_2738_, v_x_2739_, v___y_2740_, v___y_2741_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(lean_object* v___y_2744_, lean_object* v_a_2745_, lean_object* v___y_2746_, lean_object* v_a_x3f_2747_){
_start:
{
lean_object* v___x_2749_; lean_object* v_env_2750_; lean_object* v___x_2751_; 
v___x_2749_ = lean_st_ref_get(v___y_2744_);
v_env_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc_ref(v_env_2750_);
lean_dec(v___x_2749_);
v___x_2751_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2745_, v_env_2750_);
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
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2772_; 
v_a_2760_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2762_ = v___x_2751_;
v_isShared_2763_ = v_isSharedCheck_2772_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2751_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2772_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v_ref_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2770_; 
v_ref_2764_ = lean_ctor_get(v___y_2746_, 5);
v___x_2765_ = lean_io_error_to_string(v_a_2760_);
v___x_2766_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2765_);
v___x_2767_ = l_Lean_MessageData_ofFormat(v___x_2766_);
lean_inc(v_ref_2764_);
v___x_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2768_, 0, v_ref_2764_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 0, v___x_2768_);
v___x_2770_ = v___x_2762_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v___x_2768_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed(lean_object* v___y_2773_, lean_object* v_a_2774_, lean_object* v___y_2775_, lean_object* v_a_x3f_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2773_, v_a_2774_, v___y_2775_, v_a_x3f_2776_);
lean_dec(v_a_x3f_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2773_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(lean_object* v_asyncEnv_2779_, lean_object* v_a_2780_, lean_object* v_decl_2781_, lean_object* v_x_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_){
_start:
{
lean_object* v___x_2786_; lean_object* v_r_2787_; 
v___x_2786_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_asyncEnv_2779_, v___y_2784_);
lean_dec_ref(v___x_2786_);
v_r_2787_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2781_, v___y_2783_, v___y_2784_);
if (lean_obj_tag(v_r_2787_) == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2804_; 
v_a_2788_ = lean_ctor_get(v_r_2787_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v_r_2787_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2790_ = v_r_2787_;
v_isShared_2791_ = v_isSharedCheck_2804_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v_r_2787_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2804_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
lean_inc(v_a_2788_);
if (v_isShared_2791_ == 0)
{
lean_ctor_set_tag(v___x_2790_, 1);
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
lean_object* v___x_2794_; 
v___x_2794_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2784_, v_a_2780_, v___y_2783_, v___x_2793_);
lean_dec_ref(v___x_2793_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2801_ == 0)
{
lean_object* v_unused_2802_; 
v_unused_2802_ = lean_ctor_get(v___x_2794_, 0);
lean_dec(v_unused_2802_);
v___x_2796_ = v___x_2794_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_dec(v___x_2794_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 0, v_a_2788_);
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2788_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
else
{
lean_dec(v_a_2788_);
return v___x_2794_;
}
}
}
}
else
{
lean_object* v_a_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v_a_2805_ = lean_ctor_get(v_r_2787_, 0);
lean_inc(v_a_2805_);
lean_dec_ref_known(v_r_2787_, 1);
v___x_2806_ = lean_box(0);
v___x_2807_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2784_, v_a_2780_, v___y_2783_, v___x_2806_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2814_; 
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2814_ == 0)
{
lean_object* v_unused_2815_; 
v_unused_2815_ = lean_ctor_get(v___x_2807_, 0);
lean_dec(v_unused_2815_);
v___x_2809_ = v___x_2807_;
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
else
{
lean_dec(v___x_2807_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2812_; 
if (v_isShared_2810_ == 0)
{
lean_ctor_set_tag(v___x_2809_, 1);
lean_ctor_set(v___x_2809_, 0, v_a_2805_);
v___x_2812_ = v___x_2809_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2805_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
else
{
lean_dec(v_a_2805_);
return v___x_2807_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed(lean_object* v_asyncEnv_2816_, lean_object* v_a_2817_, lean_object* v_decl_2818_, lean_object* v_x_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
lean_object* v_res_2823_; 
v_res_2823_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(v_asyncEnv_2816_, v_a_2817_, v_decl_2818_, v_x_2819_, v___y_2820_, v___y_2821_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec_ref(v_x_2819_);
return v_res_2823_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2825_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__0));
v___x_2826_ = l_Lean_stringToMessageData(v___x_2825_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(lean_object* v_decl_2827_, lean_object* v_x_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_){
_start:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2832_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1);
v___x_2833_ = l_Lean_Declaration_getNames(v_decl_2827_);
v___x_2834_ = lean_box(0);
v___x_2835_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2833_, v___x_2834_);
v___x_2836_ = l_Lean_MessageData_ofList(v___x_2835_);
v___x_2837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2832_);
lean_ctor_set(v___x_2837_, 1, v___x_2836_);
v___x_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2837_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___boxed(lean_object* v_decl_2839_, lean_object* v_x_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v_decl_2839_, v_x_2840_, v___y_2841_, v___y_2842_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec_ref(v_x_2840_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(lean_object* v_cls_2847_, lean_object* v_msg_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_){
_start:
{
lean_object* v_ref_2852_; lean_object* v___x_2853_; lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2898_; 
v_ref_2852_ = lean_ctor_get(v___y_2849_, 5);
v___x_2853_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2848_, v___y_2849_, v___y_2850_);
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2856_ = v___x_2853_;
v_isShared_2857_ = v_isSharedCheck_2898_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2853_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2898_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2858_; lean_object* v_traceState_2859_; lean_object* v_env_2860_; lean_object* v_nextMacroScope_2861_; lean_object* v_ngen_2862_; lean_object* v_auxDeclNGen_2863_; lean_object* v_cache_2864_; lean_object* v_messages_2865_; lean_object* v_infoState_2866_; lean_object* v_snapshotTasks_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2897_; 
v___x_2858_ = lean_st_ref_take(v___y_2850_);
v_traceState_2859_ = lean_ctor_get(v___x_2858_, 4);
v_env_2860_ = lean_ctor_get(v___x_2858_, 0);
v_nextMacroScope_2861_ = lean_ctor_get(v___x_2858_, 1);
v_ngen_2862_ = lean_ctor_get(v___x_2858_, 2);
v_auxDeclNGen_2863_ = lean_ctor_get(v___x_2858_, 3);
v_cache_2864_ = lean_ctor_get(v___x_2858_, 5);
v_messages_2865_ = lean_ctor_get(v___x_2858_, 6);
v_infoState_2866_ = lean_ctor_get(v___x_2858_, 7);
v_snapshotTasks_2867_ = lean_ctor_get(v___x_2858_, 8);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2869_ = v___x_2858_;
v_isShared_2870_ = v_isSharedCheck_2897_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_snapshotTasks_2867_);
lean_inc(v_infoState_2866_);
lean_inc(v_messages_2865_);
lean_inc(v_cache_2864_);
lean_inc(v_traceState_2859_);
lean_inc(v_auxDeclNGen_2863_);
lean_inc(v_ngen_2862_);
lean_inc(v_nextMacroScope_2861_);
lean_inc(v_env_2860_);
lean_dec(v___x_2858_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2897_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
uint64_t v_tid_2871_; lean_object* v_traces_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2896_; 
v_tid_2871_ = lean_ctor_get_uint64(v_traceState_2859_, sizeof(void*)*1);
v_traces_2872_ = lean_ctor_get(v_traceState_2859_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v_traceState_2859_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2874_ = v_traceState_2859_;
v_isShared_2875_ = v_isSharedCheck_2896_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_traces_2872_);
lean_dec(v_traceState_2859_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2896_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2876_; double v___x_2877_; uint8_t v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2886_; 
v___x_2876_ = lean_box(0);
v___x_2877_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2);
v___x_2878_ = 0;
v___x_2879_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2880_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2880_, 0, v_cls_2847_);
lean_ctor_set(v___x_2880_, 1, v___x_2876_);
lean_ctor_set(v___x_2880_, 2, v___x_2879_);
lean_ctor_set_float(v___x_2880_, sizeof(void*)*3, v___x_2877_);
lean_ctor_set_float(v___x_2880_, sizeof(void*)*3 + 8, v___x_2877_);
lean_ctor_set_uint8(v___x_2880_, sizeof(void*)*3 + 16, v___x_2878_);
v___x_2881_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___closed__0));
v___x_2882_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2880_);
lean_ctor_set(v___x_2882_, 1, v_a_2854_);
lean_ctor_set(v___x_2882_, 2, v___x_2881_);
lean_inc(v_ref_2852_);
v___x_2883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2883_, 0, v_ref_2852_);
lean_ctor_set(v___x_2883_, 1, v___x_2882_);
v___x_2884_ = l_Lean_PersistentArray_push___redArg(v_traces_2872_, v___x_2883_);
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 0, v___x_2884_);
v___x_2886_ = v___x_2874_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2884_);
lean_ctor_set_uint64(v_reuseFailAlloc_2895_, sizeof(void*)*1, v_tid_2871_);
v___x_2886_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
lean_object* v___x_2888_; 
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 4, v___x_2886_);
v___x_2888_ = v___x_2869_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_env_2860_);
lean_ctor_set(v_reuseFailAlloc_2894_, 1, v_nextMacroScope_2861_);
lean_ctor_set(v_reuseFailAlloc_2894_, 2, v_ngen_2862_);
lean_ctor_set(v_reuseFailAlloc_2894_, 3, v_auxDeclNGen_2863_);
lean_ctor_set(v_reuseFailAlloc_2894_, 4, v___x_2886_);
lean_ctor_set(v_reuseFailAlloc_2894_, 5, v_cache_2864_);
lean_ctor_set(v_reuseFailAlloc_2894_, 6, v_messages_2865_);
lean_ctor_set(v_reuseFailAlloc_2894_, 7, v_infoState_2866_);
lean_ctor_set(v_reuseFailAlloc_2894_, 8, v_snapshotTasks_2867_);
v___x_2888_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2892_; 
v___x_2889_ = lean_st_ref_set(v___y_2850_, v___x_2888_);
v___x_2890_ = lean_box(0);
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 0, v___x_2890_);
v___x_2892_ = v___x_2856_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2890_);
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
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___boxed(lean_object* v_cls_2899_, lean_object* v_msg_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2899_, v_msg_2900_, v___y_2901_, v___y_2902_);
lean_dec(v___y_2902_);
lean_dec_ref(v___y_2901_);
return v_res_2904_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2906_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__0));
v___x_2907_ = l_Lean_stringToMessageData(v___x_2906_);
return v___x_2907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(lean_object* v_decl_2908_, lean_object* v_cls_2909_, lean_object* v_x_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v_options_2914_; uint8_t v_hasTrace_2915_; 
v_options_2914_ = lean_ctor_get(v___y_2911_, 2);
v_hasTrace_2915_ = lean_ctor_get_uint8(v_options_2914_, sizeof(void*)*1);
if (v_hasTrace_2915_ == 0)
{
lean_object* v___x_2916_; 
lean_dec(v_cls_2909_);
v___x_2916_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2908_, v___y_2911_, v___y_2912_);
return v___x_2916_;
}
else
{
lean_object* v_inheritedTraceOptions_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; uint8_t v___x_2920_; 
v_inheritedTraceOptions_2917_ = lean_ctor_get(v___y_2911_, 13);
v___x_2918_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2909_);
v___x_2919_ = l_Lean_Name_append(v___x_2918_, v_cls_2909_);
v___x_2920_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2917_, v_options_2914_, v___x_2919_);
lean_dec(v___x_2919_);
if (v___x_2920_ == 0)
{
lean_object* v___x_2921_; 
lean_dec(v_cls_2909_);
v___x_2921_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2908_, v___y_2911_, v___y_2912_);
return v___x_2921_;
}
else
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2922_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1);
v___x_2923_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2909_, v___x_2922_, v___y_2911_, v___y_2912_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v___x_2924_; 
lean_dec_ref_known(v___x_2923_, 1);
v___x_2924_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2908_, v___y_2911_, v___y_2912_);
return v___x_2924_;
}
else
{
lean_dec(v_decl_2908_);
return v___x_2923_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed(lean_object* v_decl_2925_, lean_object* v_cls_2926_, lean_object* v_x_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_2925_, v_cls_2926_, v_x_2927_, v___y_2928_, v___y_2929_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v_x_2927_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(lean_object* v_opt_2932_, lean_object* v___y_2933_){
_start:
{
lean_object* v_options_2935_; uint8_t v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v_options_2935_ = lean_ctor_get(v___y_2933_, 2);
v___x_2936_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2935_, v_opt_2932_);
v___x_2937_ = lean_box(v___x_2936_);
v___x_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg___boxed(lean_object* v_opt_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_2939_, v___y_2940_);
lean_dec_ref(v___y_2940_);
lean_dec_ref(v_opt_2939_);
return v_res_2942_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(lean_object* v_x_2943_){
_start:
{
if (lean_obj_tag(v_x_2943_) == 0)
{
uint8_t v___x_2944_; 
v___x_2944_ = 1;
return v___x_2944_;
}
else
{
lean_object* v_head_2945_; lean_object* v_tail_2946_; uint8_t v___x_2947_; 
v_head_2945_ = lean_ctor_get(v_x_2943_, 0);
v_tail_2946_ = lean_ctor_get(v_x_2943_, 1);
v___x_2947_ = l_Lean_isPrivateName(v_head_2945_);
if (v___x_2947_ == 0)
{
return v___x_2947_;
}
else
{
v_x_2943_ = v_tail_2946_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2___boxed(lean_object* v_x_2949_){
_start:
{
uint8_t v_res_2950_; lean_object* v_r_2951_; 
v_res_2950_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v_x_2949_);
lean_dec(v_x_2949_);
v_r_2951_ = lean_box(v_res_2950_);
return v_r_2951_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3(void){
_start:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2957_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__2));
v___x_2958_ = l_Lean_stringToMessageData(v___x_2957_);
return v___x_2958_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5(void){
_start:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2960_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__4));
v___x_2961_ = l_Lean_stringToMessageData(v___x_2960_);
return v___x_2961_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7(void){
_start:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2963_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__6));
v___x_2964_ = l_Lean_stringToMessageData(v___x_2963_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(lean_object* v_decl_2965_, uint8_t v_hasTrace_2966_, uint8_t v___x_2967_, lean_object* v___x_2968_, lean_object* v_cls_2969_, lean_object* v___x_2970_, lean_object* v_____x_2971_, lean_object* v_exportedInfo_x3f_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_){
_start:
{
lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v_a_2979_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v_a_2992_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v_snd_3075_; lean_object* v_fst_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3203_; 
v_snd_3075_ = lean_ctor_get(v_____x_2971_, 1);
v_fst_3076_ = lean_ctor_get(v_____x_2971_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v_____x_2971_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3078_ = v_____x_2971_;
v_isShared_3079_ = v_isSharedCheck_3203_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_snd_3075_);
lean_inc(v_fst_3076_);
lean_dec(v_____x_2971_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3203_;
goto v_resetjp_3077_;
}
v___jp_2976_:
{
lean_object* v___x_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2987_; 
v___x_2980_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2978_, v___y_2977_);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_2987_ == 0)
{
lean_object* v_unused_2988_; 
v_unused_2988_ = lean_ctor_get(v___x_2980_, 0);
lean_dec(v_unused_2988_);
v___x_2982_ = v___x_2980_;
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
else
{
lean_dec(v___x_2980_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2985_; 
if (v_isShared_2983_ == 0)
{
lean_ctor_set_tag(v___x_2982_, 1);
lean_ctor_set(v___x_2982_, 0, v_a_2979_);
v___x_2985_ = v___x_2982_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_a_2979_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
v___jp_2989_:
{
lean_object* v___x_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
v___x_2993_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2991_, v___y_2990_);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3000_ == 0)
{
lean_object* v_unused_3001_; 
v_unused_3001_ = lean_ctor_get(v___x_2993_, 0);
lean_dec(v_unused_3001_);
v___x_2995_ = v___x_2993_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_dec(v___x_2993_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 0, v_a_2992_);
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2992_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
v___jp_3002_:
{
lean_object* v___x_3013_; 
lean_inc_ref(v___y_3004_);
v___x_3013_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3010_, v___y_3004_, v___y_3011_, v___y_3012_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v___x_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3060_; 
lean_dec_ref_known(v___x_3013_, 1);
lean_inc_ref(v___y_3006_);
v___x_3014_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3006_, v___y_3005_);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3060_ == 0)
{
lean_object* v_unused_3061_; 
v_unused_3061_ = lean_ctor_get(v___x_3014_, 0);
lean_dec(v_unused_3061_);
v___x_3016_ = v___x_3014_;
v_isShared_3017_ = v_isSharedCheck_3060_;
goto v_resetjp_3015_;
}
else
{
lean_dec(v___x_3014_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3060_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v_options_3018_; lean_object* v___x_3019_; uint8_t v___x_3020_; 
v_options_3018_ = lean_ctor_get(v___y_3003_, 2);
v___x_3019_ = l_Lean_Elab_async;
v___x_3020_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3018_, v___x_3019_);
if (v___x_3020_ == 0)
{
lean_object* v___x_3021_; lean_object* v_r_3022_; 
lean_del_object(v___x_3016_);
lean_dec_ref(v___y_3009_);
lean_dec_ref(v___y_3007_);
v___x_3021_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3004_, v___y_3005_);
lean_dec_ref(v___x_3021_);
v_r_3022_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2965_, v___y_3003_, v___y_3005_);
if (lean_obj_tag(v_r_3022_) == 0)
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3032_; 
v_a_3023_ = lean_ctor_get(v_r_3022_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v_r_3022_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3025_ = v_r_3022_;
v_isShared_3026_ = v_isSharedCheck_3032_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v_r_3022_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3032_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
lean_inc(v_a_3023_);
if (v_isShared_3026_ == 0)
{
lean_ctor_set_tag(v___x_3025_, 1);
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
lean_object* v___x_3029_; 
v___x_3029_ = lean_apply_2(v___y_3008_, v___x_3028_, lean_box(0));
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_dec_ref_known(v___x_3029_, 1);
v___y_2990_ = v___y_3005_;
v___y_2991_ = v___y_3006_;
v_a_2992_ = v_a_3023_;
goto v___jp_2989_;
}
else
{
lean_object* v_a_3030_; 
lean_dec(v_a_3023_);
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_a_3030_);
lean_dec_ref_known(v___x_3029_, 1);
v___y_2977_ = v___y_3005_;
v___y_2978_ = v___y_3006_;
v_a_2979_ = v_a_3030_;
goto v___jp_2976_;
}
}
}
}
else
{
lean_object* v_a_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v_a_3033_ = lean_ctor_get(v_r_3022_, 0);
lean_inc(v_a_3033_);
lean_dec_ref_known(v_r_3022_, 1);
v___x_3034_ = lean_box(0);
v___x_3035_ = lean_apply_2(v___y_3008_, v___x_3034_, lean_box(0));
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_dec_ref_known(v___x_3035_, 1);
v___y_2977_ = v___y_3005_;
v___y_2978_ = v___y_3006_;
v_a_2979_ = v_a_3033_;
goto v___jp_2976_;
}
else
{
lean_object* v_a_3036_; 
lean_dec(v_a_3033_);
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
lean_inc(v_a_3036_);
lean_dec_ref_known(v___x_3035_, 1);
v___y_2977_ = v___y_3005_;
v___y_2978_ = v___y_3006_;
v_a_2979_ = v_a_3036_;
goto v___jp_2976_;
}
}
}
else
{
lean_object* v___x_3037_; lean_object* v___x_3039_; 
lean_dec_ref(v___y_3008_);
lean_dec_ref(v___y_3006_);
lean_dec_ref(v___y_3004_);
lean_dec(v_decl_2965_);
v___x_3037_ = l_IO_CancelToken_new();
if (v_isShared_3017_ == 0)
{
lean_ctor_set_tag(v___x_3016_, 1);
lean_ctor_set(v___x_3016_, 0, v___x_3037_);
v___x_3039_ = v___x_3016_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v___x_3037_);
v___x_3039_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3040_ = lean_unsigned_to_nat(0u);
v___x_3041_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_3042_ = l_Lean_Name_toString(v___x_3041_, v_hasTrace_2966_);
lean_inc_ref(v___x_3039_);
v___x_3043_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3007_, v___x_3039_, v___x_3042_, v___y_3003_, v___y_3005_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v_checked_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
lean_inc(v_a_3044_);
lean_dec_ref_known(v___x_3043_, 1);
v_checked_3045_ = lean_ctor_get(v___y_3009_, 2);
lean_inc_ref(v_checked_3045_);
lean_dec_ref(v___y_3009_);
v___x_3046_ = lean_io_map_task(v_a_3044_, v_checked_3045_, v___x_3040_, v___x_2967_);
v___x_3047_ = lean_box(0);
v___x_3048_ = lean_box(2);
v___x_3049_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3047_);
lean_ctor_set(v___x_3049_, 1, v___x_3048_);
lean_ctor_set(v___x_3049_, 2, v___x_3039_);
lean_ctor_set(v___x_3049_, 3, v___x_3046_);
v___x_3050_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3049_, v___y_3005_);
return v___x_3050_;
}
else
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
lean_dec_ref(v___x_3039_);
lean_dec_ref(v___y_3009_);
v_a_3051_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_3043_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3043_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3074_; 
lean_dec_ref(v___y_3009_);
lean_dec_ref(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec_ref(v___y_3006_);
lean_dec_ref(v___y_3004_);
lean_dec(v_decl_2965_);
v_a_3062_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3064_ = v___x_3013_;
v_isShared_3065_ = v_isSharedCheck_3074_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_3013_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3074_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v_ref_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3072_; 
v_ref_3066_ = lean_ctor_get(v___y_3003_, 5);
v___x_3067_ = lean_io_error_to_string(v_a_3062_);
v___x_3068_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
v___x_3069_ = l_Lean_MessageData_ofFormat(v___x_3068_);
lean_inc(v_ref_3066_);
v___x_3070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3070_, 0, v_ref_3066_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
if (v_isShared_3065_ == 0)
{
lean_ctor_set(v___x_3064_, 0, v___x_3070_);
v___x_3072_ = v___x_3064_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v___x_3070_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
v_resetjp_3077_:
{
lean_object* v_fst_3080_; lean_object* v_snd_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3202_; 
v_fst_3080_ = lean_ctor_get(v_snd_3075_, 0);
v_snd_3081_ = lean_ctor_get(v_snd_3075_, 1);
v_isSharedCheck_3202_ = !lean_is_exclusive(v_snd_3075_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3083_ = v_snd_3075_;
v_isShared_3084_ = v_isSharedCheck_3202_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_snd_3081_);
lean_inc(v_fst_3080_);
lean_dec(v_snd_3075_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3202_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v_exportedInfo_x3f_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___x_3192_; lean_object* v_env_3193_; uint8_t v___x_3194_; 
v___x_3192_ = lean_st_ref_get(v___y_2974_);
v_env_3193_ = lean_ctor_get(v___x_3192_, 0);
lean_inc_ref(v_env_3193_);
lean_dec(v___x_3192_);
v___x_3194_ = l_Lean_Environment_containsOnBranch(v_env_3193_, v_fst_3076_);
lean_dec_ref(v_env_3193_);
if (v___x_3194_ == 0)
{
lean_del_object(v___x_3078_);
v___y_3160_ = v___y_2973_;
v___y_3161_ = v___y_2974_;
goto v___jp_3159_;
}
else
{
lean_object* v___x_3195_; lean_object* v_env_3196_; lean_object* v___x_3197_; lean_object* v___x_3199_; 
lean_del_object(v___x_3083_);
lean_dec(v_snd_3081_);
lean_dec(v_fst_3080_);
lean_dec(v_exportedInfo_x3f_2972_);
lean_dec(v___x_2970_);
lean_dec(v_cls_2969_);
lean_dec_ref(v___x_2968_);
lean_dec(v_decl_2965_);
v___x_3195_ = lean_st_ref_get(v___y_2974_);
v_env_3196_ = lean_ctor_get(v___x_3195_, 0);
lean_inc_ref(v_env_3196_);
lean_dec(v___x_3195_);
v___x_3197_ = lean_elab_environment_to_kernel_env(v_env_3196_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set_tag(v___x_3078_, 1);
lean_ctor_set(v___x_3078_, 1, v_fst_3076_);
lean_ctor_set(v___x_3078_, 0, v___x_3197_);
v___x_3199_ = v___x_3078_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___x_3197_);
lean_ctor_set(v_reuseFailAlloc_3201_, 1, v_fst_3076_);
v___x_3199_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3199_, v___y_2973_, v___y_2974_);
return v___x_3200_;
}
}
v___jp_3085_:
{
uint8_t v___x_3093_; lean_object* v___x_3094_; 
v___x_3093_ = lean_unbox(v_snd_3081_);
lean_dec(v_snd_3081_);
lean_inc_ref(v___y_3086_);
v___x_3094_ = l_Lean_Environment_addConstAsync(v___y_3086_, v_fst_3076_, v___x_3093_, v___y_3092_, v___x_2967_, v_hasTrace_2966_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_object* v_a_3095_; lean_object* v_mainEnv_3096_; lean_object* v_asyncEnv_3097_; lean_object* v___f_3098_; lean_object* v___f_3099_; lean_object* v___x_3100_; 
lean_del_object(v___x_3083_);
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
lean_inc_n(v_a_3095_, 3);
lean_dec_ref_known(v___x_3094_, 1);
v_mainEnv_3096_ = lean_ctor_get(v_a_3095_, 0);
lean_inc_ref(v_mainEnv_3096_);
v_asyncEnv_3097_ = lean_ctor_get(v_a_3095_, 1);
lean_inc_ref_n(v_asyncEnv_3097_, 2);
lean_inc_ref(v___y_3088_);
lean_inc(v___y_3087_);
v___f_3098_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3098_, 0, v___y_3087_);
lean_closure_set(v___f_3098_, 1, v_a_3095_);
lean_closure_set(v___f_3098_, 2, v___y_3088_);
lean_inc(v_decl_2965_);
v___f_3099_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3099_, 0, v_asyncEnv_3097_);
lean_closure_set(v___f_3099_, 1, v_a_3095_);
lean_closure_set(v___f_3099_, 2, v_decl_2965_);
v___x_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3100_, 0, v_fst_3080_);
if (lean_obj_tag(v___y_3091_) == 0)
{
lean_inc_ref(v___x_3100_);
v___y_3003_ = v___y_3089_;
v___y_3004_ = v_asyncEnv_3097_;
v___y_3005_ = v___y_3090_;
v___y_3006_ = v_mainEnv_3096_;
v___y_3007_ = v___f_3099_;
v___y_3008_ = v___f_3098_;
v___y_3009_ = v___y_3086_;
v___y_3010_ = v_a_3095_;
v___y_3011_ = v___x_3100_;
v___y_3012_ = v___x_3100_;
goto v___jp_3002_;
}
else
{
v___y_3003_ = v___y_3089_;
v___y_3004_ = v_asyncEnv_3097_;
v___y_3005_ = v___y_3090_;
v___y_3006_ = v_mainEnv_3096_;
v___y_3007_ = v___f_3099_;
v___y_3008_ = v___f_3098_;
v___y_3009_ = v___y_3086_;
v___y_3010_ = v_a_3095_;
v___y_3011_ = v___x_3100_;
v___y_3012_ = v___y_3091_;
goto v___jp_3002_;
}
}
else
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3115_; 
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3086_);
lean_dec(v_fst_3080_);
lean_dec(v_decl_2965_);
v_a_3101_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3103_ = v___x_3094_;
v_isShared_3104_ = v_isSharedCheck_3115_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3094_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3115_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v_ref_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3110_; 
v_ref_3105_ = lean_ctor_get(v___y_3089_, 5);
v___x_3106_ = lean_io_error_to_string(v_a_3101_);
v___x_3107_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3106_);
v___x_3108_ = l_Lean_MessageData_ofFormat(v___x_3107_);
lean_inc(v_ref_3105_);
if (v_isShared_3084_ == 0)
{
lean_ctor_set(v___x_3083_, 1, v___x_3108_);
lean_ctor_set(v___x_3083_, 0, v_ref_3105_);
v___x_3110_ = v___x_3083_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_ref_3105_);
lean_ctor_set(v_reuseFailAlloc_3114_, 1, v___x_3108_);
v___x_3110_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
lean_object* v___x_3112_; 
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 0, v___x_3110_);
v___x_3112_ = v___x_3103_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3110_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
}
}
v___jp_3116_:
{
lean_object* v___x_3120_; 
v___x_3120_ = lean_st_ref_get(v___y_3119_);
if (lean_obj_tag(v_exportedInfo_x3f_3117_) == 0)
{
lean_object* v_env_3121_; lean_object* v___x_3122_; 
v_env_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc_ref(v_env_3121_);
lean_dec(v___x_3120_);
v___x_3122_ = lean_box(0);
v___y_3086_ = v_env_3121_;
v___y_3087_ = v___y_3119_;
v___y_3088_ = v___y_3118_;
v___y_3089_ = v___y_3118_;
v___y_3090_ = v___y_3119_;
v___y_3091_ = v_exportedInfo_x3f_3117_;
v___y_3092_ = v___x_3122_;
goto v___jp_3085_;
}
else
{
lean_object* v_env_3123_; lean_object* v_val_3124_; uint8_t v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v_env_3123_ = lean_ctor_get(v___x_3120_, 0);
lean_inc_ref(v_env_3123_);
lean_dec(v___x_3120_);
v_val_3124_ = lean_ctor_get(v_exportedInfo_x3f_3117_, 0);
v___x_3125_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3124_);
v___x_3126_ = lean_box(v___x_3125_);
v___x_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3126_);
v___y_3086_ = v_env_3123_;
v___y_3087_ = v___y_3119_;
v___y_3088_ = v___y_3118_;
v___y_3089_ = v___y_3118_;
v___y_3090_ = v___y_3119_;
v___y_3091_ = v_exportedInfo_x3f_3117_;
v___y_3092_ = v___x_3127_;
goto v___jp_3085_;
}
}
v___jp_3128_:
{
lean_object* v___x_3131_; 
lean_inc(v_fst_3080_);
v___x_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3131_, 0, v_fst_3080_);
v_exportedInfo_x3f_3117_ = v___x_3131_;
v___y_3118_ = v___y_3129_;
v___y_3119_ = v___y_3130_;
goto v___jp_3116_;
}
v___jp_3132_:
{
lean_object* v___x_3135_; 
lean_inc(v_fst_3080_);
v___x_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3135_, 0, v_fst_3080_);
v_exportedInfo_x3f_3117_ = v___x_3135_;
v___y_3118_ = v___y_3133_;
v___y_3119_ = v___y_3134_;
goto v___jp_3116_;
}
v___jp_3136_:
{
lean_object* v___x_3139_; lean_object* v_env_3140_; lean_object* v_nextMacroScope_3141_; lean_object* v_ngen_3142_; lean_object* v_auxDeclNGen_3143_; lean_object* v_traceState_3144_; lean_object* v_messages_3145_; lean_object* v_infoState_3146_; lean_object* v_snapshotTasks_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3157_; 
v___x_3139_ = lean_st_ref_take(v___y_3138_);
v_env_3140_ = lean_ctor_get(v___x_3139_, 0);
v_nextMacroScope_3141_ = lean_ctor_get(v___x_3139_, 1);
v_ngen_3142_ = lean_ctor_get(v___x_3139_, 2);
v_auxDeclNGen_3143_ = lean_ctor_get(v___x_3139_, 3);
v_traceState_3144_ = lean_ctor_get(v___x_3139_, 4);
v_messages_3145_ = lean_ctor_get(v___x_3139_, 6);
v_infoState_3146_ = lean_ctor_get(v___x_3139_, 7);
v_snapshotTasks_3147_ = lean_ctor_get(v___x_3139_, 8);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3157_ == 0)
{
lean_object* v_unused_3158_; 
v_unused_3158_ = lean_ctor_get(v___x_3139_, 5);
lean_dec(v_unused_3158_);
v___x_3149_ = v___x_3139_;
v_isShared_3150_ = v_isSharedCheck_3157_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_snapshotTasks_3147_);
lean_inc(v_infoState_3146_);
lean_inc(v_messages_3145_);
lean_inc(v_traceState_3144_);
lean_inc(v_auxDeclNGen_3143_);
lean_inc(v_ngen_3142_);
lean_inc(v_nextMacroScope_3141_);
lean_inc(v_env_3140_);
lean_dec(v___x_3139_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3157_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3154_; 
v___x_3151_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3081_);
lean_inc(v_fst_3076_);
v___x_3152_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3151_, v_env_3140_, v_fst_3076_, v_snd_3081_);
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 5, v___x_2968_);
lean_ctor_set(v___x_3149_, 0, v___x_3152_);
v___x_3154_ = v___x_3149_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v___x_3152_);
lean_ctor_set(v_reuseFailAlloc_3156_, 1, v_nextMacroScope_3141_);
lean_ctor_set(v_reuseFailAlloc_3156_, 2, v_ngen_3142_);
lean_ctor_set(v_reuseFailAlloc_3156_, 3, v_auxDeclNGen_3143_);
lean_ctor_set(v_reuseFailAlloc_3156_, 4, v_traceState_3144_);
lean_ctor_set(v_reuseFailAlloc_3156_, 5, v___x_2968_);
lean_ctor_set(v_reuseFailAlloc_3156_, 6, v_messages_3145_);
lean_ctor_set(v_reuseFailAlloc_3156_, 7, v_infoState_3146_);
lean_ctor_set(v_reuseFailAlloc_3156_, 8, v_snapshotTasks_3147_);
v___x_3154_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
lean_object* v___x_3155_; 
v___x_3155_ = lean_st_ref_set(v___y_3138_, v___x_3154_);
v_exportedInfo_x3f_3117_ = v_exportedInfo_x3f_2972_;
v___y_3118_ = v___y_3137_;
v___y_3119_ = v___y_3138_;
goto v___jp_3116_;
}
}
}
v___jp_3159_:
{
lean_object* v___x_3162_; uint8_t v___x_3163_; 
lean_inc(v_decl_2965_);
v___x_3162_ = l_Lean_Declaration_getTopLevelNames(v_decl_2965_);
v___x_3163_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3162_);
lean_dec(v___x_3162_);
if (v___x_3163_ == 0)
{
lean_dec(v___x_2970_);
if (lean_obj_tag(v_exportedInfo_x3f_2972_) == 0)
{
if (v___x_2967_ == 0)
{
lean_object* v_options_3164_; uint8_t v_hasTrace_3165_; 
lean_dec_ref(v___x_2968_);
v_options_3164_ = lean_ctor_get(v___y_3160_, 2);
v_hasTrace_3165_ = lean_ctor_get_uint8(v_options_3164_, sizeof(void*)*1);
if (v_hasTrace_3165_ == 0)
{
lean_dec(v_cls_2969_);
v___y_3129_ = v___y_3160_;
v___y_3130_ = v___y_3161_;
goto v___jp_3128_;
}
else
{
lean_object* v_inheritedTraceOptions_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; uint8_t v___x_3169_; 
v_inheritedTraceOptions_3166_ = lean_ctor_get(v___y_3160_, 13);
v___x_3167_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2969_);
v___x_3168_ = l_Lean_Name_append(v___x_3167_, v_cls_2969_);
v___x_3169_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3166_, v_options_3164_, v___x_3168_);
lean_dec(v___x_3168_);
if (v___x_3169_ == 0)
{
lean_dec(v_cls_2969_);
v___y_3129_ = v___y_3160_;
v___y_3130_ = v___y_3161_;
goto v___jp_3128_;
}
else
{
lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3170_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_3171_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2969_, v___x_3170_, v___y_3160_, v___y_3161_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_dec_ref_known(v___x_3171_, 1);
v___y_3129_ = v___y_3160_;
v___y_3130_ = v___y_3161_;
goto v___jp_3128_;
}
else
{
lean_del_object(v___x_3083_);
lean_dec(v_snd_3081_);
lean_dec(v_fst_3080_);
lean_dec(v_fst_3076_);
lean_dec(v_decl_2965_);
return v___x_3171_;
}
}
}
}
else
{
lean_dec(v_cls_2969_);
v___y_3137_ = v___y_3160_;
v___y_3138_ = v___y_3161_;
goto v___jp_3136_;
}
}
else
{
lean_dec(v_cls_2969_);
v___y_3137_ = v___y_3160_;
v___y_3138_ = v___y_3161_;
goto v___jp_3136_;
}
}
else
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v_a_3174_; uint8_t v___x_3175_; 
lean_dec(v_exportedInfo_x3f_2972_);
lean_dec_ref(v___x_2968_);
v___x_3172_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3173_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3172_, v___y_3160_);
v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
lean_inc(v_a_3174_);
lean_dec_ref(v___x_3173_);
v___x_3175_ = lean_unbox(v_a_3174_);
lean_dec(v_a_3174_);
if (v___x_3175_ == 0)
{
lean_object* v_options_3176_; uint8_t v_hasTrace_3177_; 
v_options_3176_ = lean_ctor_get(v___y_3160_, 2);
v_hasTrace_3177_ = lean_ctor_get_uint8(v_options_3176_, sizeof(void*)*1);
if (v_hasTrace_3177_ == 0)
{
lean_dec(v_cls_2969_);
v_exportedInfo_x3f_3117_ = v___x_2970_;
v___y_3118_ = v___y_3160_;
v___y_3119_ = v___y_3161_;
goto v___jp_3116_;
}
else
{
lean_object* v_inheritedTraceOptions_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; uint8_t v___x_3181_; 
v_inheritedTraceOptions_3178_ = lean_ctor_get(v___y_3160_, 13);
v___x_3179_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2969_);
v___x_3180_ = l_Lean_Name_append(v___x_3179_, v_cls_2969_);
v___x_3181_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3178_, v_options_3176_, v___x_3180_);
lean_dec(v___x_3180_);
if (v___x_3181_ == 0)
{
lean_dec(v_cls_2969_);
v_exportedInfo_x3f_3117_ = v___x_2970_;
v___y_3118_ = v___y_3160_;
v___y_3119_ = v___y_3161_;
goto v___jp_3116_;
}
else
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3182_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_3183_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2969_, v___x_3182_, v___y_3160_, v___y_3161_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_dec_ref_known(v___x_3183_, 1);
v_exportedInfo_x3f_3117_ = v___x_2970_;
v___y_3118_ = v___y_3160_;
v___y_3119_ = v___y_3161_;
goto v___jp_3116_;
}
else
{
lean_del_object(v___x_3083_);
lean_dec(v_snd_3081_);
lean_dec(v_fst_3080_);
lean_dec(v_fst_3076_);
lean_dec(v___x_2970_);
lean_dec(v_decl_2965_);
return v___x_3183_;
}
}
}
}
else
{
lean_object* v_options_3184_; uint8_t v_hasTrace_3185_; 
lean_dec(v___x_2970_);
v_options_3184_ = lean_ctor_get(v___y_3160_, 2);
v_hasTrace_3185_ = lean_ctor_get_uint8(v_options_3184_, sizeof(void*)*1);
if (v_hasTrace_3185_ == 0)
{
lean_dec(v_cls_2969_);
v___y_3133_ = v___y_3160_;
v___y_3134_ = v___y_3161_;
goto v___jp_3132_;
}
else
{
lean_object* v_inheritedTraceOptions_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; uint8_t v___x_3189_; 
v_inheritedTraceOptions_3186_ = lean_ctor_get(v___y_3160_, 13);
v___x_3187_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2969_);
v___x_3188_ = l_Lean_Name_append(v___x_3187_, v_cls_2969_);
v___x_3189_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3186_, v_options_3184_, v___x_3188_);
lean_dec(v___x_3188_);
if (v___x_3189_ == 0)
{
lean_dec(v_cls_2969_);
v___y_3133_ = v___y_3160_;
v___y_3134_ = v___y_3161_;
goto v___jp_3132_;
}
else
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3190_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_3191_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2969_, v___x_3190_, v___y_3160_, v___y_3161_);
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_dec_ref_known(v___x_3191_, 1);
v___y_3133_ = v___y_3160_;
v___y_3134_ = v___y_3161_;
goto v___jp_3132_;
}
else
{
lean_del_object(v___x_3083_);
lean_dec(v_snd_3081_);
lean_dec(v_fst_3080_);
lean_dec(v_fst_3076_);
lean_dec(v_decl_2965_);
return v___x_3191_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed(lean_object* v_decl_3204_, lean_object* v_hasTrace_3205_, lean_object* v___x_3206_, lean_object* v___x_3207_, lean_object* v_cls_3208_, lean_object* v___x_3209_, lean_object* v_____x_3210_, lean_object* v_exportedInfo_x3f_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
uint8_t v_hasTrace_boxed_3215_; uint8_t v___x_62744__boxed_3216_; lean_object* v_res_3217_; 
v_hasTrace_boxed_3215_ = lean_unbox(v_hasTrace_3205_);
v___x_62744__boxed_3216_ = lean_unbox(v___x_3206_);
v_res_3217_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(v_decl_3204_, v_hasTrace_boxed_3215_, v___x_62744__boxed_3216_, v___x_3207_, v_cls_3208_, v___x_3209_, v_____x_3210_, v_exportedInfo_x3f_3211_, v___y_3212_, v___y_3213_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
return v_res_3217_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1(void){
_start:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3219_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__0));
v___x_3220_ = l_Lean_stringToMessageData(v___x_3219_);
return v___x_3220_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3(void){
_start:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__2));
v___x_3223_ = l_Lean_stringToMessageData(v___x_3222_);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(lean_object* v___f_3224_, lean_object* v_cls_3225_, lean_object* v___x_3226_, uint8_t v___x_3227_, uint8_t v_forceExpose_3228_, lean_object* v_defn_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_){
_start:
{
lean_object* v_exportedInfo_x3f_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v_env_3272_; lean_object* v_env_3273_; 
v___x_3255_ = lean_st_ref_get(v___y_3231_);
v___x_3256_ = lean_st_ref_get(v___y_3231_);
v_env_3272_ = lean_ctor_get(v___x_3255_, 0);
lean_inc_ref(v_env_3272_);
lean_dec(v___x_3255_);
v_env_3273_ = lean_ctor_get(v___x_3256_, 0);
lean_inc_ref(v_env_3273_);
lean_dec(v___x_3256_);
if (v_forceExpose_3228_ == 0)
{
goto v___jp_3274_;
}
else
{
if (v___x_3227_ == 0)
{
lean_dec_ref(v_env_3273_);
lean_dec_ref(v_env_3272_);
lean_dec(v_cls_3225_);
v_exportedInfo_x3f_3234_ = v___x_3226_;
v___y_3235_ = v___y_3230_;
v___y_3236_ = v___y_3231_;
goto v___jp_3233_;
}
else
{
goto v___jp_3274_;
}
}
v___jp_3233_:
{
lean_object* v_toConstantVal_3237_; lean_object* v_name_3238_; lean_object* v___x_3239_; uint8_t v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; 
v_toConstantVal_3237_ = lean_ctor_get(v_defn_3229_, 0);
v_name_3238_ = lean_ctor_get(v_toConstantVal_3237_, 0);
lean_inc(v_name_3238_);
v___x_3239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3239_, 0, v_defn_3229_);
v___x_3240_ = 0;
v___x_3241_ = lean_box(v___x_3240_);
v___x_3242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3239_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
v___x_3243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3243_, 0, v_name_3238_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
lean_inc(v___y_3236_);
lean_inc_ref(v___y_3235_);
v___x_3244_ = lean_apply_5(v___f_3224_, v___x_3243_, v_exportedInfo_x3f_3234_, v___y_3235_, v___y_3236_, lean_box(0));
return v___x_3244_;
}
v___jp_3245_:
{
lean_object* v_toConstantVal_3248_; uint8_t v_safety_3249_; uint8_t v___x_3250_; uint8_t v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v_toConstantVal_3248_ = lean_ctor_get(v_defn_3229_, 0);
v_safety_3249_ = lean_ctor_get_uint8(v_defn_3229_, sizeof(void*)*4);
v___x_3250_ = 0;
v___x_3251_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3249_, v___x_3250_);
lean_inc_ref(v_toConstantVal_3248_);
v___x_3252_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3252_, 0, v_toConstantVal_3248_);
lean_ctor_set_uint8(v___x_3252_, sizeof(void*)*1, v___x_3251_);
v___x_3253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3252_);
v___x_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3253_);
v_exportedInfo_x3f_3234_ = v___x_3254_;
v___y_3235_ = v___y_3246_;
v___y_3236_ = v___y_3247_;
goto v___jp_3233_;
}
v___jp_3257_:
{
lean_object* v_options_3258_; uint8_t v_hasTrace_3259_; 
v_options_3258_ = lean_ctor_get(v___y_3230_, 2);
v_hasTrace_3259_ = lean_ctor_get_uint8(v_options_3258_, sizeof(void*)*1);
if (v_hasTrace_3259_ == 0)
{
lean_dec(v_cls_3225_);
v___y_3246_ = v___y_3230_;
v___y_3247_ = v___y_3231_;
goto v___jp_3245_;
}
else
{
lean_object* v_inheritedTraceOptions_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; uint8_t v___x_3263_; 
v_inheritedTraceOptions_3260_ = lean_ctor_get(v___y_3230_, 13);
v___x_3261_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3225_);
v___x_3262_ = l_Lean_Name_append(v___x_3261_, v_cls_3225_);
v___x_3263_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3260_, v_options_3258_, v___x_3262_);
lean_dec(v___x_3262_);
if (v___x_3263_ == 0)
{
lean_dec(v_cls_3225_);
v___y_3246_ = v___y_3230_;
v___y_3247_ = v___y_3231_;
goto v___jp_3245_;
}
else
{
lean_object* v_toConstantVal_3264_; lean_object* v_name_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v_toConstantVal_3264_ = lean_ctor_get(v_defn_3229_, 0);
v_name_3265_ = lean_ctor_get(v_toConstantVal_3264_, 0);
v___x_3266_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_3265_);
v___x_3267_ = l_Lean_MessageData_ofName(v_name_3265_);
v___x_3268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3266_);
lean_ctor_set(v___x_3268_, 1, v___x_3267_);
v___x_3269_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_3270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3268_);
lean_ctor_set(v___x_3270_, 1, v___x_3269_);
v___x_3271_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3225_, v___x_3270_, v___y_3230_, v___y_3231_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_dec_ref_known(v___x_3271_, 1);
v___y_3246_ = v___y_3230_;
v___y_3247_ = v___y_3231_;
goto v___jp_3245_;
}
else
{
lean_dec_ref(v_defn_3229_);
lean_dec_ref(v___f_3224_);
return v___x_3271_;
}
}
}
}
v___jp_3274_:
{
lean_object* v___x_3275_; uint8_t v_isModule_3276_; 
v___x_3275_ = l_Lean_Environment_header(v_env_3272_);
lean_dec_ref(v_env_3272_);
v_isModule_3276_ = lean_ctor_get_uint8(v___x_3275_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3275_);
if (v_isModule_3276_ == 0)
{
lean_dec_ref(v_env_3273_);
lean_dec(v_cls_3225_);
v_exportedInfo_x3f_3234_ = v___x_3226_;
v___y_3235_ = v___y_3230_;
v___y_3236_ = v___y_3231_;
goto v___jp_3233_;
}
else
{
uint8_t v_isExporting_3277_; 
v_isExporting_3277_ = lean_ctor_get_uint8(v_env_3273_, sizeof(void*)*8);
lean_dec_ref(v_env_3273_);
if (v_isExporting_3277_ == 0)
{
lean_dec(v___x_3226_);
goto v___jp_3257_;
}
else
{
if (v___x_3227_ == 0)
{
lean_dec(v_cls_3225_);
v_exportedInfo_x3f_3234_ = v___x_3226_;
v___y_3235_ = v___y_3230_;
v___y_3236_ = v___y_3231_;
goto v___jp_3233_;
}
else
{
lean_dec(v___x_3226_);
goto v___jp_3257_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___boxed(lean_object* v___f_3278_, lean_object* v_cls_3279_, lean_object* v___x_3280_, lean_object* v___x_3281_, lean_object* v_forceExpose_3282_, lean_object* v_defn_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
uint8_t v___x_63218__boxed_3287_; uint8_t v_forceExpose_boxed_3288_; lean_object* v_res_3289_; 
v___x_63218__boxed_3287_ = lean_unbox(v___x_3281_);
v_forceExpose_boxed_3288_ = lean_unbox(v_forceExpose_3282_);
v_res_3289_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v___f_3278_, v_cls_3279_, v___x_3280_, v___x_63218__boxed_3287_, v_forceExpose_boxed_3288_, v_defn_3283_, v___y_3284_, v___y_3285_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(lean_object* v_val_3290_, lean_object* v___f_3291_, lean_object* v_____r_3292_, lean_object* v_exportedInfo_x3f_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
lean_object* v_toConstantVal_3297_; lean_object* v_name_3298_; lean_object* v___x_3299_; uint8_t v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v_toConstantVal_3297_ = lean_ctor_get(v_val_3290_, 0);
v_name_3298_ = lean_ctor_get(v_toConstantVal_3297_, 0);
lean_inc(v_name_3298_);
v___x_3299_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3299_, 0, v_val_3290_);
v___x_3300_ = 1;
v___x_3301_ = lean_box(v___x_3300_);
v___x_3302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3299_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
v___x_3303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3303_, 0, v_name_3298_);
lean_ctor_set(v___x_3303_, 1, v___x_3302_);
lean_inc(v___y_3295_);
lean_inc_ref(v___y_3294_);
v___x_3304_ = lean_apply_5(v___f_3291_, v___x_3303_, v_exportedInfo_x3f_3293_, v___y_3294_, v___y_3295_, lean_box(0));
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed(lean_object* v_val_3305_, lean_object* v___f_3306_, lean_object* v_____r_3307_, lean_object* v_exportedInfo_x3f_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v_val_3305_, v___f_3306_, v_____r_3307_, v_exportedInfo_x3f_3308_, v___y_3309_, v___y_3310_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(lean_object* v_val_3313_, uint8_t v___x_3314_, lean_object* v___f_3315_, lean_object* v_____r_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_){
_start:
{
lean_object* v_toConstantVal_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v_toConstantVal_3320_ = lean_ctor_get(v_val_3313_, 0);
lean_inc_ref(v_toConstantVal_3320_);
v___x_3321_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3321_, 0, v_toConstantVal_3320_);
lean_ctor_set_uint8(v___x_3321_, sizeof(void*)*1, v___x_3314_);
v___x_3322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3321_);
v___x_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3322_);
v___x_3324_ = lean_box(0);
lean_inc(v___y_3318_);
lean_inc_ref(v___y_3317_);
v___x_3325_ = lean_apply_5(v___f_3315_, v___x_3324_, v___x_3323_, v___y_3317_, v___y_3318_, lean_box(0));
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed(lean_object* v_val_3326_, lean_object* v___x_3327_, lean_object* v___f_3328_, lean_object* v_____r_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
uint8_t v___x_63337__boxed_3333_; lean_object* v_res_3334_; 
v___x_63337__boxed_3333_ = lean_unbox(v___x_3327_);
v_res_3334_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(v_val_3326_, v___x_63337__boxed_3333_, v___f_3328_, v_____r_3329_, v___y_3330_, v___y_3331_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec_ref(v_val_3326_);
return v_res_3334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(lean_object* v_val_3335_, lean_object* v___f_3336_, lean_object* v_____r_3337_, lean_object* v_exportedInfo_x3f_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_){
_start:
{
lean_object* v_toConstantVal_3342_; lean_object* v_name_3343_; lean_object* v___x_3344_; uint8_t v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; 
v_toConstantVal_3342_ = lean_ctor_get(v_val_3335_, 0);
v_name_3343_ = lean_ctor_get(v_toConstantVal_3342_, 0);
lean_inc(v_name_3343_);
v___x_3344_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3344_, 0, v_val_3335_);
v___x_3345_ = 3;
v___x_3346_ = lean_box(v___x_3345_);
v___x_3347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3344_);
lean_ctor_set(v___x_3347_, 1, v___x_3346_);
v___x_3348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3348_, 0, v_name_3343_);
lean_ctor_set(v___x_3348_, 1, v___x_3347_);
lean_inc(v___y_3340_);
lean_inc_ref(v___y_3339_);
v___x_3349_ = lean_apply_5(v___f_3336_, v___x_3348_, v_exportedInfo_x3f_3338_, v___y_3339_, v___y_3340_, lean_box(0));
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed(lean_object* v_val_3350_, lean_object* v___f_3351_, lean_object* v_____r_3352_, lean_object* v_exportedInfo_x3f_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
lean_object* v_res_3357_; 
v_res_3357_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(v_val_3350_, v___f_3351_, v_____r_3352_, v_exportedInfo_x3f_3353_, v___y_3354_, v___y_3355_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
return v_res_3357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(lean_object* v_val_3358_, lean_object* v___f_3359_, lean_object* v_____r_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_){
_start:
{
lean_object* v_toConstantVal_3364_; uint8_t v_isUnsafe_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
v_toConstantVal_3364_ = lean_ctor_get(v_val_3358_, 0);
v_isUnsafe_3365_ = lean_ctor_get_uint8(v_val_3358_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_3364_);
v___x_3366_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3366_, 0, v_toConstantVal_3364_);
lean_ctor_set_uint8(v___x_3366_, sizeof(void*)*1, v_isUnsafe_3365_);
v___x_3367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3366_);
v___x_3368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3367_);
v___x_3369_ = lean_box(0);
lean_inc(v___y_3362_);
lean_inc_ref(v___y_3361_);
v___x_3370_ = lean_apply_5(v___f_3359_, v___x_3369_, v___x_3368_, v___y_3361_, v___y_3362_, lean_box(0));
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed(lean_object* v_val_3371_, lean_object* v___f_3372_, lean_object* v_____r_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_val_3371_, v___f_3372_, v_____r_3373_, v___y_3374_, v___y_3375_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
lean_dec_ref(v_val_3371_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(lean_object* v_decl_3378_, uint8_t v___x_3379_, lean_object* v_cls_3380_, lean_object* v___x_3381_, lean_object* v___x_3382_, lean_object* v_____x_3383_, lean_object* v_exportedInfo_x3f_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v_a_3391_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v_a_3404_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; uint8_t v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v_snd_3488_; lean_object* v_fst_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3618_; 
v_snd_3488_ = lean_ctor_get(v_____x_3383_, 1);
v_fst_3489_ = lean_ctor_get(v_____x_3383_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v_____x_3383_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3491_ = v_____x_3383_;
v_isShared_3492_ = v_isSharedCheck_3618_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_snd_3488_);
lean_inc(v_fst_3489_);
lean_dec(v_____x_3383_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3618_;
goto v_resetjp_3490_;
}
v___jp_3388_:
{
lean_object* v___x_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3399_; 
v___x_3392_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3389_, v___y_3390_);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3399_ == 0)
{
lean_object* v_unused_3400_; 
v_unused_3400_ = lean_ctor_get(v___x_3392_, 0);
lean_dec(v_unused_3400_);
v___x_3394_ = v___x_3392_;
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
else
{
lean_dec(v___x_3392_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3397_; 
if (v_isShared_3395_ == 0)
{
lean_ctor_set_tag(v___x_3394_, 1);
lean_ctor_set(v___x_3394_, 0, v_a_3391_);
v___x_3397_ = v___x_3394_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_a_3391_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
}
v___jp_3401_:
{
lean_object* v___x_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3412_; 
v___x_3405_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3402_, v___y_3403_);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3412_ == 0)
{
lean_object* v_unused_3413_; 
v_unused_3413_ = lean_ctor_get(v___x_3405_, 0);
lean_dec(v_unused_3413_);
v___x_3407_ = v___x_3405_;
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
else
{
lean_dec(v___x_3405_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3410_; 
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 0, v_a_3404_);
v___x_3410_ = v___x_3407_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_a_3404_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
v___jp_3414_:
{
lean_object* v___x_3426_; 
lean_inc_ref(v___y_3415_);
v___x_3426_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3422_, v___y_3415_, v___y_3424_, v___y_3425_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v___x_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3473_; 
lean_dec_ref_known(v___x_3426_, 1);
lean_inc_ref(v___y_3417_);
v___x_3427_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3417_, v___y_3421_);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3473_ == 0)
{
lean_object* v_unused_3474_; 
v_unused_3474_ = lean_ctor_get(v___x_3427_, 0);
lean_dec(v_unused_3474_);
v___x_3429_ = v___x_3427_;
v_isShared_3430_ = v_isSharedCheck_3473_;
goto v_resetjp_3428_;
}
else
{
lean_dec(v___x_3427_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3473_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v_options_3431_; lean_object* v___x_3432_; uint8_t v___x_3433_; 
v_options_3431_ = lean_ctor_get(v___y_3423_, 2);
v___x_3432_ = l_Lean_Elab_async;
v___x_3433_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3431_, v___x_3432_);
if (v___x_3433_ == 0)
{
lean_object* v___x_3434_; lean_object* v_r_3435_; 
lean_del_object(v___x_3429_);
lean_dec_ref(v___y_3418_);
lean_dec_ref(v___y_3416_);
v___x_3434_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3415_, v___y_3421_);
lean_dec_ref(v___x_3434_);
v_r_3435_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3378_, v___y_3423_, v___y_3421_);
if (lean_obj_tag(v_r_3435_) == 0)
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3445_; 
v_a_3436_ = lean_ctor_get(v_r_3435_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v_r_3435_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3438_ = v_r_3435_;
v_isShared_3439_ = v_isSharedCheck_3445_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v_r_3435_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3445_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
lean_inc(v_a_3436_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set_tag(v___x_3438_, 1);
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3436_);
v___x_3441_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
lean_object* v___x_3442_; 
v___x_3442_ = lean_apply_2(v___y_3419_, v___x_3441_, lean_box(0));
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_dec_ref_known(v___x_3442_, 1);
v___y_3402_ = v___y_3417_;
v___y_3403_ = v___y_3421_;
v_a_3404_ = v_a_3436_;
goto v___jp_3401_;
}
else
{
lean_object* v_a_3443_; 
lean_dec(v_a_3436_);
v_a_3443_ = lean_ctor_get(v___x_3442_, 0);
lean_inc(v_a_3443_);
lean_dec_ref_known(v___x_3442_, 1);
v___y_3389_ = v___y_3417_;
v___y_3390_ = v___y_3421_;
v_a_3391_ = v_a_3443_;
goto v___jp_3388_;
}
}
}
}
else
{
lean_object* v_a_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v_a_3446_ = lean_ctor_get(v_r_3435_, 0);
lean_inc(v_a_3446_);
lean_dec_ref_known(v_r_3435_, 1);
v___x_3447_ = lean_box(0);
v___x_3448_ = lean_apply_2(v___y_3419_, v___x_3447_, lean_box(0));
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_dec_ref_known(v___x_3448_, 1);
v___y_3389_ = v___y_3417_;
v___y_3390_ = v___y_3421_;
v_a_3391_ = v_a_3446_;
goto v___jp_3388_;
}
else
{
lean_object* v_a_3449_; 
lean_dec(v_a_3446_);
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
lean_inc(v_a_3449_);
lean_dec_ref_known(v___x_3448_, 1);
v___y_3389_ = v___y_3417_;
v___y_3390_ = v___y_3421_;
v_a_3391_ = v_a_3449_;
goto v___jp_3388_;
}
}
}
else
{
lean_object* v___x_3450_; lean_object* v___x_3452_; 
lean_dec_ref(v___y_3419_);
lean_dec_ref(v___y_3417_);
lean_dec_ref(v___y_3415_);
lean_dec(v_decl_3378_);
v___x_3450_ = l_IO_CancelToken_new();
if (v_isShared_3430_ == 0)
{
lean_ctor_set_tag(v___x_3429_, 1);
lean_ctor_set(v___x_3429_, 0, v___x_3450_);
v___x_3452_ = v___x_3429_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3450_);
v___x_3452_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3453_ = lean_unsigned_to_nat(0u);
v___x_3454_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_3455_ = l_Lean_Name_toString(v___x_3454_, v___x_3379_);
lean_inc_ref(v___x_3452_);
v___x_3456_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3416_, v___x_3452_, v___x_3455_, v___y_3423_, v___y_3421_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; lean_object* v_checked_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
lean_inc(v_a_3457_);
lean_dec_ref_known(v___x_3456_, 1);
v_checked_3458_ = lean_ctor_get(v___y_3418_, 2);
lean_inc_ref(v_checked_3458_);
lean_dec_ref(v___y_3418_);
v___x_3459_ = lean_io_map_task(v_a_3457_, v_checked_3458_, v___x_3453_, v___y_3420_);
v___x_3460_ = lean_box(0);
v___x_3461_ = lean_box(2);
v___x_3462_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3460_);
lean_ctor_set(v___x_3462_, 1, v___x_3461_);
lean_ctor_set(v___x_3462_, 2, v___x_3452_);
lean_ctor_set(v___x_3462_, 3, v___x_3459_);
v___x_3463_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3462_, v___y_3421_);
return v___x_3463_;
}
else
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
lean_dec_ref(v___x_3452_);
lean_dec_ref(v___y_3418_);
v_a_3464_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3456_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3456_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3487_; 
lean_dec_ref(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec(v_decl_3378_);
v_a_3475_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3477_ = v___x_3426_;
v_isShared_3478_ = v_isSharedCheck_3487_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3426_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3487_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v_ref_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3485_; 
v_ref_3479_ = lean_ctor_get(v___y_3423_, 5);
v___x_3480_ = lean_io_error_to_string(v_a_3475_);
v___x_3481_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3480_);
v___x_3482_ = l_Lean_MessageData_ofFormat(v___x_3481_);
lean_inc(v_ref_3479_);
v___x_3483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3483_, 0, v_ref_3479_);
lean_ctor_set(v___x_3483_, 1, v___x_3482_);
if (v_isShared_3478_ == 0)
{
lean_ctor_set(v___x_3477_, 0, v___x_3483_);
v___x_3485_ = v___x_3477_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3483_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
}
v_resetjp_3490_:
{
lean_object* v_fst_3493_; lean_object* v_snd_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3617_; 
v_fst_3493_ = lean_ctor_get(v_snd_3488_, 0);
v_snd_3494_ = lean_ctor_get(v_snd_3488_, 1);
v_isSharedCheck_3617_ = !lean_is_exclusive(v_snd_3488_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3496_ = v_snd_3488_;
v_isShared_3497_ = v_isSharedCheck_3617_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_snd_3494_);
lean_inc(v_fst_3493_);
lean_dec(v_snd_3488_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3617_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v_exportedInfo_x3f_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3551_; lean_object* v___y_3552_; uint8_t v___y_3553_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___x_3607_; lean_object* v_env_3608_; uint8_t v___x_3609_; 
v___x_3607_ = lean_st_ref_get(v___y_3386_);
v_env_3608_ = lean_ctor_get(v___x_3607_, 0);
lean_inc_ref(v_env_3608_);
lean_dec(v___x_3607_);
v___x_3609_ = l_Lean_Environment_containsOnBranch(v_env_3608_, v_fst_3489_);
lean_dec_ref(v_env_3608_);
if (v___x_3609_ == 0)
{
lean_del_object(v___x_3491_);
v___y_3583_ = v___y_3385_;
v___y_3584_ = v___y_3386_;
goto v___jp_3582_;
}
else
{
lean_object* v___x_3610_; lean_object* v_env_3611_; lean_object* v___x_3612_; lean_object* v___x_3614_; 
lean_del_object(v___x_3496_);
lean_dec(v_snd_3494_);
lean_dec(v_fst_3493_);
lean_dec(v_exportedInfo_x3f_3384_);
lean_dec(v___x_3382_);
lean_dec_ref(v___x_3381_);
lean_dec(v_cls_3380_);
lean_dec(v_decl_3378_);
v___x_3610_ = lean_st_ref_get(v___y_3386_);
v_env_3611_ = lean_ctor_get(v___x_3610_, 0);
lean_inc_ref(v_env_3611_);
lean_dec(v___x_3610_);
v___x_3612_ = lean_elab_environment_to_kernel_env(v_env_3611_);
if (v_isShared_3492_ == 0)
{
lean_ctor_set_tag(v___x_3491_, 1);
lean_ctor_set(v___x_3491_, 1, v_fst_3489_);
lean_ctor_set(v___x_3491_, 0, v___x_3612_);
v___x_3614_ = v___x_3491_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v___x_3612_);
lean_ctor_set(v_reuseFailAlloc_3616_, 1, v_fst_3489_);
v___x_3614_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
lean_object* v___x_3615_; 
v___x_3615_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3614_, v___y_3385_, v___y_3386_);
return v___x_3615_;
}
}
v___jp_3498_:
{
uint8_t v___x_3506_; uint8_t v___x_3507_; lean_object* v___x_3508_; 
v___x_3506_ = 0;
v___x_3507_ = lean_unbox(v_snd_3494_);
lean_dec(v_snd_3494_);
lean_inc_ref(v___y_3500_);
v___x_3508_ = l_Lean_Environment_addConstAsync(v___y_3500_, v_fst_3489_, v___x_3507_, v___y_3505_, v___x_3506_, v___x_3379_);
if (lean_obj_tag(v___x_3508_) == 0)
{
lean_object* v_a_3509_; lean_object* v_mainEnv_3510_; lean_object* v_asyncEnv_3511_; lean_object* v___f_3512_; lean_object* v___f_3513_; lean_object* v___x_3514_; 
lean_del_object(v___x_3496_);
v_a_3509_ = lean_ctor_get(v___x_3508_, 0);
lean_inc_n(v_a_3509_, 3);
lean_dec_ref_known(v___x_3508_, 1);
v_mainEnv_3510_ = lean_ctor_get(v_a_3509_, 0);
lean_inc_ref(v_mainEnv_3510_);
v_asyncEnv_3511_ = lean_ctor_get(v_a_3509_, 1);
lean_inc_ref_n(v_asyncEnv_3511_, 2);
lean_inc_ref(v___y_3501_);
lean_inc(v___y_3499_);
v___f_3512_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3512_, 0, v___y_3499_);
lean_closure_set(v___f_3512_, 1, v_a_3509_);
lean_closure_set(v___f_3512_, 2, v___y_3501_);
lean_inc(v_decl_3378_);
v___f_3513_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3513_, 0, v_asyncEnv_3511_);
lean_closure_set(v___f_3513_, 1, v_a_3509_);
lean_closure_set(v___f_3513_, 2, v_decl_3378_);
v___x_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3514_, 0, v_fst_3493_);
if (lean_obj_tag(v___y_3504_) == 0)
{
lean_inc_ref(v___x_3514_);
v___y_3415_ = v_asyncEnv_3511_;
v___y_3416_ = v___f_3513_;
v___y_3417_ = v_mainEnv_3510_;
v___y_3418_ = v___y_3500_;
v___y_3419_ = v___f_3512_;
v___y_3420_ = v___x_3506_;
v___y_3421_ = v___y_3502_;
v___y_3422_ = v_a_3509_;
v___y_3423_ = v___y_3503_;
v___y_3424_ = v___x_3514_;
v___y_3425_ = v___x_3514_;
goto v___jp_3414_;
}
else
{
v___y_3415_ = v_asyncEnv_3511_;
v___y_3416_ = v___f_3513_;
v___y_3417_ = v_mainEnv_3510_;
v___y_3418_ = v___y_3500_;
v___y_3419_ = v___f_3512_;
v___y_3420_ = v___x_3506_;
v___y_3421_ = v___y_3502_;
v___y_3422_ = v_a_3509_;
v___y_3423_ = v___y_3503_;
v___y_3424_ = v___x_3514_;
v___y_3425_ = v___y_3504_;
goto v___jp_3414_;
}
}
else
{
lean_object* v_a_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3529_; 
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3500_);
lean_dec(v_fst_3493_);
lean_dec(v_decl_3378_);
v_a_3515_ = lean_ctor_get(v___x_3508_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3517_ = v___x_3508_;
v_isShared_3518_ = v_isSharedCheck_3529_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_a_3515_);
lean_dec(v___x_3508_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3529_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v_ref_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3524_; 
v_ref_3519_ = lean_ctor_get(v___y_3503_, 5);
v___x_3520_ = lean_io_error_to_string(v_a_3515_);
v___x_3521_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
v___x_3522_ = l_Lean_MessageData_ofFormat(v___x_3521_);
lean_inc(v_ref_3519_);
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 1, v___x_3522_);
lean_ctor_set(v___x_3496_, 0, v_ref_3519_);
v___x_3524_ = v___x_3496_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_ref_3519_);
lean_ctor_set(v_reuseFailAlloc_3528_, 1, v___x_3522_);
v___x_3524_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
lean_object* v___x_3526_; 
if (v_isShared_3518_ == 0)
{
lean_ctor_set(v___x_3517_, 0, v___x_3524_);
v___x_3526_ = v___x_3517_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3524_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
}
}
v___jp_3530_:
{
lean_object* v___x_3534_; 
v___x_3534_ = lean_st_ref_get(v___y_3533_);
if (lean_obj_tag(v_exportedInfo_x3f_3531_) == 0)
{
lean_object* v_env_3535_; lean_object* v___x_3536_; 
v_env_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc_ref(v_env_3535_);
lean_dec(v___x_3534_);
v___x_3536_ = lean_box(0);
v___y_3499_ = v___y_3533_;
v___y_3500_ = v_env_3535_;
v___y_3501_ = v___y_3532_;
v___y_3502_ = v___y_3533_;
v___y_3503_ = v___y_3532_;
v___y_3504_ = v_exportedInfo_x3f_3531_;
v___y_3505_ = v___x_3536_;
goto v___jp_3498_;
}
else
{
lean_object* v_env_3537_; lean_object* v_val_3538_; uint8_t v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v_env_3537_ = lean_ctor_get(v___x_3534_, 0);
lean_inc_ref(v_env_3537_);
lean_dec(v___x_3534_);
v_val_3538_ = lean_ctor_get(v_exportedInfo_x3f_3531_, 0);
v___x_3539_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3538_);
v___x_3540_ = lean_box(v___x_3539_);
v___x_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3540_);
v___y_3499_ = v___y_3533_;
v___y_3500_ = v_env_3537_;
v___y_3501_ = v___y_3532_;
v___y_3502_ = v___y_3533_;
v___y_3503_ = v___y_3532_;
v___y_3504_ = v_exportedInfo_x3f_3531_;
v___y_3505_ = v___x_3541_;
goto v___jp_3498_;
}
}
v___jp_3542_:
{
lean_object* v___x_3545_; 
lean_inc(v_fst_3493_);
v___x_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3545_, 0, v_fst_3493_);
v_exportedInfo_x3f_3531_ = v___x_3545_;
v___y_3532_ = v___y_3543_;
v___y_3533_ = v___y_3544_;
goto v___jp_3530_;
}
v___jp_3546_:
{
lean_object* v___x_3549_; 
lean_inc(v_fst_3493_);
v___x_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3549_, 0, v_fst_3493_);
v_exportedInfo_x3f_3531_ = v___x_3549_;
v___y_3532_ = v___y_3547_;
v___y_3533_ = v___y_3548_;
goto v___jp_3530_;
}
v___jp_3550_:
{
if (v___y_3553_ == 0)
{
lean_object* v_options_3554_; uint8_t v_hasTrace_3555_; 
lean_dec(v_exportedInfo_x3f_3384_);
lean_dec_ref(v___x_3381_);
v_options_3554_ = lean_ctor_get(v___y_3552_, 2);
v_hasTrace_3555_ = lean_ctor_get_uint8(v_options_3554_, sizeof(void*)*1);
if (v_hasTrace_3555_ == 0)
{
lean_dec(v_cls_3380_);
v___y_3543_ = v___y_3552_;
v___y_3544_ = v___y_3551_;
goto v___jp_3542_;
}
else
{
lean_object* v_inheritedTraceOptions_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; uint8_t v___x_3559_; 
v_inheritedTraceOptions_3556_ = lean_ctor_get(v___y_3552_, 13);
v___x_3557_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3380_);
v___x_3558_ = l_Lean_Name_append(v___x_3557_, v_cls_3380_);
v___x_3559_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3556_, v_options_3554_, v___x_3558_);
lean_dec(v___x_3558_);
if (v___x_3559_ == 0)
{
lean_dec(v_cls_3380_);
v___y_3543_ = v___y_3552_;
v___y_3544_ = v___y_3551_;
goto v___jp_3542_;
}
else
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3560_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_3561_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3380_, v___x_3560_, v___y_3552_, v___y_3551_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_dec_ref_known(v___x_3561_, 1);
v___y_3543_ = v___y_3552_;
v___y_3544_ = v___y_3551_;
goto v___jp_3542_;
}
else
{
lean_del_object(v___x_3496_);
lean_dec(v_snd_3494_);
lean_dec(v_fst_3493_);
lean_dec(v_fst_3489_);
lean_dec(v_decl_3378_);
return v___x_3561_;
}
}
}
}
else
{
lean_object* v___x_3562_; lean_object* v_env_3563_; lean_object* v_nextMacroScope_3564_; lean_object* v_ngen_3565_; lean_object* v_auxDeclNGen_3566_; lean_object* v_traceState_3567_; lean_object* v_messages_3568_; lean_object* v_infoState_3569_; lean_object* v_snapshotTasks_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3580_; 
lean_dec(v_cls_3380_);
v___x_3562_ = lean_st_ref_take(v___y_3551_);
v_env_3563_ = lean_ctor_get(v___x_3562_, 0);
v_nextMacroScope_3564_ = lean_ctor_get(v___x_3562_, 1);
v_ngen_3565_ = lean_ctor_get(v___x_3562_, 2);
v_auxDeclNGen_3566_ = lean_ctor_get(v___x_3562_, 3);
v_traceState_3567_ = lean_ctor_get(v___x_3562_, 4);
v_messages_3568_ = lean_ctor_get(v___x_3562_, 6);
v_infoState_3569_ = lean_ctor_get(v___x_3562_, 7);
v_snapshotTasks_3570_ = lean_ctor_get(v___x_3562_, 8);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3580_ == 0)
{
lean_object* v_unused_3581_; 
v_unused_3581_ = lean_ctor_get(v___x_3562_, 5);
lean_dec(v_unused_3581_);
v___x_3572_ = v___x_3562_;
v_isShared_3573_ = v_isSharedCheck_3580_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_snapshotTasks_3570_);
lean_inc(v_infoState_3569_);
lean_inc(v_messages_3568_);
lean_inc(v_traceState_3567_);
lean_inc(v_auxDeclNGen_3566_);
lean_inc(v_ngen_3565_);
lean_inc(v_nextMacroScope_3564_);
lean_inc(v_env_3563_);
lean_dec(v___x_3562_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3580_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3577_; 
v___x_3574_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3494_);
lean_inc(v_fst_3489_);
v___x_3575_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3574_, v_env_3563_, v_fst_3489_, v_snd_3494_);
if (v_isShared_3573_ == 0)
{
lean_ctor_set(v___x_3572_, 5, v___x_3381_);
lean_ctor_set(v___x_3572_, 0, v___x_3575_);
v___x_3577_ = v___x_3572_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3575_);
lean_ctor_set(v_reuseFailAlloc_3579_, 1, v_nextMacroScope_3564_);
lean_ctor_set(v_reuseFailAlloc_3579_, 2, v_ngen_3565_);
lean_ctor_set(v_reuseFailAlloc_3579_, 3, v_auxDeclNGen_3566_);
lean_ctor_set(v_reuseFailAlloc_3579_, 4, v_traceState_3567_);
lean_ctor_set(v_reuseFailAlloc_3579_, 5, v___x_3381_);
lean_ctor_set(v_reuseFailAlloc_3579_, 6, v_messages_3568_);
lean_ctor_set(v_reuseFailAlloc_3579_, 7, v_infoState_3569_);
lean_ctor_set(v_reuseFailAlloc_3579_, 8, v_snapshotTasks_3570_);
v___x_3577_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
lean_object* v___x_3578_; 
v___x_3578_ = lean_st_ref_set(v___y_3551_, v___x_3577_);
v_exportedInfo_x3f_3531_ = v_exportedInfo_x3f_3384_;
v___y_3532_ = v___y_3552_;
v___y_3533_ = v___y_3551_;
goto v___jp_3530_;
}
}
}
}
v___jp_3582_:
{
lean_object* v___x_3585_; uint8_t v___x_3586_; 
lean_inc(v_decl_3378_);
v___x_3585_ = l_Lean_Declaration_getTopLevelNames(v_decl_3378_);
v___x_3586_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3585_);
lean_dec(v___x_3585_);
if (v___x_3586_ == 0)
{
lean_dec(v___x_3382_);
if (lean_obj_tag(v_exportedInfo_x3f_3384_) == 0)
{
v___y_3551_ = v___y_3584_;
v___y_3552_ = v___y_3583_;
v___y_3553_ = v___x_3586_;
goto v___jp_3550_;
}
else
{
v___y_3551_ = v___y_3584_;
v___y_3552_ = v___y_3583_;
v___y_3553_ = v___x_3379_;
goto v___jp_3550_;
}
}
else
{
lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v_a_3589_; uint8_t v___x_3590_; 
lean_dec(v_exportedInfo_x3f_3384_);
lean_dec_ref(v___x_3381_);
v___x_3587_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3588_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3587_, v___y_3583_);
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_a_3589_);
lean_dec_ref(v___x_3588_);
v___x_3590_ = lean_unbox(v_a_3589_);
lean_dec(v_a_3589_);
if (v___x_3590_ == 0)
{
lean_object* v_options_3591_; uint8_t v_hasTrace_3592_; 
v_options_3591_ = lean_ctor_get(v___y_3583_, 2);
v_hasTrace_3592_ = lean_ctor_get_uint8(v_options_3591_, sizeof(void*)*1);
if (v_hasTrace_3592_ == 0)
{
lean_dec(v_cls_3380_);
v_exportedInfo_x3f_3531_ = v___x_3382_;
v___y_3532_ = v___y_3583_;
v___y_3533_ = v___y_3584_;
goto v___jp_3530_;
}
else
{
lean_object* v_inheritedTraceOptions_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; uint8_t v___x_3596_; 
v_inheritedTraceOptions_3593_ = lean_ctor_get(v___y_3583_, 13);
v___x_3594_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3380_);
v___x_3595_ = l_Lean_Name_append(v___x_3594_, v_cls_3380_);
v___x_3596_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3593_, v_options_3591_, v___x_3595_);
lean_dec(v___x_3595_);
if (v___x_3596_ == 0)
{
lean_dec(v_cls_3380_);
v_exportedInfo_x3f_3531_ = v___x_3382_;
v___y_3532_ = v___y_3583_;
v___y_3533_ = v___y_3584_;
goto v___jp_3530_;
}
else
{
lean_object* v___x_3597_; lean_object* v___x_3598_; 
v___x_3597_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_3598_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3380_, v___x_3597_, v___y_3583_, v___y_3584_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_dec_ref_known(v___x_3598_, 1);
v_exportedInfo_x3f_3531_ = v___x_3382_;
v___y_3532_ = v___y_3583_;
v___y_3533_ = v___y_3584_;
goto v___jp_3530_;
}
else
{
lean_del_object(v___x_3496_);
lean_dec(v_snd_3494_);
lean_dec(v_fst_3493_);
lean_dec(v_fst_3489_);
lean_dec(v___x_3382_);
lean_dec(v_decl_3378_);
return v___x_3598_;
}
}
}
}
else
{
lean_object* v_options_3599_; uint8_t v_hasTrace_3600_; 
lean_dec(v___x_3382_);
v_options_3599_ = lean_ctor_get(v___y_3583_, 2);
v_hasTrace_3600_ = lean_ctor_get_uint8(v_options_3599_, sizeof(void*)*1);
if (v_hasTrace_3600_ == 0)
{
lean_dec(v_cls_3380_);
v___y_3547_ = v___y_3583_;
v___y_3548_ = v___y_3584_;
goto v___jp_3546_;
}
else
{
lean_object* v_inheritedTraceOptions_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; uint8_t v___x_3604_; 
v_inheritedTraceOptions_3601_ = lean_ctor_get(v___y_3583_, 13);
v___x_3602_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3380_);
v___x_3603_ = l_Lean_Name_append(v___x_3602_, v_cls_3380_);
v___x_3604_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3601_, v_options_3599_, v___x_3603_);
lean_dec(v___x_3603_);
if (v___x_3604_ == 0)
{
lean_dec(v_cls_3380_);
v___y_3547_ = v___y_3583_;
v___y_3548_ = v___y_3584_;
goto v___jp_3546_;
}
else
{
lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3605_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_3606_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3380_, v___x_3605_, v___y_3583_, v___y_3584_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_dec_ref_known(v___x_3606_, 1);
v___y_3547_ = v___y_3583_;
v___y_3548_ = v___y_3584_;
goto v___jp_3546_;
}
else
{
lean_del_object(v___x_3496_);
lean_dec(v_snd_3494_);
lean_dec(v_fst_3493_);
lean_dec(v_fst_3489_);
lean_dec(v_decl_3378_);
return v___x_3606_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed(lean_object* v_decl_3619_, lean_object* v___x_3620_, lean_object* v_cls_3621_, lean_object* v___x_3622_, lean_object* v___x_3623_, lean_object* v_____x_3624_, lean_object* v_exportedInfo_x3f_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
uint8_t v___x_63468__boxed_3629_; lean_object* v_res_3630_; 
v___x_63468__boxed_3629_ = lean_unbox(v___x_3620_);
v_res_3630_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_decl_3619_, v___x_63468__boxed_3629_, v_cls_3621_, v___x_3622_, v___x_3623_, v_____x_3624_, v_exportedInfo_x3f_3625_, v___y_3626_, v___y_3627_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
return v_res_3630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(lean_object* v___f_3631_, uint8_t v_forceExpose_3632_, uint8_t v___x_3633_, lean_object* v___x_3634_, lean_object* v_cls_3635_, lean_object* v_defn_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_){
_start:
{
lean_object* v_exportedInfo_x3f_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3662_ = lean_st_ref_get(v___y_3638_);
v___x_3663_ = lean_st_ref_get(v___y_3638_);
if (v_forceExpose_3632_ == 0)
{
if (v___x_3633_ == 0)
{
lean_dec(v___x_3663_);
lean_dec(v___x_3662_);
lean_dec(v_cls_3635_);
v_exportedInfo_x3f_3641_ = v___x_3634_;
v___y_3642_ = v___y_3637_;
v___y_3643_ = v___y_3638_;
goto v___jp_3640_;
}
else
{
lean_object* v_env_3664_; lean_object* v_env_3665_; lean_object* v___x_3666_; uint8_t v_isModule_3667_; 
v_env_3664_ = lean_ctor_get(v___x_3662_, 0);
lean_inc_ref(v_env_3664_);
lean_dec(v___x_3662_);
v_env_3665_ = lean_ctor_get(v___x_3663_, 0);
lean_inc_ref(v_env_3665_);
lean_dec(v___x_3663_);
v___x_3666_ = l_Lean_Environment_header(v_env_3664_);
lean_dec_ref(v_env_3664_);
v_isModule_3667_ = lean_ctor_get_uint8(v___x_3666_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3666_);
if (v_isModule_3667_ == 0)
{
lean_dec_ref(v_env_3665_);
lean_dec(v_cls_3635_);
v_exportedInfo_x3f_3641_ = v___x_3634_;
v___y_3642_ = v___y_3637_;
v___y_3643_ = v___y_3638_;
goto v___jp_3640_;
}
else
{
uint8_t v_isExporting_3668_; 
v_isExporting_3668_ = lean_ctor_get_uint8(v_env_3665_, sizeof(void*)*8);
lean_dec_ref(v_env_3665_);
if (v_isExporting_3668_ == 0)
{
lean_object* v_options_3669_; uint8_t v_hasTrace_3670_; 
lean_dec(v___x_3634_);
v_options_3669_ = lean_ctor_get(v___y_3637_, 2);
v_hasTrace_3670_ = lean_ctor_get_uint8(v_options_3669_, sizeof(void*)*1);
if (v_hasTrace_3670_ == 0)
{
lean_dec(v_cls_3635_);
v___y_3653_ = v___y_3637_;
v___y_3654_ = v___y_3638_;
goto v___jp_3652_;
}
else
{
lean_object* v_inheritedTraceOptions_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; uint8_t v___x_3674_; 
v_inheritedTraceOptions_3671_ = lean_ctor_get(v___y_3637_, 13);
v___x_3672_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3635_);
v___x_3673_ = l_Lean_Name_append(v___x_3672_, v_cls_3635_);
v___x_3674_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3671_, v_options_3669_, v___x_3673_);
lean_dec(v___x_3673_);
if (v___x_3674_ == 0)
{
lean_dec(v_cls_3635_);
v___y_3653_ = v___y_3637_;
v___y_3654_ = v___y_3638_;
goto v___jp_3652_;
}
else
{
lean_object* v_toConstantVal_3675_; lean_object* v_name_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
v_toConstantVal_3675_ = lean_ctor_get(v_defn_3636_, 0);
v_name_3676_ = lean_ctor_get(v_toConstantVal_3675_, 0);
v___x_3677_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_3676_);
v___x_3678_ = l_Lean_MessageData_ofName(v_name_3676_);
v___x_3679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3677_);
lean_ctor_set(v___x_3679_, 1, v___x_3678_);
v___x_3680_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_3681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3679_);
lean_ctor_set(v___x_3681_, 1, v___x_3680_);
v___x_3682_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3635_, v___x_3681_, v___y_3637_, v___y_3638_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_dec_ref_known(v___x_3682_, 1);
v___y_3653_ = v___y_3637_;
v___y_3654_ = v___y_3638_;
goto v___jp_3652_;
}
else
{
lean_dec_ref(v_defn_3636_);
lean_dec_ref(v___f_3631_);
return v___x_3682_;
}
}
}
}
else
{
lean_dec(v_cls_3635_);
v_exportedInfo_x3f_3641_ = v___x_3634_;
v___y_3642_ = v___y_3637_;
v___y_3643_ = v___y_3638_;
goto v___jp_3640_;
}
}
}
}
else
{
lean_dec(v___x_3663_);
lean_dec(v___x_3662_);
lean_dec(v_cls_3635_);
v_exportedInfo_x3f_3641_ = v___x_3634_;
v___y_3642_ = v___y_3637_;
v___y_3643_ = v___y_3638_;
goto v___jp_3640_;
}
v___jp_3640_:
{
lean_object* v_toConstantVal_3644_; lean_object* v_name_3645_; lean_object* v___x_3646_; uint8_t v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
v_toConstantVal_3644_ = lean_ctor_get(v_defn_3636_, 0);
v_name_3645_ = lean_ctor_get(v_toConstantVal_3644_, 0);
lean_inc(v_name_3645_);
v___x_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3646_, 0, v_defn_3636_);
v___x_3647_ = 0;
v___x_3648_ = lean_box(v___x_3647_);
v___x_3649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3646_);
lean_ctor_set(v___x_3649_, 1, v___x_3648_);
v___x_3650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3650_, 0, v_name_3645_);
lean_ctor_set(v___x_3650_, 1, v___x_3649_);
lean_inc(v___y_3643_);
lean_inc_ref(v___y_3642_);
v___x_3651_ = lean_apply_5(v___f_3631_, v___x_3650_, v_exportedInfo_x3f_3641_, v___y_3642_, v___y_3643_, lean_box(0));
return v___x_3651_;
}
v___jp_3652_:
{
lean_object* v_toConstantVal_3655_; uint8_t v_safety_3656_; uint8_t v___x_3657_; uint8_t v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v_toConstantVal_3655_ = lean_ctor_get(v_defn_3636_, 0);
v_safety_3656_ = lean_ctor_get_uint8(v_defn_3636_, sizeof(void*)*4);
v___x_3657_ = 0;
v___x_3658_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3656_, v___x_3657_);
lean_inc_ref(v_toConstantVal_3655_);
v___x_3659_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3659_, 0, v_toConstantVal_3655_);
lean_ctor_set_uint8(v___x_3659_, sizeof(void*)*1, v___x_3658_);
v___x_3660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3659_);
v___x_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3660_);
v_exportedInfo_x3f_3641_ = v___x_3661_;
v___y_3642_ = v___y_3653_;
v___y_3643_ = v___y_3654_;
goto v___jp_3640_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10___boxed(lean_object* v___f_3683_, lean_object* v_forceExpose_3684_, lean_object* v___x_3685_, lean_object* v___x_3686_, lean_object* v_cls_3687_, lean_object* v_defn_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_){
_start:
{
uint8_t v_forceExpose_boxed_3692_; uint8_t v___x_63943__boxed_3693_; lean_object* v_res_3694_; 
v_forceExpose_boxed_3692_ = lean_unbox(v_forceExpose_3684_);
v___x_63943__boxed_3693_ = lean_unbox(v___x_3685_);
v_res_3694_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v___f_3683_, v_forceExpose_boxed_3692_, v___x_63943__boxed_3693_, v___x_3686_, v_cls_3687_, v_defn_3688_, v___y_3689_, v___y_3690_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
return v_res_3694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(lean_object* v_val_3695_, uint8_t v_forceExpose_3696_, lean_object* v___f_3697_, lean_object* v_____r_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
lean_object* v_toConstantVal_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v_toConstantVal_3702_ = lean_ctor_get(v_val_3695_, 0);
lean_inc_ref(v_toConstantVal_3702_);
v___x_3703_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3703_, 0, v_toConstantVal_3702_);
lean_ctor_set_uint8(v___x_3703_, sizeof(void*)*1, v_forceExpose_3696_);
v___x_3704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3703_);
v___x_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3704_);
v___x_3706_ = lean_box(0);
lean_inc(v___y_3700_);
lean_inc_ref(v___y_3699_);
v___x_3707_ = lean_apply_5(v___f_3697_, v___x_3706_, v___x_3705_, v___y_3699_, v___y_3700_, lean_box(0));
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12___boxed(lean_object* v_val_3708_, lean_object* v_forceExpose_3709_, lean_object* v___f_3710_, lean_object* v_____r_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_){
_start:
{
uint8_t v_forceExpose_boxed_3715_; lean_object* v_res_3716_; 
v_forceExpose_boxed_3715_ = lean_unbox(v_forceExpose_3709_);
v_res_3716_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(v_val_3708_, v_forceExpose_boxed_3715_, v___f_3710_, v_____r_3711_, v___y_3712_, v___y_3713_);
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
lean_dec_ref(v_val_3708_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(lean_object* v_x_3717_, lean_object* v_x_3718_){
_start:
{
if (lean_obj_tag(v_x_3718_) == 0)
{
return v_x_3717_;
}
else
{
lean_object* v_head_3719_; lean_object* v_tail_3720_; lean_object* v___x_3721_; 
v_head_3719_ = lean_ctor_get(v_x_3718_, 0);
lean_inc(v_head_3719_);
v_tail_3720_ = lean_ctor_get(v_x_3718_, 1);
lean_inc(v_tail_3720_);
lean_dec_ref_known(v_x_3718_, 2);
v___x_3721_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(v_x_3717_, v_head_3719_);
v_x_3717_ = v___x_3721_;
v_x_3718_ = v_tail_3720_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0(void){
_start:
{
lean_object* v_cls_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; 
v_cls_3723_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_3724_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
v___x_3725_ = l_Lean_Name_append(v___x_3724_, v_cls_3723_);
return v___x_3725_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2(void){
_start:
{
lean_object* v___x_3727_; lean_object* v___x_3728_; 
v___x_3727_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1));
v___x_3728_ = l_Lean_stringToMessageData(v___x_3727_);
return v___x_3728_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4(void){
_start:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3730_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3));
v___x_3731_ = l_Lean_stringToMessageData(v___x_3730_);
return v___x_3731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore(lean_object* v_decl_3732_, uint8_t v_forceExpose_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_){
_start:
{
lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v_a_3740_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v_a_3753_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v_a_3766_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v_a_3779_; lean_object* v_options_3789_; lean_object* v_inheritedTraceOptions_3790_; uint8_t v_hasTrace_3791_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; uint8_t v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3871_; uint8_t v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3899_; uint8_t v___y_3900_; lean_object* v___y_3901_; lean_object* v_exportedInfo_x3f_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3914_; uint8_t v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3921_; uint8_t v___y_3922_; lean_object* v___y_3923_; lean_object* v___y_3924_; lean_object* v___y_3925_; lean_object* v_cls_3927_; 
v_options_3789_ = lean_ctor_get(v_a_3734_, 2);
v_inheritedTraceOptions_3790_ = lean_ctor_get(v_a_3734_, 13);
v_hasTrace_3791_ = lean_ctor_get_uint8(v_options_3789_, sizeof(void*)*1);
v_cls_3927_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
if (v_hasTrace_3791_ == 0)
{
lean_object* v___x_3928_; lean_object* v_env_3929_; lean_object* v_nextMacroScope_3930_; lean_object* v_ngen_3931_; lean_object* v_auxDeclNGen_3932_; lean_object* v_traceState_3933_; lean_object* v_messages_3934_; lean_object* v_infoState_3935_; lean_object* v_snapshotTasks_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_4125_; 
v___x_3928_ = lean_st_ref_take(v_a_3735_);
v_env_3929_ = lean_ctor_get(v___x_3928_, 0);
v_nextMacroScope_3930_ = lean_ctor_get(v___x_3928_, 1);
v_ngen_3931_ = lean_ctor_get(v___x_3928_, 2);
v_auxDeclNGen_3932_ = lean_ctor_get(v___x_3928_, 3);
v_traceState_3933_ = lean_ctor_get(v___x_3928_, 4);
v_messages_3934_ = lean_ctor_get(v___x_3928_, 6);
v_infoState_3935_ = lean_ctor_get(v___x_3928_, 7);
v_snapshotTasks_3936_ = lean_ctor_get(v___x_3928_, 8);
v_isSharedCheck_4125_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_4125_ == 0)
{
lean_object* v_unused_4126_; 
v_unused_4126_ = lean_ctor_get(v___x_3928_, 5);
lean_dec(v_unused_4126_);
v___x_3938_ = v___x_3928_;
v_isShared_3939_ = v_isSharedCheck_4125_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_snapshotTasks_3936_);
lean_inc(v_infoState_3935_);
lean_inc(v_messages_3934_);
lean_inc(v_traceState_3933_);
lean_inc(v_auxDeclNGen_3932_);
lean_inc(v_ngen_3931_);
lean_inc(v_nextMacroScope_3930_);
lean_inc(v_env_3929_);
lean_dec(v___x_3928_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_4125_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3944_; 
lean_inc(v_decl_3732_);
v___x_3940_ = l_Lean_Declaration_getNames(v_decl_3732_);
v___x_3941_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_3929_, v___x_3940_);
v___x_3942_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_3939_ == 0)
{
lean_ctor_set(v___x_3938_, 5, v___x_3942_);
lean_ctor_set(v___x_3938_, 0, v___x_3941_);
v___x_3944_ = v___x_3938_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v___x_3941_);
lean_ctor_set(v_reuseFailAlloc_4124_, 1, v_nextMacroScope_3930_);
lean_ctor_set(v_reuseFailAlloc_4124_, 2, v_ngen_3931_);
lean_ctor_set(v_reuseFailAlloc_4124_, 3, v_auxDeclNGen_3932_);
lean_ctor_set(v_reuseFailAlloc_4124_, 4, v_traceState_3933_);
lean_ctor_set(v_reuseFailAlloc_4124_, 5, v___x_3942_);
lean_ctor_set(v_reuseFailAlloc_4124_, 6, v_messages_3934_);
lean_ctor_set(v_reuseFailAlloc_4124_, 7, v_infoState_3935_);
lean_ctor_set(v_reuseFailAlloc_4124_, 8, v_snapshotTasks_3936_);
v___x_3944_ = v_reuseFailAlloc_4124_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___y_3948_; lean_object* v___y_3949_; uint8_t v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v_fst_4003_; lean_object* v_fst_4004_; uint8_t v_snd_4005_; lean_object* v_exportedInfo_x3f_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4018_; lean_object* v_toConstantVal_4019_; lean_object* v_exportedInfo_x3f_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4027_; lean_object* v_exportedInfo_x3f_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4033_; lean_object* v_toConstantVal_4034_; uint8_t v_safety_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v_defn_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; 
v___x_3945_ = lean_st_ref_set(v_a_3735_, v___x_3944_);
v___x_3946_ = lean_box(0);
switch(lean_obj_tag(v_decl_3732_))
{
case 2:
{
lean_object* v_val_4074_; lean_object* v_exportedInfo_x3f_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___x_4083_; 
v_val_4074_ = lean_ctor_get(v_decl_3732_, 0);
v___x_4083_ = lean_st_ref_get(v_a_3735_);
if (v_forceExpose_3733_ == 0)
{
lean_object* v_env_4084_; lean_object* v___x_4085_; uint8_t v_isModule_4086_; 
v_env_4084_ = lean_ctor_get(v___x_4083_, 0);
lean_inc_ref(v_env_4084_);
lean_dec(v___x_4083_);
v___x_4085_ = l_Lean_Environment_header(v_env_4084_);
lean_dec_ref(v_env_4084_);
v_isModule_4086_ = lean_ctor_get_uint8(v___x_4085_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4085_);
if (v_isModule_4086_ == 0)
{
v_exportedInfo_x3f_4076_ = v___x_3946_;
v___y_4077_ = v_a_3734_;
v___y_4078_ = v_a_3735_;
goto v___jp_4075_;
}
else
{
lean_object* v_toConstantVal_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v_toConstantVal_4087_ = lean_ctor_get(v_val_4074_, 0);
lean_inc_ref(v_toConstantVal_4087_);
v___x_4088_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4088_, 0, v_toConstantVal_4087_);
lean_ctor_set_uint8(v___x_4088_, sizeof(void*)*1, v_hasTrace_3791_);
v___x_4089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4088_);
v___x_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4089_);
v_exportedInfo_x3f_4076_ = v___x_4090_;
v___y_4077_ = v_a_3734_;
v___y_4078_ = v_a_3735_;
goto v___jp_4075_;
}
}
else
{
lean_dec(v___x_4083_);
v_exportedInfo_x3f_4076_ = v___x_3946_;
v___y_4077_ = v_a_3734_;
v___y_4078_ = v_a_3735_;
goto v___jp_4075_;
}
v___jp_4075_:
{
lean_object* v_toConstantVal_4079_; lean_object* v_name_4080_; lean_object* v___x_4081_; uint8_t v___x_4082_; 
v_toConstantVal_4079_ = lean_ctor_get(v_val_4074_, 0);
v_name_4080_ = lean_ctor_get(v_toConstantVal_4079_, 0);
lean_inc_ref(v_val_4074_);
v___x_4081_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4081_, 0, v_val_4074_);
v___x_4082_ = 1;
lean_inc(v_name_4080_);
v_fst_4003_ = v_name_4080_;
v_fst_4004_ = v___x_4081_;
v_snd_4005_ = v___x_4082_;
v_exportedInfo_x3f_4006_ = v_exportedInfo_x3f_4076_;
v___y_4007_ = v___y_4077_;
v___y_4008_ = v___y_4078_;
goto v___jp_4002_;
}
}
case 1:
{
lean_object* v_val_4091_; 
v_val_4091_ = lean_ctor_get(v_decl_3732_, 0);
lean_inc_ref(v_val_4091_);
v_defn_4050_ = v_val_4091_;
v___y_4051_ = v_a_3734_;
v___y_4052_ = v_a_3735_;
goto v___jp_4049_;
}
case 5:
{
lean_object* v_defns_4092_; 
v_defns_4092_ = lean_ctor_get(v_decl_3732_, 0);
if (lean_obj_tag(v_defns_4092_) == 1)
{
lean_object* v_tail_4093_; 
v_tail_4093_ = lean_ctor_get(v_defns_4092_, 1);
if (lean_obj_tag(v_tail_4093_) == 0)
{
lean_object* v_head_4094_; 
v_head_4094_ = lean_ctor_get(v_defns_4092_, 0);
lean_inc(v_head_4094_);
v_defn_4050_ = v_head_4094_;
v___y_4051_ = v_a_3734_;
v___y_4052_ = v_a_3735_;
goto v___jp_4049_;
}
else
{
lean_object* v___x_4095_; 
v___x_4095_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3732_, v_a_3734_, v_a_3735_);
return v___x_4095_;
}
}
else
{
lean_object* v___x_4096_; 
v___x_4096_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3732_, v_a_3734_, v_a_3735_);
return v___x_4096_;
}
}
case 3:
{
lean_object* v_val_4097_; lean_object* v_exportedInfo_x3f_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___x_4106_; lean_object* v___x_4107_; 
v_val_4097_ = lean_ctor_get(v_decl_3732_, 0);
v___x_4106_ = lean_st_ref_get(v_a_3735_);
v___x_4107_ = lean_st_ref_get(v_a_3735_);
if (v_forceExpose_3733_ == 0)
{
lean_object* v_env_4108_; lean_object* v_env_4109_; lean_object* v___x_4110_; uint8_t v_isModule_4111_; 
v_env_4108_ = lean_ctor_get(v___x_4106_, 0);
lean_inc_ref(v_env_4108_);
lean_dec(v___x_4106_);
v_env_4109_ = lean_ctor_get(v___x_4107_, 0);
lean_inc_ref(v_env_4109_);
lean_dec(v___x_4107_);
v___x_4110_ = l_Lean_Environment_header(v_env_4108_);
lean_dec_ref(v_env_4108_);
v_isModule_4111_ = lean_ctor_get_uint8(v___x_4110_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4110_);
if (v_isModule_4111_ == 0)
{
lean_dec_ref(v_env_4109_);
v_exportedInfo_x3f_4099_ = v___x_3946_;
v___y_4100_ = v_a_3734_;
v___y_4101_ = v_a_3735_;
goto v___jp_4098_;
}
else
{
uint8_t v_isExporting_4112_; 
v_isExporting_4112_ = lean_ctor_get_uint8(v_env_4109_, sizeof(void*)*8);
lean_dec_ref(v_env_4109_);
if (v_isExporting_4112_ == 0)
{
lean_object* v_toConstantVal_4113_; uint8_t v_isUnsafe_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
v_toConstantVal_4113_ = lean_ctor_get(v_val_4097_, 0);
v_isUnsafe_4114_ = lean_ctor_get_uint8(v_val_4097_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4113_);
v___x_4115_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4115_, 0, v_toConstantVal_4113_);
lean_ctor_set_uint8(v___x_4115_, sizeof(void*)*1, v_isUnsafe_4114_);
v___x_4116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4116_, 0, v___x_4115_);
v___x_4117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4116_);
v_exportedInfo_x3f_4099_ = v___x_4117_;
v___y_4100_ = v_a_3734_;
v___y_4101_ = v_a_3735_;
goto v___jp_4098_;
}
else
{
v_exportedInfo_x3f_4099_ = v___x_3946_;
v___y_4100_ = v_a_3734_;
v___y_4101_ = v_a_3735_;
goto v___jp_4098_;
}
}
}
else
{
lean_dec(v___x_4107_);
lean_dec(v___x_4106_);
v_exportedInfo_x3f_4099_ = v___x_3946_;
v___y_4100_ = v_a_3734_;
v___y_4101_ = v_a_3735_;
goto v___jp_4098_;
}
v___jp_4098_:
{
lean_object* v_toConstantVal_4102_; lean_object* v_name_4103_; lean_object* v___x_4104_; uint8_t v___x_4105_; 
v_toConstantVal_4102_ = lean_ctor_get(v_val_4097_, 0);
v_name_4103_ = lean_ctor_get(v_toConstantVal_4102_, 0);
lean_inc_ref(v_val_4097_);
v___x_4104_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4104_, 0, v_val_4097_);
v___x_4105_ = 3;
lean_inc(v_name_4103_);
v_fst_4003_ = v_name_4103_;
v_fst_4004_ = v___x_4104_;
v_snd_4005_ = v___x_4105_;
v_exportedInfo_x3f_4006_ = v_exportedInfo_x3f_4099_;
v___y_4007_ = v___y_4100_;
v___y_4008_ = v___y_4101_;
goto v___jp_4002_;
}
}
case 0:
{
lean_object* v_val_4118_; lean_object* v_toConstantVal_4119_; lean_object* v_name_4120_; lean_object* v___x_4121_; uint8_t v___x_4122_; 
v_val_4118_ = lean_ctor_get(v_decl_3732_, 0);
v_toConstantVal_4119_ = lean_ctor_get(v_val_4118_, 0);
v_name_4120_ = lean_ctor_get(v_toConstantVal_4119_, 0);
lean_inc_ref(v_val_4118_);
v___x_4121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4121_, 0, v_val_4118_);
v___x_4122_ = 2;
lean_inc(v_name_4120_);
v_fst_4003_ = v_name_4120_;
v_fst_4004_ = v___x_4121_;
v_snd_4005_ = v___x_4122_;
v_exportedInfo_x3f_4006_ = v___x_3946_;
v___y_4007_ = v_a_3734_;
v___y_4008_ = v_a_3735_;
goto v___jp_4002_;
}
default: 
{
lean_object* v___x_4123_; 
v___x_4123_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3732_, v_a_3734_, v_a_3735_);
return v___x_4123_;
}
}
v___jp_3947_:
{
lean_object* v___x_3954_; uint8_t v___x_3955_; 
lean_inc(v_decl_3732_);
v___x_3954_ = l_Lean_Declaration_getTopLevelNames(v_decl_3732_);
v___x_3955_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3954_);
lean_dec(v___x_3954_);
if (v___x_3955_ == 0)
{
if (lean_obj_tag(v___y_3949_) == 0)
{
lean_object* v_options_3956_; uint8_t v_hasTrace_3957_; 
v_options_3956_ = lean_ctor_get(v___y_3952_, 2);
v_hasTrace_3957_ = lean_ctor_get_uint8(v_options_3956_, sizeof(void*)*1);
if (v_hasTrace_3957_ == 0)
{
v___y_3914_ = v___y_3948_;
v___y_3915_ = v___y_3950_;
v___y_3916_ = v___y_3951_;
v___y_3917_ = v___y_3952_;
v___y_3918_ = v___y_3953_;
goto v___jp_3913_;
}
else
{
lean_object* v_inheritedTraceOptions_3958_; lean_object* v___x_3959_; uint8_t v___x_3960_; 
v_inheritedTraceOptions_3958_ = lean_ctor_get(v___y_3952_, 13);
v___x_3959_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_3960_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3958_, v_options_3956_, v___x_3959_);
if (v___x_3960_ == 0)
{
v___y_3914_ = v___y_3948_;
v___y_3915_ = v___y_3950_;
v___y_3916_ = v___y_3951_;
v___y_3917_ = v___y_3952_;
v___y_3918_ = v___y_3953_;
goto v___jp_3913_;
}
else
{
lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3961_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_3962_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_3961_, v___y_3952_, v___y_3953_);
if (lean_obj_tag(v___x_3962_) == 0)
{
lean_dec_ref_known(v___x_3962_, 1);
v___y_3914_ = v___y_3948_;
v___y_3915_ = v___y_3950_;
v___y_3916_ = v___y_3951_;
v___y_3917_ = v___y_3952_;
v___y_3918_ = v___y_3953_;
goto v___jp_3913_;
}
else
{
lean_dec_ref(v___y_3951_);
lean_dec(v___y_3948_);
lean_dec(v_decl_3732_);
return v___x_3962_;
}
}
}
}
else
{
lean_object* v___x_3963_; lean_object* v_env_3964_; lean_object* v_nextMacroScope_3965_; lean_object* v_ngen_3966_; lean_object* v_auxDeclNGen_3967_; lean_object* v_traceState_3968_; lean_object* v_messages_3969_; lean_object* v_infoState_3970_; lean_object* v_snapshotTasks_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3982_; 
v___x_3963_ = lean_st_ref_take(v___y_3953_);
v_env_3964_ = lean_ctor_get(v___x_3963_, 0);
v_nextMacroScope_3965_ = lean_ctor_get(v___x_3963_, 1);
v_ngen_3966_ = lean_ctor_get(v___x_3963_, 2);
v_auxDeclNGen_3967_ = lean_ctor_get(v___x_3963_, 3);
v_traceState_3968_ = lean_ctor_get(v___x_3963_, 4);
v_messages_3969_ = lean_ctor_get(v___x_3963_, 6);
v_infoState_3970_ = lean_ctor_get(v___x_3963_, 7);
v_snapshotTasks_3971_ = lean_ctor_get(v___x_3963_, 8);
v_isSharedCheck_3982_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3982_ == 0)
{
lean_object* v_unused_3983_; 
v_unused_3983_ = lean_ctor_get(v___x_3963_, 5);
lean_dec(v_unused_3983_);
v___x_3973_ = v___x_3963_;
v_isShared_3974_ = v_isSharedCheck_3982_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_snapshotTasks_3971_);
lean_inc(v_infoState_3970_);
lean_inc(v_messages_3969_);
lean_inc(v_traceState_3968_);
lean_inc(v_auxDeclNGen_3967_);
lean_inc(v_ngen_3966_);
lean_inc(v_nextMacroScope_3965_);
lean_inc(v_env_3964_);
lean_dec(v___x_3963_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3982_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3979_; 
v___x_3975_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_3976_ = lean_box(v___y_3950_);
lean_inc(v___y_3948_);
v___x_3977_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3975_, v_env_3964_, v___y_3948_, v___x_3976_);
if (v_isShared_3974_ == 0)
{
lean_ctor_set(v___x_3973_, 5, v___x_3942_);
lean_ctor_set(v___x_3973_, 0, v___x_3977_);
v___x_3979_ = v___x_3973_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3977_);
lean_ctor_set(v_reuseFailAlloc_3981_, 1, v_nextMacroScope_3965_);
lean_ctor_set(v_reuseFailAlloc_3981_, 2, v_ngen_3966_);
lean_ctor_set(v_reuseFailAlloc_3981_, 3, v_auxDeclNGen_3967_);
lean_ctor_set(v_reuseFailAlloc_3981_, 4, v_traceState_3968_);
lean_ctor_set(v_reuseFailAlloc_3981_, 5, v___x_3942_);
lean_ctor_set(v_reuseFailAlloc_3981_, 6, v_messages_3969_);
lean_ctor_set(v_reuseFailAlloc_3981_, 7, v_infoState_3970_);
lean_ctor_set(v_reuseFailAlloc_3981_, 8, v_snapshotTasks_3971_);
v___x_3979_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
lean_object* v___x_3980_; 
v___x_3980_ = lean_st_ref_set(v___y_3953_, v___x_3979_);
v___y_3899_ = v___y_3948_;
v___y_3900_ = v___y_3950_;
v___y_3901_ = v___y_3951_;
v_exportedInfo_x3f_3902_ = v___y_3949_;
v___y_3903_ = v___y_3952_;
v___y_3904_ = v___y_3953_;
goto v___jp_3898_;
}
}
}
}
else
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v_a_3986_; uint8_t v___x_3987_; 
lean_dec(v___y_3949_);
v___x_3984_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3985_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3984_, v___y_3952_);
v_a_3986_ = lean_ctor_get(v___x_3985_, 0);
lean_inc(v_a_3986_);
lean_dec_ref(v___x_3985_);
v___x_3987_ = lean_unbox(v_a_3986_);
lean_dec(v_a_3986_);
if (v___x_3987_ == 0)
{
lean_object* v_options_3988_; uint8_t v_hasTrace_3989_; 
v_options_3988_ = lean_ctor_get(v___y_3952_, 2);
v_hasTrace_3989_ = lean_ctor_get_uint8(v_options_3988_, sizeof(void*)*1);
if (v_hasTrace_3989_ == 0)
{
v___y_3899_ = v___y_3948_;
v___y_3900_ = v___y_3950_;
v___y_3901_ = v___y_3951_;
v_exportedInfo_x3f_3902_ = v___x_3946_;
v___y_3903_ = v___y_3952_;
v___y_3904_ = v___y_3953_;
goto v___jp_3898_;
}
else
{
lean_object* v_inheritedTraceOptions_3990_; lean_object* v___x_3991_; uint8_t v___x_3992_; 
v_inheritedTraceOptions_3990_ = lean_ctor_get(v___y_3952_, 13);
v___x_3991_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_3992_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3990_, v_options_3988_, v___x_3991_);
if (v___x_3992_ == 0)
{
v___y_3899_ = v___y_3948_;
v___y_3900_ = v___y_3950_;
v___y_3901_ = v___y_3951_;
v_exportedInfo_x3f_3902_ = v___x_3946_;
v___y_3903_ = v___y_3952_;
v___y_3904_ = v___y_3953_;
goto v___jp_3898_;
}
else
{
lean_object* v___x_3993_; lean_object* v___x_3994_; 
v___x_3993_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_3994_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_3993_, v___y_3952_, v___y_3953_);
if (lean_obj_tag(v___x_3994_) == 0)
{
lean_dec_ref_known(v___x_3994_, 1);
v___y_3899_ = v___y_3948_;
v___y_3900_ = v___y_3950_;
v___y_3901_ = v___y_3951_;
v_exportedInfo_x3f_3902_ = v___x_3946_;
v___y_3903_ = v___y_3952_;
v___y_3904_ = v___y_3953_;
goto v___jp_3898_;
}
else
{
lean_dec_ref(v___y_3951_);
lean_dec(v___y_3948_);
lean_dec(v_decl_3732_);
return v___x_3994_;
}
}
}
}
else
{
lean_object* v_options_3995_; uint8_t v_hasTrace_3996_; 
v_options_3995_ = lean_ctor_get(v___y_3952_, 2);
v_hasTrace_3996_ = lean_ctor_get_uint8(v_options_3995_, sizeof(void*)*1);
if (v_hasTrace_3996_ == 0)
{
v___y_3921_ = v___y_3948_;
v___y_3922_ = v___y_3950_;
v___y_3923_ = v___y_3951_;
v___y_3924_ = v___y_3952_;
v___y_3925_ = v___y_3953_;
goto v___jp_3920_;
}
else
{
lean_object* v_inheritedTraceOptions_3997_; lean_object* v___x_3998_; uint8_t v___x_3999_; 
v_inheritedTraceOptions_3997_ = lean_ctor_get(v___y_3952_, 13);
v___x_3998_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_3999_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3997_, v_options_3995_, v___x_3998_);
if (v___x_3999_ == 0)
{
v___y_3921_ = v___y_3948_;
v___y_3922_ = v___y_3950_;
v___y_3923_ = v___y_3951_;
v___y_3924_ = v___y_3952_;
v___y_3925_ = v___y_3953_;
goto v___jp_3920_;
}
else
{
lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_4000_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_4001_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_4000_, v___y_3952_, v___y_3953_);
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_dec_ref_known(v___x_4001_, 1);
v___y_3921_ = v___y_3948_;
v___y_3922_ = v___y_3950_;
v___y_3923_ = v___y_3951_;
v___y_3924_ = v___y_3952_;
v___y_3925_ = v___y_3953_;
goto v___jp_3920_;
}
else
{
lean_dec_ref(v___y_3951_);
lean_dec(v___y_3948_);
lean_dec(v_decl_3732_);
return v___x_4001_;
}
}
}
}
}
}
v___jp_4002_:
{
lean_object* v___x_4009_; lean_object* v_env_4010_; uint8_t v___x_4011_; 
v___x_4009_ = lean_st_ref_get(v___y_4008_);
v_env_4010_ = lean_ctor_get(v___x_4009_, 0);
lean_inc_ref(v_env_4010_);
lean_dec(v___x_4009_);
v___x_4011_ = l_Lean_Environment_containsOnBranch(v_env_4010_, v_fst_4003_);
lean_dec_ref(v_env_4010_);
if (v___x_4011_ == 0)
{
v___y_3948_ = v_fst_4003_;
v___y_3949_ = v_exportedInfo_x3f_4006_;
v___y_3950_ = v_snd_4005_;
v___y_3951_ = v_fst_4004_;
v___y_3952_ = v___y_4007_;
v___y_3953_ = v___y_4008_;
goto v___jp_3947_;
}
else
{
lean_object* v___x_4012_; lean_object* v_env_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; 
lean_dec(v_exportedInfo_x3f_4006_);
lean_dec_ref(v_fst_4004_);
lean_dec(v_decl_3732_);
v___x_4012_ = lean_st_ref_get(v___y_4008_);
v_env_4013_ = lean_ctor_get(v___x_4012_, 0);
lean_inc_ref(v_env_4013_);
lean_dec(v___x_4012_);
v___x_4014_ = lean_elab_environment_to_kernel_env(v_env_4013_);
v___x_4015_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4015_, 0, v___x_4014_);
lean_ctor_set(v___x_4015_, 1, v_fst_4003_);
v___x_4016_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4015_, v___y_4007_, v___y_4008_);
return v___x_4016_;
}
}
v___jp_4017_:
{
lean_object* v_name_4023_; lean_object* v___x_4024_; uint8_t v___x_4025_; 
v_name_4023_ = lean_ctor_get(v_toConstantVal_4019_, 0);
lean_inc(v_name_4023_);
lean_dec_ref(v_toConstantVal_4019_);
v___x_4024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4024_, 0, v___y_4018_);
v___x_4025_ = 0;
v_fst_4003_ = v_name_4023_;
v_fst_4004_ = v___x_4024_;
v_snd_4005_ = v___x_4025_;
v_exportedInfo_x3f_4006_ = v_exportedInfo_x3f_4020_;
v___y_4007_ = v___y_4021_;
v___y_4008_ = v___y_4022_;
goto v___jp_4002_;
}
v___jp_4026_:
{
lean_object* v_toConstantVal_4031_; 
v_toConstantVal_4031_ = lean_ctor_get(v___y_4027_, 0);
lean_inc_ref(v_toConstantVal_4031_);
v___y_4018_ = v___y_4027_;
v_toConstantVal_4019_ = v_toConstantVal_4031_;
v_exportedInfo_x3f_4020_ = v_exportedInfo_x3f_4028_;
v___y_4021_ = v___y_4029_;
v___y_4022_ = v___y_4030_;
goto v___jp_4017_;
}
v___jp_4032_:
{
uint8_t v___x_4038_; uint8_t v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4038_ = 0;
v___x_4039_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4035_, v___x_4038_);
lean_inc_ref(v_toConstantVal_4034_);
v___x_4040_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4040_, 0, v_toConstantVal_4034_);
lean_ctor_set_uint8(v___x_4040_, sizeof(void*)*1, v___x_4039_);
v___x_4041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4041_, 0, v___x_4040_);
v___x_4042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4042_, 0, v___x_4041_);
v___y_4018_ = v___y_4033_;
v_toConstantVal_4019_ = v_toConstantVal_4034_;
v_exportedInfo_x3f_4020_ = v___x_4042_;
v___y_4021_ = v___y_4036_;
v___y_4022_ = v___y_4037_;
goto v___jp_4017_;
}
v___jp_4043_:
{
lean_object* v_toConstantVal_4047_; uint8_t v_safety_4048_; 
v_toConstantVal_4047_ = lean_ctor_get(v___y_4044_, 0);
lean_inc_ref(v_toConstantVal_4047_);
v_safety_4048_ = lean_ctor_get_uint8(v___y_4044_, sizeof(void*)*4);
v___y_4033_ = v___y_4044_;
v_toConstantVal_4034_ = v_toConstantVal_4047_;
v_safety_4035_ = v_safety_4048_;
v___y_4036_ = v___y_4045_;
v___y_4037_ = v___y_4046_;
goto v___jp_4032_;
}
v___jp_4049_:
{
lean_object* v___x_4053_; lean_object* v___x_4054_; 
v___x_4053_ = lean_st_ref_get(v___y_4052_);
v___x_4054_ = lean_st_ref_get(v___y_4052_);
if (v_forceExpose_3733_ == 0)
{
lean_object* v_env_4055_; lean_object* v_env_4056_; lean_object* v___x_4057_; uint8_t v_isModule_4058_; 
v_env_4055_ = lean_ctor_get(v___x_4053_, 0);
lean_inc_ref(v_env_4055_);
lean_dec(v___x_4053_);
v_env_4056_ = lean_ctor_get(v___x_4054_, 0);
lean_inc_ref(v_env_4056_);
lean_dec(v___x_4054_);
v___x_4057_ = l_Lean_Environment_header(v_env_4055_);
lean_dec_ref(v_env_4055_);
v_isModule_4058_ = lean_ctor_get_uint8(v___x_4057_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4057_);
if (v_isModule_4058_ == 0)
{
lean_dec_ref(v_env_4056_);
v___y_4027_ = v_defn_4050_;
v_exportedInfo_x3f_4028_ = v___x_3946_;
v___y_4029_ = v___y_4051_;
v___y_4030_ = v___y_4052_;
goto v___jp_4026_;
}
else
{
uint8_t v_isExporting_4059_; 
v_isExporting_4059_ = lean_ctor_get_uint8(v_env_4056_, sizeof(void*)*8);
lean_dec_ref(v_env_4056_);
if (v_isExporting_4059_ == 0)
{
lean_object* v_options_4060_; uint8_t v_hasTrace_4061_; 
v_options_4060_ = lean_ctor_get(v___y_4051_, 2);
v_hasTrace_4061_ = lean_ctor_get_uint8(v_options_4060_, sizeof(void*)*1);
if (v_hasTrace_4061_ == 0)
{
v___y_4044_ = v_defn_4050_;
v___y_4045_ = v___y_4051_;
v___y_4046_ = v___y_4052_;
goto v___jp_4043_;
}
else
{
lean_object* v_inheritedTraceOptions_4062_; lean_object* v___x_4063_; uint8_t v___x_4064_; 
v_inheritedTraceOptions_4062_ = lean_ctor_get(v___y_4051_, 13);
v___x_4063_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4064_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4062_, v_options_4060_, v___x_4063_);
if (v___x_4064_ == 0)
{
v___y_4044_ = v_defn_4050_;
v___y_4045_ = v___y_4051_;
v___y_4046_ = v___y_4052_;
goto v___jp_4043_;
}
else
{
lean_object* v_toConstantVal_4065_; uint8_t v_safety_4066_; lean_object* v_name_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; 
v_toConstantVal_4065_ = lean_ctor_get(v_defn_4050_, 0);
lean_inc_ref(v_toConstantVal_4065_);
v_safety_4066_ = lean_ctor_get_uint8(v_defn_4050_, sizeof(void*)*4);
v_name_4067_ = lean_ctor_get(v_toConstantVal_4065_, 0);
v___x_4068_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_4067_);
v___x_4069_ = l_Lean_MessageData_ofName(v_name_4067_);
v___x_4070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4068_);
lean_ctor_set(v___x_4070_, 1, v___x_4069_);
v___x_4071_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4070_);
lean_ctor_set(v___x_4072_, 1, v___x_4071_);
v___x_4073_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_4072_, v___y_4051_, v___y_4052_);
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_dec_ref_known(v___x_4073_, 1);
v___y_4033_ = v_defn_4050_;
v_toConstantVal_4034_ = v_toConstantVal_4065_;
v_safety_4035_ = v_safety_4066_;
v___y_4036_ = v___y_4051_;
v___y_4037_ = v___y_4052_;
goto v___jp_4032_;
}
else
{
lean_dec_ref(v_toConstantVal_4065_);
lean_dec_ref(v_defn_4050_);
lean_dec(v_decl_3732_);
return v___x_4073_;
}
}
}
}
else
{
v___y_4027_ = v_defn_4050_;
v_exportedInfo_x3f_4028_ = v___x_3946_;
v___y_4029_ = v___y_4051_;
v___y_4030_ = v___y_4052_;
goto v___jp_4026_;
}
}
}
else
{
lean_dec(v___x_4054_);
lean_dec(v___x_4053_);
v___y_4027_ = v_defn_4050_;
v_exportedInfo_x3f_4028_ = v___x_3946_;
v___y_4029_ = v___y_4051_;
v___y_4030_ = v___y_4052_;
goto v___jp_4026_;
}
}
}
}
}
else
{
lean_object* v___f_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; uint8_t v___x_4130_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v_a_4134_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v_a_4180_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4237_; lean_object* v___y_4238_; uint8_t v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; 
lean_inc(v_decl_3732_);
v___f_4127_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___boxed), 5, 1);
lean_closure_set(v___f_4127_, 0, v_decl_3732_);
v___x_4128_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_4129_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4130_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3790_, v_options_3789_, v___x_4129_);
if (v___x_4130_ == 0)
{
lean_object* v___x_4430_; uint8_t v___x_4431_; lean_object* v___y_4433_; lean_object* v___y_4434_; lean_object* v___y_4435_; lean_object* v___y_4436_; lean_object* v___y_4437_; lean_object* v___y_4438_; lean_object* v___y_4439_; lean_object* v___y_4440_; lean_object* v___y_4441_; lean_object* v___y_4442_; lean_object* v___y_4506_; lean_object* v___y_4507_; lean_object* v___y_4508_; uint8_t v___y_4509_; lean_object* v___y_4510_; lean_object* v___y_4511_; lean_object* v___y_4512_; lean_object* v___y_4513_; lean_object* v___y_4514_; lean_object* v___y_4515_; uint8_t v___y_4537_; lean_object* v___y_4538_; lean_object* v___y_4539_; lean_object* v_exportedInfo_x3f_4540_; lean_object* v___y_4541_; lean_object* v___y_4542_; uint8_t v___y_4552_; lean_object* v___y_4553_; lean_object* v___y_4554_; lean_object* v___y_4555_; lean_object* v___y_4556_; uint8_t v___y_4559_; lean_object* v___y_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4563_; 
v___x_4430_ = l_Lean_trace_profiler;
v___x_4431_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3789_, v___x_4430_);
if (v___x_4431_ == 0)
{
lean_object* v___x_4565_; lean_object* v_env_4566_; lean_object* v_nextMacroScope_4567_; lean_object* v_ngen_4568_; lean_object* v_auxDeclNGen_4569_; lean_object* v_traceState_4570_; lean_object* v_messages_4571_; lean_object* v_infoState_4572_; lean_object* v_snapshotTasks_4573_; lean_object* v___x_4575_; uint8_t v_isShared_4576_; uint8_t v_isSharedCheck_4809_; 
lean_dec_ref(v___f_4127_);
v___x_4565_ = lean_st_ref_take(v_a_3735_);
v_env_4566_ = lean_ctor_get(v___x_4565_, 0);
v_nextMacroScope_4567_ = lean_ctor_get(v___x_4565_, 1);
v_ngen_4568_ = lean_ctor_get(v___x_4565_, 2);
v_auxDeclNGen_4569_ = lean_ctor_get(v___x_4565_, 3);
v_traceState_4570_ = lean_ctor_get(v___x_4565_, 4);
v_messages_4571_ = lean_ctor_get(v___x_4565_, 6);
v_infoState_4572_ = lean_ctor_get(v___x_4565_, 7);
v_snapshotTasks_4573_ = lean_ctor_get(v___x_4565_, 8);
v_isSharedCheck_4809_ = !lean_is_exclusive(v___x_4565_);
if (v_isSharedCheck_4809_ == 0)
{
lean_object* v_unused_4810_; 
v_unused_4810_ = lean_ctor_get(v___x_4565_, 5);
lean_dec(v_unused_4810_);
v___x_4575_ = v___x_4565_;
v_isShared_4576_ = v_isSharedCheck_4809_;
goto v_resetjp_4574_;
}
else
{
lean_inc(v_snapshotTasks_4573_);
lean_inc(v_infoState_4572_);
lean_inc(v_messages_4571_);
lean_inc(v_traceState_4570_);
lean_inc(v_auxDeclNGen_4569_);
lean_inc(v_ngen_4568_);
lean_inc(v_nextMacroScope_4567_);
lean_inc(v_env_4566_);
lean_dec(v___x_4565_);
v___x_4575_ = lean_box(0);
v_isShared_4576_ = v_isSharedCheck_4809_;
goto v_resetjp_4574_;
}
v_resetjp_4574_:
{
lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; uint8_t v___y_4581_; lean_object* v___y_4582_; lean_object* v___y_4583_; lean_object* v___y_4584_; lean_object* v___y_4585_; lean_object* v___y_4586_; lean_object* v___x_4609_; 
lean_inc(v_decl_3732_);
v___x_4577_ = l_Lean_Declaration_getNames(v_decl_3732_);
v___x_4578_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4566_, v___x_4577_);
v___x_4579_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4576_ == 0)
{
lean_ctor_set(v___x_4575_, 5, v___x_4579_);
lean_ctor_set(v___x_4575_, 0, v___x_4578_);
v___x_4609_ = v___x_4575_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4808_; 
v_reuseFailAlloc_4808_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4808_, 0, v___x_4578_);
lean_ctor_set(v_reuseFailAlloc_4808_, 1, v_nextMacroScope_4567_);
lean_ctor_set(v_reuseFailAlloc_4808_, 2, v_ngen_4568_);
lean_ctor_set(v_reuseFailAlloc_4808_, 3, v_auxDeclNGen_4569_);
lean_ctor_set(v_reuseFailAlloc_4808_, 4, v_traceState_4570_);
lean_ctor_set(v_reuseFailAlloc_4808_, 5, v___x_4579_);
lean_ctor_set(v_reuseFailAlloc_4808_, 6, v_messages_4571_);
lean_ctor_set(v_reuseFailAlloc_4808_, 7, v_infoState_4572_);
lean_ctor_set(v_reuseFailAlloc_4808_, 8, v_snapshotTasks_4573_);
v___x_4609_ = v_reuseFailAlloc_4808_;
goto v_reusejp_4608_;
}
v___jp_4580_:
{
lean_object* v___x_4587_; lean_object* v_env_4588_; lean_object* v_nextMacroScope_4589_; lean_object* v_ngen_4590_; lean_object* v_auxDeclNGen_4591_; lean_object* v_traceState_4592_; lean_object* v_messages_4593_; lean_object* v_infoState_4594_; lean_object* v_snapshotTasks_4595_; lean_object* v___x_4597_; uint8_t v_isShared_4598_; uint8_t v_isSharedCheck_4606_; 
v___x_4587_ = lean_st_ref_take(v___y_4585_);
v_env_4588_ = lean_ctor_get(v___x_4587_, 0);
v_nextMacroScope_4589_ = lean_ctor_get(v___x_4587_, 1);
v_ngen_4590_ = lean_ctor_get(v___x_4587_, 2);
v_auxDeclNGen_4591_ = lean_ctor_get(v___x_4587_, 3);
v_traceState_4592_ = lean_ctor_get(v___x_4587_, 4);
v_messages_4593_ = lean_ctor_get(v___x_4587_, 6);
v_infoState_4594_ = lean_ctor_get(v___x_4587_, 7);
v_snapshotTasks_4595_ = lean_ctor_get(v___x_4587_, 8);
v_isSharedCheck_4606_ = !lean_is_exclusive(v___x_4587_);
if (v_isSharedCheck_4606_ == 0)
{
lean_object* v_unused_4607_; 
v_unused_4607_ = lean_ctor_get(v___x_4587_, 5);
lean_dec(v_unused_4607_);
v___x_4597_ = v___x_4587_;
v_isShared_4598_ = v_isSharedCheck_4606_;
goto v_resetjp_4596_;
}
else
{
lean_inc(v_snapshotTasks_4595_);
lean_inc(v_infoState_4594_);
lean_inc(v_messages_4593_);
lean_inc(v_traceState_4592_);
lean_inc(v_auxDeclNGen_4591_);
lean_inc(v_ngen_4590_);
lean_inc(v_nextMacroScope_4589_);
lean_inc(v_env_4588_);
lean_dec(v___x_4587_);
v___x_4597_ = lean_box(0);
v_isShared_4598_ = v_isSharedCheck_4606_;
goto v_resetjp_4596_;
}
v_resetjp_4596_:
{
lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4603_; 
v___x_4599_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4600_ = lean_box(v___y_4581_);
lean_inc(v___y_4586_);
v___x_4601_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4599_, v_env_4588_, v___y_4586_, v___x_4600_);
if (v_isShared_4598_ == 0)
{
lean_ctor_set(v___x_4597_, 5, v___x_4579_);
lean_ctor_set(v___x_4597_, 0, v___x_4601_);
v___x_4603_ = v___x_4597_;
goto v_reusejp_4602_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v___x_4601_);
lean_ctor_set(v_reuseFailAlloc_4605_, 1, v_nextMacroScope_4589_);
lean_ctor_set(v_reuseFailAlloc_4605_, 2, v_ngen_4590_);
lean_ctor_set(v_reuseFailAlloc_4605_, 3, v_auxDeclNGen_4591_);
lean_ctor_set(v_reuseFailAlloc_4605_, 4, v_traceState_4592_);
lean_ctor_set(v_reuseFailAlloc_4605_, 5, v___x_4579_);
lean_ctor_set(v_reuseFailAlloc_4605_, 6, v_messages_4593_);
lean_ctor_set(v_reuseFailAlloc_4605_, 7, v_infoState_4594_);
lean_ctor_set(v_reuseFailAlloc_4605_, 8, v_snapshotTasks_4595_);
v___x_4603_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4602_;
}
v_reusejp_4602_:
{
lean_object* v___x_4604_; 
v___x_4604_ = lean_st_ref_set(v___y_4585_, v___x_4603_);
v___y_4537_ = v___y_4581_;
v___y_4538_ = v___y_4583_;
v___y_4539_ = v___y_4586_;
v_exportedInfo_x3f_4540_ = v___y_4582_;
v___y_4541_ = v___y_4584_;
v___y_4542_ = v___y_4585_;
goto v___jp_4536_;
}
}
}
v_reusejp_4608_:
{
lean_object* v___x_4610_; lean_object* v___y_4612_; lean_object* v_options_4613_; lean_object* v_inheritedTraceOptions_4614_; lean_object* v___y_4615_; lean_object* v___x_4621_; uint8_t v___y_4623_; lean_object* v___y_4624_; lean_object* v___y_4625_; lean_object* v___y_4626_; lean_object* v___y_4627_; lean_object* v___y_4628_; lean_object* v_fst_4654_; lean_object* v_fst_4655_; uint8_t v_snd_4656_; lean_object* v_exportedInfo_x3f_4657_; lean_object* v___y_4658_; lean_object* v___y_4659_; lean_object* v___y_4669_; lean_object* v_toConstantVal_4670_; lean_object* v_exportedInfo_x3f_4671_; lean_object* v___y_4672_; lean_object* v___y_4673_; lean_object* v___y_4678_; lean_object* v_toConstantVal_4679_; uint8_t v_safety_4680_; lean_object* v___y_4681_; lean_object* v___y_4682_; lean_object* v___y_4689_; lean_object* v___y_4690_; lean_object* v___y_4691_; lean_object* v___y_4695_; lean_object* v___y_4696_; lean_object* v___y_4697_; lean_object* v___y_4712_; lean_object* v_exportedInfo_x3f_4713_; lean_object* v___y_4714_; lean_object* v___y_4715_; lean_object* v___y_4718_; lean_object* v___y_4719_; lean_object* v___y_4720_; lean_object* v___y_4721_; lean_object* v___y_4722_; lean_object* v_defn_4727_; lean_object* v___y_4728_; lean_object* v___y_4729_; 
v___x_4610_ = lean_st_ref_set(v_a_3735_, v___x_4609_);
v___x_4621_ = lean_box(0);
switch(lean_obj_tag(v_decl_3732_))
{
case 2:
{
lean_object* v_val_4736_; lean_object* v_exportedInfo_x3f_4738_; lean_object* v___y_4739_; lean_object* v___y_4740_; lean_object* v___y_4746_; lean_object* v___y_4747_; lean_object* v___x_4752_; lean_object* v_env_4753_; 
v_val_4736_ = lean_ctor_get(v_decl_3732_, 0);
v___x_4752_ = lean_st_ref_get(v_a_3735_);
v_env_4753_ = lean_ctor_get(v___x_4752_, 0);
lean_inc_ref(v_env_4753_);
lean_dec(v___x_4752_);
if (v_forceExpose_3733_ == 0)
{
goto v___jp_4754_;
}
else
{
if (v___x_4431_ == 0)
{
lean_dec_ref(v_env_4753_);
v_exportedInfo_x3f_4738_ = v___x_4621_;
v___y_4739_ = v_a_3734_;
v___y_4740_ = v_a_3735_;
goto v___jp_4737_;
}
else
{
goto v___jp_4754_;
}
}
v___jp_4737_:
{
lean_object* v_toConstantVal_4741_; lean_object* v_name_4742_; lean_object* v___x_4743_; uint8_t v___x_4744_; 
v_toConstantVal_4741_ = lean_ctor_get(v_val_4736_, 0);
v_name_4742_ = lean_ctor_get(v_toConstantVal_4741_, 0);
lean_inc_ref(v_val_4736_);
v___x_4743_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4743_, 0, v_val_4736_);
v___x_4744_ = 1;
lean_inc(v_name_4742_);
v_fst_4654_ = v_name_4742_;
v_fst_4655_ = v___x_4743_;
v_snd_4656_ = v___x_4744_;
v_exportedInfo_x3f_4657_ = v_exportedInfo_x3f_4738_;
v___y_4658_ = v___y_4739_;
v___y_4659_ = v___y_4740_;
goto v___jp_4653_;
}
v___jp_4745_:
{
lean_object* v_toConstantVal_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; 
v_toConstantVal_4748_ = lean_ctor_get(v_val_4736_, 0);
lean_inc_ref(v_toConstantVal_4748_);
v___x_4749_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4749_, 0, v_toConstantVal_4748_);
lean_ctor_set_uint8(v___x_4749_, sizeof(void*)*1, v___x_4431_);
v___x_4750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4750_, 0, v___x_4749_);
v___x_4751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4751_, 0, v___x_4750_);
v_exportedInfo_x3f_4738_ = v___x_4751_;
v___y_4739_ = v___y_4746_;
v___y_4740_ = v___y_4747_;
goto v___jp_4737_;
}
v___jp_4754_:
{
lean_object* v___x_4755_; uint8_t v_isModule_4756_; 
v___x_4755_ = l_Lean_Environment_header(v_env_4753_);
lean_dec_ref(v_env_4753_);
v_isModule_4756_ = lean_ctor_get_uint8(v___x_4755_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4755_);
if (v_isModule_4756_ == 0)
{
v_exportedInfo_x3f_4738_ = v___x_4621_;
v___y_4739_ = v_a_3734_;
v___y_4740_ = v_a_3735_;
goto v___jp_4737_;
}
else
{
if (v___x_4130_ == 0)
{
v___y_4746_ = v_a_3734_;
v___y_4747_ = v_a_3735_;
goto v___jp_4745_;
}
else
{
lean_object* v_toConstantVal_4757_; lean_object* v_name_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; 
v_toConstantVal_4757_ = lean_ctor_get(v_val_4736_, 0);
v_name_4758_ = lean_ctor_get(v_toConstantVal_4757_, 0);
v___x_4759_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4758_);
v___x_4760_ = l_Lean_MessageData_ofName(v_name_4758_);
v___x_4761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4761_, 0, v___x_4759_);
lean_ctor_set(v___x_4761_, 1, v___x_4760_);
v___x_4762_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4763_, 0, v___x_4761_);
lean_ctor_set(v___x_4763_, 1, v___x_4762_);
v___x_4764_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_4763_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_4764_) == 0)
{
lean_dec_ref_known(v___x_4764_, 1);
v___y_4746_ = v_a_3734_;
v___y_4747_ = v_a_3735_;
goto v___jp_4745_;
}
else
{
lean_dec_ref_known(v_decl_3732_, 1);
return v___x_4764_;
}
}
}
}
}
case 1:
{
lean_object* v_val_4765_; 
v_val_4765_ = lean_ctor_get(v_decl_3732_, 0);
lean_inc_ref(v_val_4765_);
v_defn_4727_ = v_val_4765_;
v___y_4728_ = v_a_3734_;
v___y_4729_ = v_a_3735_;
goto v___jp_4726_;
}
case 5:
{
lean_object* v_defns_4766_; 
v_defns_4766_ = lean_ctor_get(v_decl_3732_, 0);
if (lean_obj_tag(v_defns_4766_) == 1)
{
lean_object* v_tail_4767_; 
v_tail_4767_ = lean_ctor_get(v_defns_4766_, 1);
if (lean_obj_tag(v_tail_4767_) == 0)
{
lean_object* v_head_4768_; 
v_head_4768_ = lean_ctor_get(v_defns_4766_, 0);
lean_inc(v_head_4768_);
v_defn_4727_ = v_head_4768_;
v___y_4728_ = v_a_3734_;
v___y_4729_ = v_a_3735_;
goto v___jp_4726_;
}
else
{
v___y_4612_ = v_a_3734_;
v_options_4613_ = v_options_3789_;
v_inheritedTraceOptions_4614_ = v_inheritedTraceOptions_3790_;
v___y_4615_ = v_a_3735_;
goto v___jp_4611_;
}
}
else
{
v___y_4612_ = v_a_3734_;
v_options_4613_ = v_options_3789_;
v_inheritedTraceOptions_4614_ = v_inheritedTraceOptions_3790_;
v___y_4615_ = v_a_3735_;
goto v___jp_4611_;
}
}
case 3:
{
lean_object* v_val_4769_; lean_object* v_exportedInfo_x3f_4771_; lean_object* v___y_4772_; lean_object* v___y_4773_; lean_object* v___y_4779_; lean_object* v___y_4780_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v_env_4797_; lean_object* v_env_4798_; 
v_val_4769_ = lean_ctor_get(v_decl_3732_, 0);
v___x_4786_ = lean_st_ref_get(v_a_3735_);
v___x_4787_ = lean_st_ref_get(v_a_3735_);
v_env_4797_ = lean_ctor_get(v___x_4786_, 0);
lean_inc_ref(v_env_4797_);
lean_dec(v___x_4786_);
v_env_4798_ = lean_ctor_get(v___x_4787_, 0);
lean_inc_ref(v_env_4798_);
lean_dec(v___x_4787_);
if (v_forceExpose_3733_ == 0)
{
goto v___jp_4799_;
}
else
{
if (v___x_4431_ == 0)
{
lean_dec_ref(v_env_4798_);
lean_dec_ref(v_env_4797_);
v_exportedInfo_x3f_4771_ = v___x_4621_;
v___y_4772_ = v_a_3734_;
v___y_4773_ = v_a_3735_;
goto v___jp_4770_;
}
else
{
goto v___jp_4799_;
}
}
v___jp_4770_:
{
lean_object* v_toConstantVal_4774_; lean_object* v_name_4775_; lean_object* v___x_4776_; uint8_t v___x_4777_; 
v_toConstantVal_4774_ = lean_ctor_get(v_val_4769_, 0);
v_name_4775_ = lean_ctor_get(v_toConstantVal_4774_, 0);
lean_inc_ref(v_val_4769_);
v___x_4776_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4776_, 0, v_val_4769_);
v___x_4777_ = 3;
lean_inc(v_name_4775_);
v_fst_4654_ = v_name_4775_;
v_fst_4655_ = v___x_4776_;
v_snd_4656_ = v___x_4777_;
v_exportedInfo_x3f_4657_ = v_exportedInfo_x3f_4771_;
v___y_4658_ = v___y_4772_;
v___y_4659_ = v___y_4773_;
goto v___jp_4653_;
}
v___jp_4778_:
{
lean_object* v_toConstantVal_4781_; uint8_t v_isUnsafe_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; 
v_toConstantVal_4781_ = lean_ctor_get(v_val_4769_, 0);
v_isUnsafe_4782_ = lean_ctor_get_uint8(v_val_4769_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4781_);
v___x_4783_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4783_, 0, v_toConstantVal_4781_);
lean_ctor_set_uint8(v___x_4783_, sizeof(void*)*1, v_isUnsafe_4782_);
v___x_4784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4784_, 0, v___x_4783_);
v___x_4785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4785_, 0, v___x_4784_);
v_exportedInfo_x3f_4771_ = v___x_4785_;
v___y_4772_ = v___y_4779_;
v___y_4773_ = v___y_4780_;
goto v___jp_4770_;
}
v___jp_4788_:
{
if (v___x_4130_ == 0)
{
v___y_4779_ = v_a_3734_;
v___y_4780_ = v_a_3735_;
goto v___jp_4778_;
}
else
{
lean_object* v_toConstantVal_4789_; lean_object* v_name_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; 
v_toConstantVal_4789_ = lean_ctor_get(v_val_4769_, 0);
v_name_4790_ = lean_ctor_get(v_toConstantVal_4789_, 0);
v___x_4791_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4790_);
v___x_4792_ = l_Lean_MessageData_ofName(v_name_4790_);
v___x_4793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4793_, 0, v___x_4791_);
lean_ctor_set(v___x_4793_, 1, v___x_4792_);
v___x_4794_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4795_, 0, v___x_4793_);
lean_ctor_set(v___x_4795_, 1, v___x_4794_);
v___x_4796_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_4795_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_4796_) == 0)
{
lean_dec_ref_known(v___x_4796_, 1);
v___y_4779_ = v_a_3734_;
v___y_4780_ = v_a_3735_;
goto v___jp_4778_;
}
else
{
lean_dec_ref_known(v_decl_3732_, 1);
return v___x_4796_;
}
}
}
v___jp_4799_:
{
lean_object* v___x_4800_; uint8_t v_isModule_4801_; 
v___x_4800_ = l_Lean_Environment_header(v_env_4797_);
lean_dec_ref(v_env_4797_);
v_isModule_4801_ = lean_ctor_get_uint8(v___x_4800_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4800_);
if (v_isModule_4801_ == 0)
{
lean_dec_ref(v_env_4798_);
v_exportedInfo_x3f_4771_ = v___x_4621_;
v___y_4772_ = v_a_3734_;
v___y_4773_ = v_a_3735_;
goto v___jp_4770_;
}
else
{
uint8_t v_isExporting_4802_; 
v_isExporting_4802_ = lean_ctor_get_uint8(v_env_4798_, sizeof(void*)*8);
lean_dec_ref(v_env_4798_);
if (v_isExporting_4802_ == 0)
{
goto v___jp_4788_;
}
else
{
if (v___x_4431_ == 0)
{
v_exportedInfo_x3f_4771_ = v___x_4621_;
v___y_4772_ = v_a_3734_;
v___y_4773_ = v_a_3735_;
goto v___jp_4770_;
}
else
{
goto v___jp_4788_;
}
}
}
}
}
case 0:
{
lean_object* v_val_4803_; lean_object* v_toConstantVal_4804_; lean_object* v_name_4805_; lean_object* v___x_4806_; uint8_t v___x_4807_; 
v_val_4803_ = lean_ctor_get(v_decl_3732_, 0);
v_toConstantVal_4804_ = lean_ctor_get(v_val_4803_, 0);
v_name_4805_ = lean_ctor_get(v_toConstantVal_4804_, 0);
lean_inc_ref(v_val_4803_);
v___x_4806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4806_, 0, v_val_4803_);
v___x_4807_ = 2;
lean_inc(v_name_4805_);
v_fst_4654_ = v_name_4805_;
v_fst_4655_ = v___x_4806_;
v_snd_4656_ = v___x_4807_;
v_exportedInfo_x3f_4657_ = v___x_4621_;
v___y_4658_ = v_a_3734_;
v___y_4659_ = v_a_3735_;
goto v___jp_4653_;
}
default: 
{
v___y_4612_ = v_a_3734_;
v_options_4613_ = v_options_3789_;
v_inheritedTraceOptions_4614_ = v_inheritedTraceOptions_3790_;
v___y_4615_ = v_a_3735_;
goto v___jp_4611_;
}
}
v___jp_4611_:
{
uint8_t v___x_4616_; 
v___x_4616_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4614_, v_options_4613_, v___x_4129_);
if (v___x_4616_ == 0)
{
lean_object* v___x_4617_; 
v___x_4617_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3732_, v___y_4612_, v___y_4615_);
return v___x_4617_;
}
else
{
lean_object* v___x_4618_; lean_object* v___x_4619_; 
v___x_4618_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1);
v___x_4619_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_4618_, v___y_4612_, v___y_4615_);
if (lean_obj_tag(v___x_4619_) == 0)
{
lean_object* v___x_4620_; 
lean_dec_ref_known(v___x_4619_, 1);
v___x_4620_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3732_, v___y_4612_, v___y_4615_);
return v___x_4620_;
}
else
{
lean_dec(v_decl_3732_);
return v___x_4619_;
}
}
}
v___jp_4622_:
{
lean_object* v___x_4629_; uint8_t v___x_4630_; 
lean_inc(v_decl_3732_);
v___x_4629_ = l_Lean_Declaration_getTopLevelNames(v_decl_3732_);
v___x_4630_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_4629_);
lean_dec(v___x_4629_);
if (v___x_4630_ == 0)
{
if (lean_obj_tag(v___y_4624_) == 0)
{
if (v___x_4431_ == 0)
{
lean_object* v_options_4631_; uint8_t v_hasTrace_4632_; 
v_options_4631_ = lean_ctor_get(v___y_4627_, 2);
v_hasTrace_4632_ = lean_ctor_get_uint8(v_options_4631_, sizeof(void*)*1);
if (v_hasTrace_4632_ == 0)
{
v___y_4552_ = v___y_4623_;
v___y_4553_ = v___y_4625_;
v___y_4554_ = v___y_4626_;
v___y_4555_ = v___y_4627_;
v___y_4556_ = v___y_4628_;
goto v___jp_4551_;
}
else
{
lean_object* v_inheritedTraceOptions_4633_; uint8_t v___x_4634_; 
v_inheritedTraceOptions_4633_ = lean_ctor_get(v___y_4627_, 13);
v___x_4634_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4633_, v_options_4631_, v___x_4129_);
if (v___x_4634_ == 0)
{
v___y_4552_ = v___y_4623_;
v___y_4553_ = v___y_4625_;
v___y_4554_ = v___y_4626_;
v___y_4555_ = v___y_4627_;
v___y_4556_ = v___y_4628_;
goto v___jp_4551_;
}
else
{
lean_object* v___x_4635_; lean_object* v___x_4636_; 
v___x_4635_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_4636_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_4635_, v___y_4627_, v___y_4628_);
if (lean_obj_tag(v___x_4636_) == 0)
{
lean_dec_ref_known(v___x_4636_, 1);
v___y_4552_ = v___y_4623_;
v___y_4553_ = v___y_4625_;
v___y_4554_ = v___y_4626_;
v___y_4555_ = v___y_4627_;
v___y_4556_ = v___y_4628_;
goto v___jp_4551_;
}
else
{
lean_dec(v___y_4626_);
lean_dec_ref(v___y_4625_);
lean_dec(v_decl_3732_);
return v___x_4636_;
}
}
}
}
else
{
v___y_4581_ = v___y_4623_;
v___y_4582_ = v___y_4624_;
v___y_4583_ = v___y_4625_;
v___y_4584_ = v___y_4627_;
v___y_4585_ = v___y_4628_;
v___y_4586_ = v___y_4626_;
goto v___jp_4580_;
}
}
else
{
v___y_4581_ = v___y_4623_;
v___y_4582_ = v___y_4624_;
v___y_4583_ = v___y_4625_;
v___y_4584_ = v___y_4627_;
v___y_4585_ = v___y_4628_;
v___y_4586_ = v___y_4626_;
goto v___jp_4580_;
}
}
else
{
lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v_a_4639_; uint8_t v___x_4640_; 
lean_dec(v___y_4624_);
v___x_4637_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4638_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4637_, v___y_4627_);
v_a_4639_ = lean_ctor_get(v___x_4638_, 0);
lean_inc(v_a_4639_);
lean_dec_ref(v___x_4638_);
v___x_4640_ = lean_unbox(v_a_4639_);
lean_dec(v_a_4639_);
if (v___x_4640_ == 0)
{
lean_object* v_options_4641_; uint8_t v_hasTrace_4642_; 
v_options_4641_ = lean_ctor_get(v___y_4627_, 2);
v_hasTrace_4642_ = lean_ctor_get_uint8(v_options_4641_, sizeof(void*)*1);
if (v_hasTrace_4642_ == 0)
{
v___y_4537_ = v___y_4623_;
v___y_4538_ = v___y_4625_;
v___y_4539_ = v___y_4626_;
v_exportedInfo_x3f_4540_ = v___x_4621_;
v___y_4541_ = v___y_4627_;
v___y_4542_ = v___y_4628_;
goto v___jp_4536_;
}
else
{
lean_object* v_inheritedTraceOptions_4643_; uint8_t v___x_4644_; 
v_inheritedTraceOptions_4643_ = lean_ctor_get(v___y_4627_, 13);
v___x_4644_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4643_, v_options_4641_, v___x_4129_);
if (v___x_4644_ == 0)
{
v___y_4537_ = v___y_4623_;
v___y_4538_ = v___y_4625_;
v___y_4539_ = v___y_4626_;
v_exportedInfo_x3f_4540_ = v___x_4621_;
v___y_4541_ = v___y_4627_;
v___y_4542_ = v___y_4628_;
goto v___jp_4536_;
}
else
{
lean_object* v___x_4645_; lean_object* v___x_4646_; 
v___x_4645_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_4646_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_4645_, v___y_4627_, v___y_4628_);
if (lean_obj_tag(v___x_4646_) == 0)
{
lean_dec_ref_known(v___x_4646_, 1);
v___y_4537_ = v___y_4623_;
v___y_4538_ = v___y_4625_;
v___y_4539_ = v___y_4626_;
v_exportedInfo_x3f_4540_ = v___x_4621_;
v___y_4541_ = v___y_4627_;
v___y_4542_ = v___y_4628_;
goto v___jp_4536_;
}
else
{
lean_dec(v___y_4626_);
lean_dec_ref(v___y_4625_);
lean_dec(v_decl_3732_);
return v___x_4646_;
}
}
}
}
else
{
lean_object* v_options_4647_; uint8_t v_hasTrace_4648_; 
v_options_4647_ = lean_ctor_get(v___y_4627_, 2);
v_hasTrace_4648_ = lean_ctor_get_uint8(v_options_4647_, sizeof(void*)*1);
if (v_hasTrace_4648_ == 0)
{
v___y_4559_ = v___y_4623_;
v___y_4560_ = v___y_4625_;
v___y_4561_ = v___y_4626_;
v___y_4562_ = v___y_4627_;
v___y_4563_ = v___y_4628_;
goto v___jp_4558_;
}
else
{
lean_object* v_inheritedTraceOptions_4649_; uint8_t v___x_4650_; 
v_inheritedTraceOptions_4649_ = lean_ctor_get(v___y_4627_, 13);
v___x_4650_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4649_, v_options_4647_, v___x_4129_);
if (v___x_4650_ == 0)
{
v___y_4559_ = v___y_4623_;
v___y_4560_ = v___y_4625_;
v___y_4561_ = v___y_4626_;
v___y_4562_ = v___y_4627_;
v___y_4563_ = v___y_4628_;
goto v___jp_4558_;
}
else
{
lean_object* v___x_4651_; lean_object* v___x_4652_; 
v___x_4651_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_4652_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_4651_, v___y_4627_, v___y_4628_);
if (lean_obj_tag(v___x_4652_) == 0)
{
lean_dec_ref_known(v___x_4652_, 1);
v___y_4559_ = v___y_4623_;
v___y_4560_ = v___y_4625_;
v___y_4561_ = v___y_4626_;
v___y_4562_ = v___y_4627_;
v___y_4563_ = v___y_4628_;
goto v___jp_4558_;
}
else
{
lean_dec(v___y_4626_);
lean_dec_ref(v___y_4625_);
lean_dec(v_decl_3732_);
return v___x_4652_;
}
}
}
}
}
}
v___jp_4653_:
{
lean_object* v___x_4660_; lean_object* v_env_4661_; uint8_t v___x_4662_; 
v___x_4660_ = lean_st_ref_get(v___y_4659_);
v_env_4661_ = lean_ctor_get(v___x_4660_, 0);
lean_inc_ref(v_env_4661_);
lean_dec(v___x_4660_);
v___x_4662_ = l_Lean_Environment_containsOnBranch(v_env_4661_, v_fst_4654_);
lean_dec_ref(v_env_4661_);
if (v___x_4662_ == 0)
{
v___y_4623_ = v_snd_4656_;
v___y_4624_ = v_exportedInfo_x3f_4657_;
v___y_4625_ = v_fst_4655_;
v___y_4626_ = v_fst_4654_;
v___y_4627_ = v___y_4658_;
v___y_4628_ = v___y_4659_;
goto v___jp_4622_;
}
else
{
lean_object* v___x_4663_; lean_object* v_env_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; 
lean_dec(v_exportedInfo_x3f_4657_);
lean_dec_ref(v_fst_4655_);
lean_dec(v_decl_3732_);
v___x_4663_ = lean_st_ref_get(v___y_4659_);
v_env_4664_ = lean_ctor_get(v___x_4663_, 0);
lean_inc_ref(v_env_4664_);
lean_dec(v___x_4663_);
v___x_4665_ = lean_elab_environment_to_kernel_env(v_env_4664_);
v___x_4666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4666_, 0, v___x_4665_);
lean_ctor_set(v___x_4666_, 1, v_fst_4654_);
v___x_4667_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4666_, v___y_4658_, v___y_4659_);
return v___x_4667_;
}
}
v___jp_4668_:
{
lean_object* v_name_4674_; lean_object* v___x_4675_; uint8_t v___x_4676_; 
v_name_4674_ = lean_ctor_get(v_toConstantVal_4670_, 0);
lean_inc(v_name_4674_);
lean_dec_ref(v_toConstantVal_4670_);
v___x_4675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4675_, 0, v___y_4669_);
v___x_4676_ = 0;
v_fst_4654_ = v_name_4674_;
v_fst_4655_ = v___x_4675_;
v_snd_4656_ = v___x_4676_;
v_exportedInfo_x3f_4657_ = v_exportedInfo_x3f_4671_;
v___y_4658_ = v___y_4672_;
v___y_4659_ = v___y_4673_;
goto v___jp_4653_;
}
v___jp_4677_:
{
uint8_t v___x_4683_; uint8_t v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; 
v___x_4683_ = 0;
v___x_4684_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4680_, v___x_4683_);
lean_inc_ref(v_toConstantVal_4679_);
v___x_4685_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4685_, 0, v_toConstantVal_4679_);
lean_ctor_set_uint8(v___x_4685_, sizeof(void*)*1, v___x_4684_);
v___x_4686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4686_, 0, v___x_4685_);
v___x_4687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4687_, 0, v___x_4686_);
v___y_4669_ = v___y_4678_;
v_toConstantVal_4670_ = v_toConstantVal_4679_;
v_exportedInfo_x3f_4671_ = v___x_4687_;
v___y_4672_ = v___y_4681_;
v___y_4673_ = v___y_4682_;
goto v___jp_4668_;
}
v___jp_4688_:
{
lean_object* v_toConstantVal_4692_; uint8_t v_safety_4693_; 
v_toConstantVal_4692_ = lean_ctor_get(v___y_4689_, 0);
lean_inc_ref(v_toConstantVal_4692_);
v_safety_4693_ = lean_ctor_get_uint8(v___y_4689_, sizeof(void*)*4);
v___y_4678_ = v___y_4689_;
v_toConstantVal_4679_ = v_toConstantVal_4692_;
v_safety_4680_ = v_safety_4693_;
v___y_4681_ = v___y_4690_;
v___y_4682_ = v___y_4691_;
goto v___jp_4677_;
}
v___jp_4694_:
{
lean_object* v_options_4698_; uint8_t v_hasTrace_4699_; 
v_options_4698_ = lean_ctor_get(v___y_4696_, 2);
v_hasTrace_4699_ = lean_ctor_get_uint8(v_options_4698_, sizeof(void*)*1);
if (v_hasTrace_4699_ == 0)
{
v___y_4689_ = v___y_4695_;
v___y_4690_ = v___y_4696_;
v___y_4691_ = v___y_4697_;
goto v___jp_4688_;
}
else
{
lean_object* v_inheritedTraceOptions_4700_; uint8_t v___x_4701_; 
v_inheritedTraceOptions_4700_ = lean_ctor_get(v___y_4696_, 13);
v___x_4701_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4700_, v_options_4698_, v___x_4129_);
if (v___x_4701_ == 0)
{
v___y_4689_ = v___y_4695_;
v___y_4690_ = v___y_4696_;
v___y_4691_ = v___y_4697_;
goto v___jp_4688_;
}
else
{
lean_object* v_toConstantVal_4702_; uint8_t v_safety_4703_; lean_object* v_name_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; 
v_toConstantVal_4702_ = lean_ctor_get(v___y_4695_, 0);
lean_inc_ref(v_toConstantVal_4702_);
v_safety_4703_ = lean_ctor_get_uint8(v___y_4695_, sizeof(void*)*4);
v_name_4704_ = lean_ctor_get(v_toConstantVal_4702_, 0);
v___x_4705_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_4704_);
v___x_4706_ = l_Lean_MessageData_ofName(v_name_4704_);
v___x_4707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4707_, 0, v___x_4705_);
lean_ctor_set(v___x_4707_, 1, v___x_4706_);
v___x_4708_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4709_, 0, v___x_4707_);
lean_ctor_set(v___x_4709_, 1, v___x_4708_);
v___x_4710_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_4709_, v___y_4696_, v___y_4697_);
if (lean_obj_tag(v___x_4710_) == 0)
{
lean_dec_ref_known(v___x_4710_, 1);
v___y_4678_ = v___y_4695_;
v_toConstantVal_4679_ = v_toConstantVal_4702_;
v_safety_4680_ = v_safety_4703_;
v___y_4681_ = v___y_4696_;
v___y_4682_ = v___y_4697_;
goto v___jp_4677_;
}
else
{
lean_dec_ref(v_toConstantVal_4702_);
lean_dec_ref(v___y_4695_);
lean_dec(v_decl_3732_);
return v___x_4710_;
}
}
}
}
v___jp_4711_:
{
lean_object* v_toConstantVal_4716_; 
v_toConstantVal_4716_ = lean_ctor_get(v___y_4712_, 0);
lean_inc_ref(v_toConstantVal_4716_);
v___y_4669_ = v___y_4712_;
v_toConstantVal_4670_ = v_toConstantVal_4716_;
v_exportedInfo_x3f_4671_ = v_exportedInfo_x3f_4713_;
v___y_4672_ = v___y_4714_;
v___y_4673_ = v___y_4715_;
goto v___jp_4668_;
}
v___jp_4717_:
{
lean_object* v___x_4723_; uint8_t v_isModule_4724_; 
v___x_4723_ = l_Lean_Environment_header(v___y_4719_);
lean_dec_ref(v___y_4719_);
v_isModule_4724_ = lean_ctor_get_uint8(v___x_4723_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4723_);
if (v_isModule_4724_ == 0)
{
lean_dec_ref(v___y_4721_);
v___y_4712_ = v___y_4718_;
v_exportedInfo_x3f_4713_ = v___x_4621_;
v___y_4714_ = v___y_4720_;
v___y_4715_ = v___y_4722_;
goto v___jp_4711_;
}
else
{
uint8_t v_isExporting_4725_; 
v_isExporting_4725_ = lean_ctor_get_uint8(v___y_4721_, sizeof(void*)*8);
lean_dec_ref(v___y_4721_);
if (v_isExporting_4725_ == 0)
{
v___y_4695_ = v___y_4718_;
v___y_4696_ = v___y_4720_;
v___y_4697_ = v___y_4722_;
goto v___jp_4694_;
}
else
{
if (v___x_4431_ == 0)
{
v___y_4712_ = v___y_4718_;
v_exportedInfo_x3f_4713_ = v___x_4621_;
v___y_4714_ = v___y_4720_;
v___y_4715_ = v___y_4722_;
goto v___jp_4711_;
}
else
{
v___y_4695_ = v___y_4718_;
v___y_4696_ = v___y_4720_;
v___y_4697_ = v___y_4722_;
goto v___jp_4694_;
}
}
}
}
v___jp_4726_:
{
lean_object* v___x_4730_; lean_object* v___x_4731_; 
v___x_4730_ = lean_st_ref_get(v___y_4729_);
v___x_4731_ = lean_st_ref_get(v___y_4729_);
if (v_forceExpose_3733_ == 0)
{
lean_object* v_env_4732_; lean_object* v_env_4733_; 
v_env_4732_ = lean_ctor_get(v___x_4730_, 0);
lean_inc_ref(v_env_4732_);
lean_dec(v___x_4730_);
v_env_4733_ = lean_ctor_get(v___x_4731_, 0);
lean_inc_ref(v_env_4733_);
lean_dec(v___x_4731_);
v___y_4718_ = v_defn_4727_;
v___y_4719_ = v_env_4732_;
v___y_4720_ = v___y_4728_;
v___y_4721_ = v_env_4733_;
v___y_4722_ = v___y_4729_;
goto v___jp_4717_;
}
else
{
if (v___x_4431_ == 0)
{
lean_dec(v___x_4731_);
lean_dec(v___x_4730_);
v___y_4712_ = v_defn_4727_;
v_exportedInfo_x3f_4713_ = v___x_4621_;
v___y_4714_ = v___y_4728_;
v___y_4715_ = v___y_4729_;
goto v___jp_4711_;
}
else
{
lean_object* v_env_4734_; lean_object* v_env_4735_; 
v_env_4734_ = lean_ctor_get(v___x_4730_, 0);
lean_inc_ref(v_env_4734_);
lean_dec(v___x_4730_);
v_env_4735_ = lean_ctor_get(v___x_4731_, 0);
lean_inc_ref(v_env_4735_);
lean_dec(v___x_4731_);
v___y_4718_ = v_defn_4727_;
v___y_4719_ = v_env_4734_;
v___y_4720_ = v___y_4728_;
v___y_4721_ = v_env_4735_;
v___y_4722_ = v___y_4729_;
goto v___jp_4717_;
}
}
}
}
}
}
else
{
goto v___jp_4278_;
}
v___jp_4432_:
{
lean_object* v___x_4443_; 
lean_inc_ref(v___y_4438_);
v___x_4443_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_4439_, v___y_4438_, v___y_4437_, v___y_4442_);
if (lean_obj_tag(v___x_4443_) == 0)
{
lean_object* v___x_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4490_; 
lean_dec_ref_known(v___x_4443_, 1);
lean_inc_ref(v___y_4436_);
v___x_4444_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4436_, v___y_4441_);
v_isSharedCheck_4490_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4490_ == 0)
{
lean_object* v_unused_4491_; 
v_unused_4491_ = lean_ctor_get(v___x_4444_, 0);
lean_dec(v_unused_4491_);
v___x_4446_ = v___x_4444_;
v_isShared_4447_ = v_isSharedCheck_4490_;
goto v_resetjp_4445_;
}
else
{
lean_dec(v___x_4444_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4490_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v_options_4448_; lean_object* v___x_4449_; uint8_t v___x_4450_; 
v_options_4448_ = lean_ctor_get(v___y_4435_, 2);
v___x_4449_ = l_Lean_Elab_async;
v___x_4450_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_4448_, v___x_4449_);
if (v___x_4450_ == 0)
{
lean_object* v___x_4451_; lean_object* v_r_4452_; 
lean_del_object(v___x_4446_);
lean_dec_ref(v___y_4434_);
lean_dec_ref(v___y_4433_);
v___x_4451_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4438_, v___y_4441_);
lean_dec_ref(v___x_4451_);
v_r_4452_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3732_, v___y_4435_, v___y_4441_);
if (lean_obj_tag(v_r_4452_) == 0)
{
lean_object* v_a_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4462_; 
v_a_4453_ = lean_ctor_get(v_r_4452_, 0);
v_isSharedCheck_4462_ = !lean_is_exclusive(v_r_4452_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4455_ = v_r_4452_;
v_isShared_4456_ = v_isSharedCheck_4462_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_a_4453_);
lean_dec(v_r_4452_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4462_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
lean_object* v___x_4458_; 
lean_inc(v_a_4453_);
if (v_isShared_4456_ == 0)
{
lean_ctor_set_tag(v___x_4455_, 1);
v___x_4458_ = v___x_4455_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v_a_4453_);
v___x_4458_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
lean_object* v___x_4459_; 
v___x_4459_ = lean_apply_2(v___y_4440_, v___x_4458_, lean_box(0));
if (lean_obj_tag(v___x_4459_) == 0)
{
lean_dec_ref_known(v___x_4459_, 1);
v___y_3764_ = v___y_4436_;
v___y_3765_ = v___y_4441_;
v_a_3766_ = v_a_4453_;
goto v___jp_3763_;
}
else
{
lean_object* v_a_4460_; 
lean_dec(v_a_4453_);
v_a_4460_ = lean_ctor_get(v___x_4459_, 0);
lean_inc(v_a_4460_);
lean_dec_ref_known(v___x_4459_, 1);
v___y_3777_ = v___y_4436_;
v___y_3778_ = v___y_4441_;
v_a_3779_ = v_a_4460_;
goto v___jp_3776_;
}
}
}
}
else
{
lean_object* v_a_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; 
v_a_4463_ = lean_ctor_get(v_r_4452_, 0);
lean_inc(v_a_4463_);
lean_dec_ref_known(v_r_4452_, 1);
v___x_4464_ = lean_box(0);
v___x_4465_ = lean_apply_2(v___y_4440_, v___x_4464_, lean_box(0));
if (lean_obj_tag(v___x_4465_) == 0)
{
lean_dec_ref_known(v___x_4465_, 1);
v___y_3777_ = v___y_4436_;
v___y_3778_ = v___y_4441_;
v_a_3779_ = v_a_4463_;
goto v___jp_3776_;
}
else
{
lean_object* v_a_4466_; 
lean_dec(v_a_4463_);
v_a_4466_ = lean_ctor_get(v___x_4465_, 0);
lean_inc(v_a_4466_);
lean_dec_ref_known(v___x_4465_, 1);
v___y_3777_ = v___y_4436_;
v___y_3778_ = v___y_4441_;
v_a_3779_ = v_a_4466_;
goto v___jp_3776_;
}
}
}
else
{
lean_object* v___x_4467_; lean_object* v___x_4469_; 
lean_dec_ref(v___y_4440_);
lean_dec_ref(v___y_4438_);
lean_dec_ref(v___y_4436_);
lean_dec(v_decl_3732_);
v___x_4467_ = l_IO_CancelToken_new();
if (v_isShared_4447_ == 0)
{
lean_ctor_set_tag(v___x_4446_, 1);
lean_ctor_set(v___x_4446_, 0, v___x_4467_);
v___x_4469_ = v___x_4446_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4489_; 
v_reuseFailAlloc_4489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4489_, 0, v___x_4467_);
v___x_4469_ = v_reuseFailAlloc_4489_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; 
v___x_4470_ = lean_unsigned_to_nat(0u);
v___x_4471_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_4472_ = l_Lean_Name_toString(v___x_4471_, v_hasTrace_3791_);
lean_inc_ref(v___x_4469_);
v___x_4473_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_4433_, v___x_4469_, v___x_4472_, v___y_4435_, v___y_4441_);
if (lean_obj_tag(v___x_4473_) == 0)
{
lean_object* v_a_4474_; lean_object* v_checked_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; 
v_a_4474_ = lean_ctor_get(v___x_4473_, 0);
lean_inc(v_a_4474_);
lean_dec_ref_known(v___x_4473_, 1);
v_checked_4475_ = lean_ctor_get(v___y_4434_, 2);
lean_inc_ref(v_checked_4475_);
lean_dec_ref(v___y_4434_);
v___x_4476_ = lean_io_map_task(v_a_4474_, v_checked_4475_, v___x_4470_, v___x_4431_);
v___x_4477_ = lean_box(0);
v___x_4478_ = lean_box(2);
v___x_4479_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4479_, 0, v___x_4477_);
lean_ctor_set(v___x_4479_, 1, v___x_4478_);
lean_ctor_set(v___x_4479_, 2, v___x_4469_);
lean_ctor_set(v___x_4479_, 3, v___x_4476_);
v___x_4480_ = l_Lean_Core_logSnapshotTask___redArg(v___x_4479_, v___y_4441_);
return v___x_4480_;
}
else
{
lean_object* v_a_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4488_; 
lean_dec_ref(v___x_4469_);
lean_dec_ref(v___y_4434_);
v_a_4481_ = lean_ctor_get(v___x_4473_, 0);
v_isSharedCheck_4488_ = !lean_is_exclusive(v___x_4473_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4483_ = v___x_4473_;
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_a_4481_);
lean_dec(v___x_4473_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v___x_4486_; 
if (v_isShared_4484_ == 0)
{
v___x_4486_ = v___x_4483_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_a_4481_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
return v___x_4486_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4504_; 
lean_dec_ref(v___y_4440_);
lean_dec_ref(v___y_4438_);
lean_dec_ref(v___y_4436_);
lean_dec_ref(v___y_4434_);
lean_dec_ref(v___y_4433_);
lean_dec(v_decl_3732_);
v_a_4492_ = lean_ctor_get(v___x_4443_, 0);
v_isSharedCheck_4504_ = !lean_is_exclusive(v___x_4443_);
if (v_isSharedCheck_4504_ == 0)
{
v___x_4494_ = v___x_4443_;
v_isShared_4495_ = v_isSharedCheck_4504_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_a_4492_);
lean_dec(v___x_4443_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4504_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v_ref_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4502_; 
v_ref_4496_ = lean_ctor_get(v___y_4435_, 5);
v___x_4497_ = lean_io_error_to_string(v_a_4492_);
v___x_4498_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4498_, 0, v___x_4497_);
v___x_4499_ = l_Lean_MessageData_ofFormat(v___x_4498_);
lean_inc(v_ref_4496_);
v___x_4500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4500_, 0, v_ref_4496_);
lean_ctor_set(v___x_4500_, 1, v___x_4499_);
if (v_isShared_4495_ == 0)
{
lean_ctor_set(v___x_4494_, 0, v___x_4500_);
v___x_4502_ = v___x_4494_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4503_; 
v_reuseFailAlloc_4503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4503_, 0, v___x_4500_);
v___x_4502_ = v_reuseFailAlloc_4503_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
return v___x_4502_;
}
}
}
}
v___jp_4505_:
{
lean_object* v___x_4516_; 
lean_inc_ref(v___y_4506_);
v___x_4516_ = l_Lean_Environment_addConstAsync(v___y_4506_, v___y_4514_, v___y_4509_, v___y_4515_, v___x_4431_, v_hasTrace_3791_);
if (lean_obj_tag(v___x_4516_) == 0)
{
lean_object* v_a_4517_; lean_object* v_mainEnv_4518_; lean_object* v_asyncEnv_4519_; lean_object* v___f_4520_; lean_object* v___f_4521_; lean_object* v___x_4522_; 
v_a_4517_ = lean_ctor_get(v___x_4516_, 0);
lean_inc_n(v_a_4517_, 3);
lean_dec_ref_known(v___x_4516_, 1);
v_mainEnv_4518_ = lean_ctor_get(v_a_4517_, 0);
lean_inc_ref(v_mainEnv_4518_);
v_asyncEnv_4519_ = lean_ctor_get(v_a_4517_, 1);
lean_inc_ref_n(v_asyncEnv_4519_, 2);
lean_inc_ref(v___y_4507_);
lean_inc(v___y_4508_);
v___f_4520_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4520_, 0, v___y_4508_);
lean_closure_set(v___f_4520_, 1, v_a_4517_);
lean_closure_set(v___f_4520_, 2, v___y_4507_);
lean_inc(v_decl_3732_);
v___f_4521_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4521_, 0, v_asyncEnv_4519_);
lean_closure_set(v___f_4521_, 1, v_a_4517_);
lean_closure_set(v___f_4521_, 2, v_decl_3732_);
v___x_4522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4522_, 0, v___y_4511_);
if (lean_obj_tag(v___y_4512_) == 0)
{
lean_inc_ref(v___x_4522_);
v___y_4433_ = v___f_4521_;
v___y_4434_ = v___y_4506_;
v___y_4435_ = v___y_4510_;
v___y_4436_ = v_mainEnv_4518_;
v___y_4437_ = v___x_4522_;
v___y_4438_ = v_asyncEnv_4519_;
v___y_4439_ = v_a_4517_;
v___y_4440_ = v___f_4520_;
v___y_4441_ = v___y_4513_;
v___y_4442_ = v___x_4522_;
goto v___jp_4432_;
}
else
{
v___y_4433_ = v___f_4521_;
v___y_4434_ = v___y_4506_;
v___y_4435_ = v___y_4510_;
v___y_4436_ = v_mainEnv_4518_;
v___y_4437_ = v___x_4522_;
v___y_4438_ = v_asyncEnv_4519_;
v___y_4439_ = v_a_4517_;
v___y_4440_ = v___f_4520_;
v___y_4441_ = v___y_4513_;
v___y_4442_ = v___y_4512_;
goto v___jp_4432_;
}
}
else
{
lean_object* v_a_4523_; lean_object* v___x_4525_; uint8_t v_isShared_4526_; uint8_t v_isSharedCheck_4535_; 
lean_dec(v___y_4512_);
lean_dec_ref(v___y_4511_);
lean_dec_ref(v___y_4506_);
lean_dec(v_decl_3732_);
v_a_4523_ = lean_ctor_get(v___x_4516_, 0);
v_isSharedCheck_4535_ = !lean_is_exclusive(v___x_4516_);
if (v_isSharedCheck_4535_ == 0)
{
v___x_4525_ = v___x_4516_;
v_isShared_4526_ = v_isSharedCheck_4535_;
goto v_resetjp_4524_;
}
else
{
lean_inc(v_a_4523_);
lean_dec(v___x_4516_);
v___x_4525_ = lean_box(0);
v_isShared_4526_ = v_isSharedCheck_4535_;
goto v_resetjp_4524_;
}
v_resetjp_4524_:
{
lean_object* v_ref_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4533_; 
v_ref_4527_ = lean_ctor_get(v___y_4510_, 5);
v___x_4528_ = lean_io_error_to_string(v_a_4523_);
v___x_4529_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4529_, 0, v___x_4528_);
v___x_4530_ = l_Lean_MessageData_ofFormat(v___x_4529_);
lean_inc(v_ref_4527_);
v___x_4531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4531_, 0, v_ref_4527_);
lean_ctor_set(v___x_4531_, 1, v___x_4530_);
if (v_isShared_4526_ == 0)
{
lean_ctor_set(v___x_4525_, 0, v___x_4531_);
v___x_4533_ = v___x_4525_;
goto v_reusejp_4532_;
}
else
{
lean_object* v_reuseFailAlloc_4534_; 
v_reuseFailAlloc_4534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4534_, 0, v___x_4531_);
v___x_4533_ = v_reuseFailAlloc_4534_;
goto v_reusejp_4532_;
}
v_reusejp_4532_:
{
return v___x_4533_;
}
}
}
}
v___jp_4536_:
{
lean_object* v___x_4543_; 
v___x_4543_ = lean_st_ref_get(v___y_4542_);
if (lean_obj_tag(v_exportedInfo_x3f_4540_) == 0)
{
lean_object* v_env_4544_; lean_object* v___x_4545_; 
v_env_4544_ = lean_ctor_get(v___x_4543_, 0);
lean_inc_ref(v_env_4544_);
lean_dec(v___x_4543_);
v___x_4545_ = lean_box(0);
v___y_4506_ = v_env_4544_;
v___y_4507_ = v___y_4541_;
v___y_4508_ = v___y_4542_;
v___y_4509_ = v___y_4537_;
v___y_4510_ = v___y_4541_;
v___y_4511_ = v___y_4538_;
v___y_4512_ = v_exportedInfo_x3f_4540_;
v___y_4513_ = v___y_4542_;
v___y_4514_ = v___y_4539_;
v___y_4515_ = v___x_4545_;
goto v___jp_4505_;
}
else
{
lean_object* v_env_4546_; lean_object* v_val_4547_; uint8_t v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; 
v_env_4546_ = lean_ctor_get(v___x_4543_, 0);
lean_inc_ref(v_env_4546_);
lean_dec(v___x_4543_);
v_val_4547_ = lean_ctor_get(v_exportedInfo_x3f_4540_, 0);
v___x_4548_ = l_Lean_ConstantKind_ofConstantInfo(v_val_4547_);
v___x_4549_ = lean_box(v___x_4548_);
v___x_4550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4550_, 0, v___x_4549_);
v___y_4506_ = v_env_4546_;
v___y_4507_ = v___y_4541_;
v___y_4508_ = v___y_4542_;
v___y_4509_ = v___y_4537_;
v___y_4510_ = v___y_4541_;
v___y_4511_ = v___y_4538_;
v___y_4512_ = v_exportedInfo_x3f_4540_;
v___y_4513_ = v___y_4542_;
v___y_4514_ = v___y_4539_;
v___y_4515_ = v___x_4550_;
goto v___jp_4505_;
}
}
v___jp_4551_:
{
lean_object* v___x_4557_; 
lean_inc_ref(v___y_4553_);
v___x_4557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4557_, 0, v___y_4553_);
v___y_4537_ = v___y_4552_;
v___y_4538_ = v___y_4553_;
v___y_4539_ = v___y_4554_;
v_exportedInfo_x3f_4540_ = v___x_4557_;
v___y_4541_ = v___y_4555_;
v___y_4542_ = v___y_4556_;
goto v___jp_4536_;
}
v___jp_4558_:
{
lean_object* v___x_4564_; 
lean_inc_ref(v___y_4560_);
v___x_4564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4564_, 0, v___y_4560_);
v___y_4537_ = v___y_4559_;
v___y_4538_ = v___y_4560_;
v___y_4539_ = v___y_4561_;
v_exportedInfo_x3f_4540_ = v___x_4564_;
v___y_4541_ = v___y_4562_;
v___y_4542_ = v___y_4563_;
goto v___jp_4536_;
}
}
else
{
goto v___jp_4278_;
}
v___jp_4131_:
{
lean_object* v___x_4135_; double v___x_4136_; double v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; 
v___x_4135_ = lean_io_get_num_heartbeats();
v___x_4136_ = lean_float_of_nat(v___y_4132_);
v___x_4137_ = lean_float_of_nat(v___x_4135_);
v___x_4138_ = lean_box_float(v___x_4136_);
v___x_4139_ = lean_box_float(v___x_4137_);
v___x_4140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4140_, 0, v___x_4138_);
lean_ctor_set(v___x_4140_, 1, v___x_4139_);
v___x_4141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4141_, 0, v_a_4134_);
lean_ctor_set(v___x_4141_, 1, v___x_4140_);
v___x_4142_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3927_, v_hasTrace_3791_, v___x_4128_, v_options_3789_, v___x_4130_, v___y_4133_, v___f_4127_, v___x_4141_, v_a_3734_, v_a_3735_);
return v___x_4142_;
}
v___jp_4143_:
{
if (lean_obj_tag(v___y_4146_) == 0)
{
lean_object* v_a_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4154_; 
v_a_4147_ = lean_ctor_get(v___y_4146_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___y_4146_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4149_ = v___y_4146_;
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_a_4147_);
lean_dec(v___y_4146_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___x_4152_; 
if (v_isShared_4150_ == 0)
{
lean_ctor_set_tag(v___x_4149_, 1);
v___x_4152_ = v___x_4149_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_a_4147_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
v___y_4132_ = v___y_4144_;
v___y_4133_ = v___y_4145_;
v_a_4134_ = v___x_4152_;
goto v___jp_4131_;
}
}
}
else
{
lean_object* v_a_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4162_; 
v_a_4155_ = lean_ctor_get(v___y_4146_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___y_4146_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4157_ = v___y_4146_;
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_a_4155_);
lean_dec(v___y_4146_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4160_; 
if (v_isShared_4158_ == 0)
{
lean_ctor_set_tag(v___x_4157_, 0);
v___x_4160_ = v___x_4157_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_a_4155_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
v___y_4132_ = v___y_4144_;
v___y_4133_ = v___y_4145_;
v_a_4134_ = v___x_4160_;
goto v___jp_4131_;
}
}
}
}
v___jp_4163_:
{
lean_object* v___x_4168_; lean_object* v___x_4169_; 
v___x_4168_ = lean_box(0);
lean_inc(v_a_3735_);
lean_inc_ref(v_a_3734_);
v___x_4169_ = lean_apply_5(v___y_4167_, v___x_4168_, v___y_4165_, v_a_3734_, v_a_3735_, lean_box(0));
v___y_4144_ = v___y_4164_;
v___y_4145_ = v___y_4166_;
v___y_4146_ = v___x_4169_;
goto v___jp_4143_;
}
v___jp_4170_:
{
lean_object* v___x_4175_; lean_object* v___x_4176_; 
v___x_4175_ = lean_box(0);
lean_inc(v_a_3735_);
lean_inc_ref(v_a_3734_);
v___x_4176_ = lean_apply_5(v___y_4171_, v___x_4175_, v___y_4173_, v_a_3734_, v_a_3735_, lean_box(0));
v___y_4144_ = v___y_4172_;
v___y_4145_ = v___y_4174_;
v___y_4146_ = v___x_4176_;
goto v___jp_4143_;
}
v___jp_4177_:
{
lean_object* v___x_4181_; double v___x_4182_; double v___x_4183_; double v___x_4184_; double v___x_4185_; double v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4181_ = lean_io_mono_nanos_now();
v___x_4182_ = lean_float_of_nat(v___y_4178_);
v___x_4183_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_4184_ = lean_float_div(v___x_4182_, v___x_4183_);
v___x_4185_ = lean_float_of_nat(v___x_4181_);
v___x_4186_ = lean_float_div(v___x_4185_, v___x_4183_);
v___x_4187_ = lean_box_float(v___x_4184_);
v___x_4188_ = lean_box_float(v___x_4186_);
v___x_4189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4189_, 0, v___x_4187_);
lean_ctor_set(v___x_4189_, 1, v___x_4188_);
v___x_4190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4190_, 0, v_a_4180_);
lean_ctor_set(v___x_4190_, 1, v___x_4189_);
v___x_4191_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3927_, v_hasTrace_3791_, v___x_4128_, v_options_3789_, v___x_4130_, v___y_4179_, v___f_4127_, v___x_4190_, v_a_3734_, v_a_3735_);
return v___x_4191_;
}
v___jp_4192_:
{
if (lean_obj_tag(v___y_4195_) == 0)
{
lean_object* v_a_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4203_; 
v_a_4196_ = lean_ctor_get(v___y_4195_, 0);
v_isSharedCheck_4203_ = !lean_is_exclusive(v___y_4195_);
if (v_isSharedCheck_4203_ == 0)
{
v___x_4198_ = v___y_4195_;
v_isShared_4199_ = v_isSharedCheck_4203_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_a_4196_);
lean_dec(v___y_4195_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4203_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
lean_object* v___x_4201_; 
if (v_isShared_4199_ == 0)
{
lean_ctor_set_tag(v___x_4198_, 1);
v___x_4201_ = v___x_4198_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_a_4196_);
v___x_4201_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
v___y_4178_ = v___y_4193_;
v___y_4179_ = v___y_4194_;
v_a_4180_ = v___x_4201_;
goto v___jp_4177_;
}
}
}
else
{
lean_object* v_a_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4211_; 
v_a_4204_ = lean_ctor_get(v___y_4195_, 0);
v_isSharedCheck_4211_ = !lean_is_exclusive(v___y_4195_);
if (v_isSharedCheck_4211_ == 0)
{
v___x_4206_ = v___y_4195_;
v_isShared_4207_ = v_isSharedCheck_4211_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_a_4204_);
lean_dec(v___y_4195_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4211_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v___x_4209_; 
if (v_isShared_4207_ == 0)
{
lean_ctor_set_tag(v___x_4206_, 0);
v___x_4209_ = v___x_4206_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v_a_4204_);
v___x_4209_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
v___y_4178_ = v___y_4193_;
v___y_4179_ = v___y_4194_;
v_a_4180_ = v___x_4209_;
goto v___jp_4177_;
}
}
}
}
v___jp_4212_:
{
lean_object* v___x_4217_; lean_object* v___x_4218_; 
v___x_4217_ = lean_box(0);
lean_inc(v_a_3735_);
lean_inc_ref(v_a_3734_);
v___x_4218_ = lean_apply_5(v___y_4214_, v___x_4217_, v___y_4215_, v_a_3734_, v_a_3735_, lean_box(0));
v___y_4193_ = v___y_4213_;
v___y_4194_ = v___y_4216_;
v___y_4195_ = v___x_4218_;
goto v___jp_4192_;
}
v___jp_4219_:
{
if (v___x_4130_ == 0)
{
lean_object* v___x_4224_; lean_object* v___x_4225_; 
lean_dec_ref(v___y_4221_);
v___x_4224_ = lean_box(0);
lean_inc(v_a_3735_);
lean_inc_ref(v_a_3734_);
v___x_4225_ = lean_apply_4(v___y_4222_, v___x_4224_, v_a_3734_, v_a_3735_, lean_box(0));
v___y_4193_ = v___y_4220_;
v___y_4194_ = v___y_4223_;
v___y_4195_ = v___x_4225_;
goto v___jp_4192_;
}
else
{
lean_object* v_toConstantVal_4226_; lean_object* v_name_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; 
v_toConstantVal_4226_ = lean_ctor_get(v___y_4221_, 0);
lean_inc_ref(v_toConstantVal_4226_);
lean_dec_ref(v___y_4221_);
v_name_4227_ = lean_ctor_get(v_toConstantVal_4226_, 0);
lean_inc(v_name_4227_);
lean_dec_ref(v_toConstantVal_4226_);
v___x_4228_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
v___x_4229_ = l_Lean_MessageData_ofName(v_name_4227_);
v___x_4230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4230_, 0, v___x_4228_);
lean_ctor_set(v___x_4230_, 1, v___x_4229_);
v___x_4231_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4232_, 0, v___x_4230_);
lean_ctor_set(v___x_4232_, 1, v___x_4231_);
v___x_4233_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_4232_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v_a_4234_; lean_object* v___x_4235_; 
v_a_4234_ = lean_ctor_get(v___x_4233_, 0);
lean_inc(v_a_4234_);
lean_dec_ref_known(v___x_4233_, 1);
lean_inc(v_a_3735_);
lean_inc_ref(v_a_3734_);
v___x_4235_ = lean_apply_4(v___y_4222_, v_a_4234_, v_a_3734_, v_a_3735_, lean_box(0));
v___y_4193_ = v___y_4220_;
v___y_4194_ = v___y_4223_;
v___y_4195_ = v___x_4235_;
goto v___jp_4192_;
}
else
{
lean_dec_ref(v___y_4222_);
v___y_4193_ = v___y_4220_;
v___y_4194_ = v___y_4223_;
v___y_4195_ = v___x_4233_;
goto v___jp_4192_;
}
}
}
v___jp_4236_:
{
lean_object* v___x_4246_; uint8_t v_isModule_4247_; 
v___x_4246_ = l_Lean_Environment_header(v___y_4241_);
lean_dec_ref(v___y_4241_);
v_isModule_4247_ = lean_ctor_get_uint8(v___x_4246_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4246_);
if (v_isModule_4247_ == 0)
{
lean_dec_ref(v___y_4244_);
lean_dec_ref(v___y_4243_);
lean_dec_ref(v___y_4238_);
v___y_4213_ = v___y_4237_;
v___y_4214_ = v___y_4240_;
v___y_4215_ = v___y_4242_;
v___y_4216_ = v___y_4245_;
goto v___jp_4212_;
}
else
{
uint8_t v_isExporting_4248_; 
v_isExporting_4248_ = lean_ctor_get_uint8(v___y_4238_, sizeof(void*)*8);
lean_dec_ref(v___y_4238_);
if (v_isExporting_4248_ == 0)
{
lean_dec(v___y_4242_);
lean_dec_ref(v___y_4240_);
v___y_4220_ = v___y_4237_;
v___y_4221_ = v___y_4244_;
v___y_4222_ = v___y_4243_;
v___y_4223_ = v___y_4245_;
goto v___jp_4219_;
}
else
{
if (v___y_4239_ == 0)
{
lean_dec_ref(v___y_4244_);
lean_dec_ref(v___y_4243_);
v___y_4213_ = v___y_4237_;
v___y_4214_ = v___y_4240_;
v___y_4215_ = v___y_4242_;
v___y_4216_ = v___y_4245_;
goto v___jp_4212_;
}
else
{
lean_dec(v___y_4242_);
lean_dec_ref(v___y_4240_);
v___y_4220_ = v___y_4237_;
v___y_4221_ = v___y_4244_;
v___y_4222_ = v___y_4243_;
v___y_4223_ = v___y_4245_;
goto v___jp_4219_;
}
}
}
}
v___jp_4249_:
{
lean_object* v___x_4254_; lean_object* v___x_4255_; 
v___x_4254_ = lean_box(0);
lean_inc(v_a_3735_);
lean_inc_ref(v_a_3734_);
v___x_4255_ = lean_apply_5(v___y_4251_, v___x_4254_, v___y_4252_, v_a_3734_, v_a_3735_, lean_box(0));
v___y_4193_ = v___y_4250_;
v___y_4194_ = v___y_4253_;
v___y_4195_ = v___x_4255_;
goto v___jp_4192_;
}
v___jp_4256_:
{
lean_object* v___x_4264_; uint8_t v_isModule_4265_; 
v___x_4264_ = l_Lean_Environment_header(v___y_4263_);
lean_dec_ref(v___y_4263_);
v_isModule_4265_ = lean_ctor_get_uint8(v___x_4264_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4264_);
if (v_isModule_4265_ == 0)
{
lean_dec_ref(v___y_4261_);
lean_dec_ref(v___y_4257_);
v___y_4250_ = v___y_4258_;
v___y_4251_ = v___y_4259_;
v___y_4252_ = v___y_4260_;
v___y_4253_ = v___y_4262_;
goto v___jp_4249_;
}
else
{
lean_dec(v___y_4260_);
lean_dec_ref(v___y_4259_);
if (v___x_4130_ == 0)
{
lean_object* v___x_4266_; lean_object* v___x_4267_; 
lean_dec_ref(v___y_4261_);
v___x_4266_ = lean_box(0);
lean_inc(v_a_3735_);
lean_inc_ref(v_a_3734_);
v___x_4267_ = lean_apply_4(v___y_4257_, v___x_4266_, v_a_3734_, v_a_3735_, lean_box(0));
v___y_4193_ = v___y_4258_;
v___y_4194_ = v___y_4262_;
v___y_4195_ = v___x_4267_;
goto v___jp_4192_;
}
else
{
lean_object* v_toConstantVal_4268_; lean_object* v_name_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
v_toConstantVal_4268_ = lean_ctor_get(v___y_4261_, 0);
lean_inc_ref(v_toConstantVal_4268_);
lean_dec_ref(v___y_4261_);
v_name_4269_ = lean_ctor_get(v_toConstantVal_4268_, 0);
lean_inc(v_name_4269_);
lean_dec_ref(v_toConstantVal_4268_);
v___x_4270_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
v___x_4271_ = l_Lean_MessageData_ofName(v_name_4269_);
v___x_4272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4272_, 0, v___x_4270_);
lean_ctor_set(v___x_4272_, 1, v___x_4271_);
v___x_4273_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4274_, 0, v___x_4272_);
lean_ctor_set(v___x_4274_, 1, v___x_4273_);
v___x_4275_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_4274_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_object* v_a_4276_; lean_object* v___x_4277_; 
v_a_4276_ = lean_ctor_get(v___x_4275_, 0);
lean_inc(v_a_4276_);
lean_dec_ref_known(v___x_4275_, 1);
lean_inc(v_a_3735_);
lean_inc_ref(v_a_3734_);
v___x_4277_ = lean_apply_4(v___y_4257_, v_a_4276_, v_a_3734_, v_a_3735_, lean_box(0));
v___y_4193_ = v___y_4258_;
v___y_4194_ = v___y_4262_;
v___y_4195_ = v___x_4277_;
goto v___jp_4192_;
}
else
{
lean_dec_ref(v___y_4257_);
v___y_4193_ = v___y_4258_;
v___y_4194_ = v___y_4262_;
v___y_4195_ = v___x_4275_;
goto v___jp_4192_;
}
}
}
}
v___jp_4278_:
{
lean_object* v___x_4279_; lean_object* v_a_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4429_; 
v___x_4279_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v_a_3735_);
v_a_4280_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4429_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4429_ == 0)
{
v___x_4282_ = v___x_4279_;
v_isShared_4283_ = v_isSharedCheck_4429_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_a_4280_);
lean_dec(v___x_4279_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4429_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v___x_4284_; uint8_t v___x_4285_; 
v___x_4284_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4285_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3789_, v___x_4284_);
if (v___x_4285_ == 0)
{
lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v_env_4288_; lean_object* v_nextMacroScope_4289_; lean_object* v_ngen_4290_; lean_object* v_auxDeclNGen_4291_; lean_object* v_traceState_4292_; lean_object* v_messages_4293_; lean_object* v_infoState_4294_; lean_object* v_snapshotTasks_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4343_; 
v___x_4286_ = lean_io_mono_nanos_now();
v___x_4287_ = lean_st_ref_take(v_a_3735_);
v_env_4288_ = lean_ctor_get(v___x_4287_, 0);
v_nextMacroScope_4289_ = lean_ctor_get(v___x_4287_, 1);
v_ngen_4290_ = lean_ctor_get(v___x_4287_, 2);
v_auxDeclNGen_4291_ = lean_ctor_get(v___x_4287_, 3);
v_traceState_4292_ = lean_ctor_get(v___x_4287_, 4);
v_messages_4293_ = lean_ctor_get(v___x_4287_, 6);
v_infoState_4294_ = lean_ctor_get(v___x_4287_, 7);
v_snapshotTasks_4295_ = lean_ctor_get(v___x_4287_, 8);
v_isSharedCheck_4343_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4343_ == 0)
{
lean_object* v_unused_4344_; 
v_unused_4344_ = lean_ctor_get(v___x_4287_, 5);
lean_dec(v_unused_4344_);
v___x_4297_ = v___x_4287_;
v_isShared_4298_ = v_isSharedCheck_4343_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_snapshotTasks_4295_);
lean_inc(v_infoState_4294_);
lean_inc(v_messages_4293_);
lean_inc(v_traceState_4292_);
lean_inc(v_auxDeclNGen_4291_);
lean_inc(v_ngen_4290_);
lean_inc(v_nextMacroScope_4289_);
lean_inc(v_env_4288_);
lean_dec(v___x_4287_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4343_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4303_; 
lean_inc(v_decl_3732_);
v___x_4299_ = l_Lean_Declaration_getNames(v_decl_3732_);
v___x_4300_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4288_, v___x_4299_);
v___x_4301_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4298_ == 0)
{
lean_ctor_set(v___x_4297_, 5, v___x_4301_);
lean_ctor_set(v___x_4297_, 0, v___x_4300_);
v___x_4303_ = v___x_4297_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v___x_4300_);
lean_ctor_set(v_reuseFailAlloc_4342_, 1, v_nextMacroScope_4289_);
lean_ctor_set(v_reuseFailAlloc_4342_, 2, v_ngen_4290_);
lean_ctor_set(v_reuseFailAlloc_4342_, 3, v_auxDeclNGen_4291_);
lean_ctor_set(v_reuseFailAlloc_4342_, 4, v_traceState_4292_);
lean_ctor_set(v_reuseFailAlloc_4342_, 5, v___x_4301_);
lean_ctor_set(v_reuseFailAlloc_4342_, 6, v_messages_4293_);
lean_ctor_set(v_reuseFailAlloc_4342_, 7, v_infoState_4294_);
lean_ctor_set(v_reuseFailAlloc_4342_, 8, v_snapshotTasks_4295_);
v___x_4303_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___f_4308_; 
v___x_4304_ = lean_st_ref_set(v_a_3735_, v___x_4303_);
v___x_4305_ = lean_box(0);
v___x_4306_ = lean_box(v_hasTrace_3791_);
v___x_4307_ = lean_box(v___x_4285_);
lean_inc(v_decl_3732_);
v___f_4308_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed), 11, 6);
lean_closure_set(v___f_4308_, 0, v_decl_3732_);
lean_closure_set(v___f_4308_, 1, v___x_4306_);
lean_closure_set(v___f_4308_, 2, v___x_4307_);
lean_closure_set(v___f_4308_, 3, v___x_4301_);
lean_closure_set(v___f_4308_, 4, v_cls_3927_);
lean_closure_set(v___f_4308_, 5, v___x_4305_);
switch(lean_obj_tag(v_decl_3732_))
{
case 2:
{
lean_object* v_val_4309_; lean_object* v___x_4310_; lean_object* v_env_4311_; lean_object* v___f_4312_; lean_object* v___x_4313_; lean_object* v___f_4314_; 
lean_del_object(v___x_4282_);
v_val_4309_ = lean_ctor_get(v_decl_3732_, 0);
lean_inc_ref_n(v_val_4309_, 3);
lean_dec_ref_known(v_decl_3732_, 1);
v___x_4310_ = lean_st_ref_get(v_a_3735_);
v_env_4311_ = lean_ctor_get(v___x_4310_, 0);
lean_inc_ref(v_env_4311_);
lean_dec(v___x_4310_);
v___f_4312_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed), 7, 2);
lean_closure_set(v___f_4312_, 0, v_val_4309_);
lean_closure_set(v___f_4312_, 1, v___f_4308_);
v___x_4313_ = lean_box(v___x_4285_);
lean_inc_ref(v___f_4312_);
v___f_4314_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed), 7, 3);
lean_closure_set(v___f_4314_, 0, v_val_4309_);
lean_closure_set(v___f_4314_, 1, v___x_4313_);
lean_closure_set(v___f_4314_, 2, v___f_4312_);
if (v_forceExpose_3733_ == 0)
{
v___y_4257_ = v___f_4314_;
v___y_4258_ = v___x_4286_;
v___y_4259_ = v___f_4312_;
v___y_4260_ = v___x_4305_;
v___y_4261_ = v_val_4309_;
v___y_4262_ = v_a_4280_;
v___y_4263_ = v_env_4311_;
goto v___jp_4256_;
}
else
{
if (v___x_4285_ == 0)
{
lean_dec_ref(v___f_4314_);
lean_dec_ref(v_env_4311_);
lean_dec_ref(v_val_4309_);
v___y_4250_ = v___x_4286_;
v___y_4251_ = v___f_4312_;
v___y_4252_ = v___x_4305_;
v___y_4253_ = v_a_4280_;
goto v___jp_4249_;
}
else
{
v___y_4257_ = v___f_4314_;
v___y_4258_ = v___x_4286_;
v___y_4259_ = v___f_4312_;
v___y_4260_ = v___x_4305_;
v___y_4261_ = v_val_4309_;
v___y_4262_ = v_a_4280_;
v___y_4263_ = v_env_4311_;
goto v___jp_4256_;
}
}
}
case 1:
{
lean_object* v_val_4315_; lean_object* v___x_4316_; 
lean_del_object(v___x_4282_);
v_val_4315_ = lean_ctor_get(v_decl_3732_, 0);
lean_inc_ref(v_val_4315_);
lean_dec_ref_known(v_decl_3732_, 1);
v___x_4316_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v___f_4308_, v_cls_3927_, v___x_4305_, v___x_4285_, v_forceExpose_3733_, v_val_4315_, v_a_3734_, v_a_3735_);
v___y_4193_ = v___x_4286_;
v___y_4194_ = v_a_4280_;
v___y_4195_ = v___x_4316_;
goto v___jp_4192_;
}
case 5:
{
lean_object* v_defns_4317_; 
lean_del_object(v___x_4282_);
v_defns_4317_ = lean_ctor_get(v_decl_3732_, 0);
if (lean_obj_tag(v_defns_4317_) == 1)
{
lean_object* v_tail_4318_; 
v_tail_4318_ = lean_ctor_get(v_defns_4317_, 1);
if (lean_obj_tag(v_tail_4318_) == 0)
{
lean_object* v_head_4319_; lean_object* v___x_4320_; 
lean_inc_ref(v_defns_4317_);
lean_dec_ref_known(v_decl_3732_, 1);
v_head_4319_ = lean_ctor_get(v_defns_4317_, 0);
lean_inc(v_head_4319_);
lean_dec_ref_known(v_defns_4317_, 2);
v___x_4320_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v___f_4308_, v_cls_3927_, v___x_4305_, v___x_4285_, v_forceExpose_3733_, v_head_4319_, v_a_3734_, v_a_3735_);
v___y_4193_ = v___x_4286_;
v___y_4194_ = v_a_4280_;
v___y_4195_ = v___x_4320_;
goto v___jp_4192_;
}
else
{
lean_object* v___x_4321_; 
lean_dec_ref(v___f_4308_);
lean_inc_ref(v_decl_3732_);
v___x_4321_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3732_, v_cls_3927_, v_decl_3732_, v_a_3734_, v_a_3735_);
lean_dec_ref_known(v_decl_3732_, 1);
v___y_4193_ = v___x_4286_;
v___y_4194_ = v_a_4280_;
v___y_4195_ = v___x_4321_;
goto v___jp_4192_;
}
}
else
{
lean_object* v___x_4322_; 
lean_dec_ref(v___f_4308_);
lean_inc_ref(v_decl_3732_);
v___x_4322_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3732_, v_cls_3927_, v_decl_3732_, v_a_3734_, v_a_3735_);
lean_dec_ref_known(v_decl_3732_, 1);
v___y_4193_ = v___x_4286_;
v___y_4194_ = v_a_4280_;
v___y_4195_ = v___x_4322_;
goto v___jp_4192_;
}
}
case 3:
{
lean_object* v_val_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v_env_4326_; lean_object* v_env_4327_; lean_object* v___f_4328_; lean_object* v___f_4329_; 
lean_del_object(v___x_4282_);
v_val_4323_ = lean_ctor_get(v_decl_3732_, 0);
lean_inc_ref_n(v_val_4323_, 3);
lean_dec_ref_known(v_decl_3732_, 1);
v___x_4324_ = lean_st_ref_get(v_a_3735_);
v___x_4325_ = lean_st_ref_get(v_a_3735_);
v_env_4326_ = lean_ctor_get(v___x_4324_, 0);
lean_inc_ref(v_env_4326_);
lean_dec(v___x_4324_);
v_env_4327_ = lean_ctor_get(v___x_4325_, 0);
lean_inc_ref(v_env_4327_);
lean_dec(v___x_4325_);
v___f_4328_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed), 7, 2);
lean_closure_set(v___f_4328_, 0, v_val_4323_);
lean_closure_set(v___f_4328_, 1, v___f_4308_);
lean_inc_ref(v___f_4328_);
v___f_4329_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed), 6, 2);
lean_closure_set(v___f_4329_, 0, v_val_4323_);
lean_closure_set(v___f_4329_, 1, v___f_4328_);
if (v_forceExpose_3733_ == 0)
{
v___y_4237_ = v___x_4286_;
v___y_4238_ = v_env_4327_;
v___y_4239_ = v___x_4285_;
v___y_4240_ = v___f_4328_;
v___y_4241_ = v_env_4326_;
v___y_4242_ = v___x_4305_;
v___y_4243_ = v___f_4329_;
v___y_4244_ = v_val_4323_;
v___y_4245_ = v_a_4280_;
goto v___jp_4236_;
}
else
{
if (v___x_4285_ == 0)
{
lean_dec_ref(v___f_4329_);
lean_dec_ref(v_env_4327_);
lean_dec_ref(v_env_4326_);
lean_dec_ref(v_val_4323_);
v___y_4213_ = v___x_4286_;
v___y_4214_ = v___f_4328_;
v___y_4215_ = v___x_4305_;
v___y_4216_ = v_a_4280_;
goto v___jp_4212_;
}
else
{
v___y_4237_ = v___x_4286_;
v___y_4238_ = v_env_4327_;
v___y_4239_ = v___x_4285_;
v___y_4240_ = v___f_4328_;
v___y_4241_ = v_env_4326_;
v___y_4242_ = v___x_4305_;
v___y_4243_ = v___f_4329_;
v___y_4244_ = v_val_4323_;
v___y_4245_ = v_a_4280_;
goto v___jp_4236_;
}
}
}
case 0:
{
lean_object* v_val_4330_; lean_object* v_toConstantVal_4331_; lean_object* v_name_4332_; lean_object* v___x_4334_; 
lean_dec_ref(v___f_4308_);
v_val_4330_ = lean_ctor_get(v_decl_3732_, 0);
v_toConstantVal_4331_ = lean_ctor_get(v_val_4330_, 0);
v_name_4332_ = lean_ctor_get(v_toConstantVal_4331_, 0);
lean_inc_ref(v_val_4330_);
if (v_isShared_4283_ == 0)
{
lean_ctor_set(v___x_4282_, 0, v_val_4330_);
v___x_4334_ = v___x_4282_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_val_4330_);
v___x_4334_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
uint8_t v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; 
v___x_4335_ = 2;
v___x_4336_ = lean_box(v___x_4335_);
v___x_4337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4337_, 0, v___x_4334_);
lean_ctor_set(v___x_4337_, 1, v___x_4336_);
lean_inc(v_name_4332_);
v___x_4338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4338_, 0, v_name_4332_);
lean_ctor_set(v___x_4338_, 1, v___x_4337_);
v___x_4339_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(v_decl_3732_, v_hasTrace_3791_, v___x_4285_, v___x_4301_, v_cls_3927_, v___x_4305_, v___x_4338_, v___x_4305_, v_a_3734_, v_a_3735_);
v___y_4193_ = v___x_4286_;
v___y_4194_ = v_a_4280_;
v___y_4195_ = v___x_4339_;
goto v___jp_4192_;
}
}
default: 
{
lean_object* v___x_4341_; 
lean_dec_ref(v___f_4308_);
lean_del_object(v___x_4282_);
lean_inc(v_decl_3732_);
v___x_4341_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3732_, v_cls_3927_, v_decl_3732_, v_a_3734_, v_a_3735_);
lean_dec(v_decl_3732_);
v___y_4193_ = v___x_4286_;
v___y_4194_ = v_a_4280_;
v___y_4195_ = v___x_4341_;
goto v___jp_4192_;
}
}
}
}
}
else
{
lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v_env_4347_; lean_object* v_nextMacroScope_4348_; lean_object* v_ngen_4349_; lean_object* v_auxDeclNGen_4350_; lean_object* v_traceState_4351_; lean_object* v_messages_4352_; lean_object* v_infoState_4353_; lean_object* v_snapshotTasks_4354_; lean_object* v___x_4356_; uint8_t v_isShared_4357_; uint8_t v_isSharedCheck_4427_; 
v___x_4345_ = lean_io_get_num_heartbeats();
v___x_4346_ = lean_st_ref_take(v_a_3735_);
v_env_4347_ = lean_ctor_get(v___x_4346_, 0);
v_nextMacroScope_4348_ = lean_ctor_get(v___x_4346_, 1);
v_ngen_4349_ = lean_ctor_get(v___x_4346_, 2);
v_auxDeclNGen_4350_ = lean_ctor_get(v___x_4346_, 3);
v_traceState_4351_ = lean_ctor_get(v___x_4346_, 4);
v_messages_4352_ = lean_ctor_get(v___x_4346_, 6);
v_infoState_4353_ = lean_ctor_get(v___x_4346_, 7);
v_snapshotTasks_4354_ = lean_ctor_get(v___x_4346_, 8);
v_isSharedCheck_4427_ = !lean_is_exclusive(v___x_4346_);
if (v_isSharedCheck_4427_ == 0)
{
lean_object* v_unused_4428_; 
v_unused_4428_ = lean_ctor_get(v___x_4346_, 5);
lean_dec(v_unused_4428_);
v___x_4356_ = v___x_4346_;
v_isShared_4357_ = v_isSharedCheck_4427_;
goto v_resetjp_4355_;
}
else
{
lean_inc(v_snapshotTasks_4354_);
lean_inc(v_infoState_4353_);
lean_inc(v_messages_4352_);
lean_inc(v_traceState_4351_);
lean_inc(v_auxDeclNGen_4350_);
lean_inc(v_ngen_4349_);
lean_inc(v_nextMacroScope_4348_);
lean_inc(v_env_4347_);
lean_dec(v___x_4346_);
v___x_4356_ = lean_box(0);
v_isShared_4357_ = v_isSharedCheck_4427_;
goto v_resetjp_4355_;
}
v_resetjp_4355_:
{
lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4362_; 
lean_inc(v_decl_3732_);
v___x_4358_ = l_Lean_Declaration_getNames(v_decl_3732_);
v___x_4359_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4347_, v___x_4358_);
v___x_4360_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4357_ == 0)
{
lean_ctor_set(v___x_4356_, 5, v___x_4360_);
lean_ctor_set(v___x_4356_, 0, v___x_4359_);
v___x_4362_ = v___x_4356_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v___x_4359_);
lean_ctor_set(v_reuseFailAlloc_4426_, 1, v_nextMacroScope_4348_);
lean_ctor_set(v_reuseFailAlloc_4426_, 2, v_ngen_4349_);
lean_ctor_set(v_reuseFailAlloc_4426_, 3, v_auxDeclNGen_4350_);
lean_ctor_set(v_reuseFailAlloc_4426_, 4, v_traceState_4351_);
lean_ctor_set(v_reuseFailAlloc_4426_, 5, v___x_4360_);
lean_ctor_set(v_reuseFailAlloc_4426_, 6, v_messages_4352_);
lean_ctor_set(v_reuseFailAlloc_4426_, 7, v_infoState_4353_);
lean_ctor_set(v_reuseFailAlloc_4426_, 8, v_snapshotTasks_4354_);
v___x_4362_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___f_4366_; 
v___x_4363_ = lean_st_ref_set(v_a_3735_, v___x_4362_);
v___x_4364_ = lean_box(0);
v___x_4365_ = lean_box(v___x_4285_);
lean_inc(v_decl_3732_);
v___f_4366_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed), 10, 5);
lean_closure_set(v___f_4366_, 0, v_decl_3732_);
lean_closure_set(v___f_4366_, 1, v___x_4365_);
lean_closure_set(v___f_4366_, 2, v_cls_3927_);
lean_closure_set(v___f_4366_, 3, v___x_4360_);
lean_closure_set(v___f_4366_, 4, v___x_4364_);
switch(lean_obj_tag(v_decl_3732_))
{
case 2:
{
lean_object* v_val_4367_; lean_object* v___x_4368_; lean_object* v_env_4369_; lean_object* v___f_4370_; 
lean_del_object(v___x_4282_);
v_val_4367_ = lean_ctor_get(v_decl_3732_, 0);
lean_inc_ref_n(v_val_4367_, 2);
lean_dec_ref_known(v_decl_3732_, 1);
v___x_4368_ = lean_st_ref_get(v_a_3735_);
v_env_4369_ = lean_ctor_get(v___x_4368_, 0);
lean_inc_ref(v_env_4369_);
lean_dec(v___x_4368_);
v___f_4370_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed), 7, 2);
lean_closure_set(v___f_4370_, 0, v_val_4367_);
lean_closure_set(v___f_4370_, 1, v___f_4366_);
if (v_forceExpose_3733_ == 0)
{
if (v___x_4285_ == 0)
{
lean_dec_ref(v_env_4369_);
lean_dec_ref(v_val_4367_);
v___y_4164_ = v___x_4345_;
v___y_4165_ = v___x_4364_;
v___y_4166_ = v_a_4280_;
v___y_4167_ = v___f_4370_;
goto v___jp_4163_;
}
else
{
lean_object* v___x_4371_; uint8_t v_isModule_4372_; 
v___x_4371_ = l_Lean_Environment_header(v_env_4369_);
lean_dec_ref(v_env_4369_);
v_isModule_4372_ = lean_ctor_get_uint8(v___x_4371_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4371_);
if (v_isModule_4372_ == 0)
{
lean_dec_ref(v_val_4367_);
v___y_4164_ = v___x_4345_;
v___y_4165_ = v___x_4364_;
v___y_4166_ = v_a_4280_;
v___y_4167_ = v___f_4370_;
goto v___jp_4163_;
}
else
{
if (v___x_4130_ == 0)
{
lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4373_ = lean_box(0);
v___x_4374_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(v_val_4367_, v_forceExpose_3733_, v___f_4370_, v___x_4373_, v_a_3734_, v_a_3735_);
lean_dec_ref(v_val_4367_);
v___y_4144_ = v___x_4345_;
v___y_4145_ = v_a_4280_;
v___y_4146_ = v___x_4374_;
goto v___jp_4143_;
}
else
{
lean_object* v_toConstantVal_4375_; lean_object* v_name_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; 
v_toConstantVal_4375_ = lean_ctor_get(v_val_4367_, 0);
v_name_4376_ = lean_ctor_get(v_toConstantVal_4375_, 0);
v___x_4377_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4376_);
v___x_4378_ = l_Lean_MessageData_ofName(v_name_4376_);
v___x_4379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4379_, 0, v___x_4377_);
lean_ctor_set(v___x_4379_, 1, v___x_4378_);
v___x_4380_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4381_, 0, v___x_4379_);
lean_ctor_set(v___x_4381_, 1, v___x_4380_);
v___x_4382_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_4381_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_4382_) == 0)
{
lean_object* v_a_4383_; lean_object* v___x_4384_; 
v_a_4383_ = lean_ctor_get(v___x_4382_, 0);
lean_inc(v_a_4383_);
lean_dec_ref_known(v___x_4382_, 1);
v___x_4384_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(v_val_4367_, v_forceExpose_3733_, v___f_4370_, v_a_4383_, v_a_3734_, v_a_3735_);
lean_dec_ref(v_val_4367_);
v___y_4144_ = v___x_4345_;
v___y_4145_ = v_a_4280_;
v___y_4146_ = v___x_4384_;
goto v___jp_4143_;
}
else
{
lean_dec_ref(v___f_4370_);
lean_dec_ref(v_val_4367_);
v___y_4144_ = v___x_4345_;
v___y_4145_ = v_a_4280_;
v___y_4146_ = v___x_4382_;
goto v___jp_4143_;
}
}
}
}
}
else
{
lean_dec_ref(v_env_4369_);
lean_dec_ref(v_val_4367_);
v___y_4164_ = v___x_4345_;
v___y_4165_ = v___x_4364_;
v___y_4166_ = v_a_4280_;
v___y_4167_ = v___f_4370_;
goto v___jp_4163_;
}
}
case 1:
{
lean_object* v_val_4385_; lean_object* v___x_4386_; 
lean_del_object(v___x_4282_);
v_val_4385_ = lean_ctor_get(v_decl_3732_, 0);
lean_inc_ref(v_val_4385_);
lean_dec_ref_known(v_decl_3732_, 1);
v___x_4386_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v___f_4366_, v_forceExpose_3733_, v___x_4285_, v___x_4364_, v_cls_3927_, v_val_4385_, v_a_3734_, v_a_3735_);
v___y_4144_ = v___x_4345_;
v___y_4145_ = v_a_4280_;
v___y_4146_ = v___x_4386_;
goto v___jp_4143_;
}
case 5:
{
lean_object* v_defns_4387_; 
lean_del_object(v___x_4282_);
v_defns_4387_ = lean_ctor_get(v_decl_3732_, 0);
if (lean_obj_tag(v_defns_4387_) == 1)
{
lean_object* v_tail_4388_; 
v_tail_4388_ = lean_ctor_get(v_defns_4387_, 1);
if (lean_obj_tag(v_tail_4388_) == 0)
{
lean_object* v_head_4389_; lean_object* v___x_4390_; 
lean_inc_ref(v_defns_4387_);
lean_dec_ref_known(v_decl_3732_, 1);
v_head_4389_ = lean_ctor_get(v_defns_4387_, 0);
lean_inc(v_head_4389_);
lean_dec_ref_known(v_defns_4387_, 2);
v___x_4390_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v___f_4366_, v_forceExpose_3733_, v___x_4285_, v___x_4364_, v_cls_3927_, v_head_4389_, v_a_3734_, v_a_3735_);
v___y_4144_ = v___x_4345_;
v___y_4145_ = v_a_4280_;
v___y_4146_ = v___x_4390_;
goto v___jp_4143_;
}
else
{
lean_object* v___x_4391_; 
lean_dec_ref(v___f_4366_);
lean_inc_ref(v_decl_3732_);
v___x_4391_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3732_, v_cls_3927_, v_decl_3732_, v_a_3734_, v_a_3735_);
lean_dec_ref_known(v_decl_3732_, 1);
v___y_4144_ = v___x_4345_;
v___y_4145_ = v_a_4280_;
v___y_4146_ = v___x_4391_;
goto v___jp_4143_;
}
}
else
{
lean_object* v___x_4392_; 
lean_dec_ref(v___f_4366_);
lean_inc_ref(v_decl_3732_);
v___x_4392_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3732_, v_cls_3927_, v_decl_3732_, v_a_3734_, v_a_3735_);
lean_dec_ref_known(v_decl_3732_, 1);
v___y_4144_ = v___x_4345_;
v___y_4145_ = v_a_4280_;
v___y_4146_ = v___x_4392_;
goto v___jp_4143_;
}
}
case 3:
{
lean_object* v_val_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v_env_4396_; lean_object* v_env_4397_; lean_object* v___f_4398_; 
lean_del_object(v___x_4282_);
v_val_4393_ = lean_ctor_get(v_decl_3732_, 0);
lean_inc_ref_n(v_val_4393_, 2);
lean_dec_ref_known(v_decl_3732_, 1);
v___x_4394_ = lean_st_ref_get(v_a_3735_);
v___x_4395_ = lean_st_ref_get(v_a_3735_);
v_env_4396_ = lean_ctor_get(v___x_4394_, 0);
lean_inc_ref(v_env_4396_);
lean_dec(v___x_4394_);
v_env_4397_ = lean_ctor_get(v___x_4395_, 0);
lean_inc_ref(v_env_4397_);
lean_dec(v___x_4395_);
v___f_4398_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed), 7, 2);
lean_closure_set(v___f_4398_, 0, v_val_4393_);
lean_closure_set(v___f_4398_, 1, v___f_4366_);
if (v_forceExpose_3733_ == 0)
{
if (v___x_4285_ == 0)
{
lean_dec_ref(v_env_4397_);
lean_dec_ref(v_env_4396_);
lean_dec_ref(v_val_4393_);
v___y_4171_ = v___f_4398_;
v___y_4172_ = v___x_4345_;
v___y_4173_ = v___x_4364_;
v___y_4174_ = v_a_4280_;
goto v___jp_4170_;
}
else
{
lean_object* v___x_4399_; uint8_t v_isModule_4400_; 
v___x_4399_ = l_Lean_Environment_header(v_env_4396_);
lean_dec_ref(v_env_4396_);
v_isModule_4400_ = lean_ctor_get_uint8(v___x_4399_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4399_);
if (v_isModule_4400_ == 0)
{
lean_dec_ref(v_env_4397_);
lean_dec_ref(v_val_4393_);
v___y_4171_ = v___f_4398_;
v___y_4172_ = v___x_4345_;
v___y_4173_ = v___x_4364_;
v___y_4174_ = v_a_4280_;
goto v___jp_4170_;
}
else
{
uint8_t v_isExporting_4401_; 
v_isExporting_4401_ = lean_ctor_get_uint8(v_env_4397_, sizeof(void*)*8);
lean_dec_ref(v_env_4397_);
if (v_isExporting_4401_ == 0)
{
if (v___x_4130_ == 0)
{
lean_object* v___x_4402_; lean_object* v___x_4403_; 
v___x_4402_ = lean_box(0);
v___x_4403_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_val_4393_, v___f_4398_, v___x_4402_, v_a_3734_, v_a_3735_);
lean_dec_ref(v_val_4393_);
v___y_4144_ = v___x_4345_;
v___y_4145_ = v_a_4280_;
v___y_4146_ = v___x_4403_;
goto v___jp_4143_;
}
else
{
lean_object* v_toConstantVal_4404_; lean_object* v_name_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
v_toConstantVal_4404_ = lean_ctor_get(v_val_4393_, 0);
v_name_4405_ = lean_ctor_get(v_toConstantVal_4404_, 0);
v___x_4406_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4405_);
v___x_4407_ = l_Lean_MessageData_ofName(v_name_4405_);
v___x_4408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4408_, 0, v___x_4406_);
lean_ctor_set(v___x_4408_, 1, v___x_4407_);
v___x_4409_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4410_, 0, v___x_4408_);
lean_ctor_set(v___x_4410_, 1, v___x_4409_);
v___x_4411_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_4410_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_4411_) == 0)
{
lean_object* v_a_4412_; lean_object* v___x_4413_; 
v_a_4412_ = lean_ctor_get(v___x_4411_, 0);
lean_inc(v_a_4412_);
lean_dec_ref_known(v___x_4411_, 1);
v___x_4413_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_val_4393_, v___f_4398_, v_a_4412_, v_a_3734_, v_a_3735_);
lean_dec_ref(v_val_4393_);
v___y_4144_ = v___x_4345_;
v___y_4145_ = v_a_4280_;
v___y_4146_ = v___x_4413_;
goto v___jp_4143_;
}
else
{
lean_dec_ref(v___f_4398_);
lean_dec_ref(v_val_4393_);
v___y_4144_ = v___x_4345_;
v___y_4145_ = v_a_4280_;
v___y_4146_ = v___x_4411_;
goto v___jp_4143_;
}
}
}
else
{
lean_dec_ref(v_val_4393_);
v___y_4171_ = v___f_4398_;
v___y_4172_ = v___x_4345_;
v___y_4173_ = v___x_4364_;
v___y_4174_ = v_a_4280_;
goto v___jp_4170_;
}
}
}
}
else
{
lean_dec_ref(v_env_4397_);
lean_dec_ref(v_env_4396_);
lean_dec_ref(v_val_4393_);
v___y_4171_ = v___f_4398_;
v___y_4172_ = v___x_4345_;
v___y_4173_ = v___x_4364_;
v___y_4174_ = v_a_4280_;
goto v___jp_4170_;
}
}
case 0:
{
lean_object* v_val_4414_; lean_object* v_toConstantVal_4415_; lean_object* v_name_4416_; lean_object* v___x_4418_; 
lean_dec_ref(v___f_4366_);
v_val_4414_ = lean_ctor_get(v_decl_3732_, 0);
v_toConstantVal_4415_ = lean_ctor_get(v_val_4414_, 0);
v_name_4416_ = lean_ctor_get(v_toConstantVal_4415_, 0);
lean_inc_ref(v_val_4414_);
if (v_isShared_4283_ == 0)
{
lean_ctor_set(v___x_4282_, 0, v_val_4414_);
v___x_4418_ = v___x_4282_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v_val_4414_);
v___x_4418_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
uint8_t v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; 
v___x_4419_ = 2;
v___x_4420_ = lean_box(v___x_4419_);
v___x_4421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4421_, 0, v___x_4418_);
lean_ctor_set(v___x_4421_, 1, v___x_4420_);
lean_inc(v_name_4416_);
v___x_4422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4422_, 0, v_name_4416_);
lean_ctor_set(v___x_4422_, 1, v___x_4421_);
v___x_4423_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_decl_3732_, v___x_4285_, v_cls_3927_, v___x_4360_, v___x_4364_, v___x_4422_, v___x_4364_, v_a_3734_, v_a_3735_);
v___y_4144_ = v___x_4345_;
v___y_4145_ = v_a_4280_;
v___y_4146_ = v___x_4423_;
goto v___jp_4143_;
}
}
default: 
{
lean_object* v___x_4425_; 
lean_dec_ref(v___f_4366_);
lean_del_object(v___x_4282_);
lean_inc(v_decl_3732_);
v___x_4425_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3732_, v_cls_3927_, v_decl_3732_, v_a_3734_, v_a_3735_);
lean_dec(v_decl_3732_);
v___y_4144_ = v___x_4345_;
v___y_4145_ = v_a_4280_;
v___y_4146_ = v___x_4425_;
goto v___jp_4143_;
}
}
}
}
}
}
}
}
v___jp_3737_:
{
lean_object* v___x_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
v___x_3741_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3738_, v___y_3739_);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3748_ == 0)
{
lean_object* v_unused_3749_; 
v_unused_3749_ = lean_ctor_get(v___x_3741_, 0);
lean_dec(v_unused_3749_);
v___x_3743_ = v___x_3741_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_dec(v___x_3741_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
lean_ctor_set_tag(v___x_3743_, 1);
lean_ctor_set(v___x_3743_, 0, v_a_3740_);
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3740_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
v___jp_3750_:
{
lean_object* v___x_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3761_; 
v___x_3754_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3751_, v___y_3752_);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3761_ == 0)
{
lean_object* v_unused_3762_; 
v_unused_3762_ = lean_ctor_get(v___x_3754_, 0);
lean_dec(v_unused_3762_);
v___x_3756_ = v___x_3754_;
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
else
{
lean_dec(v___x_3754_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
lean_ctor_set(v___x_3756_, 0, v_a_3753_);
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_a_3753_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
v___jp_3763_:
{
lean_object* v___x_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3774_; 
v___x_3767_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3764_, v___y_3765_);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3774_ == 0)
{
lean_object* v_unused_3775_; 
v_unused_3775_ = lean_ctor_get(v___x_3767_, 0);
lean_dec(v_unused_3775_);
v___x_3769_ = v___x_3767_;
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
else
{
lean_dec(v___x_3767_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3772_; 
if (v_isShared_3770_ == 0)
{
lean_ctor_set(v___x_3769_, 0, v_a_3766_);
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_a_3766_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
v___jp_3776_:
{
lean_object* v___x_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3787_; 
v___x_3780_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3777_, v___y_3778_);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3787_ == 0)
{
lean_object* v_unused_3788_; 
v_unused_3788_ = lean_ctor_get(v___x_3780_, 0);
lean_dec(v_unused_3788_);
v___x_3782_ = v___x_3780_;
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
else
{
lean_dec(v___x_3780_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3785_; 
if (v_isShared_3783_ == 0)
{
lean_ctor_set_tag(v___x_3782_, 1);
lean_ctor_set(v___x_3782_, 0, v_a_3779_);
v___x_3785_ = v___x_3782_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_a_3779_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
v___jp_3792_:
{
lean_object* v___x_3804_; 
lean_inc_ref(v___y_3797_);
v___x_3804_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3798_, v___y_3797_, v___y_3802_, v___y_3803_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v___x_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3851_; 
lean_dec_ref_known(v___x_3804_, 1);
lean_inc_ref(v___y_3793_);
v___x_3805_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3793_, v___y_3801_);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3851_ == 0)
{
lean_object* v_unused_3852_; 
v_unused_3852_ = lean_ctor_get(v___x_3805_, 0);
lean_dec(v_unused_3852_);
v___x_3807_ = v___x_3805_;
v_isShared_3808_ = v_isSharedCheck_3851_;
goto v_resetjp_3806_;
}
else
{
lean_dec(v___x_3805_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3851_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v_options_3809_; lean_object* v___x_3810_; uint8_t v___x_3811_; 
v_options_3809_ = lean_ctor_get(v___y_3794_, 2);
v___x_3810_ = l_Lean_Elab_async;
v___x_3811_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3809_, v___x_3810_);
if (v___x_3811_ == 0)
{
lean_object* v___x_3812_; lean_object* v_r_3813_; 
lean_del_object(v___x_3807_);
lean_dec_ref(v___y_3799_);
lean_dec_ref(v___y_3795_);
v___x_3812_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3797_, v___y_3801_);
lean_dec_ref(v___x_3812_);
v_r_3813_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3732_, v___y_3794_, v___y_3801_);
if (lean_obj_tag(v_r_3813_) == 0)
{
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3823_; 
v_a_3814_ = lean_ctor_get(v_r_3813_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v_r_3813_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3816_ = v_r_3813_;
v_isShared_3817_ = v_isSharedCheck_3823_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v_r_3813_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3823_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
lean_inc(v_a_3814_);
if (v_isShared_3817_ == 0)
{
lean_ctor_set_tag(v___x_3816_, 1);
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_a_3814_);
v___x_3819_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
lean_object* v___x_3820_; 
v___x_3820_ = lean_apply_2(v___y_3800_, v___x_3819_, lean_box(0));
if (lean_obj_tag(v___x_3820_) == 0)
{
lean_dec_ref_known(v___x_3820_, 1);
v___y_3751_ = v___y_3793_;
v___y_3752_ = v___y_3801_;
v_a_3753_ = v_a_3814_;
goto v___jp_3750_;
}
else
{
lean_object* v_a_3821_; 
lean_dec(v_a_3814_);
v_a_3821_ = lean_ctor_get(v___x_3820_, 0);
lean_inc(v_a_3821_);
lean_dec_ref_known(v___x_3820_, 1);
v___y_3738_ = v___y_3793_;
v___y_3739_ = v___y_3801_;
v_a_3740_ = v_a_3821_;
goto v___jp_3737_;
}
}
}
}
else
{
lean_object* v_a_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; 
v_a_3824_ = lean_ctor_get(v_r_3813_, 0);
lean_inc(v_a_3824_);
lean_dec_ref_known(v_r_3813_, 1);
v___x_3825_ = lean_box(0);
v___x_3826_ = lean_apply_2(v___y_3800_, v___x_3825_, lean_box(0));
if (lean_obj_tag(v___x_3826_) == 0)
{
lean_dec_ref_known(v___x_3826_, 1);
v___y_3738_ = v___y_3793_;
v___y_3739_ = v___y_3801_;
v_a_3740_ = v_a_3824_;
goto v___jp_3737_;
}
else
{
lean_object* v_a_3827_; 
lean_dec(v_a_3824_);
v_a_3827_ = lean_ctor_get(v___x_3826_, 0);
lean_inc(v_a_3827_);
lean_dec_ref_known(v___x_3826_, 1);
v___y_3738_ = v___y_3793_;
v___y_3739_ = v___y_3801_;
v_a_3740_ = v_a_3827_;
goto v___jp_3737_;
}
}
}
else
{
lean_object* v___x_3828_; lean_object* v___x_3830_; 
lean_dec_ref(v___y_3800_);
lean_dec_ref(v___y_3797_);
lean_dec_ref(v___y_3793_);
lean_dec(v_decl_3732_);
v___x_3828_ = l_IO_CancelToken_new();
if (v_isShared_3808_ == 0)
{
lean_ctor_set_tag(v___x_3807_, 1);
lean_ctor_set(v___x_3807_, 0, v___x_3828_);
v___x_3830_ = v___x_3807_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v___x_3828_);
v___x_3830_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; 
v___x_3831_ = lean_unsigned_to_nat(0u);
v___x_3832_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_3833_ = l_Lean_Name_toString(v___x_3832_, v___y_3796_);
lean_inc_ref(v___x_3830_);
v___x_3834_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3799_, v___x_3830_, v___x_3833_, v___y_3794_, v___y_3801_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v_a_3835_; lean_object* v_checked_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; 
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
lean_inc(v_a_3835_);
lean_dec_ref_known(v___x_3834_, 1);
v_checked_3836_ = lean_ctor_get(v___y_3795_, 2);
lean_inc_ref(v_checked_3836_);
lean_dec_ref(v___y_3795_);
v___x_3837_ = lean_io_map_task(v_a_3835_, v_checked_3836_, v___x_3831_, v_hasTrace_3791_);
v___x_3838_ = lean_box(0);
v___x_3839_ = lean_box(2);
v___x_3840_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3838_);
lean_ctor_set(v___x_3840_, 1, v___x_3839_);
lean_ctor_set(v___x_3840_, 2, v___x_3830_);
lean_ctor_set(v___x_3840_, 3, v___x_3837_);
v___x_3841_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3840_, v___y_3801_);
return v___x_3841_;
}
else
{
lean_object* v_a_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3849_; 
lean_dec_ref(v___x_3830_);
lean_dec_ref(v___y_3795_);
v_a_3842_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3844_ = v___x_3834_;
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_a_3842_);
lean_dec(v___x_3834_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3847_; 
if (v_isShared_3845_ == 0)
{
v___x_3847_ = v___x_3844_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_a_3842_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3865_; 
lean_dec_ref(v___y_3800_);
lean_dec_ref(v___y_3799_);
lean_dec_ref(v___y_3797_);
lean_dec_ref(v___y_3795_);
lean_dec_ref(v___y_3793_);
lean_dec(v_decl_3732_);
v_a_3853_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3855_ = v___x_3804_;
v_isShared_3856_ = v_isSharedCheck_3865_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3804_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3865_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v_ref_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3863_; 
v_ref_3857_ = lean_ctor_get(v___y_3794_, 5);
v___x_3858_ = lean_io_error_to_string(v_a_3853_);
v___x_3859_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3858_);
v___x_3860_ = l_Lean_MessageData_ofFormat(v___x_3859_);
lean_inc(v_ref_3857_);
v___x_3861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3861_, 0, v_ref_3857_);
lean_ctor_set(v___x_3861_, 1, v___x_3860_);
if (v_isShared_3856_ == 0)
{
lean_ctor_set(v___x_3855_, 0, v___x_3861_);
v___x_3863_ = v___x_3855_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v___x_3861_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
}
v___jp_3866_:
{
uint8_t v___x_3877_; lean_object* v___x_3878_; 
v___x_3877_ = 1;
lean_inc_ref(v___y_3868_);
v___x_3878_ = l_Lean_Environment_addConstAsync(v___y_3868_, v___y_3870_, v___y_3872_, v___y_3876_, v_hasTrace_3791_, v___x_3877_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v_a_3879_; lean_object* v_mainEnv_3880_; lean_object* v_asyncEnv_3881_; lean_object* v___f_3882_; lean_object* v___f_3883_; lean_object* v___x_3884_; 
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
lean_inc_n(v_a_3879_, 3);
lean_dec_ref_known(v___x_3878_, 1);
v_mainEnv_3880_ = lean_ctor_get(v_a_3879_, 0);
lean_inc_ref(v_mainEnv_3880_);
v_asyncEnv_3881_ = lean_ctor_get(v_a_3879_, 1);
lean_inc_ref_n(v_asyncEnv_3881_, 2);
lean_inc_ref(v___y_3867_);
lean_inc(v___y_3869_);
v___f_3882_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3882_, 0, v___y_3869_);
lean_closure_set(v___f_3882_, 1, v_a_3879_);
lean_closure_set(v___f_3882_, 2, v___y_3867_);
lean_inc(v_decl_3732_);
v___f_3883_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3883_, 0, v_asyncEnv_3881_);
lean_closure_set(v___f_3883_, 1, v_a_3879_);
lean_closure_set(v___f_3883_, 2, v_decl_3732_);
v___x_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3884_, 0, v___y_3875_);
if (lean_obj_tag(v___y_3873_) == 0)
{
lean_inc_ref(v___x_3884_);
v___y_3793_ = v_mainEnv_3880_;
v___y_3794_ = v___y_3871_;
v___y_3795_ = v___y_3868_;
v___y_3796_ = v___x_3877_;
v___y_3797_ = v_asyncEnv_3881_;
v___y_3798_ = v_a_3879_;
v___y_3799_ = v___f_3883_;
v___y_3800_ = v___f_3882_;
v___y_3801_ = v___y_3874_;
v___y_3802_ = v___x_3884_;
v___y_3803_ = v___x_3884_;
goto v___jp_3792_;
}
else
{
v___y_3793_ = v_mainEnv_3880_;
v___y_3794_ = v___y_3871_;
v___y_3795_ = v___y_3868_;
v___y_3796_ = v___x_3877_;
v___y_3797_ = v_asyncEnv_3881_;
v___y_3798_ = v_a_3879_;
v___y_3799_ = v___f_3883_;
v___y_3800_ = v___f_3882_;
v___y_3801_ = v___y_3874_;
v___y_3802_ = v___x_3884_;
v___y_3803_ = v___y_3873_;
goto v___jp_3792_;
}
}
else
{
lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3897_; 
lean_dec_ref(v___y_3875_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3868_);
lean_dec(v_decl_3732_);
v_a_3885_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3897_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3887_ = v___x_3878_;
v_isShared_3888_ = v_isSharedCheck_3897_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v___x_3878_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3897_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v_ref_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3895_; 
v_ref_3889_ = lean_ctor_get(v___y_3871_, 5);
v___x_3890_ = lean_io_error_to_string(v_a_3885_);
v___x_3891_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3890_);
v___x_3892_ = l_Lean_MessageData_ofFormat(v___x_3891_);
lean_inc(v_ref_3889_);
v___x_3893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3893_, 0, v_ref_3889_);
lean_ctor_set(v___x_3893_, 1, v___x_3892_);
if (v_isShared_3888_ == 0)
{
lean_ctor_set(v___x_3887_, 0, v___x_3893_);
v___x_3895_ = v___x_3887_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v___x_3893_);
v___x_3895_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
return v___x_3895_;
}
}
}
}
v___jp_3898_:
{
lean_object* v___x_3905_; 
v___x_3905_ = lean_st_ref_get(v___y_3904_);
if (lean_obj_tag(v_exportedInfo_x3f_3902_) == 0)
{
lean_object* v_env_3906_; lean_object* v___x_3907_; 
v_env_3906_ = lean_ctor_get(v___x_3905_, 0);
lean_inc_ref(v_env_3906_);
lean_dec(v___x_3905_);
v___x_3907_ = lean_box(0);
v___y_3867_ = v___y_3903_;
v___y_3868_ = v_env_3906_;
v___y_3869_ = v___y_3904_;
v___y_3870_ = v___y_3899_;
v___y_3871_ = v___y_3903_;
v___y_3872_ = v___y_3900_;
v___y_3873_ = v_exportedInfo_x3f_3902_;
v___y_3874_ = v___y_3904_;
v___y_3875_ = v___y_3901_;
v___y_3876_ = v___x_3907_;
goto v___jp_3866_;
}
else
{
lean_object* v_env_3908_; lean_object* v_val_3909_; uint8_t v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
v_env_3908_ = lean_ctor_get(v___x_3905_, 0);
lean_inc_ref(v_env_3908_);
lean_dec(v___x_3905_);
v_val_3909_ = lean_ctor_get(v_exportedInfo_x3f_3902_, 0);
v___x_3910_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3909_);
v___x_3911_ = lean_box(v___x_3910_);
v___x_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3912_, 0, v___x_3911_);
v___y_3867_ = v___y_3903_;
v___y_3868_ = v_env_3908_;
v___y_3869_ = v___y_3904_;
v___y_3870_ = v___y_3899_;
v___y_3871_ = v___y_3903_;
v___y_3872_ = v___y_3900_;
v___y_3873_ = v_exportedInfo_x3f_3902_;
v___y_3874_ = v___y_3904_;
v___y_3875_ = v___y_3901_;
v___y_3876_ = v___x_3912_;
goto v___jp_3866_;
}
}
v___jp_3913_:
{
lean_object* v___x_3919_; 
lean_inc_ref(v___y_3916_);
v___x_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3919_, 0, v___y_3916_);
v___y_3899_ = v___y_3914_;
v___y_3900_ = v___y_3915_;
v___y_3901_ = v___y_3916_;
v_exportedInfo_x3f_3902_ = v___x_3919_;
v___y_3903_ = v___y_3917_;
v___y_3904_ = v___y_3918_;
goto v___jp_3898_;
}
v___jp_3920_:
{
lean_object* v___x_3926_; 
lean_inc_ref(v___y_3923_);
v___x_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3926_, 0, v___y_3923_);
v___y_3899_ = v___y_3921_;
v___y_3900_ = v___y_3922_;
v___y_3901_ = v___y_3923_;
v_exportedInfo_x3f_3902_ = v___x_3926_;
v___y_3903_ = v___y_3924_;
v___y_3904_ = v___y_3925_;
goto v___jp_3898_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___boxed(lean_object* v_decl_4811_, lean_object* v_forceExpose_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_){
_start:
{
uint8_t v_forceExpose_boxed_4816_; lean_object* v_res_4817_; 
v_forceExpose_boxed_4816_ = lean_unbox(v_forceExpose_4812_);
v_res_4817_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4811_, v_forceExpose_boxed_4816_, v_a_4813_, v_a_4814_);
lean_dec(v_a_4814_);
lean_dec_ref(v_a_4813_);
return v_res_4817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(lean_object* v_opt_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_){
_start:
{
lean_object* v___x_4822_; 
v___x_4822_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_4818_, v___y_4819_);
return v___x_4822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___boxed(lean_object* v_opt_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_){
_start:
{
lean_object* v_res_4827_; 
v_res_4827_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(v_opt_4823_, v___y_4824_, v___y_4825_);
lean_dec(v___y_4825_);
lean_dec_ref(v___y_4824_);
lean_dec_ref(v_opt_4823_);
return v_res_4827_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0(lean_object* v_x_4828_, lean_object* v_x_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_){
_start:
{
if (lean_obj_tag(v_x_4828_) == 0)
{
lean_object* v___x_4833_; lean_object* v___x_4834_; 
v___x_4833_ = l_List_reverse___redArg(v_x_4829_);
v___x_4834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4834_, 0, v___x_4833_);
return v___x_4834_;
}
else
{
lean_object* v_head_4835_; lean_object* v_tail_4836_; lean_object* v___x_4838_; uint8_t v_isShared_4839_; uint8_t v_isSharedCheck_4854_; 
v_head_4835_ = lean_ctor_get(v_x_4828_, 0);
v_tail_4836_ = lean_ctor_get(v_x_4828_, 1);
v_isSharedCheck_4854_ = !lean_is_exclusive(v_x_4828_);
if (v_isSharedCheck_4854_ == 0)
{
v___x_4838_ = v_x_4828_;
v_isShared_4839_ = v_isSharedCheck_4854_;
goto v_resetjp_4837_;
}
else
{
lean_inc(v_tail_4836_);
lean_inc(v_head_4835_);
lean_dec(v_x_4828_);
v___x_4838_ = lean_box(0);
v_isShared_4839_ = v_isSharedCheck_4854_;
goto v_resetjp_4837_;
}
v_resetjp_4837_:
{
lean_object* v___x_4840_; 
v___x_4840_ = l_Lean_snapshotEnvLinterOptions(v_head_4835_, v___y_4830_, v___y_4831_);
if (lean_obj_tag(v___x_4840_) == 0)
{
lean_object* v_a_4841_; lean_object* v___x_4843_; 
v_a_4841_ = lean_ctor_get(v___x_4840_, 0);
lean_inc(v_a_4841_);
lean_dec_ref_known(v___x_4840_, 1);
if (v_isShared_4839_ == 0)
{
lean_ctor_set(v___x_4838_, 1, v_x_4829_);
lean_ctor_set(v___x_4838_, 0, v_a_4841_);
v___x_4843_ = v___x_4838_;
goto v_reusejp_4842_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v_a_4841_);
lean_ctor_set(v_reuseFailAlloc_4845_, 1, v_x_4829_);
v___x_4843_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4842_;
}
v_reusejp_4842_:
{
v_x_4828_ = v_tail_4836_;
v_x_4829_ = v___x_4843_;
goto _start;
}
}
else
{
lean_object* v_a_4846_; lean_object* v___x_4848_; uint8_t v_isShared_4849_; uint8_t v_isSharedCheck_4853_; 
lean_del_object(v___x_4838_);
lean_dec(v_tail_4836_);
lean_dec(v_x_4829_);
v_a_4846_ = lean_ctor_get(v___x_4840_, 0);
v_isSharedCheck_4853_ = !lean_is_exclusive(v___x_4840_);
if (v_isSharedCheck_4853_ == 0)
{
v___x_4848_ = v___x_4840_;
v_isShared_4849_ = v_isSharedCheck_4853_;
goto v_resetjp_4847_;
}
else
{
lean_inc(v_a_4846_);
lean_dec(v___x_4840_);
v___x_4848_ = lean_box(0);
v_isShared_4849_ = v_isSharedCheck_4853_;
goto v_resetjp_4847_;
}
v_resetjp_4847_:
{
lean_object* v___x_4851_; 
if (v_isShared_4849_ == 0)
{
v___x_4851_ = v___x_4848_;
goto v_reusejp_4850_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v_a_4846_);
v___x_4851_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4850_;
}
v_reusejp_4850_:
{
return v___x_4851_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0___boxed(lean_object* v_x_4855_, lean_object* v_x_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_){
_start:
{
lean_object* v_res_4860_; 
v_res_4860_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v_x_4855_, v_x_4856_, v___y_4857_, v___y_4858_);
lean_dec(v___y_4858_);
lean_dec_ref(v___y_4857_);
return v_res_4860_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object* v_decl_4861_, uint8_t v_forceExpose_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_){
_start:
{
lean_object* v___x_4866_; 
lean_inc(v_decl_4861_);
v___x_4866_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4861_, v_forceExpose_4862_, v_a_4863_, v_a_4864_);
if (lean_obj_tag(v___x_4866_) == 0)
{
lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; 
lean_dec_ref_known(v___x_4866_, 1);
v___x_4867_ = l_Lean_Declaration_getTopLevelNames(v_decl_4861_);
v___x_4868_ = lean_box(0);
v___x_4869_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v___x_4867_, v___x_4868_, v_a_4863_, v_a_4864_);
if (lean_obj_tag(v___x_4869_) == 0)
{
lean_object* v___x_4871_; uint8_t v_isShared_4872_; uint8_t v_isSharedCheck_4877_; 
v_isSharedCheck_4877_ = !lean_is_exclusive(v___x_4869_);
if (v_isSharedCheck_4877_ == 0)
{
lean_object* v_unused_4878_; 
v_unused_4878_ = lean_ctor_get(v___x_4869_, 0);
lean_dec(v_unused_4878_);
v___x_4871_ = v___x_4869_;
v_isShared_4872_ = v_isSharedCheck_4877_;
goto v_resetjp_4870_;
}
else
{
lean_dec(v___x_4869_);
v___x_4871_ = lean_box(0);
v_isShared_4872_ = v_isSharedCheck_4877_;
goto v_resetjp_4870_;
}
v_resetjp_4870_:
{
lean_object* v___x_4873_; lean_object* v___x_4875_; 
v___x_4873_ = lean_box(0);
if (v_isShared_4872_ == 0)
{
lean_ctor_set(v___x_4871_, 0, v___x_4873_);
v___x_4875_ = v___x_4871_;
goto v_reusejp_4874_;
}
else
{
lean_object* v_reuseFailAlloc_4876_; 
v_reuseFailAlloc_4876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4876_, 0, v___x_4873_);
v___x_4875_ = v_reuseFailAlloc_4876_;
goto v_reusejp_4874_;
}
v_reusejp_4874_:
{
return v___x_4875_;
}
}
}
else
{
lean_object* v_a_4879_; lean_object* v___x_4881_; uint8_t v_isShared_4882_; uint8_t v_isSharedCheck_4886_; 
v_a_4879_ = lean_ctor_get(v___x_4869_, 0);
v_isSharedCheck_4886_ = !lean_is_exclusive(v___x_4869_);
if (v_isSharedCheck_4886_ == 0)
{
v___x_4881_ = v___x_4869_;
v_isShared_4882_ = v_isSharedCheck_4886_;
goto v_resetjp_4880_;
}
else
{
lean_inc(v_a_4879_);
lean_dec(v___x_4869_);
v___x_4881_ = lean_box(0);
v_isShared_4882_ = v_isSharedCheck_4886_;
goto v_resetjp_4880_;
}
v_resetjp_4880_:
{
lean_object* v___x_4884_; 
if (v_isShared_4882_ == 0)
{
v___x_4884_ = v___x_4881_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v_a_4879_);
v___x_4884_ = v_reuseFailAlloc_4885_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
return v___x_4884_;
}
}
}
}
else
{
lean_dec(v_decl_4861_);
return v___x_4866_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___boxed(lean_object* v_decl_4887_, lean_object* v_forceExpose_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_){
_start:
{
uint8_t v_forceExpose_boxed_4892_; lean_object* v_res_4893_; 
v_forceExpose_boxed_4892_ = lean_unbox(v_forceExpose_4888_);
v_res_4893_ = l_Lean_addDecl(v_decl_4887_, v_forceExpose_boxed_4892_, v_a_4889_, v_a_4890_);
lean_dec(v_a_4890_);
lean_dec_ref(v_a_4889_);
return v_res_4893_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(lean_object* v_as_x27_4894_, lean_object* v_b_4895_, lean_object* v___y_4896_){
_start:
{
if (lean_obj_tag(v_as_x27_4894_) == 0)
{
lean_object* v___x_4898_; 
v___x_4898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4898_, 0, v_b_4895_);
return v___x_4898_;
}
else
{
lean_object* v_head_4899_; lean_object* v_tail_4900_; lean_object* v___x_4901_; lean_object* v_env_4902_; lean_object* v_nextMacroScope_4903_; lean_object* v_ngen_4904_; lean_object* v_auxDeclNGen_4905_; lean_object* v_traceState_4906_; lean_object* v_messages_4907_; lean_object* v_infoState_4908_; lean_object* v_snapshotTasks_4909_; lean_object* v___x_4911_; uint8_t v_isShared_4912_; uint8_t v_isSharedCheck_4921_; 
v_head_4899_ = lean_ctor_get(v_as_x27_4894_, 0);
v_tail_4900_ = lean_ctor_get(v_as_x27_4894_, 1);
v___x_4901_ = lean_st_ref_take(v___y_4896_);
v_env_4902_ = lean_ctor_get(v___x_4901_, 0);
v_nextMacroScope_4903_ = lean_ctor_get(v___x_4901_, 1);
v_ngen_4904_ = lean_ctor_get(v___x_4901_, 2);
v_auxDeclNGen_4905_ = lean_ctor_get(v___x_4901_, 3);
v_traceState_4906_ = lean_ctor_get(v___x_4901_, 4);
v_messages_4907_ = lean_ctor_get(v___x_4901_, 6);
v_infoState_4908_ = lean_ctor_get(v___x_4901_, 7);
v_snapshotTasks_4909_ = lean_ctor_get(v___x_4901_, 8);
v_isSharedCheck_4921_ = !lean_is_exclusive(v___x_4901_);
if (v_isSharedCheck_4921_ == 0)
{
lean_object* v_unused_4922_; 
v_unused_4922_ = lean_ctor_get(v___x_4901_, 5);
lean_dec(v_unused_4922_);
v___x_4911_ = v___x_4901_;
v_isShared_4912_ = v_isSharedCheck_4921_;
goto v_resetjp_4910_;
}
else
{
lean_inc(v_snapshotTasks_4909_);
lean_inc(v_infoState_4908_);
lean_inc(v_messages_4907_);
lean_inc(v_traceState_4906_);
lean_inc(v_auxDeclNGen_4905_);
lean_inc(v_ngen_4904_);
lean_inc(v_nextMacroScope_4903_);
lean_inc(v_env_4902_);
lean_dec(v___x_4901_);
v___x_4911_ = lean_box(0);
v_isShared_4912_ = v_isSharedCheck_4921_;
goto v_resetjp_4910_;
}
v_resetjp_4910_:
{
lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4916_; 
lean_inc(v_head_4899_);
v___x_4913_ = l_Lean_markMeta(v_env_4902_, v_head_4899_);
v___x_4914_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4912_ == 0)
{
lean_ctor_set(v___x_4911_, 5, v___x_4914_);
lean_ctor_set(v___x_4911_, 0, v___x_4913_);
v___x_4916_ = v___x_4911_;
goto v_reusejp_4915_;
}
else
{
lean_object* v_reuseFailAlloc_4920_; 
v_reuseFailAlloc_4920_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4920_, 0, v___x_4913_);
lean_ctor_set(v_reuseFailAlloc_4920_, 1, v_nextMacroScope_4903_);
lean_ctor_set(v_reuseFailAlloc_4920_, 2, v_ngen_4904_);
lean_ctor_set(v_reuseFailAlloc_4920_, 3, v_auxDeclNGen_4905_);
lean_ctor_set(v_reuseFailAlloc_4920_, 4, v_traceState_4906_);
lean_ctor_set(v_reuseFailAlloc_4920_, 5, v___x_4914_);
lean_ctor_set(v_reuseFailAlloc_4920_, 6, v_messages_4907_);
lean_ctor_set(v_reuseFailAlloc_4920_, 7, v_infoState_4908_);
lean_ctor_set(v_reuseFailAlloc_4920_, 8, v_snapshotTasks_4909_);
v___x_4916_ = v_reuseFailAlloc_4920_;
goto v_reusejp_4915_;
}
v_reusejp_4915_:
{
lean_object* v___x_4917_; lean_object* v___x_4918_; 
v___x_4917_ = lean_st_ref_set(v___y_4896_, v___x_4916_);
v___x_4918_ = lean_box(0);
v_as_x27_4894_ = v_tail_4900_;
v_b_4895_ = v___x_4918_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg___boxed(lean_object* v_as_x27_4923_, lean_object* v_b_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_){
_start:
{
lean_object* v_res_4927_; 
v_res_4927_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_4923_, v_b_4924_, v___y_4925_);
lean_dec(v___y_4925_);
lean_dec(v_as_x27_4923_);
return v_res_4927_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object* v_decl_4928_, uint8_t v_logCompileErrors_4929_, uint8_t v_markMeta_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_){
_start:
{
uint8_t v___x_4934_; lean_object* v___x_4935_; 
v___x_4934_ = 0;
lean_inc(v_decl_4928_);
v___x_4935_ = l_Lean_addDecl(v_decl_4928_, v___x_4934_, v_a_4931_, v_a_4932_);
if (lean_obj_tag(v___x_4935_) == 0)
{
lean_dec_ref_known(v___x_4935_, 1);
if (v_markMeta_4930_ == 0)
{
lean_object* v___x_4936_; 
v___x_4936_ = l_Lean_compileDecl(v_decl_4928_, v_logCompileErrors_4929_, v_a_4931_, v_a_4932_);
return v___x_4936_;
}
else
{
lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; 
lean_inc(v_decl_4928_);
v___x_4937_ = l_Lean_Declaration_getNames(v_decl_4928_);
v___x_4938_ = lean_box(0);
v___x_4939_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v___x_4937_, v___x_4938_, v_a_4932_);
lean_dec(v___x_4937_);
lean_dec_ref(v___x_4939_);
v___x_4940_ = l_Lean_compileDecl(v_decl_4928_, v_logCompileErrors_4929_, v_a_4931_, v_a_4932_);
return v___x_4940_;
}
}
else
{
lean_dec(v_decl_4928_);
return v___x_4935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___boxed(lean_object* v_decl_4941_, lean_object* v_logCompileErrors_4942_, lean_object* v_markMeta_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_){
_start:
{
uint8_t v_logCompileErrors_boxed_4947_; uint8_t v_markMeta_boxed_4948_; lean_object* v_res_4949_; 
v_logCompileErrors_boxed_4947_ = lean_unbox(v_logCompileErrors_4942_);
v_markMeta_boxed_4948_ = lean_unbox(v_markMeta_4943_);
v_res_4949_ = l_Lean_addAndCompile(v_decl_4941_, v_logCompileErrors_boxed_4947_, v_markMeta_boxed_4948_, v_a_4944_, v_a_4945_);
lean_dec(v_a_4945_);
lean_dec_ref(v_a_4944_);
return v_res_4949_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(lean_object* v_as_4950_, lean_object* v_as_x27_4951_, lean_object* v_b_4952_, lean_object* v_a_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_){
_start:
{
lean_object* v___x_4957_; 
v___x_4957_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_4951_, v_b_4952_, v___y_4955_);
return v___x_4957_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___boxed(lean_object* v_as_4958_, lean_object* v_as_x27_4959_, lean_object* v_b_4960_, lean_object* v_a_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_){
_start:
{
lean_object* v_res_4965_; 
v_res_4965_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(v_as_4958_, v_as_x27_4959_, v_b_4960_, v_a_4961_, v___y_4962_, v___y_4963_);
lean_dec(v___y_4963_);
lean_dec_ref(v___y_4962_);
lean_dec(v_as_x27_4959_);
lean_dec(v_as_4958_);
return v_res_4965_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sorry(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectAxioms(uint8_t builtin);
lean_object* runtime_initialize_Lean_OriginalConstKind(uint8_t builtin);
lean_object* runtime_initialize_Lean_AutoDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Init(uint8_t builtin);
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
res = runtime_initialize_Lean_AutoDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Init(builtin);
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
lean_object* initialize_Lean_AutoDecl(uint8_t builtin);
lean_object* initialize_Lean_Linter_Init(uint8_t builtin);
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
res = initialize_Lean_AutoDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Init(builtin);
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
