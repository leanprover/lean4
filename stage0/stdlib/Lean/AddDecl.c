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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Declaration_getTopLevelNames(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Declaration_getNames(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
extern lean_object* l_Lean_debug_skipKernelTC;
lean_object* l_Lean_Environment_addDeclCore(lean_object*, size_t, size_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t l_Lean_Expr_isSyntheticSorry(lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
uint8_t l_Lean_Declaration_hasSorry(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
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
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Environment_registerNamespace(lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
uint8_t l_Lean_instBEqDefinitionSafety_beq(uint8_t, uint8_t);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_AddConstAsyncResult_commitConst(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_async;
lean_object* l_IO_CancelToken_new();
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Core_logSnapshotTask___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_addConstAsync(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t);
uint8_t l_Lean_ConstantKind_ofConstantInfo(lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
extern lean_object* l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic;
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
lean_object* lean_elab_environment_to_kernel_env(lean_object*);
lean_object* lean_add_decl(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_add_decl_without_checking(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_envLinterOptionsRef;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_warnIfUsesSorry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_warnIfUsesSorry___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_warnIfUsesSorry___closed__0 = (const lean_object*)&l_Lean_warnIfUsesSorry___closed__0_value;
static const lean_array_object l_Lean_warnIfUsesSorry___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_warnIfUsesSorry___closed__1 = (const lean_object*)&l_Lean_warnIfUsesSorry___closed__1_value;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__2;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__3;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__4;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__5;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__6;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__7;
static const lean_string_object l_Lean_warnIfUsesSorry___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "hasSorry"};
static const lean_object* l_Lean_warnIfUsesSorry___closed__8 = (const lean_object*)&l_Lean_warnIfUsesSorry___closed__8_value;
static const lean_ctor_object l_Lean_warnIfUsesSorry___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_warnIfUsesSorry___closed__8_value),LEAN_SCALAR_PTR_LITERAL(111, 250, 94, 52, 248, 92, 138, 251)}};
static const lean_object* l_Lean_warnIfUsesSorry___closed__9 = (const lean_object*)&l_Lean_warnIfUsesSorry___closed__9_value;
static const lean_string_object l_Lean_warnIfUsesSorry___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "declaration uses `"};
static const lean_object* l_Lean_warnIfUsesSorry___closed__10 = (const lean_object*)&l_Lean_warnIfUsesSorry___closed__10_value;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__11;
static const lean_string_object l_Lean_warnIfUsesSorry___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_warnIfUsesSorry___closed__12 = (const lean_object*)&l_Lean_warnIfUsesSorry___closed__12_value;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__13;
static const lean_string_object l_Lean_warnIfUsesSorry___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "declaration uses `sorry`"};
static const lean_object* l_Lean_warnIfUsesSorry___closed__14 = (const lean_object*)&l_Lean_warnIfUsesSorry___closed__14_value;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__15;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__16;
static const lean_ctor_object l_Lean_warnIfUsesSorry___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_warnIfUsesSorry___closed__17 = (const lean_object*)&l_Lean_warnIfUsesSorry___closed__17_value;
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
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "sorryAx"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(196, 190, 164, 146, 38, 179, 69, 72)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "adding declarations "};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__0 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__0_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "no matching async adding rules, adding synchronously"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__0 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__0_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2___boxed(lean_object*);
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "addDeclCore"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__0 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__0_value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__8_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 15, 132, 113, 234, 47, 152, 164)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1_value;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "no matching exporting rules, exporting as is"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__2 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__2_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "not exporting private declaration at all"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__4 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__4_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "private decl under `privateInPublic`, exporting as is"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__6 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__6_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "exporting definition "};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__0 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__0_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " as axiom"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__2 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__2_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "exporting theorem "};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "exporting opaque "};
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
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v_env_94_; lean_object* v___x_95_; lean_object* v_toEnvExtension_96_; lean_object* v_asyncMode_97_; lean_object* v___x_98_; uint8_t v___x_99_; lean_object* v___x_100_; lean_object* v_merged_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_109_; 
v___x_92_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_93_ = lean_st_ref_get(v___y_90_);
v_env_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc_ref(v_env_94_);
lean_dec(v___x_93_);
v___x_95_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_96_ = lean_ctor_get(v___x_95_, 0);
v_asyncMode_97_ = lean_ctor_get(v_toEnvExtension_96_, 2);
v___x_98_ = lean_box(0);
v___x_99_ = 0;
v___x_100_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_92_, v___x_95_, v_env_94_, v_asyncMode_97_, v___x_98_, v___x_99_);
v_merged_101_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_109_ == 0)
{
lean_object* v_unused_110_; 
v_unused_110_ = lean_ctor_get(v___x_100_, 1);
lean_dec(v_unused_110_);
v___x_103_ = v___x_100_;
v_isShared_104_ = v_isSharedCheck_109_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_merged_101_);
lean_dec(v___x_100_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_109_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_106_; 
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 1, v_merged_101_);
lean_ctor_set(v___x_103_, 0, v_o_89_);
v___x_106_ = v___x_103_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_o_89_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v_merged_101_);
v___x_106_ = v_reuseFailAlloc_108_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_object* v___x_107_; 
v___x_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
return v___x_107_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg___boxed(lean_object* v_o_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(v_o_111_, v___y_112_);
lean_dec(v___y_112_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0(lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_115_);
v___x_119_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(v___x_118_, v___y_116_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0___boxed(lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0(v___y_120_, v___y_121_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
return v_res_123_;
}
}
static lean_object* _init_l_Lean_snapshotEnvLinterOptions___closed__0(void){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_124_;
}
}
static lean_object* _init_l_Lean_snapshotEnvLinterOptions___closed__1(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__0, &l_Lean_snapshotEnvLinterOptions___closed__0_once, _init_l_Lean_snapshotEnvLinterOptions___closed__0);
v___x_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
return v___x_126_;
}
}
static lean_object* _init_l_Lean_snapshotEnvLinterOptions___closed__2(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__1, &l_Lean_snapshotEnvLinterOptions___closed__1_once, _init_l_Lean_snapshotEnvLinterOptions___closed__1);
v___x_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_snapshotEnvLinterOptions(lean_object* v_declName_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_133_ = l_Lean_Linter_envLinterOptionsRef;
v___x_134_ = lean_st_ref_get(v___x_133_);
v___x_135_ = lean_array_get_size(v___x_134_);
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = lean_nat_dec_eq(v___x_135_, v___x_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; lean_object* v_a_139_; lean_object* v___x_140_; 
v___x_138_ = l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0(v_a_130_, v_a_131_);
v_a_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_a_139_);
lean_dec_ref(v___x_138_);
lean_inc(v_declName_129_);
v___x_140_ = l_Lean_isAutoDeclOrPrivate__Internal___redArg(v_declName_129_, v_a_131_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_194_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_194_ == 0)
{
v___x_143_ = v___x_140_;
v_isShared_144_ = v_isSharedCheck_194_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_140_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_194_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
uint8_t v___x_145_; 
v___x_145_ = lean_unbox(v_a_141_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; size_t v_sz_147_; size_t v___x_148_; lean_object* v___x_149_; 
lean_del_object(v___x_143_);
v___x_146_ = lean_box(1);
v_sz_147_ = lean_array_size(v___x_134_);
v___x_148_ = ((size_t)0ULL);
v___x_149_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg(v_a_139_, v___x_134_, v_sz_147_, v___x_148_, v___x_146_);
lean_dec(v___x_134_);
lean_dec(v_a_139_);
if (lean_obj_tag(v___x_149_) == 0)
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_181_; 
v_a_150_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_181_ == 0)
{
v___x_152_ = v___x_149_;
v_isShared_153_ = v_isSharedCheck_181_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_149_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_181_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; lean_object* v_env_155_; lean_object* v_nextMacroScope_156_; lean_object* v_ngen_157_; lean_object* v_auxDeclNGen_158_; lean_object* v_traceState_159_; lean_object* v_recordedDeps_160_; lean_object* v_messages_161_; lean_object* v_infoState_162_; lean_object* v_snapshotTasks_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_179_; 
v___x_154_ = lean_st_ref_take(v_a_131_);
v_env_155_ = lean_ctor_get(v___x_154_, 0);
v_nextMacroScope_156_ = lean_ctor_get(v___x_154_, 1);
v_ngen_157_ = lean_ctor_get(v___x_154_, 2);
v_auxDeclNGen_158_ = lean_ctor_get(v___x_154_, 3);
v_traceState_159_ = lean_ctor_get(v___x_154_, 4);
v_recordedDeps_160_ = lean_ctor_get(v___x_154_, 6);
v_messages_161_ = lean_ctor_get(v___x_154_, 7);
v_infoState_162_ = lean_ctor_get(v___x_154_, 8);
v_snapshotTasks_163_ = lean_ctor_get(v___x_154_, 9);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_179_ == 0)
{
lean_object* v_unused_180_; 
v_unused_180_ = lean_ctor_get(v___x_154_, 5);
lean_dec(v_unused_180_);
v___x_165_ = v___x_154_;
v_isShared_166_ = v_isSharedCheck_179_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_snapshotTasks_163_);
lean_inc(v_infoState_162_);
lean_inc(v_messages_161_);
lean_inc(v_recordedDeps_160_);
lean_inc(v_traceState_159_);
lean_inc(v_auxDeclNGen_158_);
lean_inc(v_ngen_157_);
lean_inc(v_nextMacroScope_156_);
lean_inc(v_env_155_);
lean_dec(v___x_154_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_179_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_173_; 
v___x_167_ = lean_box(0);
v___x_168_ = l_Lean_Linter_envLinterSnapshotExt;
v___x_169_ = lean_unbox(v_a_141_);
lean_dec(v_a_141_);
v___x_170_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_168_, v_env_155_, v_declName_129_, v_a_150_, v___x_169_);
v___x_171_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 5, v___x_171_);
lean_ctor_set(v___x_165_, 0, v___x_170_);
v___x_173_ = v___x_165_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_170_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v_nextMacroScope_156_);
lean_ctor_set(v_reuseFailAlloc_178_, 2, v_ngen_157_);
lean_ctor_set(v_reuseFailAlloc_178_, 3, v_auxDeclNGen_158_);
lean_ctor_set(v_reuseFailAlloc_178_, 4, v_traceState_159_);
lean_ctor_set(v_reuseFailAlloc_178_, 5, v___x_171_);
lean_ctor_set(v_reuseFailAlloc_178_, 6, v_recordedDeps_160_);
lean_ctor_set(v_reuseFailAlloc_178_, 7, v_messages_161_);
lean_ctor_set(v_reuseFailAlloc_178_, 8, v_infoState_162_);
lean_ctor_set(v_reuseFailAlloc_178_, 9, v_snapshotTasks_163_);
v___x_173_ = v_reuseFailAlloc_178_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_174_ = lean_st_ref_put(v_a_131_, v___x_173_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v___x_167_);
v___x_176_ = v___x_152_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_167_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
else
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_189_; 
lean_dec(v_a_141_);
lean_dec(v_declName_129_);
v_a_182_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_189_ == 0)
{
v___x_184_ = v___x_149_;
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_149_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_a_182_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
else
{
lean_object* v___x_190_; lean_object* v___x_192_; 
lean_dec(v_a_141_);
lean_dec(v_a_139_);
lean_dec(v___x_134_);
lean_dec(v_declName_129_);
v___x_190_ = lean_box(0);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v___x_190_);
v___x_192_ = v___x_143_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
else
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
lean_dec(v_a_139_);
lean_dec(v___x_134_);
lean_dec(v_declName_129_);
v_a_195_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_202_ == 0)
{
v___x_197_ = v___x_140_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_140_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_195_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
else
{
lean_object* v___x_203_; lean_object* v___x_204_; 
lean_dec(v___x_134_);
lean_dec(v_declName_129_);
v___x_203_ = lean_box(0);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_snapshotEnvLinterOptions___boxed(lean_object* v_declName_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_snapshotEnvLinterOptions(v_declName_205_, v_a_206_, v_a_207_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0(lean_object* v_o_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(v_o_210_, v___y_212_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___boxed(lean_object* v_o_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0(v_o_215_, v___y_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1(lean_object* v_a_220_, lean_object* v_as_221_, size_t v_sz_222_, size_t v_i_223_, lean_object* v_b_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg(v_a_220_, v_as_221_, v_sz_222_, v_i_223_, v_b_224_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___boxed(lean_object* v_a_229_, lean_object* v_as_230_, lean_object* v_sz_231_, lean_object* v_i_232_, lean_object* v_b_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
size_t v_sz_boxed_237_; size_t v_i_boxed_238_; lean_object* v_res_239_; 
v_sz_boxed_237_ = lean_unbox_usize(v_sz_231_);
lean_dec(v_sz_231_);
v_i_boxed_238_ = lean_unbox_usize(v_i_232_);
lean_dec(v_i_232_);
v_res_239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1(v_a_229_, v_as_230_, v_sz_boxed_237_, v_i_boxed_238_, v_b_233_, v___y_234_, v___y_235_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec_ref(v_as_230_);
lean_dec_ref(v_a_229_);
return v_res_239_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_AddDecl_0__Lean_isNamespaceName(lean_object* v_x_240_){
_start:
{
if (lean_obj_tag(v_x_240_) == 1)
{
lean_object* v_pre_241_; 
v_pre_241_ = lean_ctor_get(v_x_240_, 0);
if (lean_obj_tag(v_pre_241_) == 0)
{
uint8_t v___x_242_; 
v___x_242_ = 1;
return v___x_242_;
}
else
{
v_x_240_ = v_pre_241_;
goto _start;
}
}
else
{
uint8_t v___x_244_; 
v___x_244_ = 0;
return v___x_244_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_isNamespaceName___boxed(lean_object* v_x_245_){
_start:
{
uint8_t v_res_246_; lean_object* v_r_247_; 
v_res_246_ = l___private_Lean_AddDecl_0__Lean_isNamespaceName(v_x_245_);
lean_dec(v_x_245_);
v_r_247_ = lean_box(v_res_246_);
return v_r_247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_registerNamePrefixes_go(lean_object* v_env_248_, lean_object* v_x_249_){
_start:
{
if (lean_obj_tag(v_x_249_) == 1)
{
lean_object* v_pre_250_; uint8_t v___x_251_; 
v_pre_250_ = lean_ctor_get(v_x_249_, 0);
lean_inc(v_pre_250_);
lean_dec_ref_known(v_x_249_, 2);
v___x_251_ = l___private_Lean_AddDecl_0__Lean_isNamespaceName(v_pre_250_);
if (v___x_251_ == 0)
{
lean_dec(v_pre_250_);
return v_env_248_;
}
else
{
lean_object* v___x_252_; 
lean_inc(v_pre_250_);
v___x_252_ = l_Lean_Environment_registerNamespace(v_env_248_, v_pre_250_);
v_env_248_ = v___x_252_;
v_x_249_ = v_pre_250_;
goto _start;
}
}
else
{
lean_dec(v_x_249_);
return v_env_248_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(lean_object* v_env_254_, lean_object* v_name_255_){
_start:
{
lean_object* v_name_256_; uint32_t v___y_258_; 
v_name_256_ = l_Lean_privateToUserName(v_name_255_);
if (lean_obj_tag(v_name_256_) == 1)
{
lean_object* v_str_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v_str_262_ = lean_ctor_get(v_name_256_, 1);
v___x_263_ = lean_unsigned_to_nat(0u);
v___x_264_ = lean_string_utf8_byte_size(v_str_262_);
lean_inc_ref(v_str_262_);
v___x_265_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_265_, 0, v_str_262_);
lean_ctor_set(v___x_265_, 1, v___x_263_);
lean_ctor_set(v___x_265_, 2, v___x_264_);
v___x_266_ = l_String_Slice_Pos_get_x3f(v___x_265_, v___x_263_);
lean_dec_ref_known(v___x_265_, 3);
if (lean_obj_tag(v___x_266_) == 0)
{
uint32_t v___x_267_; 
v___x_267_ = 65;
v___y_258_ = v___x_267_;
goto v___jp_257_;
}
else
{
lean_object* v_val_268_; uint32_t v___x_269_; 
v_val_268_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_val_268_);
lean_dec_ref_known(v___x_266_, 1);
v___x_269_ = lean_unbox_uint32(v_val_268_);
lean_dec(v_val_268_);
v___y_258_ = v___x_269_;
goto v___jp_257_;
}
}
else
{
lean_dec(v_name_256_);
return v_env_254_;
}
v___jp_257_:
{
uint32_t v___x_259_; uint8_t v___x_260_; 
v___x_259_ = 95;
v___x_260_ = lean_uint32_dec_eq(v___y_258_, v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; 
v___x_261_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes_go(v_env_254_, v_name_256_);
return v___x_261_;
}
else
{
lean_dec(v_name_256_);
return v_env_254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(lean_object* v_name_270_, lean_object* v_decl_271_, lean_object* v_ref_272_){
_start:
{
lean_object* v_defValue_274_; lean_object* v_descr_275_; lean_object* v_deprecation_x3f_276_; lean_object* v___x_277_; uint8_t v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v_defValue_274_ = lean_ctor_get(v_decl_271_, 0);
v_descr_275_ = lean_ctor_get(v_decl_271_, 1);
v_deprecation_x3f_276_ = lean_ctor_get(v_decl_271_, 2);
v___x_277_ = lean_alloc_ctor(1, 0, 1);
v___x_278_ = lean_unbox(v_defValue_274_);
lean_ctor_set_uint8(v___x_277_, 0, v___x_278_);
lean_inc(v_deprecation_x3f_276_);
lean_inc_ref(v_descr_275_);
lean_inc_n(v_name_270_, 2);
v___x_279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_279_, 0, v_name_270_);
lean_ctor_set(v___x_279_, 1, v_ref_272_);
lean_ctor_set(v___x_279_, 2, v___x_277_);
lean_ctor_set(v___x_279_, 3, v_descr_275_);
lean_ctor_set(v___x_279_, 4, v_deprecation_x3f_276_);
v___x_280_ = lean_register_option(v_name_270_, v___x_279_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_288_; 
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_288_ == 0)
{
lean_object* v_unused_289_; 
v_unused_289_ = lean_ctor_get(v___x_280_, 0);
lean_dec(v_unused_289_);
v___x_282_ = v___x_280_;
v_isShared_283_ = v_isSharedCheck_288_;
goto v_resetjp_281_;
}
else
{
lean_dec(v___x_280_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_288_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; lean_object* v___x_286_; 
lean_inc(v_defValue_274_);
v___x_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_284_, 0, v_name_270_);
lean_ctor_set(v___x_284_, 1, v_defValue_274_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v___x_284_);
v___x_286_ = v___x_282_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
else
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
lean_dec(v_name_270_);
v_a_290_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___x_280_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_280_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_290_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_298_, lean_object* v_decl_299_, lean_object* v_ref_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(v_name_298_, v_decl_299_, v_ref_300_);
lean_dec_ref(v_decl_299_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_320_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__2_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_321_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__4_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_322_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__6_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_323_ = l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(v___x_320_, v___x_321_, v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4____boxed(lean_object* v_a_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_();
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(lean_object* v_msgData_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
lean_object* v___x_332_; lean_object* v_env_333_; uint8_t v___x_334_; lean_object* v_env_335_; lean_object* v___x_336_; lean_object* v_toCold_337_; lean_object* v_mctx_338_; lean_object* v_lctx_339_; lean_object* v_options_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_332_ = lean_st_ref_get(v___y_330_);
v_env_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc_ref(v_env_333_);
lean_dec(v___x_332_);
v___x_334_ = 0;
v_env_335_ = l_Lean_Environment_setRecordingDeps(v_env_333_, v___x_334_);
v___x_336_ = lean_st_ref_get(v___y_328_);
v_toCold_337_ = lean_ctor_get(v___y_329_, 0);
v_mctx_338_ = lean_ctor_get(v___x_336_, 0);
lean_inc_ref(v_mctx_338_);
lean_dec(v___x_336_);
v_lctx_339_ = lean_ctor_get(v___y_327_, 2);
v_options_340_ = lean_ctor_get(v_toCold_337_, 2);
lean_inc_ref(v_options_340_);
lean_inc_ref(v_lctx_339_);
v___x_341_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_341_, 0, v_env_335_);
lean_ctor_set(v___x_341_, 1, v_mctx_338_);
lean_ctor_set(v___x_341_, 2, v_lctx_339_);
lean_ctor_set(v___x_341_, 3, v_options_340_);
v___x_342_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v_msgData_326_);
v___x_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0___boxed(lean_object* v_msgData_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(v_msgData_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___lam__0(lean_object* v_s_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_374_; 
lean_inc_ref(v_s_351_);
v___x_358_ = l_Lean_MessageData_ofExpr(v_s_351_);
v___x_359_ = l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(v___x_358_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
v_a_360_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_374_ == 0)
{
v___x_362_ = v___x_359_;
v_isShared_363_ = v_isSharedCheck_374_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_359_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_374_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_364_ = lean_st_ref_take(v___y_352_);
v___x_365_ = lean_box(0);
v___x_366_ = l_Lean_Expr_isSyntheticSorry(v_s_351_);
lean_dec_ref(v_s_351_);
v___x_367_ = lean_box(v___x_366_);
v___x_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
lean_ctor_set(v___x_368_, 1, v_a_360_);
v___x_369_ = lean_array_push(v___x_364_, v___x_368_);
v___x_370_ = lean_st_ref_put(v___y_352_, v___x_369_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v___x_365_);
v___x_372_ = v___x_362_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_365_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___lam__0___boxed(lean_object* v_s_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_warnIfUsesSorry___lam__0(v_s_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
return v_res_382_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(uint8_t v_suppressElabErrors_391_, uint8_t v___y_392_, lean_object* v_x_393_){
_start:
{
if (lean_obj_tag(v_x_393_) == 1)
{
lean_object* v_pre_394_; 
v_pre_394_ = lean_ctor_get(v_x_393_, 0);
switch(lean_obj_tag(v_pre_394_))
{
case 1:
{
lean_object* v_pre_395_; 
v_pre_395_ = lean_ctor_get(v_pre_394_, 0);
switch(lean_obj_tag(v_pre_395_))
{
case 0:
{
lean_object* v_str_396_; lean_object* v_str_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v_str_396_ = lean_ctor_get(v_x_393_, 1);
v_str_397_ = lean_ctor_get(v_pre_394_, 1);
v___x_398_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__0));
v___x_399_ = lean_string_dec_eq(v_str_397_, v___x_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_400_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__1));
v___x_401_ = lean_string_dec_eq(v_str_397_, v___x_400_);
if (v___x_401_ == 0)
{
return v___x_401_;
}
else
{
lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_402_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__2));
v___x_403_ = lean_string_dec_eq(v_str_396_, v___x_402_);
if (v___x_403_ == 0)
{
return v___x_403_;
}
else
{
return v_suppressElabErrors_391_;
}
}
}
else
{
lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_404_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__3));
v___x_405_ = lean_string_dec_eq(v_str_396_, v___x_404_);
if (v___x_405_ == 0)
{
return v___x_405_;
}
else
{
return v_suppressElabErrors_391_;
}
}
}
case 1:
{
lean_object* v_pre_406_; 
v_pre_406_ = lean_ctor_get(v_pre_395_, 0);
if (lean_obj_tag(v_pre_406_) == 0)
{
lean_object* v_str_407_; lean_object* v_str_408_; lean_object* v_str_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v_str_407_ = lean_ctor_get(v_x_393_, 1);
v_str_408_ = lean_ctor_get(v_pre_394_, 1);
v_str_409_ = lean_ctor_get(v_pre_395_, 1);
v___x_410_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__4));
v___x_411_ = lean_string_dec_eq(v_str_409_, v___x_410_);
if (v___x_411_ == 0)
{
return v___x_411_;
}
else
{
lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_412_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__5));
v___x_413_ = lean_string_dec_eq(v_str_408_, v___x_412_);
if (v___x_413_ == 0)
{
return v___x_413_;
}
else
{
lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_414_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__6));
v___x_415_ = lean_string_dec_eq(v_str_407_, v___x_414_);
if (v___x_415_ == 0)
{
return v___x_415_;
}
else
{
return v_suppressElabErrors_391_;
}
}
}
}
else
{
return v___y_392_;
}
}
default: 
{
return v___y_392_;
}
}
}
case 0:
{
lean_object* v_str_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v_str_416_ = lean_ctor_get(v_x_393_, 1);
v___x_417_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__7));
v___x_418_ = lean_string_dec_eq(v_str_416_, v___x_417_);
if (v___x_418_ == 0)
{
return v___x_418_;
}
else
{
return v_suppressElabErrors_391_;
}
}
default: 
{
return v___y_392_;
}
}
}
else
{
return v___y_392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed(lean_object* v_suppressElabErrors_419_, lean_object* v___y_420_, lean_object* v_x_421_){
_start:
{
uint8_t v_suppressElabErrors_boxed_422_; uint8_t v___y_15069__boxed_423_; uint8_t v_res_424_; lean_object* v_r_425_; 
v_suppressElabErrors_boxed_422_ = lean_unbox(v_suppressElabErrors_419_);
v___y_15069__boxed_423_ = lean_unbox(v___y_420_);
v_res_424_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(v_suppressElabErrors_boxed_422_, v___y_15069__boxed_423_, v_x_421_);
lean_dec(v_x_421_);
v_r_425_ = lean_box(v_res_424_);
return v_r_425_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__0, &l_Lean_snapshotEnvLinterOptions___closed__0_once, _init_l_Lean_snapshotEnvLinterOptions___closed__0);
v___x_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
return v___x_427_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_428_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0);
v___x_429_ = lean_unsigned_to_nat(0u);
v___x_430_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
lean_ctor_set(v___x_430_, 2, v___x_429_);
lean_ctor_set(v___x_430_, 3, v___x_429_);
lean_ctor_set(v___x_430_, 4, v___x_428_);
lean_ctor_set(v___x_430_, 5, v___x_428_);
lean_ctor_set(v___x_430_, 6, v___x_428_);
lean_ctor_set(v___x_430_, 7, v___x_428_);
lean_ctor_set(v___x_430_, 8, v___x_428_);
lean_ctor_set(v___x_430_, 9, v___x_428_);
lean_ctor_set(v___x_430_, 10, v___x_428_);
return v___x_430_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_431_ = lean_unsigned_to_nat(32u);
v___x_432_ = lean_mk_empty_array_with_capacity(v___x_431_);
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
return v___x_433_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3(void){
_start:
{
size_t v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_434_ = ((size_t)5ULL);
v___x_435_ = lean_unsigned_to_nat(0u);
v___x_436_ = lean_unsigned_to_nat(32u);
v___x_437_ = lean_mk_empty_array_with_capacity(v___x_436_);
v___x_438_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2);
v___x_439_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_439_, 0, v___x_438_);
lean_ctor_set(v___x_439_, 1, v___x_437_);
lean_ctor_set(v___x_439_, 2, v___x_435_);
lean_ctor_set(v___x_439_, 3, v___x_435_);
lean_ctor_set_usize(v___x_439_, 4, v___x_434_);
return v___x_439_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_440_ = lean_box(1);
v___x_441_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3);
v___x_442_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0);
v___x_443_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
lean_ctor_set(v___x_443_, 1, v___x_441_);
lean_ctor_set(v___x_443_, 2, v___x_440_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(lean_object* v_msgData_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v___x_448_; lean_object* v_toCold_449_; lean_object* v_env_450_; lean_object* v_options_451_; uint8_t v___x_452_; lean_object* v_env_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_448_ = lean_st_ref_get(v___y_446_);
v_toCold_449_ = lean_ctor_get(v___y_445_, 0);
v_env_450_ = lean_ctor_get(v___x_448_, 0);
lean_inc_ref(v_env_450_);
lean_dec(v___x_448_);
v_options_451_ = lean_ctor_get(v_toCold_449_, 2);
v___x_452_ = 0;
v_env_453_ = l_Lean_Environment_setRecordingDeps(v_env_450_, v___x_452_);
v___x_454_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1);
v___x_455_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
lean_inc_ref(v_options_451_);
v___x_456_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_456_, 0, v_env_453_);
lean_ctor_set(v___x_456_, 1, v___x_454_);
lean_ctor_set(v___x_456_, 2, v___x_455_);
lean_ctor_set(v___x_456_, 3, v_options_451_);
v___x_457_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v_msgData_444_);
v___x_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___boxed(lean_object* v_msgData_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msgData_459_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(lean_object* v_ref_465_, lean_object* v_msgData_466_, uint8_t v_severity_467_, uint8_t v_isSilent_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
uint8_t v___y_473_; lean_object* v___y_474_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; uint8_t v___y_478_; lean_object* v___y_479_; lean_object* v_toCold_480_; lean_object* v___y_481_; lean_object* v___y_510_; lean_object* v___y_511_; uint8_t v___y_512_; uint8_t v___y_513_; uint8_t v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_537_; uint8_t v___y_538_; lean_object* v___y_539_; uint8_t v___y_540_; lean_object* v___y_541_; uint8_t v___y_542_; lean_object* v___y_543_; uint8_t v___y_547_; uint8_t v___y_548_; uint8_t v___y_549_; uint8_t v___x_560_; uint8_t v___y_562_; uint8_t v___y_563_; uint8_t v___y_564_; uint8_t v___y_566_; uint8_t v___x_574_; 
v___x_560_ = 2;
v___x_574_ = l_Lean_instBEqMessageSeverity_beq(v_severity_467_, v___x_560_);
if (v___x_574_ == 0)
{
v___y_566_ = v___x_574_;
goto v___jp_565_;
}
else
{
uint8_t v___x_575_; 
lean_inc_ref(v_msgData_466_);
v___x_575_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_466_);
v___y_566_ = v___x_575_;
goto v___jp_565_;
}
v___jp_472_:
{
lean_object* v_currNamespace_482_; lean_object* v_openDecls_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v_env_488_; lean_object* v_nextMacroScope_489_; lean_object* v_ngen_490_; lean_object* v_auxDeclNGen_491_; lean_object* v_traceState_492_; lean_object* v_cache_493_; lean_object* v_recordedDeps_494_; lean_object* v_messages_495_; lean_object* v_infoState_496_; lean_object* v_snapshotTasks_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_508_; 
v_currNamespace_482_ = lean_ctor_get(v_toCold_480_, 4);
v_openDecls_483_ = lean_ctor_get(v_toCold_480_, 5);
lean_inc(v_openDecls_483_);
lean_inc(v_currNamespace_482_);
v___x_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_484_, 0, v_currNamespace_482_);
lean_ctor_set(v___x_484_, 1, v_openDecls_483_);
v___x_485_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
lean_ctor_set(v___x_485_, 1, v___y_476_);
lean_inc_ref(v___y_475_);
lean_inc_ref(v___y_474_);
v___x_486_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_486_, 0, v___y_474_);
lean_ctor_set(v___x_486_, 1, v___y_477_);
lean_ctor_set(v___x_486_, 2, v___y_479_);
lean_ctor_set(v___x_486_, 3, v___y_475_);
lean_ctor_set(v___x_486_, 4, v___x_485_);
lean_ctor_set_uint8(v___x_486_, sizeof(void*)*5, v___y_473_);
lean_ctor_set_uint8(v___x_486_, sizeof(void*)*5 + 1, v___y_478_);
lean_ctor_set_uint8(v___x_486_, sizeof(void*)*5 + 2, v_isSilent_468_);
v___x_487_ = lean_st_ref_take(v___y_481_);
v_env_488_ = lean_ctor_get(v___x_487_, 0);
v_nextMacroScope_489_ = lean_ctor_get(v___x_487_, 1);
v_ngen_490_ = lean_ctor_get(v___x_487_, 2);
v_auxDeclNGen_491_ = lean_ctor_get(v___x_487_, 3);
v_traceState_492_ = lean_ctor_get(v___x_487_, 4);
v_cache_493_ = lean_ctor_get(v___x_487_, 5);
v_recordedDeps_494_ = lean_ctor_get(v___x_487_, 6);
v_messages_495_ = lean_ctor_get(v___x_487_, 7);
v_infoState_496_ = lean_ctor_get(v___x_487_, 8);
v_snapshotTasks_497_ = lean_ctor_get(v___x_487_, 9);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_508_ == 0)
{
v___x_499_ = v___x_487_;
v_isShared_500_ = v_isSharedCheck_508_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_snapshotTasks_497_);
lean_inc(v_infoState_496_);
lean_inc(v_messages_495_);
lean_inc(v_recordedDeps_494_);
lean_inc(v_cache_493_);
lean_inc(v_traceState_492_);
lean_inc(v_auxDeclNGen_491_);
lean_inc(v_ngen_490_);
lean_inc(v_nextMacroScope_489_);
lean_inc(v_env_488_);
lean_dec(v___x_487_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_508_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_501_ = lean_box(0);
v___x_502_ = l_Lean_MessageLog_add(v___x_486_, v_messages_495_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 7, v___x_502_);
v___x_504_ = v___x_499_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_env_488_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_nextMacroScope_489_);
lean_ctor_set(v_reuseFailAlloc_507_, 2, v_ngen_490_);
lean_ctor_set(v_reuseFailAlloc_507_, 3, v_auxDeclNGen_491_);
lean_ctor_set(v_reuseFailAlloc_507_, 4, v_traceState_492_);
lean_ctor_set(v_reuseFailAlloc_507_, 5, v_cache_493_);
lean_ctor_set(v_reuseFailAlloc_507_, 6, v_recordedDeps_494_);
lean_ctor_set(v_reuseFailAlloc_507_, 7, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_507_, 8, v_infoState_496_);
lean_ctor_set(v_reuseFailAlloc_507_, 9, v_snapshotTasks_497_);
v___x_504_ = v_reuseFailAlloc_507_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_st_ref_put(v___y_481_, v___x_504_);
v___x_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_501_);
return v___x_506_;
}
}
}
v___jp_509_:
{
lean_object* v_fileName_518_; lean_object* v_fileMap_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_535_; 
v_fileName_518_ = lean_ctor_get(v___y_516_, 0);
v_fileMap_519_ = lean_ctor_get(v___y_516_, 1);
v___x_520_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_466_);
v___x_521_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v___x_520_, v___y_469_, v___y_470_);
v_a_522_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_535_ == 0)
{
v___x_524_ = v___x_521_;
v_isShared_525_ = v_isSharedCheck_535_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_521_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_535_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
lean_inc_ref_n(v_fileMap_519_, 2);
v___x_526_ = l_Lean_FileMap_toPosition(v_fileMap_519_, v___y_515_);
lean_dec(v___y_515_);
v___x_527_ = l_Lean_FileMap_toPosition(v_fileMap_519_, v___y_517_);
lean_dec(v___y_517_);
v___x_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
v___x_529_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
if (v___y_513_ == 0)
{
lean_del_object(v___x_524_);
lean_dec_ref(v___y_510_);
v___y_473_ = v___y_512_;
v___y_474_ = v_fileName_518_;
v___y_475_ = v___x_529_;
v___y_476_ = v_a_522_;
v___y_477_ = v___x_526_;
v___y_478_ = v___y_514_;
v___y_479_ = v___x_528_;
v_toCold_480_ = v___y_511_;
v___y_481_ = v___y_470_;
goto v___jp_472_;
}
else
{
uint8_t v___x_530_; 
lean_inc(v_a_522_);
v___x_530_ = l_Lean_MessageData_hasTag(v___y_510_, v_a_522_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_533_; 
lean_dec_ref_known(v___x_528_, 1);
lean_dec_ref(v___x_526_);
lean_dec(v_a_522_);
v___x_531_ = lean_box(0);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v___x_531_);
v___x_533_ = v___x_524_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_531_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
else
{
lean_del_object(v___x_524_);
v___y_473_ = v___y_512_;
v___y_474_ = v_fileName_518_;
v___y_475_ = v___x_529_;
v___y_476_ = v_a_522_;
v___y_477_ = v___x_526_;
v___y_478_ = v___y_514_;
v___y_479_ = v___x_528_;
v_toCold_480_ = v___y_511_;
v___y_481_ = v___y_470_;
goto v___jp_472_;
}
}
}
}
v___jp_536_:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_Syntax_getTailPos_x3f(v___y_541_, v___y_540_);
lean_dec(v___y_541_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_inc(v___y_543_);
v___y_510_ = v___y_537_;
v___y_511_ = v___y_539_;
v___y_512_ = v___y_540_;
v___y_513_ = v___y_538_;
v___y_514_ = v___y_542_;
v___y_515_ = v___y_543_;
v___y_516_ = v___y_539_;
v___y_517_ = v___y_543_;
goto v___jp_509_;
}
else
{
lean_object* v_val_545_; 
v_val_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_val_545_);
lean_dec_ref_known(v___x_544_, 1);
v___y_510_ = v___y_537_;
v___y_511_ = v___y_539_;
v___y_512_ = v___y_540_;
v___y_513_ = v___y_538_;
v___y_514_ = v___y_542_;
v___y_515_ = v___y_543_;
v___y_516_ = v___y_539_;
v___y_517_ = v_val_545_;
goto v___jp_509_;
}
}
v___jp_546_:
{
lean_object* v_toCold_550_; lean_object* v_ref_551_; uint8_t v_suppressElabErrors_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___f_555_; lean_object* v_ref_556_; lean_object* v___x_557_; 
v_toCold_550_ = lean_ctor_get(v___y_469_, 0);
v_ref_551_ = lean_ctor_get(v___y_469_, 2);
v_suppressElabErrors_552_ = lean_ctor_get_uint8(v___y_469_, sizeof(void*)*3 + 2);
v___x_553_ = lean_box(v_suppressElabErrors_552_);
v___x_554_ = lean_box(v___y_547_);
v___f_555_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed), 3, 2);
lean_closure_set(v___f_555_, 0, v___x_553_);
lean_closure_set(v___f_555_, 1, v___x_554_);
v_ref_556_ = l_Lean_replaceRef(v_ref_465_, v_ref_551_);
v___x_557_ = l_Lean_Syntax_getPos_x3f(v_ref_556_, v___y_548_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v___x_558_; 
v___x_558_ = lean_unsigned_to_nat(0u);
v___y_537_ = v___f_555_;
v___y_538_ = v_suppressElabErrors_552_;
v___y_539_ = v_toCold_550_;
v___y_540_ = v___y_548_;
v___y_541_ = v_ref_556_;
v___y_542_ = v___y_549_;
v___y_543_ = v___x_558_;
goto v___jp_536_;
}
else
{
lean_object* v_val_559_; 
v_val_559_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_val_559_);
lean_dec_ref_known(v___x_557_, 1);
v___y_537_ = v___f_555_;
v___y_538_ = v_suppressElabErrors_552_;
v___y_539_ = v_toCold_550_;
v___y_540_ = v___y_548_;
v___y_541_ = v_ref_556_;
v___y_542_ = v___y_549_;
v___y_543_ = v_val_559_;
goto v___jp_536_;
}
}
v___jp_561_:
{
if (v___y_564_ == 0)
{
v___y_547_ = v___y_562_;
v___y_548_ = v___y_563_;
v___y_549_ = v_severity_467_;
goto v___jp_546_;
}
else
{
v___y_547_ = v___y_562_;
v___y_548_ = v___y_563_;
v___y_549_ = v___x_560_;
goto v___jp_546_;
}
}
v___jp_565_:
{
if (v___y_566_ == 0)
{
uint8_t v___x_567_; uint8_t v___x_568_; 
v___x_567_ = 1;
v___x_568_ = l_Lean_instBEqMessageSeverity_beq(v_severity_467_, v___x_567_);
if (v___x_568_ == 0)
{
v___y_562_ = v___y_566_;
v___y_563_ = v___y_566_;
v___y_564_ = v___x_568_;
goto v___jp_561_;
}
else
{
lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_569_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_469_);
v___x_570_ = l_Lean_warningAsError;
v___x_571_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_569_, v___x_570_);
lean_dec_ref(v___x_569_);
v___y_562_ = v___y_566_;
v___y_563_ = v___y_566_;
v___y_564_ = v___x_571_;
goto v___jp_561_;
}
}
else
{
lean_object* v___x_572_; lean_object* v___x_573_; 
lean_dec_ref(v_msgData_466_);
v___x_572_ = lean_box(0);
v___x_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
return v___x_573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___boxed(lean_object* v_ref_576_, lean_object* v_msgData_577_, lean_object* v_severity_578_, lean_object* v_isSilent_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
uint8_t v_severity_boxed_583_; uint8_t v_isSilent_boxed_584_; lean_object* v_res_585_; 
v_severity_boxed_583_ = lean_unbox(v_severity_578_);
v_isSilent_boxed_584_ = lean_unbox(v_isSilent_579_);
v_res_585_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_576_, v_msgData_577_, v_severity_boxed_583_, v_isSilent_boxed_584_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v_ref_576_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(lean_object* v_msgData_586_, uint8_t v_severity_587_, uint8_t v_isSilent_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_ref_592_; lean_object* v___x_593_; 
v_ref_592_ = lean_ctor_get(v___y_589_, 2);
v___x_593_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_592_, v_msgData_586_, v_severity_587_, v_isSilent_588_, v___y_589_, v___y_590_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4___boxed(lean_object* v_msgData_594_, lean_object* v_severity_595_, lean_object* v_isSilent_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
uint8_t v_severity_boxed_600_; uint8_t v_isSilent_boxed_601_; lean_object* v_res_602_; 
v_severity_boxed_600_ = lean_unbox(v_severity_595_);
v_isSilent_boxed_601_ = lean_unbox(v_isSilent_596_);
v_res_602_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_594_, v_severity_boxed_600_, v_isSilent_boxed_601_, v___y_597_, v___y_598_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(lean_object* v_msgData_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
uint8_t v___x_607_; uint8_t v___x_608_; lean_object* v___x_609_; 
v___x_607_ = 1;
v___x_608_ = 0;
v___x_609_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_603_, v___x_607_, v___x_608_, v___y_604_, v___y_605_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2___boxed(lean_object* v_msgData_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v_msgData_610_, v___y_611_, v___y_612_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(lean_object* v_as_618_, size_t v_sz_619_, size_t v_i_620_, lean_object* v_b_621_){
_start:
{
uint8_t v___x_622_; 
v___x_622_ = lean_usize_dec_lt(v_i_620_, v_sz_619_);
if (v___x_622_ == 0)
{
lean_inc_ref(v_b_621_);
return v_b_621_;
}
else
{
lean_object* v_a_623_; lean_object* v_fst_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v_a_623_ = lean_array_uget_borrowed(v_as_618_, v_i_620_);
v_fst_624_ = lean_ctor_get(v_a_623_, 0);
v___x_625_ = lean_box(0);
v___x_626_ = lean_unbox(v_fst_624_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; size_t v___x_628_; size_t v___x_629_; 
v___x_627_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___closed__0));
v___x_628_ = ((size_t)1ULL);
v___x_629_ = lean_usize_add(v_i_620_, v___x_628_);
v_i_620_ = v___x_629_;
v_b_621_ = v___x_627_;
goto _start;
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
lean_inc(v_a_623_);
v___x_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_631_, 0, v_a_623_);
v___x_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v___x_625_);
return v___x_633_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___boxed(lean_object* v_as_634_, lean_object* v_sz_635_, lean_object* v_i_636_, lean_object* v_b_637_){
_start:
{
size_t v_sz_boxed_638_; size_t v_i_boxed_639_; lean_object* v_res_640_; 
v_sz_boxed_638_ = lean_unbox_usize(v_sz_635_);
lean_dec(v_sz_635_);
v_i_boxed_639_ = lean_unbox_usize(v_i_636_);
lean_dec(v_i_636_);
v_res_640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v_as_634_, v_sz_boxed_638_, v_i_boxed_639_, v_b_637_);
lean_dec_ref(v_b_637_);
lean_dec_ref(v_as_634_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(lean_object* v_fn_641_, lean_object* v_e_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Lean_Expr_getSorry_x3f(v_e_642_);
if (lean_obj_tag(v___x_649_) == 1)
{
lean_object* v_val_650_; lean_object* v___x_651_; 
v_val_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_val_650_);
lean_dec_ref_known(v___x_649_, 1);
lean_inc(v___y_647_);
lean_inc_ref(v___y_646_);
lean_inc(v___y_645_);
lean_inc_ref(v___y_644_);
lean_inc(v___y_643_);
v___x_651_ = lean_apply_7(v_fn_641_, v_val_650_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, lean_box(0));
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_660_; 
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_660_ == 0)
{
lean_object* v_unused_661_; 
v_unused_661_ = lean_ctor_get(v___x_651_, 0);
lean_dec(v_unused_661_);
v___x_653_ = v___x_651_;
v_isShared_654_ = v_isSharedCheck_660_;
goto v_resetjp_652_;
}
else
{
lean_dec(v___x_651_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_660_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
uint8_t v___x_655_; lean_object* v___x_656_; lean_object* v___x_658_; 
v___x_655_ = 0;
v___x_656_ = lean_box(v___x_655_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 0, v___x_656_);
v___x_658_ = v___x_653_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
v_a_662_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_651_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_651_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
else
{
uint8_t v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
lean_dec(v___x_649_);
lean_dec_ref(v_fn_641_);
v___x_670_ = 1;
v___x_671_ = lean_box(v___x_670_);
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed(lean_object* v_fn_673_, lean_object* v_e_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(v_fn_673_, v_e_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v_e_674_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_object* v_00_u03b1_682_, lean_object* v_x_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_apply_1(v_x_683_, lean_box(0));
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v_00_u03b1_692_, lean_object* v_x_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(v_00_u03b1_692_, v_x_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(lean_object* v_k_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v_b_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v___x_710_; 
lean_inc(v___y_708_);
lean_inc_ref(v___y_707_);
lean_inc(v___y_706_);
lean_inc_ref(v___y_705_);
lean_inc(v___y_703_);
lean_inc(v___y_702_);
v___x_710_ = lean_apply_8(v_k_701_, v_b_704_, v___y_702_, v___y_703_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, lean_box(0));
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed(lean_object* v_k_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v_b_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(v_k_711_, v___y_712_, v___y_713_, v_b_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_713_);
lean_dec(v___y_712_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(lean_object* v_name_721_, lean_object* v_type_722_, lean_object* v_val_723_, lean_object* v_k_724_, uint8_t v_nondep_725_, uint8_t v_kind_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v___f_734_; lean_object* v___x_735_; 
lean_inc(v___y_728_);
lean_inc(v___y_727_);
v___f_734_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_734_, 0, v_k_724_);
lean_closure_set(v___f_734_, 1, v___y_727_);
lean_closure_set(v___f_734_, 2, v___y_728_);
v___x_735_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_721_, v_type_722_, v_val_723_, v___f_734_, v_nondep_725_, v_kind_726_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
if (lean_obj_tag(v___x_735_) == 0)
{
return v___x_735_;
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_735_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg___boxed(lean_object* v_name_744_, lean_object* v_type_745_, lean_object* v_val_746_, lean_object* v_k_747_, lean_object* v_nondep_748_, lean_object* v_kind_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
uint8_t v_nondep_boxed_757_; uint8_t v_kind_boxed_758_; lean_object* v_res_759_; 
v_nondep_boxed_757_ = lean_unbox(v_nondep_748_);
v_kind_boxed_758_ = lean_unbox(v_kind_749_);
v_res_759_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_744_, v_type_745_, v_val_746_, v_k_747_, v_nondep_boxed_757_, v_kind_boxed_758_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec(v___y_750_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed(lean_object* v_fvars_760_, lean_object* v_f_761_, lean_object* v_body_762_, lean_object* v_x_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(v_fvars_760_, v_f_761_, v_body_762_, v_x_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec(v___y_764_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(lean_object* v_f_772_, lean_object* v_fvars_773_, lean_object* v_a_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
if (lean_obj_tag(v_a_774_) == 8)
{
lean_object* v_declName_782_; lean_object* v_type_783_; lean_object* v_value_784_; lean_object* v_body_785_; lean_object* v___f_786_; lean_object* v_d_787_; lean_object* v_v_788_; lean_object* v___x_789_; 
v_declName_782_ = lean_ctor_get(v_a_774_, 0);
lean_inc(v_declName_782_);
v_type_783_ = lean_ctor_get(v_a_774_, 1);
lean_inc_ref(v_type_783_);
v_value_784_ = lean_ctor_get(v_a_774_, 2);
lean_inc_ref(v_value_784_);
v_body_785_ = lean_ctor_get(v_a_774_, 3);
lean_inc_ref(v_body_785_);
lean_dec_ref_known(v_a_774_, 4);
lean_inc_ref_n(v_f_772_, 2);
lean_inc_ref(v_fvars_773_);
v___f_786_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed), 11, 3);
lean_closure_set(v___f_786_, 0, v_fvars_773_);
lean_closure_set(v___f_786_, 1, v_f_772_);
lean_closure_set(v___f_786_, 2, v_body_785_);
v_d_787_ = lean_expr_instantiate_rev(v_type_783_, v_fvars_773_);
lean_dec_ref(v_type_783_);
v_v_788_ = lean_expr_instantiate_rev(v_value_784_, v_fvars_773_);
lean_dec_ref(v_fvars_773_);
lean_dec_ref(v_value_784_);
lean_inc(v___y_780_);
lean_inc_ref(v___y_779_);
lean_inc(v___y_778_);
lean_inc_ref(v___y_777_);
lean_inc(v___y_776_);
lean_inc(v___y_775_);
lean_inc_ref(v_d_787_);
v___x_789_ = lean_apply_8(v_f_772_, v_d_787_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, lean_box(0));
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v___x_790_; 
lean_dec_ref_known(v___x_789_, 1);
lean_inc(v___y_780_);
lean_inc_ref(v___y_779_);
lean_inc(v___y_778_);
lean_inc_ref(v___y_777_);
lean_inc(v___y_776_);
lean_inc(v___y_775_);
lean_inc_ref(v_v_788_);
v___x_790_ = lean_apply_8(v_f_772_, v_v_788_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, lean_box(0));
if (lean_obj_tag(v___x_790_) == 0)
{
uint8_t v___x_791_; uint8_t v___x_792_; lean_object* v___x_793_; 
lean_dec_ref_known(v___x_790_, 1);
v___x_791_ = 0;
v___x_792_ = 0;
v___x_793_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_declName_782_, v_d_787_, v_v_788_, v___f_786_, v___x_791_, v___x_792_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
return v___x_793_;
}
else
{
lean_dec_ref(v_v_788_);
lean_dec_ref(v_d_787_);
lean_dec_ref(v___f_786_);
lean_dec(v_declName_782_);
return v___x_790_;
}
}
else
{
lean_dec_ref(v_v_788_);
lean_dec_ref(v_d_787_);
lean_dec_ref(v___f_786_);
lean_dec(v_declName_782_);
lean_dec_ref(v_f_772_);
return v___x_789_;
}
}
else
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = lean_expr_instantiate_rev(v_a_774_, v_fvars_773_);
lean_dec_ref(v_fvars_773_);
lean_dec_ref(v_a_774_);
lean_inc(v___y_780_);
lean_inc_ref(v___y_779_);
lean_inc(v___y_778_);
lean_inc_ref(v___y_777_);
lean_inc(v___y_776_);
lean_inc(v___y_775_);
v___x_795_ = lean_apply_8(v_f_772_, v___x_794_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, lean_box(0));
return v___x_795_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(lean_object* v_fvars_796_, lean_object* v_f_797_, lean_object* v_body_798_, lean_object* v_x_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = lean_array_push(v_fvars_796_, v_x_799_);
v___x_808_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_797_, v___x_807_, v_body_798_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___boxed(lean_object* v_f_809_, lean_object* v_fvars_810_, lean_object* v_a_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_809_, v_fvars_810_, v_a_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
lean_dec(v___y_812_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(lean_object* v_f_822_, lean_object* v_e_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_832_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_822_, v___x_831_, v_e_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___boxed(lean_object* v_f_833_, lean_object* v_e_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v_f_833_, v_e_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec(v___y_835_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(lean_object* v_name_843_, uint8_t v_bi_844_, lean_object* v_type_845_, lean_object* v_k_846_, uint8_t v_kind_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v___f_855_; lean_object* v___x_856_; 
lean_inc(v___y_849_);
lean_inc(v___y_848_);
v___f_855_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_855_, 0, v_k_846_);
lean_closure_set(v___f_855_, 1, v___y_848_);
lean_closure_set(v___f_855_, 2, v___y_849_);
v___x_856_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_843_, v_bi_844_, v_type_845_, v___f_855_, v_kind_847_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
if (lean_obj_tag(v___x_856_) == 0)
{
return v___x_856_;
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_856_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_856_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_857_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___boxed(lean_object* v_name_865_, lean_object* v_bi_866_, lean_object* v_type_867_, lean_object* v_k_868_, lean_object* v_kind_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
uint8_t v_bi_boxed_877_; uint8_t v_kind_boxed_878_; lean_object* v_res_879_; 
v_bi_boxed_877_ = lean_unbox(v_bi_866_);
v_kind_boxed_878_ = lean_unbox(v_kind_869_);
v_res_879_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_865_, v_bi_boxed_877_, v_type_867_, v_k_868_, v_kind_boxed_878_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec(v___y_870_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed(lean_object* v_fvars_880_, lean_object* v_f_881_, lean_object* v_body_882_, lean_object* v_x_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(v_fvars_880_, v_f_881_, v_body_882_, v_x_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec(v___y_884_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(lean_object* v_f_892_, lean_object* v_fvars_893_, lean_object* v_a_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
if (lean_obj_tag(v_a_894_) == 7)
{
lean_object* v_binderName_902_; lean_object* v_binderType_903_; lean_object* v_body_904_; uint8_t v_binderInfo_905_; lean_object* v___f_906_; lean_object* v_d_907_; lean_object* v___x_908_; 
v_binderName_902_ = lean_ctor_get(v_a_894_, 0);
lean_inc(v_binderName_902_);
v_binderType_903_ = lean_ctor_get(v_a_894_, 1);
lean_inc_ref(v_binderType_903_);
v_body_904_ = lean_ctor_get(v_a_894_, 2);
lean_inc_ref(v_body_904_);
v_binderInfo_905_ = lean_ctor_get_uint8(v_a_894_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_894_, 3);
lean_inc_ref(v_f_892_);
lean_inc_ref(v_fvars_893_);
v___f_906_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed), 11, 3);
lean_closure_set(v___f_906_, 0, v_fvars_893_);
lean_closure_set(v___f_906_, 1, v_f_892_);
lean_closure_set(v___f_906_, 2, v_body_904_);
v_d_907_ = lean_expr_instantiate_rev(v_binderType_903_, v_fvars_893_);
lean_dec_ref(v_fvars_893_);
lean_dec_ref(v_binderType_903_);
lean_inc(v___y_900_);
lean_inc_ref(v___y_899_);
lean_inc(v___y_898_);
lean_inc_ref(v___y_897_);
lean_inc(v___y_896_);
lean_inc(v___y_895_);
lean_inc_ref(v_d_907_);
v___x_908_ = lean_apply_8(v_f_892_, v_d_907_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, lean_box(0));
if (lean_obj_tag(v___x_908_) == 0)
{
uint8_t v___x_909_; lean_object* v___x_910_; 
lean_dec_ref_known(v___x_908_, 1);
v___x_909_ = 0;
v___x_910_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_902_, v_binderInfo_905_, v_d_907_, v___f_906_, v___x_909_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
return v___x_910_;
}
else
{
lean_dec_ref(v_d_907_);
lean_dec_ref(v___f_906_);
lean_dec(v_binderName_902_);
return v___x_908_;
}
}
else
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_expr_instantiate_rev(v_a_894_, v_fvars_893_);
lean_dec_ref(v_fvars_893_);
lean_dec_ref(v_a_894_);
lean_inc(v___y_900_);
lean_inc_ref(v___y_899_);
lean_inc(v___y_898_);
lean_inc_ref(v___y_897_);
lean_inc(v___y_896_);
lean_inc(v___y_895_);
v___x_912_ = lean_apply_8(v_f_892_, v___x_911_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, lean_box(0));
return v___x_912_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(lean_object* v_fvars_913_, lean_object* v_f_914_, lean_object* v_body_915_, lean_object* v_x_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = lean_array_push(v_fvars_913_, v_x_916_);
v___x_925_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_914_, v___x_924_, v_body_915_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___boxed(lean_object* v_f_926_, lean_object* v_fvars_927_, lean_object* v_a_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_926_, v_fvars_927_, v_a_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec(v___y_929_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(lean_object* v_f_937_, lean_object* v_e_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_947_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_937_, v___x_946_, v_e_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10___boxed(lean_object* v_f_948_, lean_object* v_e_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v_f_948_, v_e_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec(v___y_950_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed(lean_object* v_fvars_958_, lean_object* v_f_959_, lean_object* v_body_960_, lean_object* v_x_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(v_fvars_958_, v_f_959_, v_body_960_, v_x_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec(v___y_962_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(lean_object* v_f_970_, lean_object* v_fvars_971_, lean_object* v_a_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
if (lean_obj_tag(v_a_972_) == 6)
{
lean_object* v_binderName_980_; lean_object* v_binderType_981_; lean_object* v_body_982_; uint8_t v_binderInfo_983_; lean_object* v___f_984_; lean_object* v_d_985_; lean_object* v___x_986_; 
v_binderName_980_ = lean_ctor_get(v_a_972_, 0);
lean_inc(v_binderName_980_);
v_binderType_981_ = lean_ctor_get(v_a_972_, 1);
lean_inc_ref(v_binderType_981_);
v_body_982_ = lean_ctor_get(v_a_972_, 2);
lean_inc_ref(v_body_982_);
v_binderInfo_983_ = lean_ctor_get_uint8(v_a_972_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_972_, 3);
lean_inc_ref(v_f_970_);
lean_inc_ref(v_fvars_971_);
v___f_984_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed), 11, 3);
lean_closure_set(v___f_984_, 0, v_fvars_971_);
lean_closure_set(v___f_984_, 1, v_f_970_);
lean_closure_set(v___f_984_, 2, v_body_982_);
v_d_985_ = lean_expr_instantiate_rev(v_binderType_981_, v_fvars_971_);
lean_dec_ref(v_fvars_971_);
lean_dec_ref(v_binderType_981_);
lean_inc(v___y_978_);
lean_inc_ref(v___y_977_);
lean_inc(v___y_976_);
lean_inc_ref(v___y_975_);
lean_inc(v___y_974_);
lean_inc(v___y_973_);
lean_inc_ref(v_d_985_);
v___x_986_ = lean_apply_8(v_f_970_, v_d_985_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, lean_box(0));
if (lean_obj_tag(v___x_986_) == 0)
{
uint8_t v___x_987_; lean_object* v___x_988_; 
lean_dec_ref_known(v___x_986_, 1);
v___x_987_ = 0;
v___x_988_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_980_, v_binderInfo_983_, v_d_985_, v___f_984_, v___x_987_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
return v___x_988_;
}
else
{
lean_dec_ref(v_d_985_);
lean_dec_ref(v___f_984_);
lean_dec(v_binderName_980_);
return v___x_986_;
}
}
else
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = lean_expr_instantiate_rev(v_a_972_, v_fvars_971_);
lean_dec_ref(v_fvars_971_);
lean_dec_ref(v_a_972_);
lean_inc(v___y_978_);
lean_inc_ref(v___y_977_);
lean_inc(v___y_976_);
lean_inc_ref(v___y_975_);
lean_inc(v___y_974_);
lean_inc(v___y_973_);
v___x_990_ = lean_apply_8(v_f_970_, v___x_989_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, lean_box(0));
return v___x_990_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(lean_object* v_fvars_991_, lean_object* v_f_992_, lean_object* v_body_993_, lean_object* v_x_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_array_push(v_fvars_991_, v_x_994_);
v___x_1003_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_992_, v___x_1002_, v_body_993_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___boxed(lean_object* v_f_1004_, lean_object* v_fvars_1005_, lean_object* v_a_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_1004_, v_fvars_1005_, v_a_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec(v___y_1007_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(lean_object* v_f_1015_, lean_object* v_e_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_1025_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_1015_, v___x_1024_, v_e_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11___boxed(lean_object* v_f_1026_, lean_object* v_e_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v_f_1026_, v_e_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec(v___y_1028_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(lean_object* v_a_1036_, lean_object* v_x_1037_){
_start:
{
if (lean_obj_tag(v_x_1037_) == 0)
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_box(0);
return v___x_1038_;
}
else
{
lean_object* v_key_1039_; lean_object* v_value_1040_; lean_object* v_tail_1041_; uint8_t v___x_1042_; 
v_key_1039_ = lean_ctor_get(v_x_1037_, 0);
v_value_1040_ = lean_ctor_get(v_x_1037_, 1);
v_tail_1041_ = lean_ctor_get(v_x_1037_, 2);
v___x_1042_ = lean_expr_eqv(v_key_1039_, v_a_1036_);
if (v___x_1042_ == 0)
{
v_x_1037_ = v_tail_1041_;
goto _start;
}
else
{
lean_object* v___x_1044_; 
lean_inc(v_value_1040_);
v___x_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1044_, 0, v_value_1040_);
return v___x_1044_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_a_1045_, lean_object* v_x_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1045_, v_x_1046_);
lean_dec(v_x_1046_);
lean_dec_ref(v_a_1045_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_m_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v_buckets_1050_; lean_object* v___x_1051_; uint64_t v___x_1052_; uint64_t v___x_1053_; uint64_t v___x_1054_; uint64_t v_fold_1055_; uint64_t v___x_1056_; uint64_t v___x_1057_; uint64_t v___x_1058_; size_t v___x_1059_; size_t v___x_1060_; size_t v___x_1061_; size_t v___x_1062_; size_t v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v_buckets_1050_ = lean_ctor_get(v_m_1048_, 1);
v___x_1051_ = lean_array_get_size(v_buckets_1050_);
v___x_1052_ = l_Lean_Expr_hash(v_a_1049_);
v___x_1053_ = 32ULL;
v___x_1054_ = lean_uint64_shift_right(v___x_1052_, v___x_1053_);
v_fold_1055_ = lean_uint64_xor(v___x_1052_, v___x_1054_);
v___x_1056_ = 16ULL;
v___x_1057_ = lean_uint64_shift_right(v_fold_1055_, v___x_1056_);
v___x_1058_ = lean_uint64_xor(v_fold_1055_, v___x_1057_);
v___x_1059_ = lean_uint64_to_usize(v___x_1058_);
v___x_1060_ = lean_usize_of_nat(v___x_1051_);
v___x_1061_ = ((size_t)1ULL);
v___x_1062_ = lean_usize_sub(v___x_1060_, v___x_1061_);
v___x_1063_ = lean_usize_land(v___x_1059_, v___x_1062_);
v___x_1064_ = lean_array_uget_borrowed(v_buckets_1050_, v___x_1063_);
v___x_1065_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1049_, v___x_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_m_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1066_, v_a_1067_);
lean_dec_ref(v_a_1067_);
lean_dec_ref(v_m_1066_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_object* v_00_u03b1_1069_, lean_object* v_x_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = lean_apply_1(v_x_1070_, lean_box(0));
v___x_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0___boxed(lean_object* v_00_u03b1_1079_, lean_object* v_x_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(v_00_u03b1_1079_, v_x_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(lean_object* v_x_1088_, lean_object* v_x_1089_){
_start:
{
if (lean_obj_tag(v_x_1089_) == 0)
{
return v_x_1088_;
}
else
{
lean_object* v_key_1090_; lean_object* v_value_1091_; lean_object* v_tail_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1115_; 
v_key_1090_ = lean_ctor_get(v_x_1089_, 0);
v_value_1091_ = lean_ctor_get(v_x_1089_, 1);
v_tail_1092_ = lean_ctor_get(v_x_1089_, 2);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_x_1089_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1094_ = v_x_1089_;
v_isShared_1095_ = v_isSharedCheck_1115_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_tail_1092_);
lean_inc(v_value_1091_);
lean_inc(v_key_1090_);
lean_dec(v_x_1089_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1115_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; uint64_t v___x_1097_; uint64_t v___x_1098_; uint64_t v___x_1099_; uint64_t v_fold_1100_; uint64_t v___x_1101_; uint64_t v___x_1102_; uint64_t v___x_1103_; size_t v___x_1104_; size_t v___x_1105_; size_t v___x_1106_; size_t v___x_1107_; size_t v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1111_; 
v___x_1096_ = lean_array_get_size(v_x_1088_);
v___x_1097_ = l_Lean_Expr_hash(v_key_1090_);
v___x_1098_ = 32ULL;
v___x_1099_ = lean_uint64_shift_right(v___x_1097_, v___x_1098_);
v_fold_1100_ = lean_uint64_xor(v___x_1097_, v___x_1099_);
v___x_1101_ = 16ULL;
v___x_1102_ = lean_uint64_shift_right(v_fold_1100_, v___x_1101_);
v___x_1103_ = lean_uint64_xor(v_fold_1100_, v___x_1102_);
v___x_1104_ = lean_uint64_to_usize(v___x_1103_);
v___x_1105_ = lean_usize_of_nat(v___x_1096_);
v___x_1106_ = ((size_t)1ULL);
v___x_1107_ = lean_usize_sub(v___x_1105_, v___x_1106_);
v___x_1108_ = lean_usize_land(v___x_1104_, v___x_1107_);
v___x_1109_ = lean_array_uget_borrowed(v_x_1088_, v___x_1108_);
lean_inc(v___x_1109_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 2, v___x_1109_);
v___x_1111_ = v___x_1094_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_key_1090_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_value_1091_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_object* v___x_1112_; 
v___x_1112_ = lean_array_uset(v_x_1088_, v___x_1108_, v___x_1111_);
v_x_1088_ = v___x_1112_;
v_x_1089_ = v_tail_1092_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(lean_object* v_i_1116_, lean_object* v_source_1117_, lean_object* v_target_1118_){
_start:
{
lean_object* v___x_1119_; uint8_t v___x_1120_; 
v___x_1119_ = lean_array_get_size(v_source_1117_);
v___x_1120_ = lean_nat_dec_lt(v_i_1116_, v___x_1119_);
if (v___x_1120_ == 0)
{
lean_dec_ref(v_source_1117_);
lean_dec(v_i_1116_);
return v_target_1118_;
}
else
{
lean_object* v_es_1121_; lean_object* v___x_1122_; lean_object* v_source_1123_; lean_object* v_target_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v_es_1121_ = lean_array_fget(v_source_1117_, v_i_1116_);
v___x_1122_ = lean_box(0);
v_source_1123_ = lean_array_fset(v_source_1117_, v_i_1116_, v___x_1122_);
v_target_1124_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_target_1118_, v_es_1121_);
v___x_1125_ = lean_unsigned_to_nat(1u);
v___x_1126_ = lean_nat_add(v_i_1116_, v___x_1125_);
lean_dec(v_i_1116_);
v_i_1116_ = v___x_1126_;
v_source_1117_ = v_source_1123_;
v_target_1118_ = v_target_1124_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(lean_object* v_data_1128_){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v_nbuckets_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1129_ = lean_array_get_size(v_data_1128_);
v___x_1130_ = lean_unsigned_to_nat(2u);
v_nbuckets_1131_ = lean_nat_mul(v___x_1129_, v___x_1130_);
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = lean_box(0);
v___x_1134_ = lean_mk_array(v_nbuckets_1131_, v___x_1133_);
v___x_1135_ = lean_array_propagate_mark(v_data_1128_, v___x_1134_);
v___x_1136_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v___x_1132_, v_data_1128_, v___x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(lean_object* v_a_1137_, lean_object* v_b_1138_, lean_object* v_x_1139_){
_start:
{
if (lean_obj_tag(v_x_1139_) == 0)
{
lean_dec(v_b_1138_);
lean_dec_ref(v_a_1137_);
return v_x_1139_;
}
else
{
lean_object* v_key_1140_; lean_object* v_value_1141_; lean_object* v_tail_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1154_; 
v_key_1140_ = lean_ctor_get(v_x_1139_, 0);
v_value_1141_ = lean_ctor_get(v_x_1139_, 1);
v_tail_1142_ = lean_ctor_get(v_x_1139_, 2);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_x_1139_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1144_ = v_x_1139_;
v_isShared_1145_ = v_isSharedCheck_1154_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_tail_1142_);
lean_inc(v_value_1141_);
lean_inc(v_key_1140_);
lean_dec(v_x_1139_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1154_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
uint8_t v___x_1146_; 
v___x_1146_ = lean_expr_eqv(v_key_1140_, v_a_1137_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1147_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1137_, v_b_1138_, v_tail_1142_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 2, v___x_1147_);
v___x_1149_ = v___x_1144_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_key_1140_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v_value_1141_);
lean_ctor_set(v_reuseFailAlloc_1150_, 2, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
else
{
lean_object* v___x_1152_; 
lean_dec(v_value_1141_);
lean_dec(v_key_1140_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 1, v_b_1138_);
lean_ctor_set(v___x_1144_, 0, v_a_1137_);
v___x_1152_ = v___x_1144_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1137_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_b_1138_);
lean_ctor_set(v_reuseFailAlloc_1153_, 2, v_tail_1142_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(lean_object* v_a_1155_, lean_object* v_x_1156_){
_start:
{
if (lean_obj_tag(v_x_1156_) == 0)
{
uint8_t v___x_1157_; 
v___x_1157_ = 0;
return v___x_1157_;
}
else
{
lean_object* v_key_1158_; lean_object* v_tail_1159_; uint8_t v___x_1160_; 
v_key_1158_ = lean_ctor_get(v_x_1156_, 0);
v_tail_1159_ = lean_ctor_get(v_x_1156_, 2);
v___x_1160_ = lean_expr_eqv(v_key_1158_, v_a_1155_);
if (v___x_1160_ == 0)
{
v_x_1156_ = v_tail_1159_;
goto _start;
}
else
{
return v___x_1160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg___boxed(lean_object* v_a_1162_, lean_object* v_x_1163_){
_start:
{
uint8_t v_res_1164_; lean_object* v_r_1165_; 
v_res_1164_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1162_, v_x_1163_);
lean_dec(v_x_1163_);
lean_dec_ref(v_a_1162_);
v_r_1165_ = lean_box(v_res_1164_);
return v_r_1165_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(lean_object* v_m_1166_, lean_object* v_a_1167_, lean_object* v_b_1168_){
_start:
{
lean_object* v_size_1169_; lean_object* v_buckets_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1213_; 
v_size_1169_ = lean_ctor_get(v_m_1166_, 0);
v_buckets_1170_ = lean_ctor_get(v_m_1166_, 1);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_m_1166_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1172_ = v_m_1166_;
v_isShared_1173_ = v_isSharedCheck_1213_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_buckets_1170_);
lean_inc(v_size_1169_);
lean_dec(v_m_1166_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1213_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1174_; uint64_t v___x_1175_; uint64_t v___x_1176_; uint64_t v___x_1177_; uint64_t v_fold_1178_; uint64_t v___x_1179_; uint64_t v___x_1180_; uint64_t v___x_1181_; size_t v___x_1182_; size_t v___x_1183_; size_t v___x_1184_; size_t v___x_1185_; size_t v___x_1186_; lean_object* v_bkt_1187_; uint8_t v___x_1188_; 
v___x_1174_ = lean_array_get_size(v_buckets_1170_);
v___x_1175_ = l_Lean_Expr_hash(v_a_1167_);
v___x_1176_ = 32ULL;
v___x_1177_ = lean_uint64_shift_right(v___x_1175_, v___x_1176_);
v_fold_1178_ = lean_uint64_xor(v___x_1175_, v___x_1177_);
v___x_1179_ = 16ULL;
v___x_1180_ = lean_uint64_shift_right(v_fold_1178_, v___x_1179_);
v___x_1181_ = lean_uint64_xor(v_fold_1178_, v___x_1180_);
v___x_1182_ = lean_uint64_to_usize(v___x_1181_);
v___x_1183_ = lean_usize_of_nat(v___x_1174_);
v___x_1184_ = ((size_t)1ULL);
v___x_1185_ = lean_usize_sub(v___x_1183_, v___x_1184_);
v___x_1186_ = lean_usize_land(v___x_1182_, v___x_1185_);
v_bkt_1187_ = lean_array_uget_borrowed(v_buckets_1170_, v___x_1186_);
v___x_1188_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1167_, v_bkt_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; lean_object* v_size_x27_1190_; lean_object* v___x_1191_; lean_object* v_buckets_x27_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1189_ = lean_unsigned_to_nat(1u);
v_size_x27_1190_ = lean_nat_add(v_size_1169_, v___x_1189_);
lean_dec(v_size_1169_);
lean_inc(v_bkt_1187_);
v___x_1191_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1191_, 0, v_a_1167_);
lean_ctor_set(v___x_1191_, 1, v_b_1168_);
lean_ctor_set(v___x_1191_, 2, v_bkt_1187_);
v_buckets_x27_1192_ = lean_array_uset(v_buckets_1170_, v___x_1186_, v___x_1191_);
v___x_1193_ = lean_unsigned_to_nat(4u);
v___x_1194_ = lean_nat_mul(v_size_x27_1190_, v___x_1193_);
v___x_1195_ = lean_unsigned_to_nat(3u);
v___x_1196_ = lean_nat_div(v___x_1194_, v___x_1195_);
lean_dec(v___x_1194_);
v___x_1197_ = lean_array_get_size(v_buckets_x27_1192_);
v___x_1198_ = lean_nat_dec_le(v___x_1196_, v___x_1197_);
lean_dec(v___x_1196_);
if (v___x_1198_ == 0)
{
lean_object* v_val_1199_; lean_object* v___x_1201_; 
v_val_1199_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_buckets_x27_1192_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 1, v_val_1199_);
lean_ctor_set(v___x_1172_, 0, v_size_x27_1190_);
v___x_1201_ = v___x_1172_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_size_x27_1190_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_val_1199_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
else
{
lean_object* v___x_1204_; 
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 1, v_buckets_x27_1192_);
lean_ctor_set(v___x_1172_, 0, v_size_x27_1190_);
v___x_1204_ = v___x_1172_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_size_x27_1190_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_buckets_x27_1192_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
else
{
lean_object* v___x_1206_; lean_object* v_buckets_x27_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1211_; 
lean_inc(v_bkt_1187_);
v___x_1206_ = lean_box(0);
v_buckets_x27_1207_ = lean_array_uset(v_buckets_1170_, v___x_1186_, v___x_1206_);
v___x_1208_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1167_, v_b_1168_, v_bkt_1187_);
v___x_1209_ = lean_array_uset(v_buckets_x27_1207_, v___x_1186_, v___x_1208_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 1, v___x_1209_);
v___x_1211_ = v___x_1172_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_size_1169_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v___x_1209_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(lean_object* v_a_1214_, lean_object* v_e_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1218_ = lean_st_ref_take(v_a_1214_);
v___x_1219_ = lean_box(0);
v___x_1220_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v___x_1218_, v_e_1215_, v_a_1216_);
v___x_1221_ = lean_st_ref_put(v_a_1214_, v___x_1220_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed(lean_object* v_a_1222_, lean_object* v_e_1223_, lean_object* v_a_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(v_a_1222_, v_e_1223_, v_a_1224_);
lean_dec(v_a_1222_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1227_, lean_object* v_e_1228_, lean_object* v_a_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1227_, v_e_1228_, v_a_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec(v_a_1229_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(lean_object* v_fn_1237_, lean_object* v_e_1238_, lean_object* v_a_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v_a_1247_; lean_object* v___y_1259_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
lean_inc(v_a_1239_);
v___x_1261_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1261_, 0, lean_box(0));
lean_closure_set(v___x_1261_, 1, lean_box(0));
lean_closure_set(v___x_1261_, 2, v_a_1239_);
v___x_1262_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___x_1261_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1299_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1265_ = v___x_1262_;
v_isShared_1266_ = v_isSharedCheck_1299_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1262_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1299_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_a_1263_, v_e_1238_);
lean_dec(v_a_1263_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v___x_1268_; 
lean_del_object(v___x_1265_);
lean_inc_ref(v_fn_1237_);
lean_inc(v___y_1244_);
lean_inc_ref(v___y_1243_);
lean_inc(v___y_1242_);
lean_inc_ref(v___y_1241_);
lean_inc(v___y_1240_);
lean_inc_ref(v_e_1238_);
v___x_1268_ = lean_apply_7(v_fn_1237_, v_e_1238_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, lean_box(0));
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; uint8_t v___x_1270_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_a_1269_);
lean_dec_ref_known(v___x_1268_, 1);
v___x_1270_ = lean_unbox(v_a_1269_);
lean_dec(v_a_1269_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; 
lean_dec_ref(v_fn_1237_);
v___x_1271_ = lean_box(0);
v_a_1247_ = v___x_1271_;
goto v___jp_1246_;
}
else
{
switch(lean_obj_tag(v_e_1238_))
{
case 7:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1272_, 0, v_fn_1237_);
lean_inc_ref(v_e_1238_);
v___x_1273_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v___x_1272_, v_e_1238_, v_a_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
v___y_1259_ = v___x_1273_;
goto v___jp_1258_;
}
case 6:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1274_, 0, v_fn_1237_);
lean_inc_ref(v_e_1238_);
v___x_1275_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v___x_1274_, v_e_1238_, v_a_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
v___y_1259_ = v___x_1275_;
goto v___jp_1258_;
}
case 8:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1276_, 0, v_fn_1237_);
lean_inc_ref(v_e_1238_);
v___x_1277_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v___x_1276_, v_e_1238_, v_a_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
v___y_1259_ = v___x_1277_;
goto v___jp_1258_;
}
case 5:
{
lean_object* v_fn_1278_; lean_object* v_arg_1279_; lean_object* v___x_1280_; 
v_fn_1278_ = lean_ctor_get(v_e_1238_, 0);
v_arg_1279_ = lean_ctor_get(v_e_1238_, 1);
lean_inc_ref(v_fn_1278_);
lean_inc_ref(v_fn_1237_);
v___x_1280_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1237_, v_fn_1278_, v_a_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v___x_1281_; 
lean_dec_ref_known(v___x_1280_, 1);
lean_inc_ref(v_arg_1279_);
v___x_1281_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1237_, v_arg_1279_, v_a_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
v___y_1259_ = v___x_1281_;
goto v___jp_1258_;
}
else
{
lean_dec_ref(v_fn_1237_);
v___y_1259_ = v___x_1280_;
goto v___jp_1258_;
}
}
case 10:
{
lean_object* v_expr_1282_; lean_object* v___x_1283_; 
v_expr_1282_ = lean_ctor_get(v_e_1238_, 1);
lean_inc_ref(v_expr_1282_);
v___x_1283_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1237_, v_expr_1282_, v_a_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
v___y_1259_ = v___x_1283_;
goto v___jp_1258_;
}
case 11:
{
lean_object* v_struct_1284_; lean_object* v___x_1285_; 
v_struct_1284_ = lean_ctor_get(v_e_1238_, 2);
lean_inc_ref(v_struct_1284_);
v___x_1285_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1237_, v_struct_1284_, v_a_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
v___y_1259_ = v___x_1285_;
goto v___jp_1258_;
}
default: 
{
lean_object* v___x_1286_; 
lean_dec_ref(v_fn_1237_);
v___x_1286_ = lean_box(0);
v_a_1247_ = v___x_1286_;
goto v___jp_1246_;
}
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec_ref(v_e_1238_);
lean_dec_ref(v_fn_1237_);
v_a_1287_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1268_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1268_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
else
{
lean_object* v_val_1295_; lean_object* v___x_1297_; 
lean_dec_ref(v_e_1238_);
lean_dec_ref(v_fn_1237_);
v_val_1295_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_val_1295_);
lean_dec_ref_known(v___x_1267_, 1);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 0, v_val_1295_);
v___x_1297_ = v___x_1265_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_val_1295_);
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
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec_ref(v_e_1238_);
lean_dec_ref(v_fn_1237_);
v_a_1300_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1262_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1262_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
v___jp_1246_:
{
lean_object* v___f_1248_; lean_object* v___x_1249_; 
lean_inc(v_a_1239_);
v___f_1248_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1248_, 0, v_a_1239_);
lean_closure_set(v___f_1248_, 1, v_e_1238_);
lean_closure_set(v___f_1248_, 2, v_a_1247_);
v___x_1249_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___f_1248_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; 
v_unused_1257_ = lean_ctor_get(v___x_1249_, 0);
lean_dec(v_unused_1257_);
v___x_1251_ = v___x_1249_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_dec(v___x_1249_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v_a_1247_);
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1247_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
else
{
return v___x_1249_;
}
}
v___jp_1258_:
{
if (lean_obj_tag(v___y_1259_) == 0)
{
lean_object* v_a_1260_; 
v_a_1260_ = lean_ctor_get(v___y_1259_, 0);
lean_inc(v_a_1260_);
lean_dec_ref_known(v___y_1259_, 1);
v_a_1247_ = v_a_1260_;
goto v___jp_1246_;
}
else
{
lean_dec_ref(v_e_1238_);
return v___y_1259_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1308_ = lean_box(0);
v___x_1309_ = lean_unsigned_to_nat(16u);
v___x_1310_ = lean_mk_array(v___x_1309_, v___x_1308_);
return v___x_1310_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0);
v___x_1312_ = lean_unsigned_to_nat(0u);
v___x_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
lean_ctor_set(v___x_1313_, 1, v___x_1311_);
return v___x_1313_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1);
v___x_1315_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1315_, 0, lean_box(0));
lean_closure_set(v___x_1315_, 1, lean_box(0));
lean_closure_set(v___x_1315_, 2, v___x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(lean_object* v_input_1316_, lean_object* v_fn_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v_a_1326_; lean_object* v___x_1327_; 
v___x_1324_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2);
v___x_1325_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1324_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
lean_dec_ref(v___x_1325_);
v___x_1327_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1317_, v_input_1316_, v_a_1326_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec_ref_known(v___x_1327_, 1);
v___x_1329_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1329_, 0, lean_box(0));
lean_closure_set(v___x_1329_, 1, lean_box(0));
lean_closure_set(v___x_1329_, 2, v_a_1326_);
v___x_1330_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1329_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1337_ == 0)
{
lean_object* v_unused_1338_; 
v_unused_1338_ = lean_ctor_get(v___x_1330_, 0);
lean_dec(v_unused_1338_);
v___x_1332_ = v___x_1330_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_dec(v___x_1330_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v_a_1328_);
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1328_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
else
{
lean_dec(v_a_1326_);
return v___x_1327_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___boxed(lean_object* v_input_1339_, lean_object* v_fn_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1339_, v_fn_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(lean_object* v_input_1348_, lean_object* v_fn_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v___f_1356_; lean_object* v___x_1357_; 
v___f_1356_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1356_, 0, v_fn_1349_);
v___x_1357_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1348_, v___f_1356_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___boxed(lean_object* v_input_1358_, lean_object* v_fn_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_input_1358_, v_fn_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(lean_object* v_fn_1367_, lean_object* v_x_1368_, lean_object* v_x_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
if (lean_obj_tag(v_x_1369_) == 0)
{
lean_object* v___x_1376_; 
lean_dec_ref(v_fn_1367_);
v___x_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1376_, 0, v_x_1368_);
return v___x_1376_;
}
else
{
lean_object* v_head_1377_; lean_object* v_tail_1378_; lean_object* v_type_1379_; lean_object* v___x_1380_; 
v_head_1377_ = lean_ctor_get(v_x_1369_, 0);
lean_inc(v_head_1377_);
v_tail_1378_ = lean_ctor_get(v_x_1369_, 1);
lean_inc(v_tail_1378_);
lean_dec_ref_known(v_x_1369_, 2);
v_type_1379_ = lean_ctor_get(v_head_1377_, 1);
lean_inc_ref(v_type_1379_);
lean_dec(v_head_1377_);
lean_inc_ref(v_fn_1367_);
v___x_1380_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1379_, v_fn_1367_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_a_1381_);
lean_dec_ref_known(v___x_1380_, 1);
v_x_1368_ = v_a_1381_;
v_x_1369_ = v_tail_1378_;
goto _start;
}
else
{
lean_dec(v_tail_1378_);
lean_dec_ref(v_fn_1367_);
return v___x_1380_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4___boxed(lean_object* v_fn_1383_, lean_object* v_x_1384_, lean_object* v_x_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1383_, v_x_1384_, v_x_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(lean_object* v_fn_1393_, lean_object* v_x_1394_, lean_object* v_x_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
if (lean_obj_tag(v_x_1395_) == 0)
{
lean_object* v___x_1402_; 
lean_dec_ref(v_fn_1393_);
v___x_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1402_, 0, v_x_1394_);
return v___x_1402_;
}
else
{
lean_object* v_head_1403_; lean_object* v_tail_1404_; lean_object* v___y_1406_; lean_object* v_type_1409_; lean_object* v_ctors_1410_; lean_object* v___x_1411_; 
v_head_1403_ = lean_ctor_get(v_x_1395_, 0);
lean_inc(v_head_1403_);
v_tail_1404_ = lean_ctor_get(v_x_1395_, 1);
lean_inc(v_tail_1404_);
lean_dec_ref_known(v_x_1395_, 2);
v_type_1409_ = lean_ctor_get(v_head_1403_, 1);
lean_inc_ref(v_type_1409_);
v_ctors_1410_ = lean_ctor_get(v_head_1403_, 2);
lean_inc(v_ctors_1410_);
lean_dec(v_head_1403_);
lean_inc_ref(v_fn_1393_);
v___x_1411_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1409_, v_fn_1393_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; lean_object* v___x_1413_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref_known(v___x_1411_, 1);
lean_inc_ref(v_fn_1393_);
v___x_1413_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1393_, v_a_1412_, v_ctors_1410_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
v___y_1406_ = v___x_1413_;
goto v___jp_1405_;
}
else
{
lean_dec(v_ctors_1410_);
v___y_1406_ = v___x_1411_;
goto v___jp_1405_;
}
v___jp_1405_:
{
if (lean_obj_tag(v___y_1406_) == 0)
{
lean_object* v_a_1407_; 
v_a_1407_ = lean_ctor_get(v___y_1406_, 0);
lean_inc(v_a_1407_);
lean_dec_ref_known(v___y_1406_, 1);
v_x_1394_ = v_a_1407_;
v_x_1395_ = v_tail_1404_;
goto _start;
}
else
{
lean_dec(v_tail_1404_);
lean_dec_ref(v_fn_1393_);
return v___y_1406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6___boxed(lean_object* v_fn_1414_, lean_object* v_x_1415_, lean_object* v_x_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1414_, v_x_1415_, v_x_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(lean_object* v_fn_1424_, lean_object* v_x_1425_, lean_object* v_x_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
if (lean_obj_tag(v_x_1426_) == 0)
{
lean_object* v___x_1433_; 
lean_dec_ref(v_fn_1424_);
v___x_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1433_, 0, v_x_1425_);
return v___x_1433_;
}
else
{
lean_object* v_head_1434_; lean_object* v_tail_1435_; lean_object* v___y_1437_; lean_object* v_toConstantVal_1440_; lean_object* v_value_1441_; lean_object* v_type_1442_; lean_object* v___x_1443_; 
v_head_1434_ = lean_ctor_get(v_x_1426_, 0);
lean_inc(v_head_1434_);
v_tail_1435_ = lean_ctor_get(v_x_1426_, 1);
lean_inc(v_tail_1435_);
lean_dec_ref_known(v_x_1426_, 2);
v_toConstantVal_1440_ = lean_ctor_get(v_head_1434_, 0);
lean_inc_ref(v_toConstantVal_1440_);
v_value_1441_ = lean_ctor_get(v_head_1434_, 1);
lean_inc_ref(v_value_1441_);
lean_dec(v_head_1434_);
v_type_1442_ = lean_ctor_get(v_toConstantVal_1440_, 2);
lean_inc_ref(v_type_1442_);
lean_dec_ref(v_toConstantVal_1440_);
lean_inc_ref(v_fn_1424_);
v___x_1443_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1442_, v_fn_1424_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v___x_1444_; 
lean_dec_ref_known(v___x_1443_, 1);
lean_inc_ref(v_fn_1424_);
v___x_1444_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1441_, v_fn_1424_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
v___y_1437_ = v___x_1444_;
goto v___jp_1436_;
}
else
{
lean_dec_ref(v_value_1441_);
v___y_1437_ = v___x_1443_;
goto v___jp_1436_;
}
v___jp_1436_:
{
if (lean_obj_tag(v___y_1437_) == 0)
{
lean_object* v_a_1438_; 
v_a_1438_ = lean_ctor_get(v___y_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref_known(v___y_1437_, 1);
v_x_1425_ = v_a_1438_;
v_x_1426_ = v_tail_1435_;
goto _start;
}
else
{
lean_dec(v_tail_1435_);
lean_dec_ref(v_fn_1424_);
return v___y_1437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1445_, lean_object* v_x_1446_, lean_object* v_x_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1445_, v_x_1446_, v_x_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(lean_object* v_fn_1455_, lean_object* v_d_1456_, lean_object* v_a_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
switch(lean_obj_tag(v_d_1456_))
{
case 0:
{
lean_object* v_val_1464_; lean_object* v_toConstantVal_1465_; lean_object* v_type_1466_; lean_object* v___x_1467_; 
v_val_1464_ = lean_ctor_get(v_d_1456_, 0);
lean_inc_ref(v_val_1464_);
lean_dec_ref_known(v_d_1456_, 1);
v_toConstantVal_1465_ = lean_ctor_get(v_val_1464_, 0);
lean_inc_ref(v_toConstantVal_1465_);
lean_dec_ref(v_val_1464_);
v_type_1466_ = lean_ctor_get(v_toConstantVal_1465_, 2);
lean_inc_ref(v_type_1466_);
lean_dec_ref(v_toConstantVal_1465_);
v___x_1467_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1466_, v_fn_1455_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
return v___x_1467_;
}
case 4:
{
lean_object* v___x_1468_; 
lean_dec_ref(v_fn_1455_);
v___x_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1468_, 0, v_a_1457_);
return v___x_1468_;
}
case 5:
{
lean_object* v_defns_1469_; lean_object* v___x_1470_; 
v_defns_1469_ = lean_ctor_get(v_d_1456_, 0);
lean_inc(v_defns_1469_);
lean_dec_ref_known(v_d_1456_, 1);
v___x_1470_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1455_, v_a_1457_, v_defns_1469_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
return v___x_1470_;
}
case 6:
{
lean_object* v_types_1471_; lean_object* v___x_1472_; 
v_types_1471_ = lean_ctor_get(v_d_1456_, 2);
lean_inc(v_types_1471_);
lean_dec_ref_known(v_d_1456_, 3);
v___x_1472_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1455_, v_a_1457_, v_types_1471_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
return v___x_1472_;
}
default: 
{
lean_object* v_val_1473_; lean_object* v_toConstantVal_1474_; lean_object* v_value_1475_; lean_object* v_type_1476_; lean_object* v___x_1477_; 
v_val_1473_ = lean_ctor_get(v_d_1456_, 0);
lean_inc_ref(v_val_1473_);
lean_dec(v_d_1456_);
v_toConstantVal_1474_ = lean_ctor_get(v_val_1473_, 0);
lean_inc_ref(v_toConstantVal_1474_);
v_value_1475_ = lean_ctor_get(v_val_1473_, 1);
lean_inc_ref(v_value_1475_);
lean_dec_ref(v_val_1473_);
v_type_1476_ = lean_ctor_get(v_toConstantVal_1474_, 2);
lean_inc_ref(v_type_1476_);
lean_dec_ref(v_toConstantVal_1474_);
lean_inc_ref(v_fn_1455_);
v___x_1477_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1476_, v_fn_1455_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v___x_1478_; 
lean_dec_ref_known(v___x_1477_, 1);
v___x_1478_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1475_, v_fn_1455_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
return v___x_1478_;
}
else
{
lean_dec_ref(v_value_1475_);
lean_dec_ref(v_fn_1455_);
return v___x_1477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2___boxed(lean_object* v_fn_1479_, lean_object* v_d_1480_, lean_object* v_a_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1479_, v_d_1480_, v_a_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(lean_object* v_decl_1489_, lean_object* v_fn_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = lean_box(0);
v___x_1498_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1490_, v_decl_1489_, v___x_1497_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1___boxed(lean_object* v_decl_1499_, lean_object* v_fn_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1499_, v_fn_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
return v_res_1507_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__2(void){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__0, &l_Lean_snapshotEnvLinterOptions___closed__0_once, _init_l_Lean_snapshotEnvLinterOptions___closed__0);
v___x_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
return v___x_1512_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__3(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1513_ = lean_box(1);
v___x_1514_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3);
v___x_1515_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1516_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
lean_ctor_set(v___x_1516_, 1, v___x_1514_);
lean_ctor_set(v___x_1516_, 2, v___x_1513_);
return v___x_1516_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__4(void){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1517_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1518_ = lean_unsigned_to_nat(0u);
v___x_1519_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1518_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
lean_ctor_set(v___x_1519_, 2, v___x_1518_);
lean_ctor_set(v___x_1519_, 3, v___x_1518_);
lean_ctor_set(v___x_1519_, 4, v___x_1517_);
lean_ctor_set(v___x_1519_, 5, v___x_1517_);
lean_ctor_set(v___x_1519_, 6, v___x_1517_);
lean_ctor_set(v___x_1519_, 7, v___x_1517_);
lean_ctor_set(v___x_1519_, 8, v___x_1517_);
lean_ctor_set(v___x_1519_, 9, v___x_1517_);
lean_ctor_set(v___x_1519_, 10, v___x_1517_);
return v___x_1519_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__5(void){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1521_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
lean_ctor_set(v___x_1521_, 2, v___x_1520_);
lean_ctor_set(v___x_1521_, 3, v___x_1520_);
lean_ctor_set(v___x_1521_, 4, v___x_1520_);
lean_ctor_set(v___x_1521_, 5, v___x_1520_);
return v___x_1521_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__6(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
lean_ctor_set(v___x_1523_, 1, v___x_1522_);
lean_ctor_set(v___x_1523_, 2, v___x_1522_);
lean_ctor_set(v___x_1523_, 3, v___x_1522_);
lean_ctor_set(v___x_1523_, 4, v___x_1522_);
return v___x_1523_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__7(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1524_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__6, &l_Lean_warnIfUsesSorry___closed__6_once, _init_l_Lean_warnIfUsesSorry___closed__6);
v___x_1525_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3);
v___x_1526_ = lean_box(1);
v___x_1527_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__5, &l_Lean_warnIfUsesSorry___closed__5_once, _init_l_Lean_warnIfUsesSorry___closed__5);
v___x_1528_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__4, &l_Lean_warnIfUsesSorry___closed__4_once, _init_l_Lean_warnIfUsesSorry___closed__4);
v___x_1529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
lean_ctor_set(v___x_1529_, 1, v___x_1527_);
lean_ctor_set(v___x_1529_, 2, v___x_1526_);
lean_ctor_set(v___x_1529_, 3, v___x_1525_);
lean_ctor_set(v___x_1529_, 4, v___x_1524_);
return v___x_1529_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__11(void){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__10));
v___x_1535_ = l_Lean_stringToMessageData(v___x_1534_);
return v___x_1535_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__13(void){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__12));
v___x_1538_ = l_Lean_stringToMessageData(v___x_1537_);
return v___x_1538_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__15(void){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__14));
v___x_1541_ = l_Lean_stringToMessageData(v___x_1540_);
return v___x_1541_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__16(void){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1542_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__15, &l_Lean_warnIfUsesSorry___closed__15_once, _init_l_Lean_warnIfUsesSorry___closed__15);
v___x_1543_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__9));
v___x_1544_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
lean_ctor_set(v___x_1544_, 1, v___x_1542_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry(lean_object* v_decl_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; 
v___x_1552_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1549_);
v___x_1553_ = l_Lean_warn_sorry;
v___x_1554_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_1552_, v___x_1553_);
lean_dec_ref(v___x_1552_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
lean_dec(v_decl_1548_);
v___x_1555_ = lean_box(0);
v___x_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
return v___x_1556_;
}
else
{
lean_object* v___f_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v_messages_1563_; uint8_t v___x_1564_; 
v___f_1557_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__0));
v___x_1558_ = lean_box(1);
v___x_1559_ = lean_st_ref_get(v_a_1550_);
v_messages_1563_ = lean_ctor_get(v___x_1559_, 7);
lean_inc_ref(v_messages_1563_);
lean_dec(v___x_1559_);
v___x_1564_ = l_Lean_MessageLog_hasErrors(v_messages_1563_);
lean_dec_ref(v_messages_1563_);
if (v___x_1564_ == 0)
{
if (v___x_1554_ == 0)
{
lean_dec(v_decl_1548_);
goto v___jp_1560_;
}
else
{
uint8_t v___x_1565_; 
v___x_1565_ = l_Lean_Declaration_hasSorry(v_decl_1548_);
if (v___x_1565_ == 0)
{
lean_dec(v_decl_1548_);
goto v___jp_1560_;
}
else
{
lean_object* v___x_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; uint8_t v___x_1569_; uint8_t v___x_1570_; lean_object* v___x_1571_; uint64_t v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1566_ = lean_unsigned_to_nat(0u);
v___x_1567_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__1));
v___x_1568_ = 1;
v___x_1569_ = 0;
v___x_1570_ = 2;
v___x_1571_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_1571_, 0, v___x_1564_);
lean_ctor_set_uint8(v___x_1571_, 1, v___x_1564_);
lean_ctor_set_uint8(v___x_1571_, 2, v___x_1564_);
lean_ctor_set_uint8(v___x_1571_, 3, v___x_1564_);
lean_ctor_set_uint8(v___x_1571_, 4, v___x_1564_);
lean_ctor_set_uint8(v___x_1571_, 5, v___x_1565_);
lean_ctor_set_uint8(v___x_1571_, 6, v___x_1565_);
lean_ctor_set_uint8(v___x_1571_, 7, v___x_1564_);
lean_ctor_set_uint8(v___x_1571_, 8, v___x_1565_);
lean_ctor_set_uint8(v___x_1571_, 9, v___x_1568_);
lean_ctor_set_uint8(v___x_1571_, 10, v___x_1569_);
lean_ctor_set_uint8(v___x_1571_, 11, v___x_1565_);
lean_ctor_set_uint8(v___x_1571_, 12, v___x_1565_);
lean_ctor_set_uint8(v___x_1571_, 13, v___x_1565_);
lean_ctor_set_uint8(v___x_1571_, 14, v___x_1570_);
lean_ctor_set_uint8(v___x_1571_, 15, v___x_1565_);
lean_ctor_set_uint8(v___x_1571_, 16, v___x_1565_);
lean_ctor_set_uint8(v___x_1571_, 17, v___x_1565_);
lean_ctor_set_uint8(v___x_1571_, 18, v___x_1565_);
lean_ctor_set_uint8(v___x_1571_, 19, v___x_1564_);
v___x_1572_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1571_);
v___x_1573_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1573_, 0, v___x_1571_);
lean_ctor_set_uint64(v___x_1573_, sizeof(void*)*1, v___x_1572_);
v___x_1574_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__3, &l_Lean_warnIfUsesSorry___closed__3_once, _init_l_Lean_warnIfUsesSorry___closed__3);
v___x_1575_ = lean_box(0);
v___x_1576_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1576_, 0, v___x_1573_);
lean_ctor_set(v___x_1576_, 1, v___x_1558_);
lean_ctor_set(v___x_1576_, 2, v___x_1574_);
lean_ctor_set(v___x_1576_, 3, v___x_1567_);
lean_ctor_set(v___x_1576_, 4, v___x_1575_);
lean_ctor_set(v___x_1576_, 5, v___x_1566_);
lean_ctor_set(v___x_1576_, 6, v___x_1575_);
lean_ctor_set_uint8(v___x_1576_, sizeof(void*)*7, v___x_1564_);
lean_ctor_set_uint8(v___x_1576_, sizeof(void*)*7 + 1, v___x_1564_);
lean_ctor_set_uint8(v___x_1576_, sizeof(void*)*7 + 2, v___x_1564_);
lean_ctor_set_uint8(v___x_1576_, sizeof(void*)*7 + 3, v___x_1554_);
v___x_1577_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__7, &l_Lean_warnIfUsesSorry___closed__7_once, _init_l_Lean_warnIfUsesSorry___closed__7);
v___x_1578_ = lean_st_mk_ref(v___x_1577_);
v___x_1579_ = lean_st_mk_ref(v___x_1567_);
v___x_1580_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1548_, v___f_1557_, v___x_1579_, v___x_1576_, v___x_1578_, v_a_1549_, v_a_1550_);
lean_dec_ref_known(v___x_1576_, 7);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v_val_1584_; lean_object* v___x_1606_; size_t v_sz_1607_; size_t v___x_1608_; lean_object* v___x_1609_; lean_object* v_fst_1610_; 
lean_dec_ref_known(v___x_1580_, 1);
v___x_1581_ = lean_st_ref_get(v___x_1579_);
lean_dec(v___x_1579_);
v___x_1582_ = lean_st_ref_get(v___x_1578_);
lean_dec(v___x_1578_);
lean_dec(v___x_1582_);
v___x_1606_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__17));
v_sz_1607_ = lean_array_size(v___x_1581_);
v___x_1608_ = ((size_t)0ULL);
v___x_1609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v___x_1581_, v_sz_1607_, v___x_1608_, v___x_1606_);
v_fst_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_fst_1610_);
lean_dec_ref(v___x_1609_);
if (lean_obj_tag(v_fst_1610_) == 0)
{
goto v___jp_1600_;
}
else
{
lean_object* v_val_1611_; 
v_val_1611_ = lean_ctor_get(v_fst_1610_, 0);
lean_inc(v_val_1611_);
lean_dec_ref_known(v_fst_1610_, 1);
if (lean_obj_tag(v_val_1611_) == 0)
{
goto v___jp_1600_;
}
else
{
lean_object* v_val_1612_; 
lean_dec(v___x_1581_);
v_val_1612_ = lean_ctor_get(v_val_1611_, 0);
lean_inc(v_val_1612_);
lean_dec_ref_known(v_val_1611_, 1);
v_val_1584_ = v_val_1612_;
goto v___jp_1583_;
}
}
v___jp_1583_:
{
lean_object* v_snd_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1598_; 
v_snd_1585_ = lean_ctor_get(v_val_1584_, 1);
v_isSharedCheck_1598_ = !lean_is_exclusive(v_val_1584_);
if (v_isSharedCheck_1598_ == 0)
{
lean_object* v_unused_1599_; 
v_unused_1599_ = lean_ctor_get(v_val_1584_, 0);
lean_dec(v_unused_1599_);
v___x_1587_ = v_val_1584_;
v_isShared_1588_ = v_isSharedCheck_1598_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_snd_1585_);
lean_dec(v_val_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1598_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1592_; 
v___x_1589_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__9));
v___x_1590_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__11, &l_Lean_warnIfUsesSorry___closed__11_once, _init_l_Lean_warnIfUsesSorry___closed__11);
if (v_isShared_1588_ == 0)
{
lean_ctor_set_tag(v___x_1587_, 7);
lean_ctor_set(v___x_1587_, 0, v___x_1590_);
v___x_1592_ = v___x_1587_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1590_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_snd_1585_);
v___x_1592_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1593_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__13, &l_Lean_warnIfUsesSorry___closed__13_once, _init_l_Lean_warnIfUsesSorry___closed__13);
v___x_1594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1592_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1589_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1595_, v_a_1549_, v_a_1550_);
return v___x_1596_;
}
}
}
v___jp_1600_:
{
lean_object* v___x_1601_; uint8_t v___x_1602_; 
v___x_1601_ = lean_array_get_size(v___x_1581_);
v___x_1602_ = lean_nat_dec_lt(v___x_1566_, v___x_1601_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
lean_dec(v___x_1581_);
v___x_1603_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__16, &l_Lean_warnIfUsesSorry___closed__16_once, _init_l_Lean_warnIfUsesSorry___closed__16);
v___x_1604_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1603_, v_a_1549_, v_a_1550_);
return v___x_1604_;
}
else
{
lean_object* v___x_1605_; 
v___x_1605_ = lean_array_fget(v___x_1581_, v___x_1566_);
lean_dec(v___x_1581_);
v_val_1584_ = v___x_1605_;
goto v___jp_1583_;
}
}
}
else
{
lean_dec(v___x_1579_);
lean_dec(v___x_1578_);
return v___x_1580_;
}
}
}
}
else
{
lean_dec(v_decl_1548_);
goto v___jp_1560_;
}
v___jp_1560_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = lean_box(0);
v___x_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
return v___x_1562_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___boxed(lean_object* v_decl_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_Lean_warnIfUsesSorry(v_decl_1613_, v_a_1614_, v_a_1615_);
lean_dec(v_a_1615_);
lean_dec_ref(v_a_1614_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1618_, lean_object* v_m_1619_, lean_object* v_a_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1619_, v_a_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1622_, lean_object* v_m_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(v_00_u03b2_1622_, v_m_1623_, v_a_1624_);
lean_dec_ref(v_a_1624_);
lean_dec_ref(v_m_1623_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_1626_, lean_object* v_m_1627_, lean_object* v_a_1628_, lean_object* v_b_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_m_1627_, v_a_1628_, v_b_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_1631_, lean_object* v_a_1632_, lean_object* v_x_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1632_, v_x_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1635_, lean_object* v_a_1636_, lean_object* v_x_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(v_00_u03b2_1635_, v_a_1636_, v_x_1637_);
lean_dec(v_x_1637_);
lean_dec_ref(v_a_1636_);
return v_res_1638_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(lean_object* v_00_u03b2_1639_, lean_object* v_a_1640_, lean_object* v_x_1641_){
_start:
{
uint8_t v___x_1642_; 
v___x_1642_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1640_, v_x_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___boxed(lean_object* v_00_u03b2_1643_, lean_object* v_a_1644_, lean_object* v_x_1645_){
_start:
{
uint8_t v_res_1646_; lean_object* v_r_1647_; 
v_res_1646_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(v_00_u03b2_1643_, v_a_1644_, v_x_1645_);
lean_dec(v_x_1645_);
lean_dec_ref(v_a_1644_);
v_r_1647_ = lean_box(v_res_1646_);
return v_r_1647_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17(lean_object* v_00_u03b2_1648_, lean_object* v_data_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_data_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18(lean_object* v_00_u03b2_1651_, lean_object* v_a_1652_, lean_object* v_b_1653_, lean_object* v_x_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1652_, v_b_1653_, v_x_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(lean_object* v_00_u03b1_1656_, lean_object* v_name_1657_, uint8_t v_bi_1658_, lean_object* v_type_1659_, lean_object* v_k_1660_, uint8_t v_kind_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_1657_, v_bi_1658_, v_type_1659_, v_k_1660_, v_kind_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___boxed(lean_object* v_00_u03b1_1670_, lean_object* v_name_1671_, lean_object* v_bi_1672_, lean_object* v_type_1673_, lean_object* v_k_1674_, lean_object* v_kind_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
uint8_t v_bi_boxed_1683_; uint8_t v_kind_boxed_1684_; lean_object* v_res_1685_; 
v_bi_boxed_1683_ = lean_unbox(v_bi_1672_);
v_kind_boxed_1684_ = lean_unbox(v_kind_1675_);
v_res_1685_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(v_00_u03b1_1670_, v_name_1671_, v_bi_boxed_1683_, v_type_1673_, v_k_1674_, v_kind_boxed_1684_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec(v___y_1676_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(lean_object* v_00_u03b1_1686_, lean_object* v_name_1687_, lean_object* v_type_1688_, lean_object* v_val_1689_, lean_object* v_k_1690_, uint8_t v_nondep_1691_, uint8_t v_kind_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_1687_, v_type_1688_, v_val_1689_, v_k_1690_, v_nondep_1691_, v_kind_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___boxed(lean_object* v_00_u03b1_1701_, lean_object* v_name_1702_, lean_object* v_type_1703_, lean_object* v_val_1704_, lean_object* v_k_1705_, lean_object* v_nondep_1706_, lean_object* v_kind_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
uint8_t v_nondep_boxed_1715_; uint8_t v_kind_boxed_1716_; lean_object* v_res_1717_; 
v_nondep_boxed_1715_ = lean_unbox(v_nondep_1706_);
v_kind_boxed_1716_ = lean_unbox(v_kind_1707_);
v_res_1717_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(v_00_u03b1_1701_, v_name_1702_, v_type_1703_, v_val_1704_, v_k_1705_, v_nondep_boxed_1715_, v_kind_boxed_1716_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec(v___y_1708_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18(lean_object* v_00_u03b2_1718_, lean_object* v_i_1719_, lean_object* v_source_1720_, lean_object* v_target_1721_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v_i_1719_, v_source_1720_, v_target_1721_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22(lean_object* v_00_u03b2_1723_, lean_object* v_x_1724_, lean_object* v_x_1725_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_x_1724_, v_x_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1776_; uint8_t v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1776_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1777_ = 0;
v___x_1778_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__20_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1779_ = l_Lean_registerTraceClass(v___x_1776_, v___x_1777_, v___x_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2____boxed(lean_object* v_a_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_();
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(lean_object* v_env_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v___x_1785_; lean_object* v_nextMacroScope_1786_; lean_object* v_ngen_1787_; lean_object* v_auxDeclNGen_1788_; lean_object* v_traceState_1789_; lean_object* v_recordedDeps_1790_; lean_object* v_messages_1791_; lean_object* v_infoState_1792_; lean_object* v_snapshotTasks_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1804_; 
v___x_1785_ = lean_st_ref_take(v___y_1783_);
v_nextMacroScope_1786_ = lean_ctor_get(v___x_1785_, 1);
v_ngen_1787_ = lean_ctor_get(v___x_1785_, 2);
v_auxDeclNGen_1788_ = lean_ctor_get(v___x_1785_, 3);
v_traceState_1789_ = lean_ctor_get(v___x_1785_, 4);
v_recordedDeps_1790_ = lean_ctor_get(v___x_1785_, 6);
v_messages_1791_ = lean_ctor_get(v___x_1785_, 7);
v_infoState_1792_ = lean_ctor_get(v___x_1785_, 8);
v_snapshotTasks_1793_ = lean_ctor_get(v___x_1785_, 9);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1804_ == 0)
{
lean_object* v_unused_1805_; lean_object* v_unused_1806_; 
v_unused_1805_ = lean_ctor_get(v___x_1785_, 5);
lean_dec(v_unused_1805_);
v_unused_1806_ = lean_ctor_get(v___x_1785_, 0);
lean_dec(v_unused_1806_);
v___x_1795_ = v___x_1785_;
v_isShared_1796_ = v_isSharedCheck_1804_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_snapshotTasks_1793_);
lean_inc(v_infoState_1792_);
lean_inc(v_messages_1791_);
lean_inc(v_recordedDeps_1790_);
lean_inc(v_traceState_1789_);
lean_inc(v_auxDeclNGen_1788_);
lean_inc(v_ngen_1787_);
lean_inc(v_nextMacroScope_1786_);
lean_dec(v___x_1785_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1804_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1800_; 
v___x_1797_ = lean_box(0);
v___x_1798_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 5, v___x_1798_);
lean_ctor_set(v___x_1795_, 0, v_env_1782_);
v___x_1800_ = v___x_1795_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_env_1782_);
lean_ctor_set(v_reuseFailAlloc_1803_, 1, v_nextMacroScope_1786_);
lean_ctor_set(v_reuseFailAlloc_1803_, 2, v_ngen_1787_);
lean_ctor_set(v_reuseFailAlloc_1803_, 3, v_auxDeclNGen_1788_);
lean_ctor_set(v_reuseFailAlloc_1803_, 4, v_traceState_1789_);
lean_ctor_set(v_reuseFailAlloc_1803_, 5, v___x_1798_);
lean_ctor_set(v_reuseFailAlloc_1803_, 6, v_recordedDeps_1790_);
lean_ctor_set(v_reuseFailAlloc_1803_, 7, v_messages_1791_);
lean_ctor_set(v_reuseFailAlloc_1803_, 8, v_infoState_1792_);
lean_ctor_set(v_reuseFailAlloc_1803_, 9, v_snapshotTasks_1793_);
v___x_1800_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = lean_st_ref_put(v___y_1783_, v___x_1800_);
v___x_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1797_);
return v___x_1802_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg___boxed(lean_object* v_env_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1807_, v___y_1808_);
lean_dec(v___y_1808_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(lean_object* v_env_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1811_, v___y_1813_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___boxed(lean_object* v_env_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(v_env_1816_, v___y_1817_, v___y_1818_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
return v_res_1820_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1821_ = lean_box(0);
v___x_1822_ = l_Lean_interruptExceptionId;
v___x_1823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
lean_ctor_set(v___x_1823_, 1, v___x_1821_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg(){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v___y_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(lean_object* v_msg_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_ref_1833_; lean_object* v___x_1834_; lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1843_; 
v_ref_1833_ = lean_ctor_get(v___y_1830_, 2);
v___x_1834_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_1829_, v___y_1830_, v___y_1831_);
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1837_ = v___x_1834_;
v_isShared_1838_ = v_isSharedCheck_1843_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1843_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1839_; lean_object* v___x_1841_; 
lean_inc(v_ref_1833_);
v___x_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1839_, 0, v_ref_1833_);
lean_ctor_set(v___x_1839_, 1, v_a_1835_);
if (v_isShared_1838_ == 0)
{
lean_ctor_set_tag(v___x_1837_, 1);
lean_ctor_set(v___x_1837_, 0, v___x_1839_);
v___x_1841_ = v___x_1837_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msg_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_1844_, v___y_1845_, v___y_1846_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(lean_object* v_ex_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v___y_1854_; lean_object* v___y_1855_; 
if (lean_obj_tag(v_ex_1849_) == 16)
{
lean_object* v___x_1859_; lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
v___x_1859_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1859_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1859_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
else
{
v___y_1854_ = v___y_1850_;
v___y_1855_ = v___y_1851_;
goto v___jp_1853_;
}
v___jp_1853_:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1856_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1854_);
v___x_1857_ = l_Lean_Kernel_Exception_toMessageData(v_ex_1849_, v___x_1856_);
v___x_1858_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v___x_1857_, v___y_1854_, v___y_1855_);
return v___x_1858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg___boxed(lean_object* v_ex_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_1868_, v___y_1869_, v___y_1870_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(lean_object* v_x_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
if (lean_obj_tag(v_x_1873_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1878_; 
v_a_1877_ = lean_ctor_get(v_x_1873_, 0);
lean_inc(v_a_1877_);
lean_dec_ref_known(v_x_1873_, 1);
v___x_1878_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_a_1877_, v___y_1874_, v___y_1875_);
return v___x_1878_;
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
v_a_1879_ = lean_ctor_get(v_x_1873_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v_x_1873_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v_x_1873_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v_x_1873_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
lean_ctor_set_tag(v___x_1881_, 0);
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg___boxed(lean_object* v_x_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_1887_, v___y_1888_, v___y_1889_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
return v_res_1891_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = lean_unsigned_to_nat(1u);
v___x_1899_ = l_Lean_Level_ofNat(v___x_1898_);
return v___x_1899_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1900_ = lean_box(0);
v___x_1901_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3);
v___x_1902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
lean_ctor_set(v___x_1902_, 1, v___x_1900_);
return v___x_1902_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1903_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4);
v___x_1904_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2));
v___x_1905_ = l_Lean_mkConst(v___x_1904_, v___x_1903_);
return v___x_1905_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1906_ = lean_unsigned_to_nat(0u);
v___x_1907_ = l_Lean_Level_ofNat(v___x_1906_);
return v___x_1907_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6);
v___x_1909_ = l_Lean_mkSort(v___x_1908_);
return v___x_1909_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11(void){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1915_ = lean_box(0);
v___x_1916_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__10));
v___x_1917_ = l_Lean_mkConst(v___x_1916_, v___x_1915_);
return v___x_1917_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12(void){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1918_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11);
v___x_1919_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7);
v___x_1920_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5);
v___x_1921_ = l_Lean_mkAppB(v___x_1920_, v___x_1919_, v___x_1918_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(lean_object* v_as_x27_1927_, lean_object* v_b_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
if (lean_obj_tag(v_as_x27_1927_) == 0)
{
lean_object* v___x_1932_; 
v___x_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1932_, 0, v_b_1928_);
return v___x_1932_;
}
else
{
lean_object* v_head_1933_; lean_object* v_tail_1934_; lean_object* v___x_1935_; lean_object* v___y_1937_; uint8_t v___y_1938_; lean_object* v_a_1942_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; uint8_t v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v_toCold_1952_; lean_object* v_env_1953_; lean_object* v_cancelTk_x3f_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
lean_dec_ref(v_b_1928_);
v_head_1933_ = lean_ctor_get(v_as_x27_1927_, 0);
v_tail_1934_ = lean_ctor_get(v_as_x27_1927_, 1);
v___x_1935_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0));
v___x_1945_ = lean_box(0);
v___x_1946_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12);
lean_inc(v_head_1933_);
v___x_1947_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1947_, 0, v_head_1933_);
lean_ctor_set(v___x_1947_, 1, v___x_1945_);
lean_ctor_set(v___x_1947_, 2, v___x_1946_);
v___x_1948_ = 0;
v___x_1949_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1949_, 0, v___x_1947_);
lean_ctor_set_uint8(v___x_1949_, sizeof(void*)*1, v___x_1948_);
v___x_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
v___x_1951_ = lean_st_ref_get(v___y_1930_);
v_toCold_1952_ = lean_ctor_get(v___y_1929_, 0);
v_env_1953_ = lean_ctor_get(v___x_1951_, 0);
lean_inc_ref(v_env_1953_);
lean_dec(v___x_1951_);
v_cancelTk_x3f_1954_ = lean_ctor_get(v_toCold_1952_, 10);
v___x_1955_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1929_);
v___x_1956_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_1953_, v___x_1955_, v___x_1950_, v_cancelTk_x3f_1954_);
lean_dec_ref_known(v___x_1950_, 1);
lean_dec_ref(v___x_1955_);
v___x_1957_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_1956_, v___y_1929_, v___y_1930_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; lean_object* v___x_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1967_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref_known(v___x_1957_, 1);
v___x_1959_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_1958_, v___y_1930_);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1967_ == 0)
{
lean_object* v_unused_1968_; 
v_unused_1968_ = lean_ctor_get(v___x_1959_, 0);
lean_dec(v_unused_1968_);
v___x_1961_ = v___x_1959_;
v_isShared_1962_ = v_isSharedCheck_1967_;
goto v_resetjp_1960_;
}
else
{
lean_dec(v___x_1959_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1967_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1963_; lean_object* v___x_1965_; 
v___x_1963_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__14));
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 0, v___x_1963_);
v___x_1965_ = v___x_1961_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1963_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
else
{
lean_object* v_a_1969_; 
v_a_1969_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1969_);
lean_dec_ref_known(v___x_1957_, 1);
v_a_1942_ = v_a_1969_;
goto v___jp_1941_;
}
v___jp_1936_:
{
if (v___y_1938_ == 0)
{
lean_dec_ref(v___y_1937_);
v_as_x27_1927_ = v_tail_1934_;
v_b_1928_ = v___x_1935_;
goto _start;
}
else
{
lean_object* v___x_1940_; 
v___x_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1940_, 0, v___y_1937_);
return v___x_1940_;
}
}
v___jp_1941_:
{
uint8_t v___x_1943_; 
v___x_1943_ = l_Lean_Exception_isInterrupt(v_a_1942_);
if (v___x_1943_ == 0)
{
uint8_t v___x_1944_; 
lean_inc_ref(v_a_1942_);
v___x_1944_ = l_Lean_Exception_isRuntime(v_a_1942_);
v___y_1937_ = v_a_1942_;
v___y_1938_ = v___x_1944_;
goto v___jp_1936_;
}
else
{
v___y_1937_ = v_a_1942_;
v___y_1938_ = v___x_1943_;
goto v___jp_1936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___boxed(lean_object* v_as_x27_1970_, lean_object* v_b_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_1970_, v_b_1971_, v___y_1972_, v___y_1973_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v_as_x27_1970_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(lean_object* v_decl_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_){
_start:
{
lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_2009_; uint8_t v___y_2010_; lean_object* v_a_2013_; lean_object* v___y_2017_; uint8_t v___y_2018_; lean_object* v_a_2021_; 
switch(lean_obj_tag(v_decl_1976_))
{
case 1:
{
lean_object* v_val_2024_; lean_object* v_toConstantVal_2025_; uint8_t v___x_2026_; lean_object* v___x_2027_; lean_object* v_fallbackDecl_2028_; lean_object* v___x_2029_; lean_object* v_toCold_2030_; lean_object* v_env_2031_; lean_object* v_cancelTk_x3f_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v_val_2024_ = lean_ctor_get(v_decl_1976_, 0);
v_toConstantVal_2025_ = lean_ctor_get(v_val_2024_, 0);
v___x_2026_ = 0;
lean_inc_ref(v_toConstantVal_2025_);
v___x_2027_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2027_, 0, v_toConstantVal_2025_);
lean_ctor_set_uint8(v___x_2027_, sizeof(void*)*1, v___x_2026_);
v_fallbackDecl_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2028_, 0, v___x_2027_);
v___x_2029_ = lean_st_ref_get(v_a_1978_);
v_toCold_2030_ = lean_ctor_get(v_a_1977_, 0);
v_env_2031_ = lean_ctor_get(v___x_2029_, 0);
lean_inc_ref(v_env_2031_);
lean_dec(v___x_2029_);
v_cancelTk_x3f_2032_ = lean_ctor_get(v_toCold_2030_, 10);
v___x_2033_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1977_);
v___x_2034_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2031_, v___x_2033_, v_fallbackDecl_2028_, v_cancelTk_x3f_2032_);
lean_dec_ref_known(v_fallbackDecl_2028_, 1);
lean_dec_ref(v___x_2033_);
v___x_2035_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2034_, v_a_1977_, v_a_1978_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v_a_2036_; lean_object* v___x_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2045_; 
lean_dec_ref_known(v_decl_1976_, 1);
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
lean_inc(v_a_2036_);
lean_dec_ref_known(v___x_2035_, 1);
v___x_2037_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2036_, v_a_1978_);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2045_ == 0)
{
lean_object* v_unused_2046_; 
v_unused_2046_ = lean_ctor_get(v___x_2037_, 0);
lean_dec(v_unused_2046_);
v___x_2039_ = v___x_2037_;
v_isShared_2040_ = v_isSharedCheck_2045_;
goto v_resetjp_2038_;
}
else
{
lean_dec(v___x_2037_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2045_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2041_; lean_object* v___x_2043_; 
v___x_2041_ = lean_box(0);
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v___x_2041_);
v___x_2043_ = v___x_2039_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2041_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
else
{
lean_object* v_a_2047_; 
v_a_2047_ = lean_ctor_get(v___x_2035_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___x_2035_, 1);
v_a_2013_ = v_a_2047_;
goto v___jp_2012_;
}
}
case 2:
{
lean_object* v_val_2048_; lean_object* v_toConstantVal_2049_; uint8_t v___x_2050_; lean_object* v___x_2051_; lean_object* v_fallbackDecl_2052_; lean_object* v___x_2053_; lean_object* v_toCold_2054_; lean_object* v_env_2055_; lean_object* v_cancelTk_x3f_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v_val_2048_ = lean_ctor_get(v_decl_1976_, 0);
v_toConstantVal_2049_ = lean_ctor_get(v_val_2048_, 0);
v___x_2050_ = 0;
lean_inc_ref(v_toConstantVal_2049_);
v___x_2051_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2051_, 0, v_toConstantVal_2049_);
lean_ctor_set_uint8(v___x_2051_, sizeof(void*)*1, v___x_2050_);
v_fallbackDecl_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2052_, 0, v___x_2051_);
v___x_2053_ = lean_st_ref_get(v_a_1978_);
v_toCold_2054_ = lean_ctor_get(v_a_1977_, 0);
v_env_2055_ = lean_ctor_get(v___x_2053_, 0);
lean_inc_ref(v_env_2055_);
lean_dec(v___x_2053_);
v_cancelTk_x3f_2056_ = lean_ctor_get(v_toCold_2054_, 10);
v___x_2057_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1977_);
v___x_2058_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2055_, v___x_2057_, v_fallbackDecl_2052_, v_cancelTk_x3f_2056_);
lean_dec_ref_known(v_fallbackDecl_2052_, 1);
lean_dec_ref(v___x_2057_);
v___x_2059_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2058_, v_a_1977_, v_a_1978_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v_a_2060_; lean_object* v___x_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2069_; 
lean_dec_ref_known(v_decl_1976_, 1);
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
lean_inc(v_a_2060_);
lean_dec_ref_known(v___x_2059_, 1);
v___x_2061_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2060_, v_a_1978_);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2069_ == 0)
{
lean_object* v_unused_2070_; 
v_unused_2070_ = lean_ctor_get(v___x_2061_, 0);
lean_dec(v_unused_2070_);
v___x_2063_ = v___x_2061_;
v_isShared_2064_ = v_isSharedCheck_2069_;
goto v_resetjp_2062_;
}
else
{
lean_dec(v___x_2061_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2069_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2065_; lean_object* v___x_2067_; 
v___x_2065_ = lean_box(0);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 0, v___x_2065_);
v___x_2067_ = v___x_2063_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2065_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
else
{
lean_object* v_a_2071_; 
v_a_2071_ = lean_ctor_get(v___x_2059_, 0);
lean_inc(v_a_2071_);
lean_dec_ref_known(v___x_2059_, 1);
v_a_2021_ = v_a_2071_;
goto v___jp_2020_;
}
}
default: 
{
v___y_1981_ = v_a_1977_;
v___y_1982_ = v_a_1978_;
goto v___jp_1980_;
}
}
v___jp_1980_:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1983_ = l_Lean_Declaration_getNames(v_decl_1976_);
v___x_1984_ = lean_box(0);
v___x_1985_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0));
v___x_1986_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v___x_1983_, v___x_1985_, v___y_1981_, v___y_1982_);
lean_dec(v___x_1983_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1999_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1989_ = v___x_1986_;
v_isShared_1990_ = v_isSharedCheck_1999_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1986_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1999_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v_fst_1991_; 
v_fst_1991_ = lean_ctor_get(v_a_1987_, 0);
lean_inc(v_fst_1991_);
lean_dec(v_a_1987_);
if (lean_obj_tag(v_fst_1991_) == 0)
{
lean_object* v___x_1993_; 
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 0, v___x_1984_);
v___x_1993_ = v___x_1989_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1984_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
else
{
lean_object* v_val_1995_; lean_object* v___x_1997_; 
v_val_1995_ = lean_ctor_get(v_fst_1991_, 0);
lean_inc(v_val_1995_);
lean_dec_ref_known(v_fst_1991_, 1);
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 0, v_val_1995_);
v___x_1997_ = v___x_1989_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_val_1995_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
v_a_2000_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1986_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1986_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
v___jp_2008_:
{
if (v___y_2010_ == 0)
{
lean_dec_ref(v___y_2009_);
v___y_1981_ = v_a_1977_;
v___y_1982_ = v_a_1978_;
goto v___jp_1980_;
}
else
{
lean_object* v___x_2011_; 
lean_dec(v_decl_1976_);
v___x_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2011_, 0, v___y_2009_);
return v___x_2011_;
}
}
v___jp_2012_:
{
uint8_t v___x_2014_; 
v___x_2014_ = l_Lean_Exception_isInterrupt(v_a_2013_);
if (v___x_2014_ == 0)
{
uint8_t v___x_2015_; 
lean_inc_ref(v_a_2013_);
v___x_2015_ = l_Lean_Exception_isRuntime(v_a_2013_);
v___y_2009_ = v_a_2013_;
v___y_2010_ = v___x_2015_;
goto v___jp_2008_;
}
else
{
v___y_2009_ = v_a_2013_;
v___y_2010_ = v___x_2014_;
goto v___jp_2008_;
}
}
v___jp_2016_:
{
if (v___y_2018_ == 0)
{
lean_dec_ref(v___y_2017_);
v___y_1981_ = v_a_1977_;
v___y_1982_ = v_a_1978_;
goto v___jp_1980_;
}
else
{
lean_object* v___x_2019_; 
lean_dec(v_decl_1976_);
v___x_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2019_, 0, v___y_2017_);
return v___x_2019_;
}
}
v___jp_2020_:
{
uint8_t v___x_2022_; 
v___x_2022_ = l_Lean_Exception_isInterrupt(v_a_2021_);
if (v___x_2022_ == 0)
{
uint8_t v___x_2023_; 
lean_inc_ref(v_a_2021_);
v___x_2023_ = l_Lean_Exception_isRuntime(v_a_2021_);
v___y_2017_ = v_a_2021_;
v___y_2018_ = v___x_2023_;
goto v___jp_2016_;
}
else
{
v___y_2017_ = v_a_2021_;
v___y_2018_ = v___x_2022_;
goto v___jp_2016_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom___boxed(lean_object* v_decl_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2072_, v_a_2073_, v_a_2074_);
lean_dec(v_a_2074_);
lean_dec_ref(v_a_2073_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(lean_object* v_00_u03b1_2077_, lean_object* v_x_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
lean_object* v___x_2082_; 
v___x_2082_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_2078_, v___y_2079_, v___y_2080_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___boxed(lean_object* v_00_u03b1_2083_, lean_object* v_x_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(v_00_u03b1_2083_, v_x_2084_, v___y_2085_, v___y_2086_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(lean_object* v_as_2089_, lean_object* v_as_x27_2090_, lean_object* v_b_2091_, lean_object* v_a_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v___x_2096_; 
v___x_2096_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_2090_, v_b_2091_, v___y_2093_, v___y_2094_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___boxed(lean_object* v_as_2097_, lean_object* v_as_x27_2098_, lean_object* v_b_2099_, lean_object* v_a_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(v_as_2097_, v_as_x27_2098_, v_b_2099_, v_a_2100_, v___y_2101_, v___y_2102_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v_as_x27_2098_);
lean_dec(v_as_2097_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v___x_2109_; 
v___x_2109_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(v_00_u03b1_2110_, v___y_2111_, v___y_2112_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(lean_object* v_00_u03b1_2115_, lean_object* v_ex_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_2116_, v___y_2117_, v___y_2118_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2121_, lean_object* v_ex_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(v_00_u03b1_2121_, v_ex_2122_, v___y_2123_, v___y_2124_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2127_, lean_object* v_msg_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_2128_, v___y_2129_, v___y_2130_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2133_, lean_object* v_msg_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(v_00_u03b1_2133_, v_msg_2134_, v___y_2135_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
return v_res_2138_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2139_ = lean_unsigned_to_nat(32u);
v___x_2140_ = lean_mk_empty_array_with_capacity(v___x_2139_);
v___x_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2140_);
return v___x_2141_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2142_ = ((size_t)5ULL);
v___x_2143_ = lean_unsigned_to_nat(0u);
v___x_2144_ = lean_unsigned_to_nat(32u);
v___x_2145_ = lean_mk_empty_array_with_capacity(v___x_2144_);
v___x_2146_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0);
v___x_2147_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
lean_ctor_set(v___x_2147_, 1, v___x_2145_);
lean_ctor_set(v___x_2147_, 2, v___x_2143_);
lean_ctor_set(v___x_2147_, 3, v___x_2143_);
lean_ctor_set_usize(v___x_2147_, 4, v___x_2142_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(lean_object* v___y_2148_){
_start:
{
lean_object* v___x_2150_; lean_object* v_traceState_2151_; lean_object* v_traces_2152_; lean_object* v___x_2153_; lean_object* v_traceState_2154_; lean_object* v_env_2155_; lean_object* v_nextMacroScope_2156_; lean_object* v_ngen_2157_; lean_object* v_auxDeclNGen_2158_; lean_object* v_cache_2159_; lean_object* v_recordedDeps_2160_; lean_object* v_messages_2161_; lean_object* v_infoState_2162_; lean_object* v_snapshotTasks_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2182_; 
v___x_2150_ = lean_st_ref_get(v___y_2148_);
v_traceState_2151_ = lean_ctor_get(v___x_2150_, 4);
lean_inc_ref(v_traceState_2151_);
lean_dec(v___x_2150_);
v_traces_2152_ = lean_ctor_get(v_traceState_2151_, 0);
lean_inc_ref(v_traces_2152_);
lean_dec_ref(v_traceState_2151_);
v___x_2153_ = lean_st_ref_take(v___y_2148_);
v_traceState_2154_ = lean_ctor_get(v___x_2153_, 4);
v_env_2155_ = lean_ctor_get(v___x_2153_, 0);
v_nextMacroScope_2156_ = lean_ctor_get(v___x_2153_, 1);
v_ngen_2157_ = lean_ctor_get(v___x_2153_, 2);
v_auxDeclNGen_2158_ = lean_ctor_get(v___x_2153_, 3);
v_cache_2159_ = lean_ctor_get(v___x_2153_, 5);
v_recordedDeps_2160_ = lean_ctor_get(v___x_2153_, 6);
v_messages_2161_ = lean_ctor_get(v___x_2153_, 7);
v_infoState_2162_ = lean_ctor_get(v___x_2153_, 8);
v_snapshotTasks_2163_ = lean_ctor_get(v___x_2153_, 9);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2165_ = v___x_2153_;
v_isShared_2166_ = v_isSharedCheck_2182_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_snapshotTasks_2163_);
lean_inc(v_infoState_2162_);
lean_inc(v_messages_2161_);
lean_inc(v_recordedDeps_2160_);
lean_inc(v_cache_2159_);
lean_inc(v_traceState_2154_);
lean_inc(v_auxDeclNGen_2158_);
lean_inc(v_ngen_2157_);
lean_inc(v_nextMacroScope_2156_);
lean_inc(v_env_2155_);
lean_dec(v___x_2153_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2182_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
uint64_t v_tid_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2180_; 
v_tid_2167_ = lean_ctor_get_uint64(v_traceState_2154_, sizeof(void*)*1);
v_isSharedCheck_2180_ = !lean_is_exclusive(v_traceState_2154_);
if (v_isSharedCheck_2180_ == 0)
{
lean_object* v_unused_2181_; 
v_unused_2181_ = lean_ctor_get(v_traceState_2154_, 0);
lean_dec(v_unused_2181_);
v___x_2169_ = v_traceState_2154_;
v_isShared_2170_ = v_isSharedCheck_2180_;
goto v_resetjp_2168_;
}
else
{
lean_dec(v_traceState_2154_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2180_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2171_; lean_object* v___x_2173_; 
v___x_2171_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 0, v___x_2171_);
v___x_2173_ = v___x_2169_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2171_);
lean_ctor_set_uint64(v_reuseFailAlloc_2179_, sizeof(void*)*1, v_tid_2167_);
v___x_2173_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2175_; 
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 4, v___x_2173_);
v___x_2175_ = v___x_2165_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_env_2155_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_nextMacroScope_2156_);
lean_ctor_set(v_reuseFailAlloc_2178_, 2, v_ngen_2157_);
lean_ctor_set(v_reuseFailAlloc_2178_, 3, v_auxDeclNGen_2158_);
lean_ctor_set(v_reuseFailAlloc_2178_, 4, v___x_2173_);
lean_ctor_set(v_reuseFailAlloc_2178_, 5, v_cache_2159_);
lean_ctor_set(v_reuseFailAlloc_2178_, 6, v_recordedDeps_2160_);
lean_ctor_set(v_reuseFailAlloc_2178_, 7, v_messages_2161_);
lean_ctor_set(v_reuseFailAlloc_2178_, 8, v_infoState_2162_);
lean_ctor_set(v_reuseFailAlloc_2178_, 9, v_snapshotTasks_2163_);
v___x_2175_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = lean_st_ref_put(v___y_2148_, v___x_2175_);
v___x_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2177_, 0, v_traces_2152_);
return v___x_2177_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___boxed(lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2183_);
lean_dec(v___y_2183_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2187_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___boxed(lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(v___y_2190_, v___y_2191_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(lean_object* v_category_2194_, lean_object* v_opts_2195_, lean_object* v_act_2196_, lean_object* v_decl_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
lean_inc(v___y_2199_);
lean_inc_ref(v___y_2198_);
v___x_2201_ = lean_apply_2(v_act_2196_, v___y_2198_, v___y_2199_);
v___x_2202_ = l_Lean_profileitIOUnsafe___redArg(v_category_2194_, v_opts_2195_, v___x_2201_, v_decl_2197_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg___boxed(lean_object* v_category_2203_, lean_object* v_opts_2204_, lean_object* v_act_2205_, lean_object* v_decl_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v_category_2203_, v_opts_2204_, v_act_2205_, v_decl_2206_, v___y_2207_, v___y_2208_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec_ref(v_opts_2204_);
lean_dec_ref(v_category_2203_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(lean_object* v_00_u03b1_2211_, lean_object* v_category_2212_, lean_object* v_opts_2213_, lean_object* v_act_2214_, lean_object* v_decl_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v_category_2212_, v_opts_2213_, v_act_2214_, v_decl_2215_, v___y_2216_, v___y_2217_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___boxed(lean_object* v_00_u03b1_2220_, lean_object* v_category_2221_, lean_object* v_opts_2222_, lean_object* v_act_2223_, lean_object* v_decl_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(v_00_u03b1_2220_, v_category_2221_, v_opts_2222_, v_act_2223_, v_decl_2224_, v___y_2225_, v___y_2226_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec_ref(v_opts_2222_);
lean_dec_ref(v_category_2221_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
if (lean_obj_tag(v_a_2229_) == 0)
{
lean_object* v___x_2231_; 
v___x_2231_ = l_List_reverse___redArg(v_a_2230_);
return v___x_2231_;
}
else
{
lean_object* v_head_2232_; lean_object* v_tail_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2242_; 
v_head_2232_ = lean_ctor_get(v_a_2229_, 0);
v_tail_2233_ = lean_ctor_get(v_a_2229_, 1);
v_isSharedCheck_2242_ = !lean_is_exclusive(v_a_2229_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2235_ = v_a_2229_;
v_isShared_2236_ = v_isSharedCheck_2242_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_tail_2233_);
lean_inc(v_head_2232_);
lean_dec(v_a_2229_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2242_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2237_ = l_Lean_MessageData_ofName(v_head_2232_);
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 1, v_a_2230_);
lean_ctor_set(v___x_2235_, 0, v___x_2237_);
v___x_2239_ = v___x_2235_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2237_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_a_2230_);
v___x_2239_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
v_a_2229_ = v_tail_2233_;
v_a_2230_ = v___x_2239_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__0));
v___x_2245_ = l_Lean_stringToMessageData(v___x_2244_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(lean_object* v_decl_2246_, lean_object* v_x_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2251_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1);
v___x_2252_ = l_Lean_Declaration_getTopLevelNames(v_decl_2246_);
v___x_2253_ = lean_box(0);
v___x_2254_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2252_, v___x_2253_);
v___x_2255_ = l_Lean_MessageData_ofList(v___x_2254_);
v___x_2256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2251_);
lean_ctor_set(v___x_2256_, 1, v___x_2255_);
v___x_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed(lean_object* v_decl_2258_, lean_object* v_x_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(v_decl_2258_, v_x_2259_, v___y_2260_, v___y_2261_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec_ref(v_x_2259_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(size_t v_sz_2264_, size_t v_i_2265_, lean_object* v_bs_2266_){
_start:
{
uint8_t v___x_2267_; 
v___x_2267_ = lean_usize_dec_lt(v_i_2265_, v_sz_2264_);
if (v___x_2267_ == 0)
{
return v_bs_2266_;
}
else
{
lean_object* v_v_2268_; lean_object* v_msg_2269_; lean_object* v___x_2270_; lean_object* v_bs_x27_2271_; size_t v___x_2272_; size_t v___x_2273_; lean_object* v___x_2274_; 
v_v_2268_ = lean_array_uget_borrowed(v_bs_2266_, v_i_2265_);
v_msg_2269_ = lean_ctor_get(v_v_2268_, 1);
lean_inc_ref(v_msg_2269_);
v___x_2270_ = lean_unsigned_to_nat(0u);
v_bs_x27_2271_ = lean_array_uset(v_bs_2266_, v_i_2265_, v___x_2270_);
v___x_2272_ = ((size_t)1ULL);
v___x_2273_ = lean_usize_add(v_i_2265_, v___x_2272_);
v___x_2274_ = lean_array_uset(v_bs_x27_2271_, v_i_2265_, v_msg_2269_);
v_i_2265_ = v___x_2273_;
v_bs_2266_ = v___x_2274_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4___boxed(lean_object* v_sz_2276_, lean_object* v_i_2277_, lean_object* v_bs_2278_){
_start:
{
size_t v_sz_boxed_2279_; size_t v_i_boxed_2280_; lean_object* v_res_2281_; 
v_sz_boxed_2279_ = lean_unbox_usize(v_sz_2276_);
lean_dec(v_sz_2276_);
v_i_boxed_2280_ = lean_unbox_usize(v_i_2277_);
lean_dec(v_i_2277_);
v_res_2281_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(v_sz_boxed_2279_, v_i_boxed_2280_, v_bs_2278_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(lean_object* v_oldTraces_2282_, lean_object* v_data_2283_, lean_object* v_ref_2284_, lean_object* v_msg_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v_toCold_2289_; lean_object* v_currRecDepth_2290_; lean_object* v_ref_2291_; uint16_t v_optionFlags_2292_; uint8_t v_suppressElabErrors_2293_; uint8_t v_isRecordingDeps_2294_; lean_object* v_ref_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v_traceState_2298_; lean_object* v_traces_2299_; lean_object* v___x_2300_; size_t v_sz_2301_; size_t v___x_2302_; lean_object* v___x_2303_; lean_object* v_msg_2304_; lean_object* v___x_2305_; lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2344_; 
v_toCold_2289_ = lean_ctor_get(v___y_2286_, 0);
v_currRecDepth_2290_ = lean_ctor_get(v___y_2286_, 1);
v_ref_2291_ = lean_ctor_get(v___y_2286_, 2);
v_optionFlags_2292_ = lean_ctor_get_uint16(v___y_2286_, sizeof(void*)*3);
v_suppressElabErrors_2293_ = lean_ctor_get_uint8(v___y_2286_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2294_ = lean_ctor_get_uint8(v___y_2286_, sizeof(void*)*3 + 3);
v_ref_2295_ = l_Lean_replaceRef(v_ref_2284_, v_ref_2291_);
lean_inc(v_currRecDepth_2290_);
lean_inc_ref(v_toCold_2289_);
v___x_2296_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2296_, 0, v_toCold_2289_);
lean_ctor_set(v___x_2296_, 1, v_currRecDepth_2290_);
lean_ctor_set(v___x_2296_, 2, v_ref_2295_);
lean_ctor_set_uint16(v___x_2296_, sizeof(void*)*3, v_optionFlags_2292_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*3 + 2, v_suppressElabErrors_2293_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*3 + 3, v_isRecordingDeps_2294_);
v___x_2297_ = lean_st_ref_get(v___y_2287_);
v_traceState_2298_ = lean_ctor_get(v___x_2297_, 4);
lean_inc_ref(v_traceState_2298_);
lean_dec(v___x_2297_);
v_traces_2299_ = lean_ctor_get(v_traceState_2298_, 0);
lean_inc_ref(v_traces_2299_);
lean_dec_ref(v_traceState_2298_);
v___x_2300_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2299_);
lean_dec_ref(v_traces_2299_);
v_sz_2301_ = lean_array_size(v___x_2300_);
v___x_2302_ = ((size_t)0ULL);
v___x_2303_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(v_sz_2301_, v___x_2302_, v___x_2300_);
v_msg_2304_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2304_, 0, v_data_2283_);
lean_ctor_set(v_msg_2304_, 1, v_msg_2285_);
lean_ctor_set(v_msg_2304_, 2, v___x_2303_);
v___x_2305_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2304_, v___x_2296_, v___y_2287_);
lean_dec_ref_known(v___x_2296_, 3);
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2308_ = v___x_2305_;
v_isShared_2309_ = v_isSharedCheck_2344_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2305_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2344_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2310_; lean_object* v_traceState_2311_; lean_object* v_env_2312_; lean_object* v_nextMacroScope_2313_; lean_object* v_ngen_2314_; lean_object* v_auxDeclNGen_2315_; lean_object* v_cache_2316_; lean_object* v_recordedDeps_2317_; lean_object* v_messages_2318_; lean_object* v_infoState_2319_; lean_object* v_snapshotTasks_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2343_; 
v___x_2310_ = lean_st_ref_take(v___y_2287_);
v_traceState_2311_ = lean_ctor_get(v___x_2310_, 4);
v_env_2312_ = lean_ctor_get(v___x_2310_, 0);
v_nextMacroScope_2313_ = lean_ctor_get(v___x_2310_, 1);
v_ngen_2314_ = lean_ctor_get(v___x_2310_, 2);
v_auxDeclNGen_2315_ = lean_ctor_get(v___x_2310_, 3);
v_cache_2316_ = lean_ctor_get(v___x_2310_, 5);
v_recordedDeps_2317_ = lean_ctor_get(v___x_2310_, 6);
v_messages_2318_ = lean_ctor_get(v___x_2310_, 7);
v_infoState_2319_ = lean_ctor_get(v___x_2310_, 8);
v_snapshotTasks_2320_ = lean_ctor_get(v___x_2310_, 9);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2322_ = v___x_2310_;
v_isShared_2323_ = v_isSharedCheck_2343_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_snapshotTasks_2320_);
lean_inc(v_infoState_2319_);
lean_inc(v_messages_2318_);
lean_inc(v_recordedDeps_2317_);
lean_inc(v_cache_2316_);
lean_inc(v_traceState_2311_);
lean_inc(v_auxDeclNGen_2315_);
lean_inc(v_ngen_2314_);
lean_inc(v_nextMacroScope_2313_);
lean_inc(v_env_2312_);
lean_dec(v___x_2310_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2343_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
uint64_t v_tid_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2341_; 
v_tid_2324_ = lean_ctor_get_uint64(v_traceState_2311_, sizeof(void*)*1);
v_isSharedCheck_2341_ = !lean_is_exclusive(v_traceState_2311_);
if (v_isSharedCheck_2341_ == 0)
{
lean_object* v_unused_2342_; 
v_unused_2342_ = lean_ctor_get(v_traceState_2311_, 0);
lean_dec(v_unused_2342_);
v___x_2326_ = v_traceState_2311_;
v_isShared_2327_ = v_isSharedCheck_2341_;
goto v_resetjp_2325_;
}
else
{
lean_dec(v_traceState_2311_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2341_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2332_; 
v___x_2328_ = lean_box(0);
v___x_2329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2329_, 0, v_ref_2284_);
lean_ctor_set(v___x_2329_, 1, v_a_2306_);
v___x_2330_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2282_, v___x_2329_);
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 0, v___x_2330_);
v___x_2332_ = v___x_2326_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2330_);
lean_ctor_set_uint64(v_reuseFailAlloc_2340_, sizeof(void*)*1, v_tid_2324_);
v___x_2332_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
lean_object* v___x_2334_; 
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 4, v___x_2332_);
v___x_2334_ = v___x_2322_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_env_2312_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v_nextMacroScope_2313_);
lean_ctor_set(v_reuseFailAlloc_2339_, 2, v_ngen_2314_);
lean_ctor_set(v_reuseFailAlloc_2339_, 3, v_auxDeclNGen_2315_);
lean_ctor_set(v_reuseFailAlloc_2339_, 4, v___x_2332_);
lean_ctor_set(v_reuseFailAlloc_2339_, 5, v_cache_2316_);
lean_ctor_set(v_reuseFailAlloc_2339_, 6, v_recordedDeps_2317_);
lean_ctor_set(v_reuseFailAlloc_2339_, 7, v_messages_2318_);
lean_ctor_set(v_reuseFailAlloc_2339_, 8, v_infoState_2319_);
lean_ctor_set(v_reuseFailAlloc_2339_, 9, v_snapshotTasks_2320_);
v___x_2334_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
lean_object* v___x_2335_; lean_object* v___x_2337_; 
v___x_2335_ = lean_st_ref_put(v___y_2287_, v___x_2334_);
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 0, v___x_2328_);
v___x_2337_ = v___x_2308_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2328_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2___boxed(lean_object* v_oldTraces_2345_, lean_object* v_data_2346_, lean_object* v_ref_2347_, lean_object* v_msg_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_oldTraces_2345_, v_data_2346_, v_ref_2347_, v_msg_2348_, v___y_2349_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(lean_object* v_x_2353_){
_start:
{
if (lean_obj_tag(v_x_2353_) == 0)
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
v_a_2355_ = lean_ctor_get(v_x_2353_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v_x_2353_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v_x_2353_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v_x_2353_);
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
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
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
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
v_a_2363_ = lean_ctor_get(v_x_2353_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v_x_2353_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v_x_2353_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v_x_2353_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
lean_ctor_set_tag(v___x_2365_, 0);
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg___boxed(lean_object* v_x_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_x_2371_);
return v_res_2373_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(lean_object* v_e_2374_){
_start:
{
if (lean_obj_tag(v_e_2374_) == 0)
{
uint8_t v___x_2375_; 
v___x_2375_ = 2;
return v___x_2375_;
}
else
{
uint8_t v___x_2376_; 
v___x_2376_ = 0;
return v___x_2376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4___boxed(lean_object* v_e_2377_){
_start:
{
uint8_t v_res_2378_; lean_object* v_r_2379_; 
v_res_2378_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(v_e_2377_);
lean_dec_ref(v_e_2377_);
v_r_2379_ = lean_box(v_res_2378_);
return v_r_2379_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2380_; double v___x_2381_; 
v___x_2380_ = lean_unsigned_to_nat(0u);
v___x_2381_ = lean_float_of_nat(v___x_2380_);
return v___x_2381_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2(void){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2383_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__1));
v___x_2384_ = l_Lean_stringToMessageData(v___x_2383_);
return v___x_2384_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2385_; double v___x_2386_; 
v___x_2385_ = lean_unsigned_to_nat(1000u);
v___x_2386_ = lean_float_of_nat(v___x_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(lean_object* v_cls_2387_, uint8_t v_collapsed_2388_, lean_object* v_tag_2389_, lean_object* v_opts_2390_, uint8_t v_clsEnabled_2391_, lean_object* v_oldTraces_2392_, lean_object* v_msg_2393_, lean_object* v_resStartStop_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v_fst_2398_; lean_object* v_snd_2399_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v_data_2403_; lean_object* v_fst_2406_; lean_object* v_snd_2407_; lean_object* v___x_2408_; uint8_t v___x_2409_; lean_object* v___y_2411_; lean_object* v_a_2412_; uint8_t v___y_2427_; double v___y_2459_; 
v_fst_2398_ = lean_ctor_get(v_resStartStop_2394_, 0);
lean_inc(v_fst_2398_);
v_snd_2399_ = lean_ctor_get(v_resStartStop_2394_, 1);
lean_inc(v_snd_2399_);
lean_dec_ref(v_resStartStop_2394_);
v_fst_2406_ = lean_ctor_get(v_snd_2399_, 0);
lean_inc(v_fst_2406_);
v_snd_2407_ = lean_ctor_get(v_snd_2399_, 1);
lean_inc(v_snd_2407_);
lean_dec(v_snd_2399_);
v___x_2408_ = l_Lean_trace_profiler;
v___x_2409_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2390_, v___x_2408_);
if (v___x_2409_ == 0)
{
v___y_2427_ = v___x_2409_;
goto v___jp_2426_;
}
else
{
lean_object* v___x_2464_; uint8_t v___x_2465_; 
v___x_2464_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2465_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2390_, v___x_2464_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; lean_object* v___x_2467_; double v___x_2468_; double v___x_2469_; double v___x_2470_; 
v___x_2466_ = l_Lean_trace_profiler_threshold;
v___x_2467_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_2390_, v___x_2466_);
v___x_2468_ = lean_float_of_nat(v___x_2467_);
v___x_2469_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3);
v___x_2470_ = lean_float_div(v___x_2468_, v___x_2469_);
v___y_2459_ = v___x_2470_;
goto v___jp_2458_;
}
else
{
lean_object* v___x_2471_; lean_object* v___x_2472_; double v___x_2473_; 
v___x_2471_ = l_Lean_trace_profiler_threshold;
v___x_2472_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_2390_, v___x_2471_);
v___x_2473_ = lean_float_of_nat(v___x_2472_);
v___y_2459_ = v___x_2473_;
goto v___jp_2458_;
}
}
v___jp_2400_:
{
lean_object* v___x_2404_; 
lean_inc(v___y_2401_);
v___x_2404_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_oldTraces_2392_, v_data_2403_, v___y_2401_, v___y_2402_, v___y_2395_, v___y_2396_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v___x_2405_; 
lean_dec_ref_known(v___x_2404_, 1);
v___x_2405_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_fst_2398_);
return v___x_2405_;
}
else
{
lean_dec(v_fst_2398_);
return v___x_2404_;
}
}
v___jp_2410_:
{
uint8_t v_result_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; double v___x_2416_; lean_object* v_data_2417_; 
v_result_2413_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(v_fst_2398_);
v___x_2414_ = lean_box(v_result_2413_);
v___x_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
v___x_2416_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0);
lean_inc_ref(v_tag_2389_);
lean_inc_ref(v___x_2415_);
lean_inc(v_cls_2387_);
v_data_2417_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2417_, 0, v_cls_2387_);
lean_ctor_set(v_data_2417_, 1, v___x_2415_);
lean_ctor_set(v_data_2417_, 2, v_tag_2389_);
lean_ctor_set_float(v_data_2417_, sizeof(void*)*3, v___x_2416_);
lean_ctor_set_float(v_data_2417_, sizeof(void*)*3 + 8, v___x_2416_);
lean_ctor_set_uint8(v_data_2417_, sizeof(void*)*3 + 16, v_collapsed_2388_);
if (v___x_2409_ == 0)
{
lean_dec_ref_known(v___x_2415_, 1);
lean_dec(v_snd_2407_);
lean_dec(v_fst_2406_);
lean_dec_ref(v_tag_2389_);
lean_dec(v_cls_2387_);
v___y_2401_ = v___y_2411_;
v___y_2402_ = v_a_2412_;
v_data_2403_ = v_data_2417_;
goto v___jp_2400_;
}
else
{
lean_object* v_data_2418_; double v___x_2419_; double v___x_2420_; 
lean_dec_ref_known(v_data_2417_, 3);
v_data_2418_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2418_, 0, v_cls_2387_);
lean_ctor_set(v_data_2418_, 1, v___x_2415_);
lean_ctor_set(v_data_2418_, 2, v_tag_2389_);
v___x_2419_ = lean_unbox_float(v_fst_2406_);
lean_dec(v_fst_2406_);
lean_ctor_set_float(v_data_2418_, sizeof(void*)*3, v___x_2419_);
v___x_2420_ = lean_unbox_float(v_snd_2407_);
lean_dec(v_snd_2407_);
lean_ctor_set_float(v_data_2418_, sizeof(void*)*3 + 8, v___x_2420_);
lean_ctor_set_uint8(v_data_2418_, sizeof(void*)*3 + 16, v_collapsed_2388_);
v___y_2401_ = v___y_2411_;
v___y_2402_ = v_a_2412_;
v_data_2403_ = v_data_2418_;
goto v___jp_2400_;
}
}
v___jp_2421_:
{
lean_object* v_ref_2422_; lean_object* v___x_2423_; 
v_ref_2422_ = lean_ctor_get(v___y_2395_, 2);
lean_inc(v___y_2396_);
lean_inc_ref(v___y_2395_);
lean_inc(v_fst_2398_);
v___x_2423_ = lean_apply_4(v_msg_2393_, v_fst_2398_, v___y_2395_, v___y_2396_, lean_box(0));
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_a_2424_);
lean_dec_ref_known(v___x_2423_, 1);
v___y_2411_ = v_ref_2422_;
v_a_2412_ = v_a_2424_;
goto v___jp_2410_;
}
else
{
lean_object* v___x_2425_; 
lean_dec_ref_known(v___x_2423_, 1);
v___x_2425_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2);
v___y_2411_ = v_ref_2422_;
v_a_2412_ = v___x_2425_;
goto v___jp_2410_;
}
}
v___jp_2426_:
{
if (v_clsEnabled_2391_ == 0)
{
if (v___y_2427_ == 0)
{
lean_object* v___x_2428_; lean_object* v_traceState_2429_; lean_object* v_env_2430_; lean_object* v_nextMacroScope_2431_; lean_object* v_ngen_2432_; lean_object* v_auxDeclNGen_2433_; lean_object* v_cache_2434_; lean_object* v_recordedDeps_2435_; lean_object* v_messages_2436_; lean_object* v_infoState_2437_; lean_object* v_snapshotTasks_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2457_; 
lean_dec(v_snd_2407_);
lean_dec(v_fst_2406_);
lean_dec_ref(v_msg_2393_);
lean_dec_ref(v_tag_2389_);
lean_dec(v_cls_2387_);
v___x_2428_ = lean_st_ref_take(v___y_2396_);
v_traceState_2429_ = lean_ctor_get(v___x_2428_, 4);
v_env_2430_ = lean_ctor_get(v___x_2428_, 0);
v_nextMacroScope_2431_ = lean_ctor_get(v___x_2428_, 1);
v_ngen_2432_ = lean_ctor_get(v___x_2428_, 2);
v_auxDeclNGen_2433_ = lean_ctor_get(v___x_2428_, 3);
v_cache_2434_ = lean_ctor_get(v___x_2428_, 5);
v_recordedDeps_2435_ = lean_ctor_get(v___x_2428_, 6);
v_messages_2436_ = lean_ctor_get(v___x_2428_, 7);
v_infoState_2437_ = lean_ctor_get(v___x_2428_, 8);
v_snapshotTasks_2438_ = lean_ctor_get(v___x_2428_, 9);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2440_ = v___x_2428_;
v_isShared_2441_ = v_isSharedCheck_2457_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_snapshotTasks_2438_);
lean_inc(v_infoState_2437_);
lean_inc(v_messages_2436_);
lean_inc(v_recordedDeps_2435_);
lean_inc(v_cache_2434_);
lean_inc(v_traceState_2429_);
lean_inc(v_auxDeclNGen_2433_);
lean_inc(v_ngen_2432_);
lean_inc(v_nextMacroScope_2431_);
lean_inc(v_env_2430_);
lean_dec(v___x_2428_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2457_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
uint64_t v_tid_2442_; lean_object* v_traces_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2456_; 
v_tid_2442_ = lean_ctor_get_uint64(v_traceState_2429_, sizeof(void*)*1);
v_traces_2443_ = lean_ctor_get(v_traceState_2429_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v_traceState_2429_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2445_ = v_traceState_2429_;
v_isShared_2446_ = v_isSharedCheck_2456_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_traces_2443_);
lean_dec(v_traceState_2429_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2456_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2447_; lean_object* v___x_2449_; 
v___x_2447_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2392_, v_traces_2443_);
lean_dec_ref(v_traces_2443_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 0, v___x_2447_);
v___x_2449_ = v___x_2445_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v___x_2447_);
lean_ctor_set_uint64(v_reuseFailAlloc_2455_, sizeof(void*)*1, v_tid_2442_);
v___x_2449_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v___x_2451_; 
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 4, v___x_2449_);
v___x_2451_ = v___x_2440_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_env_2430_);
lean_ctor_set(v_reuseFailAlloc_2454_, 1, v_nextMacroScope_2431_);
lean_ctor_set(v_reuseFailAlloc_2454_, 2, v_ngen_2432_);
lean_ctor_set(v_reuseFailAlloc_2454_, 3, v_auxDeclNGen_2433_);
lean_ctor_set(v_reuseFailAlloc_2454_, 4, v___x_2449_);
lean_ctor_set(v_reuseFailAlloc_2454_, 5, v_cache_2434_);
lean_ctor_set(v_reuseFailAlloc_2454_, 6, v_recordedDeps_2435_);
lean_ctor_set(v_reuseFailAlloc_2454_, 7, v_messages_2436_);
lean_ctor_set(v_reuseFailAlloc_2454_, 8, v_infoState_2437_);
lean_ctor_set(v_reuseFailAlloc_2454_, 9, v_snapshotTasks_2438_);
v___x_2451_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = lean_st_ref_put(v___y_2396_, v___x_2451_);
v___x_2453_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_fst_2398_);
return v___x_2453_;
}
}
}
}
}
else
{
goto v___jp_2421_;
}
}
else
{
goto v___jp_2421_;
}
}
v___jp_2458_:
{
double v___x_2460_; double v___x_2461_; double v___x_2462_; uint8_t v___x_2463_; 
v___x_2460_ = lean_unbox_float(v_snd_2407_);
v___x_2461_ = lean_unbox_float(v_fst_2406_);
v___x_2462_ = lean_float_sub(v___x_2460_, v___x_2461_);
v___x_2463_ = lean_float_decLt(v___y_2459_, v___x_2462_);
v___y_2427_ = v___x_2463_;
goto v___jp_2426_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___boxed(lean_object* v_cls_2474_, lean_object* v_collapsed_2475_, lean_object* v_tag_2476_, lean_object* v_opts_2477_, lean_object* v_clsEnabled_2478_, lean_object* v_oldTraces_2479_, lean_object* v_msg_2480_, lean_object* v_resStartStop_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
uint8_t v_collapsed_boxed_2485_; uint8_t v_clsEnabled_boxed_2486_; lean_object* v_res_2487_; 
v_collapsed_boxed_2485_ = lean_unbox(v_collapsed_2475_);
v_clsEnabled_boxed_2486_ = lean_unbox(v_clsEnabled_2478_);
v_res_2487_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_2474_, v_collapsed_boxed_2485_, v_tag_2476_, v_opts_2477_, v_clsEnabled_boxed_2486_, v_oldTraces_2479_, v_msg_2480_, v_resStartStop_2481_, v___y_2482_, v___y_2483_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec_ref(v_opts_2477_);
return v_res_2487_;
}
}
static double _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2490_; double v___x_2491_; 
v___x_2490_ = lean_unsigned_to_nat(1000000000u);
v___x_2491_ = lean_float_of_nat(v___x_2490_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(lean_object* v_decl_2492_, lean_object* v___x_2493_, uint8_t v___x_2494_, lean_object* v___x_2495_, lean_object* v___f_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v___y_2501_; lean_object* v___y_2502_; uint8_t v___y_2503_; lean_object* v___y_2514_; lean_object* v_a_2515_; lean_object* v___y_2519_; lean_object* v___y_2520_; uint8_t v___y_2521_; lean_object* v___y_2532_; lean_object* v_a_2533_; lean_object* v_toCold_2536_; lean_object* v_options_2537_; uint8_t v_hasTrace_2538_; 
v_toCold_2536_ = lean_ctor_get(v___y_2497_, 0);
v_options_2537_ = lean_ctor_get(v_toCold_2536_, 2);
v_hasTrace_2538_ = lean_ctor_get_uint8(v_options_2537_, sizeof(void*)*1);
if (v_hasTrace_2538_ == 0)
{
lean_object* v_cancelTk_x3f_2539_; lean_object* v___x_2540_; 
lean_dec_ref(v___f_2496_);
lean_dec_ref(v___x_2495_);
lean_dec(v___x_2493_);
v_cancelTk_x3f_2539_ = lean_ctor_get(v_toCold_2536_, 10);
lean_inc(v_decl_2492_);
v___x_2540_ = l_Lean_warnIfUsesSorry(v_decl_2492_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v___x_2541_; lean_object* v_env_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
lean_dec_ref_known(v___x_2540_, 1);
v___x_2541_ = lean_st_ref_get(v___y_2498_);
v_env_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc_ref(v_env_2542_);
lean_dec(v___x_2541_);
v___x_2543_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2497_);
v___x_2544_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2542_, v___x_2543_, v_decl_2492_, v_cancelTk_x3f_2539_);
lean_dec_ref(v___x_2543_);
v___x_2545_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2544_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v___x_2547_; 
lean_dec(v_decl_2492_);
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_a_2546_);
lean_dec_ref_known(v___x_2545_, 1);
v___x_2547_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2546_, v___y_2498_);
return v___x_2547_;
}
else
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2555_; 
v_a_2548_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2550_ = v___x_2545_;
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2545_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2553_; 
lean_inc(v_a_2548_);
if (v_isShared_2551_ == 0)
{
v___x_2553_ = v___x_2550_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_a_2548_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
v___y_2532_ = v___x_2553_;
v_a_2533_ = v_a_2548_;
goto v___jp_2531_;
}
}
}
}
else
{
lean_dec(v_decl_2492_);
return v___x_2540_;
}
}
else
{
lean_object* v_cancelTk_x3f_2556_; lean_object* v_inheritedTraceOptions_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; uint8_t v___x_2560_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v_a_2564_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v_a_2579_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v_a_2584_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; uint8_t v___y_2596_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v_a_2601_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v_a_2607_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v_a_2619_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v_a_2624_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; uint8_t v___y_2636_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v_a_2641_; 
v_cancelTk_x3f_2556_ = lean_ctor_get(v_toCold_2536_, 10);
v_inheritedTraceOptions_2557_ = lean_ctor_get(v_toCold_2536_, 11);
v___x_2558_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v___x_2493_);
v___x_2559_ = l_Lean_Name_append(v___x_2558_, v___x_2493_);
v___x_2560_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2557_, v_options_2537_, v___x_2559_);
lean_dec(v___x_2559_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2671_; uint8_t v___x_2672_; 
v___x_2671_ = l_Lean_trace_profiler;
v___x_2672_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2537_, v___x_2671_);
if (v___x_2672_ == 0)
{
lean_object* v___x_2673_; 
lean_dec_ref(v___f_2496_);
lean_dec_ref(v___x_2495_);
lean_dec(v___x_2493_);
lean_inc(v_decl_2492_);
v___x_2673_ = l_Lean_warnIfUsesSorry(v_decl_2492_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v___x_2674_; lean_object* v_env_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
lean_dec_ref_known(v___x_2673_, 1);
v___x_2674_ = lean_st_ref_get(v___y_2498_);
v_env_2675_ = lean_ctor_get(v___x_2674_, 0);
lean_inc_ref(v_env_2675_);
lean_dec(v___x_2674_);
v___x_2676_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2497_);
v___x_2677_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2675_, v___x_2676_, v_decl_2492_, v_cancelTk_x3f_2556_);
lean_dec_ref(v___x_2676_);
v___x_2678_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2677_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v___x_2680_; 
lean_dec(v_decl_2492_);
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref_known(v___x_2678_, 1);
v___x_2680_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2679_, v___y_2498_);
return v___x_2680_;
}
else
{
lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2688_; 
v_a_2681_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2683_ = v___x_2678_;
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2678_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2686_; 
lean_inc(v_a_2681_);
if (v_isShared_2684_ == 0)
{
v___x_2686_ = v___x_2683_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_a_2681_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
v___y_2514_ = v___x_2686_;
v_a_2515_ = v_a_2681_;
goto v___jp_2513_;
}
}
}
}
else
{
lean_dec(v_decl_2492_);
return v___x_2673_;
}
}
else
{
goto v___jp_2644_;
}
}
else
{
goto v___jp_2644_;
}
v___jp_2561_:
{
lean_object* v___x_2565_; double v___x_2566_; double v___x_2567_; double v___x_2568_; double v___x_2569_; double v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2565_ = lean_io_mono_nanos_now();
v___x_2566_ = lean_float_of_nat(v___y_2562_);
v___x_2567_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_2568_ = lean_float_div(v___x_2566_, v___x_2567_);
v___x_2569_ = lean_float_of_nat(v___x_2565_);
v___x_2570_ = lean_float_div(v___x_2569_, v___x_2567_);
v___x_2571_ = lean_box_float(v___x_2568_);
v___x_2572_ = lean_box_float(v___x_2570_);
v___x_2573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2571_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2574_, 0, v_a_2564_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
v___x_2575_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2493_, v___x_2494_, v___x_2495_, v_options_2537_, v___x_2560_, v___y_2563_, v___f_2496_, v___x_2574_, v___y_2497_, v___y_2498_);
return v___x_2575_;
}
v___jp_2576_:
{
lean_object* v___x_2580_; 
v___x_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2580_, 0, v_a_2579_);
v___y_2562_ = v___y_2577_;
v___y_2563_ = v___y_2578_;
v_a_2564_ = v___x_2580_;
goto v___jp_2561_;
}
v___jp_2581_:
{
lean_object* v___x_2585_; 
v___x_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2585_, 0, v_a_2584_);
v___y_2562_ = v___y_2582_;
v___y_2563_ = v___y_2583_;
v_a_2564_ = v___x_2585_;
goto v___jp_2561_;
}
v___jp_2586_:
{
if (lean_obj_tag(v___y_2589_) == 0)
{
lean_object* v_a_2590_; 
v_a_2590_ = lean_ctor_get(v___y_2589_, 0);
lean_inc(v_a_2590_);
lean_dec_ref_known(v___y_2589_, 1);
v___y_2582_ = v___y_2587_;
v___y_2583_ = v___y_2588_;
v_a_2584_ = v_a_2590_;
goto v___jp_2581_;
}
else
{
lean_object* v_a_2591_; 
v_a_2591_ = lean_ctor_get(v___y_2589_, 0);
lean_inc(v_a_2591_);
lean_dec_ref_known(v___y_2589_, 1);
v___y_2577_ = v___y_2587_;
v___y_2578_ = v___y_2588_;
v_a_2579_ = v_a_2591_;
goto v___jp_2576_;
}
}
v___jp_2592_:
{
if (v___y_2596_ == 0)
{
lean_object* v___x_2597_; 
v___x_2597_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2492_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_dec_ref_known(v___x_2597_, 1);
v___y_2577_ = v___y_2593_;
v___y_2578_ = v___y_2595_;
v_a_2579_ = v___y_2594_;
goto v___jp_2576_;
}
else
{
lean_dec_ref(v___y_2594_);
v___y_2587_ = v___y_2593_;
v___y_2588_ = v___y_2595_;
v___y_2589_ = v___x_2597_;
goto v___jp_2586_;
}
}
else
{
lean_dec(v_decl_2492_);
v___y_2577_ = v___y_2593_;
v___y_2578_ = v___y_2595_;
v_a_2579_ = v___y_2594_;
goto v___jp_2576_;
}
}
v___jp_2598_:
{
uint8_t v___x_2602_; 
v___x_2602_ = l_Lean_Exception_isInterrupt(v_a_2601_);
if (v___x_2602_ == 0)
{
uint8_t v___x_2603_; 
lean_inc_ref(v_a_2601_);
v___x_2603_ = l_Lean_Exception_isRuntime(v_a_2601_);
v___y_2593_ = v___y_2599_;
v___y_2594_ = v_a_2601_;
v___y_2595_ = v___y_2600_;
v___y_2596_ = v___x_2603_;
goto v___jp_2592_;
}
else
{
v___y_2593_ = v___y_2599_;
v___y_2594_ = v_a_2601_;
v___y_2595_ = v___y_2600_;
v___y_2596_ = v___x_2602_;
goto v___jp_2592_;
}
}
v___jp_2604_:
{
lean_object* v___x_2608_; double v___x_2609_; double v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2608_ = lean_io_get_num_heartbeats();
v___x_2609_ = lean_float_of_nat(v___y_2605_);
v___x_2610_ = lean_float_of_nat(v___x_2608_);
v___x_2611_ = lean_box_float(v___x_2609_);
v___x_2612_ = lean_box_float(v___x_2610_);
v___x_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2611_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
v___x_2614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2614_, 0, v_a_2607_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
v___x_2615_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2493_, v___x_2494_, v___x_2495_, v_options_2537_, v___x_2560_, v___y_2606_, v___f_2496_, v___x_2614_, v___y_2497_, v___y_2498_);
return v___x_2615_;
}
v___jp_2616_:
{
lean_object* v___x_2620_; 
v___x_2620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2620_, 0, v_a_2619_);
v___y_2605_ = v___y_2617_;
v___y_2606_ = v___y_2618_;
v_a_2607_ = v___x_2620_;
goto v___jp_2604_;
}
v___jp_2621_:
{
lean_object* v___x_2625_; 
v___x_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2625_, 0, v_a_2624_);
v___y_2605_ = v___y_2622_;
v___y_2606_ = v___y_2623_;
v_a_2607_ = v___x_2625_;
goto v___jp_2604_;
}
v___jp_2626_:
{
if (lean_obj_tag(v___y_2629_) == 0)
{
lean_object* v_a_2630_; 
v_a_2630_ = lean_ctor_get(v___y_2629_, 0);
lean_inc(v_a_2630_);
lean_dec_ref_known(v___y_2629_, 1);
v___y_2622_ = v___y_2627_;
v___y_2623_ = v___y_2628_;
v_a_2624_ = v_a_2630_;
goto v___jp_2621_;
}
else
{
lean_object* v_a_2631_; 
v_a_2631_ = lean_ctor_get(v___y_2629_, 0);
lean_inc(v_a_2631_);
lean_dec_ref_known(v___y_2629_, 1);
v___y_2617_ = v___y_2627_;
v___y_2618_ = v___y_2628_;
v_a_2619_ = v_a_2631_;
goto v___jp_2616_;
}
}
v___jp_2632_:
{
if (v___y_2636_ == 0)
{
lean_object* v___x_2637_; 
v___x_2637_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2492_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_dec_ref_known(v___x_2637_, 1);
v___y_2617_ = v___y_2634_;
v___y_2618_ = v___y_2635_;
v_a_2619_ = v___y_2633_;
goto v___jp_2616_;
}
else
{
lean_dec_ref(v___y_2633_);
v___y_2627_ = v___y_2634_;
v___y_2628_ = v___y_2635_;
v___y_2629_ = v___x_2637_;
goto v___jp_2626_;
}
}
else
{
lean_dec(v_decl_2492_);
v___y_2617_ = v___y_2634_;
v___y_2618_ = v___y_2635_;
v_a_2619_ = v___y_2633_;
goto v___jp_2616_;
}
}
v___jp_2638_:
{
uint8_t v___x_2642_; 
v___x_2642_ = l_Lean_Exception_isInterrupt(v_a_2641_);
if (v___x_2642_ == 0)
{
uint8_t v___x_2643_; 
lean_inc_ref(v_a_2641_);
v___x_2643_ = l_Lean_Exception_isRuntime(v_a_2641_);
v___y_2633_ = v_a_2641_;
v___y_2634_ = v___y_2639_;
v___y_2635_ = v___y_2640_;
v___y_2636_ = v___x_2643_;
goto v___jp_2632_;
}
else
{
v___y_2633_ = v_a_2641_;
v___y_2634_ = v___y_2639_;
v___y_2635_ = v___y_2640_;
v___y_2636_ = v___x_2642_;
goto v___jp_2632_;
}
}
v___jp_2644_:
{
lean_object* v___x_2645_; lean_object* v_a_2646_; lean_object* v___x_2647_; uint8_t v___x_2648_; 
v___x_2645_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2498_);
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_a_2646_);
lean_dec_ref(v___x_2645_);
v___x_2647_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2648_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2537_, v___x_2647_);
if (v___x_2648_ == 0)
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2649_ = lean_io_mono_nanos_now();
lean_inc(v_decl_2492_);
v___x_2650_ = l_Lean_warnIfUsesSorry(v_decl_2492_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v___x_2651_; lean_object* v_env_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
lean_dec_ref_known(v___x_2650_, 1);
v___x_2651_ = lean_st_ref_get(v___y_2498_);
v_env_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc_ref(v_env_2652_);
lean_dec(v___x_2651_);
v___x_2653_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2497_);
v___x_2654_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2652_, v___x_2653_, v_decl_2492_, v_cancelTk_x3f_2556_);
lean_dec_ref(v___x_2653_);
v___x_2655_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2654_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; lean_object* v___x_2657_; lean_object* v_a_2658_; 
lean_dec(v_decl_2492_);
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2656_);
lean_dec_ref_known(v___x_2655_, 1);
v___x_2657_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2656_, v___y_2498_);
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2658_);
lean_dec_ref(v___x_2657_);
v___y_2582_ = v___x_2649_;
v___y_2583_ = v_a_2646_;
v_a_2584_ = v_a_2658_;
goto v___jp_2581_;
}
else
{
lean_object* v_a_2659_; 
v_a_2659_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2659_);
lean_dec_ref_known(v___x_2655_, 1);
v___y_2599_ = v___x_2649_;
v___y_2600_ = v_a_2646_;
v_a_2601_ = v_a_2659_;
goto v___jp_2598_;
}
}
else
{
lean_dec(v_decl_2492_);
v___y_2587_ = v___x_2649_;
v___y_2588_ = v_a_2646_;
v___y_2589_ = v___x_2650_;
goto v___jp_2586_;
}
}
else
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2660_ = lean_io_get_num_heartbeats();
lean_inc(v_decl_2492_);
v___x_2661_ = l_Lean_warnIfUsesSorry(v_decl_2492_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v___x_2662_; lean_object* v_env_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
lean_dec_ref_known(v___x_2661_, 1);
v___x_2662_ = lean_st_ref_get(v___y_2498_);
v_env_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc_ref(v_env_2663_);
lean_dec(v___x_2662_);
v___x_2664_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2497_);
v___x_2665_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2663_, v___x_2664_, v_decl_2492_, v_cancelTk_x3f_2556_);
lean_dec_ref(v___x_2664_);
v___x_2666_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2665_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v___x_2668_; lean_object* v_a_2669_; 
lean_dec(v_decl_2492_);
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_a_2667_);
lean_dec_ref_known(v___x_2666_, 1);
v___x_2668_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2667_, v___y_2498_);
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2669_);
lean_dec_ref(v___x_2668_);
v___y_2622_ = v___x_2660_;
v___y_2623_ = v_a_2646_;
v_a_2624_ = v_a_2669_;
goto v___jp_2621_;
}
else
{
lean_object* v_a_2670_; 
v_a_2670_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_a_2670_);
lean_dec_ref_known(v___x_2666_, 1);
v___y_2639_ = v___x_2660_;
v___y_2640_ = v_a_2646_;
v_a_2641_ = v_a_2670_;
goto v___jp_2638_;
}
}
else
{
lean_dec(v_decl_2492_);
v___y_2627_ = v___x_2660_;
v___y_2628_ = v_a_2646_;
v___y_2629_ = v___x_2661_;
goto v___jp_2626_;
}
}
}
}
v___jp_2500_:
{
if (v___y_2503_ == 0)
{
lean_object* v___x_2504_; 
lean_dec_ref(v___y_2502_);
v___x_2504_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2492_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2511_ == 0)
{
lean_object* v_unused_2512_; 
v_unused_2512_ = lean_ctor_get(v___x_2504_, 0);
lean_dec(v_unused_2512_);
v___x_2506_ = v___x_2504_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_dec(v___x_2504_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2509_; 
if (v_isShared_2507_ == 0)
{
lean_ctor_set_tag(v___x_2506_, 1);
lean_ctor_set(v___x_2506_, 0, v___y_2501_);
v___x_2509_ = v___x_2506_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___y_2501_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
else
{
lean_dec_ref(v___y_2501_);
return v___x_2504_;
}
}
else
{
lean_dec_ref(v___y_2501_);
lean_dec(v_decl_2492_);
return v___y_2502_;
}
}
v___jp_2513_:
{
uint8_t v___x_2516_; 
v___x_2516_ = l_Lean_Exception_isInterrupt(v_a_2515_);
if (v___x_2516_ == 0)
{
uint8_t v___x_2517_; 
lean_inc_ref(v_a_2515_);
v___x_2517_ = l_Lean_Exception_isRuntime(v_a_2515_);
v___y_2501_ = v_a_2515_;
v___y_2502_ = v___y_2514_;
v___y_2503_ = v___x_2517_;
goto v___jp_2500_;
}
else
{
v___y_2501_ = v_a_2515_;
v___y_2502_ = v___y_2514_;
v___y_2503_ = v___x_2516_;
goto v___jp_2500_;
}
}
v___jp_2518_:
{
if (v___y_2521_ == 0)
{
lean_object* v___x_2522_; 
lean_dec_ref(v___y_2520_);
v___x_2522_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2492_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2529_ == 0)
{
lean_object* v_unused_2530_; 
v_unused_2530_ = lean_ctor_get(v___x_2522_, 0);
lean_dec(v_unused_2530_);
v___x_2524_ = v___x_2522_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_dec(v___x_2522_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
lean_ctor_set_tag(v___x_2524_, 1);
lean_ctor_set(v___x_2524_, 0, v___y_2519_);
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v___y_2519_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
else
{
lean_dec_ref(v___y_2519_);
return v___x_2522_;
}
}
else
{
lean_dec_ref(v___y_2519_);
lean_dec(v_decl_2492_);
return v___y_2520_;
}
}
v___jp_2531_:
{
uint8_t v___x_2534_; 
v___x_2534_ = l_Lean_Exception_isInterrupt(v_a_2533_);
if (v___x_2534_ == 0)
{
uint8_t v___x_2535_; 
lean_inc_ref(v_a_2533_);
v___x_2535_ = l_Lean_Exception_isRuntime(v_a_2533_);
v___y_2519_ = v_a_2533_;
v___y_2520_ = v___y_2532_;
v___y_2521_ = v___x_2535_;
goto v___jp_2518_;
}
else
{
v___y_2519_ = v_a_2533_;
v___y_2520_ = v___y_2532_;
v___y_2521_ = v___x_2534_;
goto v___jp_2518_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed(lean_object* v_decl_2689_, lean_object* v___x_2690_, lean_object* v___x_2691_, lean_object* v___x_2692_, lean_object* v___f_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
uint8_t v___x_7949__boxed_2697_; lean_object* v_res_2698_; 
v___x_7949__boxed_2697_ = lean_unbox(v___x_2691_);
v_res_2698_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(v_decl_2689_, v___x_2690_, v___x_7949__boxed_2697_, v___x_2692_, v___f_2693_, v___y_2694_, v___y_2695_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(lean_object* v_decl_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_){
_start:
{
lean_object* v___f_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; uint8_t v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___f_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
lean_inc(v_decl_2703_);
v___f_2707_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2707_, 0, v_decl_2703_);
v___x_2708_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2704_);
v___x_2709_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__0));
v___x_2710_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__2));
v___x_2711_ = 1;
v___x_2712_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2713_ = lean_box(v___x_2711_);
v___f_2714_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed), 8, 5);
lean_closure_set(v___f_2714_, 0, v_decl_2703_);
lean_closure_set(v___f_2714_, 1, v___x_2710_);
lean_closure_set(v___f_2714_, 2, v___x_2713_);
lean_closure_set(v___f_2714_, 3, v___x_2712_);
lean_closure_set(v___f_2714_, 4, v___f_2707_);
v___x_2715_ = lean_box(0);
v___x_2716_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v___x_2709_, v___x_2708_, v___f_2714_, v___x_2715_, v_a_2704_, v_a_2705_);
lean_dec_ref(v___x_2708_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___boxed(lean_object* v_decl_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2717_, v_a_2718_, v_a_2719_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(lean_object* v_00_u03b1_2722_, lean_object* v_x_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_x_2723_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2728_, lean_object* v_x_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(v_00_u03b1_2728_, v_x_2729_, v___y_2730_, v___y_2731_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(lean_object* v___y_2734_, lean_object* v_a_2735_, lean_object* v_ref_2736_, lean_object* v_a_x3f_2737_){
_start:
{
lean_object* v___x_2739_; lean_object* v_env_2740_; lean_object* v___x_2741_; 
v___x_2739_ = lean_st_ref_get(v___y_2734_);
v_env_2740_ = lean_ctor_get(v___x_2739_, 0);
lean_inc_ref(v_env_2740_);
lean_dec(v___x_2739_);
v___x_2741_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2735_, v_env_2740_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2749_; 
lean_dec(v_ref_2736_);
v_a_2742_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2744_ = v___x_2741_;
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2741_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2747_; 
if (v_isShared_2745_ == 0)
{
v___x_2747_ = v___x_2744_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_a_2742_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
else
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2761_; 
v_a_2750_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2752_ = v___x_2741_;
v_isShared_2753_ = v_isSharedCheck_2761_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2741_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2761_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2759_; 
v___x_2754_ = lean_io_error_to_string(v_a_2750_);
v___x_2755_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2754_);
v___x_2756_ = l_Lean_MessageData_ofFormat(v___x_2755_);
v___x_2757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2757_, 0, v_ref_2736_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 0, v___x_2757_);
v___x_2759_ = v___x_2752_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2757_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed(lean_object* v___y_2762_, lean_object* v_a_2763_, lean_object* v_ref_2764_, lean_object* v_a_x3f_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2762_, v_a_2763_, v_ref_2764_, v_a_x3f_2765_);
lean_dec(v_a_x3f_2765_);
lean_dec(v___y_2762_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v_a_2770_, lean_object* v_a_x3f_2771_){
_start:
{
lean_object* v___x_2773_; lean_object* v_env_2774_; lean_object* v_ref_2775_; lean_object* v___x_2776_; 
v___x_2773_ = lean_st_ref_get(v___y_2768_);
v_env_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc_ref(v_env_2774_);
lean_dec(v___x_2773_);
v_ref_2775_ = lean_ctor_get(v___y_2769_, 2);
v___x_2776_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2770_, v_env_2774_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2776_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2776_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2796_; 
v_a_2785_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2787_ = v___x_2776_;
v_isShared_2788_ = v_isSharedCheck_2796_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2776_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2796_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2794_; 
v___x_2789_ = lean_io_error_to_string(v_a_2785_);
v___x_2790_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2789_);
v___x_2791_ = l_Lean_MessageData_ofFormat(v___x_2790_);
lean_inc(v_ref_2775_);
v___x_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2792_, 0, v_ref_2775_);
lean_ctor_set(v___x_2792_, 1, v___x_2791_);
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 0, v___x_2792_);
v___x_2794_ = v___x_2787_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v___x_2792_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___boxed(lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v_a_2799_, lean_object* v_a_x3f_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v___y_2797_, v___y_2798_, v_a_2799_, v_a_x3f_2800_);
lean_dec(v_a_x3f_2800_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(lean_object* v_a_2803_, lean_object* v_asyncEnv_2804_, lean_object* v_decl_2805_, lean_object* v_x_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
lean_object* v___x_2810_; lean_object* v_r_2811_; 
v___x_2810_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_asyncEnv_2804_, v___y_2808_);
lean_dec_ref(v___x_2810_);
v_r_2811_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2805_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v_r_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2828_; 
v_a_2812_ = lean_ctor_get(v_r_2811_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v_r_2811_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2814_ = v_r_2811_;
v_isShared_2815_ = v_isSharedCheck_2828_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v_r_2811_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2828_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
lean_inc(v_a_2812_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set_tag(v___x_2814_, 1);
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_a_2812_);
v___x_2817_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
lean_object* v___x_2818_; 
v___x_2818_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v___y_2808_, v___y_2807_, v_a_2803_, v___x_2817_);
lean_dec_ref(v___x_2817_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
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
lean_ctor_set(v___x_2820_, 0, v_a_2812_);
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2812_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
else
{
lean_dec(v_a_2812_);
return v___x_2818_;
}
}
}
}
else
{
lean_object* v_a_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v_a_2829_ = lean_ctor_get(v_r_2811_, 0);
lean_inc(v_a_2829_);
lean_dec_ref_known(v_r_2811_, 1);
v___x_2830_ = lean_box(0);
v___x_2831_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v___y_2808_, v___y_2807_, v_a_2803_, v___x_2830_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2838_; 
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2838_ == 0)
{
lean_object* v_unused_2839_; 
v_unused_2839_ = lean_ctor_get(v___x_2831_, 0);
lean_dec(v_unused_2839_);
v___x_2833_ = v___x_2831_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_dec(v___x_2831_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
if (v_isShared_2834_ == 0)
{
lean_ctor_set_tag(v___x_2833_, 1);
lean_ctor_set(v___x_2833_, 0, v_a_2829_);
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2829_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
else
{
lean_dec(v_a_2829_);
return v___x_2831_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed(lean_object* v_a_2840_, lean_object* v_asyncEnv_2841_, lean_object* v_decl_2842_, lean_object* v_x_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(v_a_2840_, v_asyncEnv_2841_, v_decl_2842_, v_x_2843_, v___y_2844_, v___y_2845_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec_ref(v_x_2843_);
return v_res_2847_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2849_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__0));
v___x_2850_ = l_Lean_stringToMessageData(v___x_2849_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(lean_object* v_decl_2851_, lean_object* v_x_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_){
_start:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2856_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1);
v___x_2857_ = l_Lean_Declaration_getNames(v_decl_2851_);
v___x_2858_ = lean_box(0);
v___x_2859_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2857_, v___x_2858_);
v___x_2860_ = l_Lean_MessageData_ofList(v___x_2859_);
v___x_2861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2856_);
lean_ctor_set(v___x_2861_, 1, v___x_2860_);
v___x_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2861_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed(lean_object* v_decl_2863_, lean_object* v_x_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
lean_object* v_res_2868_; 
v_res_2868_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_2863_, v_x_2864_, v___y_2865_, v___y_2866_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec_ref(v_x_2864_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(lean_object* v_cls_2871_, lean_object* v_msg_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v_ref_2876_; lean_object* v___x_2877_; lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2923_; 
v_ref_2876_ = lean_ctor_get(v___y_2873_, 2);
v___x_2877_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2872_, v___y_2873_, v___y_2874_);
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2880_ = v___x_2877_;
v_isShared_2881_ = v_isSharedCheck_2923_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___x_2877_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2923_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2882_; lean_object* v_traceState_2883_; lean_object* v_env_2884_; lean_object* v_nextMacroScope_2885_; lean_object* v_ngen_2886_; lean_object* v_auxDeclNGen_2887_; lean_object* v_cache_2888_; lean_object* v_recordedDeps_2889_; lean_object* v_messages_2890_; lean_object* v_infoState_2891_; lean_object* v_snapshotTasks_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2922_; 
v___x_2882_ = lean_st_ref_take(v___y_2874_);
v_traceState_2883_ = lean_ctor_get(v___x_2882_, 4);
v_env_2884_ = lean_ctor_get(v___x_2882_, 0);
v_nextMacroScope_2885_ = lean_ctor_get(v___x_2882_, 1);
v_ngen_2886_ = lean_ctor_get(v___x_2882_, 2);
v_auxDeclNGen_2887_ = lean_ctor_get(v___x_2882_, 3);
v_cache_2888_ = lean_ctor_get(v___x_2882_, 5);
v_recordedDeps_2889_ = lean_ctor_get(v___x_2882_, 6);
v_messages_2890_ = lean_ctor_get(v___x_2882_, 7);
v_infoState_2891_ = lean_ctor_get(v___x_2882_, 8);
v_snapshotTasks_2892_ = lean_ctor_get(v___x_2882_, 9);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2894_ = v___x_2882_;
v_isShared_2895_ = v_isSharedCheck_2922_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_snapshotTasks_2892_);
lean_inc(v_infoState_2891_);
lean_inc(v_messages_2890_);
lean_inc(v_recordedDeps_2889_);
lean_inc(v_cache_2888_);
lean_inc(v_traceState_2883_);
lean_inc(v_auxDeclNGen_2887_);
lean_inc(v_ngen_2886_);
lean_inc(v_nextMacroScope_2885_);
lean_inc(v_env_2884_);
lean_dec(v___x_2882_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2922_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
uint64_t v_tid_2896_; lean_object* v_traces_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2921_; 
v_tid_2896_ = lean_ctor_get_uint64(v_traceState_2883_, sizeof(void*)*1);
v_traces_2897_ = lean_ctor_get(v_traceState_2883_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v_traceState_2883_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2899_ = v_traceState_2883_;
v_isShared_2900_ = v_isSharedCheck_2921_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_traces_2897_);
lean_dec(v_traceState_2883_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2921_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; double v___x_2903_; uint8_t v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2912_; 
v___x_2901_ = lean_box(0);
v___x_2902_ = lean_box(0);
v___x_2903_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0);
v___x_2904_ = 0;
v___x_2905_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2906_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2906_, 0, v_cls_2871_);
lean_ctor_set(v___x_2906_, 1, v___x_2902_);
lean_ctor_set(v___x_2906_, 2, v___x_2905_);
lean_ctor_set_float(v___x_2906_, sizeof(void*)*3, v___x_2903_);
lean_ctor_set_float(v___x_2906_, sizeof(void*)*3 + 8, v___x_2903_);
lean_ctor_set_uint8(v___x_2906_, sizeof(void*)*3 + 16, v___x_2904_);
v___x_2907_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___closed__0));
v___x_2908_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2906_);
lean_ctor_set(v___x_2908_, 1, v_a_2878_);
lean_ctor_set(v___x_2908_, 2, v___x_2907_);
lean_inc(v_ref_2876_);
v___x_2909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2909_, 0, v_ref_2876_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
v___x_2910_ = l_Lean_PersistentArray_push___redArg(v_traces_2897_, v___x_2909_);
if (v_isShared_2900_ == 0)
{
lean_ctor_set(v___x_2899_, 0, v___x_2910_);
v___x_2912_ = v___x_2899_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v___x_2910_);
lean_ctor_set_uint64(v_reuseFailAlloc_2920_, sizeof(void*)*1, v_tid_2896_);
v___x_2912_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
lean_object* v___x_2914_; 
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 4, v___x_2912_);
v___x_2914_ = v___x_2894_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_env_2884_);
lean_ctor_set(v_reuseFailAlloc_2919_, 1, v_nextMacroScope_2885_);
lean_ctor_set(v_reuseFailAlloc_2919_, 2, v_ngen_2886_);
lean_ctor_set(v_reuseFailAlloc_2919_, 3, v_auxDeclNGen_2887_);
lean_ctor_set(v_reuseFailAlloc_2919_, 4, v___x_2912_);
lean_ctor_set(v_reuseFailAlloc_2919_, 5, v_cache_2888_);
lean_ctor_set(v_reuseFailAlloc_2919_, 6, v_recordedDeps_2889_);
lean_ctor_set(v_reuseFailAlloc_2919_, 7, v_messages_2890_);
lean_ctor_set(v_reuseFailAlloc_2919_, 8, v_infoState_2891_);
lean_ctor_set(v_reuseFailAlloc_2919_, 9, v_snapshotTasks_2892_);
v___x_2914_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
lean_object* v___x_2915_; lean_object* v___x_2917_; 
v___x_2915_ = lean_st_ref_put(v___y_2874_, v___x_2914_);
if (v_isShared_2881_ == 0)
{
lean_ctor_set(v___x_2880_, 0, v___x_2901_);
v___x_2917_ = v___x_2880_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2901_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___boxed(lean_object* v_cls_2924_, lean_object* v_msg_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2924_, v_msg_2925_, v___y_2926_, v___y_2927_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
return v_res_2929_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1(void){
_start:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2931_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__0));
v___x_2932_ = l_Lean_stringToMessageData(v___x_2931_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(lean_object* v_decl_2933_, lean_object* v_cls_2934_, lean_object* v_x_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v_toCold_2939_; lean_object* v_options_2940_; uint8_t v_hasTrace_2941_; 
v_toCold_2939_ = lean_ctor_get(v___y_2936_, 0);
v_options_2940_ = lean_ctor_get(v_toCold_2939_, 2);
v_hasTrace_2941_ = lean_ctor_get_uint8(v_options_2940_, sizeof(void*)*1);
if (v_hasTrace_2941_ == 0)
{
lean_object* v___x_2942_; 
lean_dec(v_cls_2934_);
v___x_2942_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2933_, v___y_2936_, v___y_2937_);
return v___x_2942_;
}
else
{
lean_object* v_inheritedTraceOptions_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; uint8_t v___x_2946_; 
v_inheritedTraceOptions_2943_ = lean_ctor_get(v_toCold_2939_, 11);
v___x_2944_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2934_);
v___x_2945_ = l_Lean_Name_append(v___x_2944_, v_cls_2934_);
v___x_2946_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2943_, v_options_2940_, v___x_2945_);
lean_dec(v___x_2945_);
if (v___x_2946_ == 0)
{
lean_object* v___x_2947_; 
lean_dec(v_cls_2934_);
v___x_2947_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2933_, v___y_2936_, v___y_2937_);
return v___x_2947_;
}
else
{
lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2948_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
v___x_2949_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2934_, v___x_2948_, v___y_2936_, v___y_2937_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v___x_2950_; 
lean_dec_ref_known(v___x_2949_, 1);
v___x_2950_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2933_, v___y_2936_, v___y_2937_);
return v___x_2950_;
}
else
{
lean_dec(v_decl_2933_);
return v___x_2949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___boxed(lean_object* v_decl_2951_, lean_object* v_cls_2952_, lean_object* v_x_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_2951_, v_cls_2952_, v_x_2953_, v___y_2954_, v___y_2955_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v_x_2953_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(lean_object* v_opt_2958_, lean_object* v___y_2959_){
_start:
{
lean_object* v___x_2961_; uint8_t v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2961_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2959_);
v___x_2962_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_2961_, v_opt_2958_);
lean_dec_ref(v___x_2961_);
v___x_2963_ = lean_box(v___x_2962_);
v___x_2964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2963_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg___boxed(lean_object* v_opt_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_2965_, v___y_2966_);
lean_dec_ref(v___y_2966_);
lean_dec_ref(v_opt_2965_);
return v_res_2968_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(lean_object* v_x_2969_){
_start:
{
if (lean_obj_tag(v_x_2969_) == 0)
{
uint8_t v___x_2970_; 
v___x_2970_ = 1;
return v___x_2970_;
}
else
{
lean_object* v_head_2971_; lean_object* v_tail_2972_; uint8_t v___x_2973_; 
v_head_2971_ = lean_ctor_get(v_x_2969_, 0);
v_tail_2972_ = lean_ctor_get(v_x_2969_, 1);
v___x_2973_ = l_Lean_isPrivateName(v_head_2971_);
if (v___x_2973_ == 0)
{
return v___x_2973_;
}
else
{
v_x_2969_ = v_tail_2972_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2___boxed(lean_object* v_x_2975_){
_start:
{
uint8_t v_res_2976_; lean_object* v_r_2977_; 
v_res_2976_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v_x_2975_);
lean_dec(v_x_2975_);
v_r_2977_ = lean_box(v_res_2976_);
return v_r_2977_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3(void){
_start:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2983_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__2));
v___x_2984_ = l_Lean_stringToMessageData(v___x_2983_);
return v___x_2984_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5(void){
_start:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2986_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__4));
v___x_2987_ = l_Lean_stringToMessageData(v___x_2986_);
return v___x_2987_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7(void){
_start:
{
lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2989_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__6));
v___x_2990_ = l_Lean_stringToMessageData(v___x_2989_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(lean_object* v_decl_2991_, uint8_t v_hasTrace_2992_, uint8_t v___x_2993_, lean_object* v___x_2994_, lean_object* v_cls_2995_, lean_object* v___x_2996_, lean_object* v_____x_2997_, lean_object* v_exportedInfo_x3f_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v_a_3005_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v_a_3018_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v_snd_3101_; lean_object* v_fst_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3232_; 
v_snd_3101_ = lean_ctor_get(v_____x_2997_, 1);
v_fst_3102_ = lean_ctor_get(v_____x_2997_, 0);
v_isSharedCheck_3232_ = !lean_is_exclusive(v_____x_2997_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3104_ = v_____x_2997_;
v_isShared_3105_ = v_isSharedCheck_3232_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_snd_3101_);
lean_inc(v_fst_3102_);
lean_dec(v_____x_2997_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3232_;
goto v_resetjp_3103_;
}
v___jp_3002_:
{
lean_object* v___x_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3013_; 
v___x_3006_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3004_, v___y_3003_);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3013_ == 0)
{
lean_object* v_unused_3014_; 
v_unused_3014_ = lean_ctor_get(v___x_3006_, 0);
lean_dec(v_unused_3014_);
v___x_3008_ = v___x_3006_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_dec(v___x_3006_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3011_; 
if (v_isShared_3009_ == 0)
{
lean_ctor_set_tag(v___x_3008_, 1);
lean_ctor_set(v___x_3008_, 0, v_a_3005_);
v___x_3011_ = v___x_3008_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3005_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
v___jp_3015_:
{
lean_object* v___x_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
v___x_3019_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3017_, v___y_3016_);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3026_ == 0)
{
lean_object* v_unused_3027_; 
v_unused_3027_ = lean_ctor_get(v___x_3019_, 0);
lean_dec(v_unused_3027_);
v___x_3021_ = v___x_3019_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_dec(v___x_3019_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 0, v_a_3018_);
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3018_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
v___jp_3028_:
{
lean_object* v___x_3040_; 
lean_inc_ref(v___y_3036_);
v___x_3040_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3030_, v___y_3036_, v___y_3033_, v___y_3039_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v___x_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3087_; 
lean_dec_ref_known(v___x_3040_, 1);
lean_dec(v___y_3037_);
lean_inc_ref(v___y_3032_);
v___x_3041_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3032_, v___y_3029_);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3087_ == 0)
{
lean_object* v_unused_3088_; 
v_unused_3088_ = lean_ctor_get(v___x_3041_, 0);
lean_dec(v_unused_3088_);
v___x_3043_ = v___x_3041_;
v_isShared_3044_ = v_isSharedCheck_3087_;
goto v_resetjp_3042_;
}
else
{
lean_dec(v___x_3041_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3087_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; uint8_t v___x_3047_; 
v___x_3045_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3034_);
v___x_3046_ = l_Lean_Elab_async;
v___x_3047_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_3045_, v___x_3046_);
lean_dec_ref(v___x_3045_);
if (v___x_3047_ == 0)
{
lean_object* v___x_3048_; lean_object* v_r_3049_; 
lean_del_object(v___x_3043_);
lean_dec_ref(v___y_3038_);
lean_dec_ref(v___y_3035_);
v___x_3048_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3036_, v___y_3029_);
lean_dec_ref(v___x_3048_);
v_r_3049_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2991_, v___y_3034_, v___y_3029_);
if (lean_obj_tag(v_r_3049_) == 0)
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3059_; 
v_a_3050_ = lean_ctor_get(v_r_3049_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v_r_3049_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3052_ = v_r_3049_;
v_isShared_3053_ = v_isSharedCheck_3059_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v_r_3049_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3059_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
lean_inc(v_a_3050_);
if (v_isShared_3053_ == 0)
{
lean_ctor_set_tag(v___x_3052_, 1);
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3050_);
v___x_3055_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
lean_object* v___x_3056_; 
v___x_3056_ = lean_apply_2(v___y_3031_, v___x_3055_, lean_box(0));
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_dec_ref_known(v___x_3056_, 1);
v___y_3016_ = v___y_3029_;
v___y_3017_ = v___y_3032_;
v_a_3018_ = v_a_3050_;
goto v___jp_3015_;
}
else
{
lean_object* v_a_3057_; 
lean_dec(v_a_3050_);
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_a_3057_);
lean_dec_ref_known(v___x_3056_, 1);
v___y_3003_ = v___y_3029_;
v___y_3004_ = v___y_3032_;
v_a_3005_ = v_a_3057_;
goto v___jp_3002_;
}
}
}
}
else
{
lean_object* v_a_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v_a_3060_ = lean_ctor_get(v_r_3049_, 0);
lean_inc(v_a_3060_);
lean_dec_ref_known(v_r_3049_, 1);
v___x_3061_ = lean_box(0);
v___x_3062_ = lean_apply_2(v___y_3031_, v___x_3061_, lean_box(0));
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_dec_ref_known(v___x_3062_, 1);
v___y_3003_ = v___y_3029_;
v___y_3004_ = v___y_3032_;
v_a_3005_ = v_a_3060_;
goto v___jp_3002_;
}
else
{
lean_object* v_a_3063_; 
lean_dec(v_a_3060_);
v_a_3063_ = lean_ctor_get(v___x_3062_, 0);
lean_inc(v_a_3063_);
lean_dec_ref_known(v___x_3062_, 1);
v___y_3003_ = v___y_3029_;
v___y_3004_ = v___y_3032_;
v_a_3005_ = v_a_3063_;
goto v___jp_3002_;
}
}
}
else
{
lean_object* v___x_3064_; lean_object* v___x_3066_; 
lean_dec_ref(v___y_3036_);
lean_dec_ref(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v_decl_2991_);
v___x_3064_ = l_IO_CancelToken_new();
if (v_isShared_3044_ == 0)
{
lean_ctor_set_tag(v___x_3043_, 1);
lean_ctor_set(v___x_3043_, 0, v___x_3064_);
v___x_3066_ = v___x_3043_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v___x_3064_);
v___x_3066_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3067_ = lean_unsigned_to_nat(0u);
v___x_3068_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_3069_ = l_Lean_Name_toString(v___x_3068_, v_hasTrace_2992_);
lean_inc_ref(v___x_3066_);
v___x_3070_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3038_, v___x_3066_, v___x_3069_, v___y_3034_, v___y_3029_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v_a_3071_; lean_object* v_checked_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_a_3071_);
lean_dec_ref_known(v___x_3070_, 1);
v_checked_3072_ = lean_ctor_get(v___y_3035_, 2);
lean_inc_ref(v_checked_3072_);
lean_dec_ref(v___y_3035_);
v___x_3073_ = lean_io_map_task(v_a_3071_, v_checked_3072_, v___x_3067_, v___x_2993_);
v___x_3074_ = lean_box(0);
v___x_3075_ = lean_box(2);
v___x_3076_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3074_);
lean_ctor_set(v___x_3076_, 1, v___x_3075_);
lean_ctor_set(v___x_3076_, 2, v___x_3066_);
lean_ctor_set(v___x_3076_, 3, v___x_3073_);
v___x_3077_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3076_, v___y_3029_);
return v___x_3077_;
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_dec_ref(v___x_3066_);
lean_dec_ref(v___y_3035_);
v_a_3078_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_3070_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3070_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3100_; 
lean_dec_ref(v___y_3038_);
lean_dec_ref(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec_ref(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v_decl_2991_);
v_a_3089_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3091_ = v___x_3040_;
v_isShared_3092_ = v_isSharedCheck_3100_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3040_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3100_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3098_; 
v___x_3093_ = lean_io_error_to_string(v_a_3089_);
v___x_3094_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
v___x_3095_ = l_Lean_MessageData_ofFormat(v___x_3094_);
v___x_3096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3096_, 0, v___y_3037_);
lean_ctor_set(v___x_3096_, 1, v___x_3095_);
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 0, v___x_3096_);
v___x_3098_ = v___x_3091_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v___x_3096_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
}
v_resetjp_3103_:
{
lean_object* v_fst_3106_; lean_object* v_snd_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3231_; 
v_fst_3106_ = lean_ctor_get(v_snd_3101_, 0);
v_snd_3107_ = lean_ctor_get(v_snd_3101_, 1);
v_isSharedCheck_3231_ = !lean_is_exclusive(v_snd_3101_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3109_ = v_snd_3101_;
v_isShared_3110_ = v_isSharedCheck_3231_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_snd_3107_);
lean_inc(v_fst_3106_);
lean_dec(v_snd_3101_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3231_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v_exportedInfo_x3f_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3161_; uint8_t v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___x_3221_; lean_object* v_env_3222_; uint8_t v___x_3223_; 
v___x_3221_ = lean_st_ref_get(v___y_3000_);
v_env_3222_ = lean_ctor_get(v___x_3221_, 0);
lean_inc_ref(v_env_3222_);
lean_dec(v___x_3221_);
v___x_3223_ = l_Lean_Environment_containsOnBranch(v_env_3222_, v_fst_3102_);
lean_dec_ref(v_env_3222_);
if (v___x_3223_ == 0)
{
lean_del_object(v___x_3104_);
v___y_3186_ = v___y_2999_;
v___y_3187_ = v___y_3000_;
goto v___jp_3185_;
}
else
{
lean_object* v___x_3224_; lean_object* v_env_3225_; lean_object* v___x_3226_; lean_object* v___x_3228_; 
lean_del_object(v___x_3109_);
lean_dec(v_snd_3107_);
lean_dec(v_fst_3106_);
lean_dec(v_exportedInfo_x3f_2998_);
lean_dec(v___x_2996_);
lean_dec(v_cls_2995_);
lean_dec_ref(v___x_2994_);
lean_dec(v_decl_2991_);
v___x_3224_ = lean_st_ref_get(v___y_3000_);
v_env_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc_ref(v_env_3225_);
lean_dec(v___x_3224_);
v___x_3226_ = lean_elab_environment_to_kernel_env(v_env_3225_);
if (v_isShared_3105_ == 0)
{
lean_ctor_set_tag(v___x_3104_, 1);
lean_ctor_set(v___x_3104_, 1, v_fst_3102_);
lean_ctor_set(v___x_3104_, 0, v___x_3226_);
v___x_3228_ = v___x_3104_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3226_);
lean_ctor_set(v_reuseFailAlloc_3230_, 1, v_fst_3102_);
v___x_3228_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
lean_object* v___x_3229_; 
v___x_3229_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3228_, v___y_2999_, v___y_3000_);
return v___x_3229_;
}
}
v___jp_3111_:
{
lean_object* v_ref_3117_; uint8_t v___x_3118_; lean_object* v___x_3119_; 
v_ref_3117_ = lean_ctor_get(v___y_3113_, 2);
v___x_3118_ = lean_unbox(v_snd_3107_);
lean_dec(v_snd_3107_);
lean_inc_ref(v___y_3115_);
v___x_3119_ = l_Lean_Environment_addConstAsync(v___y_3115_, v_fst_3102_, v___x_3118_, v___y_3116_, v___x_2993_, v_hasTrace_2992_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v_a_3120_; lean_object* v_mainEnv_3121_; lean_object* v_asyncEnv_3122_; lean_object* v___f_3123_; lean_object* v___f_3124_; lean_object* v___x_3125_; 
lean_del_object(v___x_3109_);
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
lean_inc_n(v_a_3120_, 3);
lean_dec_ref_known(v___x_3119_, 1);
v_mainEnv_3121_ = lean_ctor_get(v_a_3120_, 0);
lean_inc_ref(v_mainEnv_3121_);
v_asyncEnv_3122_ = lean_ctor_get(v_a_3120_, 1);
lean_inc_ref_n(v_asyncEnv_3122_, 2);
lean_inc(v_ref_3117_);
lean_inc(v___y_3114_);
v___f_3123_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3123_, 0, v___y_3114_);
lean_closure_set(v___f_3123_, 1, v_a_3120_);
lean_closure_set(v___f_3123_, 2, v_ref_3117_);
lean_inc(v_decl_2991_);
v___f_3124_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3124_, 0, v_a_3120_);
lean_closure_set(v___f_3124_, 1, v_asyncEnv_3122_);
lean_closure_set(v___f_3124_, 2, v_decl_2991_);
v___x_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3125_, 0, v_fst_3106_);
if (lean_obj_tag(v___y_3112_) == 0)
{
lean_inc(v_ref_3117_);
lean_inc_ref(v___x_3125_);
v___y_3029_ = v___y_3114_;
v___y_3030_ = v_a_3120_;
v___y_3031_ = v___f_3123_;
v___y_3032_ = v_mainEnv_3121_;
v___y_3033_ = v___x_3125_;
v___y_3034_ = v___y_3113_;
v___y_3035_ = v___y_3115_;
v___y_3036_ = v_asyncEnv_3122_;
v___y_3037_ = v_ref_3117_;
v___y_3038_ = v___f_3124_;
v___y_3039_ = v___x_3125_;
goto v___jp_3028_;
}
else
{
lean_inc(v_ref_3117_);
v___y_3029_ = v___y_3114_;
v___y_3030_ = v_a_3120_;
v___y_3031_ = v___f_3123_;
v___y_3032_ = v_mainEnv_3121_;
v___y_3033_ = v___x_3125_;
v___y_3034_ = v___y_3113_;
v___y_3035_ = v___y_3115_;
v___y_3036_ = v_asyncEnv_3122_;
v___y_3037_ = v_ref_3117_;
v___y_3038_ = v___f_3124_;
v___y_3039_ = v___y_3112_;
goto v___jp_3028_;
}
}
else
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3139_; 
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3112_);
lean_dec(v_fst_3106_);
lean_dec(v_decl_2991_);
v_a_3126_ = lean_ctor_get(v___x_3119_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3128_ = v___x_3119_;
v_isShared_3129_ = v_isSharedCheck_3139_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3119_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3139_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3134_; 
v___x_3130_ = lean_io_error_to_string(v_a_3126_);
v___x_3131_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3130_);
v___x_3132_ = l_Lean_MessageData_ofFormat(v___x_3131_);
lean_inc(v_ref_3117_);
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 1, v___x_3132_);
lean_ctor_set(v___x_3109_, 0, v_ref_3117_);
v___x_3134_ = v___x_3109_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_ref_3117_);
lean_ctor_set(v_reuseFailAlloc_3138_, 1, v___x_3132_);
v___x_3134_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
lean_object* v___x_3136_; 
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 0, v___x_3134_);
v___x_3136_ = v___x_3128_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_3134_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
}
v___jp_3140_:
{
lean_object* v___x_3144_; 
v___x_3144_ = lean_st_ref_get(v___y_3143_);
if (lean_obj_tag(v_exportedInfo_x3f_3141_) == 0)
{
lean_object* v_env_3145_; lean_object* v___x_3146_; 
v_env_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc_ref(v_env_3145_);
lean_dec(v___x_3144_);
v___x_3146_ = lean_box(0);
v___y_3112_ = v_exportedInfo_x3f_3141_;
v___y_3113_ = v___y_3142_;
v___y_3114_ = v___y_3143_;
v___y_3115_ = v_env_3145_;
v___y_3116_ = v___x_3146_;
goto v___jp_3111_;
}
else
{
lean_object* v_env_3147_; lean_object* v_val_3148_; uint8_t v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v_env_3147_ = lean_ctor_get(v___x_3144_, 0);
lean_inc_ref(v_env_3147_);
lean_dec(v___x_3144_);
v_val_3148_ = lean_ctor_get(v_exportedInfo_x3f_3141_, 0);
v___x_3149_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3148_);
v___x_3150_ = lean_box(v___x_3149_);
v___x_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3150_);
v___y_3112_ = v_exportedInfo_x3f_3141_;
v___y_3113_ = v___y_3142_;
v___y_3114_ = v___y_3143_;
v___y_3115_ = v_env_3147_;
v___y_3116_ = v___x_3151_;
goto v___jp_3111_;
}
}
v___jp_3152_:
{
lean_object* v___x_3155_; 
lean_inc(v_fst_3106_);
v___x_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3155_, 0, v_fst_3106_);
v_exportedInfo_x3f_3141_ = v___x_3155_;
v___y_3142_ = v___y_3153_;
v___y_3143_ = v___y_3154_;
goto v___jp_3140_;
}
v___jp_3156_:
{
lean_object* v___x_3159_; 
lean_inc(v_fst_3106_);
v___x_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3159_, 0, v_fst_3106_);
v_exportedInfo_x3f_3141_ = v___x_3159_;
v___y_3142_ = v___y_3157_;
v___y_3143_ = v___y_3158_;
goto v___jp_3140_;
}
v___jp_3160_:
{
lean_object* v___x_3164_; lean_object* v_env_3165_; lean_object* v_nextMacroScope_3166_; lean_object* v_ngen_3167_; lean_object* v_auxDeclNGen_3168_; lean_object* v_traceState_3169_; lean_object* v_recordedDeps_3170_; lean_object* v_messages_3171_; lean_object* v_infoState_3172_; lean_object* v_snapshotTasks_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3183_; 
v___x_3164_ = lean_st_ref_take(v___y_3161_);
v_env_3165_ = lean_ctor_get(v___x_3164_, 0);
v_nextMacroScope_3166_ = lean_ctor_get(v___x_3164_, 1);
v_ngen_3167_ = lean_ctor_get(v___x_3164_, 2);
v_auxDeclNGen_3168_ = lean_ctor_get(v___x_3164_, 3);
v_traceState_3169_ = lean_ctor_get(v___x_3164_, 4);
v_recordedDeps_3170_ = lean_ctor_get(v___x_3164_, 6);
v_messages_3171_ = lean_ctor_get(v___x_3164_, 7);
v_infoState_3172_ = lean_ctor_get(v___x_3164_, 8);
v_snapshotTasks_3173_ = lean_ctor_get(v___x_3164_, 9);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3183_ == 0)
{
lean_object* v_unused_3184_; 
v_unused_3184_ = lean_ctor_get(v___x_3164_, 5);
lean_dec(v_unused_3184_);
v___x_3175_ = v___x_3164_;
v_isShared_3176_ = v_isSharedCheck_3183_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_snapshotTasks_3173_);
lean_inc(v_infoState_3172_);
lean_inc(v_messages_3171_);
lean_inc(v_recordedDeps_3170_);
lean_inc(v_traceState_3169_);
lean_inc(v_auxDeclNGen_3168_);
lean_inc(v_ngen_3167_);
lean_inc(v_nextMacroScope_3166_);
lean_inc(v_env_3165_);
lean_dec(v___x_3164_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3183_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3180_; 
v___x_3177_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3107_);
lean_inc(v_fst_3102_);
v___x_3178_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3177_, v_env_3165_, v_fst_3102_, v_snd_3107_, v___y_3162_);
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 5, v___x_2994_);
lean_ctor_set(v___x_3175_, 0, v___x_3178_);
v___x_3180_ = v___x_3175_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3178_);
lean_ctor_set(v_reuseFailAlloc_3182_, 1, v_nextMacroScope_3166_);
lean_ctor_set(v_reuseFailAlloc_3182_, 2, v_ngen_3167_);
lean_ctor_set(v_reuseFailAlloc_3182_, 3, v_auxDeclNGen_3168_);
lean_ctor_set(v_reuseFailAlloc_3182_, 4, v_traceState_3169_);
lean_ctor_set(v_reuseFailAlloc_3182_, 5, v___x_2994_);
lean_ctor_set(v_reuseFailAlloc_3182_, 6, v_recordedDeps_3170_);
lean_ctor_set(v_reuseFailAlloc_3182_, 7, v_messages_3171_);
lean_ctor_set(v_reuseFailAlloc_3182_, 8, v_infoState_3172_);
lean_ctor_set(v_reuseFailAlloc_3182_, 9, v_snapshotTasks_3173_);
v___x_3180_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
lean_object* v___x_3181_; 
v___x_3181_ = lean_st_ref_put(v___y_3161_, v___x_3180_);
v_exportedInfo_x3f_3141_ = v_exportedInfo_x3f_2998_;
v___y_3142_ = v___y_3163_;
v___y_3143_ = v___y_3161_;
goto v___jp_3140_;
}
}
}
v___jp_3185_:
{
lean_object* v___x_3188_; uint8_t v___x_3189_; 
lean_inc(v_decl_2991_);
v___x_3188_ = l_Lean_Declaration_getTopLevelNames(v_decl_2991_);
v___x_3189_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3188_);
lean_dec(v___x_3188_);
if (v___x_3189_ == 0)
{
lean_dec(v___x_2996_);
if (lean_obj_tag(v_exportedInfo_x3f_2998_) == 0)
{
if (v___x_3189_ == 0)
{
lean_object* v_toCold_3190_; lean_object* v_options_3191_; uint8_t v_hasTrace_3192_; 
lean_dec_ref(v___x_2994_);
v_toCold_3190_ = lean_ctor_get(v___y_3186_, 0);
v_options_3191_ = lean_ctor_get(v_toCold_3190_, 2);
v_hasTrace_3192_ = lean_ctor_get_uint8(v_options_3191_, sizeof(void*)*1);
if (v_hasTrace_3192_ == 0)
{
lean_dec(v_cls_2995_);
v___y_3157_ = v___y_3186_;
v___y_3158_ = v___y_3187_;
goto v___jp_3156_;
}
else
{
lean_object* v_inheritedTraceOptions_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; uint8_t v___x_3196_; 
v_inheritedTraceOptions_3193_ = lean_ctor_get(v_toCold_3190_, 11);
v___x_3194_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2995_);
v___x_3195_ = l_Lean_Name_append(v___x_3194_, v_cls_2995_);
v___x_3196_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3193_, v_options_3191_, v___x_3195_);
lean_dec(v___x_3195_);
if (v___x_3196_ == 0)
{
lean_dec(v_cls_2995_);
v___y_3157_ = v___y_3186_;
v___y_3158_ = v___y_3187_;
goto v___jp_3156_;
}
else
{
lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3197_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_3198_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2995_, v___x_3197_, v___y_3186_, v___y_3187_);
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_dec_ref_known(v___x_3198_, 1);
v___y_3157_ = v___y_3186_;
v___y_3158_ = v___y_3187_;
goto v___jp_3156_;
}
else
{
lean_del_object(v___x_3109_);
lean_dec(v_snd_3107_);
lean_dec(v_fst_3106_);
lean_dec(v_fst_3102_);
lean_dec(v_decl_2991_);
return v___x_3198_;
}
}
}
}
else
{
lean_dec(v_cls_2995_);
v___y_3161_ = v___y_3187_;
v___y_3162_ = v___x_3189_;
v___y_3163_ = v___y_3186_;
goto v___jp_3160_;
}
}
else
{
lean_dec(v_cls_2995_);
v___y_3161_ = v___y_3187_;
v___y_3162_ = v___x_3189_;
v___y_3163_ = v___y_3186_;
goto v___jp_3160_;
}
}
else
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v_a_3201_; uint8_t v___x_3202_; 
lean_dec(v_exportedInfo_x3f_2998_);
lean_dec_ref(v___x_2994_);
v___x_3199_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3200_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3199_, v___y_3186_);
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
lean_inc(v_a_3201_);
lean_dec_ref(v___x_3200_);
v___x_3202_ = lean_unbox(v_a_3201_);
lean_dec(v_a_3201_);
if (v___x_3202_ == 0)
{
lean_object* v_toCold_3203_; lean_object* v_options_3204_; uint8_t v_hasTrace_3205_; 
v_toCold_3203_ = lean_ctor_get(v___y_3186_, 0);
v_options_3204_ = lean_ctor_get(v_toCold_3203_, 2);
v_hasTrace_3205_ = lean_ctor_get_uint8(v_options_3204_, sizeof(void*)*1);
if (v_hasTrace_3205_ == 0)
{
lean_dec(v_cls_2995_);
v_exportedInfo_x3f_3141_ = v___x_2996_;
v___y_3142_ = v___y_3186_;
v___y_3143_ = v___y_3187_;
goto v___jp_3140_;
}
else
{
lean_object* v_inheritedTraceOptions_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; uint8_t v___x_3209_; 
v_inheritedTraceOptions_3206_ = lean_ctor_get(v_toCold_3203_, 11);
v___x_3207_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2995_);
v___x_3208_ = l_Lean_Name_append(v___x_3207_, v_cls_2995_);
v___x_3209_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3206_, v_options_3204_, v___x_3208_);
lean_dec(v___x_3208_);
if (v___x_3209_ == 0)
{
lean_dec(v_cls_2995_);
v_exportedInfo_x3f_3141_ = v___x_2996_;
v___y_3142_ = v___y_3186_;
v___y_3143_ = v___y_3187_;
goto v___jp_3140_;
}
else
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3210_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_3211_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2995_, v___x_3210_, v___y_3186_, v___y_3187_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_dec_ref_known(v___x_3211_, 1);
v_exportedInfo_x3f_3141_ = v___x_2996_;
v___y_3142_ = v___y_3186_;
v___y_3143_ = v___y_3187_;
goto v___jp_3140_;
}
else
{
lean_del_object(v___x_3109_);
lean_dec(v_snd_3107_);
lean_dec(v_fst_3106_);
lean_dec(v_fst_3102_);
lean_dec(v___x_2996_);
lean_dec(v_decl_2991_);
return v___x_3211_;
}
}
}
}
else
{
lean_object* v_toCold_3212_; lean_object* v_options_3213_; uint8_t v_hasTrace_3214_; 
lean_dec(v___x_2996_);
v_toCold_3212_ = lean_ctor_get(v___y_3186_, 0);
v_options_3213_ = lean_ctor_get(v_toCold_3212_, 2);
v_hasTrace_3214_ = lean_ctor_get_uint8(v_options_3213_, sizeof(void*)*1);
if (v_hasTrace_3214_ == 0)
{
lean_dec(v_cls_2995_);
v___y_3153_ = v___y_3186_;
v___y_3154_ = v___y_3187_;
goto v___jp_3152_;
}
else
{
lean_object* v_inheritedTraceOptions_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; uint8_t v___x_3218_; 
v_inheritedTraceOptions_3215_ = lean_ctor_get(v_toCold_3212_, 11);
v___x_3216_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2995_);
v___x_3217_ = l_Lean_Name_append(v___x_3216_, v_cls_2995_);
v___x_3218_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3215_, v_options_3213_, v___x_3217_);
lean_dec(v___x_3217_);
if (v___x_3218_ == 0)
{
lean_dec(v_cls_2995_);
v___y_3153_ = v___y_3186_;
v___y_3154_ = v___y_3187_;
goto v___jp_3152_;
}
else
{
lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3219_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_3220_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2995_, v___x_3219_, v___y_3186_, v___y_3187_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_dec_ref_known(v___x_3220_, 1);
v___y_3153_ = v___y_3186_;
v___y_3154_ = v___y_3187_;
goto v___jp_3152_;
}
else
{
lean_del_object(v___x_3109_);
lean_dec(v_snd_3107_);
lean_dec(v_fst_3106_);
lean_dec(v_fst_3102_);
lean_dec(v_decl_2991_);
return v___x_3220_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed(lean_object* v_decl_3233_, lean_object* v_hasTrace_3234_, lean_object* v___x_3235_, lean_object* v___x_3236_, lean_object* v_cls_3237_, lean_object* v___x_3238_, lean_object* v_____x_3239_, lean_object* v_exportedInfo_x3f_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_){
_start:
{
uint8_t v_hasTrace_boxed_3244_; uint8_t v___x_53264__boxed_3245_; lean_object* v_res_3246_; 
v_hasTrace_boxed_3244_ = lean_unbox(v_hasTrace_3234_);
v___x_53264__boxed_3245_ = lean_unbox(v___x_3235_);
v_res_3246_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_decl_3233_, v_hasTrace_boxed_3244_, v___x_53264__boxed_3245_, v___x_3236_, v_cls_3237_, v___x_3238_, v_____x_3239_, v_exportedInfo_x3f_3240_, v___y_3241_, v___y_3242_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
return v_res_3246_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1(void){
_start:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3248_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__0));
v___x_3249_ = l_Lean_stringToMessageData(v___x_3248_);
return v___x_3249_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3(void){
_start:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3251_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__2));
v___x_3252_ = l_Lean_stringToMessageData(v___x_3251_);
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(lean_object* v___f_3253_, uint8_t v___x_3254_, lean_object* v_cls_3255_, lean_object* v___x_3256_, uint8_t v_forceExpose_3257_, lean_object* v_defn_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
lean_object* v_exportedInfo_x3f_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; uint8_t v___y_3278_; uint8_t v___y_3283_; lean_object* v___x_3288_; lean_object* v_env_3289_; lean_object* v___x_3290_; uint8_t v___y_3292_; lean_object* v_env_3308_; 
v___x_3288_ = lean_st_ref_get(v___y_3260_);
v_env_3289_ = lean_ctor_get(v___x_3288_, 0);
lean_inc_ref(v_env_3289_);
lean_dec(v___x_3288_);
v___x_3290_ = lean_st_ref_get(v___y_3260_);
v_env_3308_ = lean_ctor_get(v___x_3290_, 0);
lean_inc_ref(v_env_3308_);
lean_dec(v___x_3290_);
if (v_forceExpose_3257_ == 0)
{
goto v___jp_3309_;
}
else
{
if (v___x_3254_ == 0)
{
lean_dec_ref(v_env_3308_);
lean_dec_ref(v_env_3289_);
lean_dec(v_cls_3255_);
v_exportedInfo_x3f_3263_ = v___x_3256_;
v___y_3264_ = v___y_3259_;
v___y_3265_ = v___y_3260_;
goto v___jp_3262_;
}
else
{
goto v___jp_3309_;
}
}
v___jp_3262_:
{
lean_object* v_toConstantVal_3266_; lean_object* v_name_3267_; lean_object* v___x_3268_; uint8_t v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
v_toConstantVal_3266_ = lean_ctor_get(v_defn_3258_, 0);
v_name_3267_ = lean_ctor_get(v_toConstantVal_3266_, 0);
lean_inc(v_name_3267_);
v___x_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3268_, 0, v_defn_3258_);
v___x_3269_ = 0;
v___x_3270_ = lean_box(v___x_3269_);
v___x_3271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3271_, 0, v___x_3268_);
lean_ctor_set(v___x_3271_, 1, v___x_3270_);
v___x_3272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3272_, 0, v_name_3267_);
lean_ctor_set(v___x_3272_, 1, v___x_3271_);
lean_inc(v___y_3265_);
lean_inc_ref(v___y_3264_);
v___x_3273_ = lean_apply_5(v___f_3253_, v___x_3272_, v_exportedInfo_x3f_3263_, v___y_3264_, v___y_3265_, lean_box(0));
return v___x_3273_;
}
v___jp_3274_:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3279_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3279_, 0, v___y_3277_);
lean_ctor_set_uint8(v___x_3279_, sizeof(void*)*1, v___y_3278_);
v___x_3280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3279_);
v___x_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3280_);
v_exportedInfo_x3f_3263_ = v___x_3281_;
v___y_3264_ = v___y_3275_;
v___y_3265_ = v___y_3276_;
goto v___jp_3262_;
}
v___jp_3282_:
{
lean_object* v_toConstantVal_3284_; uint8_t v_safety_3285_; uint8_t v___x_3286_; uint8_t v___x_3287_; 
v_toConstantVal_3284_ = lean_ctor_get(v_defn_3258_, 0);
v_safety_3285_ = lean_ctor_get_uint8(v_defn_3258_, sizeof(void*)*4);
v___x_3286_ = 1;
v___x_3287_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3285_, v___x_3286_);
if (v___x_3287_ == 0)
{
lean_inc_ref(v_toConstantVal_3284_);
v___y_3275_ = v___y_3259_;
v___y_3276_ = v___y_3260_;
v___y_3277_ = v_toConstantVal_3284_;
v___y_3278_ = v___y_3283_;
goto v___jp_3274_;
}
else
{
lean_inc_ref(v_toConstantVal_3284_);
v___y_3275_ = v___y_3259_;
v___y_3276_ = v___y_3260_;
v___y_3277_ = v_toConstantVal_3284_;
v___y_3278_ = v___x_3254_;
goto v___jp_3274_;
}
}
v___jp_3291_:
{
lean_object* v_toCold_3293_; lean_object* v_options_3294_; uint8_t v_hasTrace_3295_; 
v_toCold_3293_ = lean_ctor_get(v___y_3259_, 0);
v_options_3294_ = lean_ctor_get(v_toCold_3293_, 2);
v_hasTrace_3295_ = lean_ctor_get_uint8(v_options_3294_, sizeof(void*)*1);
if (v_hasTrace_3295_ == 0)
{
lean_dec(v_cls_3255_);
v___y_3283_ = v___y_3292_;
goto v___jp_3282_;
}
else
{
lean_object* v_inheritedTraceOptions_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; uint8_t v___x_3299_; 
v_inheritedTraceOptions_3296_ = lean_ctor_get(v_toCold_3293_, 11);
v___x_3297_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3255_);
v___x_3298_ = l_Lean_Name_append(v___x_3297_, v_cls_3255_);
v___x_3299_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3296_, v_options_3294_, v___x_3298_);
lean_dec(v___x_3298_);
if (v___x_3299_ == 0)
{
lean_dec(v_cls_3255_);
v___y_3283_ = v___y_3292_;
goto v___jp_3282_;
}
else
{
lean_object* v_toConstantVal_3300_; lean_object* v_name_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v_toConstantVal_3300_ = lean_ctor_get(v_defn_3258_, 0);
v_name_3301_ = lean_ctor_get(v_toConstantVal_3300_, 0);
v___x_3302_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_3301_);
v___x_3303_ = l_Lean_MessageData_ofName(v_name_3301_);
v___x_3304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3302_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
v___x_3305_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_3306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3304_);
lean_ctor_set(v___x_3306_, 1, v___x_3305_);
v___x_3307_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3255_, v___x_3306_, v___y_3259_, v___y_3260_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_dec_ref_known(v___x_3307_, 1);
v___y_3283_ = v___y_3292_;
goto v___jp_3282_;
}
else
{
lean_dec_ref(v_defn_3258_);
lean_dec_ref(v___f_3253_);
return v___x_3307_;
}
}
}
}
v___jp_3309_:
{
lean_object* v___x_3310_; uint8_t v_isModule_3311_; 
v___x_3310_ = l_Lean_Environment_header(v_env_3289_);
lean_dec_ref(v_env_3289_);
v_isModule_3311_ = lean_ctor_get_uint8(v___x_3310_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3310_);
if (v_isModule_3311_ == 0)
{
lean_dec_ref(v_env_3308_);
lean_dec(v_cls_3255_);
v_exportedInfo_x3f_3263_ = v___x_3256_;
v___y_3264_ = v___y_3259_;
v___y_3265_ = v___y_3260_;
goto v___jp_3262_;
}
else
{
uint8_t v_isExporting_3312_; 
v_isExporting_3312_ = lean_ctor_get_uint8(v_env_3308_, sizeof(void*)*13);
lean_dec_ref(v_env_3308_);
if (v_isExporting_3312_ == 0)
{
lean_dec(v___x_3256_);
v___y_3292_ = v_isModule_3311_;
goto v___jp_3291_;
}
else
{
if (v___x_3254_ == 0)
{
lean_dec(v_cls_3255_);
v_exportedInfo_x3f_3263_ = v___x_3256_;
v___y_3264_ = v___y_3259_;
v___y_3265_ = v___y_3260_;
goto v___jp_3262_;
}
else
{
lean_dec(v___x_3256_);
v___y_3292_ = v___x_3254_;
goto v___jp_3291_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed(lean_object* v___f_3313_, lean_object* v___x_3314_, lean_object* v_cls_3315_, lean_object* v___x_3316_, lean_object* v_forceExpose_3317_, lean_object* v_defn_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
uint8_t v___x_53739__boxed_3322_; uint8_t v_forceExpose_boxed_3323_; lean_object* v_res_3324_; 
v___x_53739__boxed_3322_ = lean_unbox(v___x_3314_);
v_forceExpose_boxed_3323_ = lean_unbox(v_forceExpose_3317_);
v_res_3324_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v___f_3313_, v___x_53739__boxed_3322_, v_cls_3315_, v___x_3316_, v_forceExpose_boxed_3323_, v_defn_3318_, v___y_3319_, v___y_3320_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(lean_object* v_val_3325_, lean_object* v___f_3326_, lean_object* v_____r_3327_, lean_object* v_exportedInfo_x3f_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_){
_start:
{
lean_object* v_toConstantVal_3332_; lean_object* v_name_3333_; lean_object* v___x_3334_; uint8_t v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v_toConstantVal_3332_ = lean_ctor_get(v_val_3325_, 0);
v_name_3333_ = lean_ctor_get(v_toConstantVal_3332_, 0);
lean_inc(v_name_3333_);
v___x_3334_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3334_, 0, v_val_3325_);
v___x_3335_ = 1;
v___x_3336_ = lean_box(v___x_3335_);
v___x_3337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3334_);
lean_ctor_set(v___x_3337_, 1, v___x_3336_);
v___x_3338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3338_, 0, v_name_3333_);
lean_ctor_set(v___x_3338_, 1, v___x_3337_);
lean_inc(v___y_3330_);
lean_inc_ref(v___y_3329_);
v___x_3339_ = lean_apply_5(v___f_3326_, v___x_3338_, v_exportedInfo_x3f_3328_, v___y_3329_, v___y_3330_, lean_box(0));
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed(lean_object* v_val_3340_, lean_object* v___f_3341_, lean_object* v_____r_3342_, lean_object* v_exportedInfo_x3f_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(v_val_3340_, v___f_3341_, v_____r_3342_, v_exportedInfo_x3f_3343_, v___y_3344_, v___y_3345_);
lean_dec(v___y_3345_);
lean_dec_ref(v___y_3344_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(lean_object* v_val_3348_, uint8_t v___x_3349_, lean_object* v___f_3350_, lean_object* v_____r_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_){
_start:
{
lean_object* v_toConstantVal_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v_toConstantVal_3355_ = lean_ctor_get(v_val_3348_, 0);
lean_inc_ref(v_toConstantVal_3355_);
v___x_3356_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3356_, 0, v_toConstantVal_3355_);
lean_ctor_set_uint8(v___x_3356_, sizeof(void*)*1, v___x_3349_);
v___x_3357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3356_);
v___x_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3357_);
v___x_3359_ = lean_box(0);
lean_inc(v___y_3353_);
lean_inc_ref(v___y_3352_);
v___x_3360_ = lean_apply_5(v___f_3350_, v___x_3359_, v___x_3358_, v___y_3352_, v___y_3353_, lean_box(0));
return v___x_3360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed(lean_object* v_val_3361_, lean_object* v___x_3362_, lean_object* v___f_3363_, lean_object* v_____r_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
uint8_t v___x_53870__boxed_3368_; lean_object* v_res_3369_; 
v___x_53870__boxed_3368_ = lean_unbox(v___x_3362_);
v_res_3369_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(v_val_3361_, v___x_53870__boxed_3368_, v___f_3363_, v_____r_3364_, v___y_3365_, v___y_3366_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
lean_dec_ref(v_val_3361_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(lean_object* v_val_3370_, lean_object* v___f_3371_, lean_object* v_____r_3372_, lean_object* v_exportedInfo_x3f_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v_toConstantVal_3377_; lean_object* v_name_3378_; lean_object* v___x_3379_; uint8_t v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v_toConstantVal_3377_ = lean_ctor_get(v_val_3370_, 0);
v_name_3378_ = lean_ctor_get(v_toConstantVal_3377_, 0);
lean_inc(v_name_3378_);
v___x_3379_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3379_, 0, v_val_3370_);
v___x_3380_ = 3;
v___x_3381_ = lean_box(v___x_3380_);
v___x_3382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3379_);
lean_ctor_set(v___x_3382_, 1, v___x_3381_);
v___x_3383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3383_, 0, v_name_3378_);
lean_ctor_set(v___x_3383_, 1, v___x_3382_);
lean_inc(v___y_3375_);
lean_inc_ref(v___y_3374_);
v___x_3384_ = lean_apply_5(v___f_3371_, v___x_3383_, v_exportedInfo_x3f_3373_, v___y_3374_, v___y_3375_, lean_box(0));
return v___x_3384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed(lean_object* v_val_3385_, lean_object* v___f_3386_, lean_object* v_____r_3387_, lean_object* v_exportedInfo_x3f_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(v_val_3385_, v___f_3386_, v_____r_3387_, v_exportedInfo_x3f_3388_, v___y_3389_, v___y_3390_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(lean_object* v_val_3393_, lean_object* v___f_3394_, lean_object* v_____r_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
lean_object* v_toConstantVal_3399_; uint8_t v_isUnsafe_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v_toConstantVal_3399_ = lean_ctor_get(v_val_3393_, 0);
v_isUnsafe_3400_ = lean_ctor_get_uint8(v_val_3393_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_3399_);
v___x_3401_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3401_, 0, v_toConstantVal_3399_);
lean_ctor_set_uint8(v___x_3401_, sizeof(void*)*1, v_isUnsafe_3400_);
v___x_3402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
v___x_3403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3402_);
v___x_3404_ = lean_box(0);
lean_inc(v___y_3397_);
lean_inc_ref(v___y_3396_);
v___x_3405_ = lean_apply_5(v___f_3394_, v___x_3404_, v___x_3403_, v___y_3396_, v___y_3397_, lean_box(0));
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10___boxed(lean_object* v_val_3406_, lean_object* v___f_3407_, lean_object* v_____r_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v_res_3412_; 
v_res_3412_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_3406_, v___f_3407_, v_____r_3408_, v___y_3409_, v___y_3410_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec_ref(v_val_3406_);
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(lean_object* v_decl_3413_, uint8_t v___x_3414_, lean_object* v_cls_3415_, lean_object* v___x_3416_, lean_object* v___x_3417_, lean_object* v_____x_3418_, lean_object* v_exportedInfo_x3f_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v_a_3426_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v_a_3439_; uint8_t v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v_snd_3523_; lean_object* v_fst_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3656_; 
v_snd_3523_ = lean_ctor_get(v_____x_3418_, 1);
v_fst_3524_ = lean_ctor_get(v_____x_3418_, 0);
v_isSharedCheck_3656_ = !lean_is_exclusive(v_____x_3418_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3526_ = v_____x_3418_;
v_isShared_3527_ = v_isSharedCheck_3656_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_snd_3523_);
lean_inc(v_fst_3524_);
lean_dec(v_____x_3418_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3656_;
goto v_resetjp_3525_;
}
v___jp_3423_:
{
lean_object* v___x_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
v___x_3427_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3424_, v___y_3425_);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3434_ == 0)
{
lean_object* v_unused_3435_; 
v_unused_3435_ = lean_ctor_get(v___x_3427_, 0);
lean_dec(v_unused_3435_);
v___x_3429_ = v___x_3427_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_dec(v___x_3427_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
lean_ctor_set_tag(v___x_3429_, 1);
lean_ctor_set(v___x_3429_, 0, v_a_3426_);
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3426_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
v___jp_3436_:
{
lean_object* v___x_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3447_; 
v___x_3440_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3437_, v___y_3438_);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3447_ == 0)
{
lean_object* v_unused_3448_; 
v_unused_3448_ = lean_ctor_get(v___x_3440_, 0);
lean_dec(v_unused_3448_);
v___x_3442_ = v___x_3440_;
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
else
{
lean_dec(v___x_3440_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 0, v_a_3439_);
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3439_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
v___jp_3449_:
{
lean_object* v___x_3462_; 
lean_inc_ref(v___y_3451_);
v___x_3462_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3455_, v___y_3451_, v___y_3457_, v___y_3461_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v___x_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3509_; 
lean_dec_ref_known(v___x_3462_, 1);
lean_dec(v___y_3452_);
lean_inc_ref(v___y_3456_);
v___x_3463_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3456_, v___y_3460_);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3509_ == 0)
{
lean_object* v_unused_3510_; 
v_unused_3510_ = lean_ctor_get(v___x_3463_, 0);
lean_dec(v_unused_3510_);
v___x_3465_ = v___x_3463_;
v_isShared_3466_ = v_isSharedCheck_3509_;
goto v_resetjp_3464_;
}
else
{
lean_dec(v___x_3463_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3509_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; uint8_t v___x_3469_; 
v___x_3467_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3458_);
v___x_3468_ = l_Lean_Elab_async;
v___x_3469_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_3467_, v___x_3468_);
lean_dec_ref(v___x_3467_);
if (v___x_3469_ == 0)
{
lean_object* v___x_3470_; lean_object* v_r_3471_; 
lean_del_object(v___x_3465_);
lean_dec_ref(v___y_3459_);
lean_dec_ref(v___y_3453_);
v___x_3470_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3451_, v___y_3460_);
lean_dec_ref(v___x_3470_);
v_r_3471_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3413_, v___y_3458_, v___y_3460_);
if (lean_obj_tag(v_r_3471_) == 0)
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3481_; 
v_a_3472_ = lean_ctor_get(v_r_3471_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v_r_3471_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3474_ = v_r_3471_;
v_isShared_3475_ = v_isSharedCheck_3481_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v_r_3471_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3481_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3477_; 
lean_inc(v_a_3472_);
if (v_isShared_3475_ == 0)
{
lean_ctor_set_tag(v___x_3474_, 1);
v___x_3477_ = v___x_3474_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3472_);
v___x_3477_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
lean_object* v___x_3478_; 
v___x_3478_ = lean_apply_2(v___y_3454_, v___x_3477_, lean_box(0));
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_dec_ref_known(v___x_3478_, 1);
v___y_3437_ = v___y_3456_;
v___y_3438_ = v___y_3460_;
v_a_3439_ = v_a_3472_;
goto v___jp_3436_;
}
else
{
lean_object* v_a_3479_; 
lean_dec(v_a_3472_);
v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
lean_inc(v_a_3479_);
lean_dec_ref_known(v___x_3478_, 1);
v___y_3424_ = v___y_3456_;
v___y_3425_ = v___y_3460_;
v_a_3426_ = v_a_3479_;
goto v___jp_3423_;
}
}
}
}
else
{
lean_object* v_a_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; 
v_a_3482_ = lean_ctor_get(v_r_3471_, 0);
lean_inc(v_a_3482_);
lean_dec_ref_known(v_r_3471_, 1);
v___x_3483_ = lean_box(0);
v___x_3484_ = lean_apply_2(v___y_3454_, v___x_3483_, lean_box(0));
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_dec_ref_known(v___x_3484_, 1);
v___y_3424_ = v___y_3456_;
v___y_3425_ = v___y_3460_;
v_a_3426_ = v_a_3482_;
goto v___jp_3423_;
}
else
{
lean_object* v_a_3485_; 
lean_dec(v_a_3482_);
v_a_3485_ = lean_ctor_get(v___x_3484_, 0);
lean_inc(v_a_3485_);
lean_dec_ref_known(v___x_3484_, 1);
v___y_3424_ = v___y_3456_;
v___y_3425_ = v___y_3460_;
v_a_3426_ = v_a_3485_;
goto v___jp_3423_;
}
}
}
else
{
lean_object* v___x_3486_; lean_object* v___x_3488_; 
lean_dec_ref(v___y_3456_);
lean_dec_ref(v___y_3454_);
lean_dec_ref(v___y_3451_);
lean_dec(v_decl_3413_);
v___x_3486_ = l_IO_CancelToken_new();
if (v_isShared_3466_ == 0)
{
lean_ctor_set_tag(v___x_3465_, 1);
lean_ctor_set(v___x_3465_, 0, v___x_3486_);
v___x_3488_ = v___x_3465_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3486_);
v___x_3488_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3489_ = lean_unsigned_to_nat(0u);
v___x_3490_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_3491_ = l_Lean_Name_toString(v___x_3490_, v___x_3414_);
lean_inc_ref(v___x_3488_);
v___x_3492_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3453_, v___x_3488_, v___x_3491_, v___y_3458_, v___y_3460_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v_checked_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
lean_inc(v_a_3493_);
lean_dec_ref_known(v___x_3492_, 1);
v_checked_3494_ = lean_ctor_get(v___y_3459_, 2);
lean_inc_ref(v_checked_3494_);
lean_dec_ref(v___y_3459_);
v___x_3495_ = lean_io_map_task(v_a_3493_, v_checked_3494_, v___x_3489_, v___y_3450_);
v___x_3496_ = lean_box(0);
v___x_3497_ = lean_box(2);
v___x_3498_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3498_, 0, v___x_3496_);
lean_ctor_set(v___x_3498_, 1, v___x_3497_);
lean_ctor_set(v___x_3498_, 2, v___x_3488_);
lean_ctor_set(v___x_3498_, 3, v___x_3495_);
v___x_3499_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3498_, v___y_3460_);
return v___x_3499_;
}
else
{
lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3507_; 
lean_dec_ref(v___x_3488_);
lean_dec_ref(v___y_3459_);
v_a_3500_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3502_ = v___x_3492_;
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_dec(v___x_3492_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3505_; 
if (v_isShared_3503_ == 0)
{
v___x_3505_ = v___x_3502_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_a_3500_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3522_; 
lean_dec_ref(v___y_3459_);
lean_dec_ref(v___y_3456_);
lean_dec_ref(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec_ref(v___y_3451_);
lean_dec(v_decl_3413_);
v_a_3511_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3513_ = v___x_3462_;
v_isShared_3514_ = v_isSharedCheck_3522_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_a_3511_);
lean_dec(v___x_3462_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3522_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3520_; 
v___x_3515_ = lean_io_error_to_string(v_a_3511_);
v___x_3516_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3515_);
v___x_3517_ = l_Lean_MessageData_ofFormat(v___x_3516_);
v___x_3518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3518_, 0, v___y_3452_);
lean_ctor_set(v___x_3518_, 1, v___x_3517_);
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 0, v___x_3518_);
v___x_3520_ = v___x_3513_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3518_);
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
v_resetjp_3525_:
{
lean_object* v_fst_3528_; lean_object* v_snd_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3655_; 
v_fst_3528_ = lean_ctor_get(v_snd_3523_, 0);
v_snd_3529_ = lean_ctor_get(v_snd_3523_, 1);
v_isSharedCheck_3655_ = !lean_is_exclusive(v_snd_3523_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3531_ = v_snd_3523_;
v_isShared_3532_ = v_isSharedCheck_3655_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_snd_3529_);
lean_inc(v_fst_3528_);
lean_dec(v_snd_3523_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3655_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v_exportedInfo_x3f_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3580_; lean_object* v___y_3581_; uint8_t v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; uint8_t v___y_3587_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___x_3645_; lean_object* v_env_3646_; uint8_t v___x_3647_; 
v___x_3645_ = lean_st_ref_get(v___y_3421_);
v_env_3646_ = lean_ctor_get(v___x_3645_, 0);
lean_inc_ref(v_env_3646_);
lean_dec(v___x_3645_);
v___x_3647_ = l_Lean_Environment_containsOnBranch(v_env_3646_, v_fst_3524_);
lean_dec_ref(v_env_3646_);
if (v___x_3647_ == 0)
{
lean_del_object(v___x_3526_);
v___y_3619_ = v___y_3420_;
v___y_3620_ = v___y_3421_;
goto v___jp_3618_;
}
else
{
lean_object* v___x_3648_; lean_object* v_env_3649_; lean_object* v___x_3650_; lean_object* v___x_3652_; 
lean_del_object(v___x_3531_);
lean_dec(v_snd_3529_);
lean_dec(v_fst_3528_);
lean_dec(v_exportedInfo_x3f_3419_);
lean_dec(v___x_3417_);
lean_dec_ref(v___x_3416_);
lean_dec(v_cls_3415_);
lean_dec(v_decl_3413_);
v___x_3648_ = lean_st_ref_get(v___y_3421_);
v_env_3649_ = lean_ctor_get(v___x_3648_, 0);
lean_inc_ref(v_env_3649_);
lean_dec(v___x_3648_);
v___x_3650_ = lean_elab_environment_to_kernel_env(v_env_3649_);
if (v_isShared_3527_ == 0)
{
lean_ctor_set_tag(v___x_3526_, 1);
lean_ctor_set(v___x_3526_, 1, v_fst_3524_);
lean_ctor_set(v___x_3526_, 0, v___x_3650_);
v___x_3652_ = v___x_3526_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v___x_3650_);
lean_ctor_set(v_reuseFailAlloc_3654_, 1, v_fst_3524_);
v___x_3652_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
lean_object* v___x_3653_; 
v___x_3653_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3652_, v___y_3420_, v___y_3421_);
return v___x_3653_;
}
}
v___jp_3533_:
{
lean_object* v_ref_3539_; uint8_t v___x_3540_; uint8_t v___x_3541_; lean_object* v___x_3542_; 
v_ref_3539_ = lean_ctor_get(v___y_3534_, 2);
v___x_3540_ = 0;
v___x_3541_ = lean_unbox(v_snd_3529_);
lean_dec(v_snd_3529_);
lean_inc_ref(v___y_3537_);
v___x_3542_ = l_Lean_Environment_addConstAsync(v___y_3537_, v_fst_3524_, v___x_3541_, v___y_3538_, v___x_3540_, v___x_3414_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_object* v_a_3543_; lean_object* v_mainEnv_3544_; lean_object* v_asyncEnv_3545_; lean_object* v___f_3546_; lean_object* v___f_3547_; lean_object* v___x_3548_; 
lean_del_object(v___x_3531_);
v_a_3543_ = lean_ctor_get(v___x_3542_, 0);
lean_inc_n(v_a_3543_, 3);
lean_dec_ref_known(v___x_3542_, 1);
v_mainEnv_3544_ = lean_ctor_get(v_a_3543_, 0);
lean_inc_ref(v_mainEnv_3544_);
v_asyncEnv_3545_ = lean_ctor_get(v_a_3543_, 1);
lean_inc_ref_n(v_asyncEnv_3545_, 2);
lean_inc(v_ref_3539_);
lean_inc(v___y_3536_);
v___f_3546_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3546_, 0, v___y_3536_);
lean_closure_set(v___f_3546_, 1, v_a_3543_);
lean_closure_set(v___f_3546_, 2, v_ref_3539_);
lean_inc(v_decl_3413_);
v___f_3547_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3547_, 0, v_a_3543_);
lean_closure_set(v___f_3547_, 1, v_asyncEnv_3545_);
lean_closure_set(v___f_3547_, 2, v_decl_3413_);
v___x_3548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3548_, 0, v_fst_3528_);
if (lean_obj_tag(v___y_3535_) == 0)
{
lean_inc_ref(v___x_3548_);
lean_inc(v_ref_3539_);
v___y_3450_ = v___x_3540_;
v___y_3451_ = v_asyncEnv_3545_;
v___y_3452_ = v_ref_3539_;
v___y_3453_ = v___f_3547_;
v___y_3454_ = v___f_3546_;
v___y_3455_ = v_a_3543_;
v___y_3456_ = v_mainEnv_3544_;
v___y_3457_ = v___x_3548_;
v___y_3458_ = v___y_3534_;
v___y_3459_ = v___y_3537_;
v___y_3460_ = v___y_3536_;
v___y_3461_ = v___x_3548_;
goto v___jp_3449_;
}
else
{
lean_inc(v_ref_3539_);
v___y_3450_ = v___x_3540_;
v___y_3451_ = v_asyncEnv_3545_;
v___y_3452_ = v_ref_3539_;
v___y_3453_ = v___f_3547_;
v___y_3454_ = v___f_3546_;
v___y_3455_ = v_a_3543_;
v___y_3456_ = v_mainEnv_3544_;
v___y_3457_ = v___x_3548_;
v___y_3458_ = v___y_3534_;
v___y_3459_ = v___y_3537_;
v___y_3460_ = v___y_3536_;
v___y_3461_ = v___y_3535_;
goto v___jp_3449_;
}
}
else
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3562_; 
lean_dec_ref(v___y_3537_);
lean_dec(v___y_3535_);
lean_dec(v_fst_3528_);
lean_dec(v_decl_3413_);
v_a_3549_ = lean_ctor_get(v___x_3542_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3542_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3551_ = v___x_3542_;
v_isShared_3552_ = v_isSharedCheck_3562_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3542_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3562_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3557_; 
v___x_3553_ = lean_io_error_to_string(v_a_3549_);
v___x_3554_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3554_, 0, v___x_3553_);
v___x_3555_ = l_Lean_MessageData_ofFormat(v___x_3554_);
lean_inc(v_ref_3539_);
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 1, v___x_3555_);
lean_ctor_set(v___x_3531_, 0, v_ref_3539_);
v___x_3557_ = v___x_3531_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_ref_3539_);
lean_ctor_set(v_reuseFailAlloc_3561_, 1, v___x_3555_);
v___x_3557_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
lean_object* v___x_3559_; 
if (v_isShared_3552_ == 0)
{
lean_ctor_set(v___x_3551_, 0, v___x_3557_);
v___x_3559_ = v___x_3551_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3557_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
}
}
v___jp_3563_:
{
lean_object* v___x_3567_; 
v___x_3567_ = lean_st_ref_get(v___y_3566_);
if (lean_obj_tag(v_exportedInfo_x3f_3564_) == 0)
{
lean_object* v_env_3568_; lean_object* v___x_3569_; 
v_env_3568_ = lean_ctor_get(v___x_3567_, 0);
lean_inc_ref(v_env_3568_);
lean_dec(v___x_3567_);
v___x_3569_ = lean_box(0);
v___y_3534_ = v___y_3565_;
v___y_3535_ = v_exportedInfo_x3f_3564_;
v___y_3536_ = v___y_3566_;
v___y_3537_ = v_env_3568_;
v___y_3538_ = v___x_3569_;
goto v___jp_3533_;
}
else
{
lean_object* v_env_3570_; lean_object* v_val_3571_; uint8_t v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v_env_3570_ = lean_ctor_get(v___x_3567_, 0);
lean_inc_ref(v_env_3570_);
lean_dec(v___x_3567_);
v_val_3571_ = lean_ctor_get(v_exportedInfo_x3f_3564_, 0);
v___x_3572_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3571_);
v___x_3573_ = lean_box(v___x_3572_);
v___x_3574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3573_);
v___y_3534_ = v___y_3565_;
v___y_3535_ = v_exportedInfo_x3f_3564_;
v___y_3536_ = v___y_3566_;
v___y_3537_ = v_env_3570_;
v___y_3538_ = v___x_3574_;
goto v___jp_3533_;
}
}
v___jp_3575_:
{
lean_object* v___x_3578_; 
lean_inc(v_fst_3528_);
v___x_3578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3578_, 0, v_fst_3528_);
v_exportedInfo_x3f_3564_ = v___x_3578_;
v___y_3565_ = v___y_3576_;
v___y_3566_ = v___y_3577_;
goto v___jp_3563_;
}
v___jp_3579_:
{
lean_object* v___x_3582_; 
lean_inc(v_fst_3528_);
v___x_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3582_, 0, v_fst_3528_);
v_exportedInfo_x3f_3564_ = v___x_3582_;
v___y_3565_ = v___y_3580_;
v___y_3566_ = v___y_3581_;
goto v___jp_3563_;
}
v___jp_3583_:
{
if (v___y_3587_ == 0)
{
lean_object* v_toCold_3588_; lean_object* v_options_3589_; uint8_t v_hasTrace_3590_; 
lean_dec(v_exportedInfo_x3f_3419_);
lean_dec_ref(v___x_3416_);
v_toCold_3588_ = lean_ctor_get(v___y_3585_, 0);
v_options_3589_ = lean_ctor_get(v_toCold_3588_, 2);
v_hasTrace_3590_ = lean_ctor_get_uint8(v_options_3589_, sizeof(void*)*1);
if (v_hasTrace_3590_ == 0)
{
lean_dec(v_cls_3415_);
v___y_3580_ = v___y_3585_;
v___y_3581_ = v___y_3586_;
goto v___jp_3579_;
}
else
{
lean_object* v_inheritedTraceOptions_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; uint8_t v___x_3594_; 
v_inheritedTraceOptions_3591_ = lean_ctor_get(v_toCold_3588_, 11);
v___x_3592_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3415_);
v___x_3593_ = l_Lean_Name_append(v___x_3592_, v_cls_3415_);
v___x_3594_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3591_, v_options_3589_, v___x_3593_);
lean_dec(v___x_3593_);
if (v___x_3594_ == 0)
{
lean_dec(v_cls_3415_);
v___y_3580_ = v___y_3585_;
v___y_3581_ = v___y_3586_;
goto v___jp_3579_;
}
else
{
lean_object* v___x_3595_; lean_object* v___x_3596_; 
v___x_3595_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_3596_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3415_, v___x_3595_, v___y_3585_, v___y_3586_);
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_dec_ref_known(v___x_3596_, 1);
v___y_3580_ = v___y_3585_;
v___y_3581_ = v___y_3586_;
goto v___jp_3579_;
}
else
{
lean_del_object(v___x_3531_);
lean_dec(v_snd_3529_);
lean_dec(v_fst_3528_);
lean_dec(v_fst_3524_);
lean_dec(v_decl_3413_);
return v___x_3596_;
}
}
}
}
else
{
lean_object* v___x_3597_; lean_object* v_env_3598_; lean_object* v_nextMacroScope_3599_; lean_object* v_ngen_3600_; lean_object* v_auxDeclNGen_3601_; lean_object* v_traceState_3602_; lean_object* v_recordedDeps_3603_; lean_object* v_messages_3604_; lean_object* v_infoState_3605_; lean_object* v_snapshotTasks_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3616_; 
lean_dec(v_cls_3415_);
v___x_3597_ = lean_st_ref_take(v___y_3586_);
v_env_3598_ = lean_ctor_get(v___x_3597_, 0);
v_nextMacroScope_3599_ = lean_ctor_get(v___x_3597_, 1);
v_ngen_3600_ = lean_ctor_get(v___x_3597_, 2);
v_auxDeclNGen_3601_ = lean_ctor_get(v___x_3597_, 3);
v_traceState_3602_ = lean_ctor_get(v___x_3597_, 4);
v_recordedDeps_3603_ = lean_ctor_get(v___x_3597_, 6);
v_messages_3604_ = lean_ctor_get(v___x_3597_, 7);
v_infoState_3605_ = lean_ctor_get(v___x_3597_, 8);
v_snapshotTasks_3606_ = lean_ctor_get(v___x_3597_, 9);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3616_ == 0)
{
lean_object* v_unused_3617_; 
v_unused_3617_ = lean_ctor_get(v___x_3597_, 5);
lean_dec(v_unused_3617_);
v___x_3608_ = v___x_3597_;
v_isShared_3609_ = v_isSharedCheck_3616_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_snapshotTasks_3606_);
lean_inc(v_infoState_3605_);
lean_inc(v_messages_3604_);
lean_inc(v_recordedDeps_3603_);
lean_inc(v_traceState_3602_);
lean_inc(v_auxDeclNGen_3601_);
lean_inc(v_ngen_3600_);
lean_inc(v_nextMacroScope_3599_);
lean_inc(v_env_3598_);
lean_dec(v___x_3597_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3616_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3613_; 
v___x_3610_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3529_);
lean_inc(v_fst_3524_);
v___x_3611_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3610_, v_env_3598_, v_fst_3524_, v_snd_3529_, v___y_3584_);
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 5, v___x_3416_);
lean_ctor_set(v___x_3608_, 0, v___x_3611_);
v___x_3613_ = v___x_3608_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3611_);
lean_ctor_set(v_reuseFailAlloc_3615_, 1, v_nextMacroScope_3599_);
lean_ctor_set(v_reuseFailAlloc_3615_, 2, v_ngen_3600_);
lean_ctor_set(v_reuseFailAlloc_3615_, 3, v_auxDeclNGen_3601_);
lean_ctor_set(v_reuseFailAlloc_3615_, 4, v_traceState_3602_);
lean_ctor_set(v_reuseFailAlloc_3615_, 5, v___x_3416_);
lean_ctor_set(v_reuseFailAlloc_3615_, 6, v_recordedDeps_3603_);
lean_ctor_set(v_reuseFailAlloc_3615_, 7, v_messages_3604_);
lean_ctor_set(v_reuseFailAlloc_3615_, 8, v_infoState_3605_);
lean_ctor_set(v_reuseFailAlloc_3615_, 9, v_snapshotTasks_3606_);
v___x_3613_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
lean_object* v___x_3614_; 
v___x_3614_ = lean_st_ref_put(v___y_3586_, v___x_3613_);
v_exportedInfo_x3f_3564_ = v_exportedInfo_x3f_3419_;
v___y_3565_ = v___y_3585_;
v___y_3566_ = v___y_3586_;
goto v___jp_3563_;
}
}
}
}
v___jp_3618_:
{
lean_object* v___x_3621_; uint8_t v___x_3622_; 
lean_inc(v_decl_3413_);
v___x_3621_ = l_Lean_Declaration_getTopLevelNames(v_decl_3413_);
v___x_3622_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3621_);
lean_dec(v___x_3621_);
if (v___x_3622_ == 0)
{
lean_dec(v___x_3417_);
if (lean_obj_tag(v_exportedInfo_x3f_3419_) == 0)
{
v___y_3584_ = v___x_3622_;
v___y_3585_ = v___y_3619_;
v___y_3586_ = v___y_3620_;
v___y_3587_ = v___x_3622_;
goto v___jp_3583_;
}
else
{
v___y_3584_ = v___x_3622_;
v___y_3585_ = v___y_3619_;
v___y_3586_ = v___y_3620_;
v___y_3587_ = v___x_3414_;
goto v___jp_3583_;
}
}
else
{
lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v_a_3625_; uint8_t v___x_3626_; 
lean_dec(v_exportedInfo_x3f_3419_);
lean_dec_ref(v___x_3416_);
v___x_3623_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3624_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3623_, v___y_3619_);
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
lean_inc(v_a_3625_);
lean_dec_ref(v___x_3624_);
v___x_3626_ = lean_unbox(v_a_3625_);
lean_dec(v_a_3625_);
if (v___x_3626_ == 0)
{
lean_object* v_toCold_3627_; lean_object* v_options_3628_; uint8_t v_hasTrace_3629_; 
v_toCold_3627_ = lean_ctor_get(v___y_3619_, 0);
v_options_3628_ = lean_ctor_get(v_toCold_3627_, 2);
v_hasTrace_3629_ = lean_ctor_get_uint8(v_options_3628_, sizeof(void*)*1);
if (v_hasTrace_3629_ == 0)
{
lean_dec(v_cls_3415_);
v_exportedInfo_x3f_3564_ = v___x_3417_;
v___y_3565_ = v___y_3619_;
v___y_3566_ = v___y_3620_;
goto v___jp_3563_;
}
else
{
lean_object* v_inheritedTraceOptions_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; uint8_t v___x_3633_; 
v_inheritedTraceOptions_3630_ = lean_ctor_get(v_toCold_3627_, 11);
v___x_3631_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3415_);
v___x_3632_ = l_Lean_Name_append(v___x_3631_, v_cls_3415_);
v___x_3633_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3630_, v_options_3628_, v___x_3632_);
lean_dec(v___x_3632_);
if (v___x_3633_ == 0)
{
lean_dec(v_cls_3415_);
v_exportedInfo_x3f_3564_ = v___x_3417_;
v___y_3565_ = v___y_3619_;
v___y_3566_ = v___y_3620_;
goto v___jp_3563_;
}
else
{
lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3634_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_3635_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3415_, v___x_3634_, v___y_3619_, v___y_3620_);
if (lean_obj_tag(v___x_3635_) == 0)
{
lean_dec_ref_known(v___x_3635_, 1);
v_exportedInfo_x3f_3564_ = v___x_3417_;
v___y_3565_ = v___y_3619_;
v___y_3566_ = v___y_3620_;
goto v___jp_3563_;
}
else
{
lean_del_object(v___x_3531_);
lean_dec(v_snd_3529_);
lean_dec(v_fst_3528_);
lean_dec(v_fst_3524_);
lean_dec(v___x_3417_);
lean_dec(v_decl_3413_);
return v___x_3635_;
}
}
}
}
else
{
lean_object* v_toCold_3636_; lean_object* v_options_3637_; uint8_t v_hasTrace_3638_; 
lean_dec(v___x_3417_);
v_toCold_3636_ = lean_ctor_get(v___y_3619_, 0);
v_options_3637_ = lean_ctor_get(v_toCold_3636_, 2);
v_hasTrace_3638_ = lean_ctor_get_uint8(v_options_3637_, sizeof(void*)*1);
if (v_hasTrace_3638_ == 0)
{
lean_dec(v_cls_3415_);
v___y_3576_ = v___y_3619_;
v___y_3577_ = v___y_3620_;
goto v___jp_3575_;
}
else
{
lean_object* v_inheritedTraceOptions_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; uint8_t v___x_3642_; 
v_inheritedTraceOptions_3639_ = lean_ctor_get(v_toCold_3636_, 11);
v___x_3640_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3415_);
v___x_3641_ = l_Lean_Name_append(v___x_3640_, v_cls_3415_);
v___x_3642_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3639_, v_options_3637_, v___x_3641_);
lean_dec(v___x_3641_);
if (v___x_3642_ == 0)
{
lean_dec(v_cls_3415_);
v___y_3576_ = v___y_3619_;
v___y_3577_ = v___y_3620_;
goto v___jp_3575_;
}
else
{
lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3643_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_3644_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3415_, v___x_3643_, v___y_3619_, v___y_3620_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_dec_ref_known(v___x_3644_, 1);
v___y_3576_ = v___y_3619_;
v___y_3577_ = v___y_3620_;
goto v___jp_3575_;
}
else
{
lean_del_object(v___x_3531_);
lean_dec(v_snd_3529_);
lean_dec(v_fst_3528_);
lean_dec(v_fst_3524_);
lean_dec(v_decl_3413_);
return v___x_3644_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14___boxed(lean_object* v_decl_3657_, lean_object* v___x_3658_, lean_object* v_cls_3659_, lean_object* v___x_3660_, lean_object* v___x_3661_, lean_object* v_____x_3662_, lean_object* v_exportedInfo_x3f_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
uint8_t v___x_54001__boxed_3667_; lean_object* v_res_3668_; 
v___x_54001__boxed_3667_ = lean_unbox(v___x_3658_);
v_res_3668_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(v_decl_3657_, v___x_54001__boxed_3667_, v_cls_3659_, v___x_3660_, v___x_3661_, v_____x_3662_, v_exportedInfo_x3f_3663_, v___y_3664_, v___y_3665_);
lean_dec(v___y_3665_);
lean_dec_ref(v___y_3664_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(lean_object* v___f_3669_, uint8_t v_forceExpose_3670_, uint8_t v___x_3671_, lean_object* v___x_3672_, lean_object* v_cls_3673_, lean_object* v_defn_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_){
_start:
{
lean_object* v_exportedInfo_x3f_3679_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; uint8_t v___y_3694_; lean_object* v___x_3698_; lean_object* v_env_3699_; lean_object* v___x_3700_; 
v___x_3698_ = lean_st_ref_get(v___y_3676_);
v_env_3699_ = lean_ctor_get(v___x_3698_, 0);
lean_inc_ref(v_env_3699_);
lean_dec(v___x_3698_);
v___x_3700_ = lean_st_ref_get(v___y_3676_);
if (v_forceExpose_3670_ == 0)
{
if (v___x_3671_ == 0)
{
lean_dec(v___x_3700_);
lean_dec_ref(v_env_3699_);
lean_dec(v_cls_3673_);
v_exportedInfo_x3f_3679_ = v___x_3672_;
v___y_3680_ = v___y_3675_;
v___y_3681_ = v___y_3676_;
goto v___jp_3678_;
}
else
{
lean_object* v_env_3701_; lean_object* v___x_3702_; uint8_t v_isModule_3703_; 
v_env_3701_ = lean_ctor_get(v___x_3700_, 0);
lean_inc_ref(v_env_3701_);
lean_dec(v___x_3700_);
v___x_3702_ = l_Lean_Environment_header(v_env_3699_);
lean_dec_ref(v_env_3699_);
v_isModule_3703_ = lean_ctor_get_uint8(v___x_3702_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3702_);
if (v_isModule_3703_ == 0)
{
lean_dec_ref(v_env_3701_);
lean_dec(v_cls_3673_);
v_exportedInfo_x3f_3679_ = v___x_3672_;
v___y_3680_ = v___y_3675_;
v___y_3681_ = v___y_3676_;
goto v___jp_3678_;
}
else
{
uint8_t v_isExporting_3704_; lean_object* v___y_3706_; lean_object* v___y_3707_; 
v_isExporting_3704_ = lean_ctor_get_uint8(v_env_3701_, sizeof(void*)*13);
lean_dec_ref(v_env_3701_);
if (v_isExporting_3704_ == 0)
{
lean_object* v_toCold_3712_; lean_object* v_options_3713_; uint8_t v_hasTrace_3714_; 
lean_dec(v___x_3672_);
v_toCold_3712_ = lean_ctor_get(v___y_3675_, 0);
v_options_3713_ = lean_ctor_get(v_toCold_3712_, 2);
v_hasTrace_3714_ = lean_ctor_get_uint8(v_options_3713_, sizeof(void*)*1);
if (v_hasTrace_3714_ == 0)
{
lean_dec(v_cls_3673_);
v___y_3706_ = v___y_3675_;
v___y_3707_ = v___y_3676_;
goto v___jp_3705_;
}
else
{
lean_object* v_inheritedTraceOptions_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; uint8_t v___x_3718_; 
v_inheritedTraceOptions_3715_ = lean_ctor_get(v_toCold_3712_, 11);
v___x_3716_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3673_);
v___x_3717_ = l_Lean_Name_append(v___x_3716_, v_cls_3673_);
v___x_3718_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3715_, v_options_3713_, v___x_3717_);
lean_dec(v___x_3717_);
if (v___x_3718_ == 0)
{
lean_dec(v_cls_3673_);
v___y_3706_ = v___y_3675_;
v___y_3707_ = v___y_3676_;
goto v___jp_3705_;
}
else
{
lean_object* v_toConstantVal_3719_; lean_object* v_name_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
v_toConstantVal_3719_ = lean_ctor_get(v_defn_3674_, 0);
v_name_3720_ = lean_ctor_get(v_toConstantVal_3719_, 0);
v___x_3721_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_3720_);
v___x_3722_ = l_Lean_MessageData_ofName(v_name_3720_);
v___x_3723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3721_);
lean_ctor_set(v___x_3723_, 1, v___x_3722_);
v___x_3724_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_3725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3723_);
lean_ctor_set(v___x_3725_, 1, v___x_3724_);
v___x_3726_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3673_, v___x_3725_, v___y_3675_, v___y_3676_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_dec_ref_known(v___x_3726_, 1);
v___y_3706_ = v___y_3675_;
v___y_3707_ = v___y_3676_;
goto v___jp_3705_;
}
else
{
lean_dec_ref(v_defn_3674_);
lean_dec_ref(v___f_3669_);
return v___x_3726_;
}
}
}
}
else
{
lean_dec(v_cls_3673_);
v_exportedInfo_x3f_3679_ = v___x_3672_;
v___y_3680_ = v___y_3675_;
v___y_3681_ = v___y_3676_;
goto v___jp_3678_;
}
v___jp_3705_:
{
lean_object* v_toConstantVal_3708_; uint8_t v_safety_3709_; uint8_t v___x_3710_; uint8_t v___x_3711_; 
v_toConstantVal_3708_ = lean_ctor_get(v_defn_3674_, 0);
v_safety_3709_ = lean_ctor_get_uint8(v_defn_3674_, sizeof(void*)*4);
v___x_3710_ = 1;
v___x_3711_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3709_, v___x_3710_);
if (v___x_3711_ == 0)
{
lean_inc_ref(v_toConstantVal_3708_);
v___y_3691_ = v_toConstantVal_3708_;
v___y_3692_ = v___y_3707_;
v___y_3693_ = v___y_3706_;
v___y_3694_ = v_isModule_3703_;
goto v___jp_3690_;
}
else
{
lean_inc_ref(v_toConstantVal_3708_);
v___y_3691_ = v_toConstantVal_3708_;
v___y_3692_ = v___y_3707_;
v___y_3693_ = v___y_3706_;
v___y_3694_ = v_isExporting_3704_;
goto v___jp_3690_;
}
}
}
}
}
else
{
lean_dec(v___x_3700_);
lean_dec_ref(v_env_3699_);
lean_dec(v_cls_3673_);
v_exportedInfo_x3f_3679_ = v___x_3672_;
v___y_3680_ = v___y_3675_;
v___y_3681_ = v___y_3676_;
goto v___jp_3678_;
}
v___jp_3678_:
{
lean_object* v_toConstantVal_3682_; lean_object* v_name_3683_; lean_object* v___x_3684_; uint8_t v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; 
v_toConstantVal_3682_ = lean_ctor_get(v_defn_3674_, 0);
v_name_3683_ = lean_ctor_get(v_toConstantVal_3682_, 0);
lean_inc(v_name_3683_);
v___x_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3684_, 0, v_defn_3674_);
v___x_3685_ = 0;
v___x_3686_ = lean_box(v___x_3685_);
v___x_3687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3684_);
lean_ctor_set(v___x_3687_, 1, v___x_3686_);
v___x_3688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3688_, 0, v_name_3683_);
lean_ctor_set(v___x_3688_, 1, v___x_3687_);
lean_inc(v___y_3681_);
lean_inc_ref(v___y_3680_);
v___x_3689_ = lean_apply_5(v___f_3669_, v___x_3688_, v_exportedInfo_x3f_3679_, v___y_3680_, v___y_3681_, lean_box(0));
return v___x_3689_;
}
v___jp_3690_:
{
lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; 
v___x_3695_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3695_, 0, v___y_3691_);
lean_ctor_set_uint8(v___x_3695_, sizeof(void*)*1, v___y_3694_);
v___x_3696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3695_);
v___x_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3696_);
v_exportedInfo_x3f_3679_ = v___x_3697_;
v___y_3680_ = v___y_3693_;
v___y_3681_ = v___y_3692_;
goto v___jp_3678_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11___boxed(lean_object* v___f_3727_, lean_object* v_forceExpose_3728_, lean_object* v___x_3729_, lean_object* v___x_3730_, lean_object* v_cls_3731_, lean_object* v_defn_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_){
_start:
{
uint8_t v_forceExpose_boxed_3736_; uint8_t v___x_54479__boxed_3737_; lean_object* v_res_3738_; 
v_forceExpose_boxed_3736_ = lean_unbox(v_forceExpose_3728_);
v___x_54479__boxed_3737_ = lean_unbox(v___x_3729_);
v_res_3738_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(v___f_3727_, v_forceExpose_boxed_3736_, v___x_54479__boxed_3737_, v___x_3730_, v_cls_3731_, v_defn_3732_, v___y_3733_, v___y_3734_);
lean_dec(v___y_3734_);
lean_dec_ref(v___y_3733_);
return v_res_3738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(lean_object* v_val_3739_, lean_object* v___f_3740_, lean_object* v_____r_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
lean_object* v_toConstantVal_3745_; uint8_t v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; 
v_toConstantVal_3745_ = lean_ctor_get(v_val_3739_, 0);
v___x_3746_ = 0;
lean_inc_ref(v_toConstantVal_3745_);
v___x_3747_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3747_, 0, v_toConstantVal_3745_);
lean_ctor_set_uint8(v___x_3747_, sizeof(void*)*1, v___x_3746_);
v___x_3748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3748_, 0, v___x_3747_);
v___x_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3748_);
v___x_3750_ = lean_box(0);
lean_inc(v___y_3743_);
lean_inc_ref(v___y_3742_);
v___x_3751_ = lean_apply_5(v___f_3740_, v___x_3750_, v___x_3749_, v___y_3742_, v___y_3743_, lean_box(0));
return v___x_3751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed(lean_object* v_val_3752_, lean_object* v___f_3753_, lean_object* v_____r_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
lean_object* v_res_3758_; 
v_res_3758_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_val_3752_, v___f_3753_, v_____r_3754_, v___y_3755_, v___y_3756_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec_ref(v_val_3752_);
return v_res_3758_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(lean_object* v_x_3759_, lean_object* v_x_3760_){
_start:
{
if (lean_obj_tag(v_x_3760_) == 0)
{
return v_x_3759_;
}
else
{
lean_object* v_head_3761_; lean_object* v_tail_3762_; lean_object* v___x_3763_; 
v_head_3761_ = lean_ctor_get(v_x_3760_, 0);
lean_inc(v_head_3761_);
v_tail_3762_ = lean_ctor_get(v_x_3760_, 1);
lean_inc(v_tail_3762_);
lean_dec_ref_known(v_x_3760_, 2);
v___x_3763_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(v_x_3759_, v_head_3761_);
v_x_3759_ = v___x_3763_;
v_x_3760_ = v_tail_3762_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0(void){
_start:
{
lean_object* v_cls_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; 
v_cls_3765_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_3766_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
v___x_3767_ = l_Lean_Name_append(v___x_3766_, v_cls_3765_);
return v___x_3767_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2(void){
_start:
{
lean_object* v___x_3769_; lean_object* v___x_3770_; 
v___x_3769_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1));
v___x_3770_ = l_Lean_stringToMessageData(v___x_3769_);
return v___x_3770_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4(void){
_start:
{
lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3772_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3));
v___x_3773_ = l_Lean_stringToMessageData(v___x_3772_);
return v___x_3773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore(lean_object* v_decl_3774_, uint8_t v_forceExpose_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_){
_start:
{
lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v_a_3782_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v_a_3795_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v_a_3808_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v_a_3821_; lean_object* v_toCold_3831_; lean_object* v_options_3832_; lean_object* v_inheritedTraceOptions_3833_; uint8_t v_hasTrace_3834_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; uint8_t v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3910_; lean_object* v___y_3911_; uint8_t v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; uint8_t v___y_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v_exportedInfo_x3f_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; uint8_t v___y_3955_; lean_object* v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; uint8_t v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v_cls_3968_; lean_object* v___y_3970_; lean_object* v_options_3971_; lean_object* v_inheritedTraceOptions_3972_; lean_object* v___y_3973_; 
v_toCold_3831_ = lean_ctor_get(v_a_3776_, 0);
v_options_3832_ = lean_ctor_get(v_toCold_3831_, 2);
v_inheritedTraceOptions_3833_ = lean_ctor_get(v_toCold_3831_, 11);
v_hasTrace_3834_ = lean_ctor_get_uint8(v_options_3832_, sizeof(void*)*1);
v_cls_3968_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
if (v_hasTrace_3834_ == 0)
{
lean_object* v___x_3980_; lean_object* v_env_3981_; lean_object* v_nextMacroScope_3982_; lean_object* v_ngen_3983_; lean_object* v_auxDeclNGen_3984_; lean_object* v_traceState_3985_; lean_object* v_recordedDeps_3986_; lean_object* v_messages_3987_; lean_object* v_infoState_3988_; lean_object* v_snapshotTasks_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_4193_; 
v___x_3980_ = lean_st_ref_take(v_a_3777_);
v_env_3981_ = lean_ctor_get(v___x_3980_, 0);
v_nextMacroScope_3982_ = lean_ctor_get(v___x_3980_, 1);
v_ngen_3983_ = lean_ctor_get(v___x_3980_, 2);
v_auxDeclNGen_3984_ = lean_ctor_get(v___x_3980_, 3);
v_traceState_3985_ = lean_ctor_get(v___x_3980_, 4);
v_recordedDeps_3986_ = lean_ctor_get(v___x_3980_, 6);
v_messages_3987_ = lean_ctor_get(v___x_3980_, 7);
v_infoState_3988_ = lean_ctor_get(v___x_3980_, 8);
v_snapshotTasks_3989_ = lean_ctor_get(v___x_3980_, 9);
v_isSharedCheck_4193_ = !lean_is_exclusive(v___x_3980_);
if (v_isSharedCheck_4193_ == 0)
{
lean_object* v_unused_4194_; 
v_unused_4194_ = lean_ctor_get(v___x_3980_, 5);
lean_dec(v_unused_4194_);
v___x_3991_ = v___x_3980_;
v_isShared_3992_ = v_isSharedCheck_4193_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_snapshotTasks_3989_);
lean_inc(v_infoState_3988_);
lean_inc(v_messages_3987_);
lean_inc(v_recordedDeps_3986_);
lean_inc(v_traceState_3985_);
lean_inc(v_auxDeclNGen_3984_);
lean_inc(v_ngen_3983_);
lean_inc(v_nextMacroScope_3982_);
lean_inc(v_env_3981_);
lean_dec(v___x_3980_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_4193_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; uint8_t v___y_3997_; uint8_t v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___x_4027_; 
lean_inc(v_decl_3774_);
v___x_3993_ = l_Lean_Declaration_getNames(v_decl_3774_);
v___x_3994_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_3981_, v___x_3993_);
v___x_3995_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_3992_ == 0)
{
lean_ctor_set(v___x_3991_, 5, v___x_3995_);
lean_ctor_set(v___x_3991_, 0, v___x_3994_);
v___x_4027_ = v___x_3991_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v___x_3994_);
lean_ctor_set(v_reuseFailAlloc_4192_, 1, v_nextMacroScope_3982_);
lean_ctor_set(v_reuseFailAlloc_4192_, 2, v_ngen_3983_);
lean_ctor_set(v_reuseFailAlloc_4192_, 3, v_auxDeclNGen_3984_);
lean_ctor_set(v_reuseFailAlloc_4192_, 4, v_traceState_3985_);
lean_ctor_set(v_reuseFailAlloc_4192_, 5, v___x_3995_);
lean_ctor_set(v_reuseFailAlloc_4192_, 6, v_recordedDeps_3986_);
lean_ctor_set(v_reuseFailAlloc_4192_, 7, v_messages_3987_);
lean_ctor_set(v_reuseFailAlloc_4192_, 8, v_infoState_3988_);
lean_ctor_set(v_reuseFailAlloc_4192_, 9, v_snapshotTasks_3989_);
v___x_4027_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4026_;
}
v___jp_3996_:
{
lean_object* v___x_4004_; lean_object* v_env_4005_; lean_object* v_nextMacroScope_4006_; lean_object* v_ngen_4007_; lean_object* v_auxDeclNGen_4008_; lean_object* v_traceState_4009_; lean_object* v_recordedDeps_4010_; lean_object* v_messages_4011_; lean_object* v_infoState_4012_; lean_object* v_snapshotTasks_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4024_; 
v___x_4004_ = lean_st_ref_take(v___y_4002_);
v_env_4005_ = lean_ctor_get(v___x_4004_, 0);
v_nextMacroScope_4006_ = lean_ctor_get(v___x_4004_, 1);
v_ngen_4007_ = lean_ctor_get(v___x_4004_, 2);
v_auxDeclNGen_4008_ = lean_ctor_get(v___x_4004_, 3);
v_traceState_4009_ = lean_ctor_get(v___x_4004_, 4);
v_recordedDeps_4010_ = lean_ctor_get(v___x_4004_, 6);
v_messages_4011_ = lean_ctor_get(v___x_4004_, 7);
v_infoState_4012_ = lean_ctor_get(v___x_4004_, 8);
v_snapshotTasks_4013_ = lean_ctor_get(v___x_4004_, 9);
v_isSharedCheck_4024_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4024_ == 0)
{
lean_object* v_unused_4025_; 
v_unused_4025_ = lean_ctor_get(v___x_4004_, 5);
lean_dec(v_unused_4025_);
v___x_4015_ = v___x_4004_;
v_isShared_4016_ = v_isSharedCheck_4024_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_snapshotTasks_4013_);
lean_inc(v_infoState_4012_);
lean_inc(v_messages_4011_);
lean_inc(v_recordedDeps_4010_);
lean_inc(v_traceState_4009_);
lean_inc(v_auxDeclNGen_4008_);
lean_inc(v_ngen_4007_);
lean_inc(v_nextMacroScope_4006_);
lean_inc(v_env_4005_);
lean_dec(v___x_4004_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4024_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4021_; 
v___x_4017_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4018_ = lean_box(v___y_3998_);
lean_inc(v___y_3999_);
v___x_4019_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4017_, v_env_4005_, v___y_3999_, v___x_4018_, v___y_3997_);
if (v_isShared_4016_ == 0)
{
lean_ctor_set(v___x_4015_, 5, v___x_3995_);
lean_ctor_set(v___x_4015_, 0, v___x_4019_);
v___x_4021_ = v___x_4015_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v___x_4019_);
lean_ctor_set(v_reuseFailAlloc_4023_, 1, v_nextMacroScope_4006_);
lean_ctor_set(v_reuseFailAlloc_4023_, 2, v_ngen_4007_);
lean_ctor_set(v_reuseFailAlloc_4023_, 3, v_auxDeclNGen_4008_);
lean_ctor_set(v_reuseFailAlloc_4023_, 4, v_traceState_4009_);
lean_ctor_set(v_reuseFailAlloc_4023_, 5, v___x_3995_);
lean_ctor_set(v_reuseFailAlloc_4023_, 6, v_recordedDeps_4010_);
lean_ctor_set(v_reuseFailAlloc_4023_, 7, v_messages_4011_);
lean_ctor_set(v_reuseFailAlloc_4023_, 8, v_infoState_4012_);
lean_ctor_set(v_reuseFailAlloc_4023_, 9, v_snapshotTasks_4013_);
v___x_4021_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
lean_object* v___x_4022_; 
v___x_4022_ = lean_st_ref_put(v___y_4002_, v___x_4021_);
v___y_3940_ = v___y_3998_;
v___y_3941_ = v___y_3999_;
v___y_3942_ = v___y_4000_;
v_exportedInfo_x3f_3943_ = v___y_4003_;
v___y_3944_ = v___y_4001_;
v___y_3945_ = v___y_4002_;
goto v___jp_3939_;
}
}
}
v_reusejp_4026_:
{
lean_object* v___x_4028_; lean_object* v___x_4029_; uint8_t v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v_fst_4068_; lean_object* v_fst_4069_; uint8_t v_snd_4070_; lean_object* v_exportedInfo_x3f_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4083_; lean_object* v_exportedInfo_x3f_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; uint8_t v___y_4096_; lean_object* v___y_4101_; lean_object* v_toConstantVal_4102_; uint8_t v_safety_4103_; uint8_t v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4110_; uint8_t v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v_defn_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; 
v___x_4028_ = lean_st_ref_put(v_a_3777_, v___x_4027_);
v___x_4029_ = lean_box(0);
switch(lean_obj_tag(v_decl_3774_))
{
case 2:
{
lean_object* v_val_4142_; lean_object* v_exportedInfo_x3f_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___x_4151_; 
v_val_4142_ = lean_ctor_get(v_decl_3774_, 0);
v___x_4151_ = lean_st_ref_get(v_a_3777_);
if (v_forceExpose_3775_ == 0)
{
lean_object* v_env_4152_; lean_object* v___x_4153_; uint8_t v_isModule_4154_; 
v_env_4152_ = lean_ctor_get(v___x_4151_, 0);
lean_inc_ref(v_env_4152_);
lean_dec(v___x_4151_);
v___x_4153_ = l_Lean_Environment_header(v_env_4152_);
lean_dec_ref(v_env_4152_);
v_isModule_4154_ = lean_ctor_get_uint8(v___x_4153_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4153_);
if (v_isModule_4154_ == 0)
{
v_exportedInfo_x3f_4144_ = v___x_4029_;
v___y_4145_ = v_a_3776_;
v___y_4146_ = v_a_3777_;
goto v___jp_4143_;
}
else
{
lean_object* v_toConstantVal_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
v_toConstantVal_4155_ = lean_ctor_get(v_val_4142_, 0);
lean_inc_ref(v_toConstantVal_4155_);
v___x_4156_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4156_, 0, v_toConstantVal_4155_);
lean_ctor_set_uint8(v___x_4156_, sizeof(void*)*1, v_hasTrace_3834_);
v___x_4157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4157_, 0, v___x_4156_);
v___x_4158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4157_);
v_exportedInfo_x3f_4144_ = v___x_4158_;
v___y_4145_ = v_a_3776_;
v___y_4146_ = v_a_3777_;
goto v___jp_4143_;
}
}
else
{
lean_dec(v___x_4151_);
v_exportedInfo_x3f_4144_ = v___x_4029_;
v___y_4145_ = v_a_3776_;
v___y_4146_ = v_a_3777_;
goto v___jp_4143_;
}
v___jp_4143_:
{
lean_object* v_toConstantVal_4147_; lean_object* v_name_4148_; lean_object* v___x_4149_; uint8_t v___x_4150_; 
v_toConstantVal_4147_ = lean_ctor_get(v_val_4142_, 0);
v_name_4148_ = lean_ctor_get(v_toConstantVal_4147_, 0);
lean_inc_ref(v_val_4142_);
v___x_4149_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4149_, 0, v_val_4142_);
v___x_4150_ = 1;
lean_inc(v_name_4148_);
v_fst_4068_ = v_name_4148_;
v_fst_4069_ = v___x_4149_;
v_snd_4070_ = v___x_4150_;
v_exportedInfo_x3f_4071_ = v_exportedInfo_x3f_4144_;
v___y_4072_ = v___y_4145_;
v___y_4073_ = v___y_4146_;
goto v___jp_4067_;
}
}
case 1:
{
lean_object* v_val_4159_; 
v_val_4159_ = lean_ctor_get(v_decl_3774_, 0);
lean_inc_ref(v_val_4159_);
v_defn_4117_ = v_val_4159_;
v___y_4118_ = v_a_3776_;
v___y_4119_ = v_a_3777_;
goto v___jp_4116_;
}
case 5:
{
lean_object* v_defns_4160_; 
v_defns_4160_ = lean_ctor_get(v_decl_3774_, 0);
if (lean_obj_tag(v_defns_4160_) == 1)
{
lean_object* v_tail_4161_; 
v_tail_4161_ = lean_ctor_get(v_defns_4160_, 1);
if (lean_obj_tag(v_tail_4161_) == 0)
{
lean_object* v_head_4162_; 
v_head_4162_ = lean_ctor_get(v_defns_4160_, 0);
lean_inc(v_head_4162_);
v_defn_4117_ = v_head_4162_;
v___y_4118_ = v_a_3776_;
v___y_4119_ = v_a_3777_;
goto v___jp_4116_;
}
else
{
lean_object* v___x_4163_; 
v___x_4163_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3774_, v_a_3776_, v_a_3777_);
return v___x_4163_;
}
}
else
{
lean_object* v___x_4164_; 
v___x_4164_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3774_, v_a_3776_, v_a_3777_);
return v___x_4164_;
}
}
case 3:
{
lean_object* v_val_4165_; lean_object* v_exportedInfo_x3f_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___x_4174_; lean_object* v_env_4175_; lean_object* v___x_4176_; 
v_val_4165_ = lean_ctor_get(v_decl_3774_, 0);
v___x_4174_ = lean_st_ref_get(v_a_3777_);
v_env_4175_ = lean_ctor_get(v___x_4174_, 0);
lean_inc_ref(v_env_4175_);
lean_dec(v___x_4174_);
v___x_4176_ = lean_st_ref_get(v_a_3777_);
if (v_forceExpose_3775_ == 0)
{
lean_object* v_env_4177_; lean_object* v___x_4178_; uint8_t v_isModule_4179_; 
v_env_4177_ = lean_ctor_get(v___x_4176_, 0);
lean_inc_ref(v_env_4177_);
lean_dec(v___x_4176_);
v___x_4178_ = l_Lean_Environment_header(v_env_4175_);
lean_dec_ref(v_env_4175_);
v_isModule_4179_ = lean_ctor_get_uint8(v___x_4178_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4178_);
if (v_isModule_4179_ == 0)
{
lean_dec_ref(v_env_4177_);
v_exportedInfo_x3f_4167_ = v___x_4029_;
v___y_4168_ = v_a_3776_;
v___y_4169_ = v_a_3777_;
goto v___jp_4166_;
}
else
{
uint8_t v_isExporting_4180_; 
v_isExporting_4180_ = lean_ctor_get_uint8(v_env_4177_, sizeof(void*)*13);
lean_dec_ref(v_env_4177_);
if (v_isExporting_4180_ == 0)
{
lean_object* v_toConstantVal_4181_; uint8_t v_isUnsafe_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; 
v_toConstantVal_4181_ = lean_ctor_get(v_val_4165_, 0);
v_isUnsafe_4182_ = lean_ctor_get_uint8(v_val_4165_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4181_);
v___x_4183_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4183_, 0, v_toConstantVal_4181_);
lean_ctor_set_uint8(v___x_4183_, sizeof(void*)*1, v_isUnsafe_4182_);
v___x_4184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4183_);
v___x_4185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4184_);
v_exportedInfo_x3f_4167_ = v___x_4185_;
v___y_4168_ = v_a_3776_;
v___y_4169_ = v_a_3777_;
goto v___jp_4166_;
}
else
{
v_exportedInfo_x3f_4167_ = v___x_4029_;
v___y_4168_ = v_a_3776_;
v___y_4169_ = v_a_3777_;
goto v___jp_4166_;
}
}
}
else
{
lean_dec(v___x_4176_);
lean_dec_ref(v_env_4175_);
v_exportedInfo_x3f_4167_ = v___x_4029_;
v___y_4168_ = v_a_3776_;
v___y_4169_ = v_a_3777_;
goto v___jp_4166_;
}
v___jp_4166_:
{
lean_object* v_toConstantVal_4170_; lean_object* v_name_4171_; lean_object* v___x_4172_; uint8_t v___x_4173_; 
v_toConstantVal_4170_ = lean_ctor_get(v_val_4165_, 0);
v_name_4171_ = lean_ctor_get(v_toConstantVal_4170_, 0);
lean_inc_ref(v_val_4165_);
v___x_4172_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4172_, 0, v_val_4165_);
v___x_4173_ = 3;
lean_inc(v_name_4171_);
v_fst_4068_ = v_name_4171_;
v_fst_4069_ = v___x_4172_;
v_snd_4070_ = v___x_4173_;
v_exportedInfo_x3f_4071_ = v_exportedInfo_x3f_4167_;
v___y_4072_ = v___y_4168_;
v___y_4073_ = v___y_4169_;
goto v___jp_4067_;
}
}
case 0:
{
lean_object* v_val_4186_; lean_object* v_toConstantVal_4187_; lean_object* v_name_4188_; lean_object* v___x_4189_; uint8_t v___x_4190_; 
v_val_4186_ = lean_ctor_get(v_decl_3774_, 0);
v_toConstantVal_4187_ = lean_ctor_get(v_val_4186_, 0);
v_name_4188_ = lean_ctor_get(v_toConstantVal_4187_, 0);
lean_inc_ref(v_val_4186_);
v___x_4189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4189_, 0, v_val_4186_);
v___x_4190_ = 2;
lean_inc(v_name_4188_);
v_fst_4068_ = v_name_4188_;
v_fst_4069_ = v___x_4189_;
v_snd_4070_ = v___x_4190_;
v_exportedInfo_x3f_4071_ = v___x_4029_;
v___y_4072_ = v_a_3776_;
v___y_4073_ = v_a_3777_;
goto v___jp_4067_;
}
default: 
{
lean_object* v___x_4191_; 
v___x_4191_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3774_, v_a_3776_, v_a_3777_);
return v___x_4191_;
}
}
v___jp_4030_:
{
lean_object* v___x_4037_; uint8_t v___x_4038_; 
lean_inc(v_decl_3774_);
v___x_4037_ = l_Lean_Declaration_getTopLevelNames(v_decl_3774_);
v___x_4038_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_4037_);
lean_dec(v___x_4037_);
if (v___x_4038_ == 0)
{
if (lean_obj_tag(v___y_4034_) == 0)
{
if (v___x_4038_ == 0)
{
lean_object* v_toCold_4039_; lean_object* v_options_4040_; uint8_t v_hasTrace_4041_; 
v_toCold_4039_ = lean_ctor_get(v___y_4035_, 0);
v_options_4040_ = lean_ctor_get(v_toCold_4039_, 2);
v_hasTrace_4041_ = lean_ctor_get_uint8(v_options_4040_, sizeof(void*)*1);
if (v_hasTrace_4041_ == 0)
{
v___y_3955_ = v___y_4031_;
v___y_3956_ = v___y_4032_;
v___y_3957_ = v___y_4033_;
v___y_3958_ = v___y_4035_;
v___y_3959_ = v___y_4036_;
goto v___jp_3954_;
}
else
{
lean_object* v_inheritedTraceOptions_4042_; lean_object* v___x_4043_; uint8_t v___x_4044_; 
v_inheritedTraceOptions_4042_ = lean_ctor_get(v_toCold_4039_, 11);
v___x_4043_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4044_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4042_, v_options_4040_, v___x_4043_);
if (v___x_4044_ == 0)
{
v___y_3955_ = v___y_4031_;
v___y_3956_ = v___y_4032_;
v___y_3957_ = v___y_4033_;
v___y_3958_ = v___y_4035_;
v___y_3959_ = v___y_4036_;
goto v___jp_3954_;
}
else
{
lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4045_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_4046_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3968_, v___x_4045_, v___y_4035_, v___y_4036_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_dec_ref_known(v___x_4046_, 1);
v___y_3955_ = v___y_4031_;
v___y_3956_ = v___y_4032_;
v___y_3957_ = v___y_4033_;
v___y_3958_ = v___y_4035_;
v___y_3959_ = v___y_4036_;
goto v___jp_3954_;
}
else
{
lean_dec_ref(v___y_4033_);
lean_dec(v___y_4032_);
lean_dec(v_decl_3774_);
return v___x_4046_;
}
}
}
}
else
{
v___y_3997_ = v___x_4038_;
v___y_3998_ = v___y_4031_;
v___y_3999_ = v___y_4032_;
v___y_4000_ = v___y_4033_;
v___y_4001_ = v___y_4035_;
v___y_4002_ = v___y_4036_;
v___y_4003_ = v___y_4034_;
goto v___jp_3996_;
}
}
else
{
v___y_3997_ = v___x_4038_;
v___y_3998_ = v___y_4031_;
v___y_3999_ = v___y_4032_;
v___y_4000_ = v___y_4033_;
v___y_4001_ = v___y_4035_;
v___y_4002_ = v___y_4036_;
v___y_4003_ = v___y_4034_;
goto v___jp_3996_;
}
}
else
{
lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v_a_4049_; uint8_t v___x_4050_; 
lean_dec(v___y_4034_);
v___x_4047_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4048_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4047_, v___y_4035_);
v_a_4049_ = lean_ctor_get(v___x_4048_, 0);
lean_inc(v_a_4049_);
lean_dec_ref(v___x_4048_);
v___x_4050_ = lean_unbox(v_a_4049_);
lean_dec(v_a_4049_);
if (v___x_4050_ == 0)
{
lean_object* v_toCold_4051_; lean_object* v_options_4052_; uint8_t v_hasTrace_4053_; 
v_toCold_4051_ = lean_ctor_get(v___y_4035_, 0);
v_options_4052_ = lean_ctor_get(v_toCold_4051_, 2);
v_hasTrace_4053_ = lean_ctor_get_uint8(v_options_4052_, sizeof(void*)*1);
if (v_hasTrace_4053_ == 0)
{
v___y_3940_ = v___y_4031_;
v___y_3941_ = v___y_4032_;
v___y_3942_ = v___y_4033_;
v_exportedInfo_x3f_3943_ = v___x_4029_;
v___y_3944_ = v___y_4035_;
v___y_3945_ = v___y_4036_;
goto v___jp_3939_;
}
else
{
lean_object* v_inheritedTraceOptions_4054_; lean_object* v___x_4055_; uint8_t v___x_4056_; 
v_inheritedTraceOptions_4054_ = lean_ctor_get(v_toCold_4051_, 11);
v___x_4055_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4056_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4054_, v_options_4052_, v___x_4055_);
if (v___x_4056_ == 0)
{
v___y_3940_ = v___y_4031_;
v___y_3941_ = v___y_4032_;
v___y_3942_ = v___y_4033_;
v_exportedInfo_x3f_3943_ = v___x_4029_;
v___y_3944_ = v___y_4035_;
v___y_3945_ = v___y_4036_;
goto v___jp_3939_;
}
else
{
lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4057_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_4058_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3968_, v___x_4057_, v___y_4035_, v___y_4036_);
if (lean_obj_tag(v___x_4058_) == 0)
{
lean_dec_ref_known(v___x_4058_, 1);
v___y_3940_ = v___y_4031_;
v___y_3941_ = v___y_4032_;
v___y_3942_ = v___y_4033_;
v_exportedInfo_x3f_3943_ = v___x_4029_;
v___y_3944_ = v___y_4035_;
v___y_3945_ = v___y_4036_;
goto v___jp_3939_;
}
else
{
lean_dec_ref(v___y_4033_);
lean_dec(v___y_4032_);
lean_dec(v_decl_3774_);
return v___x_4058_;
}
}
}
}
else
{
lean_object* v_toCold_4059_; lean_object* v_options_4060_; uint8_t v_hasTrace_4061_; 
v_toCold_4059_ = lean_ctor_get(v___y_4035_, 0);
v_options_4060_ = lean_ctor_get(v_toCold_4059_, 2);
v_hasTrace_4061_ = lean_ctor_get_uint8(v_options_4060_, sizeof(void*)*1);
if (v_hasTrace_4061_ == 0)
{
v___y_3962_ = v___y_4031_;
v___y_3963_ = v___y_4032_;
v___y_3964_ = v___y_4033_;
v___y_3965_ = v___y_4035_;
v___y_3966_ = v___y_4036_;
goto v___jp_3961_;
}
else
{
lean_object* v_inheritedTraceOptions_4062_; lean_object* v___x_4063_; uint8_t v___x_4064_; 
v_inheritedTraceOptions_4062_ = lean_ctor_get(v_toCold_4059_, 11);
v___x_4063_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4064_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4062_, v_options_4060_, v___x_4063_);
if (v___x_4064_ == 0)
{
v___y_3962_ = v___y_4031_;
v___y_3963_ = v___y_4032_;
v___y_3964_ = v___y_4033_;
v___y_3965_ = v___y_4035_;
v___y_3966_ = v___y_4036_;
goto v___jp_3961_;
}
else
{
lean_object* v___x_4065_; lean_object* v___x_4066_; 
v___x_4065_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_4066_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3968_, v___x_4065_, v___y_4035_, v___y_4036_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_dec_ref_known(v___x_4066_, 1);
v___y_3962_ = v___y_4031_;
v___y_3963_ = v___y_4032_;
v___y_3964_ = v___y_4033_;
v___y_3965_ = v___y_4035_;
v___y_3966_ = v___y_4036_;
goto v___jp_3961_;
}
else
{
lean_dec_ref(v___y_4033_);
lean_dec(v___y_4032_);
lean_dec(v_decl_3774_);
return v___x_4066_;
}
}
}
}
}
}
v___jp_4067_:
{
lean_object* v___x_4074_; lean_object* v_env_4075_; uint8_t v___x_4076_; 
v___x_4074_ = lean_st_ref_get(v___y_4073_);
v_env_4075_ = lean_ctor_get(v___x_4074_, 0);
lean_inc_ref(v_env_4075_);
lean_dec(v___x_4074_);
v___x_4076_ = l_Lean_Environment_containsOnBranch(v_env_4075_, v_fst_4068_);
lean_dec_ref(v_env_4075_);
if (v___x_4076_ == 0)
{
v___y_4031_ = v_snd_4070_;
v___y_4032_ = v_fst_4068_;
v___y_4033_ = v_fst_4069_;
v___y_4034_ = v_exportedInfo_x3f_4071_;
v___y_4035_ = v___y_4072_;
v___y_4036_ = v___y_4073_;
goto v___jp_4030_;
}
else
{
lean_object* v___x_4077_; lean_object* v_env_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
lean_dec(v_exportedInfo_x3f_4071_);
lean_dec_ref(v_fst_4069_);
lean_dec(v_decl_3774_);
v___x_4077_ = lean_st_ref_get(v___y_4073_);
v_env_4078_ = lean_ctor_get(v___x_4077_, 0);
lean_inc_ref(v_env_4078_);
lean_dec(v___x_4077_);
v___x_4079_ = lean_elab_environment_to_kernel_env(v_env_4078_);
v___x_4080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4079_);
lean_ctor_set(v___x_4080_, 1, v_fst_4068_);
v___x_4081_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4080_, v___y_4072_, v___y_4073_);
return v___x_4081_;
}
}
v___jp_4082_:
{
lean_object* v_toConstantVal_4087_; lean_object* v_name_4088_; lean_object* v___x_4089_; uint8_t v___x_4090_; 
v_toConstantVal_4087_ = lean_ctor_get(v___y_4083_, 0);
v_name_4088_ = lean_ctor_get(v_toConstantVal_4087_, 0);
lean_inc(v_name_4088_);
v___x_4089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4089_, 0, v___y_4083_);
v___x_4090_ = 0;
v_fst_4068_ = v_name_4088_;
v_fst_4069_ = v___x_4089_;
v_snd_4070_ = v___x_4090_;
v_exportedInfo_x3f_4071_ = v_exportedInfo_x3f_4084_;
v___y_4072_ = v___y_4085_;
v___y_4073_ = v___y_4086_;
goto v___jp_4067_;
}
v___jp_4091_:
{
lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___x_4097_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4097_, 0, v___y_4092_);
lean_ctor_set_uint8(v___x_4097_, sizeof(void*)*1, v___y_4096_);
v___x_4098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4097_);
v___x_4099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4099_, 0, v___x_4098_);
v___y_4083_ = v___y_4094_;
v_exportedInfo_x3f_4084_ = v___x_4099_;
v___y_4085_ = v___y_4093_;
v___y_4086_ = v___y_4095_;
goto v___jp_4082_;
}
v___jp_4100_:
{
uint8_t v___x_4107_; uint8_t v___x_4108_; 
v___x_4107_ = 1;
v___x_4108_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4103_, v___x_4107_);
if (v___x_4108_ == 0)
{
v___y_4092_ = v_toConstantVal_4102_;
v___y_4093_ = v___y_4105_;
v___y_4094_ = v___y_4101_;
v___y_4095_ = v___y_4106_;
v___y_4096_ = v___y_4104_;
goto v___jp_4091_;
}
else
{
v___y_4092_ = v_toConstantVal_4102_;
v___y_4093_ = v___y_4105_;
v___y_4094_ = v___y_4101_;
v___y_4095_ = v___y_4106_;
v___y_4096_ = v_hasTrace_3834_;
goto v___jp_4091_;
}
}
v___jp_4109_:
{
lean_object* v_toConstantVal_4114_; uint8_t v_safety_4115_; 
v_toConstantVal_4114_ = lean_ctor_get(v___y_4110_, 0);
lean_inc_ref(v_toConstantVal_4114_);
v_safety_4115_ = lean_ctor_get_uint8(v___y_4110_, sizeof(void*)*4);
v___y_4101_ = v___y_4110_;
v_toConstantVal_4102_ = v_toConstantVal_4114_;
v_safety_4103_ = v_safety_4115_;
v___y_4104_ = v___y_4111_;
v___y_4105_ = v___y_4112_;
v___y_4106_ = v___y_4113_;
goto v___jp_4100_;
}
v___jp_4116_:
{
lean_object* v___x_4120_; lean_object* v_env_4121_; lean_object* v___x_4122_; 
v___x_4120_ = lean_st_ref_get(v___y_4119_);
v_env_4121_ = lean_ctor_get(v___x_4120_, 0);
lean_inc_ref(v_env_4121_);
lean_dec(v___x_4120_);
v___x_4122_ = lean_st_ref_get(v___y_4119_);
if (v_forceExpose_3775_ == 0)
{
lean_object* v_env_4123_; lean_object* v___x_4124_; uint8_t v_isModule_4125_; 
v_env_4123_ = lean_ctor_get(v___x_4122_, 0);
lean_inc_ref(v_env_4123_);
lean_dec(v___x_4122_);
v___x_4124_ = l_Lean_Environment_header(v_env_4121_);
lean_dec_ref(v_env_4121_);
v_isModule_4125_ = lean_ctor_get_uint8(v___x_4124_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4124_);
if (v_isModule_4125_ == 0)
{
lean_dec_ref(v_env_4123_);
v___y_4083_ = v_defn_4117_;
v_exportedInfo_x3f_4084_ = v___x_4029_;
v___y_4085_ = v___y_4118_;
v___y_4086_ = v___y_4119_;
goto v___jp_4082_;
}
else
{
uint8_t v_isExporting_4126_; 
v_isExporting_4126_ = lean_ctor_get_uint8(v_env_4123_, sizeof(void*)*13);
lean_dec_ref(v_env_4123_);
if (v_isExporting_4126_ == 0)
{
lean_object* v_toCold_4127_; lean_object* v_options_4128_; uint8_t v_hasTrace_4129_; 
v_toCold_4127_ = lean_ctor_get(v___y_4118_, 0);
v_options_4128_ = lean_ctor_get(v_toCold_4127_, 2);
v_hasTrace_4129_ = lean_ctor_get_uint8(v_options_4128_, sizeof(void*)*1);
if (v_hasTrace_4129_ == 0)
{
v___y_4110_ = v_defn_4117_;
v___y_4111_ = v_isModule_4125_;
v___y_4112_ = v___y_4118_;
v___y_4113_ = v___y_4119_;
goto v___jp_4109_;
}
else
{
lean_object* v_inheritedTraceOptions_4130_; lean_object* v___x_4131_; uint8_t v___x_4132_; 
v_inheritedTraceOptions_4130_ = lean_ctor_get(v_toCold_4127_, 11);
v___x_4131_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4132_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4130_, v_options_4128_, v___x_4131_);
if (v___x_4132_ == 0)
{
v___y_4110_ = v_defn_4117_;
v___y_4111_ = v_isModule_4125_;
v___y_4112_ = v___y_4118_;
v___y_4113_ = v___y_4119_;
goto v___jp_4109_;
}
else
{
lean_object* v_toConstantVal_4133_; uint8_t v_safety_4134_; lean_object* v_name_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; 
v_toConstantVal_4133_ = lean_ctor_get(v_defn_4117_, 0);
lean_inc_ref(v_toConstantVal_4133_);
v_safety_4134_ = lean_ctor_get_uint8(v_defn_4117_, sizeof(void*)*4);
v_name_4135_ = lean_ctor_get(v_toConstantVal_4133_, 0);
v___x_4136_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_4135_);
v___x_4137_ = l_Lean_MessageData_ofName(v_name_4135_);
v___x_4138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4136_);
lean_ctor_set(v___x_4138_, 1, v___x_4137_);
v___x_4139_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4140_, 0, v___x_4138_);
lean_ctor_set(v___x_4140_, 1, v___x_4139_);
v___x_4141_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3968_, v___x_4140_, v___y_4118_, v___y_4119_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_dec_ref_known(v___x_4141_, 1);
v___y_4101_ = v_defn_4117_;
v_toConstantVal_4102_ = v_toConstantVal_4133_;
v_safety_4103_ = v_safety_4134_;
v___y_4104_ = v_isModule_4125_;
v___y_4105_ = v___y_4118_;
v___y_4106_ = v___y_4119_;
goto v___jp_4100_;
}
else
{
lean_dec_ref(v_toConstantVal_4133_);
lean_dec_ref(v_defn_4117_);
lean_dec(v_decl_3774_);
return v___x_4141_;
}
}
}
}
else
{
v___y_4083_ = v_defn_4117_;
v_exportedInfo_x3f_4084_ = v___x_4029_;
v___y_4085_ = v___y_4118_;
v___y_4086_ = v___y_4119_;
goto v___jp_4082_;
}
}
}
else
{
lean_dec(v___x_4122_);
lean_dec_ref(v_env_4121_);
v___y_4083_ = v_defn_4117_;
v_exportedInfo_x3f_4084_ = v___x_4029_;
v___y_4085_ = v___y_4118_;
v___y_4086_ = v___y_4119_;
goto v___jp_4082_;
}
}
}
}
}
else
{
lean_object* v___f_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; uint8_t v___x_4198_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v_a_4202_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; uint8_t v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v_a_4303_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4333_; lean_object* v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4340_; lean_object* v___y_4341_; lean_object* v___y_4342_; lean_object* v___y_4343_; 
lean_inc(v_decl_3774_);
v___f_4195_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed), 5, 1);
lean_closure_set(v___f_4195_, 0, v_decl_3774_);
v___x_4196_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_4197_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4198_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3833_, v_options_3832_, v___x_4197_);
if (v___x_4198_ == 0)
{
lean_object* v___x_4502_; uint8_t v___x_4503_; lean_object* v___y_4505_; lean_object* v___y_4506_; lean_object* v___y_4507_; lean_object* v___y_4508_; lean_object* v___y_4509_; lean_object* v___y_4510_; lean_object* v___y_4511_; lean_object* v___y_4512_; lean_object* v___y_4513_; lean_object* v___y_4514_; lean_object* v___y_4515_; lean_object* v___y_4578_; lean_object* v___y_4579_; lean_object* v___y_4580_; lean_object* v___y_4581_; lean_object* v___y_4582_; uint8_t v___y_4583_; lean_object* v___y_4584_; lean_object* v___y_4585_; uint8_t v___y_4607_; lean_object* v___y_4608_; lean_object* v___y_4609_; lean_object* v_exportedInfo_x3f_4610_; lean_object* v___y_4611_; lean_object* v___y_4612_; uint8_t v___y_4622_; lean_object* v___y_4623_; lean_object* v___y_4624_; lean_object* v___y_4625_; lean_object* v___y_4626_; uint8_t v___y_4629_; lean_object* v___y_4630_; lean_object* v___y_4631_; lean_object* v___y_4632_; lean_object* v___y_4633_; 
v___x_4502_ = l_Lean_trace_profiler;
v___x_4503_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3832_, v___x_4502_);
if (v___x_4503_ == 0)
{
lean_object* v___x_4635_; lean_object* v_env_4636_; lean_object* v_nextMacroScope_4637_; lean_object* v_ngen_4638_; lean_object* v_auxDeclNGen_4639_; lean_object* v_traceState_4640_; lean_object* v_recordedDeps_4641_; lean_object* v_messages_4642_; lean_object* v_infoState_4643_; lean_object* v_snapshotTasks_4644_; lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4878_; 
lean_dec_ref(v___f_4195_);
v___x_4635_ = lean_st_ref_take(v_a_3777_);
v_env_4636_ = lean_ctor_get(v___x_4635_, 0);
v_nextMacroScope_4637_ = lean_ctor_get(v___x_4635_, 1);
v_ngen_4638_ = lean_ctor_get(v___x_4635_, 2);
v_auxDeclNGen_4639_ = lean_ctor_get(v___x_4635_, 3);
v_traceState_4640_ = lean_ctor_get(v___x_4635_, 4);
v_recordedDeps_4641_ = lean_ctor_get(v___x_4635_, 6);
v_messages_4642_ = lean_ctor_get(v___x_4635_, 7);
v_infoState_4643_ = lean_ctor_get(v___x_4635_, 8);
v_snapshotTasks_4644_ = lean_ctor_get(v___x_4635_, 9);
v_isSharedCheck_4878_ = !lean_is_exclusive(v___x_4635_);
if (v_isSharedCheck_4878_ == 0)
{
lean_object* v_unused_4879_; 
v_unused_4879_ = lean_ctor_get(v___x_4635_, 5);
lean_dec(v_unused_4879_);
v___x_4646_ = v___x_4635_;
v_isShared_4647_ = v_isSharedCheck_4878_;
goto v_resetjp_4645_;
}
else
{
lean_inc(v_snapshotTasks_4644_);
lean_inc(v_infoState_4643_);
lean_inc(v_messages_4642_);
lean_inc(v_recordedDeps_4641_);
lean_inc(v_traceState_4640_);
lean_inc(v_auxDeclNGen_4639_);
lean_inc(v_ngen_4638_);
lean_inc(v_nextMacroScope_4637_);
lean_inc(v_env_4636_);
lean_dec(v___x_4635_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4878_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___y_4652_; lean_object* v___y_4653_; uint8_t v___y_4654_; uint8_t v___y_4655_; lean_object* v___y_4656_; lean_object* v___y_4657_; lean_object* v___y_4658_; lean_object* v___x_4682_; 
lean_inc(v_decl_3774_);
v___x_4648_ = l_Lean_Declaration_getNames(v_decl_3774_);
v___x_4649_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4636_, v___x_4648_);
v___x_4650_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4647_ == 0)
{
lean_ctor_set(v___x_4646_, 5, v___x_4650_);
lean_ctor_set(v___x_4646_, 0, v___x_4649_);
v___x_4682_ = v___x_4646_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4877_; 
v_reuseFailAlloc_4877_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4877_, 0, v___x_4649_);
lean_ctor_set(v_reuseFailAlloc_4877_, 1, v_nextMacroScope_4637_);
lean_ctor_set(v_reuseFailAlloc_4877_, 2, v_ngen_4638_);
lean_ctor_set(v_reuseFailAlloc_4877_, 3, v_auxDeclNGen_4639_);
lean_ctor_set(v_reuseFailAlloc_4877_, 4, v_traceState_4640_);
lean_ctor_set(v_reuseFailAlloc_4877_, 5, v___x_4650_);
lean_ctor_set(v_reuseFailAlloc_4877_, 6, v_recordedDeps_4641_);
lean_ctor_set(v_reuseFailAlloc_4877_, 7, v_messages_4642_);
lean_ctor_set(v_reuseFailAlloc_4877_, 8, v_infoState_4643_);
lean_ctor_set(v_reuseFailAlloc_4877_, 9, v_snapshotTasks_4644_);
v___x_4682_ = v_reuseFailAlloc_4877_;
goto v_reusejp_4681_;
}
v___jp_4651_:
{
lean_object* v___x_4659_; lean_object* v_env_4660_; lean_object* v_nextMacroScope_4661_; lean_object* v_ngen_4662_; lean_object* v_auxDeclNGen_4663_; lean_object* v_traceState_4664_; lean_object* v_recordedDeps_4665_; lean_object* v_messages_4666_; lean_object* v_infoState_4667_; lean_object* v_snapshotTasks_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4679_; 
v___x_4659_ = lean_st_ref_take(v___y_4652_);
v_env_4660_ = lean_ctor_get(v___x_4659_, 0);
v_nextMacroScope_4661_ = lean_ctor_get(v___x_4659_, 1);
v_ngen_4662_ = lean_ctor_get(v___x_4659_, 2);
v_auxDeclNGen_4663_ = lean_ctor_get(v___x_4659_, 3);
v_traceState_4664_ = lean_ctor_get(v___x_4659_, 4);
v_recordedDeps_4665_ = lean_ctor_get(v___x_4659_, 6);
v_messages_4666_ = lean_ctor_get(v___x_4659_, 7);
v_infoState_4667_ = lean_ctor_get(v___x_4659_, 8);
v_snapshotTasks_4668_ = lean_ctor_get(v___x_4659_, 9);
v_isSharedCheck_4679_ = !lean_is_exclusive(v___x_4659_);
if (v_isSharedCheck_4679_ == 0)
{
lean_object* v_unused_4680_; 
v_unused_4680_ = lean_ctor_get(v___x_4659_, 5);
lean_dec(v_unused_4680_);
v___x_4670_ = v___x_4659_;
v_isShared_4671_ = v_isSharedCheck_4679_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_snapshotTasks_4668_);
lean_inc(v_infoState_4667_);
lean_inc(v_messages_4666_);
lean_inc(v_recordedDeps_4665_);
lean_inc(v_traceState_4664_);
lean_inc(v_auxDeclNGen_4663_);
lean_inc(v_ngen_4662_);
lean_inc(v_nextMacroScope_4661_);
lean_inc(v_env_4660_);
lean_dec(v___x_4659_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4679_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4676_; 
v___x_4672_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4673_ = lean_box(v___y_4655_);
lean_inc(v___y_4657_);
v___x_4674_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4672_, v_env_4660_, v___y_4657_, v___x_4673_, v___y_4654_);
if (v_isShared_4671_ == 0)
{
lean_ctor_set(v___x_4670_, 5, v___x_4650_);
lean_ctor_set(v___x_4670_, 0, v___x_4674_);
v___x_4676_ = v___x_4670_;
goto v_reusejp_4675_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v___x_4674_);
lean_ctor_set(v_reuseFailAlloc_4678_, 1, v_nextMacroScope_4661_);
lean_ctor_set(v_reuseFailAlloc_4678_, 2, v_ngen_4662_);
lean_ctor_set(v_reuseFailAlloc_4678_, 3, v_auxDeclNGen_4663_);
lean_ctor_set(v_reuseFailAlloc_4678_, 4, v_traceState_4664_);
lean_ctor_set(v_reuseFailAlloc_4678_, 5, v___x_4650_);
lean_ctor_set(v_reuseFailAlloc_4678_, 6, v_recordedDeps_4665_);
lean_ctor_set(v_reuseFailAlloc_4678_, 7, v_messages_4666_);
lean_ctor_set(v_reuseFailAlloc_4678_, 8, v_infoState_4667_);
lean_ctor_set(v_reuseFailAlloc_4678_, 9, v_snapshotTasks_4668_);
v___x_4676_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4675_;
}
v_reusejp_4675_:
{
lean_object* v___x_4677_; 
v___x_4677_ = lean_st_ref_put(v___y_4652_, v___x_4676_);
v___y_4607_ = v___y_4655_;
v___y_4608_ = v___y_4656_;
v___y_4609_ = v___y_4657_;
v_exportedInfo_x3f_4610_ = v___y_4653_;
v___y_4611_ = v___y_4658_;
v___y_4612_ = v___y_4652_;
goto v___jp_4606_;
}
}
}
v_reusejp_4681_:
{
lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___y_4686_; uint8_t v___y_4687_; lean_object* v___y_4688_; lean_object* v___y_4689_; lean_object* v___y_4690_; lean_object* v___y_4691_; lean_object* v_fst_4720_; lean_object* v_fst_4721_; uint8_t v_snd_4722_; lean_object* v_exportedInfo_x3f_4723_; lean_object* v___y_4724_; lean_object* v___y_4725_; lean_object* v___y_4735_; lean_object* v_exportedInfo_x3f_4736_; lean_object* v___y_4737_; lean_object* v___y_4738_; lean_object* v___y_4744_; lean_object* v___y_4745_; lean_object* v___y_4746_; lean_object* v___y_4747_; uint8_t v___y_4748_; uint8_t v___y_4753_; lean_object* v___y_4754_; lean_object* v_toConstantVal_4755_; uint8_t v_safety_4756_; lean_object* v___y_4757_; lean_object* v___y_4758_; uint8_t v___y_4762_; lean_object* v___y_4763_; lean_object* v___y_4764_; lean_object* v___y_4765_; lean_object* v___y_4769_; lean_object* v___y_4770_; lean_object* v___y_4771_; uint8_t v___y_4772_; lean_object* v___y_4788_; lean_object* v___y_4789_; lean_object* v___y_4790_; lean_object* v___y_4791_; lean_object* v___y_4792_; lean_object* v_defn_4797_; lean_object* v___y_4798_; lean_object* v___y_4799_; 
v___x_4683_ = lean_st_ref_put(v_a_3777_, v___x_4682_);
v___x_4684_ = lean_box(0);
switch(lean_obj_tag(v_decl_3774_))
{
case 2:
{
lean_object* v_val_4805_; lean_object* v_exportedInfo_x3f_4807_; lean_object* v___y_4808_; lean_object* v___y_4809_; lean_object* v___y_4815_; lean_object* v___y_4816_; lean_object* v___x_4821_; lean_object* v_env_4822_; 
v_val_4805_ = lean_ctor_get(v_decl_3774_, 0);
v___x_4821_ = lean_st_ref_get(v_a_3777_);
v_env_4822_ = lean_ctor_get(v___x_4821_, 0);
lean_inc_ref(v_env_4822_);
lean_dec(v___x_4821_);
if (v_forceExpose_3775_ == 0)
{
goto v___jp_4823_;
}
else
{
if (v___x_4503_ == 0)
{
lean_dec_ref(v_env_4822_);
v_exportedInfo_x3f_4807_ = v___x_4684_;
v___y_4808_ = v_a_3776_;
v___y_4809_ = v_a_3777_;
goto v___jp_4806_;
}
else
{
goto v___jp_4823_;
}
}
v___jp_4806_:
{
lean_object* v_toConstantVal_4810_; lean_object* v_name_4811_; lean_object* v___x_4812_; uint8_t v___x_4813_; 
v_toConstantVal_4810_ = lean_ctor_get(v_val_4805_, 0);
v_name_4811_ = lean_ctor_get(v_toConstantVal_4810_, 0);
lean_inc_ref(v_val_4805_);
v___x_4812_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4812_, 0, v_val_4805_);
v___x_4813_ = 1;
lean_inc(v_name_4811_);
v_fst_4720_ = v_name_4811_;
v_fst_4721_ = v___x_4812_;
v_snd_4722_ = v___x_4813_;
v_exportedInfo_x3f_4723_ = v_exportedInfo_x3f_4807_;
v___y_4724_ = v___y_4808_;
v___y_4725_ = v___y_4809_;
goto v___jp_4719_;
}
v___jp_4814_:
{
lean_object* v_toConstantVal_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; 
v_toConstantVal_4817_ = lean_ctor_get(v_val_4805_, 0);
lean_inc_ref(v_toConstantVal_4817_);
v___x_4818_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4818_, 0, v_toConstantVal_4817_);
lean_ctor_set_uint8(v___x_4818_, sizeof(void*)*1, v___x_4503_);
v___x_4819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4819_, 0, v___x_4818_);
v___x_4820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4820_, 0, v___x_4819_);
v_exportedInfo_x3f_4807_ = v___x_4820_;
v___y_4808_ = v___y_4815_;
v___y_4809_ = v___y_4816_;
goto v___jp_4806_;
}
v___jp_4823_:
{
lean_object* v___x_4824_; uint8_t v_isModule_4825_; 
v___x_4824_ = l_Lean_Environment_header(v_env_4822_);
lean_dec_ref(v_env_4822_);
v_isModule_4825_ = lean_ctor_get_uint8(v___x_4824_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4824_);
if (v_isModule_4825_ == 0)
{
v_exportedInfo_x3f_4807_ = v___x_4684_;
v___y_4808_ = v_a_3776_;
v___y_4809_ = v_a_3777_;
goto v___jp_4806_;
}
else
{
if (v___x_4198_ == 0)
{
v___y_4815_ = v_a_3776_;
v___y_4816_ = v_a_3777_;
goto v___jp_4814_;
}
else
{
lean_object* v_toConstantVal_4826_; lean_object* v_name_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; 
v_toConstantVal_4826_ = lean_ctor_get(v_val_4805_, 0);
v_name_4827_ = lean_ctor_get(v_toConstantVal_4826_, 0);
v___x_4828_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4827_);
v___x_4829_ = l_Lean_MessageData_ofName(v_name_4827_);
v___x_4830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4830_, 0, v___x_4828_);
lean_ctor_set(v___x_4830_, 1, v___x_4829_);
v___x_4831_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4832_, 0, v___x_4830_);
lean_ctor_set(v___x_4832_, 1, v___x_4831_);
v___x_4833_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3968_, v___x_4832_, v_a_3776_, v_a_3777_);
if (lean_obj_tag(v___x_4833_) == 0)
{
lean_dec_ref_known(v___x_4833_, 1);
v___y_4815_ = v_a_3776_;
v___y_4816_ = v_a_3777_;
goto v___jp_4814_;
}
else
{
lean_dec_ref_known(v_decl_3774_, 1);
return v___x_4833_;
}
}
}
}
}
case 1:
{
lean_object* v_val_4834_; 
v_val_4834_ = lean_ctor_get(v_decl_3774_, 0);
lean_inc_ref(v_val_4834_);
v_defn_4797_ = v_val_4834_;
v___y_4798_ = v_a_3776_;
v___y_4799_ = v_a_3777_;
goto v___jp_4796_;
}
case 5:
{
lean_object* v_defns_4835_; 
v_defns_4835_ = lean_ctor_get(v_decl_3774_, 0);
if (lean_obj_tag(v_defns_4835_) == 1)
{
lean_object* v_tail_4836_; 
v_tail_4836_ = lean_ctor_get(v_defns_4835_, 1);
if (lean_obj_tag(v_tail_4836_) == 0)
{
lean_object* v_head_4837_; 
v_head_4837_ = lean_ctor_get(v_defns_4835_, 0);
lean_inc(v_head_4837_);
v_defn_4797_ = v_head_4837_;
v___y_4798_ = v_a_3776_;
v___y_4799_ = v_a_3777_;
goto v___jp_4796_;
}
else
{
v___y_3970_ = v_a_3776_;
v_options_3971_ = v_options_3832_;
v_inheritedTraceOptions_3972_ = v_inheritedTraceOptions_3833_;
v___y_3973_ = v_a_3777_;
goto v___jp_3969_;
}
}
else
{
v___y_3970_ = v_a_3776_;
v_options_3971_ = v_options_3832_;
v_inheritedTraceOptions_3972_ = v_inheritedTraceOptions_3833_;
v___y_3973_ = v_a_3777_;
goto v___jp_3969_;
}
}
case 3:
{
lean_object* v_val_4838_; lean_object* v_exportedInfo_x3f_4840_; lean_object* v___y_4841_; lean_object* v___y_4842_; lean_object* v___y_4848_; lean_object* v___y_4849_; lean_object* v___x_4855_; lean_object* v_env_4856_; lean_object* v___x_4857_; lean_object* v_env_4867_; 
v_val_4838_ = lean_ctor_get(v_decl_3774_, 0);
v___x_4855_ = lean_st_ref_get(v_a_3777_);
v_env_4856_ = lean_ctor_get(v___x_4855_, 0);
lean_inc_ref(v_env_4856_);
lean_dec(v___x_4855_);
v___x_4857_ = lean_st_ref_get(v_a_3777_);
v_env_4867_ = lean_ctor_get(v___x_4857_, 0);
lean_inc_ref(v_env_4867_);
lean_dec(v___x_4857_);
if (v_forceExpose_3775_ == 0)
{
goto v___jp_4868_;
}
else
{
if (v___x_4503_ == 0)
{
lean_dec_ref(v_env_4867_);
lean_dec_ref(v_env_4856_);
v_exportedInfo_x3f_4840_ = v___x_4684_;
v___y_4841_ = v_a_3776_;
v___y_4842_ = v_a_3777_;
goto v___jp_4839_;
}
else
{
goto v___jp_4868_;
}
}
v___jp_4839_:
{
lean_object* v_toConstantVal_4843_; lean_object* v_name_4844_; lean_object* v___x_4845_; uint8_t v___x_4846_; 
v_toConstantVal_4843_ = lean_ctor_get(v_val_4838_, 0);
v_name_4844_ = lean_ctor_get(v_toConstantVal_4843_, 0);
lean_inc_ref(v_val_4838_);
v___x_4845_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4845_, 0, v_val_4838_);
v___x_4846_ = 3;
lean_inc(v_name_4844_);
v_fst_4720_ = v_name_4844_;
v_fst_4721_ = v___x_4845_;
v_snd_4722_ = v___x_4846_;
v_exportedInfo_x3f_4723_ = v_exportedInfo_x3f_4840_;
v___y_4724_ = v___y_4841_;
v___y_4725_ = v___y_4842_;
goto v___jp_4719_;
}
v___jp_4847_:
{
lean_object* v_toConstantVal_4850_; uint8_t v_isUnsafe_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; 
v_toConstantVal_4850_ = lean_ctor_get(v_val_4838_, 0);
v_isUnsafe_4851_ = lean_ctor_get_uint8(v_val_4838_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4850_);
v___x_4852_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4852_, 0, v_toConstantVal_4850_);
lean_ctor_set_uint8(v___x_4852_, sizeof(void*)*1, v_isUnsafe_4851_);
v___x_4853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4853_, 0, v___x_4852_);
v___x_4854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4854_, 0, v___x_4853_);
v_exportedInfo_x3f_4840_ = v___x_4854_;
v___y_4841_ = v___y_4848_;
v___y_4842_ = v___y_4849_;
goto v___jp_4839_;
}
v___jp_4858_:
{
if (v___x_4198_ == 0)
{
v___y_4848_ = v_a_3776_;
v___y_4849_ = v_a_3777_;
goto v___jp_4847_;
}
else
{
lean_object* v_toConstantVal_4859_; lean_object* v_name_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; 
v_toConstantVal_4859_ = lean_ctor_get(v_val_4838_, 0);
v_name_4860_ = lean_ctor_get(v_toConstantVal_4859_, 0);
v___x_4861_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4860_);
v___x_4862_ = l_Lean_MessageData_ofName(v_name_4860_);
v___x_4863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4863_, 0, v___x_4861_);
lean_ctor_set(v___x_4863_, 1, v___x_4862_);
v___x_4864_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4865_, 0, v___x_4863_);
lean_ctor_set(v___x_4865_, 1, v___x_4864_);
v___x_4866_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3968_, v___x_4865_, v_a_3776_, v_a_3777_);
if (lean_obj_tag(v___x_4866_) == 0)
{
lean_dec_ref_known(v___x_4866_, 1);
v___y_4848_ = v_a_3776_;
v___y_4849_ = v_a_3777_;
goto v___jp_4847_;
}
else
{
lean_dec_ref_known(v_decl_3774_, 1);
return v___x_4866_;
}
}
}
v___jp_4868_:
{
lean_object* v___x_4869_; uint8_t v_isModule_4870_; 
v___x_4869_ = l_Lean_Environment_header(v_env_4856_);
lean_dec_ref(v_env_4856_);
v_isModule_4870_ = lean_ctor_get_uint8(v___x_4869_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4869_);
if (v_isModule_4870_ == 0)
{
lean_dec_ref(v_env_4867_);
v_exportedInfo_x3f_4840_ = v___x_4684_;
v___y_4841_ = v_a_3776_;
v___y_4842_ = v_a_3777_;
goto v___jp_4839_;
}
else
{
uint8_t v_isExporting_4871_; 
v_isExporting_4871_ = lean_ctor_get_uint8(v_env_4867_, sizeof(void*)*13);
lean_dec_ref(v_env_4867_);
if (v_isExporting_4871_ == 0)
{
goto v___jp_4858_;
}
else
{
if (v___x_4503_ == 0)
{
v_exportedInfo_x3f_4840_ = v___x_4684_;
v___y_4841_ = v_a_3776_;
v___y_4842_ = v_a_3777_;
goto v___jp_4839_;
}
else
{
goto v___jp_4858_;
}
}
}
}
}
case 0:
{
lean_object* v_val_4872_; lean_object* v_toConstantVal_4873_; lean_object* v_name_4874_; lean_object* v___x_4875_; uint8_t v___x_4876_; 
v_val_4872_ = lean_ctor_get(v_decl_3774_, 0);
v_toConstantVal_4873_ = lean_ctor_get(v_val_4872_, 0);
v_name_4874_ = lean_ctor_get(v_toConstantVal_4873_, 0);
lean_inc_ref(v_val_4872_);
v___x_4875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4875_, 0, v_val_4872_);
v___x_4876_ = 2;
lean_inc(v_name_4874_);
v_fst_4720_ = v_name_4874_;
v_fst_4721_ = v___x_4875_;
v_snd_4722_ = v___x_4876_;
v_exportedInfo_x3f_4723_ = v___x_4684_;
v___y_4724_ = v_a_3776_;
v___y_4725_ = v_a_3777_;
goto v___jp_4719_;
}
default: 
{
v___y_3970_ = v_a_3776_;
v_options_3971_ = v_options_3832_;
v_inheritedTraceOptions_3972_ = v_inheritedTraceOptions_3833_;
v___y_3973_ = v_a_3777_;
goto v___jp_3969_;
}
}
v___jp_4685_:
{
lean_object* v___x_4692_; uint8_t v___x_4693_; 
lean_inc(v_decl_3774_);
v___x_4692_ = l_Lean_Declaration_getTopLevelNames(v_decl_3774_);
v___x_4693_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_4692_);
lean_dec(v___x_4692_);
if (v___x_4693_ == 0)
{
if (lean_obj_tag(v___y_4686_) == 0)
{
if (v___x_4693_ == 0)
{
lean_object* v_toCold_4694_; lean_object* v_options_4695_; uint8_t v_hasTrace_4696_; 
v_toCold_4694_ = lean_ctor_get(v___y_4690_, 0);
v_options_4695_ = lean_ctor_get(v_toCold_4694_, 2);
v_hasTrace_4696_ = lean_ctor_get_uint8(v_options_4695_, sizeof(void*)*1);
if (v_hasTrace_4696_ == 0)
{
v___y_4622_ = v___y_4687_;
v___y_4623_ = v___y_4688_;
v___y_4624_ = v___y_4689_;
v___y_4625_ = v___y_4690_;
v___y_4626_ = v___y_4691_;
goto v___jp_4621_;
}
else
{
lean_object* v_inheritedTraceOptions_4697_; uint8_t v___x_4698_; 
v_inheritedTraceOptions_4697_ = lean_ctor_get(v_toCold_4694_, 11);
v___x_4698_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4697_, v_options_4695_, v___x_4197_);
if (v___x_4698_ == 0)
{
v___y_4622_ = v___y_4687_;
v___y_4623_ = v___y_4688_;
v___y_4624_ = v___y_4689_;
v___y_4625_ = v___y_4690_;
v___y_4626_ = v___y_4691_;
goto v___jp_4621_;
}
else
{
lean_object* v___x_4699_; lean_object* v___x_4700_; 
v___x_4699_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_4700_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3968_, v___x_4699_, v___y_4690_, v___y_4691_);
if (lean_obj_tag(v___x_4700_) == 0)
{
lean_dec_ref_known(v___x_4700_, 1);
v___y_4622_ = v___y_4687_;
v___y_4623_ = v___y_4688_;
v___y_4624_ = v___y_4689_;
v___y_4625_ = v___y_4690_;
v___y_4626_ = v___y_4691_;
goto v___jp_4621_;
}
else
{
lean_dec(v___y_4689_);
lean_dec_ref(v___y_4688_);
lean_dec(v_decl_3774_);
return v___x_4700_;
}
}
}
}
else
{
v___y_4652_ = v___y_4691_;
v___y_4653_ = v___y_4686_;
v___y_4654_ = v___x_4693_;
v___y_4655_ = v___y_4687_;
v___y_4656_ = v___y_4688_;
v___y_4657_ = v___y_4689_;
v___y_4658_ = v___y_4690_;
goto v___jp_4651_;
}
}
else
{
v___y_4652_ = v___y_4691_;
v___y_4653_ = v___y_4686_;
v___y_4654_ = v___x_4693_;
v___y_4655_ = v___y_4687_;
v___y_4656_ = v___y_4688_;
v___y_4657_ = v___y_4689_;
v___y_4658_ = v___y_4690_;
goto v___jp_4651_;
}
}
else
{
lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v_a_4703_; uint8_t v___x_4704_; 
lean_dec(v___y_4686_);
v___x_4701_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4702_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4701_, v___y_4690_);
v_a_4703_ = lean_ctor_get(v___x_4702_, 0);
lean_inc(v_a_4703_);
lean_dec_ref(v___x_4702_);
v___x_4704_ = lean_unbox(v_a_4703_);
lean_dec(v_a_4703_);
if (v___x_4704_ == 0)
{
lean_object* v_toCold_4705_; lean_object* v_options_4706_; uint8_t v_hasTrace_4707_; 
v_toCold_4705_ = lean_ctor_get(v___y_4690_, 0);
v_options_4706_ = lean_ctor_get(v_toCold_4705_, 2);
v_hasTrace_4707_ = lean_ctor_get_uint8(v_options_4706_, sizeof(void*)*1);
if (v_hasTrace_4707_ == 0)
{
v___y_4607_ = v___y_4687_;
v___y_4608_ = v___y_4688_;
v___y_4609_ = v___y_4689_;
v_exportedInfo_x3f_4610_ = v___x_4684_;
v___y_4611_ = v___y_4690_;
v___y_4612_ = v___y_4691_;
goto v___jp_4606_;
}
else
{
lean_object* v_inheritedTraceOptions_4708_; uint8_t v___x_4709_; 
v_inheritedTraceOptions_4708_ = lean_ctor_get(v_toCold_4705_, 11);
v___x_4709_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4708_, v_options_4706_, v___x_4197_);
if (v___x_4709_ == 0)
{
v___y_4607_ = v___y_4687_;
v___y_4608_ = v___y_4688_;
v___y_4609_ = v___y_4689_;
v_exportedInfo_x3f_4610_ = v___x_4684_;
v___y_4611_ = v___y_4690_;
v___y_4612_ = v___y_4691_;
goto v___jp_4606_;
}
else
{
lean_object* v___x_4710_; lean_object* v___x_4711_; 
v___x_4710_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_4711_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3968_, v___x_4710_, v___y_4690_, v___y_4691_);
if (lean_obj_tag(v___x_4711_) == 0)
{
lean_dec_ref_known(v___x_4711_, 1);
v___y_4607_ = v___y_4687_;
v___y_4608_ = v___y_4688_;
v___y_4609_ = v___y_4689_;
v_exportedInfo_x3f_4610_ = v___x_4684_;
v___y_4611_ = v___y_4690_;
v___y_4612_ = v___y_4691_;
goto v___jp_4606_;
}
else
{
lean_dec(v___y_4689_);
lean_dec_ref(v___y_4688_);
lean_dec(v_decl_3774_);
return v___x_4711_;
}
}
}
}
else
{
lean_object* v_toCold_4712_; lean_object* v_options_4713_; uint8_t v_hasTrace_4714_; 
v_toCold_4712_ = lean_ctor_get(v___y_4690_, 0);
v_options_4713_ = lean_ctor_get(v_toCold_4712_, 2);
v_hasTrace_4714_ = lean_ctor_get_uint8(v_options_4713_, sizeof(void*)*1);
if (v_hasTrace_4714_ == 0)
{
v___y_4629_ = v___y_4687_;
v___y_4630_ = v___y_4688_;
v___y_4631_ = v___y_4689_;
v___y_4632_ = v___y_4690_;
v___y_4633_ = v___y_4691_;
goto v___jp_4628_;
}
else
{
lean_object* v_inheritedTraceOptions_4715_; uint8_t v___x_4716_; 
v_inheritedTraceOptions_4715_ = lean_ctor_get(v_toCold_4712_, 11);
v___x_4716_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4715_, v_options_4713_, v___x_4197_);
if (v___x_4716_ == 0)
{
v___y_4629_ = v___y_4687_;
v___y_4630_ = v___y_4688_;
v___y_4631_ = v___y_4689_;
v___y_4632_ = v___y_4690_;
v___y_4633_ = v___y_4691_;
goto v___jp_4628_;
}
else
{
lean_object* v___x_4717_; lean_object* v___x_4718_; 
v___x_4717_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_4718_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3968_, v___x_4717_, v___y_4690_, v___y_4691_);
if (lean_obj_tag(v___x_4718_) == 0)
{
lean_dec_ref_known(v___x_4718_, 1);
v___y_4629_ = v___y_4687_;
v___y_4630_ = v___y_4688_;
v___y_4631_ = v___y_4689_;
v___y_4632_ = v___y_4690_;
v___y_4633_ = v___y_4691_;
goto v___jp_4628_;
}
else
{
lean_dec(v___y_4689_);
lean_dec_ref(v___y_4688_);
lean_dec(v_decl_3774_);
return v___x_4718_;
}
}
}
}
}
}
v___jp_4719_:
{
lean_object* v___x_4726_; lean_object* v_env_4727_; uint8_t v___x_4728_; 
v___x_4726_ = lean_st_ref_get(v___y_4725_);
v_env_4727_ = lean_ctor_get(v___x_4726_, 0);
lean_inc_ref(v_env_4727_);
lean_dec(v___x_4726_);
v___x_4728_ = l_Lean_Environment_containsOnBranch(v_env_4727_, v_fst_4720_);
lean_dec_ref(v_env_4727_);
if (v___x_4728_ == 0)
{
v___y_4686_ = v_exportedInfo_x3f_4723_;
v___y_4687_ = v_snd_4722_;
v___y_4688_ = v_fst_4721_;
v___y_4689_ = v_fst_4720_;
v___y_4690_ = v___y_4724_;
v___y_4691_ = v___y_4725_;
goto v___jp_4685_;
}
else
{
lean_object* v___x_4729_; lean_object* v_env_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; 
lean_dec(v_exportedInfo_x3f_4723_);
lean_dec_ref(v_fst_4721_);
lean_dec(v_decl_3774_);
v___x_4729_ = lean_st_ref_get(v___y_4725_);
v_env_4730_ = lean_ctor_get(v___x_4729_, 0);
lean_inc_ref(v_env_4730_);
lean_dec(v___x_4729_);
v___x_4731_ = lean_elab_environment_to_kernel_env(v_env_4730_);
v___x_4732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4732_, 0, v___x_4731_);
lean_ctor_set(v___x_4732_, 1, v_fst_4720_);
v___x_4733_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4732_, v___y_4724_, v___y_4725_);
return v___x_4733_;
}
}
v___jp_4734_:
{
lean_object* v_toConstantVal_4739_; lean_object* v_name_4740_; lean_object* v___x_4741_; uint8_t v___x_4742_; 
v_toConstantVal_4739_ = lean_ctor_get(v___y_4735_, 0);
v_name_4740_ = lean_ctor_get(v_toConstantVal_4739_, 0);
lean_inc(v_name_4740_);
v___x_4741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4741_, 0, v___y_4735_);
v___x_4742_ = 0;
v_fst_4720_ = v_name_4740_;
v_fst_4721_ = v___x_4741_;
v_snd_4722_ = v___x_4742_;
v_exportedInfo_x3f_4723_ = v_exportedInfo_x3f_4736_;
v___y_4724_ = v___y_4737_;
v___y_4725_ = v___y_4738_;
goto v___jp_4719_;
}
v___jp_4743_:
{
lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; 
v___x_4749_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4749_, 0, v___y_4746_);
lean_ctor_set_uint8(v___x_4749_, sizeof(void*)*1, v___y_4748_);
v___x_4750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4750_, 0, v___x_4749_);
v___x_4751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4751_, 0, v___x_4750_);
v___y_4735_ = v___y_4747_;
v_exportedInfo_x3f_4736_ = v___x_4751_;
v___y_4737_ = v___y_4745_;
v___y_4738_ = v___y_4744_;
goto v___jp_4734_;
}
v___jp_4752_:
{
uint8_t v___x_4759_; uint8_t v___x_4760_; 
v___x_4759_ = 1;
v___x_4760_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4756_, v___x_4759_);
if (v___x_4760_ == 0)
{
v___y_4744_ = v___y_4758_;
v___y_4745_ = v___y_4757_;
v___y_4746_ = v_toConstantVal_4755_;
v___y_4747_ = v___y_4754_;
v___y_4748_ = v___y_4753_;
goto v___jp_4743_;
}
else
{
v___y_4744_ = v___y_4758_;
v___y_4745_ = v___y_4757_;
v___y_4746_ = v_toConstantVal_4755_;
v___y_4747_ = v___y_4754_;
v___y_4748_ = v___x_4503_;
goto v___jp_4743_;
}
}
v___jp_4761_:
{
lean_object* v_toConstantVal_4766_; uint8_t v_safety_4767_; 
v_toConstantVal_4766_ = lean_ctor_get(v___y_4763_, 0);
lean_inc_ref(v_toConstantVal_4766_);
v_safety_4767_ = lean_ctor_get_uint8(v___y_4763_, sizeof(void*)*4);
v___y_4753_ = v___y_4762_;
v___y_4754_ = v___y_4763_;
v_toConstantVal_4755_ = v_toConstantVal_4766_;
v_safety_4756_ = v_safety_4767_;
v___y_4757_ = v___y_4764_;
v___y_4758_ = v___y_4765_;
goto v___jp_4752_;
}
v___jp_4768_:
{
lean_object* v_toCold_4773_; lean_object* v_options_4774_; uint8_t v_hasTrace_4775_; 
v_toCold_4773_ = lean_ctor_get(v___y_4771_, 0);
v_options_4774_ = lean_ctor_get(v_toCold_4773_, 2);
v_hasTrace_4775_ = lean_ctor_get_uint8(v_options_4774_, sizeof(void*)*1);
if (v_hasTrace_4775_ == 0)
{
v___y_4762_ = v___y_4772_;
v___y_4763_ = v___y_4770_;
v___y_4764_ = v___y_4771_;
v___y_4765_ = v___y_4769_;
goto v___jp_4761_;
}
else
{
lean_object* v_inheritedTraceOptions_4776_; uint8_t v___x_4777_; 
v_inheritedTraceOptions_4776_ = lean_ctor_get(v_toCold_4773_, 11);
v___x_4777_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4776_, v_options_4774_, v___x_4197_);
if (v___x_4777_ == 0)
{
v___y_4762_ = v___y_4772_;
v___y_4763_ = v___y_4770_;
v___y_4764_ = v___y_4771_;
v___y_4765_ = v___y_4769_;
goto v___jp_4761_;
}
else
{
lean_object* v_toConstantVal_4778_; uint8_t v_safety_4779_; lean_object* v_name_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; 
v_toConstantVal_4778_ = lean_ctor_get(v___y_4770_, 0);
lean_inc_ref(v_toConstantVal_4778_);
v_safety_4779_ = lean_ctor_get_uint8(v___y_4770_, sizeof(void*)*4);
v_name_4780_ = lean_ctor_get(v_toConstantVal_4778_, 0);
v___x_4781_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_4780_);
v___x_4782_ = l_Lean_MessageData_ofName(v_name_4780_);
v___x_4783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4783_, 0, v___x_4781_);
lean_ctor_set(v___x_4783_, 1, v___x_4782_);
v___x_4784_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4785_, 0, v___x_4783_);
lean_ctor_set(v___x_4785_, 1, v___x_4784_);
v___x_4786_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3968_, v___x_4785_, v___y_4771_, v___y_4769_);
if (lean_obj_tag(v___x_4786_) == 0)
{
lean_dec_ref_known(v___x_4786_, 1);
v___y_4753_ = v___y_4772_;
v___y_4754_ = v___y_4770_;
v_toConstantVal_4755_ = v_toConstantVal_4778_;
v_safety_4756_ = v_safety_4779_;
v___y_4757_ = v___y_4771_;
v___y_4758_ = v___y_4769_;
goto v___jp_4752_;
}
else
{
lean_dec_ref(v_toConstantVal_4778_);
lean_dec_ref(v___y_4770_);
lean_dec(v_decl_3774_);
return v___x_4786_;
}
}
}
}
v___jp_4787_:
{
lean_object* v___x_4793_; uint8_t v_isModule_4794_; 
v___x_4793_ = l_Lean_Environment_header(v___y_4790_);
lean_dec_ref(v___y_4790_);
v_isModule_4794_ = lean_ctor_get_uint8(v___x_4793_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4793_);
if (v_isModule_4794_ == 0)
{
lean_dec_ref(v___y_4788_);
v___y_4735_ = v___y_4791_;
v_exportedInfo_x3f_4736_ = v___x_4684_;
v___y_4737_ = v___y_4792_;
v___y_4738_ = v___y_4789_;
goto v___jp_4734_;
}
else
{
uint8_t v_isExporting_4795_; 
v_isExporting_4795_ = lean_ctor_get_uint8(v___y_4788_, sizeof(void*)*13);
lean_dec_ref(v___y_4788_);
if (v_isExporting_4795_ == 0)
{
v___y_4769_ = v___y_4789_;
v___y_4770_ = v___y_4791_;
v___y_4771_ = v___y_4792_;
v___y_4772_ = v_isModule_4794_;
goto v___jp_4768_;
}
else
{
if (v___x_4503_ == 0)
{
v___y_4735_ = v___y_4791_;
v_exportedInfo_x3f_4736_ = v___x_4684_;
v___y_4737_ = v___y_4792_;
v___y_4738_ = v___y_4789_;
goto v___jp_4734_;
}
else
{
v___y_4769_ = v___y_4789_;
v___y_4770_ = v___y_4791_;
v___y_4771_ = v___y_4792_;
v___y_4772_ = v___x_4503_;
goto v___jp_4768_;
}
}
}
}
v___jp_4796_:
{
lean_object* v___x_4800_; lean_object* v_env_4801_; lean_object* v___x_4802_; 
v___x_4800_ = lean_st_ref_get(v___y_4799_);
v_env_4801_ = lean_ctor_get(v___x_4800_, 0);
lean_inc_ref(v_env_4801_);
lean_dec(v___x_4800_);
v___x_4802_ = lean_st_ref_get(v___y_4799_);
if (v_forceExpose_3775_ == 0)
{
lean_object* v_env_4803_; 
v_env_4803_ = lean_ctor_get(v___x_4802_, 0);
lean_inc_ref(v_env_4803_);
lean_dec(v___x_4802_);
v___y_4788_ = v_env_4803_;
v___y_4789_ = v___y_4799_;
v___y_4790_ = v_env_4801_;
v___y_4791_ = v_defn_4797_;
v___y_4792_ = v___y_4798_;
goto v___jp_4787_;
}
else
{
if (v___x_4503_ == 0)
{
lean_dec(v___x_4802_);
lean_dec_ref(v_env_4801_);
v___y_4735_ = v_defn_4797_;
v_exportedInfo_x3f_4736_ = v___x_4684_;
v___y_4737_ = v___y_4798_;
v___y_4738_ = v___y_4799_;
goto v___jp_4734_;
}
else
{
lean_object* v_env_4804_; 
v_env_4804_ = lean_ctor_get(v___x_4802_, 0);
lean_inc_ref(v_env_4804_);
lean_dec(v___x_4802_);
v___y_4788_ = v_env_4804_;
v___y_4789_ = v___y_4799_;
v___y_4790_ = v_env_4801_;
v___y_4791_ = v_defn_4797_;
v___y_4792_ = v___y_4798_;
goto v___jp_4787_;
}
}
}
}
}
}
else
{
goto v___jp_4346_;
}
v___jp_4504_:
{
lean_object* v___x_4516_; 
lean_inc_ref(v___y_4508_);
v___x_4516_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_4507_, v___y_4508_, v___y_4506_, v___y_4515_);
if (lean_obj_tag(v___x_4516_) == 0)
{
lean_object* v___x_4517_; lean_object* v___x_4519_; uint8_t v_isShared_4520_; uint8_t v_isSharedCheck_4563_; 
lean_dec_ref_known(v___x_4516_, 1);
lean_dec(v___y_4512_);
lean_inc_ref(v___y_4513_);
v___x_4517_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4513_, v___y_4509_);
v_isSharedCheck_4563_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4563_ == 0)
{
lean_object* v_unused_4564_; 
v_unused_4564_ = lean_ctor_get(v___x_4517_, 0);
lean_dec(v_unused_4564_);
v___x_4519_ = v___x_4517_;
v_isShared_4520_ = v_isSharedCheck_4563_;
goto v_resetjp_4518_;
}
else
{
lean_dec(v___x_4517_);
v___x_4519_ = lean_box(0);
v_isShared_4520_ = v_isSharedCheck_4563_;
goto v_resetjp_4518_;
}
v_resetjp_4518_:
{
lean_object* v___x_4521_; lean_object* v___x_4522_; uint8_t v___x_4523_; 
v___x_4521_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4505_);
v___x_4522_ = l_Lean_Elab_async;
v___x_4523_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_4521_, v___x_4522_);
lean_dec_ref(v___x_4521_);
if (v___x_4523_ == 0)
{
lean_object* v___x_4524_; lean_object* v_r_4525_; 
lean_del_object(v___x_4519_);
lean_dec_ref(v___y_4514_);
lean_dec_ref(v___y_4510_);
v___x_4524_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4508_, v___y_4509_);
lean_dec_ref(v___x_4524_);
v_r_4525_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3774_, v___y_4505_, v___y_4509_);
if (lean_obj_tag(v_r_4525_) == 0)
{
lean_object* v_a_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4535_; 
v_a_4526_ = lean_ctor_get(v_r_4525_, 0);
v_isSharedCheck_4535_ = !lean_is_exclusive(v_r_4525_);
if (v_isSharedCheck_4535_ == 0)
{
v___x_4528_ = v_r_4525_;
v_isShared_4529_ = v_isSharedCheck_4535_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_a_4526_);
lean_dec(v_r_4525_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4535_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v___x_4531_; 
lean_inc(v_a_4526_);
if (v_isShared_4529_ == 0)
{
lean_ctor_set_tag(v___x_4528_, 1);
v___x_4531_ = v___x_4528_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4534_; 
v_reuseFailAlloc_4534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4534_, 0, v_a_4526_);
v___x_4531_ = v_reuseFailAlloc_4534_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
lean_object* v___x_4532_; 
v___x_4532_ = lean_apply_2(v___y_4511_, v___x_4531_, lean_box(0));
if (lean_obj_tag(v___x_4532_) == 0)
{
lean_dec_ref_known(v___x_4532_, 1);
v___y_3780_ = v___y_4509_;
v___y_3781_ = v___y_4513_;
v_a_3782_ = v_a_4526_;
goto v___jp_3779_;
}
else
{
lean_object* v_a_4533_; 
lean_dec(v_a_4526_);
v_a_4533_ = lean_ctor_get(v___x_4532_, 0);
lean_inc(v_a_4533_);
lean_dec_ref_known(v___x_4532_, 1);
v___y_3793_ = v___y_4509_;
v___y_3794_ = v___y_4513_;
v_a_3795_ = v_a_4533_;
goto v___jp_3792_;
}
}
}
}
else
{
lean_object* v_a_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; 
v_a_4536_ = lean_ctor_get(v_r_4525_, 0);
lean_inc(v_a_4536_);
lean_dec_ref_known(v_r_4525_, 1);
v___x_4537_ = lean_box(0);
v___x_4538_ = lean_apply_2(v___y_4511_, v___x_4537_, lean_box(0));
if (lean_obj_tag(v___x_4538_) == 0)
{
lean_dec_ref_known(v___x_4538_, 1);
v___y_3793_ = v___y_4509_;
v___y_3794_ = v___y_4513_;
v_a_3795_ = v_a_4536_;
goto v___jp_3792_;
}
else
{
lean_object* v_a_4539_; 
lean_dec(v_a_4536_);
v_a_4539_ = lean_ctor_get(v___x_4538_, 0);
lean_inc(v_a_4539_);
lean_dec_ref_known(v___x_4538_, 1);
v___y_3793_ = v___y_4509_;
v___y_3794_ = v___y_4513_;
v_a_3795_ = v_a_4539_;
goto v___jp_3792_;
}
}
}
else
{
lean_object* v___x_4540_; lean_object* v___x_4542_; 
lean_dec_ref(v___y_4513_);
lean_dec_ref(v___y_4511_);
lean_dec_ref(v___y_4508_);
lean_dec(v_decl_3774_);
v___x_4540_ = l_IO_CancelToken_new();
if (v_isShared_4520_ == 0)
{
lean_ctor_set_tag(v___x_4519_, 1);
lean_ctor_set(v___x_4519_, 0, v___x_4540_);
v___x_4542_ = v___x_4519_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v___x_4540_);
v___x_4542_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; 
v___x_4543_ = lean_unsigned_to_nat(0u);
v___x_4544_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_4545_ = l_Lean_Name_toString(v___x_4544_, v_hasTrace_3834_);
lean_inc_ref(v___x_4542_);
v___x_4546_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_4510_, v___x_4542_, v___x_4545_, v___y_4505_, v___y_4509_);
if (lean_obj_tag(v___x_4546_) == 0)
{
lean_object* v_a_4547_; lean_object* v_checked_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; 
v_a_4547_ = lean_ctor_get(v___x_4546_, 0);
lean_inc(v_a_4547_);
lean_dec_ref_known(v___x_4546_, 1);
v_checked_4548_ = lean_ctor_get(v___y_4514_, 2);
lean_inc_ref(v_checked_4548_);
lean_dec_ref(v___y_4514_);
v___x_4549_ = lean_io_map_task(v_a_4547_, v_checked_4548_, v___x_4543_, v___x_4503_);
v___x_4550_ = lean_box(0);
v___x_4551_ = lean_box(2);
v___x_4552_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4552_, 0, v___x_4550_);
lean_ctor_set(v___x_4552_, 1, v___x_4551_);
lean_ctor_set(v___x_4552_, 2, v___x_4542_);
lean_ctor_set(v___x_4552_, 3, v___x_4549_);
v___x_4553_ = l_Lean_Core_logSnapshotTask___redArg(v___x_4552_, v___y_4509_);
return v___x_4553_;
}
else
{
lean_object* v_a_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4561_; 
lean_dec_ref(v___x_4542_);
lean_dec_ref(v___y_4514_);
v_a_4554_ = lean_ctor_get(v___x_4546_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v___x_4546_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4556_ = v___x_4546_;
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_a_4554_);
lean_dec(v___x_4546_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4559_; 
if (v_isShared_4557_ == 0)
{
v___x_4559_ = v___x_4556_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_a_4554_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
return v___x_4559_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4565_; lean_object* v___x_4567_; uint8_t v_isShared_4568_; uint8_t v_isSharedCheck_4576_; 
lean_dec_ref(v___y_4514_);
lean_dec_ref(v___y_4513_);
lean_dec_ref(v___y_4511_);
lean_dec_ref(v___y_4510_);
lean_dec_ref(v___y_4508_);
lean_dec(v_decl_3774_);
v_a_4565_ = lean_ctor_get(v___x_4516_, 0);
v_isSharedCheck_4576_ = !lean_is_exclusive(v___x_4516_);
if (v_isSharedCheck_4576_ == 0)
{
v___x_4567_ = v___x_4516_;
v_isShared_4568_ = v_isSharedCheck_4576_;
goto v_resetjp_4566_;
}
else
{
lean_inc(v_a_4565_);
lean_dec(v___x_4516_);
v___x_4567_ = lean_box(0);
v_isShared_4568_ = v_isSharedCheck_4576_;
goto v_resetjp_4566_;
}
v_resetjp_4566_:
{
lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4574_; 
v___x_4569_ = lean_io_error_to_string(v_a_4565_);
v___x_4570_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4570_, 0, v___x_4569_);
v___x_4571_ = l_Lean_MessageData_ofFormat(v___x_4570_);
v___x_4572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4572_, 0, v___y_4512_);
lean_ctor_set(v___x_4572_, 1, v___x_4571_);
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 0, v___x_4572_);
v___x_4574_ = v___x_4567_;
goto v_reusejp_4573_;
}
else
{
lean_object* v_reuseFailAlloc_4575_; 
v_reuseFailAlloc_4575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4575_, 0, v___x_4572_);
v___x_4574_ = v_reuseFailAlloc_4575_;
goto v_reusejp_4573_;
}
v_reusejp_4573_:
{
return v___x_4574_;
}
}
}
}
v___jp_4577_:
{
lean_object* v_ref_4586_; lean_object* v___x_4587_; 
v_ref_4586_ = lean_ctor_get(v___y_4578_, 2);
lean_inc_ref(v___y_4584_);
v___x_4587_ = l_Lean_Environment_addConstAsync(v___y_4584_, v___y_4581_, v___y_4583_, v___y_4585_, v___x_4503_, v_hasTrace_3834_);
if (lean_obj_tag(v___x_4587_) == 0)
{
lean_object* v_a_4588_; lean_object* v_mainEnv_4589_; lean_object* v_asyncEnv_4590_; lean_object* v___f_4591_; lean_object* v___f_4592_; lean_object* v___x_4593_; 
v_a_4588_ = lean_ctor_get(v___x_4587_, 0);
lean_inc_n(v_a_4588_, 3);
lean_dec_ref_known(v___x_4587_, 1);
v_mainEnv_4589_ = lean_ctor_get(v_a_4588_, 0);
lean_inc_ref(v_mainEnv_4589_);
v_asyncEnv_4590_ = lean_ctor_get(v_a_4588_, 1);
lean_inc_ref_n(v_asyncEnv_4590_, 2);
lean_inc(v_ref_4586_);
lean_inc(v___y_4582_);
v___f_4591_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4591_, 0, v___y_4582_);
lean_closure_set(v___f_4591_, 1, v_a_4588_);
lean_closure_set(v___f_4591_, 2, v_ref_4586_);
lean_inc(v_decl_3774_);
v___f_4592_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4592_, 0, v_a_4588_);
lean_closure_set(v___f_4592_, 1, v_asyncEnv_4590_);
lean_closure_set(v___f_4592_, 2, v_decl_3774_);
v___x_4593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4593_, 0, v___y_4579_);
if (lean_obj_tag(v___y_4580_) == 0)
{
lean_inc(v_ref_4586_);
lean_inc_ref(v___x_4593_);
v___y_4505_ = v___y_4578_;
v___y_4506_ = v___x_4593_;
v___y_4507_ = v_a_4588_;
v___y_4508_ = v_asyncEnv_4590_;
v___y_4509_ = v___y_4582_;
v___y_4510_ = v___f_4592_;
v___y_4511_ = v___f_4591_;
v___y_4512_ = v_ref_4586_;
v___y_4513_ = v_mainEnv_4589_;
v___y_4514_ = v___y_4584_;
v___y_4515_ = v___x_4593_;
goto v___jp_4504_;
}
else
{
lean_inc(v_ref_4586_);
v___y_4505_ = v___y_4578_;
v___y_4506_ = v___x_4593_;
v___y_4507_ = v_a_4588_;
v___y_4508_ = v_asyncEnv_4590_;
v___y_4509_ = v___y_4582_;
v___y_4510_ = v___f_4592_;
v___y_4511_ = v___f_4591_;
v___y_4512_ = v_ref_4586_;
v___y_4513_ = v_mainEnv_4589_;
v___y_4514_ = v___y_4584_;
v___y_4515_ = v___y_4580_;
goto v___jp_4504_;
}
}
else
{
lean_object* v_a_4594_; lean_object* v___x_4596_; uint8_t v_isShared_4597_; uint8_t v_isSharedCheck_4605_; 
lean_dec_ref(v___y_4584_);
lean_dec(v___y_4580_);
lean_dec_ref(v___y_4579_);
lean_dec(v_decl_3774_);
v_a_4594_ = lean_ctor_get(v___x_4587_, 0);
v_isSharedCheck_4605_ = !lean_is_exclusive(v___x_4587_);
if (v_isSharedCheck_4605_ == 0)
{
v___x_4596_ = v___x_4587_;
v_isShared_4597_ = v_isSharedCheck_4605_;
goto v_resetjp_4595_;
}
else
{
lean_inc(v_a_4594_);
lean_dec(v___x_4587_);
v___x_4596_ = lean_box(0);
v_isShared_4597_ = v_isSharedCheck_4605_;
goto v_resetjp_4595_;
}
v_resetjp_4595_:
{
lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4603_; 
v___x_4598_ = lean_io_error_to_string(v_a_4594_);
v___x_4599_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4599_, 0, v___x_4598_);
v___x_4600_ = l_Lean_MessageData_ofFormat(v___x_4599_);
lean_inc(v_ref_4586_);
v___x_4601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4601_, 0, v_ref_4586_);
lean_ctor_set(v___x_4601_, 1, v___x_4600_);
if (v_isShared_4597_ == 0)
{
lean_ctor_set(v___x_4596_, 0, v___x_4601_);
v___x_4603_ = v___x_4596_;
goto v_reusejp_4602_;
}
else
{
lean_object* v_reuseFailAlloc_4604_; 
v_reuseFailAlloc_4604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4604_, 0, v___x_4601_);
v___x_4603_ = v_reuseFailAlloc_4604_;
goto v_reusejp_4602_;
}
v_reusejp_4602_:
{
return v___x_4603_;
}
}
}
}
v___jp_4606_:
{
lean_object* v___x_4613_; 
v___x_4613_ = lean_st_ref_get(v___y_4612_);
if (lean_obj_tag(v_exportedInfo_x3f_4610_) == 0)
{
lean_object* v_env_4614_; lean_object* v___x_4615_; 
v_env_4614_ = lean_ctor_get(v___x_4613_, 0);
lean_inc_ref(v_env_4614_);
lean_dec(v___x_4613_);
v___x_4615_ = lean_box(0);
v___y_4578_ = v___y_4611_;
v___y_4579_ = v___y_4608_;
v___y_4580_ = v_exportedInfo_x3f_4610_;
v___y_4581_ = v___y_4609_;
v___y_4582_ = v___y_4612_;
v___y_4583_ = v___y_4607_;
v___y_4584_ = v_env_4614_;
v___y_4585_ = v___x_4615_;
goto v___jp_4577_;
}
else
{
lean_object* v_env_4616_; lean_object* v_val_4617_; uint8_t v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; 
v_env_4616_ = lean_ctor_get(v___x_4613_, 0);
lean_inc_ref(v_env_4616_);
lean_dec(v___x_4613_);
v_val_4617_ = lean_ctor_get(v_exportedInfo_x3f_4610_, 0);
v___x_4618_ = l_Lean_ConstantKind_ofConstantInfo(v_val_4617_);
v___x_4619_ = lean_box(v___x_4618_);
v___x_4620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4620_, 0, v___x_4619_);
v___y_4578_ = v___y_4611_;
v___y_4579_ = v___y_4608_;
v___y_4580_ = v_exportedInfo_x3f_4610_;
v___y_4581_ = v___y_4609_;
v___y_4582_ = v___y_4612_;
v___y_4583_ = v___y_4607_;
v___y_4584_ = v_env_4616_;
v___y_4585_ = v___x_4620_;
goto v___jp_4577_;
}
}
v___jp_4621_:
{
lean_object* v___x_4627_; 
lean_inc_ref(v___y_4623_);
v___x_4627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4627_, 0, v___y_4623_);
v___y_4607_ = v___y_4622_;
v___y_4608_ = v___y_4623_;
v___y_4609_ = v___y_4624_;
v_exportedInfo_x3f_4610_ = v___x_4627_;
v___y_4611_ = v___y_4625_;
v___y_4612_ = v___y_4626_;
goto v___jp_4606_;
}
v___jp_4628_:
{
lean_object* v___x_4634_; 
lean_inc_ref(v___y_4630_);
v___x_4634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4634_, 0, v___y_4630_);
v___y_4607_ = v___y_4629_;
v___y_4608_ = v___y_4630_;
v___y_4609_ = v___y_4631_;
v_exportedInfo_x3f_4610_ = v___x_4634_;
v___y_4611_ = v___y_4632_;
v___y_4612_ = v___y_4633_;
goto v___jp_4606_;
}
}
else
{
goto v___jp_4346_;
}
v___jp_4199_:
{
lean_object* v___x_4203_; double v___x_4204_; double v___x_4205_; double v___x_4206_; double v___x_4207_; double v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; 
v___x_4203_ = lean_io_mono_nanos_now();
v___x_4204_ = lean_float_of_nat(v___y_4200_);
v___x_4205_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_4206_ = lean_float_div(v___x_4204_, v___x_4205_);
v___x_4207_ = lean_float_of_nat(v___x_4203_);
v___x_4208_ = lean_float_div(v___x_4207_, v___x_4205_);
v___x_4209_ = lean_box_float(v___x_4206_);
v___x_4210_ = lean_box_float(v___x_4208_);
v___x_4211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4211_, 0, v___x_4209_);
lean_ctor_set(v___x_4211_, 1, v___x_4210_);
v___x_4212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4212_, 0, v_a_4202_);
lean_ctor_set(v___x_4212_, 1, v___x_4211_);
v___x_4213_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3968_, v_hasTrace_3834_, v___x_4196_, v_options_3832_, v___x_4198_, v___y_4201_, v___f_4195_, v___x_4212_, v_a_3776_, v_a_3777_);
return v___x_4213_;
}
v___jp_4214_:
{
if (lean_obj_tag(v___y_4217_) == 0)
{
lean_object* v_a_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4225_; 
v_a_4218_ = lean_ctor_get(v___y_4217_, 0);
v_isSharedCheck_4225_ = !lean_is_exclusive(v___y_4217_);
if (v_isSharedCheck_4225_ == 0)
{
v___x_4220_ = v___y_4217_;
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_a_4218_);
lean_dec(v___y_4217_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4223_; 
if (v_isShared_4221_ == 0)
{
lean_ctor_set_tag(v___x_4220_, 1);
v___x_4223_ = v___x_4220_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v_a_4218_);
v___x_4223_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
v___y_4200_ = v___y_4215_;
v___y_4201_ = v___y_4216_;
v_a_4202_ = v___x_4223_;
goto v___jp_4199_;
}
}
}
else
{
lean_object* v_a_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4233_; 
v_a_4226_ = lean_ctor_get(v___y_4217_, 0);
v_isSharedCheck_4233_ = !lean_is_exclusive(v___y_4217_);
if (v_isSharedCheck_4233_ == 0)
{
v___x_4228_ = v___y_4217_;
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_a_4226_);
lean_dec(v___y_4217_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v___x_4231_; 
if (v_isShared_4229_ == 0)
{
lean_ctor_set_tag(v___x_4228_, 0);
v___x_4231_ = v___x_4228_;
goto v_reusejp_4230_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_a_4226_);
v___x_4231_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4230_;
}
v_reusejp_4230_:
{
v___y_4200_ = v___y_4215_;
v___y_4201_ = v___y_4216_;
v_a_4202_ = v___x_4231_;
goto v___jp_4199_;
}
}
}
}
v___jp_4234_:
{
lean_object* v___x_4239_; lean_object* v___x_4240_; 
v___x_4239_ = lean_box(0);
lean_inc(v_a_3777_);
lean_inc_ref(v_a_3776_);
v___x_4240_ = lean_apply_5(v___y_4236_, v___x_4239_, v___y_4235_, v_a_3776_, v_a_3777_, lean_box(0));
v___y_4215_ = v___y_4237_;
v___y_4216_ = v___y_4238_;
v___y_4217_ = v___x_4240_;
goto v___jp_4214_;
}
v___jp_4241_:
{
lean_object* v___x_4249_; uint8_t v_isModule_4250_; 
v___x_4249_ = l_Lean_Environment_header(v___y_4246_);
lean_dec_ref(v___y_4246_);
v_isModule_4250_ = lean_ctor_get_uint8(v___x_4249_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4249_);
if (v_isModule_4250_ == 0)
{
lean_dec_ref(v___y_4245_);
lean_dec_ref(v___y_4242_);
v___y_4235_ = v___y_4243_;
v___y_4236_ = v___y_4244_;
v___y_4237_ = v___y_4247_;
v___y_4238_ = v___y_4248_;
goto v___jp_4234_;
}
else
{
lean_dec_ref(v___y_4244_);
lean_dec(v___y_4243_);
if (v___x_4198_ == 0)
{
lean_object* v___x_4251_; lean_object* v___x_4252_; 
lean_dec_ref(v___y_4245_);
v___x_4251_ = lean_box(0);
lean_inc(v_a_3777_);
lean_inc_ref(v_a_3776_);
v___x_4252_ = lean_apply_4(v___y_4242_, v___x_4251_, v_a_3776_, v_a_3777_, lean_box(0));
v___y_4215_ = v___y_4247_;
v___y_4216_ = v___y_4248_;
v___y_4217_ = v___x_4252_;
goto v___jp_4214_;
}
else
{
lean_object* v_toConstantVal_4253_; lean_object* v_name_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; 
v_toConstantVal_4253_ = lean_ctor_get(v___y_4245_, 0);
lean_inc_ref(v_toConstantVal_4253_);
lean_dec_ref(v___y_4245_);
v_name_4254_ = lean_ctor_get(v_toConstantVal_4253_, 0);
lean_inc(v_name_4254_);
lean_dec_ref(v_toConstantVal_4253_);
v___x_4255_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
v___x_4256_ = l_Lean_MessageData_ofName(v_name_4254_);
v___x_4257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4257_, 0, v___x_4255_);
lean_ctor_set(v___x_4257_, 1, v___x_4256_);
v___x_4258_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4259_, 0, v___x_4257_);
lean_ctor_set(v___x_4259_, 1, v___x_4258_);
v___x_4260_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3968_, v___x_4259_, v_a_3776_, v_a_3777_);
if (lean_obj_tag(v___x_4260_) == 0)
{
lean_object* v_a_4261_; lean_object* v___x_4262_; 
v_a_4261_ = lean_ctor_get(v___x_4260_, 0);
lean_inc(v_a_4261_);
lean_dec_ref_known(v___x_4260_, 1);
lean_inc(v_a_3777_);
lean_inc_ref(v_a_3776_);
v___x_4262_ = lean_apply_4(v___y_4242_, v_a_4261_, v_a_3776_, v_a_3777_, lean_box(0));
v___y_4215_ = v___y_4247_;
v___y_4216_ = v___y_4248_;
v___y_4217_ = v___x_4262_;
goto v___jp_4214_;
}
else
{
lean_dec_ref(v___y_4242_);
v___y_4215_ = v___y_4247_;
v___y_4216_ = v___y_4248_;
v___y_4217_ = v___x_4260_;
goto v___jp_4214_;
}
}
}
}
v___jp_4263_:
{
if (v___x_4198_ == 0)
{
lean_object* v___x_4268_; lean_object* v___x_4269_; 
lean_dec_ref(v___y_4265_);
v___x_4268_ = lean_box(0);
lean_inc(v_a_3777_);
lean_inc_ref(v_a_3776_);
v___x_4269_ = lean_apply_4(v___y_4264_, v___x_4268_, v_a_3776_, v_a_3777_, lean_box(0));
v___y_4215_ = v___y_4266_;
v___y_4216_ = v___y_4267_;
v___y_4217_ = v___x_4269_;
goto v___jp_4214_;
}
else
{
lean_object* v_toConstantVal_4270_; lean_object* v_name_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v_toConstantVal_4270_ = lean_ctor_get(v___y_4265_, 0);
lean_inc_ref(v_toConstantVal_4270_);
lean_dec_ref(v___y_4265_);
v_name_4271_ = lean_ctor_get(v_toConstantVal_4270_, 0);
lean_inc(v_name_4271_);
lean_dec_ref(v_toConstantVal_4270_);
v___x_4272_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
v___x_4273_ = l_Lean_MessageData_ofName(v_name_4271_);
v___x_4274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4274_, 0, v___x_4272_);
lean_ctor_set(v___x_4274_, 1, v___x_4273_);
v___x_4275_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4276_, 0, v___x_4274_);
lean_ctor_set(v___x_4276_, 1, v___x_4275_);
v___x_4277_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3968_, v___x_4276_, v_a_3776_, v_a_3777_);
if (lean_obj_tag(v___x_4277_) == 0)
{
lean_object* v_a_4278_; lean_object* v___x_4279_; 
v_a_4278_ = lean_ctor_get(v___x_4277_, 0);
lean_inc(v_a_4278_);
lean_dec_ref_known(v___x_4277_, 1);
lean_inc(v_a_3777_);
lean_inc_ref(v_a_3776_);
v___x_4279_ = lean_apply_4(v___y_4264_, v_a_4278_, v_a_3776_, v_a_3777_, lean_box(0));
v___y_4215_ = v___y_4266_;
v___y_4216_ = v___y_4267_;
v___y_4217_ = v___x_4279_;
goto v___jp_4214_;
}
else
{
lean_dec_ref(v___y_4264_);
v___y_4215_ = v___y_4266_;
v___y_4216_ = v___y_4267_;
v___y_4217_ = v___x_4277_;
goto v___jp_4214_;
}
}
}
v___jp_4280_:
{
lean_object* v___x_4285_; lean_object* v___x_4286_; 
v___x_4285_ = lean_box(0);
lean_inc(v_a_3777_);
lean_inc_ref(v_a_3776_);
v___x_4286_ = lean_apply_5(v___y_4281_, v___x_4285_, v___y_4282_, v_a_3776_, v_a_3777_, lean_box(0));
v___y_4215_ = v___y_4283_;
v___y_4216_ = v___y_4284_;
v___y_4217_ = v___x_4286_;
goto v___jp_4214_;
}
v___jp_4287_:
{
lean_object* v___x_4297_; uint8_t v_isModule_4298_; 
v___x_4297_ = l_Lean_Environment_header(v___y_4293_);
lean_dec_ref(v___y_4293_);
v_isModule_4298_ = lean_ctor_get_uint8(v___x_4297_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4297_);
if (v_isModule_4298_ == 0)
{
lean_dec_ref(v___y_4294_);
lean_dec_ref(v___y_4292_);
lean_dec_ref(v___y_4290_);
v___y_4281_ = v___y_4288_;
v___y_4282_ = v___y_4289_;
v___y_4283_ = v___y_4295_;
v___y_4284_ = v___y_4296_;
goto v___jp_4280_;
}
else
{
uint8_t v_isExporting_4299_; 
v_isExporting_4299_ = lean_ctor_get_uint8(v___y_4292_, sizeof(void*)*13);
lean_dec_ref(v___y_4292_);
if (v_isExporting_4299_ == 0)
{
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
v___y_4264_ = v___y_4290_;
v___y_4265_ = v___y_4294_;
v___y_4266_ = v___y_4295_;
v___y_4267_ = v___y_4296_;
goto v___jp_4263_;
}
else
{
if (v___y_4291_ == 0)
{
lean_dec_ref(v___y_4294_);
lean_dec_ref(v___y_4290_);
v___y_4281_ = v___y_4288_;
v___y_4282_ = v___y_4289_;
v___y_4283_ = v___y_4295_;
v___y_4284_ = v___y_4296_;
goto v___jp_4280_;
}
else
{
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
v___y_4264_ = v___y_4290_;
v___y_4265_ = v___y_4294_;
v___y_4266_ = v___y_4295_;
v___y_4267_ = v___y_4296_;
goto v___jp_4263_;
}
}
}
}
v___jp_4300_:
{
lean_object* v___x_4304_; double v___x_4305_; double v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; 
v___x_4304_ = lean_io_get_num_heartbeats();
v___x_4305_ = lean_float_of_nat(v___y_4301_);
v___x_4306_ = lean_float_of_nat(v___x_4304_);
v___x_4307_ = lean_box_float(v___x_4305_);
v___x_4308_ = lean_box_float(v___x_4306_);
v___x_4309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4309_, 0, v___x_4307_);
lean_ctor_set(v___x_4309_, 1, v___x_4308_);
v___x_4310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4310_, 0, v_a_4303_);
lean_ctor_set(v___x_4310_, 1, v___x_4309_);
v___x_4311_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3968_, v_hasTrace_3834_, v___x_4196_, v_options_3832_, v___x_4198_, v___y_4302_, v___f_4195_, v___x_4310_, v_a_3776_, v_a_3777_);
return v___x_4311_;
}
v___jp_4312_:
{
if (lean_obj_tag(v___y_4315_) == 0)
{
lean_object* v_a_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4323_; 
v_a_4316_ = lean_ctor_get(v___y_4315_, 0);
v_isSharedCheck_4323_ = !lean_is_exclusive(v___y_4315_);
if (v_isSharedCheck_4323_ == 0)
{
v___x_4318_ = v___y_4315_;
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_a_4316_);
lean_dec(v___y_4315_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v___x_4321_; 
if (v_isShared_4319_ == 0)
{
lean_ctor_set_tag(v___x_4318_, 1);
v___x_4321_ = v___x_4318_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_a_4316_);
v___x_4321_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
v___y_4301_ = v___y_4313_;
v___y_4302_ = v___y_4314_;
v_a_4303_ = v___x_4321_;
goto v___jp_4300_;
}
}
}
else
{
lean_object* v_a_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4331_; 
v_a_4324_ = lean_ctor_get(v___y_4315_, 0);
v_isSharedCheck_4331_ = !lean_is_exclusive(v___y_4315_);
if (v_isSharedCheck_4331_ == 0)
{
v___x_4326_ = v___y_4315_;
v_isShared_4327_ = v_isSharedCheck_4331_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_a_4324_);
lean_dec(v___y_4315_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4331_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v___x_4329_; 
if (v_isShared_4327_ == 0)
{
lean_ctor_set_tag(v___x_4326_, 0);
v___x_4329_ = v___x_4326_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v_a_4324_);
v___x_4329_ = v_reuseFailAlloc_4330_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
v___y_4301_ = v___y_4313_;
v___y_4302_ = v___y_4314_;
v_a_4303_ = v___x_4329_;
goto v___jp_4300_;
}
}
}
}
v___jp_4332_:
{
lean_object* v___x_4337_; lean_object* v___x_4338_; 
v___x_4337_ = lean_box(0);
lean_inc(v_a_3777_);
lean_inc_ref(v_a_3776_);
v___x_4338_ = lean_apply_5(v___y_4333_, v___x_4337_, v___y_4335_, v_a_3776_, v_a_3777_, lean_box(0));
v___y_4313_ = v___y_4334_;
v___y_4314_ = v___y_4336_;
v___y_4315_ = v___x_4338_;
goto v___jp_4312_;
}
v___jp_4339_:
{
lean_object* v___x_4344_; lean_object* v___x_4345_; 
v___x_4344_ = lean_box(0);
lean_inc(v_a_3777_);
lean_inc_ref(v_a_3776_);
v___x_4345_ = lean_apply_5(v___y_4342_, v___x_4344_, v___y_4341_, v_a_3776_, v_a_3777_, lean_box(0));
v___y_4313_ = v___y_4340_;
v___y_4314_ = v___y_4343_;
v___y_4315_ = v___x_4345_;
goto v___jp_4312_;
}
v___jp_4346_:
{
lean_object* v___x_4347_; lean_object* v_a_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4501_; 
v___x_4347_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v_a_3777_);
v_a_4348_ = lean_ctor_get(v___x_4347_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4347_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4350_ = v___x_4347_;
v_isShared_4351_ = v_isSharedCheck_4501_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_a_4348_);
lean_dec(v___x_4347_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4501_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4352_; uint8_t v___x_4353_; 
v___x_4352_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4353_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3832_, v___x_4352_);
if (v___x_4353_ == 0)
{
lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v_env_4356_; lean_object* v_nextMacroScope_4357_; lean_object* v_ngen_4358_; lean_object* v_auxDeclNGen_4359_; lean_object* v_traceState_4360_; lean_object* v_recordedDeps_4361_; lean_object* v_messages_4362_; lean_object* v_infoState_4363_; lean_object* v_snapshotTasks_4364_; lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4414_; 
v___x_4354_ = lean_io_mono_nanos_now();
v___x_4355_ = lean_st_ref_take(v_a_3777_);
v_env_4356_ = lean_ctor_get(v___x_4355_, 0);
v_nextMacroScope_4357_ = lean_ctor_get(v___x_4355_, 1);
v_ngen_4358_ = lean_ctor_get(v___x_4355_, 2);
v_auxDeclNGen_4359_ = lean_ctor_get(v___x_4355_, 3);
v_traceState_4360_ = lean_ctor_get(v___x_4355_, 4);
v_recordedDeps_4361_ = lean_ctor_get(v___x_4355_, 6);
v_messages_4362_ = lean_ctor_get(v___x_4355_, 7);
v_infoState_4363_ = lean_ctor_get(v___x_4355_, 8);
v_snapshotTasks_4364_ = lean_ctor_get(v___x_4355_, 9);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4414_ == 0)
{
lean_object* v_unused_4415_; 
v_unused_4415_ = lean_ctor_get(v___x_4355_, 5);
lean_dec(v_unused_4415_);
v___x_4366_ = v___x_4355_;
v_isShared_4367_ = v_isSharedCheck_4414_;
goto v_resetjp_4365_;
}
else
{
lean_inc(v_snapshotTasks_4364_);
lean_inc(v_infoState_4363_);
lean_inc(v_messages_4362_);
lean_inc(v_recordedDeps_4361_);
lean_inc(v_traceState_4360_);
lean_inc(v_auxDeclNGen_4359_);
lean_inc(v_ngen_4358_);
lean_inc(v_nextMacroScope_4357_);
lean_inc(v_env_4356_);
lean_dec(v___x_4355_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_4414_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4372_; 
lean_inc(v_decl_3774_);
v___x_4368_ = l_Lean_Declaration_getNames(v_decl_3774_);
v___x_4369_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4356_, v___x_4368_);
v___x_4370_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4367_ == 0)
{
lean_ctor_set(v___x_4366_, 5, v___x_4370_);
lean_ctor_set(v___x_4366_, 0, v___x_4369_);
v___x_4372_ = v___x_4366_;
goto v_reusejp_4371_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v___x_4369_);
lean_ctor_set(v_reuseFailAlloc_4413_, 1, v_nextMacroScope_4357_);
lean_ctor_set(v_reuseFailAlloc_4413_, 2, v_ngen_4358_);
lean_ctor_set(v_reuseFailAlloc_4413_, 3, v_auxDeclNGen_4359_);
lean_ctor_set(v_reuseFailAlloc_4413_, 4, v_traceState_4360_);
lean_ctor_set(v_reuseFailAlloc_4413_, 5, v___x_4370_);
lean_ctor_set(v_reuseFailAlloc_4413_, 6, v_recordedDeps_4361_);
lean_ctor_set(v_reuseFailAlloc_4413_, 7, v_messages_4362_);
lean_ctor_set(v_reuseFailAlloc_4413_, 8, v_infoState_4363_);
lean_ctor_set(v_reuseFailAlloc_4413_, 9, v_snapshotTasks_4364_);
v___x_4372_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4371_;
}
v_reusejp_4371_:
{
lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___f_4377_; 
v___x_4373_ = lean_st_ref_put(v_a_3777_, v___x_4372_);
v___x_4374_ = lean_box(0);
v___x_4375_ = lean_box(v_hasTrace_3834_);
v___x_4376_ = lean_box(v___x_4353_);
lean_inc(v_decl_3774_);
v___f_4377_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed), 11, 6);
lean_closure_set(v___f_4377_, 0, v_decl_3774_);
lean_closure_set(v___f_4377_, 1, v___x_4375_);
lean_closure_set(v___f_4377_, 2, v___x_4376_);
lean_closure_set(v___f_4377_, 3, v___x_4370_);
lean_closure_set(v___f_4377_, 4, v_cls_3968_);
lean_closure_set(v___f_4377_, 5, v___x_4374_);
switch(lean_obj_tag(v_decl_3774_))
{
case 2:
{
lean_object* v_val_4378_; lean_object* v___f_4379_; lean_object* v___x_4380_; lean_object* v___f_4381_; lean_object* v___x_4382_; 
lean_del_object(v___x_4350_);
v_val_4378_ = lean_ctor_get(v_decl_3774_, 0);
lean_inc_ref_n(v_val_4378_, 3);
lean_dec_ref_known(v_decl_3774_, 1);
v___f_4379_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed), 7, 2);
lean_closure_set(v___f_4379_, 0, v_val_4378_);
lean_closure_set(v___f_4379_, 1, v___f_4377_);
v___x_4380_ = lean_box(v___x_4353_);
lean_inc_ref(v___f_4379_);
v___f_4381_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed), 7, 3);
lean_closure_set(v___f_4381_, 0, v_val_4378_);
lean_closure_set(v___f_4381_, 1, v___x_4380_);
lean_closure_set(v___f_4381_, 2, v___f_4379_);
v___x_4382_ = lean_st_ref_get(v_a_3777_);
if (v_forceExpose_3775_ == 0)
{
lean_object* v_env_4383_; 
v_env_4383_ = lean_ctor_get(v___x_4382_, 0);
lean_inc_ref(v_env_4383_);
lean_dec(v___x_4382_);
v___y_4242_ = v___f_4381_;
v___y_4243_ = v___x_4374_;
v___y_4244_ = v___f_4379_;
v___y_4245_ = v_val_4378_;
v___y_4246_ = v_env_4383_;
v___y_4247_ = v___x_4354_;
v___y_4248_ = v_a_4348_;
goto v___jp_4241_;
}
else
{
if (v___x_4353_ == 0)
{
lean_dec(v___x_4382_);
lean_dec_ref(v___f_4381_);
lean_dec_ref(v_val_4378_);
v___y_4235_ = v___x_4374_;
v___y_4236_ = v___f_4379_;
v___y_4237_ = v___x_4354_;
v___y_4238_ = v_a_4348_;
goto v___jp_4234_;
}
else
{
lean_object* v_env_4384_; 
v_env_4384_ = lean_ctor_get(v___x_4382_, 0);
lean_inc_ref(v_env_4384_);
lean_dec(v___x_4382_);
v___y_4242_ = v___f_4381_;
v___y_4243_ = v___x_4374_;
v___y_4244_ = v___f_4379_;
v___y_4245_ = v_val_4378_;
v___y_4246_ = v_env_4384_;
v___y_4247_ = v___x_4354_;
v___y_4248_ = v_a_4348_;
goto v___jp_4241_;
}
}
}
case 1:
{
lean_object* v_val_4385_; lean_object* v___x_4386_; 
lean_del_object(v___x_4350_);
v_val_4385_ = lean_ctor_get(v_decl_3774_, 0);
lean_inc_ref(v_val_4385_);
lean_dec_ref_known(v_decl_3774_, 1);
v___x_4386_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v___f_4377_, v___x_4353_, v_cls_3968_, v___x_4374_, v_forceExpose_3775_, v_val_4385_, v_a_3776_, v_a_3777_);
v___y_4215_ = v___x_4354_;
v___y_4216_ = v_a_4348_;
v___y_4217_ = v___x_4386_;
goto v___jp_4214_;
}
case 5:
{
lean_object* v_defns_4387_; 
lean_del_object(v___x_4350_);
v_defns_4387_ = lean_ctor_get(v_decl_3774_, 0);
if (lean_obj_tag(v_defns_4387_) == 1)
{
lean_object* v_tail_4388_; 
v_tail_4388_ = lean_ctor_get(v_defns_4387_, 1);
if (lean_obj_tag(v_tail_4388_) == 0)
{
lean_object* v_head_4389_; lean_object* v___x_4390_; 
lean_inc_ref(v_defns_4387_);
lean_dec_ref_known(v_decl_3774_, 1);
v_head_4389_ = lean_ctor_get(v_defns_4387_, 0);
lean_inc(v_head_4389_);
lean_dec_ref_known(v_defns_4387_, 2);
v___x_4390_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v___f_4377_, v___x_4353_, v_cls_3968_, v___x_4374_, v_forceExpose_3775_, v_head_4389_, v_a_3776_, v_a_3777_);
v___y_4215_ = v___x_4354_;
v___y_4216_ = v_a_4348_;
v___y_4217_ = v___x_4390_;
goto v___jp_4214_;
}
else
{
lean_object* v___x_4391_; 
lean_dec_ref(v___f_4377_);
lean_inc_ref(v_decl_3774_);
v___x_4391_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3774_, v_cls_3968_, v_decl_3774_, v_a_3776_, v_a_3777_);
lean_dec_ref_known(v_decl_3774_, 1);
v___y_4215_ = v___x_4354_;
v___y_4216_ = v_a_4348_;
v___y_4217_ = v___x_4391_;
goto v___jp_4214_;
}
}
else
{
lean_object* v___x_4392_; 
lean_dec_ref(v___f_4377_);
lean_inc_ref(v_decl_3774_);
v___x_4392_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3774_, v_cls_3968_, v_decl_3774_, v_a_3776_, v_a_3777_);
lean_dec_ref_known(v_decl_3774_, 1);
v___y_4215_ = v___x_4354_;
v___y_4216_ = v_a_4348_;
v___y_4217_ = v___x_4392_;
goto v___jp_4214_;
}
}
case 3:
{
lean_object* v_val_4393_; lean_object* v___f_4394_; lean_object* v___f_4395_; lean_object* v___x_4396_; lean_object* v_env_4397_; lean_object* v___x_4398_; 
lean_del_object(v___x_4350_);
v_val_4393_ = lean_ctor_get(v_decl_3774_, 0);
lean_inc_ref_n(v_val_4393_, 3);
lean_dec_ref_known(v_decl_3774_, 1);
v___f_4394_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed), 7, 2);
lean_closure_set(v___f_4394_, 0, v_val_4393_);
lean_closure_set(v___f_4394_, 1, v___f_4377_);
lean_inc_ref(v___f_4394_);
v___f_4395_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10___boxed), 6, 2);
lean_closure_set(v___f_4395_, 0, v_val_4393_);
lean_closure_set(v___f_4395_, 1, v___f_4394_);
v___x_4396_ = lean_st_ref_get(v_a_3777_);
v_env_4397_ = lean_ctor_get(v___x_4396_, 0);
lean_inc_ref(v_env_4397_);
lean_dec(v___x_4396_);
v___x_4398_ = lean_st_ref_get(v_a_3777_);
if (v_forceExpose_3775_ == 0)
{
lean_object* v_env_4399_; 
v_env_4399_ = lean_ctor_get(v___x_4398_, 0);
lean_inc_ref(v_env_4399_);
lean_dec(v___x_4398_);
v___y_4288_ = v___f_4394_;
v___y_4289_ = v___x_4374_;
v___y_4290_ = v___f_4395_;
v___y_4291_ = v___x_4353_;
v___y_4292_ = v_env_4399_;
v___y_4293_ = v_env_4397_;
v___y_4294_ = v_val_4393_;
v___y_4295_ = v___x_4354_;
v___y_4296_ = v_a_4348_;
goto v___jp_4287_;
}
else
{
if (v___x_4353_ == 0)
{
lean_dec(v___x_4398_);
lean_dec_ref(v_env_4397_);
lean_dec_ref(v___f_4395_);
lean_dec_ref(v_val_4393_);
v___y_4281_ = v___f_4394_;
v___y_4282_ = v___x_4374_;
v___y_4283_ = v___x_4354_;
v___y_4284_ = v_a_4348_;
goto v___jp_4280_;
}
else
{
lean_object* v_env_4400_; 
v_env_4400_ = lean_ctor_get(v___x_4398_, 0);
lean_inc_ref(v_env_4400_);
lean_dec(v___x_4398_);
v___y_4288_ = v___f_4394_;
v___y_4289_ = v___x_4374_;
v___y_4290_ = v___f_4395_;
v___y_4291_ = v___x_4353_;
v___y_4292_ = v_env_4400_;
v___y_4293_ = v_env_4397_;
v___y_4294_ = v_val_4393_;
v___y_4295_ = v___x_4354_;
v___y_4296_ = v_a_4348_;
goto v___jp_4287_;
}
}
}
case 0:
{
lean_object* v_val_4401_; lean_object* v_toConstantVal_4402_; lean_object* v_name_4403_; lean_object* v___x_4405_; 
lean_dec_ref(v___f_4377_);
v_val_4401_ = lean_ctor_get(v_decl_3774_, 0);
v_toConstantVal_4402_ = lean_ctor_get(v_val_4401_, 0);
v_name_4403_ = lean_ctor_get(v_toConstantVal_4402_, 0);
lean_inc_ref(v_val_4401_);
if (v_isShared_4351_ == 0)
{
lean_ctor_set(v___x_4350_, 0, v_val_4401_);
v___x_4405_ = v___x_4350_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v_val_4401_);
v___x_4405_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
uint8_t v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; 
v___x_4406_ = 2;
v___x_4407_ = lean_box(v___x_4406_);
v___x_4408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4408_, 0, v___x_4405_);
lean_ctor_set(v___x_4408_, 1, v___x_4407_);
lean_inc(v_name_4403_);
v___x_4409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4409_, 0, v_name_4403_);
lean_ctor_set(v___x_4409_, 1, v___x_4408_);
v___x_4410_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_decl_3774_, v_hasTrace_3834_, v___x_4353_, v___x_4370_, v_cls_3968_, v___x_4374_, v___x_4409_, v___x_4374_, v_a_3776_, v_a_3777_);
v___y_4215_ = v___x_4354_;
v___y_4216_ = v_a_4348_;
v___y_4217_ = v___x_4410_;
goto v___jp_4214_;
}
}
default: 
{
lean_object* v___x_4412_; 
lean_dec_ref(v___f_4377_);
lean_del_object(v___x_4350_);
lean_inc(v_decl_3774_);
v___x_4412_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3774_, v_cls_3968_, v_decl_3774_, v_a_3776_, v_a_3777_);
lean_dec(v_decl_3774_);
v___y_4215_ = v___x_4354_;
v___y_4216_ = v_a_4348_;
v___y_4217_ = v___x_4412_;
goto v___jp_4214_;
}
}
}
}
}
else
{
lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v_env_4418_; lean_object* v_nextMacroScope_4419_; lean_object* v_ngen_4420_; lean_object* v_auxDeclNGen_4421_; lean_object* v_traceState_4422_; lean_object* v_recordedDeps_4423_; lean_object* v_messages_4424_; lean_object* v_infoState_4425_; lean_object* v_snapshotTasks_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4499_; 
v___x_4416_ = lean_io_get_num_heartbeats();
v___x_4417_ = lean_st_ref_take(v_a_3777_);
v_env_4418_ = lean_ctor_get(v___x_4417_, 0);
v_nextMacroScope_4419_ = lean_ctor_get(v___x_4417_, 1);
v_ngen_4420_ = lean_ctor_get(v___x_4417_, 2);
v_auxDeclNGen_4421_ = lean_ctor_get(v___x_4417_, 3);
v_traceState_4422_ = lean_ctor_get(v___x_4417_, 4);
v_recordedDeps_4423_ = lean_ctor_get(v___x_4417_, 6);
v_messages_4424_ = lean_ctor_get(v___x_4417_, 7);
v_infoState_4425_ = lean_ctor_get(v___x_4417_, 8);
v_snapshotTasks_4426_ = lean_ctor_get(v___x_4417_, 9);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4417_);
if (v_isSharedCheck_4499_ == 0)
{
lean_object* v_unused_4500_; 
v_unused_4500_ = lean_ctor_get(v___x_4417_, 5);
lean_dec(v_unused_4500_);
v___x_4428_ = v___x_4417_;
v_isShared_4429_ = v_isSharedCheck_4499_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_snapshotTasks_4426_);
lean_inc(v_infoState_4425_);
lean_inc(v_messages_4424_);
lean_inc(v_recordedDeps_4423_);
lean_inc(v_traceState_4422_);
lean_inc(v_auxDeclNGen_4421_);
lean_inc(v_ngen_4420_);
lean_inc(v_nextMacroScope_4419_);
lean_inc(v_env_4418_);
lean_dec(v___x_4417_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4499_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4434_; 
lean_inc(v_decl_3774_);
v___x_4430_ = l_Lean_Declaration_getNames(v_decl_3774_);
v___x_4431_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4418_, v___x_4430_);
v___x_4432_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4429_ == 0)
{
lean_ctor_set(v___x_4428_, 5, v___x_4432_);
lean_ctor_set(v___x_4428_, 0, v___x_4431_);
v___x_4434_ = v___x_4428_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v___x_4431_);
lean_ctor_set(v_reuseFailAlloc_4498_, 1, v_nextMacroScope_4419_);
lean_ctor_set(v_reuseFailAlloc_4498_, 2, v_ngen_4420_);
lean_ctor_set(v_reuseFailAlloc_4498_, 3, v_auxDeclNGen_4421_);
lean_ctor_set(v_reuseFailAlloc_4498_, 4, v_traceState_4422_);
lean_ctor_set(v_reuseFailAlloc_4498_, 5, v___x_4432_);
lean_ctor_set(v_reuseFailAlloc_4498_, 6, v_recordedDeps_4423_);
lean_ctor_set(v_reuseFailAlloc_4498_, 7, v_messages_4424_);
lean_ctor_set(v_reuseFailAlloc_4498_, 8, v_infoState_4425_);
lean_ctor_set(v_reuseFailAlloc_4498_, 9, v_snapshotTasks_4426_);
v___x_4434_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___f_4438_; 
v___x_4435_ = lean_st_ref_put(v_a_3777_, v___x_4434_);
v___x_4436_ = lean_box(0);
v___x_4437_ = lean_box(v___x_4353_);
lean_inc(v_decl_3774_);
v___f_4438_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14___boxed), 10, 5);
lean_closure_set(v___f_4438_, 0, v_decl_3774_);
lean_closure_set(v___f_4438_, 1, v___x_4437_);
lean_closure_set(v___f_4438_, 2, v_cls_3968_);
lean_closure_set(v___f_4438_, 3, v___x_4432_);
lean_closure_set(v___f_4438_, 4, v___x_4436_);
switch(lean_obj_tag(v_decl_3774_))
{
case 2:
{
lean_object* v_val_4439_; lean_object* v___f_4440_; lean_object* v___x_4441_; 
lean_del_object(v___x_4350_);
v_val_4439_ = lean_ctor_get(v_decl_3774_, 0);
lean_inc_ref_n(v_val_4439_, 2);
lean_dec_ref_known(v_decl_3774_, 1);
v___f_4440_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed), 7, 2);
lean_closure_set(v___f_4440_, 0, v_val_4439_);
lean_closure_set(v___f_4440_, 1, v___f_4438_);
v___x_4441_ = lean_st_ref_get(v_a_3777_);
if (v_forceExpose_3775_ == 0)
{
if (v___x_4353_ == 0)
{
lean_dec(v___x_4441_);
lean_dec_ref(v_val_4439_);
v___y_4340_ = v___x_4416_;
v___y_4341_ = v___x_4436_;
v___y_4342_ = v___f_4440_;
v___y_4343_ = v_a_4348_;
goto v___jp_4339_;
}
else
{
lean_object* v_env_4442_; lean_object* v___x_4443_; uint8_t v_isModule_4444_; 
v_env_4442_ = lean_ctor_get(v___x_4441_, 0);
lean_inc_ref(v_env_4442_);
lean_dec(v___x_4441_);
v___x_4443_ = l_Lean_Environment_header(v_env_4442_);
lean_dec_ref(v_env_4442_);
v_isModule_4444_ = lean_ctor_get_uint8(v___x_4443_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4443_);
if (v_isModule_4444_ == 0)
{
lean_dec_ref(v_val_4439_);
v___y_4340_ = v___x_4416_;
v___y_4341_ = v___x_4436_;
v___y_4342_ = v___f_4440_;
v___y_4343_ = v_a_4348_;
goto v___jp_4339_;
}
else
{
if (v___x_4198_ == 0)
{
lean_object* v___x_4445_; lean_object* v___x_4446_; 
v___x_4445_ = lean_box(0);
v___x_4446_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_val_4439_, v___f_4440_, v___x_4445_, v_a_3776_, v_a_3777_);
lean_dec_ref(v_val_4439_);
v___y_4313_ = v___x_4416_;
v___y_4314_ = v_a_4348_;
v___y_4315_ = v___x_4446_;
goto v___jp_4312_;
}
else
{
lean_object* v_toConstantVal_4447_; lean_object* v_name_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; 
v_toConstantVal_4447_ = lean_ctor_get(v_val_4439_, 0);
v_name_4448_ = lean_ctor_get(v_toConstantVal_4447_, 0);
v___x_4449_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4448_);
v___x_4450_ = l_Lean_MessageData_ofName(v_name_4448_);
v___x_4451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4451_, 0, v___x_4449_);
lean_ctor_set(v___x_4451_, 1, v___x_4450_);
v___x_4452_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4453_, 0, v___x_4451_);
lean_ctor_set(v___x_4453_, 1, v___x_4452_);
v___x_4454_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3968_, v___x_4453_, v_a_3776_, v_a_3777_);
if (lean_obj_tag(v___x_4454_) == 0)
{
lean_object* v_a_4455_; lean_object* v___x_4456_; 
v_a_4455_ = lean_ctor_get(v___x_4454_, 0);
lean_inc(v_a_4455_);
lean_dec_ref_known(v___x_4454_, 1);
v___x_4456_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_val_4439_, v___f_4440_, v_a_4455_, v_a_3776_, v_a_3777_);
lean_dec_ref(v_val_4439_);
v___y_4313_ = v___x_4416_;
v___y_4314_ = v_a_4348_;
v___y_4315_ = v___x_4456_;
goto v___jp_4312_;
}
else
{
lean_dec_ref(v___f_4440_);
lean_dec_ref(v_val_4439_);
v___y_4313_ = v___x_4416_;
v___y_4314_ = v_a_4348_;
v___y_4315_ = v___x_4454_;
goto v___jp_4312_;
}
}
}
}
}
else
{
lean_dec(v___x_4441_);
lean_dec_ref(v_val_4439_);
v___y_4340_ = v___x_4416_;
v___y_4341_ = v___x_4436_;
v___y_4342_ = v___f_4440_;
v___y_4343_ = v_a_4348_;
goto v___jp_4339_;
}
}
case 1:
{
lean_object* v_val_4457_; lean_object* v___x_4458_; 
lean_del_object(v___x_4350_);
v_val_4457_ = lean_ctor_get(v_decl_3774_, 0);
lean_inc_ref(v_val_4457_);
lean_dec_ref_known(v_decl_3774_, 1);
v___x_4458_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(v___f_4438_, v_forceExpose_3775_, v___x_4353_, v___x_4436_, v_cls_3968_, v_val_4457_, v_a_3776_, v_a_3777_);
v___y_4313_ = v___x_4416_;
v___y_4314_ = v_a_4348_;
v___y_4315_ = v___x_4458_;
goto v___jp_4312_;
}
case 5:
{
lean_object* v_defns_4459_; 
lean_del_object(v___x_4350_);
v_defns_4459_ = lean_ctor_get(v_decl_3774_, 0);
if (lean_obj_tag(v_defns_4459_) == 1)
{
lean_object* v_tail_4460_; 
v_tail_4460_ = lean_ctor_get(v_defns_4459_, 1);
if (lean_obj_tag(v_tail_4460_) == 0)
{
lean_object* v_head_4461_; lean_object* v___x_4462_; 
lean_inc_ref(v_defns_4459_);
lean_dec_ref_known(v_decl_3774_, 1);
v_head_4461_ = lean_ctor_get(v_defns_4459_, 0);
lean_inc(v_head_4461_);
lean_dec_ref_known(v_defns_4459_, 2);
v___x_4462_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(v___f_4438_, v_forceExpose_3775_, v___x_4353_, v___x_4436_, v_cls_3968_, v_head_4461_, v_a_3776_, v_a_3777_);
v___y_4313_ = v___x_4416_;
v___y_4314_ = v_a_4348_;
v___y_4315_ = v___x_4462_;
goto v___jp_4312_;
}
else
{
lean_object* v___x_4463_; 
lean_dec_ref(v___f_4438_);
lean_inc_ref(v_decl_3774_);
v___x_4463_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3774_, v_cls_3968_, v_decl_3774_, v_a_3776_, v_a_3777_);
lean_dec_ref_known(v_decl_3774_, 1);
v___y_4313_ = v___x_4416_;
v___y_4314_ = v_a_4348_;
v___y_4315_ = v___x_4463_;
goto v___jp_4312_;
}
}
else
{
lean_object* v___x_4464_; 
lean_dec_ref(v___f_4438_);
lean_inc_ref(v_decl_3774_);
v___x_4464_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3774_, v_cls_3968_, v_decl_3774_, v_a_3776_, v_a_3777_);
lean_dec_ref_known(v_decl_3774_, 1);
v___y_4313_ = v___x_4416_;
v___y_4314_ = v_a_4348_;
v___y_4315_ = v___x_4464_;
goto v___jp_4312_;
}
}
case 3:
{
lean_object* v_val_4465_; lean_object* v___f_4466_; lean_object* v___x_4467_; lean_object* v_env_4468_; lean_object* v___x_4469_; 
lean_del_object(v___x_4350_);
v_val_4465_ = lean_ctor_get(v_decl_3774_, 0);
lean_inc_ref_n(v_val_4465_, 2);
lean_dec_ref_known(v_decl_3774_, 1);
v___f_4466_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed), 7, 2);
lean_closure_set(v___f_4466_, 0, v_val_4465_);
lean_closure_set(v___f_4466_, 1, v___f_4438_);
v___x_4467_ = lean_st_ref_get(v_a_3777_);
v_env_4468_ = lean_ctor_get(v___x_4467_, 0);
lean_inc_ref(v_env_4468_);
lean_dec(v___x_4467_);
v___x_4469_ = lean_st_ref_get(v_a_3777_);
if (v_forceExpose_3775_ == 0)
{
if (v___x_4353_ == 0)
{
lean_dec(v___x_4469_);
lean_dec_ref(v_env_4468_);
lean_dec_ref(v_val_4465_);
v___y_4333_ = v___f_4466_;
v___y_4334_ = v___x_4416_;
v___y_4335_ = v___x_4436_;
v___y_4336_ = v_a_4348_;
goto v___jp_4332_;
}
else
{
lean_object* v_env_4470_; lean_object* v___x_4471_; uint8_t v_isModule_4472_; 
v_env_4470_ = lean_ctor_get(v___x_4469_, 0);
lean_inc_ref(v_env_4470_);
lean_dec(v___x_4469_);
v___x_4471_ = l_Lean_Environment_header(v_env_4468_);
lean_dec_ref(v_env_4468_);
v_isModule_4472_ = lean_ctor_get_uint8(v___x_4471_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4471_);
if (v_isModule_4472_ == 0)
{
lean_dec_ref(v_env_4470_);
lean_dec_ref(v_val_4465_);
v___y_4333_ = v___f_4466_;
v___y_4334_ = v___x_4416_;
v___y_4335_ = v___x_4436_;
v___y_4336_ = v_a_4348_;
goto v___jp_4332_;
}
else
{
uint8_t v_isExporting_4473_; 
v_isExporting_4473_ = lean_ctor_get_uint8(v_env_4470_, sizeof(void*)*13);
lean_dec_ref(v_env_4470_);
if (v_isExporting_4473_ == 0)
{
if (v___x_4198_ == 0)
{
lean_object* v___x_4474_; lean_object* v___x_4475_; 
v___x_4474_ = lean_box(0);
v___x_4475_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_4465_, v___f_4466_, v___x_4474_, v_a_3776_, v_a_3777_);
lean_dec_ref(v_val_4465_);
v___y_4313_ = v___x_4416_;
v___y_4314_ = v_a_4348_;
v___y_4315_ = v___x_4475_;
goto v___jp_4312_;
}
else
{
lean_object* v_toConstantVal_4476_; lean_object* v_name_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; 
v_toConstantVal_4476_ = lean_ctor_get(v_val_4465_, 0);
v_name_4477_ = lean_ctor_get(v_toConstantVal_4476_, 0);
v___x_4478_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4477_);
v___x_4479_ = l_Lean_MessageData_ofName(v_name_4477_);
v___x_4480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4480_, 0, v___x_4478_);
lean_ctor_set(v___x_4480_, 1, v___x_4479_);
v___x_4481_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4482_, 0, v___x_4480_);
lean_ctor_set(v___x_4482_, 1, v___x_4481_);
v___x_4483_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3968_, v___x_4482_, v_a_3776_, v_a_3777_);
if (lean_obj_tag(v___x_4483_) == 0)
{
lean_object* v_a_4484_; lean_object* v___x_4485_; 
v_a_4484_ = lean_ctor_get(v___x_4483_, 0);
lean_inc(v_a_4484_);
lean_dec_ref_known(v___x_4483_, 1);
v___x_4485_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_4465_, v___f_4466_, v_a_4484_, v_a_3776_, v_a_3777_);
lean_dec_ref(v_val_4465_);
v___y_4313_ = v___x_4416_;
v___y_4314_ = v_a_4348_;
v___y_4315_ = v___x_4485_;
goto v___jp_4312_;
}
else
{
lean_dec_ref(v___f_4466_);
lean_dec_ref(v_val_4465_);
v___y_4313_ = v___x_4416_;
v___y_4314_ = v_a_4348_;
v___y_4315_ = v___x_4483_;
goto v___jp_4312_;
}
}
}
else
{
lean_dec_ref(v_val_4465_);
v___y_4333_ = v___f_4466_;
v___y_4334_ = v___x_4416_;
v___y_4335_ = v___x_4436_;
v___y_4336_ = v_a_4348_;
goto v___jp_4332_;
}
}
}
}
else
{
lean_dec(v___x_4469_);
lean_dec_ref(v_env_4468_);
lean_dec_ref(v_val_4465_);
v___y_4333_ = v___f_4466_;
v___y_4334_ = v___x_4416_;
v___y_4335_ = v___x_4436_;
v___y_4336_ = v_a_4348_;
goto v___jp_4332_;
}
}
case 0:
{
lean_object* v_val_4486_; lean_object* v_toConstantVal_4487_; lean_object* v_name_4488_; lean_object* v___x_4490_; 
lean_dec_ref(v___f_4438_);
v_val_4486_ = lean_ctor_get(v_decl_3774_, 0);
v_toConstantVal_4487_ = lean_ctor_get(v_val_4486_, 0);
v_name_4488_ = lean_ctor_get(v_toConstantVal_4487_, 0);
lean_inc_ref(v_val_4486_);
if (v_isShared_4351_ == 0)
{
lean_ctor_set(v___x_4350_, 0, v_val_4486_);
v___x_4490_ = v___x_4350_;
goto v_reusejp_4489_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_val_4486_);
v___x_4490_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4489_;
}
v_reusejp_4489_:
{
uint8_t v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; 
v___x_4491_ = 2;
v___x_4492_ = lean_box(v___x_4491_);
v___x_4493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4493_, 0, v___x_4490_);
lean_ctor_set(v___x_4493_, 1, v___x_4492_);
lean_inc(v_name_4488_);
v___x_4494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4494_, 0, v_name_4488_);
lean_ctor_set(v___x_4494_, 1, v___x_4493_);
v___x_4495_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(v_decl_3774_, v___x_4353_, v_cls_3968_, v___x_4432_, v___x_4436_, v___x_4494_, v___x_4436_, v_a_3776_, v_a_3777_);
v___y_4313_ = v___x_4416_;
v___y_4314_ = v_a_4348_;
v___y_4315_ = v___x_4495_;
goto v___jp_4312_;
}
}
default: 
{
lean_object* v___x_4497_; 
lean_dec_ref(v___f_4438_);
lean_del_object(v___x_4350_);
lean_inc(v_decl_3774_);
v___x_4497_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3774_, v_cls_3968_, v_decl_3774_, v_a_3776_, v_a_3777_);
lean_dec(v_decl_3774_);
v___y_4313_ = v___x_4416_;
v___y_4314_ = v_a_4348_;
v___y_4315_ = v___x_4497_;
goto v___jp_4312_;
}
}
}
}
}
}
}
}
v___jp_3779_:
{
lean_object* v___x_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3790_; 
v___x_3783_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3781_, v___y_3780_);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3790_ == 0)
{
lean_object* v_unused_3791_; 
v_unused_3791_ = lean_ctor_get(v___x_3783_, 0);
lean_dec(v_unused_3791_);
v___x_3785_ = v___x_3783_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_dec(v___x_3783_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3788_; 
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 0, v_a_3782_);
v___x_3788_ = v___x_3785_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3782_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
v___jp_3792_:
{
lean_object* v___x_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3803_; 
v___x_3796_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3794_, v___y_3793_);
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3803_ == 0)
{
lean_object* v_unused_3804_; 
v_unused_3804_ = lean_ctor_get(v___x_3796_, 0);
lean_dec(v_unused_3804_);
v___x_3798_ = v___x_3796_;
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
else
{
lean_dec(v___x_3796_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v___x_3801_; 
if (v_isShared_3799_ == 0)
{
lean_ctor_set_tag(v___x_3798_, 1);
lean_ctor_set(v___x_3798_, 0, v_a_3795_);
v___x_3801_ = v___x_3798_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_a_3795_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
}
v___jp_3805_:
{
lean_object* v___x_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3816_; 
v___x_3809_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3807_, v___y_3806_);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3809_);
if (v_isSharedCheck_3816_ == 0)
{
lean_object* v_unused_3817_; 
v_unused_3817_ = lean_ctor_get(v___x_3809_, 0);
lean_dec(v_unused_3817_);
v___x_3811_ = v___x_3809_;
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
else
{
lean_dec(v___x_3809_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3814_; 
if (v_isShared_3812_ == 0)
{
lean_ctor_set(v___x_3811_, 0, v_a_3808_);
v___x_3814_ = v___x_3811_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_a_3808_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
v___jp_3818_:
{
lean_object* v___x_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3829_; 
v___x_3822_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3820_, v___y_3819_);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3829_ == 0)
{
lean_object* v_unused_3830_; 
v_unused_3830_ = lean_ctor_get(v___x_3822_, 0);
lean_dec(v_unused_3830_);
v___x_3824_ = v___x_3822_;
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
else
{
lean_dec(v___x_3822_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3827_; 
if (v_isShared_3825_ == 0)
{
lean_ctor_set_tag(v___x_3824_, 1);
lean_ctor_set(v___x_3824_, 0, v_a_3821_);
v___x_3827_ = v___x_3824_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_a_3821_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
}
v___jp_3835_:
{
lean_object* v___x_3848_; 
lean_inc_ref(v___y_3841_);
v___x_3848_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3842_, v___y_3841_, v___y_3843_, v___y_3847_);
if (lean_obj_tag(v___x_3848_) == 0)
{
lean_object* v___x_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3895_; 
lean_dec_ref_known(v___x_3848_, 1);
lean_dec(v___y_3838_);
lean_inc_ref(v___y_3840_);
v___x_3849_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3840_, v___y_3837_);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3895_ == 0)
{
lean_object* v_unused_3896_; 
v_unused_3896_ = lean_ctor_get(v___x_3849_, 0);
lean_dec(v_unused_3896_);
v___x_3851_ = v___x_3849_;
v_isShared_3852_ = v_isSharedCheck_3895_;
goto v_resetjp_3850_;
}
else
{
lean_dec(v___x_3849_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3895_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3853_; lean_object* v___x_3854_; uint8_t v___x_3855_; 
v___x_3853_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3845_);
v___x_3854_ = l_Lean_Elab_async;
v___x_3855_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_3853_, v___x_3854_);
lean_dec_ref(v___x_3853_);
if (v___x_3855_ == 0)
{
lean_object* v___x_3856_; lean_object* v_r_3857_; 
lean_del_object(v___x_3851_);
lean_dec_ref(v___y_3839_);
lean_dec_ref(v___y_3836_);
v___x_3856_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3841_, v___y_3837_);
lean_dec_ref(v___x_3856_);
v_r_3857_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3774_, v___y_3845_, v___y_3837_);
if (lean_obj_tag(v_r_3857_) == 0)
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3867_; 
v_a_3858_ = lean_ctor_get(v_r_3857_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v_r_3857_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3860_ = v_r_3857_;
v_isShared_3861_ = v_isSharedCheck_3867_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v_r_3857_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3867_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3863_; 
lean_inc(v_a_3858_);
if (v_isShared_3861_ == 0)
{
lean_ctor_set_tag(v___x_3860_, 1);
v___x_3863_ = v___x_3860_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3858_);
v___x_3863_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
lean_object* v___x_3864_; 
v___x_3864_ = lean_apply_2(v___y_3844_, v___x_3863_, lean_box(0));
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_dec_ref_known(v___x_3864_, 1);
v___y_3806_ = v___y_3837_;
v___y_3807_ = v___y_3840_;
v_a_3808_ = v_a_3858_;
goto v___jp_3805_;
}
else
{
lean_object* v_a_3865_; 
lean_dec(v_a_3858_);
v_a_3865_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_a_3865_);
lean_dec_ref_known(v___x_3864_, 1);
v___y_3819_ = v___y_3837_;
v___y_3820_ = v___y_3840_;
v_a_3821_ = v_a_3865_;
goto v___jp_3818_;
}
}
}
}
else
{
lean_object* v_a_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
v_a_3868_ = lean_ctor_get(v_r_3857_, 0);
lean_inc(v_a_3868_);
lean_dec_ref_known(v_r_3857_, 1);
v___x_3869_ = lean_box(0);
v___x_3870_ = lean_apply_2(v___y_3844_, v___x_3869_, lean_box(0));
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_dec_ref_known(v___x_3870_, 1);
v___y_3819_ = v___y_3837_;
v___y_3820_ = v___y_3840_;
v_a_3821_ = v_a_3868_;
goto v___jp_3818_;
}
else
{
lean_object* v_a_3871_; 
lean_dec(v_a_3868_);
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref_known(v___x_3870_, 1);
v___y_3819_ = v___y_3837_;
v___y_3820_ = v___y_3840_;
v_a_3821_ = v_a_3871_;
goto v___jp_3818_;
}
}
}
else
{
lean_object* v___x_3872_; lean_object* v___x_3874_; 
lean_dec_ref(v___y_3844_);
lean_dec_ref(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v_decl_3774_);
v___x_3872_ = l_IO_CancelToken_new();
if (v_isShared_3852_ == 0)
{
lean_ctor_set_tag(v___x_3851_, 1);
lean_ctor_set(v___x_3851_, 0, v___x_3872_);
v___x_3874_ = v___x_3851_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v___x_3872_);
v___x_3874_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3875_ = lean_unsigned_to_nat(0u);
v___x_3876_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_3877_ = l_Lean_Name_toString(v___x_3876_, v___y_3846_);
lean_inc_ref(v___x_3874_);
v___x_3878_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3836_, v___x_3874_, v___x_3877_, v___y_3845_, v___y_3837_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v_a_3879_; lean_object* v_checked_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
lean_inc(v_a_3879_);
lean_dec_ref_known(v___x_3878_, 1);
v_checked_3880_ = lean_ctor_get(v___y_3839_, 2);
lean_inc_ref(v_checked_3880_);
lean_dec_ref(v___y_3839_);
v___x_3881_ = lean_io_map_task(v_a_3879_, v_checked_3880_, v___x_3875_, v_hasTrace_3834_);
v___x_3882_ = lean_box(0);
v___x_3883_ = lean_box(2);
v___x_3884_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3882_);
lean_ctor_set(v___x_3884_, 1, v___x_3883_);
lean_ctor_set(v___x_3884_, 2, v___x_3874_);
lean_ctor_set(v___x_3884_, 3, v___x_3881_);
v___x_3885_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3884_, v___y_3837_);
return v___x_3885_;
}
else
{
lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3893_; 
lean_dec_ref(v___x_3874_);
lean_dec_ref(v___y_3839_);
v_a_3886_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3888_ = v___x_3878_;
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v___x_3878_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3891_; 
if (v_isShared_3889_ == 0)
{
v___x_3891_ = v___x_3888_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v_a_3886_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
return v___x_3891_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3908_; 
lean_dec_ref(v___y_3844_);
lean_dec_ref(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec_ref(v___y_3839_);
lean_dec_ref(v___y_3836_);
lean_dec(v_decl_3774_);
v_a_3897_ = lean_ctor_get(v___x_3848_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3848_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3899_ = v___x_3848_;
v_isShared_3900_ = v_isSharedCheck_3908_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3848_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3908_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3906_; 
v___x_3901_ = lean_io_error_to_string(v_a_3897_);
v___x_3902_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3901_);
v___x_3903_ = l_Lean_MessageData_ofFormat(v___x_3902_);
v___x_3904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3904_, 0, v___y_3838_);
lean_ctor_set(v___x_3904_, 1, v___x_3903_);
if (v_isShared_3900_ == 0)
{
lean_ctor_set(v___x_3899_, 0, v___x_3904_);
v___x_3906_ = v___x_3899_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v___x_3904_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
}
v___jp_3909_:
{
lean_object* v_ref_3918_; uint8_t v___x_3919_; lean_object* v___x_3920_; 
v_ref_3918_ = lean_ctor_get(v___y_3915_, 2);
v___x_3919_ = 1;
lean_inc_ref(v___y_3916_);
v___x_3920_ = l_Lean_Environment_addConstAsync(v___y_3916_, v___y_3913_, v___y_3912_, v___y_3917_, v_hasTrace_3834_, v___x_3919_);
if (lean_obj_tag(v___x_3920_) == 0)
{
lean_object* v_a_3921_; lean_object* v_mainEnv_3922_; lean_object* v_asyncEnv_3923_; lean_object* v___f_3924_; lean_object* v___f_3925_; lean_object* v___x_3926_; 
v_a_3921_ = lean_ctor_get(v___x_3920_, 0);
lean_inc_n(v_a_3921_, 3);
lean_dec_ref_known(v___x_3920_, 1);
v_mainEnv_3922_ = lean_ctor_get(v_a_3921_, 0);
lean_inc_ref(v_mainEnv_3922_);
v_asyncEnv_3923_ = lean_ctor_get(v_a_3921_, 1);
lean_inc_ref_n(v_asyncEnv_3923_, 2);
lean_inc(v_ref_3918_);
lean_inc(v___y_3910_);
v___f_3924_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3924_, 0, v___y_3910_);
lean_closure_set(v___f_3924_, 1, v_a_3921_);
lean_closure_set(v___f_3924_, 2, v_ref_3918_);
lean_inc(v_decl_3774_);
v___f_3925_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3925_, 0, v_a_3921_);
lean_closure_set(v___f_3925_, 1, v_asyncEnv_3923_);
lean_closure_set(v___f_3925_, 2, v_decl_3774_);
v___x_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3926_, 0, v___y_3914_);
if (lean_obj_tag(v___y_3911_) == 0)
{
lean_inc_ref(v___x_3926_);
lean_inc(v_ref_3918_);
v___y_3836_ = v___f_3925_;
v___y_3837_ = v___y_3910_;
v___y_3838_ = v_ref_3918_;
v___y_3839_ = v___y_3916_;
v___y_3840_ = v_mainEnv_3922_;
v___y_3841_ = v_asyncEnv_3923_;
v___y_3842_ = v_a_3921_;
v___y_3843_ = v___x_3926_;
v___y_3844_ = v___f_3924_;
v___y_3845_ = v___y_3915_;
v___y_3846_ = v___x_3919_;
v___y_3847_ = v___x_3926_;
goto v___jp_3835_;
}
else
{
lean_inc(v_ref_3918_);
v___y_3836_ = v___f_3925_;
v___y_3837_ = v___y_3910_;
v___y_3838_ = v_ref_3918_;
v___y_3839_ = v___y_3916_;
v___y_3840_ = v_mainEnv_3922_;
v___y_3841_ = v_asyncEnv_3923_;
v___y_3842_ = v_a_3921_;
v___y_3843_ = v___x_3926_;
v___y_3844_ = v___f_3924_;
v___y_3845_ = v___y_3915_;
v___y_3846_ = v___x_3919_;
v___y_3847_ = v___y_3911_;
goto v___jp_3835_;
}
}
else
{
lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3938_; 
lean_dec_ref(v___y_3916_);
lean_dec_ref(v___y_3914_);
lean_dec(v___y_3911_);
lean_dec(v_decl_3774_);
v_a_3927_ = lean_ctor_get(v___x_3920_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___x_3920_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3929_ = v___x_3920_;
v_isShared_3930_ = v_isSharedCheck_3938_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_a_3927_);
lean_dec(v___x_3920_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3938_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3936_; 
v___x_3931_ = lean_io_error_to_string(v_a_3927_);
v___x_3932_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3931_);
v___x_3933_ = l_Lean_MessageData_ofFormat(v___x_3932_);
lean_inc(v_ref_3918_);
v___x_3934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3934_, 0, v_ref_3918_);
lean_ctor_set(v___x_3934_, 1, v___x_3933_);
if (v_isShared_3930_ == 0)
{
lean_ctor_set(v___x_3929_, 0, v___x_3934_);
v___x_3936_ = v___x_3929_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v___x_3934_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
}
v___jp_3939_:
{
lean_object* v___x_3946_; 
v___x_3946_ = lean_st_ref_get(v___y_3945_);
if (lean_obj_tag(v_exportedInfo_x3f_3943_) == 0)
{
lean_object* v_env_3947_; lean_object* v___x_3948_; 
v_env_3947_ = lean_ctor_get(v___x_3946_, 0);
lean_inc_ref(v_env_3947_);
lean_dec(v___x_3946_);
v___x_3948_ = lean_box(0);
v___y_3910_ = v___y_3945_;
v___y_3911_ = v_exportedInfo_x3f_3943_;
v___y_3912_ = v___y_3940_;
v___y_3913_ = v___y_3941_;
v___y_3914_ = v___y_3942_;
v___y_3915_ = v___y_3944_;
v___y_3916_ = v_env_3947_;
v___y_3917_ = v___x_3948_;
goto v___jp_3909_;
}
else
{
lean_object* v_env_3949_; lean_object* v_val_3950_; uint8_t v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; 
v_env_3949_ = lean_ctor_get(v___x_3946_, 0);
lean_inc_ref(v_env_3949_);
lean_dec(v___x_3946_);
v_val_3950_ = lean_ctor_get(v_exportedInfo_x3f_3943_, 0);
v___x_3951_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3950_);
v___x_3952_ = lean_box(v___x_3951_);
v___x_3953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3952_);
v___y_3910_ = v___y_3945_;
v___y_3911_ = v_exportedInfo_x3f_3943_;
v___y_3912_ = v___y_3940_;
v___y_3913_ = v___y_3941_;
v___y_3914_ = v___y_3942_;
v___y_3915_ = v___y_3944_;
v___y_3916_ = v_env_3949_;
v___y_3917_ = v___x_3953_;
goto v___jp_3909_;
}
}
v___jp_3954_:
{
lean_object* v___x_3960_; 
lean_inc_ref(v___y_3957_);
v___x_3960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3960_, 0, v___y_3957_);
v___y_3940_ = v___y_3955_;
v___y_3941_ = v___y_3956_;
v___y_3942_ = v___y_3957_;
v_exportedInfo_x3f_3943_ = v___x_3960_;
v___y_3944_ = v___y_3958_;
v___y_3945_ = v___y_3959_;
goto v___jp_3939_;
}
v___jp_3961_:
{
lean_object* v___x_3967_; 
lean_inc_ref(v___y_3964_);
v___x_3967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3967_, 0, v___y_3964_);
v___y_3940_ = v___y_3962_;
v___y_3941_ = v___y_3963_;
v___y_3942_ = v___y_3964_;
v_exportedInfo_x3f_3943_ = v___x_3967_;
v___y_3944_ = v___y_3965_;
v___y_3945_ = v___y_3966_;
goto v___jp_3939_;
}
v___jp_3969_:
{
lean_object* v___x_3974_; uint8_t v___x_3975_; 
v___x_3974_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_3975_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3972_, v_options_3971_, v___x_3974_);
if (v___x_3975_ == 0)
{
lean_object* v___x_3976_; 
v___x_3976_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3774_, v___y_3970_, v___y_3973_);
return v___x_3976_;
}
else
{
lean_object* v___x_3977_; lean_object* v___x_3978_; 
v___x_3977_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
v___x_3978_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3968_, v___x_3977_, v___y_3970_, v___y_3973_);
if (lean_obj_tag(v___x_3978_) == 0)
{
lean_object* v___x_3979_; 
lean_dec_ref_known(v___x_3978_, 1);
v___x_3979_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3774_, v___y_3970_, v___y_3973_);
return v___x_3979_;
}
else
{
lean_dec(v_decl_3774_);
return v___x_3978_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___boxed(lean_object* v_decl_4880_, lean_object* v_forceExpose_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_){
_start:
{
uint8_t v_forceExpose_boxed_4885_; lean_object* v_res_4886_; 
v_forceExpose_boxed_4885_ = lean_unbox(v_forceExpose_4881_);
v_res_4886_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4880_, v_forceExpose_boxed_4885_, v_a_4882_, v_a_4883_);
lean_dec(v_a_4883_);
lean_dec_ref(v_a_4882_);
return v_res_4886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(lean_object* v_opt_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_){
_start:
{
lean_object* v___x_4891_; 
v___x_4891_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_4887_, v___y_4888_);
return v___x_4891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___boxed(lean_object* v_opt_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_){
_start:
{
lean_object* v_res_4896_; 
v_res_4896_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(v_opt_4892_, v___y_4893_, v___y_4894_);
lean_dec(v___y_4894_);
lean_dec_ref(v___y_4893_);
lean_dec_ref(v_opt_4892_);
return v_res_4896_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0(lean_object* v_x_4897_, lean_object* v_x_4898_, lean_object* v___y_4899_, lean_object* v___y_4900_){
_start:
{
if (lean_obj_tag(v_x_4897_) == 0)
{
lean_object* v___x_4902_; lean_object* v___x_4903_; 
v___x_4902_ = l_List_reverse___redArg(v_x_4898_);
v___x_4903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4903_, 0, v___x_4902_);
return v___x_4903_;
}
else
{
lean_object* v_head_4904_; lean_object* v_tail_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4923_; 
v_head_4904_ = lean_ctor_get(v_x_4897_, 0);
v_tail_4905_ = lean_ctor_get(v_x_4897_, 1);
v_isSharedCheck_4923_ = !lean_is_exclusive(v_x_4897_);
if (v_isSharedCheck_4923_ == 0)
{
v___x_4907_ = v_x_4897_;
v_isShared_4908_ = v_isSharedCheck_4923_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_tail_4905_);
lean_inc(v_head_4904_);
lean_dec(v_x_4897_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4923_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v___x_4909_; 
v___x_4909_ = l_Lean_snapshotEnvLinterOptions(v_head_4904_, v___y_4899_, v___y_4900_);
if (lean_obj_tag(v___x_4909_) == 0)
{
lean_object* v_a_4910_; lean_object* v___x_4912_; 
v_a_4910_ = lean_ctor_get(v___x_4909_, 0);
lean_inc(v_a_4910_);
lean_dec_ref_known(v___x_4909_, 1);
if (v_isShared_4908_ == 0)
{
lean_ctor_set(v___x_4907_, 1, v_x_4898_);
lean_ctor_set(v___x_4907_, 0, v_a_4910_);
v___x_4912_ = v___x_4907_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4914_; 
v_reuseFailAlloc_4914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4914_, 0, v_a_4910_);
lean_ctor_set(v_reuseFailAlloc_4914_, 1, v_x_4898_);
v___x_4912_ = v_reuseFailAlloc_4914_;
goto v_reusejp_4911_;
}
v_reusejp_4911_:
{
v_x_4897_ = v_tail_4905_;
v_x_4898_ = v___x_4912_;
goto _start;
}
}
else
{
lean_object* v_a_4915_; lean_object* v___x_4917_; uint8_t v_isShared_4918_; uint8_t v_isSharedCheck_4922_; 
lean_del_object(v___x_4907_);
lean_dec(v_tail_4905_);
lean_dec(v_x_4898_);
v_a_4915_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_4922_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4922_ == 0)
{
v___x_4917_ = v___x_4909_;
v_isShared_4918_ = v_isSharedCheck_4922_;
goto v_resetjp_4916_;
}
else
{
lean_inc(v_a_4915_);
lean_dec(v___x_4909_);
v___x_4917_ = lean_box(0);
v_isShared_4918_ = v_isSharedCheck_4922_;
goto v_resetjp_4916_;
}
v_resetjp_4916_:
{
lean_object* v___x_4920_; 
if (v_isShared_4918_ == 0)
{
v___x_4920_ = v___x_4917_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v_a_4915_);
v___x_4920_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
return v___x_4920_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0___boxed(lean_object* v_x_4924_, lean_object* v_x_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_){
_start:
{
lean_object* v_res_4929_; 
v_res_4929_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v_x_4924_, v_x_4925_, v___y_4926_, v___y_4927_);
lean_dec(v___y_4927_);
lean_dec_ref(v___y_4926_);
return v_res_4929_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object* v_decl_4930_, uint8_t v_forceExpose_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_){
_start:
{
lean_object* v___x_4935_; 
lean_inc(v_decl_4930_);
v___x_4935_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4930_, v_forceExpose_4931_, v_a_4932_, v_a_4933_);
if (lean_obj_tag(v___x_4935_) == 0)
{
lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; 
lean_dec_ref_known(v___x_4935_, 1);
v___x_4936_ = l_Lean_Declaration_getTopLevelNames(v_decl_4930_);
v___x_4937_ = lean_box(0);
v___x_4938_ = lean_box(0);
v___x_4939_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v___x_4936_, v___x_4937_, v_a_4932_, v_a_4933_);
if (lean_obj_tag(v___x_4939_) == 0)
{
lean_object* v___x_4941_; uint8_t v_isShared_4942_; uint8_t v_isSharedCheck_4946_; 
v_isSharedCheck_4946_ = !lean_is_exclusive(v___x_4939_);
if (v_isSharedCheck_4946_ == 0)
{
lean_object* v_unused_4947_; 
v_unused_4947_ = lean_ctor_get(v___x_4939_, 0);
lean_dec(v_unused_4947_);
v___x_4941_ = v___x_4939_;
v_isShared_4942_ = v_isSharedCheck_4946_;
goto v_resetjp_4940_;
}
else
{
lean_dec(v___x_4939_);
v___x_4941_ = lean_box(0);
v_isShared_4942_ = v_isSharedCheck_4946_;
goto v_resetjp_4940_;
}
v_resetjp_4940_:
{
lean_object* v___x_4944_; 
if (v_isShared_4942_ == 0)
{
lean_ctor_set(v___x_4941_, 0, v___x_4938_);
v___x_4944_ = v___x_4941_;
goto v_reusejp_4943_;
}
else
{
lean_object* v_reuseFailAlloc_4945_; 
v_reuseFailAlloc_4945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4945_, 0, v___x_4938_);
v___x_4944_ = v_reuseFailAlloc_4945_;
goto v_reusejp_4943_;
}
v_reusejp_4943_:
{
return v___x_4944_;
}
}
}
else
{
lean_object* v_a_4948_; lean_object* v___x_4950_; uint8_t v_isShared_4951_; uint8_t v_isSharedCheck_4955_; 
v_a_4948_ = lean_ctor_get(v___x_4939_, 0);
v_isSharedCheck_4955_ = !lean_is_exclusive(v___x_4939_);
if (v_isSharedCheck_4955_ == 0)
{
v___x_4950_ = v___x_4939_;
v_isShared_4951_ = v_isSharedCheck_4955_;
goto v_resetjp_4949_;
}
else
{
lean_inc(v_a_4948_);
lean_dec(v___x_4939_);
v___x_4950_ = lean_box(0);
v_isShared_4951_ = v_isSharedCheck_4955_;
goto v_resetjp_4949_;
}
v_resetjp_4949_:
{
lean_object* v___x_4953_; 
if (v_isShared_4951_ == 0)
{
v___x_4953_ = v___x_4950_;
goto v_reusejp_4952_;
}
else
{
lean_object* v_reuseFailAlloc_4954_; 
v_reuseFailAlloc_4954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4954_, 0, v_a_4948_);
v___x_4953_ = v_reuseFailAlloc_4954_;
goto v_reusejp_4952_;
}
v_reusejp_4952_:
{
return v___x_4953_;
}
}
}
}
else
{
lean_dec(v_decl_4930_);
return v___x_4935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___boxed(lean_object* v_decl_4956_, lean_object* v_forceExpose_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_){
_start:
{
uint8_t v_forceExpose_boxed_4961_; lean_object* v_res_4962_; 
v_forceExpose_boxed_4961_ = lean_unbox(v_forceExpose_4957_);
v_res_4962_ = l_Lean_addDecl(v_decl_4956_, v_forceExpose_boxed_4961_, v_a_4958_, v_a_4959_);
lean_dec(v_a_4959_);
lean_dec_ref(v_a_4958_);
return v_res_4962_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(lean_object* v_as_x27_4963_, lean_object* v_b_4964_, lean_object* v___y_4965_){
_start:
{
if (lean_obj_tag(v_as_x27_4963_) == 0)
{
lean_object* v___x_4967_; 
v___x_4967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4967_, 0, v_b_4964_);
return v___x_4967_;
}
else
{
lean_object* v_head_4968_; lean_object* v_tail_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v_env_4972_; lean_object* v_nextMacroScope_4973_; lean_object* v_ngen_4974_; lean_object* v_auxDeclNGen_4975_; lean_object* v_traceState_4976_; lean_object* v_recordedDeps_4977_; lean_object* v_messages_4978_; lean_object* v_infoState_4979_; lean_object* v_snapshotTasks_4980_; lean_object* v___x_4982_; uint8_t v_isShared_4983_; uint8_t v_isSharedCheck_4991_; 
v_head_4968_ = lean_ctor_get(v_as_x27_4963_, 0);
v_tail_4969_ = lean_ctor_get(v_as_x27_4963_, 1);
v___x_4970_ = lean_box(0);
v___x_4971_ = lean_st_ref_take(v___y_4965_);
v_env_4972_ = lean_ctor_get(v___x_4971_, 0);
v_nextMacroScope_4973_ = lean_ctor_get(v___x_4971_, 1);
v_ngen_4974_ = lean_ctor_get(v___x_4971_, 2);
v_auxDeclNGen_4975_ = lean_ctor_get(v___x_4971_, 3);
v_traceState_4976_ = lean_ctor_get(v___x_4971_, 4);
v_recordedDeps_4977_ = lean_ctor_get(v___x_4971_, 6);
v_messages_4978_ = lean_ctor_get(v___x_4971_, 7);
v_infoState_4979_ = lean_ctor_get(v___x_4971_, 8);
v_snapshotTasks_4980_ = lean_ctor_get(v___x_4971_, 9);
v_isSharedCheck_4991_ = !lean_is_exclusive(v___x_4971_);
if (v_isSharedCheck_4991_ == 0)
{
lean_object* v_unused_4992_; 
v_unused_4992_ = lean_ctor_get(v___x_4971_, 5);
lean_dec(v_unused_4992_);
v___x_4982_ = v___x_4971_;
v_isShared_4983_ = v_isSharedCheck_4991_;
goto v_resetjp_4981_;
}
else
{
lean_inc(v_snapshotTasks_4980_);
lean_inc(v_infoState_4979_);
lean_inc(v_messages_4978_);
lean_inc(v_recordedDeps_4977_);
lean_inc(v_traceState_4976_);
lean_inc(v_auxDeclNGen_4975_);
lean_inc(v_ngen_4974_);
lean_inc(v_nextMacroScope_4973_);
lean_inc(v_env_4972_);
lean_dec(v___x_4971_);
v___x_4982_ = lean_box(0);
v_isShared_4983_ = v_isSharedCheck_4991_;
goto v_resetjp_4981_;
}
v_resetjp_4981_:
{
lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4987_; 
lean_inc(v_head_4968_);
v___x_4984_ = l_Lean_markMeta(v_env_4972_, v_head_4968_);
v___x_4985_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4983_ == 0)
{
lean_ctor_set(v___x_4982_, 5, v___x_4985_);
lean_ctor_set(v___x_4982_, 0, v___x_4984_);
v___x_4987_ = v___x_4982_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_4990_; 
v_reuseFailAlloc_4990_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4990_, 0, v___x_4984_);
lean_ctor_set(v_reuseFailAlloc_4990_, 1, v_nextMacroScope_4973_);
lean_ctor_set(v_reuseFailAlloc_4990_, 2, v_ngen_4974_);
lean_ctor_set(v_reuseFailAlloc_4990_, 3, v_auxDeclNGen_4975_);
lean_ctor_set(v_reuseFailAlloc_4990_, 4, v_traceState_4976_);
lean_ctor_set(v_reuseFailAlloc_4990_, 5, v___x_4985_);
lean_ctor_set(v_reuseFailAlloc_4990_, 6, v_recordedDeps_4977_);
lean_ctor_set(v_reuseFailAlloc_4990_, 7, v_messages_4978_);
lean_ctor_set(v_reuseFailAlloc_4990_, 8, v_infoState_4979_);
lean_ctor_set(v_reuseFailAlloc_4990_, 9, v_snapshotTasks_4980_);
v___x_4987_ = v_reuseFailAlloc_4990_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
lean_object* v___x_4988_; 
v___x_4988_ = lean_st_ref_put(v___y_4965_, v___x_4987_);
v_as_x27_4963_ = v_tail_4969_;
v_b_4964_ = v___x_4970_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg___boxed(lean_object* v_as_x27_4993_, lean_object* v_b_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_){
_start:
{
lean_object* v_res_4997_; 
v_res_4997_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_4993_, v_b_4994_, v___y_4995_);
lean_dec(v___y_4995_);
lean_dec(v_as_x27_4993_);
return v_res_4997_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object* v_decl_4998_, uint8_t v_logCompileErrors_4999_, uint8_t v_markMeta_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_){
_start:
{
uint8_t v___x_5004_; lean_object* v___x_5005_; 
v___x_5004_ = 0;
lean_inc(v_decl_4998_);
v___x_5005_ = l_Lean_addDecl(v_decl_4998_, v___x_5004_, v_a_5001_, v_a_5002_);
if (lean_obj_tag(v___x_5005_) == 0)
{
lean_dec_ref_known(v___x_5005_, 1);
if (v_markMeta_5000_ == 0)
{
lean_object* v___x_5006_; 
v___x_5006_ = l_Lean_compileDecl(v_decl_4998_, v_logCompileErrors_4999_, v_a_5001_, v_a_5002_);
return v___x_5006_;
}
else
{
lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; 
lean_inc(v_decl_4998_);
v___x_5007_ = l_Lean_Declaration_getNames(v_decl_4998_);
v___x_5008_ = lean_box(0);
v___x_5009_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v___x_5007_, v___x_5008_, v_a_5002_);
lean_dec(v___x_5007_);
lean_dec_ref(v___x_5009_);
v___x_5010_ = l_Lean_compileDecl(v_decl_4998_, v_logCompileErrors_4999_, v_a_5001_, v_a_5002_);
return v___x_5010_;
}
}
else
{
lean_dec(v_decl_4998_);
return v___x_5005_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___boxed(lean_object* v_decl_5011_, lean_object* v_logCompileErrors_5012_, lean_object* v_markMeta_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_){
_start:
{
uint8_t v_logCompileErrors_boxed_5017_; uint8_t v_markMeta_boxed_5018_; lean_object* v_res_5019_; 
v_logCompileErrors_boxed_5017_ = lean_unbox(v_logCompileErrors_5012_);
v_markMeta_boxed_5018_ = lean_unbox(v_markMeta_5013_);
v_res_5019_ = l_Lean_addAndCompile(v_decl_5011_, v_logCompileErrors_boxed_5017_, v_markMeta_boxed_5018_, v_a_5014_, v_a_5015_);
lean_dec(v_a_5015_);
lean_dec_ref(v_a_5014_);
return v_res_5019_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(lean_object* v_as_5020_, lean_object* v_as_x27_5021_, lean_object* v_b_5022_, lean_object* v_a_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_){
_start:
{
lean_object* v___x_5027_; 
v___x_5027_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_5021_, v_b_5022_, v___y_5025_);
return v___x_5027_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___boxed(lean_object* v_as_5028_, lean_object* v_as_x27_5029_, lean_object* v_b_5030_, lean_object* v_a_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_){
_start:
{
lean_object* v_res_5035_; 
v_res_5035_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(v_as_5028_, v_as_x27_5029_, v_b_5030_, v_a_5031_, v___y_5032_, v___y_5033_);
lean_dec(v___y_5033_);
lean_dec_ref(v___y_5032_);
lean_dec(v_as_x27_5029_);
lean_dec(v_as_5028_);
return v_res_5035_;
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
