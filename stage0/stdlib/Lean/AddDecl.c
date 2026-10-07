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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
uint8_t v_suppressElabErrors_boxed_422_; uint8_t v___y_15084__boxed_423_; uint8_t v_res_424_; lean_object* v_r_425_; 
v_suppressElabErrors_boxed_422_ = lean_unbox(v_suppressElabErrors_419_);
v___y_15084__boxed_423_ = lean_unbox(v___y_420_);
v_res_424_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(v_suppressElabErrors_boxed_422_, v___y_15084__boxed_423_, v_x_421_);
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
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_428_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_429_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0);
v___x_430_ = lean_unsigned_to_nat(0u);
v___x_431_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
lean_ctor_set(v___x_431_, 2, v___x_430_);
lean_ctor_set(v___x_431_, 3, v___x_430_);
lean_ctor_set(v___x_431_, 4, v___x_429_);
lean_ctor_set(v___x_431_, 5, v___x_429_);
lean_ctor_set(v___x_431_, 6, v___x_429_);
lean_ctor_set(v___x_431_, 7, v___x_429_);
lean_ctor_set(v___x_431_, 8, v___x_429_);
lean_ctor_set(v___x_431_, 9, v___x_429_);
lean_ctor_set(v___x_431_, 10, v___x_429_);
lean_ctor_set(v___x_431_, 11, v___x_428_);
return v___x_431_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_432_ = lean_unsigned_to_nat(32u);
v___x_433_ = lean_mk_empty_array_with_capacity(v___x_432_);
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
return v___x_434_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3(void){
_start:
{
size_t v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_435_ = ((size_t)5ULL);
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = lean_unsigned_to_nat(32u);
v___x_438_ = lean_mk_empty_array_with_capacity(v___x_437_);
v___x_439_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2);
v___x_440_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v___x_438_);
lean_ctor_set(v___x_440_, 2, v___x_436_);
lean_ctor_set(v___x_440_, 3, v___x_436_);
lean_ctor_set_usize(v___x_440_, 4, v___x_435_);
return v___x_440_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_441_ = lean_box(1);
v___x_442_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3);
v___x_443_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0);
v___x_444_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v___x_442_);
lean_ctor_set(v___x_444_, 2, v___x_441_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(lean_object* v_msgData_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___x_449_; lean_object* v_toCold_450_; lean_object* v_env_451_; lean_object* v_options_452_; uint8_t v___x_453_; lean_object* v_env_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_449_ = lean_st_ref_get(v___y_447_);
v_toCold_450_ = lean_ctor_get(v___y_446_, 0);
v_env_451_ = lean_ctor_get(v___x_449_, 0);
lean_inc_ref(v_env_451_);
lean_dec(v___x_449_);
v_options_452_ = lean_ctor_get(v_toCold_450_, 2);
v___x_453_ = 0;
v_env_454_ = l_Lean_Environment_setRecordingDeps(v_env_451_, v___x_453_);
v___x_455_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1);
v___x_456_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
lean_inc_ref(v_options_452_);
v___x_457_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_457_, 0, v_env_454_);
lean_ctor_set(v___x_457_, 1, v___x_455_);
lean_ctor_set(v___x_457_, 2, v___x_456_);
lean_ctor_set(v___x_457_, 3, v_options_452_);
v___x_458_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v_msgData_445_);
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___boxed(lean_object* v_msgData_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msgData_460_, v___y_461_, v___y_462_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(lean_object* v_ref_466_, lean_object* v_msgData_467_, uint8_t v_severity_468_, uint8_t v_isSilent_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
uint8_t v___y_474_; uint8_t v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v_toCold_481_; lean_object* v___y_482_; lean_object* v___y_511_; lean_object* v___y_512_; uint8_t v___y_513_; lean_object* v___y_514_; uint8_t v___y_515_; uint8_t v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; uint8_t v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; uint8_t v___y_541_; uint8_t v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; uint8_t v___y_548_; uint8_t v___y_549_; uint8_t v___y_550_; uint8_t v___x_561_; uint8_t v___y_563_; uint8_t v___y_564_; uint8_t v___y_565_; uint8_t v___y_567_; uint8_t v___x_575_; 
v___x_561_ = 2;
v___x_575_ = l_Lean_instBEqMessageSeverity_beq(v_severity_468_, v___x_561_);
if (v___x_575_ == 0)
{
v___y_567_ = v___x_575_;
goto v___jp_566_;
}
else
{
uint8_t v___x_576_; 
lean_inc_ref(v_msgData_467_);
v___x_576_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_467_);
v___y_567_ = v___x_576_;
goto v___jp_566_;
}
v___jp_473_:
{
lean_object* v_currNamespace_483_; lean_object* v_openDecls_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v_env_489_; lean_object* v_nextMacroScope_490_; lean_object* v_ngen_491_; lean_object* v_auxDeclNGen_492_; lean_object* v_traceState_493_; lean_object* v_cache_494_; lean_object* v_recordedDeps_495_; lean_object* v_messages_496_; lean_object* v_infoState_497_; lean_object* v_snapshotTasks_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_509_; 
v_currNamespace_483_ = lean_ctor_get(v_toCold_481_, 4);
v_openDecls_484_ = lean_ctor_get(v_toCold_481_, 5);
lean_inc(v_openDecls_484_);
lean_inc(v_currNamespace_483_);
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v_currNamespace_483_);
lean_ctor_set(v___x_485_, 1, v_openDecls_484_);
v___x_486_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v___y_476_);
lean_inc_ref(v___y_480_);
lean_inc_ref(v___y_478_);
v___x_487_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_487_, 0, v___y_478_);
lean_ctor_set(v___x_487_, 1, v___y_479_);
lean_ctor_set(v___x_487_, 2, v___y_477_);
lean_ctor_set(v___x_487_, 3, v___y_480_);
lean_ctor_set(v___x_487_, 4, v___x_486_);
lean_ctor_set_uint8(v___x_487_, sizeof(void*)*5, v___y_475_);
lean_ctor_set_uint8(v___x_487_, sizeof(void*)*5 + 1, v___y_474_);
lean_ctor_set_uint8(v___x_487_, sizeof(void*)*5 + 2, v_isSilent_469_);
v___x_488_ = lean_st_ref_take(v___y_482_);
v_env_489_ = lean_ctor_get(v___x_488_, 0);
v_nextMacroScope_490_ = lean_ctor_get(v___x_488_, 1);
v_ngen_491_ = lean_ctor_get(v___x_488_, 2);
v_auxDeclNGen_492_ = lean_ctor_get(v___x_488_, 3);
v_traceState_493_ = lean_ctor_get(v___x_488_, 4);
v_cache_494_ = lean_ctor_get(v___x_488_, 5);
v_recordedDeps_495_ = lean_ctor_get(v___x_488_, 6);
v_messages_496_ = lean_ctor_get(v___x_488_, 7);
v_infoState_497_ = lean_ctor_get(v___x_488_, 8);
v_snapshotTasks_498_ = lean_ctor_get(v___x_488_, 9);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_509_ == 0)
{
v___x_500_ = v___x_488_;
v_isShared_501_ = v_isSharedCheck_509_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_snapshotTasks_498_);
lean_inc(v_infoState_497_);
lean_inc(v_messages_496_);
lean_inc(v_recordedDeps_495_);
lean_inc(v_cache_494_);
lean_inc(v_traceState_493_);
lean_inc(v_auxDeclNGen_492_);
lean_inc(v_ngen_491_);
lean_inc(v_nextMacroScope_490_);
lean_inc(v_env_489_);
lean_dec(v___x_488_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_509_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_502_ = lean_box(0);
v___x_503_ = l_Lean_MessageLog_add(v___x_487_, v_messages_496_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 7, v___x_503_);
v___x_505_ = v___x_500_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_env_489_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v_nextMacroScope_490_);
lean_ctor_set(v_reuseFailAlloc_508_, 2, v_ngen_491_);
lean_ctor_set(v_reuseFailAlloc_508_, 3, v_auxDeclNGen_492_);
lean_ctor_set(v_reuseFailAlloc_508_, 4, v_traceState_493_);
lean_ctor_set(v_reuseFailAlloc_508_, 5, v_cache_494_);
lean_ctor_set(v_reuseFailAlloc_508_, 6, v_recordedDeps_495_);
lean_ctor_set(v_reuseFailAlloc_508_, 7, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_508_, 8, v_infoState_497_);
lean_ctor_set(v_reuseFailAlloc_508_, 9, v_snapshotTasks_498_);
v___x_505_ = v_reuseFailAlloc_508_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_st_ref_put(v___y_482_, v___x_505_);
v___x_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_502_);
return v___x_507_;
}
}
}
v___jp_510_:
{
lean_object* v_fileName_519_; lean_object* v_fileMap_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_536_; 
v_fileName_519_ = lean_ctor_get(v___y_517_, 0);
v_fileMap_520_ = lean_ctor_get(v___y_517_, 1);
v___x_521_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_467_);
v___x_522_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v___x_521_, v___y_470_, v___y_471_);
v_a_523_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_536_ == 0)
{
v___x_525_ = v___x_522_;
v_isShared_526_ = v_isSharedCheck_536_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_522_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_536_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
lean_inc_ref_n(v_fileMap_520_, 2);
v___x_527_ = l_Lean_FileMap_toPosition(v_fileMap_520_, v___y_514_);
lean_dec(v___y_514_);
v___x_528_ = l_Lean_FileMap_toPosition(v_fileMap_520_, v___y_518_);
lean_dec(v___y_518_);
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
v___x_530_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
if (v___y_513_ == 0)
{
lean_del_object(v___x_525_);
lean_dec_ref(v___y_511_);
v___y_474_ = v___y_516_;
v___y_475_ = v___y_515_;
v___y_476_ = v_a_523_;
v___y_477_ = v___x_529_;
v___y_478_ = v_fileName_519_;
v___y_479_ = v___x_527_;
v___y_480_ = v___x_530_;
v_toCold_481_ = v___y_512_;
v___y_482_ = v___y_471_;
goto v___jp_473_;
}
else
{
uint8_t v___x_531_; 
lean_inc(v_a_523_);
v___x_531_ = l_Lean_MessageData_hasTag(v___y_511_, v_a_523_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; lean_object* v___x_534_; 
lean_dec_ref_known(v___x_529_, 1);
lean_dec_ref(v___x_527_);
lean_dec(v_a_523_);
v___x_532_ = lean_box(0);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_532_);
v___x_534_ = v___x_525_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
else
{
lean_del_object(v___x_525_);
v___y_474_ = v___y_516_;
v___y_475_ = v___y_515_;
v___y_476_ = v_a_523_;
v___y_477_ = v___x_529_;
v___y_478_ = v_fileName_519_;
v___y_479_ = v___x_527_;
v___y_480_ = v___x_530_;
v_toCold_481_ = v___y_512_;
v___y_482_ = v___y_471_;
goto v___jp_473_;
}
}
}
}
v___jp_537_:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_Syntax_getTailPos_x3f(v___y_543_, v___y_542_);
lean_dec(v___y_543_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_inc(v___y_544_);
v___y_511_ = v___y_539_;
v___y_512_ = v___y_540_;
v___y_513_ = v___y_538_;
v___y_514_ = v___y_544_;
v___y_515_ = v___y_542_;
v___y_516_ = v___y_541_;
v___y_517_ = v___y_540_;
v___y_518_ = v___y_544_;
goto v___jp_510_;
}
else
{
lean_object* v_val_546_; 
v_val_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_val_546_);
lean_dec_ref_known(v___x_545_, 1);
v___y_511_ = v___y_539_;
v___y_512_ = v___y_540_;
v___y_513_ = v___y_538_;
v___y_514_ = v___y_544_;
v___y_515_ = v___y_542_;
v___y_516_ = v___y_541_;
v___y_517_ = v___y_540_;
v___y_518_ = v_val_546_;
goto v___jp_510_;
}
}
v___jp_547_:
{
lean_object* v_toCold_551_; lean_object* v_ref_552_; uint8_t v_suppressElabErrors_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___f_556_; lean_object* v_ref_557_; lean_object* v___x_558_; 
v_toCold_551_ = lean_ctor_get(v___y_470_, 0);
v_ref_552_ = lean_ctor_get(v___y_470_, 2);
v_suppressElabErrors_553_ = lean_ctor_get_uint8(v___y_470_, sizeof(void*)*3 + 2);
v___x_554_ = lean_box(v_suppressElabErrors_553_);
v___x_555_ = lean_box(v___y_548_);
v___f_556_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed), 3, 2);
lean_closure_set(v___f_556_, 0, v___x_554_);
lean_closure_set(v___f_556_, 1, v___x_555_);
v_ref_557_ = l_Lean_replaceRef(v_ref_466_, v_ref_552_);
v___x_558_ = l_Lean_Syntax_getPos_x3f(v_ref_557_, v___y_549_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v___x_559_; 
v___x_559_ = lean_unsigned_to_nat(0u);
v___y_538_ = v_suppressElabErrors_553_;
v___y_539_ = v___f_556_;
v___y_540_ = v_toCold_551_;
v___y_541_ = v___y_550_;
v___y_542_ = v___y_549_;
v___y_543_ = v_ref_557_;
v___y_544_ = v___x_559_;
goto v___jp_537_;
}
else
{
lean_object* v_val_560_; 
v_val_560_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_val_560_);
lean_dec_ref_known(v___x_558_, 1);
v___y_538_ = v_suppressElabErrors_553_;
v___y_539_ = v___f_556_;
v___y_540_ = v_toCold_551_;
v___y_541_ = v___y_550_;
v___y_542_ = v___y_549_;
v___y_543_ = v_ref_557_;
v___y_544_ = v_val_560_;
goto v___jp_537_;
}
}
v___jp_562_:
{
if (v___y_565_ == 0)
{
v___y_548_ = v___y_563_;
v___y_549_ = v___y_564_;
v___y_550_ = v_severity_468_;
goto v___jp_547_;
}
else
{
v___y_548_ = v___y_563_;
v___y_549_ = v___y_564_;
v___y_550_ = v___x_561_;
goto v___jp_547_;
}
}
v___jp_566_:
{
if (v___y_567_ == 0)
{
uint8_t v___x_568_; uint8_t v___x_569_; 
v___x_568_ = 1;
v___x_569_ = l_Lean_instBEqMessageSeverity_beq(v_severity_468_, v___x_568_);
if (v___x_569_ == 0)
{
v___y_563_ = v___y_567_;
v___y_564_ = v___y_567_;
v___y_565_ = v___x_569_;
goto v___jp_562_;
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_570_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_470_);
v___x_571_ = l_Lean_warningAsError;
v___x_572_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_570_, v___x_571_);
lean_dec_ref(v___x_570_);
v___y_563_ = v___y_567_;
v___y_564_ = v___y_567_;
v___y_565_ = v___x_572_;
goto v___jp_562_;
}
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec_ref(v_msgData_467_);
v___x_573_ = lean_box(0);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___boxed(lean_object* v_ref_577_, lean_object* v_msgData_578_, lean_object* v_severity_579_, lean_object* v_isSilent_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
uint8_t v_severity_boxed_584_; uint8_t v_isSilent_boxed_585_; lean_object* v_res_586_; 
v_severity_boxed_584_ = lean_unbox(v_severity_579_);
v_isSilent_boxed_585_ = lean_unbox(v_isSilent_580_);
v_res_586_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_577_, v_msgData_578_, v_severity_boxed_584_, v_isSilent_boxed_585_, v___y_581_, v___y_582_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v_ref_577_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(lean_object* v_msgData_587_, uint8_t v_severity_588_, uint8_t v_isSilent_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v_ref_593_; lean_object* v___x_594_; 
v_ref_593_ = lean_ctor_get(v___y_590_, 2);
v___x_594_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_593_, v_msgData_587_, v_severity_588_, v_isSilent_589_, v___y_590_, v___y_591_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4___boxed(lean_object* v_msgData_595_, lean_object* v_severity_596_, lean_object* v_isSilent_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
uint8_t v_severity_boxed_601_; uint8_t v_isSilent_boxed_602_; lean_object* v_res_603_; 
v_severity_boxed_601_ = lean_unbox(v_severity_596_);
v_isSilent_boxed_602_ = lean_unbox(v_isSilent_597_);
v_res_603_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_595_, v_severity_boxed_601_, v_isSilent_boxed_602_, v___y_598_, v___y_599_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(lean_object* v_msgData_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
uint8_t v___x_608_; uint8_t v___x_609_; lean_object* v___x_610_; 
v___x_608_ = 1;
v___x_609_ = 0;
v___x_610_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_604_, v___x_608_, v___x_609_, v___y_605_, v___y_606_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2___boxed(lean_object* v_msgData_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v_msgData_611_, v___y_612_, v___y_613_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(lean_object* v_as_619_, size_t v_sz_620_, size_t v_i_621_, lean_object* v_b_622_){
_start:
{
uint8_t v___x_623_; 
v___x_623_ = lean_usize_dec_lt(v_i_621_, v_sz_620_);
if (v___x_623_ == 0)
{
lean_inc_ref(v_b_622_);
return v_b_622_;
}
else
{
lean_object* v_a_624_; lean_object* v_fst_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v_a_624_ = lean_array_uget_borrowed(v_as_619_, v_i_621_);
v_fst_625_ = lean_ctor_get(v_a_624_, 0);
v___x_626_ = lean_box(0);
v___x_627_ = lean_unbox(v_fst_625_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; size_t v___x_629_; size_t v___x_630_; 
v___x_628_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___closed__0));
v___x_629_ = ((size_t)1ULL);
v___x_630_ = lean_usize_add(v_i_621_, v___x_629_);
v_i_621_ = v___x_630_;
v_b_622_ = v___x_628_;
goto _start;
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
lean_inc(v_a_624_);
v___x_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_632_, 0, v_a_624_);
v___x_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
lean_ctor_set(v___x_634_, 1, v___x_626_);
return v___x_634_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___boxed(lean_object* v_as_635_, lean_object* v_sz_636_, lean_object* v_i_637_, lean_object* v_b_638_){
_start:
{
size_t v_sz_boxed_639_; size_t v_i_boxed_640_; lean_object* v_res_641_; 
v_sz_boxed_639_ = lean_unbox_usize(v_sz_636_);
lean_dec(v_sz_636_);
v_i_boxed_640_ = lean_unbox_usize(v_i_637_);
lean_dec(v_i_637_);
v_res_641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v_as_635_, v_sz_boxed_639_, v_i_boxed_640_, v_b_638_);
lean_dec_ref(v_b_638_);
lean_dec_ref(v_as_635_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(lean_object* v_fn_642_, lean_object* v_e_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_Expr_getSorry_x3f(v_e_643_);
if (lean_obj_tag(v___x_650_) == 1)
{
lean_object* v_val_651_; lean_object* v___x_652_; 
v_val_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_val_651_);
lean_dec_ref_known(v___x_650_, 1);
lean_inc(v___y_648_);
lean_inc_ref(v___y_647_);
lean_inc(v___y_646_);
lean_inc_ref(v___y_645_);
lean_inc(v___y_644_);
v___x_652_ = lean_apply_7(v_fn_642_, v_val_651_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, lean_box(0));
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_661_; 
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_661_ == 0)
{
lean_object* v_unused_662_; 
v_unused_662_ = lean_ctor_get(v___x_652_, 0);
lean_dec(v_unused_662_);
v___x_654_ = v___x_652_;
v_isShared_655_ = v_isSharedCheck_661_;
goto v_resetjp_653_;
}
else
{
lean_dec(v___x_652_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_661_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
uint8_t v___x_656_; lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_656_ = 0;
v___x_657_ = lean_box(v___x_656_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_657_);
v___x_659_ = v___x_654_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
v_a_663_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_652_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_652_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
else
{
uint8_t v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
lean_dec(v___x_650_);
lean_dec_ref(v_fn_642_);
v___x_671_ = 1;
v___x_672_ = lean_box(v___x_671_);
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed(lean_object* v_fn_674_, lean_object* v_e_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(v_fn_674_, v_e_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v_e_675_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_object* v_00_u03b1_683_, lean_object* v_x_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = lean_apply_1(v_x_684_, lean_box(0));
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v_00_u03b1_693_, lean_object* v_x_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(v_00_u03b1_693_, v_x_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(lean_object* v_k_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v_b_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v___x_711_; 
lean_inc(v___y_709_);
lean_inc_ref(v___y_708_);
lean_inc(v___y_707_);
lean_inc_ref(v___y_706_);
lean_inc(v___y_704_);
lean_inc(v___y_703_);
v___x_711_ = lean_apply_8(v_k_702_, v_b_705_, v___y_703_, v___y_704_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, lean_box(0));
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed(lean_object* v_k_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v_b_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(v_k_712_, v___y_713_, v___y_714_, v_b_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_714_);
lean_dec(v___y_713_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(lean_object* v_name_722_, lean_object* v_type_723_, lean_object* v_val_724_, lean_object* v_k_725_, uint8_t v_nondep_726_, uint8_t v_kind_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v___f_735_; lean_object* v___x_736_; 
lean_inc(v___y_729_);
lean_inc(v___y_728_);
v___f_735_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_735_, 0, v_k_725_);
lean_closure_set(v___f_735_, 1, v___y_728_);
lean_closure_set(v___f_735_, 2, v___y_729_);
v___x_736_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_722_, v_type_723_, v_val_724_, v___f_735_, v_nondep_726_, v_kind_727_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
if (lean_obj_tag(v___x_736_) == 0)
{
return v___x_736_;
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg___boxed(lean_object* v_name_745_, lean_object* v_type_746_, lean_object* v_val_747_, lean_object* v_k_748_, lean_object* v_nondep_749_, lean_object* v_kind_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
uint8_t v_nondep_boxed_758_; uint8_t v_kind_boxed_759_; lean_object* v_res_760_; 
v_nondep_boxed_758_ = lean_unbox(v_nondep_749_);
v_kind_boxed_759_ = lean_unbox(v_kind_750_);
v_res_760_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_745_, v_type_746_, v_val_747_, v_k_748_, v_nondep_boxed_758_, v_kind_boxed_759_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec(v___y_751_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed(lean_object* v_fvars_761_, lean_object* v_f_762_, lean_object* v_body_763_, lean_object* v_x_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(v_fvars_761_, v_f_762_, v_body_763_, v_x_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec(v___y_765_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(lean_object* v_f_773_, lean_object* v_fvars_774_, lean_object* v_a_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
if (lean_obj_tag(v_a_775_) == 8)
{
lean_object* v_declName_783_; lean_object* v_type_784_; lean_object* v_value_785_; lean_object* v_body_786_; lean_object* v___f_787_; lean_object* v_d_788_; lean_object* v_v_789_; lean_object* v___x_790_; 
v_declName_783_ = lean_ctor_get(v_a_775_, 0);
lean_inc(v_declName_783_);
v_type_784_ = lean_ctor_get(v_a_775_, 1);
lean_inc_ref(v_type_784_);
v_value_785_ = lean_ctor_get(v_a_775_, 2);
lean_inc_ref(v_value_785_);
v_body_786_ = lean_ctor_get(v_a_775_, 3);
lean_inc_ref(v_body_786_);
lean_dec_ref_known(v_a_775_, 4);
lean_inc_ref_n(v_f_773_, 2);
lean_inc_ref(v_fvars_774_);
v___f_787_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed), 11, 3);
lean_closure_set(v___f_787_, 0, v_fvars_774_);
lean_closure_set(v___f_787_, 1, v_f_773_);
lean_closure_set(v___f_787_, 2, v_body_786_);
v_d_788_ = lean_expr_instantiate_rev(v_type_784_, v_fvars_774_);
lean_dec_ref(v_type_784_);
v_v_789_ = lean_expr_instantiate_rev(v_value_785_, v_fvars_774_);
lean_dec_ref(v_fvars_774_);
lean_dec_ref(v_value_785_);
lean_inc(v___y_781_);
lean_inc_ref(v___y_780_);
lean_inc(v___y_779_);
lean_inc_ref(v___y_778_);
lean_inc(v___y_777_);
lean_inc(v___y_776_);
lean_inc_ref(v_d_788_);
v___x_790_ = lean_apply_8(v_f_773_, v_d_788_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, lean_box(0));
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v___x_791_; 
lean_dec_ref_known(v___x_790_, 1);
lean_inc(v___y_781_);
lean_inc_ref(v___y_780_);
lean_inc(v___y_779_);
lean_inc_ref(v___y_778_);
lean_inc(v___y_777_);
lean_inc(v___y_776_);
lean_inc_ref(v_v_789_);
v___x_791_ = lean_apply_8(v_f_773_, v_v_789_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, lean_box(0));
if (lean_obj_tag(v___x_791_) == 0)
{
uint8_t v___x_792_; uint8_t v___x_793_; lean_object* v___x_794_; 
lean_dec_ref_known(v___x_791_, 1);
v___x_792_ = 0;
v___x_793_ = 0;
v___x_794_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_declName_783_, v_d_788_, v_v_789_, v___f_787_, v___x_792_, v___x_793_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
return v___x_794_;
}
else
{
lean_dec_ref(v_v_789_);
lean_dec_ref(v_d_788_);
lean_dec_ref(v___f_787_);
lean_dec(v_declName_783_);
return v___x_791_;
}
}
else
{
lean_dec_ref(v_v_789_);
lean_dec_ref(v_d_788_);
lean_dec_ref(v___f_787_);
lean_dec(v_declName_783_);
lean_dec_ref(v_f_773_);
return v___x_790_;
}
}
else
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = lean_expr_instantiate_rev(v_a_775_, v_fvars_774_);
lean_dec_ref(v_fvars_774_);
lean_dec_ref(v_a_775_);
lean_inc(v___y_781_);
lean_inc_ref(v___y_780_);
lean_inc(v___y_779_);
lean_inc_ref(v___y_778_);
lean_inc(v___y_777_);
lean_inc(v___y_776_);
v___x_796_ = lean_apply_8(v_f_773_, v___x_795_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, lean_box(0));
return v___x_796_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(lean_object* v_fvars_797_, lean_object* v_f_798_, lean_object* v_body_799_, lean_object* v_x_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = lean_array_push(v_fvars_797_, v_x_800_);
v___x_809_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_798_, v___x_808_, v_body_799_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___boxed(lean_object* v_f_810_, lean_object* v_fvars_811_, lean_object* v_a_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_810_, v_fvars_811_, v_a_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec(v___y_813_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(lean_object* v_f_823_, lean_object* v_e_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_833_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_823_, v___x_832_, v_e_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___boxed(lean_object* v_f_834_, lean_object* v_e_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v_f_834_, v_e_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec(v___y_836_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(lean_object* v_name_844_, uint8_t v_bi_845_, lean_object* v_type_846_, lean_object* v_k_847_, uint8_t v_kind_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v___f_856_; lean_object* v___x_857_; 
lean_inc(v___y_850_);
lean_inc(v___y_849_);
v___f_856_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_856_, 0, v_k_847_);
lean_closure_set(v___f_856_, 1, v___y_849_);
lean_closure_set(v___f_856_, 2, v___y_850_);
v___x_857_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_844_, v_bi_845_, v_type_846_, v___f_856_, v_kind_848_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
if (lean_obj_tag(v___x_857_) == 0)
{
return v___x_857_;
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_857_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_857_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___boxed(lean_object* v_name_866_, lean_object* v_bi_867_, lean_object* v_type_868_, lean_object* v_k_869_, lean_object* v_kind_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
uint8_t v_bi_boxed_878_; uint8_t v_kind_boxed_879_; lean_object* v_res_880_; 
v_bi_boxed_878_ = lean_unbox(v_bi_867_);
v_kind_boxed_879_ = lean_unbox(v_kind_870_);
v_res_880_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_866_, v_bi_boxed_878_, v_type_868_, v_k_869_, v_kind_boxed_879_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec(v___y_871_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed(lean_object* v_fvars_881_, lean_object* v_f_882_, lean_object* v_body_883_, lean_object* v_x_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(v_fvars_881_, v_f_882_, v_body_883_, v_x_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec(v___y_885_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(lean_object* v_f_893_, lean_object* v_fvars_894_, lean_object* v_a_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
if (lean_obj_tag(v_a_895_) == 7)
{
lean_object* v_binderName_903_; lean_object* v_binderType_904_; lean_object* v_body_905_; uint8_t v_binderInfo_906_; lean_object* v___f_907_; lean_object* v_d_908_; lean_object* v___x_909_; 
v_binderName_903_ = lean_ctor_get(v_a_895_, 0);
lean_inc(v_binderName_903_);
v_binderType_904_ = lean_ctor_get(v_a_895_, 1);
lean_inc_ref(v_binderType_904_);
v_body_905_ = lean_ctor_get(v_a_895_, 2);
lean_inc_ref(v_body_905_);
v_binderInfo_906_ = lean_ctor_get_uint8(v_a_895_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_895_, 3);
lean_inc_ref(v_f_893_);
lean_inc_ref(v_fvars_894_);
v___f_907_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed), 11, 3);
lean_closure_set(v___f_907_, 0, v_fvars_894_);
lean_closure_set(v___f_907_, 1, v_f_893_);
lean_closure_set(v___f_907_, 2, v_body_905_);
v_d_908_ = lean_expr_instantiate_rev(v_binderType_904_, v_fvars_894_);
lean_dec_ref(v_fvars_894_);
lean_dec_ref(v_binderType_904_);
lean_inc(v___y_901_);
lean_inc_ref(v___y_900_);
lean_inc(v___y_899_);
lean_inc_ref(v___y_898_);
lean_inc(v___y_897_);
lean_inc(v___y_896_);
lean_inc_ref(v_d_908_);
v___x_909_ = lean_apply_8(v_f_893_, v_d_908_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, lean_box(0));
if (lean_obj_tag(v___x_909_) == 0)
{
uint8_t v___x_910_; lean_object* v___x_911_; 
lean_dec_ref_known(v___x_909_, 1);
v___x_910_ = 0;
v___x_911_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_903_, v_binderInfo_906_, v_d_908_, v___f_907_, v___x_910_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
return v___x_911_;
}
else
{
lean_dec_ref(v_d_908_);
lean_dec_ref(v___f_907_);
lean_dec(v_binderName_903_);
return v___x_909_;
}
}
else
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = lean_expr_instantiate_rev(v_a_895_, v_fvars_894_);
lean_dec_ref(v_fvars_894_);
lean_dec_ref(v_a_895_);
lean_inc(v___y_901_);
lean_inc_ref(v___y_900_);
lean_inc(v___y_899_);
lean_inc_ref(v___y_898_);
lean_inc(v___y_897_);
lean_inc(v___y_896_);
v___x_913_ = lean_apply_8(v_f_893_, v___x_912_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, lean_box(0));
return v___x_913_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(lean_object* v_fvars_914_, lean_object* v_f_915_, lean_object* v_body_916_, lean_object* v_x_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = lean_array_push(v_fvars_914_, v_x_917_);
v___x_926_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_915_, v___x_925_, v_body_916_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___boxed(lean_object* v_f_927_, lean_object* v_fvars_928_, lean_object* v_a_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_927_, v_fvars_928_, v_a_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec(v___y_930_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(lean_object* v_f_938_, lean_object* v_e_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_948_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_938_, v___x_947_, v_e_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10___boxed(lean_object* v_f_949_, lean_object* v_e_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v_f_949_, v_e_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec(v___y_951_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed(lean_object* v_fvars_959_, lean_object* v_f_960_, lean_object* v_body_961_, lean_object* v_x_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(v_fvars_959_, v_f_960_, v_body_961_, v_x_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec(v___y_963_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(lean_object* v_f_971_, lean_object* v_fvars_972_, lean_object* v_a_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
if (lean_obj_tag(v_a_973_) == 6)
{
lean_object* v_binderName_981_; lean_object* v_binderType_982_; lean_object* v_body_983_; uint8_t v_binderInfo_984_; lean_object* v___f_985_; lean_object* v_d_986_; lean_object* v___x_987_; 
v_binderName_981_ = lean_ctor_get(v_a_973_, 0);
lean_inc(v_binderName_981_);
v_binderType_982_ = lean_ctor_get(v_a_973_, 1);
lean_inc_ref(v_binderType_982_);
v_body_983_ = lean_ctor_get(v_a_973_, 2);
lean_inc_ref(v_body_983_);
v_binderInfo_984_ = lean_ctor_get_uint8(v_a_973_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_973_, 3);
lean_inc_ref(v_f_971_);
lean_inc_ref(v_fvars_972_);
v___f_985_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed), 11, 3);
lean_closure_set(v___f_985_, 0, v_fvars_972_);
lean_closure_set(v___f_985_, 1, v_f_971_);
lean_closure_set(v___f_985_, 2, v_body_983_);
v_d_986_ = lean_expr_instantiate_rev(v_binderType_982_, v_fvars_972_);
lean_dec_ref(v_fvars_972_);
lean_dec_ref(v_binderType_982_);
lean_inc(v___y_979_);
lean_inc_ref(v___y_978_);
lean_inc(v___y_977_);
lean_inc_ref(v___y_976_);
lean_inc(v___y_975_);
lean_inc(v___y_974_);
lean_inc_ref(v_d_986_);
v___x_987_ = lean_apply_8(v_f_971_, v_d_986_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, lean_box(0));
if (lean_obj_tag(v___x_987_) == 0)
{
uint8_t v___x_988_; lean_object* v___x_989_; 
lean_dec_ref_known(v___x_987_, 1);
v___x_988_ = 0;
v___x_989_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_981_, v_binderInfo_984_, v_d_986_, v___f_985_, v___x_988_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
return v___x_989_;
}
else
{
lean_dec_ref(v_d_986_);
lean_dec_ref(v___f_985_);
lean_dec(v_binderName_981_);
return v___x_987_;
}
}
else
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = lean_expr_instantiate_rev(v_a_973_, v_fvars_972_);
lean_dec_ref(v_fvars_972_);
lean_dec_ref(v_a_973_);
lean_inc(v___y_979_);
lean_inc_ref(v___y_978_);
lean_inc(v___y_977_);
lean_inc_ref(v___y_976_);
lean_inc(v___y_975_);
lean_inc(v___y_974_);
v___x_991_ = lean_apply_8(v_f_971_, v___x_990_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, lean_box(0));
return v___x_991_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(lean_object* v_fvars_992_, lean_object* v_f_993_, lean_object* v_body_994_, lean_object* v_x_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_array_push(v_fvars_992_, v_x_995_);
v___x_1004_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_993_, v___x_1003_, v_body_994_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___boxed(lean_object* v_f_1005_, lean_object* v_fvars_1006_, lean_object* v_a_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_1005_, v_fvars_1006_, v_a_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec(v___y_1008_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(lean_object* v_f_1016_, lean_object* v_e_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_1026_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_1016_, v___x_1025_, v_e_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11___boxed(lean_object* v_f_1027_, lean_object* v_e_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v_f_1027_, v_e_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec(v___y_1029_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(lean_object* v_a_1037_, lean_object* v_x_1038_){
_start:
{
if (lean_obj_tag(v_x_1038_) == 0)
{
lean_object* v___x_1039_; 
v___x_1039_ = lean_box(0);
return v___x_1039_;
}
else
{
lean_object* v_key_1040_; lean_object* v_value_1041_; lean_object* v_tail_1042_; uint8_t v___x_1043_; 
v_key_1040_ = lean_ctor_get(v_x_1038_, 0);
v_value_1041_ = lean_ctor_get(v_x_1038_, 1);
v_tail_1042_ = lean_ctor_get(v_x_1038_, 2);
v___x_1043_ = lean_expr_eqv(v_key_1040_, v_a_1037_);
if (v___x_1043_ == 0)
{
v_x_1038_ = v_tail_1042_;
goto _start;
}
else
{
lean_object* v___x_1045_; 
lean_inc(v_value_1041_);
v___x_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1045_, 0, v_value_1041_);
return v___x_1045_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_a_1046_, lean_object* v_x_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1046_, v_x_1047_);
lean_dec(v_x_1047_);
lean_dec_ref(v_a_1046_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_m_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v_buckets_1051_; lean_object* v___x_1052_; uint64_t v___x_1053_; uint64_t v___x_1054_; uint64_t v___x_1055_; uint64_t v_fold_1056_; uint64_t v___x_1057_; uint64_t v___x_1058_; uint64_t v___x_1059_; size_t v___x_1060_; size_t v___x_1061_; size_t v___x_1062_; size_t v___x_1063_; size_t v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v_buckets_1051_ = lean_ctor_get(v_m_1049_, 1);
v___x_1052_ = lean_array_get_size(v_buckets_1051_);
v___x_1053_ = l_Lean_Expr_hash(v_a_1050_);
v___x_1054_ = 32ULL;
v___x_1055_ = lean_uint64_shift_right(v___x_1053_, v___x_1054_);
v_fold_1056_ = lean_uint64_xor(v___x_1053_, v___x_1055_);
v___x_1057_ = 16ULL;
v___x_1058_ = lean_uint64_shift_right(v_fold_1056_, v___x_1057_);
v___x_1059_ = lean_uint64_xor(v_fold_1056_, v___x_1058_);
v___x_1060_ = lean_uint64_to_usize(v___x_1059_);
v___x_1061_ = lean_usize_of_nat(v___x_1052_);
v___x_1062_ = ((size_t)1ULL);
v___x_1063_ = lean_usize_sub(v___x_1061_, v___x_1062_);
v___x_1064_ = lean_usize_land(v___x_1060_, v___x_1063_);
v___x_1065_ = lean_array_uget_borrowed(v_buckets_1051_, v___x_1064_);
v___x_1066_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1050_, v___x_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_m_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1067_, v_a_1068_);
lean_dec_ref(v_a_1068_);
lean_dec_ref(v_m_1067_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_object* v_00_u03b1_1070_, lean_object* v_x_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_apply_1(v_x_1071_, lean_box(0));
v___x_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0___boxed(lean_object* v_00_u03b1_1080_, lean_object* v_x_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(v_00_u03b1_1080_, v_x_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(lean_object* v_x_1089_, lean_object* v_x_1090_){
_start:
{
if (lean_obj_tag(v_x_1090_) == 0)
{
return v_x_1089_;
}
else
{
lean_object* v_key_1091_; lean_object* v_value_1092_; lean_object* v_tail_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1116_; 
v_key_1091_ = lean_ctor_get(v_x_1090_, 0);
v_value_1092_ = lean_ctor_get(v_x_1090_, 1);
v_tail_1093_ = lean_ctor_get(v_x_1090_, 2);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_x_1090_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1095_ = v_x_1090_;
v_isShared_1096_ = v_isSharedCheck_1116_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_tail_1093_);
lean_inc(v_value_1092_);
lean_inc(v_key_1091_);
lean_dec(v_x_1090_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1116_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; uint64_t v___x_1098_; uint64_t v___x_1099_; uint64_t v___x_1100_; uint64_t v_fold_1101_; uint64_t v___x_1102_; uint64_t v___x_1103_; uint64_t v___x_1104_; size_t v___x_1105_; size_t v___x_1106_; size_t v___x_1107_; size_t v___x_1108_; size_t v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1112_; 
v___x_1097_ = lean_array_get_size(v_x_1089_);
v___x_1098_ = l_Lean_Expr_hash(v_key_1091_);
v___x_1099_ = 32ULL;
v___x_1100_ = lean_uint64_shift_right(v___x_1098_, v___x_1099_);
v_fold_1101_ = lean_uint64_xor(v___x_1098_, v___x_1100_);
v___x_1102_ = 16ULL;
v___x_1103_ = lean_uint64_shift_right(v_fold_1101_, v___x_1102_);
v___x_1104_ = lean_uint64_xor(v_fold_1101_, v___x_1103_);
v___x_1105_ = lean_uint64_to_usize(v___x_1104_);
v___x_1106_ = lean_usize_of_nat(v___x_1097_);
v___x_1107_ = ((size_t)1ULL);
v___x_1108_ = lean_usize_sub(v___x_1106_, v___x_1107_);
v___x_1109_ = lean_usize_land(v___x_1105_, v___x_1108_);
v___x_1110_ = lean_array_uget_borrowed(v_x_1089_, v___x_1109_);
lean_inc(v___x_1110_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 2, v___x_1110_);
v___x_1112_ = v___x_1095_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_key_1091_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_value_1092_);
lean_ctor_set(v_reuseFailAlloc_1115_, 2, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_array_uset(v_x_1089_, v___x_1109_, v___x_1112_);
v_x_1089_ = v___x_1113_;
v_x_1090_ = v_tail_1093_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(lean_object* v_i_1117_, lean_object* v_source_1118_, lean_object* v_target_1119_){
_start:
{
lean_object* v___x_1120_; uint8_t v___x_1121_; 
v___x_1120_ = lean_array_get_size(v_source_1118_);
v___x_1121_ = lean_nat_dec_lt(v_i_1117_, v___x_1120_);
if (v___x_1121_ == 0)
{
lean_dec_ref(v_source_1118_);
lean_dec(v_i_1117_);
return v_target_1119_;
}
else
{
lean_object* v_es_1122_; lean_object* v___x_1123_; lean_object* v_source_1124_; lean_object* v_target_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v_es_1122_ = lean_array_fget(v_source_1118_, v_i_1117_);
v___x_1123_ = lean_box(0);
v_source_1124_ = lean_array_fset(v_source_1118_, v_i_1117_, v___x_1123_);
v_target_1125_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_target_1119_, v_es_1122_);
v___x_1126_ = lean_unsigned_to_nat(1u);
v___x_1127_ = lean_nat_add(v_i_1117_, v___x_1126_);
lean_dec(v_i_1117_);
v_i_1117_ = v___x_1127_;
v_source_1118_ = v_source_1124_;
v_target_1119_ = v_target_1125_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(lean_object* v_data_1129_){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v_nbuckets_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1130_ = lean_array_get_size(v_data_1129_);
v___x_1131_ = lean_unsigned_to_nat(2u);
v_nbuckets_1132_ = lean_nat_mul(v___x_1130_, v___x_1131_);
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = lean_box(0);
v___x_1135_ = lean_mk_array(v_nbuckets_1132_, v___x_1134_);
v___x_1136_ = lean_array_propagate_mark(v_data_1129_, v___x_1135_);
v___x_1137_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v___x_1133_, v_data_1129_, v___x_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(lean_object* v_a_1138_, lean_object* v_b_1139_, lean_object* v_x_1140_){
_start:
{
if (lean_obj_tag(v_x_1140_) == 0)
{
lean_dec(v_b_1139_);
lean_dec_ref(v_a_1138_);
return v_x_1140_;
}
else
{
lean_object* v_key_1141_; lean_object* v_value_1142_; lean_object* v_tail_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1155_; 
v_key_1141_ = lean_ctor_get(v_x_1140_, 0);
v_value_1142_ = lean_ctor_get(v_x_1140_, 1);
v_tail_1143_ = lean_ctor_get(v_x_1140_, 2);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_x_1140_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1145_ = v_x_1140_;
v_isShared_1146_ = v_isSharedCheck_1155_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_tail_1143_);
lean_inc(v_value_1142_);
lean_inc(v_key_1141_);
lean_dec(v_x_1140_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1155_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
uint8_t v___x_1147_; 
v___x_1147_ = lean_expr_eqv(v_key_1141_, v_a_1138_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1148_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1138_, v_b_1139_, v_tail_1143_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 2, v___x_1148_);
v___x_1150_ = v___x_1145_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_key_1141_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_value_1142_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
else
{
lean_object* v___x_1153_; 
lean_dec(v_value_1142_);
lean_dec(v_key_1141_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v_b_1139_);
lean_ctor_set(v___x_1145_, 0, v_a_1138_);
v___x_1153_ = v___x_1145_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1138_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_b_1139_);
lean_ctor_set(v_reuseFailAlloc_1154_, 2, v_tail_1143_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(lean_object* v_a_1156_, lean_object* v_x_1157_){
_start:
{
if (lean_obj_tag(v_x_1157_) == 0)
{
uint8_t v___x_1158_; 
v___x_1158_ = 0;
return v___x_1158_;
}
else
{
lean_object* v_key_1159_; lean_object* v_tail_1160_; uint8_t v___x_1161_; 
v_key_1159_ = lean_ctor_get(v_x_1157_, 0);
v_tail_1160_ = lean_ctor_get(v_x_1157_, 2);
v___x_1161_ = lean_expr_eqv(v_key_1159_, v_a_1156_);
if (v___x_1161_ == 0)
{
v_x_1157_ = v_tail_1160_;
goto _start;
}
else
{
return v___x_1161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg___boxed(lean_object* v_a_1163_, lean_object* v_x_1164_){
_start:
{
uint8_t v_res_1165_; lean_object* v_r_1166_; 
v_res_1165_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1163_, v_x_1164_);
lean_dec(v_x_1164_);
lean_dec_ref(v_a_1163_);
v_r_1166_ = lean_box(v_res_1165_);
return v_r_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(lean_object* v_m_1167_, lean_object* v_a_1168_, lean_object* v_b_1169_){
_start:
{
lean_object* v_size_1170_; lean_object* v_buckets_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1214_; 
v_size_1170_ = lean_ctor_get(v_m_1167_, 0);
v_buckets_1171_ = lean_ctor_get(v_m_1167_, 1);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_m_1167_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1173_ = v_m_1167_;
v_isShared_1174_ = v_isSharedCheck_1214_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_buckets_1171_);
lean_inc(v_size_1170_);
lean_dec(v_m_1167_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1214_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1175_; uint64_t v___x_1176_; uint64_t v___x_1177_; uint64_t v___x_1178_; uint64_t v_fold_1179_; uint64_t v___x_1180_; uint64_t v___x_1181_; uint64_t v___x_1182_; size_t v___x_1183_; size_t v___x_1184_; size_t v___x_1185_; size_t v___x_1186_; size_t v___x_1187_; lean_object* v_bkt_1188_; uint8_t v___x_1189_; 
v___x_1175_ = lean_array_get_size(v_buckets_1171_);
v___x_1176_ = l_Lean_Expr_hash(v_a_1168_);
v___x_1177_ = 32ULL;
v___x_1178_ = lean_uint64_shift_right(v___x_1176_, v___x_1177_);
v_fold_1179_ = lean_uint64_xor(v___x_1176_, v___x_1178_);
v___x_1180_ = 16ULL;
v___x_1181_ = lean_uint64_shift_right(v_fold_1179_, v___x_1180_);
v___x_1182_ = lean_uint64_xor(v_fold_1179_, v___x_1181_);
v___x_1183_ = lean_uint64_to_usize(v___x_1182_);
v___x_1184_ = lean_usize_of_nat(v___x_1175_);
v___x_1185_ = ((size_t)1ULL);
v___x_1186_ = lean_usize_sub(v___x_1184_, v___x_1185_);
v___x_1187_ = lean_usize_land(v___x_1183_, v___x_1186_);
v_bkt_1188_ = lean_array_uget_borrowed(v_buckets_1171_, v___x_1187_);
v___x_1189_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1168_, v_bkt_1188_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; lean_object* v_size_x27_1191_; lean_object* v___x_1192_; lean_object* v_buckets_x27_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; 
v___x_1190_ = lean_unsigned_to_nat(1u);
v_size_x27_1191_ = lean_nat_add(v_size_1170_, v___x_1190_);
lean_dec(v_size_1170_);
lean_inc(v_bkt_1188_);
v___x_1192_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1192_, 0, v_a_1168_);
lean_ctor_set(v___x_1192_, 1, v_b_1169_);
lean_ctor_set(v___x_1192_, 2, v_bkt_1188_);
v_buckets_x27_1193_ = lean_array_uset(v_buckets_1171_, v___x_1187_, v___x_1192_);
v___x_1194_ = lean_unsigned_to_nat(4u);
v___x_1195_ = lean_nat_mul(v_size_x27_1191_, v___x_1194_);
v___x_1196_ = lean_unsigned_to_nat(3u);
v___x_1197_ = lean_nat_div(v___x_1195_, v___x_1196_);
lean_dec(v___x_1195_);
v___x_1198_ = lean_array_get_size(v_buckets_x27_1193_);
v___x_1199_ = lean_nat_dec_le(v___x_1197_, v___x_1198_);
lean_dec(v___x_1197_);
if (v___x_1199_ == 0)
{
lean_object* v_val_1200_; lean_object* v___x_1202_; 
v_val_1200_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_buckets_x27_1193_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 1, v_val_1200_);
lean_ctor_set(v___x_1173_, 0, v_size_x27_1191_);
v___x_1202_ = v___x_1173_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_size_x27_1191_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_val_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
else
{
lean_object* v___x_1205_; 
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 1, v_buckets_x27_1193_);
lean_ctor_set(v___x_1173_, 0, v_size_x27_1191_);
v___x_1205_ = v___x_1173_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_size_x27_1191_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_buckets_x27_1193_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
else
{
lean_object* v___x_1207_; lean_object* v_buckets_x27_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
lean_inc(v_bkt_1188_);
v___x_1207_ = lean_box(0);
v_buckets_x27_1208_ = lean_array_uset(v_buckets_1171_, v___x_1187_, v___x_1207_);
v___x_1209_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1168_, v_b_1169_, v_bkt_1188_);
v___x_1210_ = lean_array_uset(v_buckets_x27_1208_, v___x_1187_, v___x_1209_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 1, v___x_1210_);
v___x_1212_ = v___x_1173_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_size_1170_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(lean_object* v_a_1215_, lean_object* v_e_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1219_ = lean_st_ref_take(v_a_1215_);
v___x_1220_ = lean_box(0);
v___x_1221_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v___x_1219_, v_e_1216_, v_a_1217_);
v___x_1222_ = lean_st_ref_put(v_a_1215_, v___x_1221_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed(lean_object* v_a_1223_, lean_object* v_e_1224_, lean_object* v_a_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(v_a_1223_, v_e_1224_, v_a_1225_);
lean_dec(v_a_1223_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1228_, lean_object* v_e_1229_, lean_object* v_a_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1228_, v_e_1229_, v_a_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec(v_a_1230_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(lean_object* v_fn_1238_, lean_object* v_e_1239_, lean_object* v_a_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v_a_1248_; lean_object* v___y_1260_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
lean_inc(v_a_1240_);
v___x_1262_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1262_, 0, lean_box(0));
lean_closure_set(v___x_1262_, 1, lean_box(0));
lean_closure_set(v___x_1262_, 2, v_a_1240_);
v___x_1263_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___x_1262_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1300_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1266_ = v___x_1263_;
v_isShared_1267_ = v_isSharedCheck_1300_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1263_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1300_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_a_1264_, v_e_1239_);
lean_dec(v_a_1264_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v___x_1269_; 
lean_del_object(v___x_1266_);
lean_inc_ref(v_fn_1238_);
lean_inc(v___y_1245_);
lean_inc_ref(v___y_1244_);
lean_inc(v___y_1243_);
lean_inc_ref(v___y_1242_);
lean_inc(v___y_1241_);
lean_inc_ref(v_e_1239_);
v___x_1269_ = lean_apply_7(v_fn_1238_, v_e_1239_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, lean_box(0));
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; uint8_t v___x_1271_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v___x_1269_, 1);
v___x_1271_ = lean_unbox(v_a_1270_);
lean_dec(v_a_1270_);
if (v___x_1271_ == 0)
{
lean_object* v___x_1272_; 
lean_dec_ref(v_fn_1238_);
v___x_1272_ = lean_box(0);
v_a_1248_ = v___x_1272_;
goto v___jp_1247_;
}
else
{
switch(lean_obj_tag(v_e_1239_))
{
case 7:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1273_, 0, v_fn_1238_);
lean_inc_ref(v_e_1239_);
v___x_1274_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v___x_1273_, v_e_1239_, v_a_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
v___y_1260_ = v___x_1274_;
goto v___jp_1259_;
}
case 6:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1275_, 0, v_fn_1238_);
lean_inc_ref(v_e_1239_);
v___x_1276_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v___x_1275_, v_e_1239_, v_a_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
v___y_1260_ = v___x_1276_;
goto v___jp_1259_;
}
case 8:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1277_, 0, v_fn_1238_);
lean_inc_ref(v_e_1239_);
v___x_1278_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v___x_1277_, v_e_1239_, v_a_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
v___y_1260_ = v___x_1278_;
goto v___jp_1259_;
}
case 5:
{
lean_object* v_fn_1279_; lean_object* v_arg_1280_; lean_object* v___x_1281_; 
v_fn_1279_ = lean_ctor_get(v_e_1239_, 0);
v_arg_1280_ = lean_ctor_get(v_e_1239_, 1);
lean_inc_ref(v_fn_1279_);
lean_inc_ref(v_fn_1238_);
v___x_1281_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1238_, v_fn_1279_, v_a_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v___x_1282_; 
lean_dec_ref_known(v___x_1281_, 1);
lean_inc_ref(v_arg_1280_);
v___x_1282_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1238_, v_arg_1280_, v_a_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
v___y_1260_ = v___x_1282_;
goto v___jp_1259_;
}
else
{
lean_dec_ref(v_fn_1238_);
v___y_1260_ = v___x_1281_;
goto v___jp_1259_;
}
}
case 10:
{
lean_object* v_expr_1283_; lean_object* v___x_1284_; 
v_expr_1283_ = lean_ctor_get(v_e_1239_, 1);
lean_inc_ref(v_expr_1283_);
v___x_1284_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1238_, v_expr_1283_, v_a_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
v___y_1260_ = v___x_1284_;
goto v___jp_1259_;
}
case 11:
{
lean_object* v_struct_1285_; lean_object* v___x_1286_; 
v_struct_1285_ = lean_ctor_get(v_e_1239_, 2);
lean_inc_ref(v_struct_1285_);
v___x_1286_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1238_, v_struct_1285_, v_a_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
v___y_1260_ = v___x_1286_;
goto v___jp_1259_;
}
default: 
{
lean_object* v___x_1287_; 
lean_dec_ref(v_fn_1238_);
v___x_1287_ = lean_box(0);
v_a_1248_ = v___x_1287_;
goto v___jp_1247_;
}
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref(v_e_1239_);
lean_dec_ref(v_fn_1238_);
v_a_1288_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1269_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1269_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
else
{
lean_object* v_val_1296_; lean_object* v___x_1298_; 
lean_dec_ref(v_e_1239_);
lean_dec_ref(v_fn_1238_);
v_val_1296_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_val_1296_);
lean_dec_ref_known(v___x_1268_, 1);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v_val_1296_);
v___x_1298_ = v___x_1266_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_val_1296_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
lean_dec_ref(v_e_1239_);
lean_dec_ref(v_fn_1238_);
v_a_1301_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1263_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1263_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
v___jp_1247_:
{
lean_object* v___f_1249_; lean_object* v___x_1250_; 
lean_inc(v_a_1240_);
v___f_1249_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1249_, 0, v_a_1240_);
lean_closure_set(v___f_1249_, 1, v_e_1239_);
lean_closure_set(v___f_1249_, 2, v_a_1248_);
v___x_1250_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___f_1249_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1257_ == 0)
{
lean_object* v_unused_1258_; 
v_unused_1258_ = lean_ctor_get(v___x_1250_, 0);
lean_dec(v_unused_1258_);
v___x_1252_ = v___x_1250_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_dec(v___x_1250_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 0, v_a_1248_);
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1248_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
else
{
return v___x_1250_;
}
}
v___jp_1259_:
{
if (lean_obj_tag(v___y_1260_) == 0)
{
lean_object* v_a_1261_; 
v_a_1261_ = lean_ctor_get(v___y_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref_known(v___y_1260_, 1);
v_a_1248_ = v_a_1261_;
goto v___jp_1247_;
}
else
{
lean_dec_ref(v_e_1239_);
return v___y_1260_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = lean_box(0);
v___x_1310_ = lean_unsigned_to_nat(16u);
v___x_1311_ = lean_mk_array(v___x_1310_, v___x_1309_);
return v___x_1311_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1312_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0);
v___x_1313_ = lean_unsigned_to_nat(0u);
v___x_1314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1313_);
lean_ctor_set(v___x_1314_, 1, v___x_1312_);
return v___x_1314_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1);
v___x_1316_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1316_, 0, lean_box(0));
lean_closure_set(v___x_1316_, 1, lean_box(0));
lean_closure_set(v___x_1316_, 2, v___x_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(lean_object* v_input_1317_, lean_object* v_fn_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v_a_1327_; lean_object* v___x_1328_; 
v___x_1325_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2);
v___x_1326_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1325_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1327_);
lean_dec_ref(v___x_1326_);
v___x_1328_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1318_, v_input_1317_, v_a_1327_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1329_);
lean_dec_ref_known(v___x_1328_, 1);
v___x_1330_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1330_, 0, lean_box(0));
lean_closure_set(v___x_1330_, 1, lean_box(0));
lean_closure_set(v___x_1330_, 2, v_a_1327_);
v___x_1331_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1330_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1338_ == 0)
{
lean_object* v_unused_1339_; 
v_unused_1339_ = lean_ctor_get(v___x_1331_, 0);
lean_dec(v_unused_1339_);
v___x_1333_ = v___x_1331_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_dec(v___x_1331_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v_a_1329_);
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1329_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
else
{
lean_dec(v_a_1327_);
return v___x_1328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___boxed(lean_object* v_input_1340_, lean_object* v_fn_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1340_, v_fn_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(lean_object* v_input_1349_, lean_object* v_fn_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v___f_1357_; lean_object* v___x_1358_; 
v___f_1357_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1357_, 0, v_fn_1350_);
v___x_1358_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1349_, v___f_1357_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___boxed(lean_object* v_input_1359_, lean_object* v_fn_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_input_1359_, v_fn_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v___y_1361_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(lean_object* v_fn_1368_, lean_object* v_x_1369_, lean_object* v_x_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
if (lean_obj_tag(v_x_1370_) == 0)
{
lean_object* v___x_1377_; 
lean_dec_ref(v_fn_1368_);
v___x_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1377_, 0, v_x_1369_);
return v___x_1377_;
}
else
{
lean_object* v_head_1378_; lean_object* v_tail_1379_; lean_object* v_type_1380_; lean_object* v___x_1381_; 
v_head_1378_ = lean_ctor_get(v_x_1370_, 0);
lean_inc(v_head_1378_);
v_tail_1379_ = lean_ctor_get(v_x_1370_, 1);
lean_inc(v_tail_1379_);
lean_dec_ref_known(v_x_1370_, 2);
v_type_1380_ = lean_ctor_get(v_head_1378_, 1);
lean_inc_ref(v_type_1380_);
lean_dec(v_head_1378_);
lean_inc_ref(v_fn_1368_);
v___x_1381_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1380_, v_fn_1368_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1381_, 1);
v_x_1369_ = v_a_1382_;
v_x_1370_ = v_tail_1379_;
goto _start;
}
else
{
lean_dec(v_tail_1379_);
lean_dec_ref(v_fn_1368_);
return v___x_1381_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4___boxed(lean_object* v_fn_1384_, lean_object* v_x_1385_, lean_object* v_x_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1384_, v_x_1385_, v_x_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(lean_object* v_fn_1394_, lean_object* v_x_1395_, lean_object* v_x_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
if (lean_obj_tag(v_x_1396_) == 0)
{
lean_object* v___x_1403_; 
lean_dec_ref(v_fn_1394_);
v___x_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1403_, 0, v_x_1395_);
return v___x_1403_;
}
else
{
lean_object* v_head_1404_; lean_object* v_tail_1405_; lean_object* v___y_1407_; lean_object* v_type_1410_; lean_object* v_ctors_1411_; lean_object* v___x_1412_; 
v_head_1404_ = lean_ctor_get(v_x_1396_, 0);
lean_inc(v_head_1404_);
v_tail_1405_ = lean_ctor_get(v_x_1396_, 1);
lean_inc(v_tail_1405_);
lean_dec_ref_known(v_x_1396_, 2);
v_type_1410_ = lean_ctor_get(v_head_1404_, 1);
lean_inc_ref(v_type_1410_);
v_ctors_1411_ = lean_ctor_get(v_head_1404_, 2);
lean_inc(v_ctors_1411_);
lean_dec(v_head_1404_);
lean_inc_ref(v_fn_1394_);
v___x_1412_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1410_, v_fn_1394_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1414_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref_known(v___x_1412_, 1);
lean_inc_ref(v_fn_1394_);
v___x_1414_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1394_, v_a_1413_, v_ctors_1411_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
v___y_1407_ = v___x_1414_;
goto v___jp_1406_;
}
else
{
lean_dec(v_ctors_1411_);
v___y_1407_ = v___x_1412_;
goto v___jp_1406_;
}
v___jp_1406_:
{
if (lean_obj_tag(v___y_1407_) == 0)
{
lean_object* v_a_1408_; 
v_a_1408_ = lean_ctor_get(v___y_1407_, 0);
lean_inc(v_a_1408_);
lean_dec_ref_known(v___y_1407_, 1);
v_x_1395_ = v_a_1408_;
v_x_1396_ = v_tail_1405_;
goto _start;
}
else
{
lean_dec(v_tail_1405_);
lean_dec_ref(v_fn_1394_);
return v___y_1407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6___boxed(lean_object* v_fn_1415_, lean_object* v_x_1416_, lean_object* v_x_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1415_, v_x_1416_, v_x_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(lean_object* v_fn_1425_, lean_object* v_x_1426_, lean_object* v_x_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
if (lean_obj_tag(v_x_1427_) == 0)
{
lean_object* v___x_1434_; 
lean_dec_ref(v_fn_1425_);
v___x_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1434_, 0, v_x_1426_);
return v___x_1434_;
}
else
{
lean_object* v_head_1435_; lean_object* v_tail_1436_; lean_object* v___y_1438_; lean_object* v_toConstantVal_1441_; lean_object* v_value_1442_; lean_object* v_type_1443_; lean_object* v___x_1444_; 
v_head_1435_ = lean_ctor_get(v_x_1427_, 0);
lean_inc(v_head_1435_);
v_tail_1436_ = lean_ctor_get(v_x_1427_, 1);
lean_inc(v_tail_1436_);
lean_dec_ref_known(v_x_1427_, 2);
v_toConstantVal_1441_ = lean_ctor_get(v_head_1435_, 0);
lean_inc_ref(v_toConstantVal_1441_);
v_value_1442_ = lean_ctor_get(v_head_1435_, 1);
lean_inc_ref(v_value_1442_);
lean_dec(v_head_1435_);
v_type_1443_ = lean_ctor_get(v_toConstantVal_1441_, 2);
lean_inc_ref(v_type_1443_);
lean_dec_ref(v_toConstantVal_1441_);
lean_inc_ref(v_fn_1425_);
v___x_1444_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1443_, v_fn_1425_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v___x_1445_; 
lean_dec_ref_known(v___x_1444_, 1);
lean_inc_ref(v_fn_1425_);
v___x_1445_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1442_, v_fn_1425_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
v___y_1438_ = v___x_1445_;
goto v___jp_1437_;
}
else
{
lean_dec_ref(v_value_1442_);
v___y_1438_ = v___x_1444_;
goto v___jp_1437_;
}
v___jp_1437_:
{
if (lean_obj_tag(v___y_1438_) == 0)
{
lean_object* v_a_1439_; 
v_a_1439_ = lean_ctor_get(v___y_1438_, 0);
lean_inc(v_a_1439_);
lean_dec_ref_known(v___y_1438_, 1);
v_x_1426_ = v_a_1439_;
v_x_1427_ = v_tail_1436_;
goto _start;
}
else
{
lean_dec(v_tail_1436_);
lean_dec_ref(v_fn_1425_);
return v___y_1438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1446_, lean_object* v_x_1447_, lean_object* v_x_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1446_, v_x_1447_, v_x_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(lean_object* v_fn_1456_, lean_object* v_d_1457_, lean_object* v_a_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
switch(lean_obj_tag(v_d_1457_))
{
case 0:
{
lean_object* v_val_1465_; lean_object* v_toConstantVal_1466_; lean_object* v_type_1467_; lean_object* v___x_1468_; 
v_val_1465_ = lean_ctor_get(v_d_1457_, 0);
lean_inc_ref(v_val_1465_);
lean_dec_ref_known(v_d_1457_, 1);
v_toConstantVal_1466_ = lean_ctor_get(v_val_1465_, 0);
lean_inc_ref(v_toConstantVal_1466_);
lean_dec_ref(v_val_1465_);
v_type_1467_ = lean_ctor_get(v_toConstantVal_1466_, 2);
lean_inc_ref(v_type_1467_);
lean_dec_ref(v_toConstantVal_1466_);
v___x_1468_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1467_, v_fn_1456_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
return v___x_1468_;
}
case 4:
{
lean_object* v___x_1469_; 
lean_dec_ref(v_fn_1456_);
v___x_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1469_, 0, v_a_1458_);
return v___x_1469_;
}
case 5:
{
lean_object* v_defns_1470_; lean_object* v___x_1471_; 
v_defns_1470_ = lean_ctor_get(v_d_1457_, 0);
lean_inc(v_defns_1470_);
lean_dec_ref_known(v_d_1457_, 1);
v___x_1471_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1456_, v_a_1458_, v_defns_1470_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
return v___x_1471_;
}
case 6:
{
lean_object* v_types_1472_; lean_object* v___x_1473_; 
v_types_1472_ = lean_ctor_get(v_d_1457_, 2);
lean_inc(v_types_1472_);
lean_dec_ref_known(v_d_1457_, 3);
v___x_1473_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1456_, v_a_1458_, v_types_1472_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
return v___x_1473_;
}
default: 
{
lean_object* v_val_1474_; lean_object* v_toConstantVal_1475_; lean_object* v_value_1476_; lean_object* v_type_1477_; lean_object* v___x_1478_; 
v_val_1474_ = lean_ctor_get(v_d_1457_, 0);
lean_inc_ref(v_val_1474_);
lean_dec(v_d_1457_);
v_toConstantVal_1475_ = lean_ctor_get(v_val_1474_, 0);
lean_inc_ref(v_toConstantVal_1475_);
v_value_1476_ = lean_ctor_get(v_val_1474_, 1);
lean_inc_ref(v_value_1476_);
lean_dec_ref(v_val_1474_);
v_type_1477_ = lean_ctor_get(v_toConstantVal_1475_, 2);
lean_inc_ref(v_type_1477_);
lean_dec_ref(v_toConstantVal_1475_);
lean_inc_ref(v_fn_1456_);
v___x_1478_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1477_, v_fn_1456_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v___x_1479_; 
lean_dec_ref_known(v___x_1478_, 1);
v___x_1479_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1476_, v_fn_1456_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
return v___x_1479_;
}
else
{
lean_dec_ref(v_value_1476_);
lean_dec_ref(v_fn_1456_);
return v___x_1478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2___boxed(lean_object* v_fn_1480_, lean_object* v_d_1481_, lean_object* v_a_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1480_, v_d_1481_, v_a_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(lean_object* v_decl_1490_, lean_object* v_fn_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = lean_box(0);
v___x_1499_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1491_, v_decl_1490_, v___x_1498_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1___boxed(lean_object* v_decl_1500_, lean_object* v_fn_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1500_, v_fn_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
return v_res_1508_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__2(void){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__0, &l_Lean_snapshotEnvLinterOptions___closed__0_once, _init_l_Lean_snapshotEnvLinterOptions___closed__0);
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
return v___x_1513_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__3(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1514_ = lean_box(1);
v___x_1515_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3);
v___x_1516_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1517_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
lean_ctor_set(v___x_1517_, 1, v___x_1515_);
lean_ctor_set(v___x_1517_, 2, v___x_1514_);
return v___x_1517_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__4(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1518_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1519_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1520_ = lean_unsigned_to_nat(0u);
v___x_1521_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
lean_ctor_set(v___x_1521_, 2, v___x_1520_);
lean_ctor_set(v___x_1521_, 3, v___x_1520_);
lean_ctor_set(v___x_1521_, 4, v___x_1519_);
lean_ctor_set(v___x_1521_, 5, v___x_1519_);
lean_ctor_set(v___x_1521_, 6, v___x_1519_);
lean_ctor_set(v___x_1521_, 7, v___x_1519_);
lean_ctor_set(v___x_1521_, 8, v___x_1519_);
lean_ctor_set(v___x_1521_, 9, v___x_1519_);
lean_ctor_set(v___x_1521_, 10, v___x_1519_);
lean_ctor_set(v___x_1521_, 11, v___x_1518_);
return v___x_1521_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__5(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1523_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
lean_ctor_set(v___x_1523_, 1, v___x_1522_);
lean_ctor_set(v___x_1523_, 2, v___x_1522_);
lean_ctor_set(v___x_1523_, 3, v___x_1522_);
lean_ctor_set(v___x_1523_, 4, v___x_1522_);
lean_ctor_set(v___x_1523_, 5, v___x_1522_);
return v___x_1523_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__6(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1524_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
lean_ctor_set(v___x_1525_, 2, v___x_1524_);
lean_ctor_set(v___x_1525_, 3, v___x_1524_);
lean_ctor_set(v___x_1525_, 4, v___x_1524_);
return v___x_1525_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__7(void){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1526_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__6, &l_Lean_warnIfUsesSorry___closed__6_once, _init_l_Lean_warnIfUsesSorry___closed__6);
v___x_1527_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3);
v___x_1528_ = lean_box(1);
v___x_1529_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__5, &l_Lean_warnIfUsesSorry___closed__5_once, _init_l_Lean_warnIfUsesSorry___closed__5);
v___x_1530_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__4, &l_Lean_warnIfUsesSorry___closed__4_once, _init_l_Lean_warnIfUsesSorry___closed__4);
v___x_1531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
lean_ctor_set(v___x_1531_, 1, v___x_1529_);
lean_ctor_set(v___x_1531_, 2, v___x_1528_);
lean_ctor_set(v___x_1531_, 3, v___x_1527_);
lean_ctor_set(v___x_1531_, 4, v___x_1526_);
return v___x_1531_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__11(void){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__10));
v___x_1537_ = l_Lean_stringToMessageData(v___x_1536_);
return v___x_1537_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__13(void){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__12));
v___x_1540_ = l_Lean_stringToMessageData(v___x_1539_);
return v___x_1540_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__15(void){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__14));
v___x_1543_ = l_Lean_stringToMessageData(v___x_1542_);
return v___x_1543_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__16(void){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1544_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__15, &l_Lean_warnIfUsesSorry___closed__15_once, _init_l_Lean_warnIfUsesSorry___closed__15);
v___x_1545_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__9));
v___x_1546_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
lean_ctor_set(v___x_1546_, 1, v___x_1544_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry(lean_object* v_decl_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1554_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1551_);
v___x_1555_ = l_Lean_warn_sorry;
v___x_1556_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_1554_, v___x_1555_);
lean_dec_ref(v___x_1554_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
lean_dec(v_decl_1550_);
v___x_1557_ = lean_box(0);
v___x_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
return v___x_1558_;
}
else
{
lean_object* v___f_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v_messages_1565_; uint8_t v___x_1566_; 
v___f_1559_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__0));
v___x_1560_ = lean_box(1);
v___x_1561_ = lean_st_ref_get(v_a_1552_);
v_messages_1565_ = lean_ctor_get(v___x_1561_, 7);
lean_inc_ref(v_messages_1565_);
lean_dec(v___x_1561_);
v___x_1566_ = l_Lean_MessageLog_hasErrors(v_messages_1565_);
lean_dec_ref(v_messages_1565_);
if (v___x_1566_ == 0)
{
if (v___x_1556_ == 0)
{
lean_dec(v_decl_1550_);
goto v___jp_1562_;
}
else
{
uint8_t v___x_1567_; 
v___x_1567_ = l_Lean_Declaration_hasSorry(v_decl_1550_);
if (v___x_1567_ == 0)
{
lean_dec(v_decl_1550_);
goto v___jp_1562_;
}
else
{
lean_object* v___x_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; uint8_t v___x_1571_; uint8_t v___x_1572_; lean_object* v___x_1573_; uint64_t v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1568_ = lean_unsigned_to_nat(0u);
v___x_1569_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__1));
v___x_1570_ = 1;
v___x_1571_ = 0;
v___x_1572_ = 2;
v___x_1573_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_1573_, 0, v___x_1566_);
lean_ctor_set_uint8(v___x_1573_, 1, v___x_1566_);
lean_ctor_set_uint8(v___x_1573_, 2, v___x_1566_);
lean_ctor_set_uint8(v___x_1573_, 3, v___x_1566_);
lean_ctor_set_uint8(v___x_1573_, 4, v___x_1566_);
lean_ctor_set_uint8(v___x_1573_, 5, v___x_1567_);
lean_ctor_set_uint8(v___x_1573_, 6, v___x_1567_);
lean_ctor_set_uint8(v___x_1573_, 7, v___x_1566_);
lean_ctor_set_uint8(v___x_1573_, 8, v___x_1567_);
lean_ctor_set_uint8(v___x_1573_, 9, v___x_1570_);
lean_ctor_set_uint8(v___x_1573_, 10, v___x_1571_);
lean_ctor_set_uint8(v___x_1573_, 11, v___x_1567_);
lean_ctor_set_uint8(v___x_1573_, 12, v___x_1567_);
lean_ctor_set_uint8(v___x_1573_, 13, v___x_1567_);
lean_ctor_set_uint8(v___x_1573_, 14, v___x_1572_);
lean_ctor_set_uint8(v___x_1573_, 15, v___x_1567_);
lean_ctor_set_uint8(v___x_1573_, 16, v___x_1567_);
lean_ctor_set_uint8(v___x_1573_, 17, v___x_1567_);
lean_ctor_set_uint8(v___x_1573_, 18, v___x_1567_);
lean_ctor_set_uint8(v___x_1573_, 19, v___x_1566_);
v___x_1574_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1573_);
v___x_1575_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1575_, 0, v___x_1573_);
lean_ctor_set_uint64(v___x_1575_, sizeof(void*)*1, v___x_1574_);
v___x_1576_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__3, &l_Lean_warnIfUsesSorry___closed__3_once, _init_l_Lean_warnIfUsesSorry___closed__3);
v___x_1577_ = lean_box(0);
v___x_1578_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1578_, 0, v___x_1575_);
lean_ctor_set(v___x_1578_, 1, v___x_1560_);
lean_ctor_set(v___x_1578_, 2, v___x_1576_);
lean_ctor_set(v___x_1578_, 3, v___x_1569_);
lean_ctor_set(v___x_1578_, 4, v___x_1577_);
lean_ctor_set(v___x_1578_, 5, v___x_1568_);
lean_ctor_set(v___x_1578_, 6, v___x_1577_);
lean_ctor_set_uint8(v___x_1578_, sizeof(void*)*7, v___x_1566_);
lean_ctor_set_uint8(v___x_1578_, sizeof(void*)*7 + 1, v___x_1566_);
lean_ctor_set_uint8(v___x_1578_, sizeof(void*)*7 + 2, v___x_1566_);
lean_ctor_set_uint8(v___x_1578_, sizeof(void*)*7 + 3, v___x_1556_);
v___x_1579_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__7, &l_Lean_warnIfUsesSorry___closed__7_once, _init_l_Lean_warnIfUsesSorry___closed__7);
v___x_1580_ = lean_st_mk_ref(v___x_1579_);
v___x_1581_ = lean_st_mk_ref(v___x_1569_);
v___x_1582_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1550_, v___f_1559_, v___x_1581_, v___x_1578_, v___x_1580_, v_a_1551_, v_a_1552_);
lean_dec_ref_known(v___x_1578_, 7);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v_val_1586_; lean_object* v___x_1608_; size_t v_sz_1609_; size_t v___x_1610_; lean_object* v___x_1611_; lean_object* v_fst_1612_; 
lean_dec_ref_known(v___x_1582_, 1);
v___x_1583_ = lean_st_ref_get(v___x_1581_);
lean_dec(v___x_1581_);
v___x_1584_ = lean_st_ref_get(v___x_1580_);
lean_dec(v___x_1580_);
lean_dec(v___x_1584_);
v___x_1608_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__17));
v_sz_1609_ = lean_array_size(v___x_1583_);
v___x_1610_ = ((size_t)0ULL);
v___x_1611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v___x_1583_, v_sz_1609_, v___x_1610_, v___x_1608_);
v_fst_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_fst_1612_);
lean_dec_ref(v___x_1611_);
if (lean_obj_tag(v_fst_1612_) == 0)
{
goto v___jp_1602_;
}
else
{
lean_object* v_val_1613_; 
v_val_1613_ = lean_ctor_get(v_fst_1612_, 0);
lean_inc(v_val_1613_);
lean_dec_ref_known(v_fst_1612_, 1);
if (lean_obj_tag(v_val_1613_) == 0)
{
goto v___jp_1602_;
}
else
{
lean_object* v_val_1614_; 
lean_dec(v___x_1583_);
v_val_1614_ = lean_ctor_get(v_val_1613_, 0);
lean_inc(v_val_1614_);
lean_dec_ref_known(v_val_1613_, 1);
v_val_1586_ = v_val_1614_;
goto v___jp_1585_;
}
}
v___jp_1585_:
{
lean_object* v_snd_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1600_; 
v_snd_1587_ = lean_ctor_get(v_val_1586_, 1);
v_isSharedCheck_1600_ = !lean_is_exclusive(v_val_1586_);
if (v_isSharedCheck_1600_ == 0)
{
lean_object* v_unused_1601_; 
v_unused_1601_ = lean_ctor_get(v_val_1586_, 0);
lean_dec(v_unused_1601_);
v___x_1589_ = v_val_1586_;
v_isShared_1590_ = v_isSharedCheck_1600_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_snd_1587_);
lean_dec(v_val_1586_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1600_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1594_; 
v___x_1591_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__9));
v___x_1592_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__11, &l_Lean_warnIfUsesSorry___closed__11_once, _init_l_Lean_warnIfUsesSorry___closed__11);
if (v_isShared_1590_ == 0)
{
lean_ctor_set_tag(v___x_1589_, 7);
lean_ctor_set(v___x_1589_, 0, v___x_1592_);
v___x_1594_ = v___x_1589_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1592_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v_snd_1587_);
v___x_1594_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1595_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__13, &l_Lean_warnIfUsesSorry___closed__13_once, _init_l_Lean_warnIfUsesSorry___closed__13);
v___x_1596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1594_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
v___x_1597_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1591_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1597_, v_a_1551_, v_a_1552_);
return v___x_1598_;
}
}
}
v___jp_1602_:
{
lean_object* v___x_1603_; uint8_t v___x_1604_; 
v___x_1603_ = lean_array_get_size(v___x_1583_);
v___x_1604_ = lean_nat_dec_lt(v___x_1568_, v___x_1603_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
lean_dec(v___x_1583_);
v___x_1605_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__16, &l_Lean_warnIfUsesSorry___closed__16_once, _init_l_Lean_warnIfUsesSorry___closed__16);
v___x_1606_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1605_, v_a_1551_, v_a_1552_);
return v___x_1606_;
}
else
{
lean_object* v___x_1607_; 
v___x_1607_ = lean_array_fget(v___x_1583_, v___x_1568_);
lean_dec(v___x_1583_);
v_val_1586_ = v___x_1607_;
goto v___jp_1585_;
}
}
}
else
{
lean_dec(v___x_1581_);
lean_dec(v___x_1580_);
return v___x_1582_;
}
}
}
}
else
{
lean_dec(v_decl_1550_);
goto v___jp_1562_;
}
v___jp_1562_:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1563_ = lean_box(0);
v___x_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
return v___x_1564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___boxed(lean_object* v_decl_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lean_warnIfUsesSorry(v_decl_1615_, v_a_1616_, v_a_1617_);
lean_dec(v_a_1617_);
lean_dec_ref(v_a_1616_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1620_, lean_object* v_m_1621_, lean_object* v_a_1622_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1621_, v_a_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1624_, lean_object* v_m_1625_, lean_object* v_a_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(v_00_u03b2_1624_, v_m_1625_, v_a_1626_);
lean_dec_ref(v_a_1626_);
lean_dec_ref(v_m_1625_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_1628_, lean_object* v_m_1629_, lean_object* v_a_1630_, lean_object* v_b_1631_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_m_1629_, v_a_1630_, v_b_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_1633_, lean_object* v_a_1634_, lean_object* v_x_1635_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1634_, v_x_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1637_, lean_object* v_a_1638_, lean_object* v_x_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(v_00_u03b2_1637_, v_a_1638_, v_x_1639_);
lean_dec(v_x_1639_);
lean_dec_ref(v_a_1638_);
return v_res_1640_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(lean_object* v_00_u03b2_1641_, lean_object* v_a_1642_, lean_object* v_x_1643_){
_start:
{
uint8_t v___x_1644_; 
v___x_1644_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1642_, v_x_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___boxed(lean_object* v_00_u03b2_1645_, lean_object* v_a_1646_, lean_object* v_x_1647_){
_start:
{
uint8_t v_res_1648_; lean_object* v_r_1649_; 
v_res_1648_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(v_00_u03b2_1645_, v_a_1646_, v_x_1647_);
lean_dec(v_x_1647_);
lean_dec_ref(v_a_1646_);
v_r_1649_ = lean_box(v_res_1648_);
return v_r_1649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17(lean_object* v_00_u03b2_1650_, lean_object* v_data_1651_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_data_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18(lean_object* v_00_u03b2_1653_, lean_object* v_a_1654_, lean_object* v_b_1655_, lean_object* v_x_1656_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1654_, v_b_1655_, v_x_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(lean_object* v_00_u03b1_1658_, lean_object* v_name_1659_, uint8_t v_bi_1660_, lean_object* v_type_1661_, lean_object* v_k_1662_, uint8_t v_kind_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_1659_, v_bi_1660_, v_type_1661_, v_k_1662_, v_kind_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___boxed(lean_object* v_00_u03b1_1672_, lean_object* v_name_1673_, lean_object* v_bi_1674_, lean_object* v_type_1675_, lean_object* v_k_1676_, lean_object* v_kind_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
uint8_t v_bi_boxed_1685_; uint8_t v_kind_boxed_1686_; lean_object* v_res_1687_; 
v_bi_boxed_1685_ = lean_unbox(v_bi_1674_);
v_kind_boxed_1686_ = lean_unbox(v_kind_1677_);
v_res_1687_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(v_00_u03b1_1672_, v_name_1673_, v_bi_boxed_1685_, v_type_1675_, v_k_1676_, v_kind_boxed_1686_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec(v___y_1678_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(lean_object* v_00_u03b1_1688_, lean_object* v_name_1689_, lean_object* v_type_1690_, lean_object* v_val_1691_, lean_object* v_k_1692_, uint8_t v_nondep_1693_, uint8_t v_kind_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_1689_, v_type_1690_, v_val_1691_, v_k_1692_, v_nondep_1693_, v_kind_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___boxed(lean_object* v_00_u03b1_1703_, lean_object* v_name_1704_, lean_object* v_type_1705_, lean_object* v_val_1706_, lean_object* v_k_1707_, lean_object* v_nondep_1708_, lean_object* v_kind_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
uint8_t v_nondep_boxed_1717_; uint8_t v_kind_boxed_1718_; lean_object* v_res_1719_; 
v_nondep_boxed_1717_ = lean_unbox(v_nondep_1708_);
v_kind_boxed_1718_ = lean_unbox(v_kind_1709_);
v_res_1719_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(v_00_u03b1_1703_, v_name_1704_, v_type_1705_, v_val_1706_, v_k_1707_, v_nondep_boxed_1717_, v_kind_boxed_1718_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec(v___y_1710_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18(lean_object* v_00_u03b2_1720_, lean_object* v_i_1721_, lean_object* v_source_1722_, lean_object* v_target_1723_){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v_i_1721_, v_source_1722_, v_target_1723_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22(lean_object* v_00_u03b2_1725_, lean_object* v_x_1726_, lean_object* v_x_1727_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_x_1726_, v_x_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1778_; uint8_t v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1778_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1779_ = 0;
v___x_1780_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__20_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1781_ = l_Lean_registerTraceClass(v___x_1778_, v___x_1779_, v___x_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2____boxed(lean_object* v_a_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_();
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(lean_object* v_env_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v___x_1787_; lean_object* v_nextMacroScope_1788_; lean_object* v_ngen_1789_; lean_object* v_auxDeclNGen_1790_; lean_object* v_traceState_1791_; lean_object* v_recordedDeps_1792_; lean_object* v_messages_1793_; lean_object* v_infoState_1794_; lean_object* v_snapshotTasks_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1806_; 
v___x_1787_ = lean_st_ref_take(v___y_1785_);
v_nextMacroScope_1788_ = lean_ctor_get(v___x_1787_, 1);
v_ngen_1789_ = lean_ctor_get(v___x_1787_, 2);
v_auxDeclNGen_1790_ = lean_ctor_get(v___x_1787_, 3);
v_traceState_1791_ = lean_ctor_get(v___x_1787_, 4);
v_recordedDeps_1792_ = lean_ctor_get(v___x_1787_, 6);
v_messages_1793_ = lean_ctor_get(v___x_1787_, 7);
v_infoState_1794_ = lean_ctor_get(v___x_1787_, 8);
v_snapshotTasks_1795_ = lean_ctor_get(v___x_1787_, 9);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1806_ == 0)
{
lean_object* v_unused_1807_; lean_object* v_unused_1808_; 
v_unused_1807_ = lean_ctor_get(v___x_1787_, 5);
lean_dec(v_unused_1807_);
v_unused_1808_ = lean_ctor_get(v___x_1787_, 0);
lean_dec(v_unused_1808_);
v___x_1797_ = v___x_1787_;
v_isShared_1798_ = v_isSharedCheck_1806_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_snapshotTasks_1795_);
lean_inc(v_infoState_1794_);
lean_inc(v_messages_1793_);
lean_inc(v_recordedDeps_1792_);
lean_inc(v_traceState_1791_);
lean_inc(v_auxDeclNGen_1790_);
lean_inc(v_ngen_1789_);
lean_inc(v_nextMacroScope_1788_);
lean_dec(v___x_1787_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1806_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1802_; 
v___x_1799_ = lean_box(0);
v___x_1800_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 5, v___x_1800_);
lean_ctor_set(v___x_1797_, 0, v_env_1784_);
v___x_1802_ = v___x_1797_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_env_1784_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v_nextMacroScope_1788_);
lean_ctor_set(v_reuseFailAlloc_1805_, 2, v_ngen_1789_);
lean_ctor_set(v_reuseFailAlloc_1805_, 3, v_auxDeclNGen_1790_);
lean_ctor_set(v_reuseFailAlloc_1805_, 4, v_traceState_1791_);
lean_ctor_set(v_reuseFailAlloc_1805_, 5, v___x_1800_);
lean_ctor_set(v_reuseFailAlloc_1805_, 6, v_recordedDeps_1792_);
lean_ctor_set(v_reuseFailAlloc_1805_, 7, v_messages_1793_);
lean_ctor_set(v_reuseFailAlloc_1805_, 8, v_infoState_1794_);
lean_ctor_set(v_reuseFailAlloc_1805_, 9, v_snapshotTasks_1795_);
v___x_1802_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = lean_st_ref_put(v___y_1785_, v___x_1802_);
v___x_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1799_);
return v___x_1804_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg___boxed(lean_object* v_env_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1809_, v___y_1810_);
lean_dec(v___y_1810_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(lean_object* v_env_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1813_, v___y_1815_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___boxed(lean_object* v_env_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(v_env_1818_, v___y_1819_, v___y_1820_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
return v_res_1822_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1823_ = lean_box(0);
v___x_1824_ = l_Lean_interruptExceptionId;
v___x_1825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
lean_ctor_set(v___x_1825_, 1, v___x_1823_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg(){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1827_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v___y_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(lean_object* v_msg_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_ref_1835_; lean_object* v___x_1836_; lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1845_; 
v_ref_1835_ = lean_ctor_get(v___y_1832_, 2);
v___x_1836_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_1831_, v___y_1832_, v___y_1833_);
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1845_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1845_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1841_; lean_object* v___x_1843_; 
lean_inc(v_ref_1835_);
v___x_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1841_, 0, v_ref_1835_);
lean_ctor_set(v___x_1841_, 1, v_a_1837_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set_tag(v___x_1839_, 1);
lean_ctor_set(v___x_1839_, 0, v___x_1841_);
v___x_1843_ = v___x_1839_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msg_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_1846_, v___y_1847_, v___y_1848_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(lean_object* v_ex_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v___y_1856_; lean_object* v___y_1857_; 
if (lean_obj_tag(v_ex_1851_) == 16)
{
lean_object* v___x_1861_; lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
v___x_1861_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1861_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1861_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
else
{
v___y_1856_ = v___y_1852_;
v___y_1857_ = v___y_1853_;
goto v___jp_1855_;
}
v___jp_1855_:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1858_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1856_);
v___x_1859_ = l_Lean_Kernel_Exception_toMessageData(v_ex_1851_, v___x_1858_);
v___x_1860_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v___x_1859_, v___y_1856_, v___y_1857_);
return v___x_1860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg___boxed(lean_object* v_ex_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_1870_, v___y_1871_, v___y_1872_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(lean_object* v_x_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
if (lean_obj_tag(v_x_1875_) == 0)
{
lean_object* v_a_1879_; lean_object* v___x_1880_; 
v_a_1879_ = lean_ctor_get(v_x_1875_, 0);
lean_inc(v_a_1879_);
lean_dec_ref_known(v_x_1875_, 1);
v___x_1880_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_a_1879_, v___y_1876_, v___y_1877_);
return v___x_1880_;
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
v_a_1881_ = lean_ctor_get(v_x_1875_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v_x_1875_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v_x_1875_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v_x_1875_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
lean_ctor_set_tag(v___x_1883_, 0);
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg___boxed(lean_object* v_x_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_1889_, v___y_1890_, v___y_1891_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
return v_res_1893_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = lean_unsigned_to_nat(1u);
v___x_1901_ = l_Lean_Level_ofNat(v___x_1900_);
return v___x_1901_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1902_ = lean_box(0);
v___x_1903_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3);
v___x_1904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
lean_ctor_set(v___x_1904_, 1, v___x_1902_);
return v___x_1904_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1905_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4);
v___x_1906_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2));
v___x_1907_ = l_Lean_mkConst(v___x_1906_, v___x_1905_);
return v___x_1907_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = lean_unsigned_to_nat(0u);
v___x_1909_ = l_Lean_Level_ofNat(v___x_1908_);
return v___x_1909_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1910_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6);
v___x_1911_ = l_Lean_mkSort(v___x_1910_);
return v___x_1911_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11(void){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = lean_box(0);
v___x_1918_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__10));
v___x_1919_ = l_Lean_mkConst(v___x_1918_, v___x_1917_);
return v___x_1919_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12(void){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1920_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11);
v___x_1921_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7);
v___x_1922_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5);
v___x_1923_ = l_Lean_mkAppB(v___x_1922_, v___x_1921_, v___x_1920_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(lean_object* v_as_x27_1929_, lean_object* v_b_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
if (lean_obj_tag(v_as_x27_1929_) == 0)
{
lean_object* v___x_1934_; 
v___x_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1934_, 0, v_b_1930_);
return v___x_1934_;
}
else
{
lean_object* v_head_1935_; lean_object* v_tail_1936_; lean_object* v___x_1937_; lean_object* v___y_1939_; uint8_t v___y_1940_; lean_object* v_a_1944_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; uint8_t v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v_toCold_1954_; lean_object* v_env_1955_; lean_object* v_cancelTk_x3f_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
lean_dec_ref(v_b_1930_);
v_head_1935_ = lean_ctor_get(v_as_x27_1929_, 0);
v_tail_1936_ = lean_ctor_get(v_as_x27_1929_, 1);
v___x_1937_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0));
v___x_1947_ = lean_box(0);
v___x_1948_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12);
lean_inc(v_head_1935_);
v___x_1949_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1949_, 0, v_head_1935_);
lean_ctor_set(v___x_1949_, 1, v___x_1947_);
lean_ctor_set(v___x_1949_, 2, v___x_1948_);
v___x_1950_ = 0;
v___x_1951_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1951_, 0, v___x_1949_);
lean_ctor_set_uint8(v___x_1951_, sizeof(void*)*1, v___x_1950_);
v___x_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
v___x_1953_ = lean_st_ref_get(v___y_1932_);
v_toCold_1954_ = lean_ctor_get(v___y_1931_, 0);
v_env_1955_ = lean_ctor_get(v___x_1953_, 0);
lean_inc_ref(v_env_1955_);
lean_dec(v___x_1953_);
v_cancelTk_x3f_1956_ = lean_ctor_get(v_toCold_1954_, 10);
v___x_1957_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1931_);
v___x_1958_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_1955_, v___x_1957_, v___x_1952_, v_cancelTk_x3f_1956_);
lean_dec_ref_known(v___x_1952_, 1);
lean_dec_ref(v___x_1957_);
v___x_1959_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_1958_, v___y_1931_, v___y_1932_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; lean_object* v___x_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1969_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1960_);
lean_dec_ref_known(v___x_1959_, 1);
v___x_1961_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_1960_, v___y_1932_);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1969_ == 0)
{
lean_object* v_unused_1970_; 
v_unused_1970_ = lean_ctor_get(v___x_1961_, 0);
lean_dec(v_unused_1970_);
v___x_1963_ = v___x_1961_;
v_isShared_1964_ = v_isSharedCheck_1969_;
goto v_resetjp_1962_;
}
else
{
lean_dec(v___x_1961_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1969_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1965_; lean_object* v___x_1967_; 
v___x_1965_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__14));
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v___x_1965_);
v___x_1967_ = v___x_1963_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1965_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
else
{
lean_object* v_a_1971_; 
v_a_1971_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1971_);
lean_dec_ref_known(v___x_1959_, 1);
v_a_1944_ = v_a_1971_;
goto v___jp_1943_;
}
v___jp_1938_:
{
if (v___y_1940_ == 0)
{
lean_dec_ref(v___y_1939_);
v_as_x27_1929_ = v_tail_1936_;
v_b_1930_ = v___x_1937_;
goto _start;
}
else
{
lean_object* v___x_1942_; 
v___x_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1942_, 0, v___y_1939_);
return v___x_1942_;
}
}
v___jp_1943_:
{
uint8_t v___x_1945_; 
v___x_1945_ = l_Lean_Exception_isInterrupt(v_a_1944_);
if (v___x_1945_ == 0)
{
uint8_t v___x_1946_; 
lean_inc_ref(v_a_1944_);
v___x_1946_ = l_Lean_Exception_isRuntime(v_a_1944_);
v___y_1939_ = v_a_1944_;
v___y_1940_ = v___x_1946_;
goto v___jp_1938_;
}
else
{
v___y_1939_ = v_a_1944_;
v___y_1940_ = v___x_1945_;
goto v___jp_1938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___boxed(lean_object* v_as_x27_1972_, lean_object* v_b_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_1972_, v_b_1973_, v___y_1974_, v___y_1975_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v_as_x27_1972_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(lean_object* v_decl_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_){
_start:
{
lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_2011_; uint8_t v___y_2012_; lean_object* v_a_2015_; lean_object* v___y_2019_; uint8_t v___y_2020_; lean_object* v_a_2023_; 
switch(lean_obj_tag(v_decl_1978_))
{
case 1:
{
lean_object* v_val_2026_; lean_object* v_toConstantVal_2027_; uint8_t v___x_2028_; lean_object* v___x_2029_; lean_object* v_fallbackDecl_2030_; lean_object* v___x_2031_; lean_object* v_toCold_2032_; lean_object* v_env_2033_; lean_object* v_cancelTk_x3f_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v_val_2026_ = lean_ctor_get(v_decl_1978_, 0);
v_toConstantVal_2027_ = lean_ctor_get(v_val_2026_, 0);
v___x_2028_ = 0;
lean_inc_ref(v_toConstantVal_2027_);
v___x_2029_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2029_, 0, v_toConstantVal_2027_);
lean_ctor_set_uint8(v___x_2029_, sizeof(void*)*1, v___x_2028_);
v_fallbackDecl_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2030_, 0, v___x_2029_);
v___x_2031_ = lean_st_ref_get(v_a_1980_);
v_toCold_2032_ = lean_ctor_get(v_a_1979_, 0);
v_env_2033_ = lean_ctor_get(v___x_2031_, 0);
lean_inc_ref(v_env_2033_);
lean_dec(v___x_2031_);
v_cancelTk_x3f_2034_ = lean_ctor_get(v_toCold_2032_, 10);
v___x_2035_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1979_);
v___x_2036_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2033_, v___x_2035_, v_fallbackDecl_2030_, v_cancelTk_x3f_2034_);
lean_dec_ref_known(v_fallbackDecl_2030_, 1);
lean_dec_ref(v___x_2035_);
v___x_2037_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2036_, v_a_1979_, v_a_1980_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v___x_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2047_; 
lean_dec_ref_known(v_decl_1978_, 1);
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2038_);
lean_dec_ref_known(v___x_2037_, 1);
v___x_2039_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2038_, v_a_1980_);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2047_ == 0)
{
lean_object* v_unused_2048_; 
v_unused_2048_ = lean_ctor_get(v___x_2039_, 0);
lean_dec(v_unused_2048_);
v___x_2041_ = v___x_2039_;
v_isShared_2042_ = v_isSharedCheck_2047_;
goto v_resetjp_2040_;
}
else
{
lean_dec(v___x_2039_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2047_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2043_; lean_object* v___x_2045_; 
v___x_2043_ = lean_box(0);
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 0, v___x_2043_);
v___x_2045_ = v___x_2041_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2043_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
else
{
lean_object* v_a_2049_; 
v_a_2049_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2049_);
lean_dec_ref_known(v___x_2037_, 1);
v_a_2015_ = v_a_2049_;
goto v___jp_2014_;
}
}
case 2:
{
lean_object* v_val_2050_; lean_object* v_toConstantVal_2051_; uint8_t v___x_2052_; lean_object* v___x_2053_; lean_object* v_fallbackDecl_2054_; lean_object* v___x_2055_; lean_object* v_toCold_2056_; lean_object* v_env_2057_; lean_object* v_cancelTk_x3f_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v_val_2050_ = lean_ctor_get(v_decl_1978_, 0);
v_toConstantVal_2051_ = lean_ctor_get(v_val_2050_, 0);
v___x_2052_ = 0;
lean_inc_ref(v_toConstantVal_2051_);
v___x_2053_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2053_, 0, v_toConstantVal_2051_);
lean_ctor_set_uint8(v___x_2053_, sizeof(void*)*1, v___x_2052_);
v_fallbackDecl_2054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2054_, 0, v___x_2053_);
v___x_2055_ = lean_st_ref_get(v_a_1980_);
v_toCold_2056_ = lean_ctor_get(v_a_1979_, 0);
v_env_2057_ = lean_ctor_get(v___x_2055_, 0);
lean_inc_ref(v_env_2057_);
lean_dec(v___x_2055_);
v_cancelTk_x3f_2058_ = lean_ctor_get(v_toCold_2056_, 10);
v___x_2059_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1979_);
v___x_2060_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2057_, v___x_2059_, v_fallbackDecl_2054_, v_cancelTk_x3f_2058_);
lean_dec_ref_known(v_fallbackDecl_2054_, 1);
lean_dec_ref(v___x_2059_);
v___x_2061_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2060_, v_a_1979_, v_a_1980_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2071_; 
lean_dec_ref_known(v_decl_1978_, 1);
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2062_);
lean_dec_ref_known(v___x_2061_, 1);
v___x_2063_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2062_, v_a_1980_);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2071_ == 0)
{
lean_object* v_unused_2072_; 
v_unused_2072_ = lean_ctor_get(v___x_2063_, 0);
lean_dec(v_unused_2072_);
v___x_2065_ = v___x_2063_;
v_isShared_2066_ = v_isSharedCheck_2071_;
goto v_resetjp_2064_;
}
else
{
lean_dec(v___x_2063_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2071_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2067_ = lean_box(0);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v___x_2067_);
v___x_2069_ = v___x_2065_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2067_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
else
{
lean_object* v_a_2073_; 
v_a_2073_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2073_);
lean_dec_ref_known(v___x_2061_, 1);
v_a_2023_ = v_a_2073_;
goto v___jp_2022_;
}
}
default: 
{
v___y_1983_ = v_a_1979_;
v___y_1984_ = v_a_1980_;
goto v___jp_1982_;
}
}
v___jp_1982_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1985_ = l_Lean_Declaration_getNames(v_decl_1978_);
v___x_1986_ = lean_box(0);
v___x_1987_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0));
v___x_1988_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v___x_1985_, v___x_1987_, v___y_1983_, v___y_1984_);
lean_dec(v___x_1985_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2001_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1991_ = v___x_1988_;
v_isShared_1992_ = v_isSharedCheck_2001_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1988_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2001_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v_fst_1993_; 
v_fst_1993_ = lean_ctor_get(v_a_1989_, 0);
lean_inc(v_fst_1993_);
lean_dec(v_a_1989_);
if (lean_obj_tag(v_fst_1993_) == 0)
{
lean_object* v___x_1995_; 
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v___x_1986_);
v___x_1995_ = v___x_1991_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1986_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
else
{
lean_object* v_val_1997_; lean_object* v___x_1999_; 
v_val_1997_ = lean_ctor_get(v_fst_1993_, 0);
lean_inc(v_val_1997_);
lean_dec_ref_known(v_fst_1993_, 1);
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v_val_1997_);
v___x_1999_ = v___x_1991_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_val_1997_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
else
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
v_a_2002_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_1988_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_1988_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
v___jp_2010_:
{
if (v___y_2012_ == 0)
{
lean_dec_ref(v___y_2011_);
v___y_1983_ = v_a_1979_;
v___y_1984_ = v_a_1980_;
goto v___jp_1982_;
}
else
{
lean_object* v___x_2013_; 
lean_dec(v_decl_1978_);
v___x_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2013_, 0, v___y_2011_);
return v___x_2013_;
}
}
v___jp_2014_:
{
uint8_t v___x_2016_; 
v___x_2016_ = l_Lean_Exception_isInterrupt(v_a_2015_);
if (v___x_2016_ == 0)
{
uint8_t v___x_2017_; 
lean_inc_ref(v_a_2015_);
v___x_2017_ = l_Lean_Exception_isRuntime(v_a_2015_);
v___y_2011_ = v_a_2015_;
v___y_2012_ = v___x_2017_;
goto v___jp_2010_;
}
else
{
v___y_2011_ = v_a_2015_;
v___y_2012_ = v___x_2016_;
goto v___jp_2010_;
}
}
v___jp_2018_:
{
if (v___y_2020_ == 0)
{
lean_dec_ref(v___y_2019_);
v___y_1983_ = v_a_1979_;
v___y_1984_ = v_a_1980_;
goto v___jp_1982_;
}
else
{
lean_object* v___x_2021_; 
lean_dec(v_decl_1978_);
v___x_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2021_, 0, v___y_2019_);
return v___x_2021_;
}
}
v___jp_2022_:
{
uint8_t v___x_2024_; 
v___x_2024_ = l_Lean_Exception_isInterrupt(v_a_2023_);
if (v___x_2024_ == 0)
{
uint8_t v___x_2025_; 
lean_inc_ref(v_a_2023_);
v___x_2025_ = l_Lean_Exception_isRuntime(v_a_2023_);
v___y_2019_ = v_a_2023_;
v___y_2020_ = v___x_2025_;
goto v___jp_2018_;
}
else
{
v___y_2019_ = v_a_2023_;
v___y_2020_ = v___x_2024_;
goto v___jp_2018_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom___boxed(lean_object* v_decl_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2074_, v_a_2075_, v_a_2076_);
lean_dec(v_a_2076_);
lean_dec_ref(v_a_2075_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(lean_object* v_00_u03b1_2079_, lean_object* v_x_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v___x_2084_; 
v___x_2084_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_2080_, v___y_2081_, v___y_2082_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___boxed(lean_object* v_00_u03b1_2085_, lean_object* v_x_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(v_00_u03b1_2085_, v_x_2086_, v___y_2087_, v___y_2088_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(lean_object* v_as_2091_, lean_object* v_as_x27_2092_, lean_object* v_b_2093_, lean_object* v_a_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_2092_, v_b_2093_, v___y_2095_, v___y_2096_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___boxed(lean_object* v_as_2099_, lean_object* v_as_x27_2100_, lean_object* v_b_2101_, lean_object* v_a_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(v_as_2099_, v_as_x27_2100_, v_b_2101_, v_a_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v_as_x27_2100_);
lean_dec(v_as_2099_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v___x_2111_; 
v___x_2111_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(v_00_u03b1_2112_, v___y_2113_, v___y_2114_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(lean_object* v_00_u03b1_2117_, lean_object* v_ex_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_2118_, v___y_2119_, v___y_2120_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2123_, lean_object* v_ex_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(v_00_u03b1_2123_, v_ex_2124_, v___y_2125_, v___y_2126_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2129_, lean_object* v_msg_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_2130_, v___y_2131_, v___y_2132_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2135_, lean_object* v_msg_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(v_00_u03b1_2135_, v_msg_2136_, v___y_2137_, v___y_2138_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
return v_res_2140_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2141_ = lean_unsigned_to_nat(32u);
v___x_2142_ = lean_mk_empty_array_with_capacity(v___x_2141_);
v___x_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
return v___x_2143_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2144_ = ((size_t)5ULL);
v___x_2145_ = lean_unsigned_to_nat(0u);
v___x_2146_ = lean_unsigned_to_nat(32u);
v___x_2147_ = lean_mk_empty_array_with_capacity(v___x_2146_);
v___x_2148_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0);
v___x_2149_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2149_, 0, v___x_2148_);
lean_ctor_set(v___x_2149_, 1, v___x_2147_);
lean_ctor_set(v___x_2149_, 2, v___x_2145_);
lean_ctor_set(v___x_2149_, 3, v___x_2145_);
lean_ctor_set_usize(v___x_2149_, 4, v___x_2144_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(lean_object* v___y_2150_){
_start:
{
lean_object* v___x_2152_; lean_object* v_traceState_2153_; lean_object* v_traces_2154_; lean_object* v___x_2155_; lean_object* v_traceState_2156_; lean_object* v_env_2157_; lean_object* v_nextMacroScope_2158_; lean_object* v_ngen_2159_; lean_object* v_auxDeclNGen_2160_; lean_object* v_cache_2161_; lean_object* v_recordedDeps_2162_; lean_object* v_messages_2163_; lean_object* v_infoState_2164_; lean_object* v_snapshotTasks_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2184_; 
v___x_2152_ = lean_st_ref_get(v___y_2150_);
v_traceState_2153_ = lean_ctor_get(v___x_2152_, 4);
lean_inc_ref(v_traceState_2153_);
lean_dec(v___x_2152_);
v_traces_2154_ = lean_ctor_get(v_traceState_2153_, 0);
lean_inc_ref(v_traces_2154_);
lean_dec_ref(v_traceState_2153_);
v___x_2155_ = lean_st_ref_take(v___y_2150_);
v_traceState_2156_ = lean_ctor_get(v___x_2155_, 4);
v_env_2157_ = lean_ctor_get(v___x_2155_, 0);
v_nextMacroScope_2158_ = lean_ctor_get(v___x_2155_, 1);
v_ngen_2159_ = lean_ctor_get(v___x_2155_, 2);
v_auxDeclNGen_2160_ = lean_ctor_get(v___x_2155_, 3);
v_cache_2161_ = lean_ctor_get(v___x_2155_, 5);
v_recordedDeps_2162_ = lean_ctor_get(v___x_2155_, 6);
v_messages_2163_ = lean_ctor_get(v___x_2155_, 7);
v_infoState_2164_ = lean_ctor_get(v___x_2155_, 8);
v_snapshotTasks_2165_ = lean_ctor_get(v___x_2155_, 9);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2167_ = v___x_2155_;
v_isShared_2168_ = v_isSharedCheck_2184_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_snapshotTasks_2165_);
lean_inc(v_infoState_2164_);
lean_inc(v_messages_2163_);
lean_inc(v_recordedDeps_2162_);
lean_inc(v_cache_2161_);
lean_inc(v_traceState_2156_);
lean_inc(v_auxDeclNGen_2160_);
lean_inc(v_ngen_2159_);
lean_inc(v_nextMacroScope_2158_);
lean_inc(v_env_2157_);
lean_dec(v___x_2155_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2184_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
uint64_t v_tid_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2182_; 
v_tid_2169_ = lean_ctor_get_uint64(v_traceState_2156_, sizeof(void*)*1);
v_isSharedCheck_2182_ = !lean_is_exclusive(v_traceState_2156_);
if (v_isSharedCheck_2182_ == 0)
{
lean_object* v_unused_2183_; 
v_unused_2183_ = lean_ctor_get(v_traceState_2156_, 0);
lean_dec(v_unused_2183_);
v___x_2171_ = v_traceState_2156_;
v_isShared_2172_ = v_isSharedCheck_2182_;
goto v_resetjp_2170_;
}
else
{
lean_dec(v_traceState_2156_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2182_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2173_; lean_object* v___x_2175_; 
v___x_2173_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1);
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 0, v___x_2173_);
v___x_2175_ = v___x_2171_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2173_);
lean_ctor_set_uint64(v_reuseFailAlloc_2181_, sizeof(void*)*1, v_tid_2169_);
v___x_2175_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
lean_object* v___x_2177_; 
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 4, v___x_2175_);
v___x_2177_ = v___x_2167_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_env_2157_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_nextMacroScope_2158_);
lean_ctor_set(v_reuseFailAlloc_2180_, 2, v_ngen_2159_);
lean_ctor_set(v_reuseFailAlloc_2180_, 3, v_auxDeclNGen_2160_);
lean_ctor_set(v_reuseFailAlloc_2180_, 4, v___x_2175_);
lean_ctor_set(v_reuseFailAlloc_2180_, 5, v_cache_2161_);
lean_ctor_set(v_reuseFailAlloc_2180_, 6, v_recordedDeps_2162_);
lean_ctor_set(v_reuseFailAlloc_2180_, 7, v_messages_2163_);
lean_ctor_set(v_reuseFailAlloc_2180_, 8, v_infoState_2164_);
lean_ctor_set(v_reuseFailAlloc_2180_, 9, v_snapshotTasks_2165_);
v___x_2177_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = lean_st_ref_put(v___y_2150_, v___x_2177_);
v___x_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2179_, 0, v_traces_2154_);
return v___x_2179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___boxed(lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2185_);
lean_dec(v___y_2185_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v___x_2191_; 
v___x_2191_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2189_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___boxed(lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(v___y_2192_, v___y_2193_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(lean_object* v_category_2196_, lean_object* v_opts_2197_, lean_object* v_act_2198_, lean_object* v_decl_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
lean_inc(v___y_2201_);
lean_inc_ref(v___y_2200_);
v___x_2203_ = lean_apply_2(v_act_2198_, v___y_2200_, v___y_2201_);
v___x_2204_ = l_Lean_profileitIOUnsafe___redArg(v_category_2196_, v_opts_2197_, v___x_2203_, v_decl_2199_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg___boxed(lean_object* v_category_2205_, lean_object* v_opts_2206_, lean_object* v_act_2207_, lean_object* v_decl_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v_category_2205_, v_opts_2206_, v_act_2207_, v_decl_2208_, v___y_2209_, v___y_2210_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec_ref(v_opts_2206_);
lean_dec_ref(v_category_2205_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(lean_object* v_00_u03b1_2213_, lean_object* v_category_2214_, lean_object* v_opts_2215_, lean_object* v_act_2216_, lean_object* v_decl_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v_category_2214_, v_opts_2215_, v_act_2216_, v_decl_2217_, v___y_2218_, v___y_2219_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___boxed(lean_object* v_00_u03b1_2222_, lean_object* v_category_2223_, lean_object* v_opts_2224_, lean_object* v_act_2225_, lean_object* v_decl_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(v_00_u03b1_2222_, v_category_2223_, v_opts_2224_, v_act_2225_, v_decl_2226_, v___y_2227_, v___y_2228_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec_ref(v_opts_2224_);
lean_dec_ref(v_category_2223_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(lean_object* v_a_2231_, lean_object* v_a_2232_){
_start:
{
if (lean_obj_tag(v_a_2231_) == 0)
{
lean_object* v___x_2233_; 
v___x_2233_ = l_List_reverse___redArg(v_a_2232_);
return v___x_2233_;
}
else
{
lean_object* v_head_2234_; lean_object* v_tail_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2244_; 
v_head_2234_ = lean_ctor_get(v_a_2231_, 0);
v_tail_2235_ = lean_ctor_get(v_a_2231_, 1);
v_isSharedCheck_2244_ = !lean_is_exclusive(v_a_2231_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2237_ = v_a_2231_;
v_isShared_2238_ = v_isSharedCheck_2244_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_tail_2235_);
lean_inc(v_head_2234_);
lean_dec(v_a_2231_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2244_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2239_; lean_object* v___x_2241_; 
v___x_2239_ = l_Lean_MessageData_ofName(v_head_2234_);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 1, v_a_2232_);
lean_ctor_set(v___x_2237_, 0, v___x_2239_);
v___x_2241_ = v___x_2237_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2239_);
lean_ctor_set(v_reuseFailAlloc_2243_, 1, v_a_2232_);
v___x_2241_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
v_a_2231_ = v_tail_2235_;
v_a_2232_ = v___x_2241_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2246_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__0));
v___x_2247_ = l_Lean_stringToMessageData(v___x_2246_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(lean_object* v_decl_2248_, lean_object* v_x_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2253_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1);
v___x_2254_ = l_Lean_Declaration_getTopLevelNames(v_decl_2248_);
v___x_2255_ = lean_box(0);
v___x_2256_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2254_, v___x_2255_);
v___x_2257_ = l_Lean_MessageData_ofList(v___x_2256_);
v___x_2258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2253_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
v___x_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed(lean_object* v_decl_2260_, lean_object* v_x_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(v_decl_2260_, v_x_2261_, v___y_2262_, v___y_2263_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec_ref(v_x_2261_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(size_t v_sz_2266_, size_t v_i_2267_, lean_object* v_bs_2268_){
_start:
{
uint8_t v___x_2269_; 
v___x_2269_ = lean_usize_dec_lt(v_i_2267_, v_sz_2266_);
if (v___x_2269_ == 0)
{
return v_bs_2268_;
}
else
{
lean_object* v_v_2270_; lean_object* v_msg_2271_; lean_object* v___x_2272_; lean_object* v_bs_x27_2273_; size_t v___x_2274_; size_t v___x_2275_; lean_object* v___x_2276_; 
v_v_2270_ = lean_array_uget_borrowed(v_bs_2268_, v_i_2267_);
v_msg_2271_ = lean_ctor_get(v_v_2270_, 1);
lean_inc_ref(v_msg_2271_);
v___x_2272_ = lean_unsigned_to_nat(0u);
v_bs_x27_2273_ = lean_array_uset(v_bs_2268_, v_i_2267_, v___x_2272_);
v___x_2274_ = ((size_t)1ULL);
v___x_2275_ = lean_usize_add(v_i_2267_, v___x_2274_);
v___x_2276_ = lean_array_uset(v_bs_x27_2273_, v_i_2267_, v_msg_2271_);
v_i_2267_ = v___x_2275_;
v_bs_2268_ = v___x_2276_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4___boxed(lean_object* v_sz_2278_, lean_object* v_i_2279_, lean_object* v_bs_2280_){
_start:
{
size_t v_sz_boxed_2281_; size_t v_i_boxed_2282_; lean_object* v_res_2283_; 
v_sz_boxed_2281_ = lean_unbox_usize(v_sz_2278_);
lean_dec(v_sz_2278_);
v_i_boxed_2282_ = lean_unbox_usize(v_i_2279_);
lean_dec(v_i_2279_);
v_res_2283_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(v_sz_boxed_2281_, v_i_boxed_2282_, v_bs_2280_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(lean_object* v_oldTraces_2284_, lean_object* v_data_2285_, lean_object* v_ref_2286_, lean_object* v_msg_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v_toCold_2291_; lean_object* v_currRecDepth_2292_; lean_object* v_ref_2293_; uint16_t v_optionFlags_2294_; uint8_t v_suppressElabErrors_2295_; uint8_t v_isRecordingDeps_2296_; lean_object* v_ref_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v_traceState_2300_; lean_object* v_traces_2301_; lean_object* v___x_2302_; size_t v_sz_2303_; size_t v___x_2304_; lean_object* v___x_2305_; lean_object* v_msg_2306_; lean_object* v___x_2307_; lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2346_; 
v_toCold_2291_ = lean_ctor_get(v___y_2288_, 0);
v_currRecDepth_2292_ = lean_ctor_get(v___y_2288_, 1);
v_ref_2293_ = lean_ctor_get(v___y_2288_, 2);
v_optionFlags_2294_ = lean_ctor_get_uint16(v___y_2288_, sizeof(void*)*3);
v_suppressElabErrors_2295_ = lean_ctor_get_uint8(v___y_2288_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2296_ = lean_ctor_get_uint8(v___y_2288_, sizeof(void*)*3 + 3);
v_ref_2297_ = l_Lean_replaceRef(v_ref_2286_, v_ref_2293_);
lean_inc(v_currRecDepth_2292_);
lean_inc_ref(v_toCold_2291_);
v___x_2298_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2298_, 0, v_toCold_2291_);
lean_ctor_set(v___x_2298_, 1, v_currRecDepth_2292_);
lean_ctor_set(v___x_2298_, 2, v_ref_2297_);
lean_ctor_set_uint16(v___x_2298_, sizeof(void*)*3, v_optionFlags_2294_);
lean_ctor_set_uint8(v___x_2298_, sizeof(void*)*3 + 2, v_suppressElabErrors_2295_);
lean_ctor_set_uint8(v___x_2298_, sizeof(void*)*3 + 3, v_isRecordingDeps_2296_);
v___x_2299_ = lean_st_ref_get(v___y_2289_);
v_traceState_2300_ = lean_ctor_get(v___x_2299_, 4);
lean_inc_ref(v_traceState_2300_);
lean_dec(v___x_2299_);
v_traces_2301_ = lean_ctor_get(v_traceState_2300_, 0);
lean_inc_ref(v_traces_2301_);
lean_dec_ref(v_traceState_2300_);
v___x_2302_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2301_);
lean_dec_ref(v_traces_2301_);
v_sz_2303_ = lean_array_size(v___x_2302_);
v___x_2304_ = ((size_t)0ULL);
v___x_2305_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(v_sz_2303_, v___x_2304_, v___x_2302_);
v_msg_2306_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2306_, 0, v_data_2285_);
lean_ctor_set(v_msg_2306_, 1, v_msg_2287_);
lean_ctor_set(v_msg_2306_, 2, v___x_2305_);
v___x_2307_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2306_, v___x_2298_, v___y_2289_);
lean_dec_ref_known(v___x_2298_, 3);
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2310_ = v___x_2307_;
v_isShared_2311_ = v_isSharedCheck_2346_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2307_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2346_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2312_; lean_object* v_traceState_2313_; lean_object* v_env_2314_; lean_object* v_nextMacroScope_2315_; lean_object* v_ngen_2316_; lean_object* v_auxDeclNGen_2317_; lean_object* v_cache_2318_; lean_object* v_recordedDeps_2319_; lean_object* v_messages_2320_; lean_object* v_infoState_2321_; lean_object* v_snapshotTasks_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2345_; 
v___x_2312_ = lean_st_ref_take(v___y_2289_);
v_traceState_2313_ = lean_ctor_get(v___x_2312_, 4);
v_env_2314_ = lean_ctor_get(v___x_2312_, 0);
v_nextMacroScope_2315_ = lean_ctor_get(v___x_2312_, 1);
v_ngen_2316_ = lean_ctor_get(v___x_2312_, 2);
v_auxDeclNGen_2317_ = lean_ctor_get(v___x_2312_, 3);
v_cache_2318_ = lean_ctor_get(v___x_2312_, 5);
v_recordedDeps_2319_ = lean_ctor_get(v___x_2312_, 6);
v_messages_2320_ = lean_ctor_get(v___x_2312_, 7);
v_infoState_2321_ = lean_ctor_get(v___x_2312_, 8);
v_snapshotTasks_2322_ = lean_ctor_get(v___x_2312_, 9);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2324_ = v___x_2312_;
v_isShared_2325_ = v_isSharedCheck_2345_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_snapshotTasks_2322_);
lean_inc(v_infoState_2321_);
lean_inc(v_messages_2320_);
lean_inc(v_recordedDeps_2319_);
lean_inc(v_cache_2318_);
lean_inc(v_traceState_2313_);
lean_inc(v_auxDeclNGen_2317_);
lean_inc(v_ngen_2316_);
lean_inc(v_nextMacroScope_2315_);
lean_inc(v_env_2314_);
lean_dec(v___x_2312_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2345_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
uint64_t v_tid_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2343_; 
v_tid_2326_ = lean_ctor_get_uint64(v_traceState_2313_, sizeof(void*)*1);
v_isSharedCheck_2343_ = !lean_is_exclusive(v_traceState_2313_);
if (v_isSharedCheck_2343_ == 0)
{
lean_object* v_unused_2344_; 
v_unused_2344_ = lean_ctor_get(v_traceState_2313_, 0);
lean_dec(v_unused_2344_);
v___x_2328_ = v_traceState_2313_;
v_isShared_2329_ = v_isSharedCheck_2343_;
goto v_resetjp_2327_;
}
else
{
lean_dec(v_traceState_2313_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2343_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2334_; 
v___x_2330_ = lean_box(0);
v___x_2331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2331_, 0, v_ref_2286_);
lean_ctor_set(v___x_2331_, 1, v_a_2308_);
v___x_2332_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2284_, v___x_2331_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v___x_2332_);
v___x_2334_ = v___x_2328_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v___x_2332_);
lean_ctor_set_uint64(v_reuseFailAlloc_2342_, sizeof(void*)*1, v_tid_2326_);
v___x_2334_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
lean_object* v___x_2336_; 
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 4, v___x_2334_);
v___x_2336_ = v___x_2324_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_env_2314_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v_nextMacroScope_2315_);
lean_ctor_set(v_reuseFailAlloc_2341_, 2, v_ngen_2316_);
lean_ctor_set(v_reuseFailAlloc_2341_, 3, v_auxDeclNGen_2317_);
lean_ctor_set(v_reuseFailAlloc_2341_, 4, v___x_2334_);
lean_ctor_set(v_reuseFailAlloc_2341_, 5, v_cache_2318_);
lean_ctor_set(v_reuseFailAlloc_2341_, 6, v_recordedDeps_2319_);
lean_ctor_set(v_reuseFailAlloc_2341_, 7, v_messages_2320_);
lean_ctor_set(v_reuseFailAlloc_2341_, 8, v_infoState_2321_);
lean_ctor_set(v_reuseFailAlloc_2341_, 9, v_snapshotTasks_2322_);
v___x_2336_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
lean_object* v___x_2337_; lean_object* v___x_2339_; 
v___x_2337_ = lean_st_ref_put(v___y_2289_, v___x_2336_);
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 0, v___x_2330_);
v___x_2339_ = v___x_2310_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2330_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2___boxed(lean_object* v_oldTraces_2347_, lean_object* v_data_2348_, lean_object* v_ref_2349_, lean_object* v_msg_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_oldTraces_2347_, v_data_2348_, v_ref_2349_, v_msg_2350_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(lean_object* v_x_2355_){
_start:
{
if (lean_obj_tag(v_x_2355_) == 0)
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
v_a_2357_ = lean_ctor_get(v_x_2355_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v_x_2355_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v_x_2355_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v_x_2355_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
lean_ctor_set_tag(v___x_2359_, 1);
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
v_a_2365_ = lean_ctor_get(v_x_2355_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v_x_2355_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v_x_2355_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v_x_2355_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
lean_ctor_set_tag(v___x_2367_, 0);
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg___boxed(lean_object* v_x_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_x_2373_);
return v_res_2375_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(lean_object* v_e_2376_){
_start:
{
if (lean_obj_tag(v_e_2376_) == 0)
{
uint8_t v___x_2377_; 
v___x_2377_ = 2;
return v___x_2377_;
}
else
{
uint8_t v___x_2378_; 
v___x_2378_ = 0;
return v___x_2378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4___boxed(lean_object* v_e_2379_){
_start:
{
uint8_t v_res_2380_; lean_object* v_r_2381_; 
v_res_2380_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(v_e_2379_);
lean_dec_ref(v_e_2379_);
v_r_2381_ = lean_box(v_res_2380_);
return v_r_2381_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2382_; double v___x_2383_; 
v___x_2382_ = lean_unsigned_to_nat(0u);
v___x_2383_ = lean_float_of_nat(v___x_2382_);
return v___x_2383_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2(void){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__1));
v___x_2386_ = l_Lean_stringToMessageData(v___x_2385_);
return v___x_2386_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2387_; double v___x_2388_; 
v___x_2387_ = lean_unsigned_to_nat(1000u);
v___x_2388_ = lean_float_of_nat(v___x_2387_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(lean_object* v_cls_2389_, uint8_t v_collapsed_2390_, lean_object* v_tag_2391_, lean_object* v_opts_2392_, uint8_t v_clsEnabled_2393_, lean_object* v_oldTraces_2394_, lean_object* v_msg_2395_, lean_object* v_resStartStop_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v_fst_2400_; lean_object* v_snd_2401_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v_data_2405_; lean_object* v_fst_2408_; lean_object* v_snd_2409_; lean_object* v___x_2410_; uint8_t v___x_2411_; lean_object* v___y_2413_; lean_object* v_a_2414_; uint8_t v___y_2429_; double v___y_2461_; 
v_fst_2400_ = lean_ctor_get(v_resStartStop_2396_, 0);
lean_inc(v_fst_2400_);
v_snd_2401_ = lean_ctor_get(v_resStartStop_2396_, 1);
lean_inc(v_snd_2401_);
lean_dec_ref(v_resStartStop_2396_);
v_fst_2408_ = lean_ctor_get(v_snd_2401_, 0);
lean_inc(v_fst_2408_);
v_snd_2409_ = lean_ctor_get(v_snd_2401_, 1);
lean_inc(v_snd_2409_);
lean_dec(v_snd_2401_);
v___x_2410_ = l_Lean_trace_profiler;
v___x_2411_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2392_, v___x_2410_);
if (v___x_2411_ == 0)
{
v___y_2429_ = v___x_2411_;
goto v___jp_2428_;
}
else
{
lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2466_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2467_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2392_, v___x_2466_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; lean_object* v___x_2469_; double v___x_2470_; double v___x_2471_; double v___x_2472_; 
v___x_2468_ = l_Lean_trace_profiler_threshold;
v___x_2469_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_2392_, v___x_2468_);
v___x_2470_ = lean_float_of_nat(v___x_2469_);
v___x_2471_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3);
v___x_2472_ = lean_float_div(v___x_2470_, v___x_2471_);
v___y_2461_ = v___x_2472_;
goto v___jp_2460_;
}
else
{
lean_object* v___x_2473_; lean_object* v___x_2474_; double v___x_2475_; 
v___x_2473_ = l_Lean_trace_profiler_threshold;
v___x_2474_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_2392_, v___x_2473_);
v___x_2475_ = lean_float_of_nat(v___x_2474_);
v___y_2461_ = v___x_2475_;
goto v___jp_2460_;
}
}
v___jp_2402_:
{
lean_object* v___x_2406_; 
lean_inc(v___y_2404_);
v___x_2406_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_oldTraces_2394_, v_data_2405_, v___y_2404_, v___y_2403_, v___y_2397_, v___y_2398_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v___x_2407_; 
lean_dec_ref_known(v___x_2406_, 1);
v___x_2407_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_fst_2400_);
return v___x_2407_;
}
else
{
lean_dec(v_fst_2400_);
return v___x_2406_;
}
}
v___jp_2412_:
{
uint8_t v_result_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; double v___x_2418_; lean_object* v_data_2419_; 
v_result_2415_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(v_fst_2400_);
v___x_2416_ = lean_box(v_result_2415_);
v___x_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2416_);
v___x_2418_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0);
lean_inc_ref(v_tag_2391_);
lean_inc_ref(v___x_2417_);
lean_inc(v_cls_2389_);
v_data_2419_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2419_, 0, v_cls_2389_);
lean_ctor_set(v_data_2419_, 1, v___x_2417_);
lean_ctor_set(v_data_2419_, 2, v_tag_2391_);
lean_ctor_set_float(v_data_2419_, sizeof(void*)*3, v___x_2418_);
lean_ctor_set_float(v_data_2419_, sizeof(void*)*3 + 8, v___x_2418_);
lean_ctor_set_uint8(v_data_2419_, sizeof(void*)*3 + 16, v_collapsed_2390_);
if (v___x_2411_ == 0)
{
lean_dec_ref_known(v___x_2417_, 1);
lean_dec(v_snd_2409_);
lean_dec(v_fst_2408_);
lean_dec_ref(v_tag_2391_);
lean_dec(v_cls_2389_);
v___y_2403_ = v_a_2414_;
v___y_2404_ = v___y_2413_;
v_data_2405_ = v_data_2419_;
goto v___jp_2402_;
}
else
{
lean_object* v_data_2420_; double v___x_2421_; double v___x_2422_; 
lean_dec_ref_known(v_data_2419_, 3);
v_data_2420_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2420_, 0, v_cls_2389_);
lean_ctor_set(v_data_2420_, 1, v___x_2417_);
lean_ctor_set(v_data_2420_, 2, v_tag_2391_);
v___x_2421_ = lean_unbox_float(v_fst_2408_);
lean_dec(v_fst_2408_);
lean_ctor_set_float(v_data_2420_, sizeof(void*)*3, v___x_2421_);
v___x_2422_ = lean_unbox_float(v_snd_2409_);
lean_dec(v_snd_2409_);
lean_ctor_set_float(v_data_2420_, sizeof(void*)*3 + 8, v___x_2422_);
lean_ctor_set_uint8(v_data_2420_, sizeof(void*)*3 + 16, v_collapsed_2390_);
v___y_2403_ = v_a_2414_;
v___y_2404_ = v___y_2413_;
v_data_2405_ = v_data_2420_;
goto v___jp_2402_;
}
}
v___jp_2423_:
{
lean_object* v_ref_2424_; lean_object* v___x_2425_; 
v_ref_2424_ = lean_ctor_get(v___y_2397_, 2);
lean_inc(v___y_2398_);
lean_inc_ref(v___y_2397_);
lean_inc(v_fst_2400_);
v___x_2425_ = lean_apply_4(v_msg_2395_, v_fst_2400_, v___y_2397_, v___y_2398_, lean_box(0));
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_a_2426_);
lean_dec_ref_known(v___x_2425_, 1);
v___y_2413_ = v_ref_2424_;
v_a_2414_ = v_a_2426_;
goto v___jp_2412_;
}
else
{
lean_object* v___x_2427_; 
lean_dec_ref_known(v___x_2425_, 1);
v___x_2427_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2);
v___y_2413_ = v_ref_2424_;
v_a_2414_ = v___x_2427_;
goto v___jp_2412_;
}
}
v___jp_2428_:
{
if (v_clsEnabled_2393_ == 0)
{
if (v___y_2429_ == 0)
{
lean_object* v___x_2430_; lean_object* v_traceState_2431_; lean_object* v_env_2432_; lean_object* v_nextMacroScope_2433_; lean_object* v_ngen_2434_; lean_object* v_auxDeclNGen_2435_; lean_object* v_cache_2436_; lean_object* v_recordedDeps_2437_; lean_object* v_messages_2438_; lean_object* v_infoState_2439_; lean_object* v_snapshotTasks_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2459_; 
lean_dec(v_snd_2409_);
lean_dec(v_fst_2408_);
lean_dec_ref(v_msg_2395_);
lean_dec_ref(v_tag_2391_);
lean_dec(v_cls_2389_);
v___x_2430_ = lean_st_ref_take(v___y_2398_);
v_traceState_2431_ = lean_ctor_get(v___x_2430_, 4);
v_env_2432_ = lean_ctor_get(v___x_2430_, 0);
v_nextMacroScope_2433_ = lean_ctor_get(v___x_2430_, 1);
v_ngen_2434_ = lean_ctor_get(v___x_2430_, 2);
v_auxDeclNGen_2435_ = lean_ctor_get(v___x_2430_, 3);
v_cache_2436_ = lean_ctor_get(v___x_2430_, 5);
v_recordedDeps_2437_ = lean_ctor_get(v___x_2430_, 6);
v_messages_2438_ = lean_ctor_get(v___x_2430_, 7);
v_infoState_2439_ = lean_ctor_get(v___x_2430_, 8);
v_snapshotTasks_2440_ = lean_ctor_get(v___x_2430_, 9);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2442_ = v___x_2430_;
v_isShared_2443_ = v_isSharedCheck_2459_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_snapshotTasks_2440_);
lean_inc(v_infoState_2439_);
lean_inc(v_messages_2438_);
lean_inc(v_recordedDeps_2437_);
lean_inc(v_cache_2436_);
lean_inc(v_traceState_2431_);
lean_inc(v_auxDeclNGen_2435_);
lean_inc(v_ngen_2434_);
lean_inc(v_nextMacroScope_2433_);
lean_inc(v_env_2432_);
lean_dec(v___x_2430_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2459_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
uint64_t v_tid_2444_; lean_object* v_traces_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2458_; 
v_tid_2444_ = lean_ctor_get_uint64(v_traceState_2431_, sizeof(void*)*1);
v_traces_2445_ = lean_ctor_get(v_traceState_2431_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v_traceState_2431_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2447_ = v_traceState_2431_;
v_isShared_2448_ = v_isSharedCheck_2458_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_traces_2445_);
lean_dec(v_traceState_2431_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2458_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2449_; lean_object* v___x_2451_; 
v___x_2449_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2394_, v_traces_2445_);
lean_dec_ref(v_traces_2445_);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 0, v___x_2449_);
v___x_2451_ = v___x_2447_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2449_);
lean_ctor_set_uint64(v_reuseFailAlloc_2457_, sizeof(void*)*1, v_tid_2444_);
v___x_2451_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
lean_object* v___x_2453_; 
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 4, v___x_2451_);
v___x_2453_ = v___x_2442_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_env_2432_);
lean_ctor_set(v_reuseFailAlloc_2456_, 1, v_nextMacroScope_2433_);
lean_ctor_set(v_reuseFailAlloc_2456_, 2, v_ngen_2434_);
lean_ctor_set(v_reuseFailAlloc_2456_, 3, v_auxDeclNGen_2435_);
lean_ctor_set(v_reuseFailAlloc_2456_, 4, v___x_2451_);
lean_ctor_set(v_reuseFailAlloc_2456_, 5, v_cache_2436_);
lean_ctor_set(v_reuseFailAlloc_2456_, 6, v_recordedDeps_2437_);
lean_ctor_set(v_reuseFailAlloc_2456_, 7, v_messages_2438_);
lean_ctor_set(v_reuseFailAlloc_2456_, 8, v_infoState_2439_);
lean_ctor_set(v_reuseFailAlloc_2456_, 9, v_snapshotTasks_2440_);
v___x_2453_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = lean_st_ref_put(v___y_2398_, v___x_2453_);
v___x_2455_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_fst_2400_);
return v___x_2455_;
}
}
}
}
}
else
{
goto v___jp_2423_;
}
}
else
{
goto v___jp_2423_;
}
}
v___jp_2460_:
{
double v___x_2462_; double v___x_2463_; double v___x_2464_; uint8_t v___x_2465_; 
v___x_2462_ = lean_unbox_float(v_snd_2409_);
v___x_2463_ = lean_unbox_float(v_fst_2408_);
v___x_2464_ = lean_float_sub(v___x_2462_, v___x_2463_);
v___x_2465_ = lean_float_decLt(v___y_2461_, v___x_2464_);
v___y_2429_ = v___x_2465_;
goto v___jp_2428_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___boxed(lean_object* v_cls_2476_, lean_object* v_collapsed_2477_, lean_object* v_tag_2478_, lean_object* v_opts_2479_, lean_object* v_clsEnabled_2480_, lean_object* v_oldTraces_2481_, lean_object* v_msg_2482_, lean_object* v_resStartStop_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
uint8_t v_collapsed_boxed_2487_; uint8_t v_clsEnabled_boxed_2488_; lean_object* v_res_2489_; 
v_collapsed_boxed_2487_ = lean_unbox(v_collapsed_2477_);
v_clsEnabled_boxed_2488_ = lean_unbox(v_clsEnabled_2480_);
v_res_2489_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_2476_, v_collapsed_boxed_2487_, v_tag_2478_, v_opts_2479_, v_clsEnabled_boxed_2488_, v_oldTraces_2481_, v_msg_2482_, v_resStartStop_2483_, v___y_2484_, v___y_2485_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec_ref(v_opts_2479_);
return v_res_2489_;
}
}
static double _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2492_; double v___x_2493_; 
v___x_2492_ = lean_unsigned_to_nat(1000000000u);
v___x_2493_ = lean_float_of_nat(v___x_2492_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(lean_object* v_decl_2494_, lean_object* v___x_2495_, uint8_t v___x_2496_, lean_object* v___x_2497_, lean_object* v___f_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
lean_object* v___y_2503_; lean_object* v___y_2504_; uint8_t v___y_2505_; lean_object* v___y_2516_; lean_object* v_a_2517_; lean_object* v___y_2521_; lean_object* v___y_2522_; uint8_t v___y_2523_; lean_object* v___y_2534_; lean_object* v_a_2535_; lean_object* v_toCold_2538_; lean_object* v_options_2539_; uint8_t v_hasTrace_2540_; 
v_toCold_2538_ = lean_ctor_get(v___y_2499_, 0);
v_options_2539_ = lean_ctor_get(v_toCold_2538_, 2);
v_hasTrace_2540_ = lean_ctor_get_uint8(v_options_2539_, sizeof(void*)*1);
if (v_hasTrace_2540_ == 0)
{
lean_object* v_cancelTk_x3f_2541_; lean_object* v___x_2542_; 
lean_dec_ref(v___f_2498_);
lean_dec_ref(v___x_2497_);
lean_dec(v___x_2495_);
v_cancelTk_x3f_2541_ = lean_ctor_get(v_toCold_2538_, 10);
lean_inc(v_decl_2494_);
v___x_2542_ = l_Lean_warnIfUsesSorry(v_decl_2494_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v___x_2543_; lean_object* v_env_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
lean_dec_ref_known(v___x_2542_, 1);
v___x_2543_ = lean_st_ref_get(v___y_2500_);
v_env_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc_ref(v_env_2544_);
lean_dec(v___x_2543_);
v___x_2545_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2499_);
v___x_2546_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2544_, v___x_2545_, v_decl_2494_, v_cancelTk_x3f_2541_);
lean_dec_ref(v___x_2545_);
v___x_2547_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2546_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_a_2548_; lean_object* v___x_2549_; 
lean_dec(v_decl_2494_);
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_a_2548_);
lean_dec_ref_known(v___x_2547_, 1);
v___x_2549_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2548_, v___y_2500_);
return v___x_2549_;
}
else
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2557_; 
v_a_2550_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2552_ = v___x_2547_;
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2547_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
lean_inc(v_a_2550_);
if (v_isShared_2553_ == 0)
{
v___x_2555_ = v___x_2552_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2550_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
v___y_2534_ = v___x_2555_;
v_a_2535_ = v_a_2550_;
goto v___jp_2533_;
}
}
}
}
else
{
lean_dec(v_decl_2494_);
return v___x_2542_;
}
}
else
{
lean_object* v_cancelTk_x3f_2558_; lean_object* v_inheritedTraceOptions_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; uint8_t v___x_2562_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v_a_2566_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v_a_2581_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v_a_2586_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; uint8_t v___y_2598_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v_a_2603_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v_a_2609_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v_a_2621_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v_a_2626_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; uint8_t v___y_2638_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v_a_2643_; 
v_cancelTk_x3f_2558_ = lean_ctor_get(v_toCold_2538_, 10);
v_inheritedTraceOptions_2559_ = lean_ctor_get(v_toCold_2538_, 11);
v___x_2560_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v___x_2495_);
v___x_2561_ = l_Lean_Name_append(v___x_2560_, v___x_2495_);
v___x_2562_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2559_, v_options_2539_, v___x_2561_);
lean_dec(v___x_2561_);
if (v___x_2562_ == 0)
{
lean_object* v___x_2673_; uint8_t v___x_2674_; 
v___x_2673_ = l_Lean_trace_profiler;
v___x_2674_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2539_, v___x_2673_);
if (v___x_2674_ == 0)
{
lean_object* v___x_2675_; 
lean_dec_ref(v___f_2498_);
lean_dec_ref(v___x_2497_);
lean_dec(v___x_2495_);
lean_inc(v_decl_2494_);
v___x_2675_ = l_Lean_warnIfUsesSorry(v_decl_2494_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v___x_2676_; lean_object* v_env_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
lean_dec_ref_known(v___x_2675_, 1);
v___x_2676_ = lean_st_ref_get(v___y_2500_);
v_env_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc_ref(v_env_2677_);
lean_dec(v___x_2676_);
v___x_2678_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2499_);
v___x_2679_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2677_, v___x_2678_, v_decl_2494_, v_cancelTk_x3f_2558_);
lean_dec_ref(v___x_2678_);
v___x_2680_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2679_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; lean_object* v___x_2682_; 
lean_dec(v_decl_2494_);
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2680_, 1);
v___x_2682_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2681_, v___y_2500_);
return v___x_2682_;
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2690_; 
v_a_2683_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2685_ = v___x_2680_;
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2680_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2688_; 
lean_inc(v_a_2683_);
if (v_isShared_2686_ == 0)
{
v___x_2688_ = v___x_2685_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_a_2683_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
v___y_2516_ = v___x_2688_;
v_a_2517_ = v_a_2683_;
goto v___jp_2515_;
}
}
}
}
else
{
lean_dec(v_decl_2494_);
return v___x_2675_;
}
}
else
{
goto v___jp_2646_;
}
}
else
{
goto v___jp_2646_;
}
v___jp_2563_:
{
lean_object* v___x_2567_; double v___x_2568_; double v___x_2569_; double v___x_2570_; double v___x_2571_; double v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2567_ = lean_io_mono_nanos_now();
v___x_2568_ = lean_float_of_nat(v___y_2564_);
v___x_2569_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_2570_ = lean_float_div(v___x_2568_, v___x_2569_);
v___x_2571_ = lean_float_of_nat(v___x_2567_);
v___x_2572_ = lean_float_div(v___x_2571_, v___x_2569_);
v___x_2573_ = lean_box_float(v___x_2570_);
v___x_2574_ = lean_box_float(v___x_2572_);
v___x_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2573_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
v___x_2576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2576_, 0, v_a_2566_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
v___x_2577_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2495_, v___x_2496_, v___x_2497_, v_options_2539_, v___x_2562_, v___y_2565_, v___f_2498_, v___x_2576_, v___y_2499_, v___y_2500_);
return v___x_2577_;
}
v___jp_2578_:
{
lean_object* v___x_2582_; 
v___x_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2582_, 0, v_a_2581_);
v___y_2564_ = v___y_2579_;
v___y_2565_ = v___y_2580_;
v_a_2566_ = v___x_2582_;
goto v___jp_2563_;
}
v___jp_2583_:
{
lean_object* v___x_2587_; 
v___x_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2587_, 0, v_a_2586_);
v___y_2564_ = v___y_2584_;
v___y_2565_ = v___y_2585_;
v_a_2566_ = v___x_2587_;
goto v___jp_2563_;
}
v___jp_2588_:
{
if (lean_obj_tag(v___y_2591_) == 0)
{
lean_object* v_a_2592_; 
v_a_2592_ = lean_ctor_get(v___y_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref_known(v___y_2591_, 1);
v___y_2584_ = v___y_2589_;
v___y_2585_ = v___y_2590_;
v_a_2586_ = v_a_2592_;
goto v___jp_2583_;
}
else
{
lean_object* v_a_2593_; 
v_a_2593_ = lean_ctor_get(v___y_2591_, 0);
lean_inc(v_a_2593_);
lean_dec_ref_known(v___y_2591_, 1);
v___y_2579_ = v___y_2589_;
v___y_2580_ = v___y_2590_;
v_a_2581_ = v_a_2593_;
goto v___jp_2578_;
}
}
v___jp_2594_:
{
if (v___y_2598_ == 0)
{
lean_object* v___x_2599_; 
v___x_2599_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2494_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_dec_ref_known(v___x_2599_, 1);
v___y_2579_ = v___y_2596_;
v___y_2580_ = v___y_2597_;
v_a_2581_ = v___y_2595_;
goto v___jp_2578_;
}
else
{
lean_dec_ref(v___y_2595_);
v___y_2589_ = v___y_2596_;
v___y_2590_ = v___y_2597_;
v___y_2591_ = v___x_2599_;
goto v___jp_2588_;
}
}
else
{
lean_dec(v_decl_2494_);
v___y_2579_ = v___y_2596_;
v___y_2580_ = v___y_2597_;
v_a_2581_ = v___y_2595_;
goto v___jp_2578_;
}
}
v___jp_2600_:
{
uint8_t v___x_2604_; 
v___x_2604_ = l_Lean_Exception_isInterrupt(v_a_2603_);
if (v___x_2604_ == 0)
{
uint8_t v___x_2605_; 
lean_inc_ref(v_a_2603_);
v___x_2605_ = l_Lean_Exception_isRuntime(v_a_2603_);
v___y_2595_ = v_a_2603_;
v___y_2596_ = v___y_2601_;
v___y_2597_ = v___y_2602_;
v___y_2598_ = v___x_2605_;
goto v___jp_2594_;
}
else
{
v___y_2595_ = v_a_2603_;
v___y_2596_ = v___y_2601_;
v___y_2597_ = v___y_2602_;
v___y_2598_ = v___x_2604_;
goto v___jp_2594_;
}
}
v___jp_2606_:
{
lean_object* v___x_2610_; double v___x_2611_; double v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2610_ = lean_io_get_num_heartbeats();
v___x_2611_ = lean_float_of_nat(v___y_2607_);
v___x_2612_ = lean_float_of_nat(v___x_2610_);
v___x_2613_ = lean_box_float(v___x_2611_);
v___x_2614_ = lean_box_float(v___x_2612_);
v___x_2615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2613_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
v___x_2616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2616_, 0, v_a_2609_);
lean_ctor_set(v___x_2616_, 1, v___x_2615_);
v___x_2617_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2495_, v___x_2496_, v___x_2497_, v_options_2539_, v___x_2562_, v___y_2608_, v___f_2498_, v___x_2616_, v___y_2499_, v___y_2500_);
return v___x_2617_;
}
v___jp_2618_:
{
lean_object* v___x_2622_; 
v___x_2622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2622_, 0, v_a_2621_);
v___y_2607_ = v___y_2619_;
v___y_2608_ = v___y_2620_;
v_a_2609_ = v___x_2622_;
goto v___jp_2606_;
}
v___jp_2623_:
{
lean_object* v___x_2627_; 
v___x_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2627_, 0, v_a_2626_);
v___y_2607_ = v___y_2624_;
v___y_2608_ = v___y_2625_;
v_a_2609_ = v___x_2627_;
goto v___jp_2606_;
}
v___jp_2628_:
{
if (lean_obj_tag(v___y_2631_) == 0)
{
lean_object* v_a_2632_; 
v_a_2632_ = lean_ctor_get(v___y_2631_, 0);
lean_inc(v_a_2632_);
lean_dec_ref_known(v___y_2631_, 1);
v___y_2624_ = v___y_2629_;
v___y_2625_ = v___y_2630_;
v_a_2626_ = v_a_2632_;
goto v___jp_2623_;
}
else
{
lean_object* v_a_2633_; 
v_a_2633_ = lean_ctor_get(v___y_2631_, 0);
lean_inc(v_a_2633_);
lean_dec_ref_known(v___y_2631_, 1);
v___y_2619_ = v___y_2629_;
v___y_2620_ = v___y_2630_;
v_a_2621_ = v_a_2633_;
goto v___jp_2618_;
}
}
v___jp_2634_:
{
if (v___y_2638_ == 0)
{
lean_object* v___x_2639_; 
v___x_2639_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2494_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_dec_ref_known(v___x_2639_, 1);
v___y_2619_ = v___y_2635_;
v___y_2620_ = v___y_2637_;
v_a_2621_ = v___y_2636_;
goto v___jp_2618_;
}
else
{
lean_dec_ref(v___y_2636_);
v___y_2629_ = v___y_2635_;
v___y_2630_ = v___y_2637_;
v___y_2631_ = v___x_2639_;
goto v___jp_2628_;
}
}
else
{
lean_dec(v_decl_2494_);
v___y_2619_ = v___y_2635_;
v___y_2620_ = v___y_2637_;
v_a_2621_ = v___y_2636_;
goto v___jp_2618_;
}
}
v___jp_2640_:
{
uint8_t v___x_2644_; 
v___x_2644_ = l_Lean_Exception_isInterrupt(v_a_2643_);
if (v___x_2644_ == 0)
{
uint8_t v___x_2645_; 
lean_inc_ref(v_a_2643_);
v___x_2645_ = l_Lean_Exception_isRuntime(v_a_2643_);
v___y_2635_ = v___y_2641_;
v___y_2636_ = v_a_2643_;
v___y_2637_ = v___y_2642_;
v___y_2638_ = v___x_2645_;
goto v___jp_2634_;
}
else
{
v___y_2635_ = v___y_2641_;
v___y_2636_ = v_a_2643_;
v___y_2637_ = v___y_2642_;
v___y_2638_ = v___x_2644_;
goto v___jp_2634_;
}
}
v___jp_2646_:
{
lean_object* v___x_2647_; lean_object* v_a_2648_; lean_object* v___x_2649_; uint8_t v___x_2650_; 
v___x_2647_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2500_);
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_a_2648_);
lean_dec_ref(v___x_2647_);
v___x_2649_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2650_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2539_, v___x_2649_);
if (v___x_2650_ == 0)
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2651_ = lean_io_mono_nanos_now();
lean_inc(v_decl_2494_);
v___x_2652_ = l_Lean_warnIfUsesSorry(v_decl_2494_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v___x_2653_; lean_object* v_env_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
lean_dec_ref_known(v___x_2652_, 1);
v___x_2653_ = lean_st_ref_get(v___y_2500_);
v_env_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc_ref(v_env_2654_);
lean_dec(v___x_2653_);
v___x_2655_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2499_);
v___x_2656_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2654_, v___x_2655_, v_decl_2494_, v_cancelTk_x3f_2558_);
lean_dec_ref(v___x_2655_);
v___x_2657_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2656_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; lean_object* v___x_2659_; lean_object* v_a_2660_; 
lean_dec(v_decl_2494_);
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2658_);
lean_dec_ref_known(v___x_2657_, 1);
v___x_2659_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2658_, v___y_2500_);
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref(v___x_2659_);
v___y_2584_ = v___x_2651_;
v___y_2585_ = v_a_2648_;
v_a_2586_ = v_a_2660_;
goto v___jp_2583_;
}
else
{
lean_object* v_a_2661_; 
v_a_2661_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2661_);
lean_dec_ref_known(v___x_2657_, 1);
v___y_2601_ = v___x_2651_;
v___y_2602_ = v_a_2648_;
v_a_2603_ = v_a_2661_;
goto v___jp_2600_;
}
}
else
{
lean_dec(v_decl_2494_);
v___y_2589_ = v___x_2651_;
v___y_2590_ = v_a_2648_;
v___y_2591_ = v___x_2652_;
goto v___jp_2588_;
}
}
else
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2662_ = lean_io_get_num_heartbeats();
lean_inc(v_decl_2494_);
v___x_2663_ = l_Lean_warnIfUsesSorry(v_decl_2494_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v___x_2664_; lean_object* v_env_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
lean_dec_ref_known(v___x_2663_, 1);
v___x_2664_ = lean_st_ref_get(v___y_2500_);
v_env_2665_ = lean_ctor_get(v___x_2664_, 0);
lean_inc_ref(v_env_2665_);
lean_dec(v___x_2664_);
v___x_2666_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2499_);
v___x_2667_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2665_, v___x_2666_, v_decl_2494_, v_cancelTk_x3f_2558_);
lean_dec_ref(v___x_2666_);
v___x_2668_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2667_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v_a_2669_; lean_object* v___x_2670_; lean_object* v_a_2671_; 
lean_dec(v_decl_2494_);
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2669_);
lean_dec_ref_known(v___x_2668_, 1);
v___x_2670_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2669_, v___y_2500_);
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2671_);
lean_dec_ref(v___x_2670_);
v___y_2624_ = v___x_2662_;
v___y_2625_ = v_a_2648_;
v_a_2626_ = v_a_2671_;
goto v___jp_2623_;
}
else
{
lean_object* v_a_2672_; 
v_a_2672_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2672_);
lean_dec_ref_known(v___x_2668_, 1);
v___y_2641_ = v___x_2662_;
v___y_2642_ = v_a_2648_;
v_a_2643_ = v_a_2672_;
goto v___jp_2640_;
}
}
else
{
lean_dec(v_decl_2494_);
v___y_2629_ = v___x_2662_;
v___y_2630_ = v_a_2648_;
v___y_2631_ = v___x_2663_;
goto v___jp_2628_;
}
}
}
}
v___jp_2502_:
{
if (v___y_2505_ == 0)
{
lean_object* v___x_2506_; 
lean_dec_ref(v___y_2504_);
v___x_2506_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2494_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2513_ == 0)
{
lean_object* v_unused_2514_; 
v_unused_2514_ = lean_ctor_get(v___x_2506_, 0);
lean_dec(v_unused_2514_);
v___x_2508_ = v___x_2506_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_dec(v___x_2506_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
lean_ctor_set_tag(v___x_2508_, 1);
lean_ctor_set(v___x_2508_, 0, v___y_2503_);
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___y_2503_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
else
{
lean_dec_ref(v___y_2503_);
return v___x_2506_;
}
}
else
{
lean_dec_ref(v___y_2503_);
lean_dec(v_decl_2494_);
return v___y_2504_;
}
}
v___jp_2515_:
{
uint8_t v___x_2518_; 
v___x_2518_ = l_Lean_Exception_isInterrupt(v_a_2517_);
if (v___x_2518_ == 0)
{
uint8_t v___x_2519_; 
lean_inc_ref(v_a_2517_);
v___x_2519_ = l_Lean_Exception_isRuntime(v_a_2517_);
v___y_2503_ = v_a_2517_;
v___y_2504_ = v___y_2516_;
v___y_2505_ = v___x_2519_;
goto v___jp_2502_;
}
else
{
v___y_2503_ = v_a_2517_;
v___y_2504_ = v___y_2516_;
v___y_2505_ = v___x_2518_;
goto v___jp_2502_;
}
}
v___jp_2520_:
{
if (v___y_2523_ == 0)
{
lean_object* v___x_2524_; 
lean_dec_ref(v___y_2522_);
v___x_2524_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2494_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2531_ == 0)
{
lean_object* v_unused_2532_; 
v_unused_2532_ = lean_ctor_get(v___x_2524_, 0);
lean_dec(v_unused_2532_);
v___x_2526_ = v___x_2524_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_dec(v___x_2524_);
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
lean_ctor_set(v___x_2526_, 0, v___y_2521_);
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___y_2521_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
else
{
lean_dec_ref(v___y_2521_);
return v___x_2524_;
}
}
else
{
lean_dec_ref(v___y_2521_);
lean_dec(v_decl_2494_);
return v___y_2522_;
}
}
v___jp_2533_:
{
uint8_t v___x_2536_; 
v___x_2536_ = l_Lean_Exception_isInterrupt(v_a_2535_);
if (v___x_2536_ == 0)
{
uint8_t v___x_2537_; 
lean_inc_ref(v_a_2535_);
v___x_2537_ = l_Lean_Exception_isRuntime(v_a_2535_);
v___y_2521_ = v_a_2535_;
v___y_2522_ = v___y_2534_;
v___y_2523_ = v___x_2537_;
goto v___jp_2520_;
}
else
{
v___y_2521_ = v_a_2535_;
v___y_2522_ = v___y_2534_;
v___y_2523_ = v___x_2536_;
goto v___jp_2520_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed(lean_object* v_decl_2691_, lean_object* v___x_2692_, lean_object* v___x_2693_, lean_object* v___x_2694_, lean_object* v___f_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
uint8_t v___x_7949__boxed_2699_; lean_object* v_res_2700_; 
v___x_7949__boxed_2699_ = lean_unbox(v___x_2693_);
v_res_2700_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(v_decl_2691_, v___x_2692_, v___x_7949__boxed_2699_, v___x_2694_, v___f_2695_, v___y_2696_, v___y_2697_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(lean_object* v_decl_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_){
_start:
{
lean_object* v___f_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; uint8_t v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___f_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
lean_inc(v_decl_2705_);
v___f_2709_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2709_, 0, v_decl_2705_);
v___x_2710_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2706_);
v___x_2711_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__0));
v___x_2712_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__2));
v___x_2713_ = 1;
v___x_2714_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2715_ = lean_box(v___x_2713_);
v___f_2716_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed), 8, 5);
lean_closure_set(v___f_2716_, 0, v_decl_2705_);
lean_closure_set(v___f_2716_, 1, v___x_2712_);
lean_closure_set(v___f_2716_, 2, v___x_2715_);
lean_closure_set(v___f_2716_, 3, v___x_2714_);
lean_closure_set(v___f_2716_, 4, v___f_2709_);
v___x_2717_ = lean_box(0);
v___x_2718_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v___x_2711_, v___x_2710_, v___f_2716_, v___x_2717_, v_a_2706_, v_a_2707_);
lean_dec_ref(v___x_2710_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___boxed(lean_object* v_decl_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2719_, v_a_2720_, v_a_2721_);
lean_dec(v_a_2721_);
lean_dec_ref(v_a_2720_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(lean_object* v_00_u03b1_2724_, lean_object* v_x_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_x_2725_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2730_, lean_object* v_x_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(v_00_u03b1_2730_, v_x_2731_, v___y_2732_, v___y_2733_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(lean_object* v___y_2736_, lean_object* v_a_2737_, lean_object* v_ref_2738_, lean_object* v_a_x3f_2739_){
_start:
{
lean_object* v___x_2741_; lean_object* v_env_2742_; lean_object* v___x_2743_; 
v___x_2741_ = lean_st_ref_get(v___y_2736_);
v_env_2742_ = lean_ctor_get(v___x_2741_, 0);
lean_inc_ref(v_env_2742_);
lean_dec(v___x_2741_);
v___x_2743_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2737_, v_env_2742_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
lean_dec(v_ref_2738_);
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
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2763_; 
v_a_2752_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2754_ = v___x_2743_;
v_isShared_2755_ = v_isSharedCheck_2763_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2743_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2763_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2761_; 
v___x_2756_ = lean_io_error_to_string(v_a_2752_);
v___x_2757_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2756_);
v___x_2758_ = l_Lean_MessageData_ofFormat(v___x_2757_);
v___x_2759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2759_, 0, v_ref_2738_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v___x_2759_);
v___x_2761_ = v___x_2754_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v___x_2759_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed(lean_object* v___y_2764_, lean_object* v_a_2765_, lean_object* v_ref_2766_, lean_object* v_a_x3f_2767_, lean_object* v___y_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2764_, v_a_2765_, v_ref_2766_, v_a_x3f_2767_);
lean_dec(v_a_x3f_2767_);
lean_dec(v___y_2764_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v_a_2772_, lean_object* v_a_x3f_2773_){
_start:
{
lean_object* v___x_2775_; lean_object* v_env_2776_; lean_object* v_ref_2777_; lean_object* v___x_2778_; 
v___x_2775_ = lean_st_ref_get(v___y_2770_);
v_env_2776_ = lean_ctor_get(v___x_2775_, 0);
lean_inc_ref(v_env_2776_);
lean_dec(v___x_2775_);
v_ref_2777_ = lean_ctor_get(v___y_2771_, 2);
v___x_2778_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2772_, v_env_2776_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v___x_2778_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
else
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2798_; 
v_a_2787_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2789_ = v___x_2778_;
v_isShared_2790_ = v_isSharedCheck_2798_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2778_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2798_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2796_; 
v___x_2791_ = lean_io_error_to_string(v_a_2787_);
v___x_2792_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2791_);
v___x_2793_ = l_Lean_MessageData_ofFormat(v___x_2792_);
lean_inc(v_ref_2777_);
v___x_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2794_, 0, v_ref_2777_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
if (v_isShared_2790_ == 0)
{
lean_ctor_set(v___x_2789_, 0, v___x_2794_);
v___x_2796_ = v___x_2789_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2794_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___boxed(lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v_a_2801_, lean_object* v_a_x3f_2802_, lean_object* v___y_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v___y_2799_, v___y_2800_, v_a_2801_, v_a_x3f_2802_);
lean_dec(v_a_x3f_2802_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(lean_object* v_a_2805_, lean_object* v_asyncEnv_2806_, lean_object* v_decl_2807_, lean_object* v_x_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
lean_object* v___x_2812_; lean_object* v_r_2813_; 
v___x_2812_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_asyncEnv_2806_, v___y_2810_);
lean_dec_ref(v___x_2812_);
v_r_2813_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2807_, v___y_2809_, v___y_2810_);
if (lean_obj_tag(v_r_2813_) == 0)
{
lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2830_; 
v_a_2814_ = lean_ctor_get(v_r_2813_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v_r_2813_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2816_ = v_r_2813_;
v_isShared_2817_ = v_isSharedCheck_2830_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_dec(v_r_2813_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2830_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2819_; 
lean_inc(v_a_2814_);
if (v_isShared_2817_ == 0)
{
lean_ctor_set_tag(v___x_2816_, 1);
v___x_2819_ = v___x_2816_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2814_);
v___x_2819_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
lean_object* v___x_2820_; 
v___x_2820_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v___y_2810_, v___y_2809_, v_a_2805_, v___x_2819_);
lean_dec_ref(v___x_2819_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2827_ == 0)
{
lean_object* v_unused_2828_; 
v_unused_2828_ = lean_ctor_get(v___x_2820_, 0);
lean_dec(v_unused_2828_);
v___x_2822_ = v___x_2820_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_dec(v___x_2820_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 0, v_a_2814_);
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2814_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
else
{
lean_dec(v_a_2814_);
return v___x_2820_;
}
}
}
}
else
{
lean_object* v_a_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
v_a_2831_ = lean_ctor_get(v_r_2813_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v_r_2813_, 1);
v___x_2832_ = lean_box(0);
v___x_2833_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v___y_2810_, v___y_2809_, v_a_2805_, v___x_2832_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2840_; 
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2840_ == 0)
{
lean_object* v_unused_2841_; 
v_unused_2841_ = lean_ctor_get(v___x_2833_, 0);
lean_dec(v_unused_2841_);
v___x_2835_ = v___x_2833_;
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
else
{
lean_dec(v___x_2833_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2838_; 
if (v_isShared_2836_ == 0)
{
lean_ctor_set_tag(v___x_2835_, 1);
lean_ctor_set(v___x_2835_, 0, v_a_2831_);
v___x_2838_ = v___x_2835_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2831_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
else
{
lean_dec(v_a_2831_);
return v___x_2833_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed(lean_object* v_a_2842_, lean_object* v_asyncEnv_2843_, lean_object* v_decl_2844_, lean_object* v_x_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(v_a_2842_, v_asyncEnv_2843_, v_decl_2844_, v_x_2845_, v___y_2846_, v___y_2847_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec_ref(v_x_2845_);
return v_res_2849_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2851_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__0));
v___x_2852_ = l_Lean_stringToMessageData(v___x_2851_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(lean_object* v_decl_2853_, lean_object* v_x_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2858_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1);
v___x_2859_ = l_Lean_Declaration_getNames(v_decl_2853_);
v___x_2860_ = lean_box(0);
v___x_2861_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2859_, v___x_2860_);
v___x_2862_ = l_Lean_MessageData_ofList(v___x_2861_);
v___x_2863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2858_);
lean_ctor_set(v___x_2863_, 1, v___x_2862_);
v___x_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2863_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed(lean_object* v_decl_2865_, lean_object* v_x_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_2865_, v_x_2866_, v___y_2867_, v___y_2868_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec_ref(v_x_2866_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(lean_object* v_cls_2873_, lean_object* v_msg_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v_ref_2878_; lean_object* v___x_2879_; lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2925_; 
v_ref_2878_ = lean_ctor_get(v___y_2875_, 2);
v___x_2879_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2874_, v___y_2875_, v___y_2876_);
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2882_ = v___x_2879_;
v_isShared_2883_ = v_isSharedCheck_2925_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2879_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2925_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2884_; lean_object* v_traceState_2885_; lean_object* v_env_2886_; lean_object* v_nextMacroScope_2887_; lean_object* v_ngen_2888_; lean_object* v_auxDeclNGen_2889_; lean_object* v_cache_2890_; lean_object* v_recordedDeps_2891_; lean_object* v_messages_2892_; lean_object* v_infoState_2893_; lean_object* v_snapshotTasks_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2924_; 
v___x_2884_ = lean_st_ref_take(v___y_2876_);
v_traceState_2885_ = lean_ctor_get(v___x_2884_, 4);
v_env_2886_ = lean_ctor_get(v___x_2884_, 0);
v_nextMacroScope_2887_ = lean_ctor_get(v___x_2884_, 1);
v_ngen_2888_ = lean_ctor_get(v___x_2884_, 2);
v_auxDeclNGen_2889_ = lean_ctor_get(v___x_2884_, 3);
v_cache_2890_ = lean_ctor_get(v___x_2884_, 5);
v_recordedDeps_2891_ = lean_ctor_get(v___x_2884_, 6);
v_messages_2892_ = lean_ctor_get(v___x_2884_, 7);
v_infoState_2893_ = lean_ctor_get(v___x_2884_, 8);
v_snapshotTasks_2894_ = lean_ctor_get(v___x_2884_, 9);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2896_ = v___x_2884_;
v_isShared_2897_ = v_isSharedCheck_2924_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_snapshotTasks_2894_);
lean_inc(v_infoState_2893_);
lean_inc(v_messages_2892_);
lean_inc(v_recordedDeps_2891_);
lean_inc(v_cache_2890_);
lean_inc(v_traceState_2885_);
lean_inc(v_auxDeclNGen_2889_);
lean_inc(v_ngen_2888_);
lean_inc(v_nextMacroScope_2887_);
lean_inc(v_env_2886_);
lean_dec(v___x_2884_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2924_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
uint64_t v_tid_2898_; lean_object* v_traces_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2923_; 
v_tid_2898_ = lean_ctor_get_uint64(v_traceState_2885_, sizeof(void*)*1);
v_traces_2899_ = lean_ctor_get(v_traceState_2885_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v_traceState_2885_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2901_ = v_traceState_2885_;
v_isShared_2902_ = v_isSharedCheck_2923_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_traces_2899_);
lean_dec(v_traceState_2885_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2923_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; double v___x_2905_; uint8_t v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2914_; 
v___x_2903_ = lean_box(0);
v___x_2904_ = lean_box(0);
v___x_2905_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0);
v___x_2906_ = 0;
v___x_2907_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2908_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2908_, 0, v_cls_2873_);
lean_ctor_set(v___x_2908_, 1, v___x_2904_);
lean_ctor_set(v___x_2908_, 2, v___x_2907_);
lean_ctor_set_float(v___x_2908_, sizeof(void*)*3, v___x_2905_);
lean_ctor_set_float(v___x_2908_, sizeof(void*)*3 + 8, v___x_2905_);
lean_ctor_set_uint8(v___x_2908_, sizeof(void*)*3 + 16, v___x_2906_);
v___x_2909_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___closed__0));
v___x_2910_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2908_);
lean_ctor_set(v___x_2910_, 1, v_a_2880_);
lean_ctor_set(v___x_2910_, 2, v___x_2909_);
lean_inc(v_ref_2878_);
v___x_2911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2911_, 0, v_ref_2878_);
lean_ctor_set(v___x_2911_, 1, v___x_2910_);
v___x_2912_ = l_Lean_PersistentArray_push___redArg(v_traces_2899_, v___x_2911_);
if (v_isShared_2902_ == 0)
{
lean_ctor_set(v___x_2901_, 0, v___x_2912_);
v___x_2914_ = v___x_2901_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v___x_2912_);
lean_ctor_set_uint64(v_reuseFailAlloc_2922_, sizeof(void*)*1, v_tid_2898_);
v___x_2914_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
lean_object* v___x_2916_; 
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 4, v___x_2914_);
v___x_2916_ = v___x_2896_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_env_2886_);
lean_ctor_set(v_reuseFailAlloc_2921_, 1, v_nextMacroScope_2887_);
lean_ctor_set(v_reuseFailAlloc_2921_, 2, v_ngen_2888_);
lean_ctor_set(v_reuseFailAlloc_2921_, 3, v_auxDeclNGen_2889_);
lean_ctor_set(v_reuseFailAlloc_2921_, 4, v___x_2914_);
lean_ctor_set(v_reuseFailAlloc_2921_, 5, v_cache_2890_);
lean_ctor_set(v_reuseFailAlloc_2921_, 6, v_recordedDeps_2891_);
lean_ctor_set(v_reuseFailAlloc_2921_, 7, v_messages_2892_);
lean_ctor_set(v_reuseFailAlloc_2921_, 8, v_infoState_2893_);
lean_ctor_set(v_reuseFailAlloc_2921_, 9, v_snapshotTasks_2894_);
v___x_2916_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
lean_object* v___x_2917_; lean_object* v___x_2919_; 
v___x_2917_ = lean_st_ref_put(v___y_2876_, v___x_2916_);
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 0, v___x_2903_);
v___x_2919_ = v___x_2882_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v___x_2903_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___boxed(lean_object* v_cls_2926_, lean_object* v_msg_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2926_, v_msg_2927_, v___y_2928_, v___y_2929_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
return v_res_2931_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1(void){
_start:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2933_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__0));
v___x_2934_ = l_Lean_stringToMessageData(v___x_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(lean_object* v_decl_2935_, lean_object* v_cls_2936_, lean_object* v_x_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
lean_object* v_toCold_2941_; lean_object* v_options_2942_; uint8_t v_hasTrace_2943_; 
v_toCold_2941_ = lean_ctor_get(v___y_2938_, 0);
v_options_2942_ = lean_ctor_get(v_toCold_2941_, 2);
v_hasTrace_2943_ = lean_ctor_get_uint8(v_options_2942_, sizeof(void*)*1);
if (v_hasTrace_2943_ == 0)
{
lean_object* v___x_2944_; 
lean_dec(v_cls_2936_);
v___x_2944_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2935_, v___y_2938_, v___y_2939_);
return v___x_2944_;
}
else
{
lean_object* v_inheritedTraceOptions_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; uint8_t v___x_2948_; 
v_inheritedTraceOptions_2945_ = lean_ctor_get(v_toCold_2941_, 11);
v___x_2946_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2936_);
v___x_2947_ = l_Lean_Name_append(v___x_2946_, v_cls_2936_);
v___x_2948_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2945_, v_options_2942_, v___x_2947_);
lean_dec(v___x_2947_);
if (v___x_2948_ == 0)
{
lean_object* v___x_2949_; 
lean_dec(v_cls_2936_);
v___x_2949_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2935_, v___y_2938_, v___y_2939_);
return v___x_2949_;
}
else
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2950_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
v___x_2951_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2936_, v___x_2950_, v___y_2938_, v___y_2939_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v___x_2952_; 
lean_dec_ref_known(v___x_2951_, 1);
v___x_2952_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2935_, v___y_2938_, v___y_2939_);
return v___x_2952_;
}
else
{
lean_dec(v_decl_2935_);
return v___x_2951_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___boxed(lean_object* v_decl_2953_, lean_object* v_cls_2954_, lean_object* v_x_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_2953_, v_cls_2954_, v_x_2955_, v___y_2956_, v___y_2957_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v_x_2955_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(lean_object* v_opt_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v___x_2963_; uint8_t v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2963_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2961_);
v___x_2964_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_2963_, v_opt_2960_);
lean_dec_ref(v___x_2963_);
v___x_2965_ = lean_box(v___x_2964_);
v___x_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2965_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg___boxed(lean_object* v_opt_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_2967_, v___y_2968_);
lean_dec_ref(v___y_2968_);
lean_dec_ref(v_opt_2967_);
return v_res_2970_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(lean_object* v_x_2971_){
_start:
{
if (lean_obj_tag(v_x_2971_) == 0)
{
uint8_t v___x_2972_; 
v___x_2972_ = 1;
return v___x_2972_;
}
else
{
lean_object* v_head_2973_; lean_object* v_tail_2974_; uint8_t v___x_2975_; 
v_head_2973_ = lean_ctor_get(v_x_2971_, 0);
v_tail_2974_ = lean_ctor_get(v_x_2971_, 1);
v___x_2975_ = l_Lean_isPrivateName(v_head_2973_);
if (v___x_2975_ == 0)
{
return v___x_2975_;
}
else
{
v_x_2971_ = v_tail_2974_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2___boxed(lean_object* v_x_2977_){
_start:
{
uint8_t v_res_2978_; lean_object* v_r_2979_; 
v_res_2978_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v_x_2977_);
lean_dec(v_x_2977_);
v_r_2979_ = lean_box(v_res_2978_);
return v_r_2979_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3(void){
_start:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2985_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__2));
v___x_2986_ = l_Lean_stringToMessageData(v___x_2985_);
return v___x_2986_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5(void){
_start:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2988_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__4));
v___x_2989_ = l_Lean_stringToMessageData(v___x_2988_);
return v___x_2989_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7(void){
_start:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2991_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__6));
v___x_2992_ = l_Lean_stringToMessageData(v___x_2991_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(lean_object* v_decl_2993_, uint8_t v_hasTrace_2994_, uint8_t v___x_2995_, lean_object* v___x_2996_, lean_object* v_cls_2997_, lean_object* v___x_2998_, lean_object* v_____x_2999_, lean_object* v_exportedInfo_x3f_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v_a_3007_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v_a_3020_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v_snd_3103_; lean_object* v_fst_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3234_; 
v_snd_3103_ = lean_ctor_get(v_____x_2999_, 1);
v_fst_3104_ = lean_ctor_get(v_____x_2999_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v_____x_2999_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3106_ = v_____x_2999_;
v_isShared_3107_ = v_isSharedCheck_3234_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_snd_3103_);
lean_inc(v_fst_3104_);
lean_dec(v_____x_2999_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3234_;
goto v_resetjp_3105_;
}
v___jp_3004_:
{
lean_object* v___x_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3015_; 
v___x_3008_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3005_, v___y_3006_);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3015_ == 0)
{
lean_object* v_unused_3016_; 
v_unused_3016_ = lean_ctor_get(v___x_3008_, 0);
lean_dec(v_unused_3016_);
v___x_3010_ = v___x_3008_;
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
else
{
lean_dec(v___x_3008_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3013_; 
if (v_isShared_3011_ == 0)
{
lean_ctor_set_tag(v___x_3010_, 1);
lean_ctor_set(v___x_3010_, 0, v_a_3007_);
v___x_3013_ = v___x_3010_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_a_3007_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
v___jp_3017_:
{
lean_object* v___x_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
v___x_3021_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3018_, v___y_3019_);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3028_ == 0)
{
lean_object* v_unused_3029_; 
v_unused_3029_ = lean_ctor_get(v___x_3021_, 0);
lean_dec(v_unused_3029_);
v___x_3023_ = v___x_3021_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_dec(v___x_3021_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3026_; 
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 0, v_a_3020_);
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_a_3020_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
v___jp_3030_:
{
lean_object* v___x_3042_; 
lean_inc_ref(v___y_3040_);
v___x_3042_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3038_, v___y_3040_, v___y_3037_, v___y_3041_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v___x_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3089_; 
lean_dec_ref_known(v___x_3042_, 1);
lean_dec(v___y_3032_);
lean_inc_ref(v___y_3031_);
v___x_3043_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3031_, v___y_3036_);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3089_ == 0)
{
lean_object* v_unused_3090_; 
v_unused_3090_ = lean_ctor_get(v___x_3043_, 0);
lean_dec(v_unused_3090_);
v___x_3045_ = v___x_3043_;
v_isShared_3046_ = v_isSharedCheck_3089_;
goto v_resetjp_3044_;
}
else
{
lean_dec(v___x_3043_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3089_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; uint8_t v___x_3049_; 
v___x_3047_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3033_);
v___x_3048_ = l_Lean_Elab_async;
v___x_3049_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_3047_, v___x_3048_);
lean_dec_ref(v___x_3047_);
if (v___x_3049_ == 0)
{
lean_object* v___x_3050_; lean_object* v_r_3051_; 
lean_del_object(v___x_3045_);
lean_dec_ref(v___y_3035_);
lean_dec_ref(v___y_3034_);
v___x_3050_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3040_, v___y_3036_);
lean_dec_ref(v___x_3050_);
v_r_3051_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2993_, v___y_3033_, v___y_3036_);
if (lean_obj_tag(v_r_3051_) == 0)
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3061_; 
v_a_3052_ = lean_ctor_get(v_r_3051_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v_r_3051_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3054_ = v_r_3051_;
v_isShared_3055_ = v_isSharedCheck_3061_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v_r_3051_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3061_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
lean_inc(v_a_3052_);
if (v_isShared_3055_ == 0)
{
lean_ctor_set_tag(v___x_3054_, 1);
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3052_);
v___x_3057_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
lean_object* v___x_3058_; 
v___x_3058_ = lean_apply_2(v___y_3039_, v___x_3057_, lean_box(0));
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_dec_ref_known(v___x_3058_, 1);
v___y_3018_ = v___y_3031_;
v___y_3019_ = v___y_3036_;
v_a_3020_ = v_a_3052_;
goto v___jp_3017_;
}
else
{
lean_object* v_a_3059_; 
lean_dec(v_a_3052_);
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref_known(v___x_3058_, 1);
v___y_3005_ = v___y_3031_;
v___y_3006_ = v___y_3036_;
v_a_3007_ = v_a_3059_;
goto v___jp_3004_;
}
}
}
}
else
{
lean_object* v_a_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v_a_3062_ = lean_ctor_get(v_r_3051_, 0);
lean_inc(v_a_3062_);
lean_dec_ref_known(v_r_3051_, 1);
v___x_3063_ = lean_box(0);
v___x_3064_ = lean_apply_2(v___y_3039_, v___x_3063_, lean_box(0));
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_dec_ref_known(v___x_3064_, 1);
v___y_3005_ = v___y_3031_;
v___y_3006_ = v___y_3036_;
v_a_3007_ = v_a_3062_;
goto v___jp_3004_;
}
else
{
lean_object* v_a_3065_; 
lean_dec(v_a_3062_);
v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
lean_inc(v_a_3065_);
lean_dec_ref_known(v___x_3064_, 1);
v___y_3005_ = v___y_3031_;
v___y_3006_ = v___y_3036_;
v_a_3007_ = v_a_3065_;
goto v___jp_3004_;
}
}
}
else
{
lean_object* v___x_3066_; lean_object* v___x_3068_; 
lean_dec_ref(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec_ref(v___y_3031_);
lean_dec(v_decl_2993_);
v___x_3066_ = l_IO_CancelToken_new();
if (v_isShared_3046_ == 0)
{
lean_ctor_set_tag(v___x_3045_, 1);
lean_ctor_set(v___x_3045_, 0, v___x_3066_);
v___x_3068_ = v___x_3045_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3066_);
v___x_3068_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3069_ = lean_unsigned_to_nat(0u);
v___x_3070_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_3071_ = l_Lean_Name_toString(v___x_3070_, v_hasTrace_2994_);
lean_inc_ref(v___x_3068_);
v___x_3072_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3035_, v___x_3068_, v___x_3071_, v___y_3033_, v___y_3036_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v_a_3073_; lean_object* v_checked_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
lean_inc(v_a_3073_);
lean_dec_ref_known(v___x_3072_, 1);
v_checked_3074_ = lean_ctor_get(v___y_3034_, 2);
lean_inc_ref(v_checked_3074_);
lean_dec_ref(v___y_3034_);
v___x_3075_ = lean_io_map_task(v_a_3073_, v_checked_3074_, v___x_3069_, v___x_2995_);
v___x_3076_ = lean_box(0);
v___x_3077_ = lean_box(2);
v___x_3078_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3076_);
lean_ctor_set(v___x_3078_, 1, v___x_3077_);
lean_ctor_set(v___x_3078_, 2, v___x_3068_);
lean_ctor_set(v___x_3078_, 3, v___x_3075_);
v___x_3079_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3078_, v___y_3036_);
return v___x_3079_;
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
lean_dec_ref(v___x_3068_);
lean_dec_ref(v___y_3034_);
v_a_3080_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3072_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3072_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3102_; 
lean_dec_ref(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec_ref(v___y_3035_);
lean_dec_ref(v___y_3034_);
lean_dec_ref(v___y_3031_);
lean_dec(v_decl_2993_);
v_a_3091_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3093_ = v___x_3042_;
v_isShared_3094_ = v_isSharedCheck_3102_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3042_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3102_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3100_; 
v___x_3095_ = lean_io_error_to_string(v_a_3091_);
v___x_3096_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3095_);
v___x_3097_ = l_Lean_MessageData_ofFormat(v___x_3096_);
v___x_3098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___y_3032_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 0, v___x_3098_);
v___x_3100_ = v___x_3093_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3098_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
v_resetjp_3105_:
{
lean_object* v_fst_3108_; lean_object* v_snd_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3233_; 
v_fst_3108_ = lean_ctor_get(v_snd_3103_, 0);
v_snd_3109_ = lean_ctor_get(v_snd_3103_, 1);
v_isSharedCheck_3233_ = !lean_is_exclusive(v_snd_3103_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3111_ = v_snd_3103_;
v_isShared_3112_ = v_isSharedCheck_3233_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_snd_3109_);
lean_inc(v_fst_3108_);
lean_dec(v_snd_3103_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3233_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v_exportedInfo_x3f_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3163_; lean_object* v___y_3164_; uint8_t v___y_3165_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___x_3223_; lean_object* v_env_3224_; uint8_t v___x_3225_; 
v___x_3223_ = lean_st_ref_get(v___y_3002_);
v_env_3224_ = lean_ctor_get(v___x_3223_, 0);
lean_inc_ref(v_env_3224_);
lean_dec(v___x_3223_);
v___x_3225_ = l_Lean_Environment_containsOnBranch(v_env_3224_, v_fst_3104_);
lean_dec_ref(v_env_3224_);
if (v___x_3225_ == 0)
{
lean_del_object(v___x_3106_);
v___y_3188_ = v___y_3001_;
v___y_3189_ = v___y_3002_;
goto v___jp_3187_;
}
else
{
lean_object* v___x_3226_; lean_object* v_env_3227_; lean_object* v___x_3228_; lean_object* v___x_3230_; 
lean_del_object(v___x_3111_);
lean_dec(v_snd_3109_);
lean_dec(v_fst_3108_);
lean_dec(v_exportedInfo_x3f_3000_);
lean_dec(v___x_2998_);
lean_dec(v_cls_2997_);
lean_dec_ref(v___x_2996_);
lean_dec(v_decl_2993_);
v___x_3226_ = lean_st_ref_get(v___y_3002_);
v_env_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc_ref(v_env_3227_);
lean_dec(v___x_3226_);
v___x_3228_ = lean_elab_environment_to_kernel_env(v_env_3227_);
if (v_isShared_3107_ == 0)
{
lean_ctor_set_tag(v___x_3106_, 1);
lean_ctor_set(v___x_3106_, 1, v_fst_3104_);
lean_ctor_set(v___x_3106_, 0, v___x_3228_);
v___x_3230_ = v___x_3106_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v___x_3228_);
lean_ctor_set(v_reuseFailAlloc_3232_, 1, v_fst_3104_);
v___x_3230_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
lean_object* v___x_3231_; 
v___x_3231_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3230_, v___y_3001_, v___y_3002_);
return v___x_3231_;
}
}
v___jp_3113_:
{
lean_object* v_ref_3119_; uint8_t v___x_3120_; lean_object* v___x_3121_; 
v_ref_3119_ = lean_ctor_get(v___y_3114_, 2);
v___x_3120_ = lean_unbox(v_snd_3109_);
lean_dec(v_snd_3109_);
lean_inc_ref(v___y_3117_);
v___x_3121_ = l_Lean_Environment_addConstAsync(v___y_3117_, v_fst_3104_, v___x_3120_, v___y_3118_, v___x_2995_, v_hasTrace_2994_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_object* v_a_3122_; lean_object* v_mainEnv_3123_; lean_object* v_asyncEnv_3124_; lean_object* v___f_3125_; lean_object* v___f_3126_; lean_object* v___x_3127_; 
lean_del_object(v___x_3111_);
v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
lean_inc_n(v_a_3122_, 3);
lean_dec_ref_known(v___x_3121_, 1);
v_mainEnv_3123_ = lean_ctor_get(v_a_3122_, 0);
lean_inc_ref(v_mainEnv_3123_);
v_asyncEnv_3124_ = lean_ctor_get(v_a_3122_, 1);
lean_inc_ref_n(v_asyncEnv_3124_, 2);
lean_inc(v_ref_3119_);
lean_inc(v___y_3115_);
v___f_3125_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3125_, 0, v___y_3115_);
lean_closure_set(v___f_3125_, 1, v_a_3122_);
lean_closure_set(v___f_3125_, 2, v_ref_3119_);
lean_inc(v_decl_2993_);
v___f_3126_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3126_, 0, v_a_3122_);
lean_closure_set(v___f_3126_, 1, v_asyncEnv_3124_);
lean_closure_set(v___f_3126_, 2, v_decl_2993_);
v___x_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3127_, 0, v_fst_3108_);
if (lean_obj_tag(v___y_3116_) == 0)
{
lean_inc_ref(v___x_3127_);
lean_inc(v_ref_3119_);
v___y_3031_ = v_mainEnv_3123_;
v___y_3032_ = v_ref_3119_;
v___y_3033_ = v___y_3114_;
v___y_3034_ = v___y_3117_;
v___y_3035_ = v___f_3126_;
v___y_3036_ = v___y_3115_;
v___y_3037_ = v___x_3127_;
v___y_3038_ = v_a_3122_;
v___y_3039_ = v___f_3125_;
v___y_3040_ = v_asyncEnv_3124_;
v___y_3041_ = v___x_3127_;
goto v___jp_3030_;
}
else
{
lean_inc(v_ref_3119_);
v___y_3031_ = v_mainEnv_3123_;
v___y_3032_ = v_ref_3119_;
v___y_3033_ = v___y_3114_;
v___y_3034_ = v___y_3117_;
v___y_3035_ = v___f_3126_;
v___y_3036_ = v___y_3115_;
v___y_3037_ = v___x_3127_;
v___y_3038_ = v_a_3122_;
v___y_3039_ = v___f_3125_;
v___y_3040_ = v_asyncEnv_3124_;
v___y_3041_ = v___y_3116_;
goto v___jp_3030_;
}
}
else
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3141_; 
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec(v_fst_3108_);
lean_dec(v_decl_2993_);
v_a_3128_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3130_ = v___x_3121_;
v_isShared_3131_ = v_isSharedCheck_3141_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3121_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3141_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3136_; 
v___x_3132_ = lean_io_error_to_string(v_a_3128_);
v___x_3133_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3132_);
v___x_3134_ = l_Lean_MessageData_ofFormat(v___x_3133_);
lean_inc(v_ref_3119_);
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 1, v___x_3134_);
lean_ctor_set(v___x_3111_, 0, v_ref_3119_);
v___x_3136_ = v___x_3111_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_ref_3119_);
lean_ctor_set(v_reuseFailAlloc_3140_, 1, v___x_3134_);
v___x_3136_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
lean_object* v___x_3138_; 
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v___x_3136_);
v___x_3138_ = v___x_3130_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v___x_3136_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
}
v___jp_3142_:
{
lean_object* v___x_3146_; 
v___x_3146_ = lean_st_ref_get(v___y_3145_);
if (lean_obj_tag(v_exportedInfo_x3f_3143_) == 0)
{
lean_object* v_env_3147_; lean_object* v___x_3148_; 
v_env_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc_ref(v_env_3147_);
lean_dec(v___x_3146_);
v___x_3148_ = lean_box(0);
v___y_3114_ = v___y_3144_;
v___y_3115_ = v___y_3145_;
v___y_3116_ = v_exportedInfo_x3f_3143_;
v___y_3117_ = v_env_3147_;
v___y_3118_ = v___x_3148_;
goto v___jp_3113_;
}
else
{
lean_object* v_env_3149_; lean_object* v_val_3150_; uint8_t v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v_env_3149_ = lean_ctor_get(v___x_3146_, 0);
lean_inc_ref(v_env_3149_);
lean_dec(v___x_3146_);
v_val_3150_ = lean_ctor_get(v_exportedInfo_x3f_3143_, 0);
v___x_3151_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3150_);
v___x_3152_ = lean_box(v___x_3151_);
v___x_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3152_);
v___y_3114_ = v___y_3144_;
v___y_3115_ = v___y_3145_;
v___y_3116_ = v_exportedInfo_x3f_3143_;
v___y_3117_ = v_env_3149_;
v___y_3118_ = v___x_3153_;
goto v___jp_3113_;
}
}
v___jp_3154_:
{
lean_object* v___x_3157_; 
lean_inc(v_fst_3108_);
v___x_3157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3157_, 0, v_fst_3108_);
v_exportedInfo_x3f_3143_ = v___x_3157_;
v___y_3144_ = v___y_3155_;
v___y_3145_ = v___y_3156_;
goto v___jp_3142_;
}
v___jp_3158_:
{
lean_object* v___x_3161_; 
lean_inc(v_fst_3108_);
v___x_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3161_, 0, v_fst_3108_);
v_exportedInfo_x3f_3143_ = v___x_3161_;
v___y_3144_ = v___y_3159_;
v___y_3145_ = v___y_3160_;
goto v___jp_3142_;
}
v___jp_3162_:
{
lean_object* v___x_3166_; lean_object* v_env_3167_; lean_object* v_nextMacroScope_3168_; lean_object* v_ngen_3169_; lean_object* v_auxDeclNGen_3170_; lean_object* v_traceState_3171_; lean_object* v_recordedDeps_3172_; lean_object* v_messages_3173_; lean_object* v_infoState_3174_; lean_object* v_snapshotTasks_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3185_; 
v___x_3166_ = lean_st_ref_take(v___y_3164_);
v_env_3167_ = lean_ctor_get(v___x_3166_, 0);
v_nextMacroScope_3168_ = lean_ctor_get(v___x_3166_, 1);
v_ngen_3169_ = lean_ctor_get(v___x_3166_, 2);
v_auxDeclNGen_3170_ = lean_ctor_get(v___x_3166_, 3);
v_traceState_3171_ = lean_ctor_get(v___x_3166_, 4);
v_recordedDeps_3172_ = lean_ctor_get(v___x_3166_, 6);
v_messages_3173_ = lean_ctor_get(v___x_3166_, 7);
v_infoState_3174_ = lean_ctor_get(v___x_3166_, 8);
v_snapshotTasks_3175_ = lean_ctor_get(v___x_3166_, 9);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3185_ == 0)
{
lean_object* v_unused_3186_; 
v_unused_3186_ = lean_ctor_get(v___x_3166_, 5);
lean_dec(v_unused_3186_);
v___x_3177_ = v___x_3166_;
v_isShared_3178_ = v_isSharedCheck_3185_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_snapshotTasks_3175_);
lean_inc(v_infoState_3174_);
lean_inc(v_messages_3173_);
lean_inc(v_recordedDeps_3172_);
lean_inc(v_traceState_3171_);
lean_inc(v_auxDeclNGen_3170_);
lean_inc(v_ngen_3169_);
lean_inc(v_nextMacroScope_3168_);
lean_inc(v_env_3167_);
lean_dec(v___x_3166_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3185_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3182_; 
v___x_3179_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3109_);
lean_inc(v_fst_3104_);
v___x_3180_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3179_, v_env_3167_, v_fst_3104_, v_snd_3109_, v___y_3165_);
if (v_isShared_3178_ == 0)
{
lean_ctor_set(v___x_3177_, 5, v___x_2996_);
lean_ctor_set(v___x_3177_, 0, v___x_3180_);
v___x_3182_ = v___x_3177_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v___x_3180_);
lean_ctor_set(v_reuseFailAlloc_3184_, 1, v_nextMacroScope_3168_);
lean_ctor_set(v_reuseFailAlloc_3184_, 2, v_ngen_3169_);
lean_ctor_set(v_reuseFailAlloc_3184_, 3, v_auxDeclNGen_3170_);
lean_ctor_set(v_reuseFailAlloc_3184_, 4, v_traceState_3171_);
lean_ctor_set(v_reuseFailAlloc_3184_, 5, v___x_2996_);
lean_ctor_set(v_reuseFailAlloc_3184_, 6, v_recordedDeps_3172_);
lean_ctor_set(v_reuseFailAlloc_3184_, 7, v_messages_3173_);
lean_ctor_set(v_reuseFailAlloc_3184_, 8, v_infoState_3174_);
lean_ctor_set(v_reuseFailAlloc_3184_, 9, v_snapshotTasks_3175_);
v___x_3182_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
lean_object* v___x_3183_; 
v___x_3183_ = lean_st_ref_put(v___y_3164_, v___x_3182_);
v_exportedInfo_x3f_3143_ = v_exportedInfo_x3f_3000_;
v___y_3144_ = v___y_3163_;
v___y_3145_ = v___y_3164_;
goto v___jp_3142_;
}
}
}
v___jp_3187_:
{
lean_object* v___x_3190_; uint8_t v___x_3191_; 
lean_inc(v_decl_2993_);
v___x_3190_ = l_Lean_Declaration_getTopLevelNames(v_decl_2993_);
v___x_3191_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3190_);
lean_dec(v___x_3190_);
if (v___x_3191_ == 0)
{
lean_dec(v___x_2998_);
if (lean_obj_tag(v_exportedInfo_x3f_3000_) == 0)
{
if (v___x_3191_ == 0)
{
lean_object* v_toCold_3192_; lean_object* v_options_3193_; uint8_t v_hasTrace_3194_; 
lean_dec_ref(v___x_2996_);
v_toCold_3192_ = lean_ctor_get(v___y_3188_, 0);
v_options_3193_ = lean_ctor_get(v_toCold_3192_, 2);
v_hasTrace_3194_ = lean_ctor_get_uint8(v_options_3193_, sizeof(void*)*1);
if (v_hasTrace_3194_ == 0)
{
lean_dec(v_cls_2997_);
v___y_3159_ = v___y_3188_;
v___y_3160_ = v___y_3189_;
goto v___jp_3158_;
}
else
{
lean_object* v_inheritedTraceOptions_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; uint8_t v___x_3198_; 
v_inheritedTraceOptions_3195_ = lean_ctor_get(v_toCold_3192_, 11);
v___x_3196_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2997_);
v___x_3197_ = l_Lean_Name_append(v___x_3196_, v_cls_2997_);
v___x_3198_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3195_, v_options_3193_, v___x_3197_);
lean_dec(v___x_3197_);
if (v___x_3198_ == 0)
{
lean_dec(v_cls_2997_);
v___y_3159_ = v___y_3188_;
v___y_3160_ = v___y_3189_;
goto v___jp_3158_;
}
else
{
lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3199_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_3200_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2997_, v___x_3199_, v___y_3188_, v___y_3189_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_dec_ref_known(v___x_3200_, 1);
v___y_3159_ = v___y_3188_;
v___y_3160_ = v___y_3189_;
goto v___jp_3158_;
}
else
{
lean_del_object(v___x_3111_);
lean_dec(v_snd_3109_);
lean_dec(v_fst_3108_);
lean_dec(v_fst_3104_);
lean_dec(v_decl_2993_);
return v___x_3200_;
}
}
}
}
else
{
lean_dec(v_cls_2997_);
v___y_3163_ = v___y_3188_;
v___y_3164_ = v___y_3189_;
v___y_3165_ = v___x_3191_;
goto v___jp_3162_;
}
}
else
{
lean_dec(v_cls_2997_);
v___y_3163_ = v___y_3188_;
v___y_3164_ = v___y_3189_;
v___y_3165_ = v___x_3191_;
goto v___jp_3162_;
}
}
else
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v_a_3203_; uint8_t v___x_3204_; 
lean_dec(v_exportedInfo_x3f_3000_);
lean_dec_ref(v___x_2996_);
v___x_3201_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3202_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3201_, v___y_3188_);
v_a_3203_ = lean_ctor_get(v___x_3202_, 0);
lean_inc(v_a_3203_);
lean_dec_ref(v___x_3202_);
v___x_3204_ = lean_unbox(v_a_3203_);
lean_dec(v_a_3203_);
if (v___x_3204_ == 0)
{
lean_object* v_toCold_3205_; lean_object* v_options_3206_; uint8_t v_hasTrace_3207_; 
v_toCold_3205_ = lean_ctor_get(v___y_3188_, 0);
v_options_3206_ = lean_ctor_get(v_toCold_3205_, 2);
v_hasTrace_3207_ = lean_ctor_get_uint8(v_options_3206_, sizeof(void*)*1);
if (v_hasTrace_3207_ == 0)
{
lean_dec(v_cls_2997_);
v_exportedInfo_x3f_3143_ = v___x_2998_;
v___y_3144_ = v___y_3188_;
v___y_3145_ = v___y_3189_;
goto v___jp_3142_;
}
else
{
lean_object* v_inheritedTraceOptions_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; uint8_t v___x_3211_; 
v_inheritedTraceOptions_3208_ = lean_ctor_get(v_toCold_3205_, 11);
v___x_3209_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2997_);
v___x_3210_ = l_Lean_Name_append(v___x_3209_, v_cls_2997_);
v___x_3211_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3208_, v_options_3206_, v___x_3210_);
lean_dec(v___x_3210_);
if (v___x_3211_ == 0)
{
lean_dec(v_cls_2997_);
v_exportedInfo_x3f_3143_ = v___x_2998_;
v___y_3144_ = v___y_3188_;
v___y_3145_ = v___y_3189_;
goto v___jp_3142_;
}
else
{
lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3212_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_3213_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2997_, v___x_3212_, v___y_3188_, v___y_3189_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_dec_ref_known(v___x_3213_, 1);
v_exportedInfo_x3f_3143_ = v___x_2998_;
v___y_3144_ = v___y_3188_;
v___y_3145_ = v___y_3189_;
goto v___jp_3142_;
}
else
{
lean_del_object(v___x_3111_);
lean_dec(v_snd_3109_);
lean_dec(v_fst_3108_);
lean_dec(v_fst_3104_);
lean_dec(v___x_2998_);
lean_dec(v_decl_2993_);
return v___x_3213_;
}
}
}
}
else
{
lean_object* v_toCold_3214_; lean_object* v_options_3215_; uint8_t v_hasTrace_3216_; 
lean_dec(v___x_2998_);
v_toCold_3214_ = lean_ctor_get(v___y_3188_, 0);
v_options_3215_ = lean_ctor_get(v_toCold_3214_, 2);
v_hasTrace_3216_ = lean_ctor_get_uint8(v_options_3215_, sizeof(void*)*1);
if (v_hasTrace_3216_ == 0)
{
lean_dec(v_cls_2997_);
v___y_3155_ = v___y_3188_;
v___y_3156_ = v___y_3189_;
goto v___jp_3154_;
}
else
{
lean_object* v_inheritedTraceOptions_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; uint8_t v___x_3220_; 
v_inheritedTraceOptions_3217_ = lean_ctor_get(v_toCold_3214_, 11);
v___x_3218_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2997_);
v___x_3219_ = l_Lean_Name_append(v___x_3218_, v_cls_2997_);
v___x_3220_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3217_, v_options_3215_, v___x_3219_);
lean_dec(v___x_3219_);
if (v___x_3220_ == 0)
{
lean_dec(v_cls_2997_);
v___y_3155_ = v___y_3188_;
v___y_3156_ = v___y_3189_;
goto v___jp_3154_;
}
else
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3221_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_3222_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2997_, v___x_3221_, v___y_3188_, v___y_3189_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_dec_ref_known(v___x_3222_, 1);
v___y_3155_ = v___y_3188_;
v___y_3156_ = v___y_3189_;
goto v___jp_3154_;
}
else
{
lean_del_object(v___x_3111_);
lean_dec(v_snd_3109_);
lean_dec(v_fst_3108_);
lean_dec(v_fst_3104_);
lean_dec(v_decl_2993_);
return v___x_3222_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed(lean_object* v_decl_3235_, lean_object* v_hasTrace_3236_, lean_object* v___x_3237_, lean_object* v___x_3238_, lean_object* v_cls_3239_, lean_object* v___x_3240_, lean_object* v_____x_3241_, lean_object* v_exportedInfo_x3f_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
uint8_t v_hasTrace_boxed_3246_; uint8_t v___x_53264__boxed_3247_; lean_object* v_res_3248_; 
v_hasTrace_boxed_3246_ = lean_unbox(v_hasTrace_3236_);
v___x_53264__boxed_3247_ = lean_unbox(v___x_3237_);
v_res_3248_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_decl_3235_, v_hasTrace_boxed_3246_, v___x_53264__boxed_3247_, v___x_3238_, v_cls_3239_, v___x_3240_, v_____x_3241_, v_exportedInfo_x3f_3242_, v___y_3243_, v___y_3244_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
return v_res_3248_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1(void){
_start:
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3250_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__0));
v___x_3251_ = l_Lean_stringToMessageData(v___x_3250_);
return v___x_3251_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3(void){
_start:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3253_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__2));
v___x_3254_ = l_Lean_stringToMessageData(v___x_3253_);
return v___x_3254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(lean_object* v___f_3255_, uint8_t v___x_3256_, lean_object* v_cls_3257_, lean_object* v___x_3258_, uint8_t v_forceExpose_3259_, lean_object* v_defn_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
lean_object* v_exportedInfo_x3f_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; uint8_t v___y_3280_; uint8_t v___y_3285_; lean_object* v___x_3290_; lean_object* v_env_3291_; lean_object* v___x_3292_; uint8_t v___y_3294_; lean_object* v_env_3310_; 
v___x_3290_ = lean_st_ref_get(v___y_3262_);
v_env_3291_ = lean_ctor_get(v___x_3290_, 0);
lean_inc_ref(v_env_3291_);
lean_dec(v___x_3290_);
v___x_3292_ = lean_st_ref_get(v___y_3262_);
v_env_3310_ = lean_ctor_get(v___x_3292_, 0);
lean_inc_ref(v_env_3310_);
lean_dec(v___x_3292_);
if (v_forceExpose_3259_ == 0)
{
goto v___jp_3311_;
}
else
{
if (v___x_3256_ == 0)
{
lean_dec_ref(v_env_3310_);
lean_dec_ref(v_env_3291_);
lean_dec(v_cls_3257_);
v_exportedInfo_x3f_3265_ = v___x_3258_;
v___y_3266_ = v___y_3261_;
v___y_3267_ = v___y_3262_;
goto v___jp_3264_;
}
else
{
goto v___jp_3311_;
}
}
v___jp_3264_:
{
lean_object* v_toConstantVal_3268_; lean_object* v_name_3269_; lean_object* v___x_3270_; uint8_t v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v_toConstantVal_3268_ = lean_ctor_get(v_defn_3260_, 0);
v_name_3269_ = lean_ctor_get(v_toConstantVal_3268_, 0);
lean_inc(v_name_3269_);
v___x_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3270_, 0, v_defn_3260_);
v___x_3271_ = 0;
v___x_3272_ = lean_box(v___x_3271_);
v___x_3273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3270_);
lean_ctor_set(v___x_3273_, 1, v___x_3272_);
v___x_3274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3274_, 0, v_name_3269_);
lean_ctor_set(v___x_3274_, 1, v___x_3273_);
lean_inc(v___y_3267_);
lean_inc_ref(v___y_3266_);
v___x_3275_ = lean_apply_5(v___f_3255_, v___x_3274_, v_exportedInfo_x3f_3265_, v___y_3266_, v___y_3267_, lean_box(0));
return v___x_3275_;
}
v___jp_3276_:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3281_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3281_, 0, v___y_3277_);
lean_ctor_set_uint8(v___x_3281_, sizeof(void*)*1, v___y_3280_);
v___x_3282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3281_);
v___x_3283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3282_);
v_exportedInfo_x3f_3265_ = v___x_3283_;
v___y_3266_ = v___y_3278_;
v___y_3267_ = v___y_3279_;
goto v___jp_3264_;
}
v___jp_3284_:
{
lean_object* v_toConstantVal_3286_; uint8_t v_safety_3287_; uint8_t v___x_3288_; uint8_t v___x_3289_; 
v_toConstantVal_3286_ = lean_ctor_get(v_defn_3260_, 0);
v_safety_3287_ = lean_ctor_get_uint8(v_defn_3260_, sizeof(void*)*4);
v___x_3288_ = 1;
v___x_3289_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3287_, v___x_3288_);
if (v___x_3289_ == 0)
{
lean_inc_ref(v_toConstantVal_3286_);
v___y_3277_ = v_toConstantVal_3286_;
v___y_3278_ = v___y_3261_;
v___y_3279_ = v___y_3262_;
v___y_3280_ = v___y_3285_;
goto v___jp_3276_;
}
else
{
lean_inc_ref(v_toConstantVal_3286_);
v___y_3277_ = v_toConstantVal_3286_;
v___y_3278_ = v___y_3261_;
v___y_3279_ = v___y_3262_;
v___y_3280_ = v___x_3256_;
goto v___jp_3276_;
}
}
v___jp_3293_:
{
lean_object* v_toCold_3295_; lean_object* v_options_3296_; uint8_t v_hasTrace_3297_; 
v_toCold_3295_ = lean_ctor_get(v___y_3261_, 0);
v_options_3296_ = lean_ctor_get(v_toCold_3295_, 2);
v_hasTrace_3297_ = lean_ctor_get_uint8(v_options_3296_, sizeof(void*)*1);
if (v_hasTrace_3297_ == 0)
{
lean_dec(v_cls_3257_);
v___y_3285_ = v___y_3294_;
goto v___jp_3284_;
}
else
{
lean_object* v_inheritedTraceOptions_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; uint8_t v___x_3301_; 
v_inheritedTraceOptions_3298_ = lean_ctor_get(v_toCold_3295_, 11);
v___x_3299_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3257_);
v___x_3300_ = l_Lean_Name_append(v___x_3299_, v_cls_3257_);
v___x_3301_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3298_, v_options_3296_, v___x_3300_);
lean_dec(v___x_3300_);
if (v___x_3301_ == 0)
{
lean_dec(v_cls_3257_);
v___y_3285_ = v___y_3294_;
goto v___jp_3284_;
}
else
{
lean_object* v_toConstantVal_3302_; lean_object* v_name_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v_toConstantVal_3302_ = lean_ctor_get(v_defn_3260_, 0);
v_name_3303_ = lean_ctor_get(v_toConstantVal_3302_, 0);
v___x_3304_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_3303_);
v___x_3305_ = l_Lean_MessageData_ofName(v_name_3303_);
v___x_3306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3304_);
lean_ctor_set(v___x_3306_, 1, v___x_3305_);
v___x_3307_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_3308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3306_);
lean_ctor_set(v___x_3308_, 1, v___x_3307_);
v___x_3309_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3257_, v___x_3308_, v___y_3261_, v___y_3262_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_dec_ref_known(v___x_3309_, 1);
v___y_3285_ = v___y_3294_;
goto v___jp_3284_;
}
else
{
lean_dec_ref(v_defn_3260_);
lean_dec_ref(v___f_3255_);
return v___x_3309_;
}
}
}
}
v___jp_3311_:
{
lean_object* v___x_3312_; uint8_t v_isModule_3313_; 
v___x_3312_ = l_Lean_Environment_header(v_env_3291_);
lean_dec_ref(v_env_3291_);
v_isModule_3313_ = lean_ctor_get_uint8(v___x_3312_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3312_);
if (v_isModule_3313_ == 0)
{
lean_dec_ref(v_env_3310_);
lean_dec(v_cls_3257_);
v_exportedInfo_x3f_3265_ = v___x_3258_;
v___y_3266_ = v___y_3261_;
v___y_3267_ = v___y_3262_;
goto v___jp_3264_;
}
else
{
uint8_t v_isExporting_3314_; 
v_isExporting_3314_ = lean_ctor_get_uint8(v_env_3310_, sizeof(void*)*13);
lean_dec_ref(v_env_3310_);
if (v_isExporting_3314_ == 0)
{
lean_dec(v___x_3258_);
v___y_3294_ = v_isModule_3313_;
goto v___jp_3293_;
}
else
{
if (v___x_3256_ == 0)
{
lean_dec(v_cls_3257_);
v_exportedInfo_x3f_3265_ = v___x_3258_;
v___y_3266_ = v___y_3261_;
v___y_3267_ = v___y_3262_;
goto v___jp_3264_;
}
else
{
lean_dec(v___x_3258_);
v___y_3294_ = v___x_3256_;
goto v___jp_3293_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed(lean_object* v___f_3315_, lean_object* v___x_3316_, lean_object* v_cls_3317_, lean_object* v___x_3318_, lean_object* v_forceExpose_3319_, lean_object* v_defn_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
uint8_t v___x_53739__boxed_3324_; uint8_t v_forceExpose_boxed_3325_; lean_object* v_res_3326_; 
v___x_53739__boxed_3324_ = lean_unbox(v___x_3316_);
v_forceExpose_boxed_3325_ = lean_unbox(v_forceExpose_3319_);
v_res_3326_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v___f_3315_, v___x_53739__boxed_3324_, v_cls_3317_, v___x_3318_, v_forceExpose_boxed_3325_, v_defn_3320_, v___y_3321_, v___y_3322_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(lean_object* v_val_3327_, lean_object* v___f_3328_, lean_object* v_____r_3329_, lean_object* v_exportedInfo_x3f_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
lean_object* v_toConstantVal_3334_; lean_object* v_name_3335_; lean_object* v___x_3336_; uint8_t v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v_toConstantVal_3334_ = lean_ctor_get(v_val_3327_, 0);
v_name_3335_ = lean_ctor_get(v_toConstantVal_3334_, 0);
lean_inc(v_name_3335_);
v___x_3336_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3336_, 0, v_val_3327_);
v___x_3337_ = 1;
v___x_3338_ = lean_box(v___x_3337_);
v___x_3339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3336_);
lean_ctor_set(v___x_3339_, 1, v___x_3338_);
v___x_3340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3340_, 0, v_name_3335_);
lean_ctor_set(v___x_3340_, 1, v___x_3339_);
lean_inc(v___y_3332_);
lean_inc_ref(v___y_3331_);
v___x_3341_ = lean_apply_5(v___f_3328_, v___x_3340_, v_exportedInfo_x3f_3330_, v___y_3331_, v___y_3332_, lean_box(0));
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed(lean_object* v_val_3342_, lean_object* v___f_3343_, lean_object* v_____r_3344_, lean_object* v_exportedInfo_x3f_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
lean_object* v_res_3349_; 
v_res_3349_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(v_val_3342_, v___f_3343_, v_____r_3344_, v_exportedInfo_x3f_3345_, v___y_3346_, v___y_3347_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(lean_object* v_val_3350_, uint8_t v___x_3351_, lean_object* v___f_3352_, lean_object* v_____r_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_){
_start:
{
lean_object* v_toConstantVal_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v_toConstantVal_3357_ = lean_ctor_get(v_val_3350_, 0);
lean_inc_ref(v_toConstantVal_3357_);
v___x_3358_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3358_, 0, v_toConstantVal_3357_);
lean_ctor_set_uint8(v___x_3358_, sizeof(void*)*1, v___x_3351_);
v___x_3359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3358_);
v___x_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3359_);
v___x_3361_ = lean_box(0);
lean_inc(v___y_3355_);
lean_inc_ref(v___y_3354_);
v___x_3362_ = lean_apply_5(v___f_3352_, v___x_3361_, v___x_3360_, v___y_3354_, v___y_3355_, lean_box(0));
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed(lean_object* v_val_3363_, lean_object* v___x_3364_, lean_object* v___f_3365_, lean_object* v_____r_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
uint8_t v___x_53870__boxed_3370_; lean_object* v_res_3371_; 
v___x_53870__boxed_3370_ = lean_unbox(v___x_3364_);
v_res_3371_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(v_val_3363_, v___x_53870__boxed_3370_, v___f_3365_, v_____r_3366_, v___y_3367_, v___y_3368_);
lean_dec(v___y_3368_);
lean_dec_ref(v___y_3367_);
lean_dec_ref(v_val_3363_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(lean_object* v_val_3372_, lean_object* v___f_3373_, lean_object* v_____r_3374_, lean_object* v_exportedInfo_x3f_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
lean_object* v_toConstantVal_3379_; lean_object* v_name_3380_; lean_object* v___x_3381_; uint8_t v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v_toConstantVal_3379_ = lean_ctor_get(v_val_3372_, 0);
v_name_3380_ = lean_ctor_get(v_toConstantVal_3379_, 0);
lean_inc(v_name_3380_);
v___x_3381_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3381_, 0, v_val_3372_);
v___x_3382_ = 3;
v___x_3383_ = lean_box(v___x_3382_);
v___x_3384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3381_);
lean_ctor_set(v___x_3384_, 1, v___x_3383_);
v___x_3385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3385_, 0, v_name_3380_);
lean_ctor_set(v___x_3385_, 1, v___x_3384_);
lean_inc(v___y_3377_);
lean_inc_ref(v___y_3376_);
v___x_3386_ = lean_apply_5(v___f_3373_, v___x_3385_, v_exportedInfo_x3f_3375_, v___y_3376_, v___y_3377_, lean_box(0));
return v___x_3386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed(lean_object* v_val_3387_, lean_object* v___f_3388_, lean_object* v_____r_3389_, lean_object* v_exportedInfo_x3f_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(v_val_3387_, v___f_3388_, v_____r_3389_, v_exportedInfo_x3f_3390_, v___y_3391_, v___y_3392_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(lean_object* v_val_3395_, lean_object* v___f_3396_, lean_object* v_____r_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_){
_start:
{
lean_object* v_toConstantVal_3401_; uint8_t v_isUnsafe_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v_toConstantVal_3401_ = lean_ctor_get(v_val_3395_, 0);
v_isUnsafe_3402_ = lean_ctor_get_uint8(v_val_3395_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_3401_);
v___x_3403_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3403_, 0, v_toConstantVal_3401_);
lean_ctor_set_uint8(v___x_3403_, sizeof(void*)*1, v_isUnsafe_3402_);
v___x_3404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3403_);
v___x_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3404_);
v___x_3406_ = lean_box(0);
lean_inc(v___y_3399_);
lean_inc_ref(v___y_3398_);
v___x_3407_ = lean_apply_5(v___f_3396_, v___x_3406_, v___x_3405_, v___y_3398_, v___y_3399_, lean_box(0));
return v___x_3407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10___boxed(lean_object* v_val_3408_, lean_object* v___f_3409_, lean_object* v_____r_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_){
_start:
{
lean_object* v_res_3414_; 
v_res_3414_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_3408_, v___f_3409_, v_____r_3410_, v___y_3411_, v___y_3412_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec_ref(v_val_3408_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(lean_object* v_decl_3415_, uint8_t v___x_3416_, lean_object* v_cls_3417_, lean_object* v___x_3418_, lean_object* v___x_3419_, lean_object* v_____x_3420_, lean_object* v_exportedInfo_x3f_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
_start:
{
lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v_a_3428_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v_a_3441_; uint8_t v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v_snd_3525_; lean_object* v_fst_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3658_; 
v_snd_3525_ = lean_ctor_get(v_____x_3420_, 1);
v_fst_3526_ = lean_ctor_get(v_____x_3420_, 0);
v_isSharedCheck_3658_ = !lean_is_exclusive(v_____x_3420_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3528_ = v_____x_3420_;
v_isShared_3529_ = v_isSharedCheck_3658_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_snd_3525_);
lean_inc(v_fst_3526_);
lean_dec(v_____x_3420_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3658_;
goto v_resetjp_3527_;
}
v___jp_3425_:
{
lean_object* v___x_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3436_; 
v___x_3429_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3427_, v___y_3426_);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3436_ == 0)
{
lean_object* v_unused_3437_; 
v_unused_3437_ = lean_ctor_get(v___x_3429_, 0);
lean_dec(v_unused_3437_);
v___x_3431_ = v___x_3429_;
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
else
{
lean_dec(v___x_3429_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3434_; 
if (v_isShared_3432_ == 0)
{
lean_ctor_set_tag(v___x_3431_, 1);
lean_ctor_set(v___x_3431_, 0, v_a_3428_);
v___x_3434_ = v___x_3431_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_a_3428_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
}
v___jp_3438_:
{
lean_object* v___x_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3449_; 
v___x_3442_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3440_, v___y_3439_);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3449_ == 0)
{
lean_object* v_unused_3450_; 
v_unused_3450_ = lean_ctor_get(v___x_3442_, 0);
lean_dec(v_unused_3450_);
v___x_3444_ = v___x_3442_;
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
else
{
lean_dec(v___x_3442_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3447_; 
if (v_isShared_3445_ == 0)
{
lean_ctor_set(v___x_3444_, 0, v_a_3441_);
v___x_3447_ = v___x_3444_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_a_3441_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
v___jp_3451_:
{
lean_object* v___x_3464_; 
lean_inc_ref(v___y_3460_);
v___x_3464_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3454_, v___y_3460_, v___y_3462_, v___y_3463_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v___x_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3511_; 
lean_dec_ref_known(v___x_3464_, 1);
lean_dec(v___y_3456_);
lean_inc_ref(v___y_3459_);
v___x_3465_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3459_, v___y_3458_);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3511_ == 0)
{
lean_object* v_unused_3512_; 
v_unused_3512_ = lean_ctor_get(v___x_3465_, 0);
lean_dec(v_unused_3512_);
v___x_3467_ = v___x_3465_;
v_isShared_3468_ = v_isSharedCheck_3511_;
goto v_resetjp_3466_;
}
else
{
lean_dec(v___x_3465_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3511_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; uint8_t v___x_3471_; 
v___x_3469_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3457_);
v___x_3470_ = l_Lean_Elab_async;
v___x_3471_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_3469_, v___x_3470_);
lean_dec_ref(v___x_3469_);
if (v___x_3471_ == 0)
{
lean_object* v___x_3472_; lean_object* v_r_3473_; 
lean_del_object(v___x_3467_);
lean_dec_ref(v___y_3461_);
lean_dec_ref(v___y_3453_);
v___x_3472_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3460_, v___y_3458_);
lean_dec_ref(v___x_3472_);
v_r_3473_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3415_, v___y_3457_, v___y_3458_);
if (lean_obj_tag(v_r_3473_) == 0)
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3483_; 
v_a_3474_ = lean_ctor_get(v_r_3473_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v_r_3473_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3476_ = v_r_3473_;
v_isShared_3477_ = v_isSharedCheck_3483_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v_r_3473_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3483_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3479_; 
lean_inc(v_a_3474_);
if (v_isShared_3477_ == 0)
{
lean_ctor_set_tag(v___x_3476_, 1);
v___x_3479_ = v___x_3476_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_a_3474_);
v___x_3479_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
lean_object* v___x_3480_; 
v___x_3480_ = lean_apply_2(v___y_3455_, v___x_3479_, lean_box(0));
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_dec_ref_known(v___x_3480_, 1);
v___y_3439_ = v___y_3458_;
v___y_3440_ = v___y_3459_;
v_a_3441_ = v_a_3474_;
goto v___jp_3438_;
}
else
{
lean_object* v_a_3481_; 
lean_dec(v_a_3474_);
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
lean_inc(v_a_3481_);
lean_dec_ref_known(v___x_3480_, 1);
v___y_3426_ = v___y_3458_;
v___y_3427_ = v___y_3459_;
v_a_3428_ = v_a_3481_;
goto v___jp_3425_;
}
}
}
}
else
{
lean_object* v_a_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v_a_3484_ = lean_ctor_get(v_r_3473_, 0);
lean_inc(v_a_3484_);
lean_dec_ref_known(v_r_3473_, 1);
v___x_3485_ = lean_box(0);
v___x_3486_ = lean_apply_2(v___y_3455_, v___x_3485_, lean_box(0));
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_dec_ref_known(v___x_3486_, 1);
v___y_3426_ = v___y_3458_;
v___y_3427_ = v___y_3459_;
v_a_3428_ = v_a_3484_;
goto v___jp_3425_;
}
else
{
lean_object* v_a_3487_; 
lean_dec(v_a_3484_);
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_a_3487_);
lean_dec_ref_known(v___x_3486_, 1);
v___y_3426_ = v___y_3458_;
v___y_3427_ = v___y_3459_;
v_a_3428_ = v_a_3487_;
goto v___jp_3425_;
}
}
}
else
{
lean_object* v___x_3488_; lean_object* v___x_3490_; 
lean_dec_ref(v___y_3460_);
lean_dec_ref(v___y_3459_);
lean_dec_ref(v___y_3455_);
lean_dec(v_decl_3415_);
v___x_3488_ = l_IO_CancelToken_new();
if (v_isShared_3468_ == 0)
{
lean_ctor_set_tag(v___x_3467_, 1);
lean_ctor_set(v___x_3467_, 0, v___x_3488_);
v___x_3490_ = v___x_3467_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v___x_3488_);
v___x_3490_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3491_ = lean_unsigned_to_nat(0u);
v___x_3492_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_3493_ = l_Lean_Name_toString(v___x_3492_, v___x_3416_);
lean_inc_ref(v___x_3490_);
v___x_3494_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3461_, v___x_3490_, v___x_3493_, v___y_3457_, v___y_3458_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v_a_3495_; lean_object* v_checked_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; 
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
lean_inc(v_a_3495_);
lean_dec_ref_known(v___x_3494_, 1);
v_checked_3496_ = lean_ctor_get(v___y_3453_, 2);
lean_inc_ref(v_checked_3496_);
lean_dec_ref(v___y_3453_);
v___x_3497_ = lean_io_map_task(v_a_3495_, v_checked_3496_, v___x_3491_, v___y_3452_);
v___x_3498_ = lean_box(0);
v___x_3499_ = lean_box(2);
v___x_3500_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3498_);
lean_ctor_set(v___x_3500_, 1, v___x_3499_);
lean_ctor_set(v___x_3500_, 2, v___x_3490_);
lean_ctor_set(v___x_3500_, 3, v___x_3497_);
v___x_3501_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3500_, v___y_3458_);
return v___x_3501_;
}
else
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3509_; 
lean_dec_ref(v___x_3490_);
lean_dec_ref(v___y_3453_);
v_a_3502_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3504_ = v___x_3494_;
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3494_);
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
}
else
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3524_; 
lean_dec_ref(v___y_3461_);
lean_dec_ref(v___y_3460_);
lean_dec_ref(v___y_3459_);
lean_dec_ref(v___y_3455_);
lean_dec_ref(v___y_3453_);
lean_dec(v_decl_3415_);
v_a_3513_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3515_ = v___x_3464_;
v_isShared_3516_ = v_isSharedCheck_3524_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3464_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3524_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3522_; 
v___x_3517_ = lean_io_error_to_string(v_a_3513_);
v___x_3518_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3517_);
v___x_3519_ = l_Lean_MessageData_ofFormat(v___x_3518_);
v___x_3520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___y_3456_);
lean_ctor_set(v___x_3520_, 1, v___x_3519_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 0, v___x_3520_);
v___x_3522_ = v___x_3515_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v___x_3520_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
}
v_resetjp_3527_:
{
lean_object* v_fst_3530_; lean_object* v_snd_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3657_; 
v_fst_3530_ = lean_ctor_get(v_snd_3525_, 0);
v_snd_3531_ = lean_ctor_get(v_snd_3525_, 1);
v_isSharedCheck_3657_ = !lean_is_exclusive(v_snd_3525_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3533_ = v_snd_3525_;
v_isShared_3534_ = v_isSharedCheck_3657_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_snd_3531_);
lean_inc(v_fst_3530_);
lean_dec(v_snd_3525_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3657_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v_exportedInfo_x3f_3566_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3586_; lean_object* v___y_3587_; uint8_t v___y_3588_; uint8_t v___y_3589_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___x_3647_; lean_object* v_env_3648_; uint8_t v___x_3649_; 
v___x_3647_ = lean_st_ref_get(v___y_3423_);
v_env_3648_ = lean_ctor_get(v___x_3647_, 0);
lean_inc_ref(v_env_3648_);
lean_dec(v___x_3647_);
v___x_3649_ = l_Lean_Environment_containsOnBranch(v_env_3648_, v_fst_3526_);
lean_dec_ref(v_env_3648_);
if (v___x_3649_ == 0)
{
lean_del_object(v___x_3528_);
v___y_3621_ = v___y_3422_;
v___y_3622_ = v___y_3423_;
goto v___jp_3620_;
}
else
{
lean_object* v___x_3650_; lean_object* v_env_3651_; lean_object* v___x_3652_; lean_object* v___x_3654_; 
lean_del_object(v___x_3533_);
lean_dec(v_snd_3531_);
lean_dec(v_fst_3530_);
lean_dec(v_exportedInfo_x3f_3421_);
lean_dec(v___x_3419_);
lean_dec_ref(v___x_3418_);
lean_dec(v_cls_3417_);
lean_dec(v_decl_3415_);
v___x_3650_ = lean_st_ref_get(v___y_3423_);
v_env_3651_ = lean_ctor_get(v___x_3650_, 0);
lean_inc_ref(v_env_3651_);
lean_dec(v___x_3650_);
v___x_3652_ = lean_elab_environment_to_kernel_env(v_env_3651_);
if (v_isShared_3529_ == 0)
{
lean_ctor_set_tag(v___x_3528_, 1);
lean_ctor_set(v___x_3528_, 1, v_fst_3526_);
lean_ctor_set(v___x_3528_, 0, v___x_3652_);
v___x_3654_ = v___x_3528_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v___x_3652_);
lean_ctor_set(v_reuseFailAlloc_3656_, 1, v_fst_3526_);
v___x_3654_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
lean_object* v___x_3655_; 
v___x_3655_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3654_, v___y_3422_, v___y_3423_);
return v___x_3655_;
}
}
v___jp_3535_:
{
lean_object* v_ref_3541_; uint8_t v___x_3542_; uint8_t v___x_3543_; lean_object* v___x_3544_; 
v_ref_3541_ = lean_ctor_get(v___y_3536_, 2);
v___x_3542_ = 0;
v___x_3543_ = lean_unbox(v_snd_3531_);
lean_dec(v_snd_3531_);
lean_inc_ref(v___y_3539_);
v___x_3544_ = l_Lean_Environment_addConstAsync(v___y_3539_, v_fst_3526_, v___x_3543_, v___y_3540_, v___x_3542_, v___x_3416_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_object* v_a_3545_; lean_object* v_mainEnv_3546_; lean_object* v_asyncEnv_3547_; lean_object* v___f_3548_; lean_object* v___f_3549_; lean_object* v___x_3550_; 
lean_del_object(v___x_3533_);
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
lean_inc_n(v_a_3545_, 3);
lean_dec_ref_known(v___x_3544_, 1);
v_mainEnv_3546_ = lean_ctor_get(v_a_3545_, 0);
lean_inc_ref(v_mainEnv_3546_);
v_asyncEnv_3547_ = lean_ctor_get(v_a_3545_, 1);
lean_inc_ref_n(v_asyncEnv_3547_, 2);
lean_inc(v_ref_3541_);
lean_inc(v___y_3537_);
v___f_3548_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3548_, 0, v___y_3537_);
lean_closure_set(v___f_3548_, 1, v_a_3545_);
lean_closure_set(v___f_3548_, 2, v_ref_3541_);
lean_inc(v_decl_3415_);
v___f_3549_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3549_, 0, v_a_3545_);
lean_closure_set(v___f_3549_, 1, v_asyncEnv_3547_);
lean_closure_set(v___f_3549_, 2, v_decl_3415_);
v___x_3550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3550_, 0, v_fst_3530_);
if (lean_obj_tag(v___y_3538_) == 0)
{
lean_inc_ref(v___x_3550_);
lean_inc(v_ref_3541_);
v___y_3452_ = v___x_3542_;
v___y_3453_ = v___y_3539_;
v___y_3454_ = v_a_3545_;
v___y_3455_ = v___f_3548_;
v___y_3456_ = v_ref_3541_;
v___y_3457_ = v___y_3536_;
v___y_3458_ = v___y_3537_;
v___y_3459_ = v_mainEnv_3546_;
v___y_3460_ = v_asyncEnv_3547_;
v___y_3461_ = v___f_3549_;
v___y_3462_ = v___x_3550_;
v___y_3463_ = v___x_3550_;
goto v___jp_3451_;
}
else
{
lean_inc(v_ref_3541_);
v___y_3452_ = v___x_3542_;
v___y_3453_ = v___y_3539_;
v___y_3454_ = v_a_3545_;
v___y_3455_ = v___f_3548_;
v___y_3456_ = v_ref_3541_;
v___y_3457_ = v___y_3536_;
v___y_3458_ = v___y_3537_;
v___y_3459_ = v_mainEnv_3546_;
v___y_3460_ = v_asyncEnv_3547_;
v___y_3461_ = v___f_3549_;
v___y_3462_ = v___x_3550_;
v___y_3463_ = v___y_3538_;
goto v___jp_3451_;
}
}
else
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3564_; 
lean_dec_ref(v___y_3539_);
lean_dec(v___y_3538_);
lean_dec(v_fst_3530_);
lean_dec(v_decl_3415_);
v_a_3551_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3553_ = v___x_3544_;
v_isShared_3554_ = v_isSharedCheck_3564_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3544_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3564_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3559_; 
v___x_3555_ = lean_io_error_to_string(v_a_3551_);
v___x_3556_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3556_, 0, v___x_3555_);
v___x_3557_ = l_Lean_MessageData_ofFormat(v___x_3556_);
lean_inc(v_ref_3541_);
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 1, v___x_3557_);
lean_ctor_set(v___x_3533_, 0, v_ref_3541_);
v___x_3559_ = v___x_3533_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_ref_3541_);
lean_ctor_set(v_reuseFailAlloc_3563_, 1, v___x_3557_);
v___x_3559_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
lean_object* v___x_3561_; 
if (v_isShared_3554_ == 0)
{
lean_ctor_set(v___x_3553_, 0, v___x_3559_);
v___x_3561_ = v___x_3553_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v___x_3559_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
}
}
}
v___jp_3565_:
{
lean_object* v___x_3569_; 
v___x_3569_ = lean_st_ref_get(v___y_3568_);
if (lean_obj_tag(v_exportedInfo_x3f_3566_) == 0)
{
lean_object* v_env_3570_; lean_object* v___x_3571_; 
v_env_3570_ = lean_ctor_get(v___x_3569_, 0);
lean_inc_ref(v_env_3570_);
lean_dec(v___x_3569_);
v___x_3571_ = lean_box(0);
v___y_3536_ = v___y_3567_;
v___y_3537_ = v___y_3568_;
v___y_3538_ = v_exportedInfo_x3f_3566_;
v___y_3539_ = v_env_3570_;
v___y_3540_ = v___x_3571_;
goto v___jp_3535_;
}
else
{
lean_object* v_env_3572_; lean_object* v_val_3573_; uint8_t v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v_env_3572_ = lean_ctor_get(v___x_3569_, 0);
lean_inc_ref(v_env_3572_);
lean_dec(v___x_3569_);
v_val_3573_ = lean_ctor_get(v_exportedInfo_x3f_3566_, 0);
v___x_3574_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3573_);
v___x_3575_ = lean_box(v___x_3574_);
v___x_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3575_);
v___y_3536_ = v___y_3567_;
v___y_3537_ = v___y_3568_;
v___y_3538_ = v_exportedInfo_x3f_3566_;
v___y_3539_ = v_env_3572_;
v___y_3540_ = v___x_3576_;
goto v___jp_3535_;
}
}
v___jp_3577_:
{
lean_object* v___x_3580_; 
lean_inc(v_fst_3530_);
v___x_3580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3580_, 0, v_fst_3530_);
v_exportedInfo_x3f_3566_ = v___x_3580_;
v___y_3567_ = v___y_3578_;
v___y_3568_ = v___y_3579_;
goto v___jp_3565_;
}
v___jp_3581_:
{
lean_object* v___x_3584_; 
lean_inc(v_fst_3530_);
v___x_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3584_, 0, v_fst_3530_);
v_exportedInfo_x3f_3566_ = v___x_3584_;
v___y_3567_ = v___y_3582_;
v___y_3568_ = v___y_3583_;
goto v___jp_3565_;
}
v___jp_3585_:
{
if (v___y_3589_ == 0)
{
lean_object* v_toCold_3590_; lean_object* v_options_3591_; uint8_t v_hasTrace_3592_; 
lean_dec(v_exportedInfo_x3f_3421_);
lean_dec_ref(v___x_3418_);
v_toCold_3590_ = lean_ctor_get(v___y_3587_, 0);
v_options_3591_ = lean_ctor_get(v_toCold_3590_, 2);
v_hasTrace_3592_ = lean_ctor_get_uint8(v_options_3591_, sizeof(void*)*1);
if (v_hasTrace_3592_ == 0)
{
lean_dec(v_cls_3417_);
v___y_3582_ = v___y_3587_;
v___y_3583_ = v___y_3586_;
goto v___jp_3581_;
}
else
{
lean_object* v_inheritedTraceOptions_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; uint8_t v___x_3596_; 
v_inheritedTraceOptions_3593_ = lean_ctor_get(v_toCold_3590_, 11);
v___x_3594_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3417_);
v___x_3595_ = l_Lean_Name_append(v___x_3594_, v_cls_3417_);
v___x_3596_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3593_, v_options_3591_, v___x_3595_);
lean_dec(v___x_3595_);
if (v___x_3596_ == 0)
{
lean_dec(v_cls_3417_);
v___y_3582_ = v___y_3587_;
v___y_3583_ = v___y_3586_;
goto v___jp_3581_;
}
else
{
lean_object* v___x_3597_; lean_object* v___x_3598_; 
v___x_3597_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_3598_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3417_, v___x_3597_, v___y_3587_, v___y_3586_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_dec_ref_known(v___x_3598_, 1);
v___y_3582_ = v___y_3587_;
v___y_3583_ = v___y_3586_;
goto v___jp_3581_;
}
else
{
lean_del_object(v___x_3533_);
lean_dec(v_snd_3531_);
lean_dec(v_fst_3530_);
lean_dec(v_fst_3526_);
lean_dec(v_decl_3415_);
return v___x_3598_;
}
}
}
}
else
{
lean_object* v___x_3599_; lean_object* v_env_3600_; lean_object* v_nextMacroScope_3601_; lean_object* v_ngen_3602_; lean_object* v_auxDeclNGen_3603_; lean_object* v_traceState_3604_; lean_object* v_recordedDeps_3605_; lean_object* v_messages_3606_; lean_object* v_infoState_3607_; lean_object* v_snapshotTasks_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3618_; 
lean_dec(v_cls_3417_);
v___x_3599_ = lean_st_ref_take(v___y_3586_);
v_env_3600_ = lean_ctor_get(v___x_3599_, 0);
v_nextMacroScope_3601_ = lean_ctor_get(v___x_3599_, 1);
v_ngen_3602_ = lean_ctor_get(v___x_3599_, 2);
v_auxDeclNGen_3603_ = lean_ctor_get(v___x_3599_, 3);
v_traceState_3604_ = lean_ctor_get(v___x_3599_, 4);
v_recordedDeps_3605_ = lean_ctor_get(v___x_3599_, 6);
v_messages_3606_ = lean_ctor_get(v___x_3599_, 7);
v_infoState_3607_ = lean_ctor_get(v___x_3599_, 8);
v_snapshotTasks_3608_ = lean_ctor_get(v___x_3599_, 9);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3618_ == 0)
{
lean_object* v_unused_3619_; 
v_unused_3619_ = lean_ctor_get(v___x_3599_, 5);
lean_dec(v_unused_3619_);
v___x_3610_ = v___x_3599_;
v_isShared_3611_ = v_isSharedCheck_3618_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_snapshotTasks_3608_);
lean_inc(v_infoState_3607_);
lean_inc(v_messages_3606_);
lean_inc(v_recordedDeps_3605_);
lean_inc(v_traceState_3604_);
lean_inc(v_auxDeclNGen_3603_);
lean_inc(v_ngen_3602_);
lean_inc(v_nextMacroScope_3601_);
lean_inc(v_env_3600_);
lean_dec(v___x_3599_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3618_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3615_; 
v___x_3612_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3531_);
lean_inc(v_fst_3526_);
v___x_3613_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3612_, v_env_3600_, v_fst_3526_, v_snd_3531_, v___y_3588_);
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 5, v___x_3418_);
lean_ctor_set(v___x_3610_, 0, v___x_3613_);
v___x_3615_ = v___x_3610_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v___x_3613_);
lean_ctor_set(v_reuseFailAlloc_3617_, 1, v_nextMacroScope_3601_);
lean_ctor_set(v_reuseFailAlloc_3617_, 2, v_ngen_3602_);
lean_ctor_set(v_reuseFailAlloc_3617_, 3, v_auxDeclNGen_3603_);
lean_ctor_set(v_reuseFailAlloc_3617_, 4, v_traceState_3604_);
lean_ctor_set(v_reuseFailAlloc_3617_, 5, v___x_3418_);
lean_ctor_set(v_reuseFailAlloc_3617_, 6, v_recordedDeps_3605_);
lean_ctor_set(v_reuseFailAlloc_3617_, 7, v_messages_3606_);
lean_ctor_set(v_reuseFailAlloc_3617_, 8, v_infoState_3607_);
lean_ctor_set(v_reuseFailAlloc_3617_, 9, v_snapshotTasks_3608_);
v___x_3615_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
lean_object* v___x_3616_; 
v___x_3616_ = lean_st_ref_put(v___y_3586_, v___x_3615_);
v_exportedInfo_x3f_3566_ = v_exportedInfo_x3f_3421_;
v___y_3567_ = v___y_3587_;
v___y_3568_ = v___y_3586_;
goto v___jp_3565_;
}
}
}
}
v___jp_3620_:
{
lean_object* v___x_3623_; uint8_t v___x_3624_; 
lean_inc(v_decl_3415_);
v___x_3623_ = l_Lean_Declaration_getTopLevelNames(v_decl_3415_);
v___x_3624_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3623_);
lean_dec(v___x_3623_);
if (v___x_3624_ == 0)
{
lean_dec(v___x_3419_);
if (lean_obj_tag(v_exportedInfo_x3f_3421_) == 0)
{
v___y_3586_ = v___y_3622_;
v___y_3587_ = v___y_3621_;
v___y_3588_ = v___x_3624_;
v___y_3589_ = v___x_3624_;
goto v___jp_3585_;
}
else
{
v___y_3586_ = v___y_3622_;
v___y_3587_ = v___y_3621_;
v___y_3588_ = v___x_3624_;
v___y_3589_ = v___x_3416_;
goto v___jp_3585_;
}
}
else
{
lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v_a_3627_; uint8_t v___x_3628_; 
lean_dec(v_exportedInfo_x3f_3421_);
lean_dec_ref(v___x_3418_);
v___x_3625_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3626_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3625_, v___y_3621_);
v_a_3627_ = lean_ctor_get(v___x_3626_, 0);
lean_inc(v_a_3627_);
lean_dec_ref(v___x_3626_);
v___x_3628_ = lean_unbox(v_a_3627_);
lean_dec(v_a_3627_);
if (v___x_3628_ == 0)
{
lean_object* v_toCold_3629_; lean_object* v_options_3630_; uint8_t v_hasTrace_3631_; 
v_toCold_3629_ = lean_ctor_get(v___y_3621_, 0);
v_options_3630_ = lean_ctor_get(v_toCold_3629_, 2);
v_hasTrace_3631_ = lean_ctor_get_uint8(v_options_3630_, sizeof(void*)*1);
if (v_hasTrace_3631_ == 0)
{
lean_dec(v_cls_3417_);
v_exportedInfo_x3f_3566_ = v___x_3419_;
v___y_3567_ = v___y_3621_;
v___y_3568_ = v___y_3622_;
goto v___jp_3565_;
}
else
{
lean_object* v_inheritedTraceOptions_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; uint8_t v___x_3635_; 
v_inheritedTraceOptions_3632_ = lean_ctor_get(v_toCold_3629_, 11);
v___x_3633_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3417_);
v___x_3634_ = l_Lean_Name_append(v___x_3633_, v_cls_3417_);
v___x_3635_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3632_, v_options_3630_, v___x_3634_);
lean_dec(v___x_3634_);
if (v___x_3635_ == 0)
{
lean_dec(v_cls_3417_);
v_exportedInfo_x3f_3566_ = v___x_3419_;
v___y_3567_ = v___y_3621_;
v___y_3568_ = v___y_3622_;
goto v___jp_3565_;
}
else
{
lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3636_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_3637_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3417_, v___x_3636_, v___y_3621_, v___y_3622_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_dec_ref_known(v___x_3637_, 1);
v_exportedInfo_x3f_3566_ = v___x_3419_;
v___y_3567_ = v___y_3621_;
v___y_3568_ = v___y_3622_;
goto v___jp_3565_;
}
else
{
lean_del_object(v___x_3533_);
lean_dec(v_snd_3531_);
lean_dec(v_fst_3530_);
lean_dec(v_fst_3526_);
lean_dec(v___x_3419_);
lean_dec(v_decl_3415_);
return v___x_3637_;
}
}
}
}
else
{
lean_object* v_toCold_3638_; lean_object* v_options_3639_; uint8_t v_hasTrace_3640_; 
lean_dec(v___x_3419_);
v_toCold_3638_ = lean_ctor_get(v___y_3621_, 0);
v_options_3639_ = lean_ctor_get(v_toCold_3638_, 2);
v_hasTrace_3640_ = lean_ctor_get_uint8(v_options_3639_, sizeof(void*)*1);
if (v_hasTrace_3640_ == 0)
{
lean_dec(v_cls_3417_);
v___y_3578_ = v___y_3621_;
v___y_3579_ = v___y_3622_;
goto v___jp_3577_;
}
else
{
lean_object* v_inheritedTraceOptions_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; uint8_t v___x_3644_; 
v_inheritedTraceOptions_3641_ = lean_ctor_get(v_toCold_3638_, 11);
v___x_3642_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3417_);
v___x_3643_ = l_Lean_Name_append(v___x_3642_, v_cls_3417_);
v___x_3644_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3641_, v_options_3639_, v___x_3643_);
lean_dec(v___x_3643_);
if (v___x_3644_ == 0)
{
lean_dec(v_cls_3417_);
v___y_3578_ = v___y_3621_;
v___y_3579_ = v___y_3622_;
goto v___jp_3577_;
}
else
{
lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3645_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_3646_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3417_, v___x_3645_, v___y_3621_, v___y_3622_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_dec_ref_known(v___x_3646_, 1);
v___y_3578_ = v___y_3621_;
v___y_3579_ = v___y_3622_;
goto v___jp_3577_;
}
else
{
lean_del_object(v___x_3533_);
lean_dec(v_snd_3531_);
lean_dec(v_fst_3530_);
lean_dec(v_fst_3526_);
lean_dec(v_decl_3415_);
return v___x_3646_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14___boxed(lean_object* v_decl_3659_, lean_object* v___x_3660_, lean_object* v_cls_3661_, lean_object* v___x_3662_, lean_object* v___x_3663_, lean_object* v_____x_3664_, lean_object* v_exportedInfo_x3f_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_){
_start:
{
uint8_t v___x_54001__boxed_3669_; lean_object* v_res_3670_; 
v___x_54001__boxed_3669_ = lean_unbox(v___x_3660_);
v_res_3670_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(v_decl_3659_, v___x_54001__boxed_3669_, v_cls_3661_, v___x_3662_, v___x_3663_, v_____x_3664_, v_exportedInfo_x3f_3665_, v___y_3666_, v___y_3667_);
lean_dec(v___y_3667_);
lean_dec_ref(v___y_3666_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(lean_object* v___f_3671_, uint8_t v_forceExpose_3672_, uint8_t v___x_3673_, lean_object* v___x_3674_, lean_object* v_cls_3675_, lean_object* v_defn_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_){
_start:
{
lean_object* v_exportedInfo_x3f_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; uint8_t v___y_3696_; lean_object* v___x_3700_; lean_object* v_env_3701_; lean_object* v___x_3702_; 
v___x_3700_ = lean_st_ref_get(v___y_3678_);
v_env_3701_ = lean_ctor_get(v___x_3700_, 0);
lean_inc_ref(v_env_3701_);
lean_dec(v___x_3700_);
v___x_3702_ = lean_st_ref_get(v___y_3678_);
if (v_forceExpose_3672_ == 0)
{
if (v___x_3673_ == 0)
{
lean_dec(v___x_3702_);
lean_dec_ref(v_env_3701_);
lean_dec(v_cls_3675_);
v_exportedInfo_x3f_3681_ = v___x_3674_;
v___y_3682_ = v___y_3677_;
v___y_3683_ = v___y_3678_;
goto v___jp_3680_;
}
else
{
lean_object* v_env_3703_; lean_object* v___x_3704_; uint8_t v_isModule_3705_; 
v_env_3703_ = lean_ctor_get(v___x_3702_, 0);
lean_inc_ref(v_env_3703_);
lean_dec(v___x_3702_);
v___x_3704_ = l_Lean_Environment_header(v_env_3701_);
lean_dec_ref(v_env_3701_);
v_isModule_3705_ = lean_ctor_get_uint8(v___x_3704_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3704_);
if (v_isModule_3705_ == 0)
{
lean_dec_ref(v_env_3703_);
lean_dec(v_cls_3675_);
v_exportedInfo_x3f_3681_ = v___x_3674_;
v___y_3682_ = v___y_3677_;
v___y_3683_ = v___y_3678_;
goto v___jp_3680_;
}
else
{
uint8_t v_isExporting_3706_; lean_object* v___y_3708_; lean_object* v___y_3709_; 
v_isExporting_3706_ = lean_ctor_get_uint8(v_env_3703_, sizeof(void*)*13);
lean_dec_ref(v_env_3703_);
if (v_isExporting_3706_ == 0)
{
lean_object* v_toCold_3714_; lean_object* v_options_3715_; uint8_t v_hasTrace_3716_; 
lean_dec(v___x_3674_);
v_toCold_3714_ = lean_ctor_get(v___y_3677_, 0);
v_options_3715_ = lean_ctor_get(v_toCold_3714_, 2);
v_hasTrace_3716_ = lean_ctor_get_uint8(v_options_3715_, sizeof(void*)*1);
if (v_hasTrace_3716_ == 0)
{
lean_dec(v_cls_3675_);
v___y_3708_ = v___y_3677_;
v___y_3709_ = v___y_3678_;
goto v___jp_3707_;
}
else
{
lean_object* v_inheritedTraceOptions_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; uint8_t v___x_3720_; 
v_inheritedTraceOptions_3717_ = lean_ctor_get(v_toCold_3714_, 11);
v___x_3718_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3675_);
v___x_3719_ = l_Lean_Name_append(v___x_3718_, v_cls_3675_);
v___x_3720_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3717_, v_options_3715_, v___x_3719_);
lean_dec(v___x_3719_);
if (v___x_3720_ == 0)
{
lean_dec(v_cls_3675_);
v___y_3708_ = v___y_3677_;
v___y_3709_ = v___y_3678_;
goto v___jp_3707_;
}
else
{
lean_object* v_toConstantVal_3721_; lean_object* v_name_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; 
v_toConstantVal_3721_ = lean_ctor_get(v_defn_3676_, 0);
v_name_3722_ = lean_ctor_get(v_toConstantVal_3721_, 0);
v___x_3723_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_3722_);
v___x_3724_ = l_Lean_MessageData_ofName(v_name_3722_);
v___x_3725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3723_);
lean_ctor_set(v___x_3725_, 1, v___x_3724_);
v___x_3726_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_3727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3725_);
lean_ctor_set(v___x_3727_, 1, v___x_3726_);
v___x_3728_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3675_, v___x_3727_, v___y_3677_, v___y_3678_);
if (lean_obj_tag(v___x_3728_) == 0)
{
lean_dec_ref_known(v___x_3728_, 1);
v___y_3708_ = v___y_3677_;
v___y_3709_ = v___y_3678_;
goto v___jp_3707_;
}
else
{
lean_dec_ref(v_defn_3676_);
lean_dec_ref(v___f_3671_);
return v___x_3728_;
}
}
}
}
else
{
lean_dec(v_cls_3675_);
v_exportedInfo_x3f_3681_ = v___x_3674_;
v___y_3682_ = v___y_3677_;
v___y_3683_ = v___y_3678_;
goto v___jp_3680_;
}
v___jp_3707_:
{
lean_object* v_toConstantVal_3710_; uint8_t v_safety_3711_; uint8_t v___x_3712_; uint8_t v___x_3713_; 
v_toConstantVal_3710_ = lean_ctor_get(v_defn_3676_, 0);
v_safety_3711_ = lean_ctor_get_uint8(v_defn_3676_, sizeof(void*)*4);
v___x_3712_ = 1;
v___x_3713_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3711_, v___x_3712_);
if (v___x_3713_ == 0)
{
lean_inc_ref(v_toConstantVal_3710_);
v___y_3693_ = v___y_3709_;
v___y_3694_ = v___y_3708_;
v___y_3695_ = v_toConstantVal_3710_;
v___y_3696_ = v_isModule_3705_;
goto v___jp_3692_;
}
else
{
lean_inc_ref(v_toConstantVal_3710_);
v___y_3693_ = v___y_3709_;
v___y_3694_ = v___y_3708_;
v___y_3695_ = v_toConstantVal_3710_;
v___y_3696_ = v_isExporting_3706_;
goto v___jp_3692_;
}
}
}
}
}
else
{
lean_dec(v___x_3702_);
lean_dec_ref(v_env_3701_);
lean_dec(v_cls_3675_);
v_exportedInfo_x3f_3681_ = v___x_3674_;
v___y_3682_ = v___y_3677_;
v___y_3683_ = v___y_3678_;
goto v___jp_3680_;
}
v___jp_3680_:
{
lean_object* v_toConstantVal_3684_; lean_object* v_name_3685_; lean_object* v___x_3686_; uint8_t v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v_toConstantVal_3684_ = lean_ctor_get(v_defn_3676_, 0);
v_name_3685_ = lean_ctor_get(v_toConstantVal_3684_, 0);
lean_inc(v_name_3685_);
v___x_3686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3686_, 0, v_defn_3676_);
v___x_3687_ = 0;
v___x_3688_ = lean_box(v___x_3687_);
v___x_3689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3686_);
lean_ctor_set(v___x_3689_, 1, v___x_3688_);
v___x_3690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3690_, 0, v_name_3685_);
lean_ctor_set(v___x_3690_, 1, v___x_3689_);
lean_inc(v___y_3683_);
lean_inc_ref(v___y_3682_);
v___x_3691_ = lean_apply_5(v___f_3671_, v___x_3690_, v_exportedInfo_x3f_3681_, v___y_3682_, v___y_3683_, lean_box(0));
return v___x_3691_;
}
v___jp_3692_:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3697_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3697_, 0, v___y_3695_);
lean_ctor_set_uint8(v___x_3697_, sizeof(void*)*1, v___y_3696_);
v___x_3698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3697_);
v___x_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3698_);
v_exportedInfo_x3f_3681_ = v___x_3699_;
v___y_3682_ = v___y_3694_;
v___y_3683_ = v___y_3693_;
goto v___jp_3680_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11___boxed(lean_object* v___f_3729_, lean_object* v_forceExpose_3730_, lean_object* v___x_3731_, lean_object* v___x_3732_, lean_object* v_cls_3733_, lean_object* v_defn_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
uint8_t v_forceExpose_boxed_3738_; uint8_t v___x_54479__boxed_3739_; lean_object* v_res_3740_; 
v_forceExpose_boxed_3738_ = lean_unbox(v_forceExpose_3730_);
v___x_54479__boxed_3739_ = lean_unbox(v___x_3731_);
v_res_3740_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(v___f_3729_, v_forceExpose_boxed_3738_, v___x_54479__boxed_3739_, v___x_3732_, v_cls_3733_, v_defn_3734_, v___y_3735_, v___y_3736_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(lean_object* v_val_3741_, lean_object* v___f_3742_, lean_object* v_____r_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
lean_object* v_toConstantVal_3747_; uint8_t v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; 
v_toConstantVal_3747_ = lean_ctor_get(v_val_3741_, 0);
v___x_3748_ = 0;
lean_inc_ref(v_toConstantVal_3747_);
v___x_3749_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3749_, 0, v_toConstantVal_3747_);
lean_ctor_set_uint8(v___x_3749_, sizeof(void*)*1, v___x_3748_);
v___x_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3749_);
v___x_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3750_);
v___x_3752_ = lean_box(0);
lean_inc(v___y_3745_);
lean_inc_ref(v___y_3744_);
v___x_3753_ = lean_apply_5(v___f_3742_, v___x_3752_, v___x_3751_, v___y_3744_, v___y_3745_, lean_box(0));
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed(lean_object* v_val_3754_, lean_object* v___f_3755_, lean_object* v_____r_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
lean_object* v_res_3760_; 
v_res_3760_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_val_3754_, v___f_3755_, v_____r_3756_, v___y_3757_, v___y_3758_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec_ref(v_val_3754_);
return v_res_3760_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(lean_object* v_x_3761_, lean_object* v_x_3762_){
_start:
{
if (lean_obj_tag(v_x_3762_) == 0)
{
return v_x_3761_;
}
else
{
lean_object* v_head_3763_; lean_object* v_tail_3764_; lean_object* v___x_3765_; 
v_head_3763_ = lean_ctor_get(v_x_3762_, 0);
lean_inc(v_head_3763_);
v_tail_3764_ = lean_ctor_get(v_x_3762_, 1);
lean_inc(v_tail_3764_);
lean_dec_ref_known(v_x_3762_, 2);
v___x_3765_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(v_x_3761_, v_head_3763_);
v_x_3761_ = v___x_3765_;
v_x_3762_ = v_tail_3764_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0(void){
_start:
{
lean_object* v_cls_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; 
v_cls_3767_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_3768_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
v___x_3769_ = l_Lean_Name_append(v___x_3768_, v_cls_3767_);
return v___x_3769_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2(void){
_start:
{
lean_object* v___x_3771_; lean_object* v___x_3772_; 
v___x_3771_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1));
v___x_3772_ = l_Lean_stringToMessageData(v___x_3771_);
return v___x_3772_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4(void){
_start:
{
lean_object* v___x_3774_; lean_object* v___x_3775_; 
v___x_3774_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3));
v___x_3775_ = l_Lean_stringToMessageData(v___x_3774_);
return v___x_3775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore(lean_object* v_decl_3776_, uint8_t v_forceExpose_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_){
_start:
{
lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v_a_3784_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v_a_3797_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v_a_3810_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v_a_3823_; lean_object* v_toCold_3833_; lean_object* v_options_3834_; lean_object* v_inheritedTraceOptions_3835_; uint8_t v_hasTrace_3836_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; uint8_t v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; uint8_t v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; uint8_t v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v_exportedInfo_x3f_3945_; lean_object* v___y_3946_; lean_object* v___y_3947_; uint8_t v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; uint8_t v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v_cls_3970_; lean_object* v___y_3972_; lean_object* v_options_3973_; lean_object* v_inheritedTraceOptions_3974_; lean_object* v___y_3975_; 
v_toCold_3833_ = lean_ctor_get(v_a_3778_, 0);
v_options_3834_ = lean_ctor_get(v_toCold_3833_, 2);
v_inheritedTraceOptions_3835_ = lean_ctor_get(v_toCold_3833_, 11);
v_hasTrace_3836_ = lean_ctor_get_uint8(v_options_3834_, sizeof(void*)*1);
v_cls_3970_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
if (v_hasTrace_3836_ == 0)
{
lean_object* v___x_3982_; lean_object* v_env_3983_; lean_object* v_nextMacroScope_3984_; lean_object* v_ngen_3985_; lean_object* v_auxDeclNGen_3986_; lean_object* v_traceState_3987_; lean_object* v_recordedDeps_3988_; lean_object* v_messages_3989_; lean_object* v_infoState_3990_; lean_object* v_snapshotTasks_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_4195_; 
v___x_3982_ = lean_st_ref_take(v_a_3779_);
v_env_3983_ = lean_ctor_get(v___x_3982_, 0);
v_nextMacroScope_3984_ = lean_ctor_get(v___x_3982_, 1);
v_ngen_3985_ = lean_ctor_get(v___x_3982_, 2);
v_auxDeclNGen_3986_ = lean_ctor_get(v___x_3982_, 3);
v_traceState_3987_ = lean_ctor_get(v___x_3982_, 4);
v_recordedDeps_3988_ = lean_ctor_get(v___x_3982_, 6);
v_messages_3989_ = lean_ctor_get(v___x_3982_, 7);
v_infoState_3990_ = lean_ctor_get(v___x_3982_, 8);
v_snapshotTasks_3991_ = lean_ctor_get(v___x_3982_, 9);
v_isSharedCheck_4195_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_4195_ == 0)
{
lean_object* v_unused_4196_; 
v_unused_4196_ = lean_ctor_get(v___x_3982_, 5);
lean_dec(v_unused_4196_);
v___x_3993_ = v___x_3982_;
v_isShared_3994_ = v_isSharedCheck_4195_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_snapshotTasks_3991_);
lean_inc(v_infoState_3990_);
lean_inc(v_messages_3989_);
lean_inc(v_recordedDeps_3988_);
lean_inc(v_traceState_3987_);
lean_inc(v_auxDeclNGen_3986_);
lean_inc(v_ngen_3985_);
lean_inc(v_nextMacroScope_3984_);
lean_inc(v_env_3983_);
lean_dec(v___x_3982_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_4195_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; uint8_t v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; uint8_t v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___x_4029_; 
lean_inc(v_decl_3776_);
v___x_3995_ = l_Lean_Declaration_getNames(v_decl_3776_);
v___x_3996_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_3983_, v___x_3995_);
v___x_3997_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_3994_ == 0)
{
lean_ctor_set(v___x_3993_, 5, v___x_3997_);
lean_ctor_set(v___x_3993_, 0, v___x_3996_);
v___x_4029_ = v___x_3993_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v___x_3996_);
lean_ctor_set(v_reuseFailAlloc_4194_, 1, v_nextMacroScope_3984_);
lean_ctor_set(v_reuseFailAlloc_4194_, 2, v_ngen_3985_);
lean_ctor_set(v_reuseFailAlloc_4194_, 3, v_auxDeclNGen_3986_);
lean_ctor_set(v_reuseFailAlloc_4194_, 4, v_traceState_3987_);
lean_ctor_set(v_reuseFailAlloc_4194_, 5, v___x_3997_);
lean_ctor_set(v_reuseFailAlloc_4194_, 6, v_recordedDeps_3988_);
lean_ctor_set(v_reuseFailAlloc_4194_, 7, v_messages_3989_);
lean_ctor_set(v_reuseFailAlloc_4194_, 8, v_infoState_3990_);
lean_ctor_set(v_reuseFailAlloc_4194_, 9, v_snapshotTasks_3991_);
v___x_4029_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4028_;
}
v___jp_3998_:
{
lean_object* v___x_4006_; lean_object* v_env_4007_; lean_object* v_nextMacroScope_4008_; lean_object* v_ngen_4009_; lean_object* v_auxDeclNGen_4010_; lean_object* v_traceState_4011_; lean_object* v_recordedDeps_4012_; lean_object* v_messages_4013_; lean_object* v_infoState_4014_; lean_object* v_snapshotTasks_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4026_; 
v___x_4006_ = lean_st_ref_take(v___y_4000_);
v_env_4007_ = lean_ctor_get(v___x_4006_, 0);
v_nextMacroScope_4008_ = lean_ctor_get(v___x_4006_, 1);
v_ngen_4009_ = lean_ctor_get(v___x_4006_, 2);
v_auxDeclNGen_4010_ = lean_ctor_get(v___x_4006_, 3);
v_traceState_4011_ = lean_ctor_get(v___x_4006_, 4);
v_recordedDeps_4012_ = lean_ctor_get(v___x_4006_, 6);
v_messages_4013_ = lean_ctor_get(v___x_4006_, 7);
v_infoState_4014_ = lean_ctor_get(v___x_4006_, 8);
v_snapshotTasks_4015_ = lean_ctor_get(v___x_4006_, 9);
v_isSharedCheck_4026_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4026_ == 0)
{
lean_object* v_unused_4027_; 
v_unused_4027_ = lean_ctor_get(v___x_4006_, 5);
lean_dec(v_unused_4027_);
v___x_4017_ = v___x_4006_;
v_isShared_4018_ = v_isSharedCheck_4026_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_snapshotTasks_4015_);
lean_inc(v_infoState_4014_);
lean_inc(v_messages_4013_);
lean_inc(v_recordedDeps_4012_);
lean_inc(v_traceState_4011_);
lean_inc(v_auxDeclNGen_4010_);
lean_inc(v_ngen_4009_);
lean_inc(v_nextMacroScope_4008_);
lean_inc(v_env_4007_);
lean_dec(v___x_4006_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4026_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4023_; 
v___x_4019_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4020_ = lean_box(v___y_3999_);
lean_inc(v___y_4004_);
v___x_4021_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4019_, v_env_4007_, v___y_4004_, v___x_4020_, v___y_4002_);
if (v_isShared_4018_ == 0)
{
lean_ctor_set(v___x_4017_, 5, v___x_3997_);
lean_ctor_set(v___x_4017_, 0, v___x_4021_);
v___x_4023_ = v___x_4017_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v___x_4021_);
lean_ctor_set(v_reuseFailAlloc_4025_, 1, v_nextMacroScope_4008_);
lean_ctor_set(v_reuseFailAlloc_4025_, 2, v_ngen_4009_);
lean_ctor_set(v_reuseFailAlloc_4025_, 3, v_auxDeclNGen_4010_);
lean_ctor_set(v_reuseFailAlloc_4025_, 4, v_traceState_4011_);
lean_ctor_set(v_reuseFailAlloc_4025_, 5, v___x_3997_);
lean_ctor_set(v_reuseFailAlloc_4025_, 6, v_recordedDeps_4012_);
lean_ctor_set(v_reuseFailAlloc_4025_, 7, v_messages_4013_);
lean_ctor_set(v_reuseFailAlloc_4025_, 8, v_infoState_4014_);
lean_ctor_set(v_reuseFailAlloc_4025_, 9, v_snapshotTasks_4015_);
v___x_4023_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
lean_object* v___x_4024_; 
v___x_4024_ = lean_st_ref_put(v___y_4000_, v___x_4023_);
v___y_3942_ = v___y_3999_;
v___y_3943_ = v___y_4001_;
v___y_3944_ = v___y_4004_;
v_exportedInfo_x3f_3945_ = v___y_4005_;
v___y_3946_ = v___y_4003_;
v___y_3947_ = v___y_4000_;
goto v___jp_3941_;
}
}
}
v_reusejp_4028_:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; uint8_t v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v_fst_4070_; lean_object* v_fst_4071_; uint8_t v_snd_4072_; lean_object* v_exportedInfo_x3f_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4085_; lean_object* v_exportedInfo_x3f_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; uint8_t v___y_4098_; lean_object* v___y_4103_; lean_object* v_toConstantVal_4104_; uint8_t v_safety_4105_; uint8_t v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4112_; uint8_t v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v_defn_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; 
v___x_4030_ = lean_st_ref_put(v_a_3779_, v___x_4029_);
v___x_4031_ = lean_box(0);
switch(lean_obj_tag(v_decl_3776_))
{
case 2:
{
lean_object* v_val_4144_; lean_object* v_exportedInfo_x3f_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v___x_4153_; 
v_val_4144_ = lean_ctor_get(v_decl_3776_, 0);
v___x_4153_ = lean_st_ref_get(v_a_3779_);
if (v_forceExpose_3777_ == 0)
{
lean_object* v_env_4154_; lean_object* v___x_4155_; uint8_t v_isModule_4156_; 
v_env_4154_ = lean_ctor_get(v___x_4153_, 0);
lean_inc_ref(v_env_4154_);
lean_dec(v___x_4153_);
v___x_4155_ = l_Lean_Environment_header(v_env_4154_);
lean_dec_ref(v_env_4154_);
v_isModule_4156_ = lean_ctor_get_uint8(v___x_4155_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4155_);
if (v_isModule_4156_ == 0)
{
v_exportedInfo_x3f_4146_ = v___x_4031_;
v___y_4147_ = v_a_3778_;
v___y_4148_ = v_a_3779_;
goto v___jp_4145_;
}
else
{
lean_object* v_toConstantVal_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
v_toConstantVal_4157_ = lean_ctor_get(v_val_4144_, 0);
lean_inc_ref(v_toConstantVal_4157_);
v___x_4158_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4158_, 0, v_toConstantVal_4157_);
lean_ctor_set_uint8(v___x_4158_, sizeof(void*)*1, v_hasTrace_3836_);
v___x_4159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4158_);
v___x_4160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4160_, 0, v___x_4159_);
v_exportedInfo_x3f_4146_ = v___x_4160_;
v___y_4147_ = v_a_3778_;
v___y_4148_ = v_a_3779_;
goto v___jp_4145_;
}
}
else
{
lean_dec(v___x_4153_);
v_exportedInfo_x3f_4146_ = v___x_4031_;
v___y_4147_ = v_a_3778_;
v___y_4148_ = v_a_3779_;
goto v___jp_4145_;
}
v___jp_4145_:
{
lean_object* v_toConstantVal_4149_; lean_object* v_name_4150_; lean_object* v___x_4151_; uint8_t v___x_4152_; 
v_toConstantVal_4149_ = lean_ctor_get(v_val_4144_, 0);
v_name_4150_ = lean_ctor_get(v_toConstantVal_4149_, 0);
lean_inc_ref(v_val_4144_);
v___x_4151_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4151_, 0, v_val_4144_);
v___x_4152_ = 1;
lean_inc(v_name_4150_);
v_fst_4070_ = v_name_4150_;
v_fst_4071_ = v___x_4151_;
v_snd_4072_ = v___x_4152_;
v_exportedInfo_x3f_4073_ = v_exportedInfo_x3f_4146_;
v___y_4074_ = v___y_4147_;
v___y_4075_ = v___y_4148_;
goto v___jp_4069_;
}
}
case 1:
{
lean_object* v_val_4161_; 
v_val_4161_ = lean_ctor_get(v_decl_3776_, 0);
lean_inc_ref(v_val_4161_);
v_defn_4119_ = v_val_4161_;
v___y_4120_ = v_a_3778_;
v___y_4121_ = v_a_3779_;
goto v___jp_4118_;
}
case 5:
{
lean_object* v_defns_4162_; 
v_defns_4162_ = lean_ctor_get(v_decl_3776_, 0);
if (lean_obj_tag(v_defns_4162_) == 1)
{
lean_object* v_tail_4163_; 
v_tail_4163_ = lean_ctor_get(v_defns_4162_, 1);
if (lean_obj_tag(v_tail_4163_) == 0)
{
lean_object* v_head_4164_; 
v_head_4164_ = lean_ctor_get(v_defns_4162_, 0);
lean_inc(v_head_4164_);
v_defn_4119_ = v_head_4164_;
v___y_4120_ = v_a_3778_;
v___y_4121_ = v_a_3779_;
goto v___jp_4118_;
}
else
{
lean_object* v___x_4165_; 
v___x_4165_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3776_, v_a_3778_, v_a_3779_);
return v___x_4165_;
}
}
else
{
lean_object* v___x_4166_; 
v___x_4166_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3776_, v_a_3778_, v_a_3779_);
return v___x_4166_;
}
}
case 3:
{
lean_object* v_val_4167_; lean_object* v_exportedInfo_x3f_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___x_4176_; lean_object* v_env_4177_; lean_object* v___x_4178_; 
v_val_4167_ = lean_ctor_get(v_decl_3776_, 0);
v___x_4176_ = lean_st_ref_get(v_a_3779_);
v_env_4177_ = lean_ctor_get(v___x_4176_, 0);
lean_inc_ref(v_env_4177_);
lean_dec(v___x_4176_);
v___x_4178_ = lean_st_ref_get(v_a_3779_);
if (v_forceExpose_3777_ == 0)
{
lean_object* v_env_4179_; lean_object* v___x_4180_; uint8_t v_isModule_4181_; 
v_env_4179_ = lean_ctor_get(v___x_4178_, 0);
lean_inc_ref(v_env_4179_);
lean_dec(v___x_4178_);
v___x_4180_ = l_Lean_Environment_header(v_env_4177_);
lean_dec_ref(v_env_4177_);
v_isModule_4181_ = lean_ctor_get_uint8(v___x_4180_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4180_);
if (v_isModule_4181_ == 0)
{
lean_dec_ref(v_env_4179_);
v_exportedInfo_x3f_4169_ = v___x_4031_;
v___y_4170_ = v_a_3778_;
v___y_4171_ = v_a_3779_;
goto v___jp_4168_;
}
else
{
uint8_t v_isExporting_4182_; 
v_isExporting_4182_ = lean_ctor_get_uint8(v_env_4179_, sizeof(void*)*13);
lean_dec_ref(v_env_4179_);
if (v_isExporting_4182_ == 0)
{
lean_object* v_toConstantVal_4183_; uint8_t v_isUnsafe_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; 
v_toConstantVal_4183_ = lean_ctor_get(v_val_4167_, 0);
v_isUnsafe_4184_ = lean_ctor_get_uint8(v_val_4167_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4183_);
v___x_4185_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4185_, 0, v_toConstantVal_4183_);
lean_ctor_set_uint8(v___x_4185_, sizeof(void*)*1, v_isUnsafe_4184_);
v___x_4186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4186_, 0, v___x_4185_);
v___x_4187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4186_);
v_exportedInfo_x3f_4169_ = v___x_4187_;
v___y_4170_ = v_a_3778_;
v___y_4171_ = v_a_3779_;
goto v___jp_4168_;
}
else
{
v_exportedInfo_x3f_4169_ = v___x_4031_;
v___y_4170_ = v_a_3778_;
v___y_4171_ = v_a_3779_;
goto v___jp_4168_;
}
}
}
else
{
lean_dec(v___x_4178_);
lean_dec_ref(v_env_4177_);
v_exportedInfo_x3f_4169_ = v___x_4031_;
v___y_4170_ = v_a_3778_;
v___y_4171_ = v_a_3779_;
goto v___jp_4168_;
}
v___jp_4168_:
{
lean_object* v_toConstantVal_4172_; lean_object* v_name_4173_; lean_object* v___x_4174_; uint8_t v___x_4175_; 
v_toConstantVal_4172_ = lean_ctor_get(v_val_4167_, 0);
v_name_4173_ = lean_ctor_get(v_toConstantVal_4172_, 0);
lean_inc_ref(v_val_4167_);
v___x_4174_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4174_, 0, v_val_4167_);
v___x_4175_ = 3;
lean_inc(v_name_4173_);
v_fst_4070_ = v_name_4173_;
v_fst_4071_ = v___x_4174_;
v_snd_4072_ = v___x_4175_;
v_exportedInfo_x3f_4073_ = v_exportedInfo_x3f_4169_;
v___y_4074_ = v___y_4170_;
v___y_4075_ = v___y_4171_;
goto v___jp_4069_;
}
}
case 0:
{
lean_object* v_val_4188_; lean_object* v_toConstantVal_4189_; lean_object* v_name_4190_; lean_object* v___x_4191_; uint8_t v___x_4192_; 
v_val_4188_ = lean_ctor_get(v_decl_3776_, 0);
v_toConstantVal_4189_ = lean_ctor_get(v_val_4188_, 0);
v_name_4190_ = lean_ctor_get(v_toConstantVal_4189_, 0);
lean_inc_ref(v_val_4188_);
v___x_4191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4191_, 0, v_val_4188_);
v___x_4192_ = 2;
lean_inc(v_name_4190_);
v_fst_4070_ = v_name_4190_;
v_fst_4071_ = v___x_4191_;
v_snd_4072_ = v___x_4192_;
v_exportedInfo_x3f_4073_ = v___x_4031_;
v___y_4074_ = v_a_3778_;
v___y_4075_ = v_a_3779_;
goto v___jp_4069_;
}
default: 
{
lean_object* v___x_4193_; 
v___x_4193_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3776_, v_a_3778_, v_a_3779_);
return v___x_4193_;
}
}
v___jp_4032_:
{
lean_object* v___x_4039_; uint8_t v___x_4040_; 
lean_inc(v_decl_3776_);
v___x_4039_ = l_Lean_Declaration_getTopLevelNames(v_decl_3776_);
v___x_4040_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_4039_);
lean_dec(v___x_4039_);
if (v___x_4040_ == 0)
{
if (lean_obj_tag(v___y_4036_) == 0)
{
if (v___x_4040_ == 0)
{
lean_object* v_toCold_4041_; lean_object* v_options_4042_; uint8_t v_hasTrace_4043_; 
v_toCold_4041_ = lean_ctor_get(v___y_4037_, 0);
v_options_4042_ = lean_ctor_get(v_toCold_4041_, 2);
v_hasTrace_4043_ = lean_ctor_get_uint8(v_options_4042_, sizeof(void*)*1);
if (v_hasTrace_4043_ == 0)
{
v___y_3957_ = v___y_4033_;
v___y_3958_ = v___y_4034_;
v___y_3959_ = v___y_4035_;
v___y_3960_ = v___y_4037_;
v___y_3961_ = v___y_4038_;
goto v___jp_3956_;
}
else
{
lean_object* v_inheritedTraceOptions_4044_; lean_object* v___x_4045_; uint8_t v___x_4046_; 
v_inheritedTraceOptions_4044_ = lean_ctor_get(v_toCold_4041_, 11);
v___x_4045_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4046_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4044_, v_options_4042_, v___x_4045_);
if (v___x_4046_ == 0)
{
v___y_3957_ = v___y_4033_;
v___y_3958_ = v___y_4034_;
v___y_3959_ = v___y_4035_;
v___y_3960_ = v___y_4037_;
v___y_3961_ = v___y_4038_;
goto v___jp_3956_;
}
else
{
lean_object* v___x_4047_; lean_object* v___x_4048_; 
v___x_4047_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_4048_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3970_, v___x_4047_, v___y_4037_, v___y_4038_);
if (lean_obj_tag(v___x_4048_) == 0)
{
lean_dec_ref_known(v___x_4048_, 1);
v___y_3957_ = v___y_4033_;
v___y_3958_ = v___y_4034_;
v___y_3959_ = v___y_4035_;
v___y_3960_ = v___y_4037_;
v___y_3961_ = v___y_4038_;
goto v___jp_3956_;
}
else
{
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec(v_decl_3776_);
return v___x_4048_;
}
}
}
}
else
{
v___y_3999_ = v___y_4033_;
v___y_4000_ = v___y_4038_;
v___y_4001_ = v___y_4034_;
v___y_4002_ = v___x_4040_;
v___y_4003_ = v___y_4037_;
v___y_4004_ = v___y_4035_;
v___y_4005_ = v___y_4036_;
goto v___jp_3998_;
}
}
else
{
v___y_3999_ = v___y_4033_;
v___y_4000_ = v___y_4038_;
v___y_4001_ = v___y_4034_;
v___y_4002_ = v___x_4040_;
v___y_4003_ = v___y_4037_;
v___y_4004_ = v___y_4035_;
v___y_4005_ = v___y_4036_;
goto v___jp_3998_;
}
}
else
{
lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v_a_4051_; uint8_t v___x_4052_; 
lean_dec(v___y_4036_);
v___x_4049_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4050_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4049_, v___y_4037_);
v_a_4051_ = lean_ctor_get(v___x_4050_, 0);
lean_inc(v_a_4051_);
lean_dec_ref(v___x_4050_);
v___x_4052_ = lean_unbox(v_a_4051_);
lean_dec(v_a_4051_);
if (v___x_4052_ == 0)
{
lean_object* v_toCold_4053_; lean_object* v_options_4054_; uint8_t v_hasTrace_4055_; 
v_toCold_4053_ = lean_ctor_get(v___y_4037_, 0);
v_options_4054_ = lean_ctor_get(v_toCold_4053_, 2);
v_hasTrace_4055_ = lean_ctor_get_uint8(v_options_4054_, sizeof(void*)*1);
if (v_hasTrace_4055_ == 0)
{
v___y_3942_ = v___y_4033_;
v___y_3943_ = v___y_4034_;
v___y_3944_ = v___y_4035_;
v_exportedInfo_x3f_3945_ = v___x_4031_;
v___y_3946_ = v___y_4037_;
v___y_3947_ = v___y_4038_;
goto v___jp_3941_;
}
else
{
lean_object* v_inheritedTraceOptions_4056_; lean_object* v___x_4057_; uint8_t v___x_4058_; 
v_inheritedTraceOptions_4056_ = lean_ctor_get(v_toCold_4053_, 11);
v___x_4057_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4058_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4056_, v_options_4054_, v___x_4057_);
if (v___x_4058_ == 0)
{
v___y_3942_ = v___y_4033_;
v___y_3943_ = v___y_4034_;
v___y_3944_ = v___y_4035_;
v_exportedInfo_x3f_3945_ = v___x_4031_;
v___y_3946_ = v___y_4037_;
v___y_3947_ = v___y_4038_;
goto v___jp_3941_;
}
else
{
lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4059_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_4060_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3970_, v___x_4059_, v___y_4037_, v___y_4038_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_dec_ref_known(v___x_4060_, 1);
v___y_3942_ = v___y_4033_;
v___y_3943_ = v___y_4034_;
v___y_3944_ = v___y_4035_;
v_exportedInfo_x3f_3945_ = v___x_4031_;
v___y_3946_ = v___y_4037_;
v___y_3947_ = v___y_4038_;
goto v___jp_3941_;
}
else
{
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec(v_decl_3776_);
return v___x_4060_;
}
}
}
}
else
{
lean_object* v_toCold_4061_; lean_object* v_options_4062_; uint8_t v_hasTrace_4063_; 
v_toCold_4061_ = lean_ctor_get(v___y_4037_, 0);
v_options_4062_ = lean_ctor_get(v_toCold_4061_, 2);
v_hasTrace_4063_ = lean_ctor_get_uint8(v_options_4062_, sizeof(void*)*1);
if (v_hasTrace_4063_ == 0)
{
v___y_3964_ = v___y_4033_;
v___y_3965_ = v___y_4034_;
v___y_3966_ = v___y_4035_;
v___y_3967_ = v___y_4037_;
v___y_3968_ = v___y_4038_;
goto v___jp_3963_;
}
else
{
lean_object* v_inheritedTraceOptions_4064_; lean_object* v___x_4065_; uint8_t v___x_4066_; 
v_inheritedTraceOptions_4064_ = lean_ctor_get(v_toCold_4061_, 11);
v___x_4065_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4066_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4064_, v_options_4062_, v___x_4065_);
if (v___x_4066_ == 0)
{
v___y_3964_ = v___y_4033_;
v___y_3965_ = v___y_4034_;
v___y_3966_ = v___y_4035_;
v___y_3967_ = v___y_4037_;
v___y_3968_ = v___y_4038_;
goto v___jp_3963_;
}
else
{
lean_object* v___x_4067_; lean_object* v___x_4068_; 
v___x_4067_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_4068_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3970_, v___x_4067_, v___y_4037_, v___y_4038_);
if (lean_obj_tag(v___x_4068_) == 0)
{
lean_dec_ref_known(v___x_4068_, 1);
v___y_3964_ = v___y_4033_;
v___y_3965_ = v___y_4034_;
v___y_3966_ = v___y_4035_;
v___y_3967_ = v___y_4037_;
v___y_3968_ = v___y_4038_;
goto v___jp_3963_;
}
else
{
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec(v_decl_3776_);
return v___x_4068_;
}
}
}
}
}
}
v___jp_4069_:
{
lean_object* v___x_4076_; lean_object* v_env_4077_; uint8_t v___x_4078_; 
v___x_4076_ = lean_st_ref_get(v___y_4075_);
v_env_4077_ = lean_ctor_get(v___x_4076_, 0);
lean_inc_ref(v_env_4077_);
lean_dec(v___x_4076_);
v___x_4078_ = l_Lean_Environment_containsOnBranch(v_env_4077_, v_fst_4070_);
lean_dec_ref(v_env_4077_);
if (v___x_4078_ == 0)
{
v___y_4033_ = v_snd_4072_;
v___y_4034_ = v_fst_4071_;
v___y_4035_ = v_fst_4070_;
v___y_4036_ = v_exportedInfo_x3f_4073_;
v___y_4037_ = v___y_4074_;
v___y_4038_ = v___y_4075_;
goto v___jp_4032_;
}
else
{
lean_object* v___x_4079_; lean_object* v_env_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
lean_dec(v_exportedInfo_x3f_4073_);
lean_dec_ref(v_fst_4071_);
lean_dec(v_decl_3776_);
v___x_4079_ = lean_st_ref_get(v___y_4075_);
v_env_4080_ = lean_ctor_get(v___x_4079_, 0);
lean_inc_ref(v_env_4080_);
lean_dec(v___x_4079_);
v___x_4081_ = lean_elab_environment_to_kernel_env(v_env_4080_);
v___x_4082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4081_);
lean_ctor_set(v___x_4082_, 1, v_fst_4070_);
v___x_4083_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4082_, v___y_4074_, v___y_4075_);
return v___x_4083_;
}
}
v___jp_4084_:
{
lean_object* v_toConstantVal_4089_; lean_object* v_name_4090_; lean_object* v___x_4091_; uint8_t v___x_4092_; 
v_toConstantVal_4089_ = lean_ctor_get(v___y_4085_, 0);
v_name_4090_ = lean_ctor_get(v_toConstantVal_4089_, 0);
lean_inc(v_name_4090_);
v___x_4091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4091_, 0, v___y_4085_);
v___x_4092_ = 0;
v_fst_4070_ = v_name_4090_;
v_fst_4071_ = v___x_4091_;
v_snd_4072_ = v___x_4092_;
v_exportedInfo_x3f_4073_ = v_exportedInfo_x3f_4086_;
v___y_4074_ = v___y_4087_;
v___y_4075_ = v___y_4088_;
goto v___jp_4069_;
}
v___jp_4093_:
{
lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; 
v___x_4099_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4099_, 0, v___y_4096_);
lean_ctor_set_uint8(v___x_4099_, sizeof(void*)*1, v___y_4098_);
v___x_4100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4099_);
v___x_4101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4101_, 0, v___x_4100_);
v___y_4085_ = v___y_4095_;
v_exportedInfo_x3f_4086_ = v___x_4101_;
v___y_4087_ = v___y_4094_;
v___y_4088_ = v___y_4097_;
goto v___jp_4084_;
}
v___jp_4102_:
{
uint8_t v___x_4109_; uint8_t v___x_4110_; 
v___x_4109_ = 1;
v___x_4110_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4105_, v___x_4109_);
if (v___x_4110_ == 0)
{
v___y_4094_ = v___y_4107_;
v___y_4095_ = v___y_4103_;
v___y_4096_ = v_toConstantVal_4104_;
v___y_4097_ = v___y_4108_;
v___y_4098_ = v___y_4106_;
goto v___jp_4093_;
}
else
{
v___y_4094_ = v___y_4107_;
v___y_4095_ = v___y_4103_;
v___y_4096_ = v_toConstantVal_4104_;
v___y_4097_ = v___y_4108_;
v___y_4098_ = v_hasTrace_3836_;
goto v___jp_4093_;
}
}
v___jp_4111_:
{
lean_object* v_toConstantVal_4116_; uint8_t v_safety_4117_; 
v_toConstantVal_4116_ = lean_ctor_get(v___y_4112_, 0);
lean_inc_ref(v_toConstantVal_4116_);
v_safety_4117_ = lean_ctor_get_uint8(v___y_4112_, sizeof(void*)*4);
v___y_4103_ = v___y_4112_;
v_toConstantVal_4104_ = v_toConstantVal_4116_;
v_safety_4105_ = v_safety_4117_;
v___y_4106_ = v___y_4113_;
v___y_4107_ = v___y_4114_;
v___y_4108_ = v___y_4115_;
goto v___jp_4102_;
}
v___jp_4118_:
{
lean_object* v___x_4122_; lean_object* v_env_4123_; lean_object* v___x_4124_; 
v___x_4122_ = lean_st_ref_get(v___y_4121_);
v_env_4123_ = lean_ctor_get(v___x_4122_, 0);
lean_inc_ref(v_env_4123_);
lean_dec(v___x_4122_);
v___x_4124_ = lean_st_ref_get(v___y_4121_);
if (v_forceExpose_3777_ == 0)
{
lean_object* v_env_4125_; lean_object* v___x_4126_; uint8_t v_isModule_4127_; 
v_env_4125_ = lean_ctor_get(v___x_4124_, 0);
lean_inc_ref(v_env_4125_);
lean_dec(v___x_4124_);
v___x_4126_ = l_Lean_Environment_header(v_env_4123_);
lean_dec_ref(v_env_4123_);
v_isModule_4127_ = lean_ctor_get_uint8(v___x_4126_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4126_);
if (v_isModule_4127_ == 0)
{
lean_dec_ref(v_env_4125_);
v___y_4085_ = v_defn_4119_;
v_exportedInfo_x3f_4086_ = v___x_4031_;
v___y_4087_ = v___y_4120_;
v___y_4088_ = v___y_4121_;
goto v___jp_4084_;
}
else
{
uint8_t v_isExporting_4128_; 
v_isExporting_4128_ = lean_ctor_get_uint8(v_env_4125_, sizeof(void*)*13);
lean_dec_ref(v_env_4125_);
if (v_isExporting_4128_ == 0)
{
lean_object* v_toCold_4129_; lean_object* v_options_4130_; uint8_t v_hasTrace_4131_; 
v_toCold_4129_ = lean_ctor_get(v___y_4120_, 0);
v_options_4130_ = lean_ctor_get(v_toCold_4129_, 2);
v_hasTrace_4131_ = lean_ctor_get_uint8(v_options_4130_, sizeof(void*)*1);
if (v_hasTrace_4131_ == 0)
{
v___y_4112_ = v_defn_4119_;
v___y_4113_ = v_isModule_4127_;
v___y_4114_ = v___y_4120_;
v___y_4115_ = v___y_4121_;
goto v___jp_4111_;
}
else
{
lean_object* v_inheritedTraceOptions_4132_; lean_object* v___x_4133_; uint8_t v___x_4134_; 
v_inheritedTraceOptions_4132_ = lean_ctor_get(v_toCold_4129_, 11);
v___x_4133_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4134_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4132_, v_options_4130_, v___x_4133_);
if (v___x_4134_ == 0)
{
v___y_4112_ = v_defn_4119_;
v___y_4113_ = v_isModule_4127_;
v___y_4114_ = v___y_4120_;
v___y_4115_ = v___y_4121_;
goto v___jp_4111_;
}
else
{
lean_object* v_toConstantVal_4135_; uint8_t v_safety_4136_; lean_object* v_name_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; 
v_toConstantVal_4135_ = lean_ctor_get(v_defn_4119_, 0);
lean_inc_ref(v_toConstantVal_4135_);
v_safety_4136_ = lean_ctor_get_uint8(v_defn_4119_, sizeof(void*)*4);
v_name_4137_ = lean_ctor_get(v_toConstantVal_4135_, 0);
v___x_4138_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_4137_);
v___x_4139_ = l_Lean_MessageData_ofName(v_name_4137_);
v___x_4140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4140_, 0, v___x_4138_);
lean_ctor_set(v___x_4140_, 1, v___x_4139_);
v___x_4141_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4142_, 0, v___x_4140_);
lean_ctor_set(v___x_4142_, 1, v___x_4141_);
v___x_4143_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3970_, v___x_4142_, v___y_4120_, v___y_4121_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_dec_ref_known(v___x_4143_, 1);
v___y_4103_ = v_defn_4119_;
v_toConstantVal_4104_ = v_toConstantVal_4135_;
v_safety_4105_ = v_safety_4136_;
v___y_4106_ = v_isModule_4127_;
v___y_4107_ = v___y_4120_;
v___y_4108_ = v___y_4121_;
goto v___jp_4102_;
}
else
{
lean_dec_ref(v_toConstantVal_4135_);
lean_dec_ref(v_defn_4119_);
lean_dec(v_decl_3776_);
return v___x_4143_;
}
}
}
}
else
{
v___y_4085_ = v_defn_4119_;
v_exportedInfo_x3f_4086_ = v___x_4031_;
v___y_4087_ = v___y_4120_;
v___y_4088_ = v___y_4121_;
goto v___jp_4084_;
}
}
}
else
{
lean_dec(v___x_4124_);
lean_dec_ref(v_env_4123_);
v___y_4085_ = v_defn_4119_;
v_exportedInfo_x3f_4086_ = v___x_4031_;
v___y_4087_ = v___y_4120_;
v___y_4088_ = v___y_4121_;
goto v___jp_4084_;
}
}
}
}
}
else
{
lean_object* v___f_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; uint8_t v___x_4200_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v_a_4204_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; uint8_t v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v_a_4305_; lean_object* v___y_4315_; lean_object* v___y_4316_; lean_object* v___y_4317_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; 
lean_inc(v_decl_3776_);
v___f_4197_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed), 5, 1);
lean_closure_set(v___f_4197_, 0, v_decl_3776_);
v___x_4198_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_4199_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4200_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3835_, v_options_3834_, v___x_4199_);
if (v___x_4200_ == 0)
{
lean_object* v___x_4504_; uint8_t v___x_4505_; lean_object* v___y_4507_; lean_object* v___y_4508_; lean_object* v___y_4509_; lean_object* v___y_4510_; lean_object* v___y_4511_; lean_object* v___y_4512_; lean_object* v___y_4513_; lean_object* v___y_4514_; lean_object* v___y_4515_; lean_object* v___y_4516_; lean_object* v___y_4517_; lean_object* v___y_4580_; lean_object* v___y_4581_; lean_object* v___y_4582_; lean_object* v___y_4583_; lean_object* v___y_4584_; uint8_t v___y_4585_; lean_object* v___y_4586_; lean_object* v___y_4587_; lean_object* v___y_4609_; uint8_t v___y_4610_; lean_object* v___y_4611_; lean_object* v_exportedInfo_x3f_4612_; lean_object* v___y_4613_; lean_object* v___y_4614_; lean_object* v___y_4624_; uint8_t v___y_4625_; lean_object* v___y_4626_; lean_object* v___y_4627_; lean_object* v___y_4628_; lean_object* v___y_4631_; uint8_t v___y_4632_; lean_object* v___y_4633_; lean_object* v___y_4634_; lean_object* v___y_4635_; 
v___x_4504_ = l_Lean_trace_profiler;
v___x_4505_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3834_, v___x_4504_);
if (v___x_4505_ == 0)
{
lean_object* v___x_4637_; lean_object* v_env_4638_; lean_object* v_nextMacroScope_4639_; lean_object* v_ngen_4640_; lean_object* v_auxDeclNGen_4641_; lean_object* v_traceState_4642_; lean_object* v_recordedDeps_4643_; lean_object* v_messages_4644_; lean_object* v_infoState_4645_; lean_object* v_snapshotTasks_4646_; lean_object* v___x_4648_; uint8_t v_isShared_4649_; uint8_t v_isSharedCheck_4880_; 
lean_dec_ref(v___f_4197_);
v___x_4637_ = lean_st_ref_take(v_a_3779_);
v_env_4638_ = lean_ctor_get(v___x_4637_, 0);
v_nextMacroScope_4639_ = lean_ctor_get(v___x_4637_, 1);
v_ngen_4640_ = lean_ctor_get(v___x_4637_, 2);
v_auxDeclNGen_4641_ = lean_ctor_get(v___x_4637_, 3);
v_traceState_4642_ = lean_ctor_get(v___x_4637_, 4);
v_recordedDeps_4643_ = lean_ctor_get(v___x_4637_, 6);
v_messages_4644_ = lean_ctor_get(v___x_4637_, 7);
v_infoState_4645_ = lean_ctor_get(v___x_4637_, 8);
v_snapshotTasks_4646_ = lean_ctor_get(v___x_4637_, 9);
v_isSharedCheck_4880_ = !lean_is_exclusive(v___x_4637_);
if (v_isSharedCheck_4880_ == 0)
{
lean_object* v_unused_4881_; 
v_unused_4881_ = lean_ctor_get(v___x_4637_, 5);
lean_dec(v_unused_4881_);
v___x_4648_ = v___x_4637_;
v_isShared_4649_ = v_isSharedCheck_4880_;
goto v_resetjp_4647_;
}
else
{
lean_inc(v_snapshotTasks_4646_);
lean_inc(v_infoState_4645_);
lean_inc(v_messages_4644_);
lean_inc(v_recordedDeps_4643_);
lean_inc(v_traceState_4642_);
lean_inc(v_auxDeclNGen_4641_);
lean_inc(v_ngen_4640_);
lean_inc(v_nextMacroScope_4639_);
lean_inc(v_env_4638_);
lean_dec(v___x_4637_);
v___x_4648_ = lean_box(0);
v_isShared_4649_ = v_isSharedCheck_4880_;
goto v_resetjp_4647_;
}
v_resetjp_4647_:
{
lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___y_4654_; uint8_t v___y_4655_; lean_object* v___y_4656_; lean_object* v___y_4657_; lean_object* v___y_4658_; lean_object* v___y_4659_; uint8_t v___y_4660_; lean_object* v___x_4684_; 
lean_inc(v_decl_3776_);
v___x_4650_ = l_Lean_Declaration_getNames(v_decl_3776_);
v___x_4651_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4638_, v___x_4650_);
v___x_4652_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 5, v___x_4652_);
lean_ctor_set(v___x_4648_, 0, v___x_4651_);
v___x_4684_ = v___x_4648_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4879_; 
v_reuseFailAlloc_4879_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4879_, 0, v___x_4651_);
lean_ctor_set(v_reuseFailAlloc_4879_, 1, v_nextMacroScope_4639_);
lean_ctor_set(v_reuseFailAlloc_4879_, 2, v_ngen_4640_);
lean_ctor_set(v_reuseFailAlloc_4879_, 3, v_auxDeclNGen_4641_);
lean_ctor_set(v_reuseFailAlloc_4879_, 4, v_traceState_4642_);
lean_ctor_set(v_reuseFailAlloc_4879_, 5, v___x_4652_);
lean_ctor_set(v_reuseFailAlloc_4879_, 6, v_recordedDeps_4643_);
lean_ctor_set(v_reuseFailAlloc_4879_, 7, v_messages_4644_);
lean_ctor_set(v_reuseFailAlloc_4879_, 8, v_infoState_4645_);
lean_ctor_set(v_reuseFailAlloc_4879_, 9, v_snapshotTasks_4646_);
v___x_4684_ = v_reuseFailAlloc_4879_;
goto v_reusejp_4683_;
}
v___jp_4653_:
{
lean_object* v___x_4661_; lean_object* v_env_4662_; lean_object* v_nextMacroScope_4663_; lean_object* v_ngen_4664_; lean_object* v_auxDeclNGen_4665_; lean_object* v_traceState_4666_; lean_object* v_recordedDeps_4667_; lean_object* v_messages_4668_; lean_object* v_infoState_4669_; lean_object* v_snapshotTasks_4670_; lean_object* v___x_4672_; uint8_t v_isShared_4673_; uint8_t v_isSharedCheck_4681_; 
v___x_4661_ = lean_st_ref_take(v___y_4657_);
v_env_4662_ = lean_ctor_get(v___x_4661_, 0);
v_nextMacroScope_4663_ = lean_ctor_get(v___x_4661_, 1);
v_ngen_4664_ = lean_ctor_get(v___x_4661_, 2);
v_auxDeclNGen_4665_ = lean_ctor_get(v___x_4661_, 3);
v_traceState_4666_ = lean_ctor_get(v___x_4661_, 4);
v_recordedDeps_4667_ = lean_ctor_get(v___x_4661_, 6);
v_messages_4668_ = lean_ctor_get(v___x_4661_, 7);
v_infoState_4669_ = lean_ctor_get(v___x_4661_, 8);
v_snapshotTasks_4670_ = lean_ctor_get(v___x_4661_, 9);
v_isSharedCheck_4681_ = !lean_is_exclusive(v___x_4661_);
if (v_isSharedCheck_4681_ == 0)
{
lean_object* v_unused_4682_; 
v_unused_4682_ = lean_ctor_get(v___x_4661_, 5);
lean_dec(v_unused_4682_);
v___x_4672_ = v___x_4661_;
v_isShared_4673_ = v_isSharedCheck_4681_;
goto v_resetjp_4671_;
}
else
{
lean_inc(v_snapshotTasks_4670_);
lean_inc(v_infoState_4669_);
lean_inc(v_messages_4668_);
lean_inc(v_recordedDeps_4667_);
lean_inc(v_traceState_4666_);
lean_inc(v_auxDeclNGen_4665_);
lean_inc(v_ngen_4664_);
lean_inc(v_nextMacroScope_4663_);
lean_inc(v_env_4662_);
lean_dec(v___x_4661_);
v___x_4672_ = lean_box(0);
v_isShared_4673_ = v_isSharedCheck_4681_;
goto v_resetjp_4671_;
}
v_resetjp_4671_:
{
lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4678_; 
v___x_4674_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4675_ = lean_box(v___y_4660_);
lean_inc(v___y_4656_);
v___x_4676_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4674_, v_env_4662_, v___y_4656_, v___x_4675_, v___y_4655_);
if (v_isShared_4673_ == 0)
{
lean_ctor_set(v___x_4672_, 5, v___x_4652_);
lean_ctor_set(v___x_4672_, 0, v___x_4676_);
v___x_4678_ = v___x_4672_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v___x_4676_);
lean_ctor_set(v_reuseFailAlloc_4680_, 1, v_nextMacroScope_4663_);
lean_ctor_set(v_reuseFailAlloc_4680_, 2, v_ngen_4664_);
lean_ctor_set(v_reuseFailAlloc_4680_, 3, v_auxDeclNGen_4665_);
lean_ctor_set(v_reuseFailAlloc_4680_, 4, v_traceState_4666_);
lean_ctor_set(v_reuseFailAlloc_4680_, 5, v___x_4652_);
lean_ctor_set(v_reuseFailAlloc_4680_, 6, v_recordedDeps_4667_);
lean_ctor_set(v_reuseFailAlloc_4680_, 7, v_messages_4668_);
lean_ctor_set(v_reuseFailAlloc_4680_, 8, v_infoState_4669_);
lean_ctor_set(v_reuseFailAlloc_4680_, 9, v_snapshotTasks_4670_);
v___x_4678_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
lean_object* v___x_4679_; 
v___x_4679_ = lean_st_ref_put(v___y_4657_, v___x_4678_);
v___y_4609_ = v___y_4656_;
v___y_4610_ = v___y_4660_;
v___y_4611_ = v___y_4658_;
v_exportedInfo_x3f_4612_ = v___y_4659_;
v___y_4613_ = v___y_4654_;
v___y_4614_ = v___y_4657_;
goto v___jp_4608_;
}
}
}
v_reusejp_4683_:
{
lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___y_4688_; uint8_t v___y_4689_; lean_object* v___y_4690_; lean_object* v___y_4691_; lean_object* v___y_4692_; lean_object* v___y_4693_; lean_object* v_fst_4722_; lean_object* v_fst_4723_; uint8_t v_snd_4724_; lean_object* v_exportedInfo_x3f_4725_; lean_object* v___y_4726_; lean_object* v___y_4727_; lean_object* v___y_4737_; lean_object* v_exportedInfo_x3f_4738_; lean_object* v___y_4739_; lean_object* v___y_4740_; lean_object* v___y_4746_; lean_object* v___y_4747_; lean_object* v___y_4748_; lean_object* v___y_4749_; uint8_t v___y_4750_; lean_object* v___y_4755_; lean_object* v_toConstantVal_4756_; uint8_t v_safety_4757_; uint8_t v___y_4758_; lean_object* v___y_4759_; lean_object* v___y_4760_; lean_object* v___y_4764_; uint8_t v___y_4765_; lean_object* v___y_4766_; lean_object* v___y_4767_; lean_object* v___y_4771_; lean_object* v___y_4772_; lean_object* v___y_4773_; uint8_t v___y_4774_; lean_object* v___y_4790_; lean_object* v___y_4791_; lean_object* v___y_4792_; lean_object* v___y_4793_; lean_object* v___y_4794_; lean_object* v_defn_4799_; lean_object* v___y_4800_; lean_object* v___y_4801_; 
v___x_4685_ = lean_st_ref_put(v_a_3779_, v___x_4684_);
v___x_4686_ = lean_box(0);
switch(lean_obj_tag(v_decl_3776_))
{
case 2:
{
lean_object* v_val_4807_; lean_object* v_exportedInfo_x3f_4809_; lean_object* v___y_4810_; lean_object* v___y_4811_; lean_object* v___y_4817_; lean_object* v___y_4818_; lean_object* v___x_4823_; lean_object* v_env_4824_; 
v_val_4807_ = lean_ctor_get(v_decl_3776_, 0);
v___x_4823_ = lean_st_ref_get(v_a_3779_);
v_env_4824_ = lean_ctor_get(v___x_4823_, 0);
lean_inc_ref(v_env_4824_);
lean_dec(v___x_4823_);
if (v_forceExpose_3777_ == 0)
{
goto v___jp_4825_;
}
else
{
if (v___x_4505_ == 0)
{
lean_dec_ref(v_env_4824_);
v_exportedInfo_x3f_4809_ = v___x_4686_;
v___y_4810_ = v_a_3778_;
v___y_4811_ = v_a_3779_;
goto v___jp_4808_;
}
else
{
goto v___jp_4825_;
}
}
v___jp_4808_:
{
lean_object* v_toConstantVal_4812_; lean_object* v_name_4813_; lean_object* v___x_4814_; uint8_t v___x_4815_; 
v_toConstantVal_4812_ = lean_ctor_get(v_val_4807_, 0);
v_name_4813_ = lean_ctor_get(v_toConstantVal_4812_, 0);
lean_inc_ref(v_val_4807_);
v___x_4814_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4814_, 0, v_val_4807_);
v___x_4815_ = 1;
lean_inc(v_name_4813_);
v_fst_4722_ = v_name_4813_;
v_fst_4723_ = v___x_4814_;
v_snd_4724_ = v___x_4815_;
v_exportedInfo_x3f_4725_ = v_exportedInfo_x3f_4809_;
v___y_4726_ = v___y_4810_;
v___y_4727_ = v___y_4811_;
goto v___jp_4721_;
}
v___jp_4816_:
{
lean_object* v_toConstantVal_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; 
v_toConstantVal_4819_ = lean_ctor_get(v_val_4807_, 0);
lean_inc_ref(v_toConstantVal_4819_);
v___x_4820_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4820_, 0, v_toConstantVal_4819_);
lean_ctor_set_uint8(v___x_4820_, sizeof(void*)*1, v___x_4505_);
v___x_4821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4821_, 0, v___x_4820_);
v___x_4822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4822_, 0, v___x_4821_);
v_exportedInfo_x3f_4809_ = v___x_4822_;
v___y_4810_ = v___y_4817_;
v___y_4811_ = v___y_4818_;
goto v___jp_4808_;
}
v___jp_4825_:
{
lean_object* v___x_4826_; uint8_t v_isModule_4827_; 
v___x_4826_ = l_Lean_Environment_header(v_env_4824_);
lean_dec_ref(v_env_4824_);
v_isModule_4827_ = lean_ctor_get_uint8(v___x_4826_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4826_);
if (v_isModule_4827_ == 0)
{
v_exportedInfo_x3f_4809_ = v___x_4686_;
v___y_4810_ = v_a_3778_;
v___y_4811_ = v_a_3779_;
goto v___jp_4808_;
}
else
{
if (v___x_4200_ == 0)
{
v___y_4817_ = v_a_3778_;
v___y_4818_ = v_a_3779_;
goto v___jp_4816_;
}
else
{
lean_object* v_toConstantVal_4828_; lean_object* v_name_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; 
v_toConstantVal_4828_ = lean_ctor_get(v_val_4807_, 0);
v_name_4829_ = lean_ctor_get(v_toConstantVal_4828_, 0);
v___x_4830_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4829_);
v___x_4831_ = l_Lean_MessageData_ofName(v_name_4829_);
v___x_4832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4832_, 0, v___x_4830_);
lean_ctor_set(v___x_4832_, 1, v___x_4831_);
v___x_4833_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4834_, 0, v___x_4832_);
lean_ctor_set(v___x_4834_, 1, v___x_4833_);
v___x_4835_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3970_, v___x_4834_, v_a_3778_, v_a_3779_);
if (lean_obj_tag(v___x_4835_) == 0)
{
lean_dec_ref_known(v___x_4835_, 1);
v___y_4817_ = v_a_3778_;
v___y_4818_ = v_a_3779_;
goto v___jp_4816_;
}
else
{
lean_dec_ref_known(v_decl_3776_, 1);
return v___x_4835_;
}
}
}
}
}
case 1:
{
lean_object* v_val_4836_; 
v_val_4836_ = lean_ctor_get(v_decl_3776_, 0);
lean_inc_ref(v_val_4836_);
v_defn_4799_ = v_val_4836_;
v___y_4800_ = v_a_3778_;
v___y_4801_ = v_a_3779_;
goto v___jp_4798_;
}
case 5:
{
lean_object* v_defns_4837_; 
v_defns_4837_ = lean_ctor_get(v_decl_3776_, 0);
if (lean_obj_tag(v_defns_4837_) == 1)
{
lean_object* v_tail_4838_; 
v_tail_4838_ = lean_ctor_get(v_defns_4837_, 1);
if (lean_obj_tag(v_tail_4838_) == 0)
{
lean_object* v_head_4839_; 
v_head_4839_ = lean_ctor_get(v_defns_4837_, 0);
lean_inc(v_head_4839_);
v_defn_4799_ = v_head_4839_;
v___y_4800_ = v_a_3778_;
v___y_4801_ = v_a_3779_;
goto v___jp_4798_;
}
else
{
v___y_3972_ = v_a_3778_;
v_options_3973_ = v_options_3834_;
v_inheritedTraceOptions_3974_ = v_inheritedTraceOptions_3835_;
v___y_3975_ = v_a_3779_;
goto v___jp_3971_;
}
}
else
{
v___y_3972_ = v_a_3778_;
v_options_3973_ = v_options_3834_;
v_inheritedTraceOptions_3974_ = v_inheritedTraceOptions_3835_;
v___y_3975_ = v_a_3779_;
goto v___jp_3971_;
}
}
case 3:
{
lean_object* v_val_4840_; lean_object* v_exportedInfo_x3f_4842_; lean_object* v___y_4843_; lean_object* v___y_4844_; lean_object* v___y_4850_; lean_object* v___y_4851_; lean_object* v___x_4857_; lean_object* v_env_4858_; lean_object* v___x_4859_; lean_object* v_env_4869_; 
v_val_4840_ = lean_ctor_get(v_decl_3776_, 0);
v___x_4857_ = lean_st_ref_get(v_a_3779_);
v_env_4858_ = lean_ctor_get(v___x_4857_, 0);
lean_inc_ref(v_env_4858_);
lean_dec(v___x_4857_);
v___x_4859_ = lean_st_ref_get(v_a_3779_);
v_env_4869_ = lean_ctor_get(v___x_4859_, 0);
lean_inc_ref(v_env_4869_);
lean_dec(v___x_4859_);
if (v_forceExpose_3777_ == 0)
{
goto v___jp_4870_;
}
else
{
if (v___x_4505_ == 0)
{
lean_dec_ref(v_env_4869_);
lean_dec_ref(v_env_4858_);
v_exportedInfo_x3f_4842_ = v___x_4686_;
v___y_4843_ = v_a_3778_;
v___y_4844_ = v_a_3779_;
goto v___jp_4841_;
}
else
{
goto v___jp_4870_;
}
}
v___jp_4841_:
{
lean_object* v_toConstantVal_4845_; lean_object* v_name_4846_; lean_object* v___x_4847_; uint8_t v___x_4848_; 
v_toConstantVal_4845_ = lean_ctor_get(v_val_4840_, 0);
v_name_4846_ = lean_ctor_get(v_toConstantVal_4845_, 0);
lean_inc_ref(v_val_4840_);
v___x_4847_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4847_, 0, v_val_4840_);
v___x_4848_ = 3;
lean_inc(v_name_4846_);
v_fst_4722_ = v_name_4846_;
v_fst_4723_ = v___x_4847_;
v_snd_4724_ = v___x_4848_;
v_exportedInfo_x3f_4725_ = v_exportedInfo_x3f_4842_;
v___y_4726_ = v___y_4843_;
v___y_4727_ = v___y_4844_;
goto v___jp_4721_;
}
v___jp_4849_:
{
lean_object* v_toConstantVal_4852_; uint8_t v_isUnsafe_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; 
v_toConstantVal_4852_ = lean_ctor_get(v_val_4840_, 0);
v_isUnsafe_4853_ = lean_ctor_get_uint8(v_val_4840_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4852_);
v___x_4854_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4854_, 0, v_toConstantVal_4852_);
lean_ctor_set_uint8(v___x_4854_, sizeof(void*)*1, v_isUnsafe_4853_);
v___x_4855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4855_, 0, v___x_4854_);
v___x_4856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4856_, 0, v___x_4855_);
v_exportedInfo_x3f_4842_ = v___x_4856_;
v___y_4843_ = v___y_4850_;
v___y_4844_ = v___y_4851_;
goto v___jp_4841_;
}
v___jp_4860_:
{
if (v___x_4200_ == 0)
{
v___y_4850_ = v_a_3778_;
v___y_4851_ = v_a_3779_;
goto v___jp_4849_;
}
else
{
lean_object* v_toConstantVal_4861_; lean_object* v_name_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; 
v_toConstantVal_4861_ = lean_ctor_get(v_val_4840_, 0);
v_name_4862_ = lean_ctor_get(v_toConstantVal_4861_, 0);
v___x_4863_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4862_);
v___x_4864_ = l_Lean_MessageData_ofName(v_name_4862_);
v___x_4865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4865_, 0, v___x_4863_);
lean_ctor_set(v___x_4865_, 1, v___x_4864_);
v___x_4866_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4867_, 0, v___x_4865_);
lean_ctor_set(v___x_4867_, 1, v___x_4866_);
v___x_4868_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3970_, v___x_4867_, v_a_3778_, v_a_3779_);
if (lean_obj_tag(v___x_4868_) == 0)
{
lean_dec_ref_known(v___x_4868_, 1);
v___y_4850_ = v_a_3778_;
v___y_4851_ = v_a_3779_;
goto v___jp_4849_;
}
else
{
lean_dec_ref_known(v_decl_3776_, 1);
return v___x_4868_;
}
}
}
v___jp_4870_:
{
lean_object* v___x_4871_; uint8_t v_isModule_4872_; 
v___x_4871_ = l_Lean_Environment_header(v_env_4858_);
lean_dec_ref(v_env_4858_);
v_isModule_4872_ = lean_ctor_get_uint8(v___x_4871_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4871_);
if (v_isModule_4872_ == 0)
{
lean_dec_ref(v_env_4869_);
v_exportedInfo_x3f_4842_ = v___x_4686_;
v___y_4843_ = v_a_3778_;
v___y_4844_ = v_a_3779_;
goto v___jp_4841_;
}
else
{
uint8_t v_isExporting_4873_; 
v_isExporting_4873_ = lean_ctor_get_uint8(v_env_4869_, sizeof(void*)*13);
lean_dec_ref(v_env_4869_);
if (v_isExporting_4873_ == 0)
{
goto v___jp_4860_;
}
else
{
if (v___x_4505_ == 0)
{
v_exportedInfo_x3f_4842_ = v___x_4686_;
v___y_4843_ = v_a_3778_;
v___y_4844_ = v_a_3779_;
goto v___jp_4841_;
}
else
{
goto v___jp_4860_;
}
}
}
}
}
case 0:
{
lean_object* v_val_4874_; lean_object* v_toConstantVal_4875_; lean_object* v_name_4876_; lean_object* v___x_4877_; uint8_t v___x_4878_; 
v_val_4874_ = lean_ctor_get(v_decl_3776_, 0);
v_toConstantVal_4875_ = lean_ctor_get(v_val_4874_, 0);
v_name_4876_ = lean_ctor_get(v_toConstantVal_4875_, 0);
lean_inc_ref(v_val_4874_);
v___x_4877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4877_, 0, v_val_4874_);
v___x_4878_ = 2;
lean_inc(v_name_4876_);
v_fst_4722_ = v_name_4876_;
v_fst_4723_ = v___x_4877_;
v_snd_4724_ = v___x_4878_;
v_exportedInfo_x3f_4725_ = v___x_4686_;
v___y_4726_ = v_a_3778_;
v___y_4727_ = v_a_3779_;
goto v___jp_4721_;
}
default: 
{
v___y_3972_ = v_a_3778_;
v_options_3973_ = v_options_3834_;
v_inheritedTraceOptions_3974_ = v_inheritedTraceOptions_3835_;
v___y_3975_ = v_a_3779_;
goto v___jp_3971_;
}
}
v___jp_4687_:
{
lean_object* v___x_4694_; uint8_t v___x_4695_; 
lean_inc(v_decl_3776_);
v___x_4694_ = l_Lean_Declaration_getTopLevelNames(v_decl_3776_);
v___x_4695_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_4694_);
lean_dec(v___x_4694_);
if (v___x_4695_ == 0)
{
if (lean_obj_tag(v___y_4690_) == 0)
{
if (v___x_4695_ == 0)
{
lean_object* v_toCold_4696_; lean_object* v_options_4697_; uint8_t v_hasTrace_4698_; 
v_toCold_4696_ = lean_ctor_get(v___y_4692_, 0);
v_options_4697_ = lean_ctor_get(v_toCold_4696_, 2);
v_hasTrace_4698_ = lean_ctor_get_uint8(v_options_4697_, sizeof(void*)*1);
if (v_hasTrace_4698_ == 0)
{
v___y_4624_ = v___y_4688_;
v___y_4625_ = v___y_4689_;
v___y_4626_ = v___y_4691_;
v___y_4627_ = v___y_4692_;
v___y_4628_ = v___y_4693_;
goto v___jp_4623_;
}
else
{
lean_object* v_inheritedTraceOptions_4699_; uint8_t v___x_4700_; 
v_inheritedTraceOptions_4699_ = lean_ctor_get(v_toCold_4696_, 11);
v___x_4700_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4699_, v_options_4697_, v___x_4199_);
if (v___x_4700_ == 0)
{
v___y_4624_ = v___y_4688_;
v___y_4625_ = v___y_4689_;
v___y_4626_ = v___y_4691_;
v___y_4627_ = v___y_4692_;
v___y_4628_ = v___y_4693_;
goto v___jp_4623_;
}
else
{
lean_object* v___x_4701_; lean_object* v___x_4702_; 
v___x_4701_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_4702_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3970_, v___x_4701_, v___y_4692_, v___y_4693_);
if (lean_obj_tag(v___x_4702_) == 0)
{
lean_dec_ref_known(v___x_4702_, 1);
v___y_4624_ = v___y_4688_;
v___y_4625_ = v___y_4689_;
v___y_4626_ = v___y_4691_;
v___y_4627_ = v___y_4692_;
v___y_4628_ = v___y_4693_;
goto v___jp_4623_;
}
else
{
lean_dec_ref(v___y_4691_);
lean_dec(v___y_4688_);
lean_dec(v_decl_3776_);
return v___x_4702_;
}
}
}
}
else
{
v___y_4654_ = v___y_4692_;
v___y_4655_ = v___x_4695_;
v___y_4656_ = v___y_4688_;
v___y_4657_ = v___y_4693_;
v___y_4658_ = v___y_4691_;
v___y_4659_ = v___y_4690_;
v___y_4660_ = v___y_4689_;
goto v___jp_4653_;
}
}
else
{
v___y_4654_ = v___y_4692_;
v___y_4655_ = v___x_4695_;
v___y_4656_ = v___y_4688_;
v___y_4657_ = v___y_4693_;
v___y_4658_ = v___y_4691_;
v___y_4659_ = v___y_4690_;
v___y_4660_ = v___y_4689_;
goto v___jp_4653_;
}
}
else
{
lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v_a_4705_; uint8_t v___x_4706_; 
lean_dec(v___y_4690_);
v___x_4703_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4704_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4703_, v___y_4692_);
v_a_4705_ = lean_ctor_get(v___x_4704_, 0);
lean_inc(v_a_4705_);
lean_dec_ref(v___x_4704_);
v___x_4706_ = lean_unbox(v_a_4705_);
lean_dec(v_a_4705_);
if (v___x_4706_ == 0)
{
lean_object* v_toCold_4707_; lean_object* v_options_4708_; uint8_t v_hasTrace_4709_; 
v_toCold_4707_ = lean_ctor_get(v___y_4692_, 0);
v_options_4708_ = lean_ctor_get(v_toCold_4707_, 2);
v_hasTrace_4709_ = lean_ctor_get_uint8(v_options_4708_, sizeof(void*)*1);
if (v_hasTrace_4709_ == 0)
{
v___y_4609_ = v___y_4688_;
v___y_4610_ = v___y_4689_;
v___y_4611_ = v___y_4691_;
v_exportedInfo_x3f_4612_ = v___x_4686_;
v___y_4613_ = v___y_4692_;
v___y_4614_ = v___y_4693_;
goto v___jp_4608_;
}
else
{
lean_object* v_inheritedTraceOptions_4710_; uint8_t v___x_4711_; 
v_inheritedTraceOptions_4710_ = lean_ctor_get(v_toCold_4707_, 11);
v___x_4711_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4710_, v_options_4708_, v___x_4199_);
if (v___x_4711_ == 0)
{
v___y_4609_ = v___y_4688_;
v___y_4610_ = v___y_4689_;
v___y_4611_ = v___y_4691_;
v_exportedInfo_x3f_4612_ = v___x_4686_;
v___y_4613_ = v___y_4692_;
v___y_4614_ = v___y_4693_;
goto v___jp_4608_;
}
else
{
lean_object* v___x_4712_; lean_object* v___x_4713_; 
v___x_4712_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_4713_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3970_, v___x_4712_, v___y_4692_, v___y_4693_);
if (lean_obj_tag(v___x_4713_) == 0)
{
lean_dec_ref_known(v___x_4713_, 1);
v___y_4609_ = v___y_4688_;
v___y_4610_ = v___y_4689_;
v___y_4611_ = v___y_4691_;
v_exportedInfo_x3f_4612_ = v___x_4686_;
v___y_4613_ = v___y_4692_;
v___y_4614_ = v___y_4693_;
goto v___jp_4608_;
}
else
{
lean_dec_ref(v___y_4691_);
lean_dec(v___y_4688_);
lean_dec(v_decl_3776_);
return v___x_4713_;
}
}
}
}
else
{
lean_object* v_toCold_4714_; lean_object* v_options_4715_; uint8_t v_hasTrace_4716_; 
v_toCold_4714_ = lean_ctor_get(v___y_4692_, 0);
v_options_4715_ = lean_ctor_get(v_toCold_4714_, 2);
v_hasTrace_4716_ = lean_ctor_get_uint8(v_options_4715_, sizeof(void*)*1);
if (v_hasTrace_4716_ == 0)
{
v___y_4631_ = v___y_4688_;
v___y_4632_ = v___y_4689_;
v___y_4633_ = v___y_4691_;
v___y_4634_ = v___y_4692_;
v___y_4635_ = v___y_4693_;
goto v___jp_4630_;
}
else
{
lean_object* v_inheritedTraceOptions_4717_; uint8_t v___x_4718_; 
v_inheritedTraceOptions_4717_ = lean_ctor_get(v_toCold_4714_, 11);
v___x_4718_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4717_, v_options_4715_, v___x_4199_);
if (v___x_4718_ == 0)
{
v___y_4631_ = v___y_4688_;
v___y_4632_ = v___y_4689_;
v___y_4633_ = v___y_4691_;
v___y_4634_ = v___y_4692_;
v___y_4635_ = v___y_4693_;
goto v___jp_4630_;
}
else
{
lean_object* v___x_4719_; lean_object* v___x_4720_; 
v___x_4719_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_4720_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3970_, v___x_4719_, v___y_4692_, v___y_4693_);
if (lean_obj_tag(v___x_4720_) == 0)
{
lean_dec_ref_known(v___x_4720_, 1);
v___y_4631_ = v___y_4688_;
v___y_4632_ = v___y_4689_;
v___y_4633_ = v___y_4691_;
v___y_4634_ = v___y_4692_;
v___y_4635_ = v___y_4693_;
goto v___jp_4630_;
}
else
{
lean_dec_ref(v___y_4691_);
lean_dec(v___y_4688_);
lean_dec(v_decl_3776_);
return v___x_4720_;
}
}
}
}
}
}
v___jp_4721_:
{
lean_object* v___x_4728_; lean_object* v_env_4729_; uint8_t v___x_4730_; 
v___x_4728_ = lean_st_ref_get(v___y_4727_);
v_env_4729_ = lean_ctor_get(v___x_4728_, 0);
lean_inc_ref(v_env_4729_);
lean_dec(v___x_4728_);
v___x_4730_ = l_Lean_Environment_containsOnBranch(v_env_4729_, v_fst_4722_);
lean_dec_ref(v_env_4729_);
if (v___x_4730_ == 0)
{
v___y_4688_ = v_fst_4722_;
v___y_4689_ = v_snd_4724_;
v___y_4690_ = v_exportedInfo_x3f_4725_;
v___y_4691_ = v_fst_4723_;
v___y_4692_ = v___y_4726_;
v___y_4693_ = v___y_4727_;
goto v___jp_4687_;
}
else
{
lean_object* v___x_4731_; lean_object* v_env_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; 
lean_dec(v_exportedInfo_x3f_4725_);
lean_dec_ref(v_fst_4723_);
lean_dec(v_decl_3776_);
v___x_4731_ = lean_st_ref_get(v___y_4727_);
v_env_4732_ = lean_ctor_get(v___x_4731_, 0);
lean_inc_ref(v_env_4732_);
lean_dec(v___x_4731_);
v___x_4733_ = lean_elab_environment_to_kernel_env(v_env_4732_);
v___x_4734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4734_, 0, v___x_4733_);
lean_ctor_set(v___x_4734_, 1, v_fst_4722_);
v___x_4735_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4734_, v___y_4726_, v___y_4727_);
return v___x_4735_;
}
}
v___jp_4736_:
{
lean_object* v_toConstantVal_4741_; lean_object* v_name_4742_; lean_object* v___x_4743_; uint8_t v___x_4744_; 
v_toConstantVal_4741_ = lean_ctor_get(v___y_4737_, 0);
v_name_4742_ = lean_ctor_get(v_toConstantVal_4741_, 0);
lean_inc(v_name_4742_);
v___x_4743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4743_, 0, v___y_4737_);
v___x_4744_ = 0;
v_fst_4722_ = v_name_4742_;
v_fst_4723_ = v___x_4743_;
v_snd_4724_ = v___x_4744_;
v_exportedInfo_x3f_4725_ = v_exportedInfo_x3f_4738_;
v___y_4726_ = v___y_4739_;
v___y_4727_ = v___y_4740_;
goto v___jp_4721_;
}
v___jp_4745_:
{
lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; 
v___x_4751_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4751_, 0, v___y_4749_);
lean_ctor_set_uint8(v___x_4751_, sizeof(void*)*1, v___y_4750_);
v___x_4752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4752_, 0, v___x_4751_);
v___x_4753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4753_, 0, v___x_4752_);
v___y_4737_ = v___y_4746_;
v_exportedInfo_x3f_4738_ = v___x_4753_;
v___y_4739_ = v___y_4748_;
v___y_4740_ = v___y_4747_;
goto v___jp_4736_;
}
v___jp_4754_:
{
uint8_t v___x_4761_; uint8_t v___x_4762_; 
v___x_4761_ = 1;
v___x_4762_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4757_, v___x_4761_);
if (v___x_4762_ == 0)
{
v___y_4746_ = v___y_4755_;
v___y_4747_ = v___y_4760_;
v___y_4748_ = v___y_4759_;
v___y_4749_ = v_toConstantVal_4756_;
v___y_4750_ = v___y_4758_;
goto v___jp_4745_;
}
else
{
v___y_4746_ = v___y_4755_;
v___y_4747_ = v___y_4760_;
v___y_4748_ = v___y_4759_;
v___y_4749_ = v_toConstantVal_4756_;
v___y_4750_ = v___x_4505_;
goto v___jp_4745_;
}
}
v___jp_4763_:
{
lean_object* v_toConstantVal_4768_; uint8_t v_safety_4769_; 
v_toConstantVal_4768_ = lean_ctor_get(v___y_4764_, 0);
lean_inc_ref(v_toConstantVal_4768_);
v_safety_4769_ = lean_ctor_get_uint8(v___y_4764_, sizeof(void*)*4);
v___y_4755_ = v___y_4764_;
v_toConstantVal_4756_ = v_toConstantVal_4768_;
v_safety_4757_ = v_safety_4769_;
v___y_4758_ = v___y_4765_;
v___y_4759_ = v___y_4766_;
v___y_4760_ = v___y_4767_;
goto v___jp_4754_;
}
v___jp_4770_:
{
lean_object* v_toCold_4775_; lean_object* v_options_4776_; uint8_t v_hasTrace_4777_; 
v_toCold_4775_ = lean_ctor_get(v___y_4773_, 0);
v_options_4776_ = lean_ctor_get(v_toCold_4775_, 2);
v_hasTrace_4777_ = lean_ctor_get_uint8(v_options_4776_, sizeof(void*)*1);
if (v_hasTrace_4777_ == 0)
{
v___y_4764_ = v___y_4771_;
v___y_4765_ = v___y_4774_;
v___y_4766_ = v___y_4773_;
v___y_4767_ = v___y_4772_;
goto v___jp_4763_;
}
else
{
lean_object* v_inheritedTraceOptions_4778_; uint8_t v___x_4779_; 
v_inheritedTraceOptions_4778_ = lean_ctor_get(v_toCold_4775_, 11);
v___x_4779_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4778_, v_options_4776_, v___x_4199_);
if (v___x_4779_ == 0)
{
v___y_4764_ = v___y_4771_;
v___y_4765_ = v___y_4774_;
v___y_4766_ = v___y_4773_;
v___y_4767_ = v___y_4772_;
goto v___jp_4763_;
}
else
{
lean_object* v_toConstantVal_4780_; uint8_t v_safety_4781_; lean_object* v_name_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; 
v_toConstantVal_4780_ = lean_ctor_get(v___y_4771_, 0);
lean_inc_ref(v_toConstantVal_4780_);
v_safety_4781_ = lean_ctor_get_uint8(v___y_4771_, sizeof(void*)*4);
v_name_4782_ = lean_ctor_get(v_toConstantVal_4780_, 0);
v___x_4783_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_4782_);
v___x_4784_ = l_Lean_MessageData_ofName(v_name_4782_);
v___x_4785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4785_, 0, v___x_4783_);
lean_ctor_set(v___x_4785_, 1, v___x_4784_);
v___x_4786_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4787_, 0, v___x_4785_);
lean_ctor_set(v___x_4787_, 1, v___x_4786_);
v___x_4788_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3970_, v___x_4787_, v___y_4773_, v___y_4772_);
if (lean_obj_tag(v___x_4788_) == 0)
{
lean_dec_ref_known(v___x_4788_, 1);
v___y_4755_ = v___y_4771_;
v_toConstantVal_4756_ = v_toConstantVal_4780_;
v_safety_4757_ = v_safety_4781_;
v___y_4758_ = v___y_4774_;
v___y_4759_ = v___y_4773_;
v___y_4760_ = v___y_4772_;
goto v___jp_4754_;
}
else
{
lean_dec_ref(v_toConstantVal_4780_);
lean_dec_ref(v___y_4771_);
lean_dec(v_decl_3776_);
return v___x_4788_;
}
}
}
}
v___jp_4789_:
{
lean_object* v___x_4795_; uint8_t v_isModule_4796_; 
v___x_4795_ = l_Lean_Environment_header(v___y_4793_);
lean_dec_ref(v___y_4793_);
v_isModule_4796_ = lean_ctor_get_uint8(v___x_4795_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4795_);
if (v_isModule_4796_ == 0)
{
lean_dec_ref(v___y_4792_);
v___y_4737_ = v___y_4790_;
v_exportedInfo_x3f_4738_ = v___x_4686_;
v___y_4739_ = v___y_4794_;
v___y_4740_ = v___y_4791_;
goto v___jp_4736_;
}
else
{
uint8_t v_isExporting_4797_; 
v_isExporting_4797_ = lean_ctor_get_uint8(v___y_4792_, sizeof(void*)*13);
lean_dec_ref(v___y_4792_);
if (v_isExporting_4797_ == 0)
{
v___y_4771_ = v___y_4790_;
v___y_4772_ = v___y_4791_;
v___y_4773_ = v___y_4794_;
v___y_4774_ = v_isModule_4796_;
goto v___jp_4770_;
}
else
{
if (v___x_4505_ == 0)
{
v___y_4737_ = v___y_4790_;
v_exportedInfo_x3f_4738_ = v___x_4686_;
v___y_4739_ = v___y_4794_;
v___y_4740_ = v___y_4791_;
goto v___jp_4736_;
}
else
{
v___y_4771_ = v___y_4790_;
v___y_4772_ = v___y_4791_;
v___y_4773_ = v___y_4794_;
v___y_4774_ = v___x_4505_;
goto v___jp_4770_;
}
}
}
}
v___jp_4798_:
{
lean_object* v___x_4802_; lean_object* v_env_4803_; lean_object* v___x_4804_; 
v___x_4802_ = lean_st_ref_get(v___y_4801_);
v_env_4803_ = lean_ctor_get(v___x_4802_, 0);
lean_inc_ref(v_env_4803_);
lean_dec(v___x_4802_);
v___x_4804_ = lean_st_ref_get(v___y_4801_);
if (v_forceExpose_3777_ == 0)
{
lean_object* v_env_4805_; 
v_env_4805_ = lean_ctor_get(v___x_4804_, 0);
lean_inc_ref(v_env_4805_);
lean_dec(v___x_4804_);
v___y_4790_ = v_defn_4799_;
v___y_4791_ = v___y_4801_;
v___y_4792_ = v_env_4805_;
v___y_4793_ = v_env_4803_;
v___y_4794_ = v___y_4800_;
goto v___jp_4789_;
}
else
{
if (v___x_4505_ == 0)
{
lean_dec(v___x_4804_);
lean_dec_ref(v_env_4803_);
v___y_4737_ = v_defn_4799_;
v_exportedInfo_x3f_4738_ = v___x_4686_;
v___y_4739_ = v___y_4800_;
v___y_4740_ = v___y_4801_;
goto v___jp_4736_;
}
else
{
lean_object* v_env_4806_; 
v_env_4806_ = lean_ctor_get(v___x_4804_, 0);
lean_inc_ref(v_env_4806_);
lean_dec(v___x_4804_);
v___y_4790_ = v_defn_4799_;
v___y_4791_ = v___y_4801_;
v___y_4792_ = v_env_4806_;
v___y_4793_ = v_env_4803_;
v___y_4794_ = v___y_4800_;
goto v___jp_4789_;
}
}
}
}
}
}
else
{
goto v___jp_4348_;
}
v___jp_4506_:
{
lean_object* v___x_4518_; 
lean_inc_ref(v___y_4509_);
v___x_4518_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_4512_, v___y_4509_, v___y_4514_, v___y_4517_);
if (lean_obj_tag(v___x_4518_) == 0)
{
lean_object* v___x_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4565_; 
lean_dec_ref_known(v___x_4518_, 1);
lean_dec(v___y_4507_);
lean_inc_ref(v___y_4513_);
v___x_4519_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4513_, v___y_4515_);
v_isSharedCheck_4565_ = !lean_is_exclusive(v___x_4519_);
if (v_isSharedCheck_4565_ == 0)
{
lean_object* v_unused_4566_; 
v_unused_4566_ = lean_ctor_get(v___x_4519_, 0);
lean_dec(v_unused_4566_);
v___x_4521_ = v___x_4519_;
v_isShared_4522_ = v_isSharedCheck_4565_;
goto v_resetjp_4520_;
}
else
{
lean_dec(v___x_4519_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4565_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v___x_4523_; lean_object* v___x_4524_; uint8_t v___x_4525_; 
v___x_4523_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4510_);
v___x_4524_ = l_Lean_Elab_async;
v___x_4525_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_4523_, v___x_4524_);
lean_dec_ref(v___x_4523_);
if (v___x_4525_ == 0)
{
lean_object* v___x_4526_; lean_object* v_r_4527_; 
lean_del_object(v___x_4521_);
lean_dec_ref(v___y_4516_);
lean_dec_ref(v___y_4511_);
v___x_4526_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4509_, v___y_4515_);
lean_dec_ref(v___x_4526_);
v_r_4527_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3776_, v___y_4510_, v___y_4515_);
if (lean_obj_tag(v_r_4527_) == 0)
{
lean_object* v_a_4528_; lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4537_; 
v_a_4528_ = lean_ctor_get(v_r_4527_, 0);
v_isSharedCheck_4537_ = !lean_is_exclusive(v_r_4527_);
if (v_isSharedCheck_4537_ == 0)
{
v___x_4530_ = v_r_4527_;
v_isShared_4531_ = v_isSharedCheck_4537_;
goto v_resetjp_4529_;
}
else
{
lean_inc(v_a_4528_);
lean_dec(v_r_4527_);
v___x_4530_ = lean_box(0);
v_isShared_4531_ = v_isSharedCheck_4537_;
goto v_resetjp_4529_;
}
v_resetjp_4529_:
{
lean_object* v___x_4533_; 
lean_inc(v_a_4528_);
if (v_isShared_4531_ == 0)
{
lean_ctor_set_tag(v___x_4530_, 1);
v___x_4533_ = v___x_4530_;
goto v_reusejp_4532_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v_a_4528_);
v___x_4533_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4532_;
}
v_reusejp_4532_:
{
lean_object* v___x_4534_; 
v___x_4534_ = lean_apply_2(v___y_4508_, v___x_4533_, lean_box(0));
if (lean_obj_tag(v___x_4534_) == 0)
{
lean_dec_ref_known(v___x_4534_, 1);
v___y_3782_ = v___y_4513_;
v___y_3783_ = v___y_4515_;
v_a_3784_ = v_a_4528_;
goto v___jp_3781_;
}
else
{
lean_object* v_a_4535_; 
lean_dec(v_a_4528_);
v_a_4535_ = lean_ctor_get(v___x_4534_, 0);
lean_inc(v_a_4535_);
lean_dec_ref_known(v___x_4534_, 1);
v___y_3795_ = v___y_4513_;
v___y_3796_ = v___y_4515_;
v_a_3797_ = v_a_4535_;
goto v___jp_3794_;
}
}
}
}
else
{
lean_object* v_a_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; 
v_a_4538_ = lean_ctor_get(v_r_4527_, 0);
lean_inc(v_a_4538_);
lean_dec_ref_known(v_r_4527_, 1);
v___x_4539_ = lean_box(0);
v___x_4540_ = lean_apply_2(v___y_4508_, v___x_4539_, lean_box(0));
if (lean_obj_tag(v___x_4540_) == 0)
{
lean_dec_ref_known(v___x_4540_, 1);
v___y_3795_ = v___y_4513_;
v___y_3796_ = v___y_4515_;
v_a_3797_ = v_a_4538_;
goto v___jp_3794_;
}
else
{
lean_object* v_a_4541_; 
lean_dec(v_a_4538_);
v_a_4541_ = lean_ctor_get(v___x_4540_, 0);
lean_inc(v_a_4541_);
lean_dec_ref_known(v___x_4540_, 1);
v___y_3795_ = v___y_4513_;
v___y_3796_ = v___y_4515_;
v_a_3797_ = v_a_4541_;
goto v___jp_3794_;
}
}
}
else
{
lean_object* v___x_4542_; lean_object* v___x_4544_; 
lean_dec_ref(v___y_4513_);
lean_dec_ref(v___y_4509_);
lean_dec_ref(v___y_4508_);
lean_dec(v_decl_3776_);
v___x_4542_ = l_IO_CancelToken_new();
if (v_isShared_4522_ == 0)
{
lean_ctor_set_tag(v___x_4521_, 1);
lean_ctor_set(v___x_4521_, 0, v___x_4542_);
v___x_4544_ = v___x_4521_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4564_; 
v_reuseFailAlloc_4564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4564_, 0, v___x_4542_);
v___x_4544_ = v_reuseFailAlloc_4564_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; 
v___x_4545_ = lean_unsigned_to_nat(0u);
v___x_4546_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_4547_ = l_Lean_Name_toString(v___x_4546_, v_hasTrace_3836_);
lean_inc_ref(v___x_4544_);
v___x_4548_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_4511_, v___x_4544_, v___x_4547_, v___y_4510_, v___y_4515_);
if (lean_obj_tag(v___x_4548_) == 0)
{
lean_object* v_a_4549_; lean_object* v_checked_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; 
v_a_4549_ = lean_ctor_get(v___x_4548_, 0);
lean_inc(v_a_4549_);
lean_dec_ref_known(v___x_4548_, 1);
v_checked_4550_ = lean_ctor_get(v___y_4516_, 2);
lean_inc_ref(v_checked_4550_);
lean_dec_ref(v___y_4516_);
v___x_4551_ = lean_io_map_task(v_a_4549_, v_checked_4550_, v___x_4545_, v___x_4505_);
v___x_4552_ = lean_box(0);
v___x_4553_ = lean_box(2);
v___x_4554_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4554_, 0, v___x_4552_);
lean_ctor_set(v___x_4554_, 1, v___x_4553_);
lean_ctor_set(v___x_4554_, 2, v___x_4544_);
lean_ctor_set(v___x_4554_, 3, v___x_4551_);
v___x_4555_ = l_Lean_Core_logSnapshotTask___redArg(v___x_4554_, v___y_4515_);
return v___x_4555_;
}
else
{
lean_object* v_a_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4563_; 
lean_dec_ref(v___x_4544_);
lean_dec_ref(v___y_4516_);
v_a_4556_ = lean_ctor_get(v___x_4548_, 0);
v_isSharedCheck_4563_ = !lean_is_exclusive(v___x_4548_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4558_ = v___x_4548_;
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_a_4556_);
lean_dec(v___x_4548_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v___x_4561_; 
if (v_isShared_4559_ == 0)
{
v___x_4561_ = v___x_4558_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v_a_4556_);
v___x_4561_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
return v___x_4561_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4567_; lean_object* v___x_4569_; uint8_t v_isShared_4570_; uint8_t v_isSharedCheck_4578_; 
lean_dec_ref(v___y_4516_);
lean_dec_ref(v___y_4513_);
lean_dec_ref(v___y_4511_);
lean_dec_ref(v___y_4509_);
lean_dec_ref(v___y_4508_);
lean_dec(v_decl_3776_);
v_a_4567_ = lean_ctor_get(v___x_4518_, 0);
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4518_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4569_ = v___x_4518_;
v_isShared_4570_ = v_isSharedCheck_4578_;
goto v_resetjp_4568_;
}
else
{
lean_inc(v_a_4567_);
lean_dec(v___x_4518_);
v___x_4569_ = lean_box(0);
v_isShared_4570_ = v_isSharedCheck_4578_;
goto v_resetjp_4568_;
}
v_resetjp_4568_:
{
lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4576_; 
v___x_4571_ = lean_io_error_to_string(v_a_4567_);
v___x_4572_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4572_, 0, v___x_4571_);
v___x_4573_ = l_Lean_MessageData_ofFormat(v___x_4572_);
v___x_4574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4574_, 0, v___y_4507_);
lean_ctor_set(v___x_4574_, 1, v___x_4573_);
if (v_isShared_4570_ == 0)
{
lean_ctor_set(v___x_4569_, 0, v___x_4574_);
v___x_4576_ = v___x_4569_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v___x_4574_);
v___x_4576_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
return v___x_4576_;
}
}
}
}
v___jp_4579_:
{
lean_object* v_ref_4588_; lean_object* v___x_4589_; 
v_ref_4588_ = lean_ctor_get(v___y_4580_, 2);
lean_inc_ref(v___y_4586_);
v___x_4589_ = l_Lean_Environment_addConstAsync(v___y_4586_, v___y_4582_, v___y_4585_, v___y_4587_, v___x_4505_, v_hasTrace_3836_);
if (lean_obj_tag(v___x_4589_) == 0)
{
lean_object* v_a_4590_; lean_object* v_mainEnv_4591_; lean_object* v_asyncEnv_4592_; lean_object* v___f_4593_; lean_object* v___f_4594_; lean_object* v___x_4595_; 
v_a_4590_ = lean_ctor_get(v___x_4589_, 0);
lean_inc_n(v_a_4590_, 3);
lean_dec_ref_known(v___x_4589_, 1);
v_mainEnv_4591_ = lean_ctor_get(v_a_4590_, 0);
lean_inc_ref(v_mainEnv_4591_);
v_asyncEnv_4592_ = lean_ctor_get(v_a_4590_, 1);
lean_inc_ref_n(v_asyncEnv_4592_, 2);
lean_inc(v_ref_4588_);
lean_inc(v___y_4584_);
v___f_4593_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4593_, 0, v___y_4584_);
lean_closure_set(v___f_4593_, 1, v_a_4590_);
lean_closure_set(v___f_4593_, 2, v_ref_4588_);
lean_inc(v_decl_3776_);
v___f_4594_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4594_, 0, v_a_4590_);
lean_closure_set(v___f_4594_, 1, v_asyncEnv_4592_);
lean_closure_set(v___f_4594_, 2, v_decl_3776_);
v___x_4595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4595_, 0, v___y_4581_);
if (lean_obj_tag(v___y_4583_) == 0)
{
lean_inc_ref(v___x_4595_);
lean_inc(v_ref_4588_);
v___y_4507_ = v_ref_4588_;
v___y_4508_ = v___f_4593_;
v___y_4509_ = v_asyncEnv_4592_;
v___y_4510_ = v___y_4580_;
v___y_4511_ = v___f_4594_;
v___y_4512_ = v_a_4590_;
v___y_4513_ = v_mainEnv_4591_;
v___y_4514_ = v___x_4595_;
v___y_4515_ = v___y_4584_;
v___y_4516_ = v___y_4586_;
v___y_4517_ = v___x_4595_;
goto v___jp_4506_;
}
else
{
lean_inc(v_ref_4588_);
v___y_4507_ = v_ref_4588_;
v___y_4508_ = v___f_4593_;
v___y_4509_ = v_asyncEnv_4592_;
v___y_4510_ = v___y_4580_;
v___y_4511_ = v___f_4594_;
v___y_4512_ = v_a_4590_;
v___y_4513_ = v_mainEnv_4591_;
v___y_4514_ = v___x_4595_;
v___y_4515_ = v___y_4584_;
v___y_4516_ = v___y_4586_;
v___y_4517_ = v___y_4583_;
goto v___jp_4506_;
}
}
else
{
lean_object* v_a_4596_; lean_object* v___x_4598_; uint8_t v_isShared_4599_; uint8_t v_isSharedCheck_4607_; 
lean_dec_ref(v___y_4586_);
lean_dec(v___y_4583_);
lean_dec_ref(v___y_4581_);
lean_dec(v_decl_3776_);
v_a_4596_ = lean_ctor_get(v___x_4589_, 0);
v_isSharedCheck_4607_ = !lean_is_exclusive(v___x_4589_);
if (v_isSharedCheck_4607_ == 0)
{
v___x_4598_ = v___x_4589_;
v_isShared_4599_ = v_isSharedCheck_4607_;
goto v_resetjp_4597_;
}
else
{
lean_inc(v_a_4596_);
lean_dec(v___x_4589_);
v___x_4598_ = lean_box(0);
v_isShared_4599_ = v_isSharedCheck_4607_;
goto v_resetjp_4597_;
}
v_resetjp_4597_:
{
lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4605_; 
v___x_4600_ = lean_io_error_to_string(v_a_4596_);
v___x_4601_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4601_, 0, v___x_4600_);
v___x_4602_ = l_Lean_MessageData_ofFormat(v___x_4601_);
lean_inc(v_ref_4588_);
v___x_4603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4603_, 0, v_ref_4588_);
lean_ctor_set(v___x_4603_, 1, v___x_4602_);
if (v_isShared_4599_ == 0)
{
lean_ctor_set(v___x_4598_, 0, v___x_4603_);
v___x_4605_ = v___x_4598_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v___x_4603_);
v___x_4605_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
return v___x_4605_;
}
}
}
}
v___jp_4608_:
{
lean_object* v___x_4615_; 
v___x_4615_ = lean_st_ref_get(v___y_4614_);
if (lean_obj_tag(v_exportedInfo_x3f_4612_) == 0)
{
lean_object* v_env_4616_; lean_object* v___x_4617_; 
v_env_4616_ = lean_ctor_get(v___x_4615_, 0);
lean_inc_ref(v_env_4616_);
lean_dec(v___x_4615_);
v___x_4617_ = lean_box(0);
v___y_4580_ = v___y_4613_;
v___y_4581_ = v___y_4611_;
v___y_4582_ = v___y_4609_;
v___y_4583_ = v_exportedInfo_x3f_4612_;
v___y_4584_ = v___y_4614_;
v___y_4585_ = v___y_4610_;
v___y_4586_ = v_env_4616_;
v___y_4587_ = v___x_4617_;
goto v___jp_4579_;
}
else
{
lean_object* v_env_4618_; lean_object* v_val_4619_; uint8_t v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; 
v_env_4618_ = lean_ctor_get(v___x_4615_, 0);
lean_inc_ref(v_env_4618_);
lean_dec(v___x_4615_);
v_val_4619_ = lean_ctor_get(v_exportedInfo_x3f_4612_, 0);
v___x_4620_ = l_Lean_ConstantKind_ofConstantInfo(v_val_4619_);
v___x_4621_ = lean_box(v___x_4620_);
v___x_4622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4622_, 0, v___x_4621_);
v___y_4580_ = v___y_4613_;
v___y_4581_ = v___y_4611_;
v___y_4582_ = v___y_4609_;
v___y_4583_ = v_exportedInfo_x3f_4612_;
v___y_4584_ = v___y_4614_;
v___y_4585_ = v___y_4610_;
v___y_4586_ = v_env_4618_;
v___y_4587_ = v___x_4622_;
goto v___jp_4579_;
}
}
v___jp_4623_:
{
lean_object* v___x_4629_; 
lean_inc_ref(v___y_4626_);
v___x_4629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4629_, 0, v___y_4626_);
v___y_4609_ = v___y_4624_;
v___y_4610_ = v___y_4625_;
v___y_4611_ = v___y_4626_;
v_exportedInfo_x3f_4612_ = v___x_4629_;
v___y_4613_ = v___y_4627_;
v___y_4614_ = v___y_4628_;
goto v___jp_4608_;
}
v___jp_4630_:
{
lean_object* v___x_4636_; 
lean_inc_ref(v___y_4633_);
v___x_4636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4636_, 0, v___y_4633_);
v___y_4609_ = v___y_4631_;
v___y_4610_ = v___y_4632_;
v___y_4611_ = v___y_4633_;
v_exportedInfo_x3f_4612_ = v___x_4636_;
v___y_4613_ = v___y_4634_;
v___y_4614_ = v___y_4635_;
goto v___jp_4608_;
}
}
else
{
goto v___jp_4348_;
}
v___jp_4201_:
{
lean_object* v___x_4205_; double v___x_4206_; double v___x_4207_; double v___x_4208_; double v___x_4209_; double v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
v___x_4205_ = lean_io_mono_nanos_now();
v___x_4206_ = lean_float_of_nat(v___y_4202_);
v___x_4207_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_4208_ = lean_float_div(v___x_4206_, v___x_4207_);
v___x_4209_ = lean_float_of_nat(v___x_4205_);
v___x_4210_ = lean_float_div(v___x_4209_, v___x_4207_);
v___x_4211_ = lean_box_float(v___x_4208_);
v___x_4212_ = lean_box_float(v___x_4210_);
v___x_4213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4213_, 0, v___x_4211_);
lean_ctor_set(v___x_4213_, 1, v___x_4212_);
v___x_4214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4214_, 0, v_a_4204_);
lean_ctor_set(v___x_4214_, 1, v___x_4213_);
v___x_4215_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3970_, v_hasTrace_3836_, v___x_4198_, v_options_3834_, v___x_4200_, v___y_4203_, v___f_4197_, v___x_4214_, v_a_3778_, v_a_3779_);
return v___x_4215_;
}
v___jp_4216_:
{
if (lean_obj_tag(v___y_4219_) == 0)
{
lean_object* v_a_4220_; lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4227_; 
v_a_4220_ = lean_ctor_get(v___y_4219_, 0);
v_isSharedCheck_4227_ = !lean_is_exclusive(v___y_4219_);
if (v_isSharedCheck_4227_ == 0)
{
v___x_4222_ = v___y_4219_;
v_isShared_4223_ = v_isSharedCheck_4227_;
goto v_resetjp_4221_;
}
else
{
lean_inc(v_a_4220_);
lean_dec(v___y_4219_);
v___x_4222_ = lean_box(0);
v_isShared_4223_ = v_isSharedCheck_4227_;
goto v_resetjp_4221_;
}
v_resetjp_4221_:
{
lean_object* v___x_4225_; 
if (v_isShared_4223_ == 0)
{
lean_ctor_set_tag(v___x_4222_, 1);
v___x_4225_ = v___x_4222_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_a_4220_);
v___x_4225_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
v___y_4202_ = v___y_4217_;
v___y_4203_ = v___y_4218_;
v_a_4204_ = v___x_4225_;
goto v___jp_4201_;
}
}
}
else
{
lean_object* v_a_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4235_; 
v_a_4228_ = lean_ctor_get(v___y_4219_, 0);
v_isSharedCheck_4235_ = !lean_is_exclusive(v___y_4219_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4230_ = v___y_4219_;
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_a_4228_);
lean_dec(v___y_4219_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___x_4233_; 
if (v_isShared_4231_ == 0)
{
lean_ctor_set_tag(v___x_4230_, 0);
v___x_4233_ = v___x_4230_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_a_4228_);
v___x_4233_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
v___y_4202_ = v___y_4217_;
v___y_4203_ = v___y_4218_;
v_a_4204_ = v___x_4233_;
goto v___jp_4201_;
}
}
}
}
v___jp_4236_:
{
lean_object* v___x_4241_; lean_object* v___x_4242_; 
v___x_4241_ = lean_box(0);
lean_inc(v_a_3779_);
lean_inc_ref(v_a_3778_);
v___x_4242_ = lean_apply_5(v___y_4240_, v___x_4241_, v___y_4239_, v_a_3778_, v_a_3779_, lean_box(0));
v___y_4217_ = v___y_4237_;
v___y_4218_ = v___y_4238_;
v___y_4219_ = v___x_4242_;
goto v___jp_4216_;
}
v___jp_4243_:
{
lean_object* v___x_4251_; uint8_t v_isModule_4252_; 
v___x_4251_ = l_Lean_Environment_header(v___y_4244_);
lean_dec_ref(v___y_4244_);
v_isModule_4252_ = lean_ctor_get_uint8(v___x_4251_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4251_);
if (v_isModule_4252_ == 0)
{
lean_dec_ref(v___y_4250_);
lean_dec_ref(v___y_4247_);
v___y_4237_ = v___y_4245_;
v___y_4238_ = v___y_4246_;
v___y_4239_ = v___y_4248_;
v___y_4240_ = v___y_4249_;
goto v___jp_4236_;
}
else
{
lean_dec_ref(v___y_4249_);
lean_dec(v___y_4248_);
if (v___x_4200_ == 0)
{
lean_object* v___x_4253_; lean_object* v___x_4254_; 
lean_dec_ref(v___y_4247_);
v___x_4253_ = lean_box(0);
lean_inc(v_a_3779_);
lean_inc_ref(v_a_3778_);
v___x_4254_ = lean_apply_4(v___y_4250_, v___x_4253_, v_a_3778_, v_a_3779_, lean_box(0));
v___y_4217_ = v___y_4245_;
v___y_4218_ = v___y_4246_;
v___y_4219_ = v___x_4254_;
goto v___jp_4216_;
}
else
{
lean_object* v_toConstantVal_4255_; lean_object* v_name_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; 
v_toConstantVal_4255_ = lean_ctor_get(v___y_4247_, 0);
lean_inc_ref(v_toConstantVal_4255_);
lean_dec_ref(v___y_4247_);
v_name_4256_ = lean_ctor_get(v_toConstantVal_4255_, 0);
lean_inc(v_name_4256_);
lean_dec_ref(v_toConstantVal_4255_);
v___x_4257_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
v___x_4258_ = l_Lean_MessageData_ofName(v_name_4256_);
v___x_4259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4259_, 0, v___x_4257_);
lean_ctor_set(v___x_4259_, 1, v___x_4258_);
v___x_4260_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4261_, 0, v___x_4259_);
lean_ctor_set(v___x_4261_, 1, v___x_4260_);
v___x_4262_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3970_, v___x_4261_, v_a_3778_, v_a_3779_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v_a_4263_; lean_object* v___x_4264_; 
v_a_4263_ = lean_ctor_get(v___x_4262_, 0);
lean_inc(v_a_4263_);
lean_dec_ref_known(v___x_4262_, 1);
lean_inc(v_a_3779_);
lean_inc_ref(v_a_3778_);
v___x_4264_ = lean_apply_4(v___y_4250_, v_a_4263_, v_a_3778_, v_a_3779_, lean_box(0));
v___y_4217_ = v___y_4245_;
v___y_4218_ = v___y_4246_;
v___y_4219_ = v___x_4264_;
goto v___jp_4216_;
}
else
{
lean_dec_ref(v___y_4250_);
v___y_4217_ = v___y_4245_;
v___y_4218_ = v___y_4246_;
v___y_4219_ = v___x_4262_;
goto v___jp_4216_;
}
}
}
}
v___jp_4265_:
{
if (v___x_4200_ == 0)
{
lean_object* v___x_4270_; lean_object* v___x_4271_; 
lean_dec_ref(v___y_4267_);
v___x_4270_ = lean_box(0);
lean_inc(v_a_3779_);
lean_inc_ref(v_a_3778_);
v___x_4271_ = lean_apply_4(v___y_4269_, v___x_4270_, v_a_3778_, v_a_3779_, lean_box(0));
v___y_4217_ = v___y_4266_;
v___y_4218_ = v___y_4268_;
v___y_4219_ = v___x_4271_;
goto v___jp_4216_;
}
else
{
lean_object* v_toConstantVal_4272_; lean_object* v_name_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; 
v_toConstantVal_4272_ = lean_ctor_get(v___y_4267_, 0);
lean_inc_ref(v_toConstantVal_4272_);
lean_dec_ref(v___y_4267_);
v_name_4273_ = lean_ctor_get(v_toConstantVal_4272_, 0);
lean_inc(v_name_4273_);
lean_dec_ref(v_toConstantVal_4272_);
v___x_4274_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
v___x_4275_ = l_Lean_MessageData_ofName(v_name_4273_);
v___x_4276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4276_, 0, v___x_4274_);
lean_ctor_set(v___x_4276_, 1, v___x_4275_);
v___x_4277_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4278_, 0, v___x_4276_);
lean_ctor_set(v___x_4278_, 1, v___x_4277_);
v___x_4279_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3970_, v___x_4278_, v_a_3778_, v_a_3779_);
if (lean_obj_tag(v___x_4279_) == 0)
{
lean_object* v_a_4280_; lean_object* v___x_4281_; 
v_a_4280_ = lean_ctor_get(v___x_4279_, 0);
lean_inc(v_a_4280_);
lean_dec_ref_known(v___x_4279_, 1);
lean_inc(v_a_3779_);
lean_inc_ref(v_a_3778_);
v___x_4281_ = lean_apply_4(v___y_4269_, v_a_4280_, v_a_3778_, v_a_3779_, lean_box(0));
v___y_4217_ = v___y_4266_;
v___y_4218_ = v___y_4268_;
v___y_4219_ = v___x_4281_;
goto v___jp_4216_;
}
else
{
lean_dec_ref(v___y_4269_);
v___y_4217_ = v___y_4266_;
v___y_4218_ = v___y_4268_;
v___y_4219_ = v___x_4279_;
goto v___jp_4216_;
}
}
}
v___jp_4282_:
{
lean_object* v___x_4287_; lean_object* v___x_4288_; 
v___x_4287_ = lean_box(0);
lean_inc(v_a_3779_);
lean_inc_ref(v_a_3778_);
v___x_4288_ = lean_apply_5(v___y_4286_, v___x_4287_, v___y_4285_, v_a_3778_, v_a_3779_, lean_box(0));
v___y_4217_ = v___y_4283_;
v___y_4218_ = v___y_4284_;
v___y_4219_ = v___x_4288_;
goto v___jp_4216_;
}
v___jp_4289_:
{
lean_object* v___x_4299_; uint8_t v_isModule_4300_; 
v___x_4299_ = l_Lean_Environment_header(v___y_4296_);
lean_dec_ref(v___y_4296_);
v_isModule_4300_ = lean_ctor_get_uint8(v___x_4299_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4299_);
if (v_isModule_4300_ == 0)
{
lean_dec_ref(v___y_4297_);
lean_dec_ref(v___y_4293_);
lean_dec_ref(v___y_4291_);
v___y_4283_ = v___y_4290_;
v___y_4284_ = v___y_4292_;
v___y_4285_ = v___y_4295_;
v___y_4286_ = v___y_4298_;
goto v___jp_4282_;
}
else
{
uint8_t v_isExporting_4301_; 
v_isExporting_4301_ = lean_ctor_get_uint8(v___y_4293_, sizeof(void*)*13);
lean_dec_ref(v___y_4293_);
if (v_isExporting_4301_ == 0)
{
lean_dec_ref(v___y_4298_);
lean_dec(v___y_4295_);
v___y_4266_ = v___y_4290_;
v___y_4267_ = v___y_4291_;
v___y_4268_ = v___y_4292_;
v___y_4269_ = v___y_4297_;
goto v___jp_4265_;
}
else
{
if (v___y_4294_ == 0)
{
lean_dec_ref(v___y_4297_);
lean_dec_ref(v___y_4291_);
v___y_4283_ = v___y_4290_;
v___y_4284_ = v___y_4292_;
v___y_4285_ = v___y_4295_;
v___y_4286_ = v___y_4298_;
goto v___jp_4282_;
}
else
{
lean_dec_ref(v___y_4298_);
lean_dec(v___y_4295_);
v___y_4266_ = v___y_4290_;
v___y_4267_ = v___y_4291_;
v___y_4268_ = v___y_4292_;
v___y_4269_ = v___y_4297_;
goto v___jp_4265_;
}
}
}
}
v___jp_4302_:
{
lean_object* v___x_4306_; double v___x_4307_; double v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; 
v___x_4306_ = lean_io_get_num_heartbeats();
v___x_4307_ = lean_float_of_nat(v___y_4304_);
v___x_4308_ = lean_float_of_nat(v___x_4306_);
v___x_4309_ = lean_box_float(v___x_4307_);
v___x_4310_ = lean_box_float(v___x_4308_);
v___x_4311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4311_, 0, v___x_4309_);
lean_ctor_set(v___x_4311_, 1, v___x_4310_);
v___x_4312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4312_, 0, v_a_4305_);
lean_ctor_set(v___x_4312_, 1, v___x_4311_);
v___x_4313_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3970_, v_hasTrace_3836_, v___x_4198_, v_options_3834_, v___x_4200_, v___y_4303_, v___f_4197_, v___x_4312_, v_a_3778_, v_a_3779_);
return v___x_4313_;
}
v___jp_4314_:
{
if (lean_obj_tag(v___y_4317_) == 0)
{
lean_object* v_a_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4325_; 
v_a_4318_ = lean_ctor_get(v___y_4317_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___y_4317_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4320_ = v___y_4317_;
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_a_4318_);
lean_dec(v___y_4317_);
v___x_4320_ = lean_box(0);
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
v_resetjp_4319_:
{
lean_object* v___x_4323_; 
if (v_isShared_4321_ == 0)
{
lean_ctor_set_tag(v___x_4320_, 1);
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
v___y_4303_ = v___y_4315_;
v___y_4304_ = v___y_4316_;
v_a_4305_ = v___x_4323_;
goto v___jp_4302_;
}
}
}
else
{
lean_object* v_a_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4333_; 
v_a_4326_ = lean_ctor_get(v___y_4317_, 0);
v_isSharedCheck_4333_ = !lean_is_exclusive(v___y_4317_);
if (v_isSharedCheck_4333_ == 0)
{
v___x_4328_ = v___y_4317_;
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_a_4326_);
lean_dec(v___y_4317_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v___x_4331_; 
if (v_isShared_4329_ == 0)
{
lean_ctor_set_tag(v___x_4328_, 0);
v___x_4331_ = v___x_4328_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v_a_4326_);
v___x_4331_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
v___y_4303_ = v___y_4315_;
v___y_4304_ = v___y_4316_;
v_a_4305_ = v___x_4331_;
goto v___jp_4302_;
}
}
}
}
v___jp_4334_:
{
lean_object* v___x_4339_; lean_object* v___x_4340_; 
v___x_4339_ = lean_box(0);
lean_inc(v_a_3779_);
lean_inc_ref(v_a_3778_);
v___x_4340_ = lean_apply_5(v___y_4337_, v___x_4339_, v___y_4336_, v_a_3778_, v_a_3779_, lean_box(0));
v___y_4315_ = v___y_4335_;
v___y_4316_ = v___y_4338_;
v___y_4317_ = v___x_4340_;
goto v___jp_4314_;
}
v___jp_4341_:
{
lean_object* v___x_4346_; lean_object* v___x_4347_; 
v___x_4346_ = lean_box(0);
lean_inc(v_a_3779_);
lean_inc_ref(v_a_3778_);
v___x_4347_ = lean_apply_5(v___y_4344_, v___x_4346_, v___y_4343_, v_a_3778_, v_a_3779_, lean_box(0));
v___y_4315_ = v___y_4342_;
v___y_4316_ = v___y_4345_;
v___y_4317_ = v___x_4347_;
goto v___jp_4314_;
}
v___jp_4348_:
{
lean_object* v___x_4349_; lean_object* v_a_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4503_; 
v___x_4349_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v_a_3779_);
v_a_4350_ = lean_ctor_get(v___x_4349_, 0);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4349_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4352_ = v___x_4349_;
v_isShared_4353_ = v_isSharedCheck_4503_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_a_4350_);
lean_dec(v___x_4349_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4503_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v___x_4354_; uint8_t v___x_4355_; 
v___x_4354_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4355_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3834_, v___x_4354_);
if (v___x_4355_ == 0)
{
lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v_env_4358_; lean_object* v_nextMacroScope_4359_; lean_object* v_ngen_4360_; lean_object* v_auxDeclNGen_4361_; lean_object* v_traceState_4362_; lean_object* v_recordedDeps_4363_; lean_object* v_messages_4364_; lean_object* v_infoState_4365_; lean_object* v_snapshotTasks_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4416_; 
v___x_4356_ = lean_io_mono_nanos_now();
v___x_4357_ = lean_st_ref_take(v_a_3779_);
v_env_4358_ = lean_ctor_get(v___x_4357_, 0);
v_nextMacroScope_4359_ = lean_ctor_get(v___x_4357_, 1);
v_ngen_4360_ = lean_ctor_get(v___x_4357_, 2);
v_auxDeclNGen_4361_ = lean_ctor_get(v___x_4357_, 3);
v_traceState_4362_ = lean_ctor_get(v___x_4357_, 4);
v_recordedDeps_4363_ = lean_ctor_get(v___x_4357_, 6);
v_messages_4364_ = lean_ctor_get(v___x_4357_, 7);
v_infoState_4365_ = lean_ctor_get(v___x_4357_, 8);
v_snapshotTasks_4366_ = lean_ctor_get(v___x_4357_, 9);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4357_);
if (v_isSharedCheck_4416_ == 0)
{
lean_object* v_unused_4417_; 
v_unused_4417_ = lean_ctor_get(v___x_4357_, 5);
lean_dec(v_unused_4417_);
v___x_4368_ = v___x_4357_;
v_isShared_4369_ = v_isSharedCheck_4416_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_snapshotTasks_4366_);
lean_inc(v_infoState_4365_);
lean_inc(v_messages_4364_);
lean_inc(v_recordedDeps_4363_);
lean_inc(v_traceState_4362_);
lean_inc(v_auxDeclNGen_4361_);
lean_inc(v_ngen_4360_);
lean_inc(v_nextMacroScope_4359_);
lean_inc(v_env_4358_);
lean_dec(v___x_4357_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4416_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4374_; 
lean_inc(v_decl_3776_);
v___x_4370_ = l_Lean_Declaration_getNames(v_decl_3776_);
v___x_4371_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4358_, v___x_4370_);
v___x_4372_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4369_ == 0)
{
lean_ctor_set(v___x_4368_, 5, v___x_4372_);
lean_ctor_set(v___x_4368_, 0, v___x_4371_);
v___x_4374_ = v___x_4368_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v___x_4371_);
lean_ctor_set(v_reuseFailAlloc_4415_, 1, v_nextMacroScope_4359_);
lean_ctor_set(v_reuseFailAlloc_4415_, 2, v_ngen_4360_);
lean_ctor_set(v_reuseFailAlloc_4415_, 3, v_auxDeclNGen_4361_);
lean_ctor_set(v_reuseFailAlloc_4415_, 4, v_traceState_4362_);
lean_ctor_set(v_reuseFailAlloc_4415_, 5, v___x_4372_);
lean_ctor_set(v_reuseFailAlloc_4415_, 6, v_recordedDeps_4363_);
lean_ctor_set(v_reuseFailAlloc_4415_, 7, v_messages_4364_);
lean_ctor_set(v_reuseFailAlloc_4415_, 8, v_infoState_4365_);
lean_ctor_set(v_reuseFailAlloc_4415_, 9, v_snapshotTasks_4366_);
v___x_4374_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___f_4379_; 
v___x_4375_ = lean_st_ref_put(v_a_3779_, v___x_4374_);
v___x_4376_ = lean_box(0);
v___x_4377_ = lean_box(v_hasTrace_3836_);
v___x_4378_ = lean_box(v___x_4355_);
lean_inc(v_decl_3776_);
v___f_4379_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed), 11, 6);
lean_closure_set(v___f_4379_, 0, v_decl_3776_);
lean_closure_set(v___f_4379_, 1, v___x_4377_);
lean_closure_set(v___f_4379_, 2, v___x_4378_);
lean_closure_set(v___f_4379_, 3, v___x_4372_);
lean_closure_set(v___f_4379_, 4, v_cls_3970_);
lean_closure_set(v___f_4379_, 5, v___x_4376_);
switch(lean_obj_tag(v_decl_3776_))
{
case 2:
{
lean_object* v_val_4380_; lean_object* v___f_4381_; lean_object* v___x_4382_; lean_object* v___f_4383_; lean_object* v___x_4384_; 
lean_del_object(v___x_4352_);
v_val_4380_ = lean_ctor_get(v_decl_3776_, 0);
lean_inc_ref_n(v_val_4380_, 3);
lean_dec_ref_known(v_decl_3776_, 1);
v___f_4381_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed), 7, 2);
lean_closure_set(v___f_4381_, 0, v_val_4380_);
lean_closure_set(v___f_4381_, 1, v___f_4379_);
v___x_4382_ = lean_box(v___x_4355_);
lean_inc_ref(v___f_4381_);
v___f_4383_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed), 7, 3);
lean_closure_set(v___f_4383_, 0, v_val_4380_);
lean_closure_set(v___f_4383_, 1, v___x_4382_);
lean_closure_set(v___f_4383_, 2, v___f_4381_);
v___x_4384_ = lean_st_ref_get(v_a_3779_);
if (v_forceExpose_3777_ == 0)
{
lean_object* v_env_4385_; 
v_env_4385_ = lean_ctor_get(v___x_4384_, 0);
lean_inc_ref(v_env_4385_);
lean_dec(v___x_4384_);
v___y_4244_ = v_env_4385_;
v___y_4245_ = v___x_4356_;
v___y_4246_ = v_a_4350_;
v___y_4247_ = v_val_4380_;
v___y_4248_ = v___x_4376_;
v___y_4249_ = v___f_4381_;
v___y_4250_ = v___f_4383_;
goto v___jp_4243_;
}
else
{
if (v___x_4355_ == 0)
{
lean_dec(v___x_4384_);
lean_dec_ref(v___f_4383_);
lean_dec_ref(v_val_4380_);
v___y_4237_ = v___x_4356_;
v___y_4238_ = v_a_4350_;
v___y_4239_ = v___x_4376_;
v___y_4240_ = v___f_4381_;
goto v___jp_4236_;
}
else
{
lean_object* v_env_4386_; 
v_env_4386_ = lean_ctor_get(v___x_4384_, 0);
lean_inc_ref(v_env_4386_);
lean_dec(v___x_4384_);
v___y_4244_ = v_env_4386_;
v___y_4245_ = v___x_4356_;
v___y_4246_ = v_a_4350_;
v___y_4247_ = v_val_4380_;
v___y_4248_ = v___x_4376_;
v___y_4249_ = v___f_4381_;
v___y_4250_ = v___f_4383_;
goto v___jp_4243_;
}
}
}
case 1:
{
lean_object* v_val_4387_; lean_object* v___x_4388_; 
lean_del_object(v___x_4352_);
v_val_4387_ = lean_ctor_get(v_decl_3776_, 0);
lean_inc_ref(v_val_4387_);
lean_dec_ref_known(v_decl_3776_, 1);
v___x_4388_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v___f_4379_, v___x_4355_, v_cls_3970_, v___x_4376_, v_forceExpose_3777_, v_val_4387_, v_a_3778_, v_a_3779_);
v___y_4217_ = v___x_4356_;
v___y_4218_ = v_a_4350_;
v___y_4219_ = v___x_4388_;
goto v___jp_4216_;
}
case 5:
{
lean_object* v_defns_4389_; 
lean_del_object(v___x_4352_);
v_defns_4389_ = lean_ctor_get(v_decl_3776_, 0);
if (lean_obj_tag(v_defns_4389_) == 1)
{
lean_object* v_tail_4390_; 
v_tail_4390_ = lean_ctor_get(v_defns_4389_, 1);
if (lean_obj_tag(v_tail_4390_) == 0)
{
lean_object* v_head_4391_; lean_object* v___x_4392_; 
lean_inc_ref(v_defns_4389_);
lean_dec_ref_known(v_decl_3776_, 1);
v_head_4391_ = lean_ctor_get(v_defns_4389_, 0);
lean_inc(v_head_4391_);
lean_dec_ref_known(v_defns_4389_, 2);
v___x_4392_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v___f_4379_, v___x_4355_, v_cls_3970_, v___x_4376_, v_forceExpose_3777_, v_head_4391_, v_a_3778_, v_a_3779_);
v___y_4217_ = v___x_4356_;
v___y_4218_ = v_a_4350_;
v___y_4219_ = v___x_4392_;
goto v___jp_4216_;
}
else
{
lean_object* v___x_4393_; 
lean_dec_ref(v___f_4379_);
lean_inc_ref(v_decl_3776_);
v___x_4393_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3776_, v_cls_3970_, v_decl_3776_, v_a_3778_, v_a_3779_);
lean_dec_ref_known(v_decl_3776_, 1);
v___y_4217_ = v___x_4356_;
v___y_4218_ = v_a_4350_;
v___y_4219_ = v___x_4393_;
goto v___jp_4216_;
}
}
else
{
lean_object* v___x_4394_; 
lean_dec_ref(v___f_4379_);
lean_inc_ref(v_decl_3776_);
v___x_4394_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3776_, v_cls_3970_, v_decl_3776_, v_a_3778_, v_a_3779_);
lean_dec_ref_known(v_decl_3776_, 1);
v___y_4217_ = v___x_4356_;
v___y_4218_ = v_a_4350_;
v___y_4219_ = v___x_4394_;
goto v___jp_4216_;
}
}
case 3:
{
lean_object* v_val_4395_; lean_object* v___f_4396_; lean_object* v___f_4397_; lean_object* v___x_4398_; lean_object* v_env_4399_; lean_object* v___x_4400_; 
lean_del_object(v___x_4352_);
v_val_4395_ = lean_ctor_get(v_decl_3776_, 0);
lean_inc_ref_n(v_val_4395_, 3);
lean_dec_ref_known(v_decl_3776_, 1);
v___f_4396_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed), 7, 2);
lean_closure_set(v___f_4396_, 0, v_val_4395_);
lean_closure_set(v___f_4396_, 1, v___f_4379_);
lean_inc_ref(v___f_4396_);
v___f_4397_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10___boxed), 6, 2);
lean_closure_set(v___f_4397_, 0, v_val_4395_);
lean_closure_set(v___f_4397_, 1, v___f_4396_);
v___x_4398_ = lean_st_ref_get(v_a_3779_);
v_env_4399_ = lean_ctor_get(v___x_4398_, 0);
lean_inc_ref(v_env_4399_);
lean_dec(v___x_4398_);
v___x_4400_ = lean_st_ref_get(v_a_3779_);
if (v_forceExpose_3777_ == 0)
{
lean_object* v_env_4401_; 
v_env_4401_ = lean_ctor_get(v___x_4400_, 0);
lean_inc_ref(v_env_4401_);
lean_dec(v___x_4400_);
v___y_4290_ = v___x_4356_;
v___y_4291_ = v_val_4395_;
v___y_4292_ = v_a_4350_;
v___y_4293_ = v_env_4401_;
v___y_4294_ = v___x_4355_;
v___y_4295_ = v___x_4376_;
v___y_4296_ = v_env_4399_;
v___y_4297_ = v___f_4397_;
v___y_4298_ = v___f_4396_;
goto v___jp_4289_;
}
else
{
if (v___x_4355_ == 0)
{
lean_dec(v___x_4400_);
lean_dec_ref(v_env_4399_);
lean_dec_ref(v___f_4397_);
lean_dec_ref(v_val_4395_);
v___y_4283_ = v___x_4356_;
v___y_4284_ = v_a_4350_;
v___y_4285_ = v___x_4376_;
v___y_4286_ = v___f_4396_;
goto v___jp_4282_;
}
else
{
lean_object* v_env_4402_; 
v_env_4402_ = lean_ctor_get(v___x_4400_, 0);
lean_inc_ref(v_env_4402_);
lean_dec(v___x_4400_);
v___y_4290_ = v___x_4356_;
v___y_4291_ = v_val_4395_;
v___y_4292_ = v_a_4350_;
v___y_4293_ = v_env_4402_;
v___y_4294_ = v___x_4355_;
v___y_4295_ = v___x_4376_;
v___y_4296_ = v_env_4399_;
v___y_4297_ = v___f_4397_;
v___y_4298_ = v___f_4396_;
goto v___jp_4289_;
}
}
}
case 0:
{
lean_object* v_val_4403_; lean_object* v_toConstantVal_4404_; lean_object* v_name_4405_; lean_object* v___x_4407_; 
lean_dec_ref(v___f_4379_);
v_val_4403_ = lean_ctor_get(v_decl_3776_, 0);
v_toConstantVal_4404_ = lean_ctor_get(v_val_4403_, 0);
v_name_4405_ = lean_ctor_get(v_toConstantVal_4404_, 0);
lean_inc_ref(v_val_4403_);
if (v_isShared_4353_ == 0)
{
lean_ctor_set(v___x_4352_, 0, v_val_4403_);
v___x_4407_ = v___x_4352_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_val_4403_);
v___x_4407_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
uint8_t v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; 
v___x_4408_ = 2;
v___x_4409_ = lean_box(v___x_4408_);
v___x_4410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4410_, 0, v___x_4407_);
lean_ctor_set(v___x_4410_, 1, v___x_4409_);
lean_inc(v_name_4405_);
v___x_4411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4411_, 0, v_name_4405_);
lean_ctor_set(v___x_4411_, 1, v___x_4410_);
v___x_4412_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_decl_3776_, v_hasTrace_3836_, v___x_4355_, v___x_4372_, v_cls_3970_, v___x_4376_, v___x_4411_, v___x_4376_, v_a_3778_, v_a_3779_);
v___y_4217_ = v___x_4356_;
v___y_4218_ = v_a_4350_;
v___y_4219_ = v___x_4412_;
goto v___jp_4216_;
}
}
default: 
{
lean_object* v___x_4414_; 
lean_dec_ref(v___f_4379_);
lean_del_object(v___x_4352_);
lean_inc(v_decl_3776_);
v___x_4414_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3776_, v_cls_3970_, v_decl_3776_, v_a_3778_, v_a_3779_);
lean_dec(v_decl_3776_);
v___y_4217_ = v___x_4356_;
v___y_4218_ = v_a_4350_;
v___y_4219_ = v___x_4414_;
goto v___jp_4216_;
}
}
}
}
}
else
{
lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v_env_4420_; lean_object* v_nextMacroScope_4421_; lean_object* v_ngen_4422_; lean_object* v_auxDeclNGen_4423_; lean_object* v_traceState_4424_; lean_object* v_recordedDeps_4425_; lean_object* v_messages_4426_; lean_object* v_infoState_4427_; lean_object* v_snapshotTasks_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4501_; 
v___x_4418_ = lean_io_get_num_heartbeats();
v___x_4419_ = lean_st_ref_take(v_a_3779_);
v_env_4420_ = lean_ctor_get(v___x_4419_, 0);
v_nextMacroScope_4421_ = lean_ctor_get(v___x_4419_, 1);
v_ngen_4422_ = lean_ctor_get(v___x_4419_, 2);
v_auxDeclNGen_4423_ = lean_ctor_get(v___x_4419_, 3);
v_traceState_4424_ = lean_ctor_get(v___x_4419_, 4);
v_recordedDeps_4425_ = lean_ctor_get(v___x_4419_, 6);
v_messages_4426_ = lean_ctor_get(v___x_4419_, 7);
v_infoState_4427_ = lean_ctor_get(v___x_4419_, 8);
v_snapshotTasks_4428_ = lean_ctor_get(v___x_4419_, 9);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4501_ == 0)
{
lean_object* v_unused_4502_; 
v_unused_4502_ = lean_ctor_get(v___x_4419_, 5);
lean_dec(v_unused_4502_);
v___x_4430_ = v___x_4419_;
v_isShared_4431_ = v_isSharedCheck_4501_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_snapshotTasks_4428_);
lean_inc(v_infoState_4427_);
lean_inc(v_messages_4426_);
lean_inc(v_recordedDeps_4425_);
lean_inc(v_traceState_4424_);
lean_inc(v_auxDeclNGen_4423_);
lean_inc(v_ngen_4422_);
lean_inc(v_nextMacroScope_4421_);
lean_inc(v_env_4420_);
lean_dec(v___x_4419_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4501_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4436_; 
lean_inc(v_decl_3776_);
v___x_4432_ = l_Lean_Declaration_getNames(v_decl_3776_);
v___x_4433_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4420_, v___x_4432_);
v___x_4434_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4431_ == 0)
{
lean_ctor_set(v___x_4430_, 5, v___x_4434_);
lean_ctor_set(v___x_4430_, 0, v___x_4433_);
v___x_4436_ = v___x_4430_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v___x_4433_);
lean_ctor_set(v_reuseFailAlloc_4500_, 1, v_nextMacroScope_4421_);
lean_ctor_set(v_reuseFailAlloc_4500_, 2, v_ngen_4422_);
lean_ctor_set(v_reuseFailAlloc_4500_, 3, v_auxDeclNGen_4423_);
lean_ctor_set(v_reuseFailAlloc_4500_, 4, v_traceState_4424_);
lean_ctor_set(v_reuseFailAlloc_4500_, 5, v___x_4434_);
lean_ctor_set(v_reuseFailAlloc_4500_, 6, v_recordedDeps_4425_);
lean_ctor_set(v_reuseFailAlloc_4500_, 7, v_messages_4426_);
lean_ctor_set(v_reuseFailAlloc_4500_, 8, v_infoState_4427_);
lean_ctor_set(v_reuseFailAlloc_4500_, 9, v_snapshotTasks_4428_);
v___x_4436_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___f_4440_; 
v___x_4437_ = lean_st_ref_put(v_a_3779_, v___x_4436_);
v___x_4438_ = lean_box(0);
v___x_4439_ = lean_box(v___x_4355_);
lean_inc(v_decl_3776_);
v___f_4440_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14___boxed), 10, 5);
lean_closure_set(v___f_4440_, 0, v_decl_3776_);
lean_closure_set(v___f_4440_, 1, v___x_4439_);
lean_closure_set(v___f_4440_, 2, v_cls_3970_);
lean_closure_set(v___f_4440_, 3, v___x_4434_);
lean_closure_set(v___f_4440_, 4, v___x_4438_);
switch(lean_obj_tag(v_decl_3776_))
{
case 2:
{
lean_object* v_val_4441_; lean_object* v___f_4442_; lean_object* v___x_4443_; 
lean_del_object(v___x_4352_);
v_val_4441_ = lean_ctor_get(v_decl_3776_, 0);
lean_inc_ref_n(v_val_4441_, 2);
lean_dec_ref_known(v_decl_3776_, 1);
v___f_4442_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed), 7, 2);
lean_closure_set(v___f_4442_, 0, v_val_4441_);
lean_closure_set(v___f_4442_, 1, v___f_4440_);
v___x_4443_ = lean_st_ref_get(v_a_3779_);
if (v_forceExpose_3777_ == 0)
{
if (v___x_4355_ == 0)
{
lean_dec(v___x_4443_);
lean_dec_ref(v_val_4441_);
v___y_4342_ = v_a_4350_;
v___y_4343_ = v___x_4438_;
v___y_4344_ = v___f_4442_;
v___y_4345_ = v___x_4418_;
goto v___jp_4341_;
}
else
{
lean_object* v_env_4444_; lean_object* v___x_4445_; uint8_t v_isModule_4446_; 
v_env_4444_ = lean_ctor_get(v___x_4443_, 0);
lean_inc_ref(v_env_4444_);
lean_dec(v___x_4443_);
v___x_4445_ = l_Lean_Environment_header(v_env_4444_);
lean_dec_ref(v_env_4444_);
v_isModule_4446_ = lean_ctor_get_uint8(v___x_4445_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4445_);
if (v_isModule_4446_ == 0)
{
lean_dec_ref(v_val_4441_);
v___y_4342_ = v_a_4350_;
v___y_4343_ = v___x_4438_;
v___y_4344_ = v___f_4442_;
v___y_4345_ = v___x_4418_;
goto v___jp_4341_;
}
else
{
if (v___x_4200_ == 0)
{
lean_object* v___x_4447_; lean_object* v___x_4448_; 
v___x_4447_ = lean_box(0);
v___x_4448_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_val_4441_, v___f_4442_, v___x_4447_, v_a_3778_, v_a_3779_);
lean_dec_ref(v_val_4441_);
v___y_4315_ = v_a_4350_;
v___y_4316_ = v___x_4418_;
v___y_4317_ = v___x_4448_;
goto v___jp_4314_;
}
else
{
lean_object* v_toConstantVal_4449_; lean_object* v_name_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; 
v_toConstantVal_4449_ = lean_ctor_get(v_val_4441_, 0);
v_name_4450_ = lean_ctor_get(v_toConstantVal_4449_, 0);
v___x_4451_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4450_);
v___x_4452_ = l_Lean_MessageData_ofName(v_name_4450_);
v___x_4453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4453_, 0, v___x_4451_);
lean_ctor_set(v___x_4453_, 1, v___x_4452_);
v___x_4454_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4455_, 0, v___x_4453_);
lean_ctor_set(v___x_4455_, 1, v___x_4454_);
v___x_4456_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3970_, v___x_4455_, v_a_3778_, v_a_3779_);
if (lean_obj_tag(v___x_4456_) == 0)
{
lean_object* v_a_4457_; lean_object* v___x_4458_; 
v_a_4457_ = lean_ctor_get(v___x_4456_, 0);
lean_inc(v_a_4457_);
lean_dec_ref_known(v___x_4456_, 1);
v___x_4458_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_val_4441_, v___f_4442_, v_a_4457_, v_a_3778_, v_a_3779_);
lean_dec_ref(v_val_4441_);
v___y_4315_ = v_a_4350_;
v___y_4316_ = v___x_4418_;
v___y_4317_ = v___x_4458_;
goto v___jp_4314_;
}
else
{
lean_dec_ref(v___f_4442_);
lean_dec_ref(v_val_4441_);
v___y_4315_ = v_a_4350_;
v___y_4316_ = v___x_4418_;
v___y_4317_ = v___x_4456_;
goto v___jp_4314_;
}
}
}
}
}
else
{
lean_dec(v___x_4443_);
lean_dec_ref(v_val_4441_);
v___y_4342_ = v_a_4350_;
v___y_4343_ = v___x_4438_;
v___y_4344_ = v___f_4442_;
v___y_4345_ = v___x_4418_;
goto v___jp_4341_;
}
}
case 1:
{
lean_object* v_val_4459_; lean_object* v___x_4460_; 
lean_del_object(v___x_4352_);
v_val_4459_ = lean_ctor_get(v_decl_3776_, 0);
lean_inc_ref(v_val_4459_);
lean_dec_ref_known(v_decl_3776_, 1);
v___x_4460_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(v___f_4440_, v_forceExpose_3777_, v___x_4355_, v___x_4438_, v_cls_3970_, v_val_4459_, v_a_3778_, v_a_3779_);
v___y_4315_ = v_a_4350_;
v___y_4316_ = v___x_4418_;
v___y_4317_ = v___x_4460_;
goto v___jp_4314_;
}
case 5:
{
lean_object* v_defns_4461_; 
lean_del_object(v___x_4352_);
v_defns_4461_ = lean_ctor_get(v_decl_3776_, 0);
if (lean_obj_tag(v_defns_4461_) == 1)
{
lean_object* v_tail_4462_; 
v_tail_4462_ = lean_ctor_get(v_defns_4461_, 1);
if (lean_obj_tag(v_tail_4462_) == 0)
{
lean_object* v_head_4463_; lean_object* v___x_4464_; 
lean_inc_ref(v_defns_4461_);
lean_dec_ref_known(v_decl_3776_, 1);
v_head_4463_ = lean_ctor_get(v_defns_4461_, 0);
lean_inc(v_head_4463_);
lean_dec_ref_known(v_defns_4461_, 2);
v___x_4464_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(v___f_4440_, v_forceExpose_3777_, v___x_4355_, v___x_4438_, v_cls_3970_, v_head_4463_, v_a_3778_, v_a_3779_);
v___y_4315_ = v_a_4350_;
v___y_4316_ = v___x_4418_;
v___y_4317_ = v___x_4464_;
goto v___jp_4314_;
}
else
{
lean_object* v___x_4465_; 
lean_dec_ref(v___f_4440_);
lean_inc_ref(v_decl_3776_);
v___x_4465_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3776_, v_cls_3970_, v_decl_3776_, v_a_3778_, v_a_3779_);
lean_dec_ref_known(v_decl_3776_, 1);
v___y_4315_ = v_a_4350_;
v___y_4316_ = v___x_4418_;
v___y_4317_ = v___x_4465_;
goto v___jp_4314_;
}
}
else
{
lean_object* v___x_4466_; 
lean_dec_ref(v___f_4440_);
lean_inc_ref(v_decl_3776_);
v___x_4466_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3776_, v_cls_3970_, v_decl_3776_, v_a_3778_, v_a_3779_);
lean_dec_ref_known(v_decl_3776_, 1);
v___y_4315_ = v_a_4350_;
v___y_4316_ = v___x_4418_;
v___y_4317_ = v___x_4466_;
goto v___jp_4314_;
}
}
case 3:
{
lean_object* v_val_4467_; lean_object* v___f_4468_; lean_object* v___x_4469_; lean_object* v_env_4470_; lean_object* v___x_4471_; 
lean_del_object(v___x_4352_);
v_val_4467_ = lean_ctor_get(v_decl_3776_, 0);
lean_inc_ref_n(v_val_4467_, 2);
lean_dec_ref_known(v_decl_3776_, 1);
v___f_4468_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed), 7, 2);
lean_closure_set(v___f_4468_, 0, v_val_4467_);
lean_closure_set(v___f_4468_, 1, v___f_4440_);
v___x_4469_ = lean_st_ref_get(v_a_3779_);
v_env_4470_ = lean_ctor_get(v___x_4469_, 0);
lean_inc_ref(v_env_4470_);
lean_dec(v___x_4469_);
v___x_4471_ = lean_st_ref_get(v_a_3779_);
if (v_forceExpose_3777_ == 0)
{
if (v___x_4355_ == 0)
{
lean_dec(v___x_4471_);
lean_dec_ref(v_env_4470_);
lean_dec_ref(v_val_4467_);
v___y_4335_ = v_a_4350_;
v___y_4336_ = v___x_4438_;
v___y_4337_ = v___f_4468_;
v___y_4338_ = v___x_4418_;
goto v___jp_4334_;
}
else
{
lean_object* v_env_4472_; lean_object* v___x_4473_; uint8_t v_isModule_4474_; 
v_env_4472_ = lean_ctor_get(v___x_4471_, 0);
lean_inc_ref(v_env_4472_);
lean_dec(v___x_4471_);
v___x_4473_ = l_Lean_Environment_header(v_env_4470_);
lean_dec_ref(v_env_4470_);
v_isModule_4474_ = lean_ctor_get_uint8(v___x_4473_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4473_);
if (v_isModule_4474_ == 0)
{
lean_dec_ref(v_env_4472_);
lean_dec_ref(v_val_4467_);
v___y_4335_ = v_a_4350_;
v___y_4336_ = v___x_4438_;
v___y_4337_ = v___f_4468_;
v___y_4338_ = v___x_4418_;
goto v___jp_4334_;
}
else
{
uint8_t v_isExporting_4475_; 
v_isExporting_4475_ = lean_ctor_get_uint8(v_env_4472_, sizeof(void*)*13);
lean_dec_ref(v_env_4472_);
if (v_isExporting_4475_ == 0)
{
if (v___x_4200_ == 0)
{
lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4476_ = lean_box(0);
v___x_4477_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_4467_, v___f_4468_, v___x_4476_, v_a_3778_, v_a_3779_);
lean_dec_ref(v_val_4467_);
v___y_4315_ = v_a_4350_;
v___y_4316_ = v___x_4418_;
v___y_4317_ = v___x_4477_;
goto v___jp_4314_;
}
else
{
lean_object* v_toConstantVal_4478_; lean_object* v_name_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; 
v_toConstantVal_4478_ = lean_ctor_get(v_val_4467_, 0);
v_name_4479_ = lean_ctor_get(v_toConstantVal_4478_, 0);
v___x_4480_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4479_);
v___x_4481_ = l_Lean_MessageData_ofName(v_name_4479_);
v___x_4482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4482_, 0, v___x_4480_);
lean_ctor_set(v___x_4482_, 1, v___x_4481_);
v___x_4483_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4484_, 0, v___x_4482_);
lean_ctor_set(v___x_4484_, 1, v___x_4483_);
v___x_4485_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3970_, v___x_4484_, v_a_3778_, v_a_3779_);
if (lean_obj_tag(v___x_4485_) == 0)
{
lean_object* v_a_4486_; lean_object* v___x_4487_; 
v_a_4486_ = lean_ctor_get(v___x_4485_, 0);
lean_inc(v_a_4486_);
lean_dec_ref_known(v___x_4485_, 1);
v___x_4487_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_4467_, v___f_4468_, v_a_4486_, v_a_3778_, v_a_3779_);
lean_dec_ref(v_val_4467_);
v___y_4315_ = v_a_4350_;
v___y_4316_ = v___x_4418_;
v___y_4317_ = v___x_4487_;
goto v___jp_4314_;
}
else
{
lean_dec_ref(v___f_4468_);
lean_dec_ref(v_val_4467_);
v___y_4315_ = v_a_4350_;
v___y_4316_ = v___x_4418_;
v___y_4317_ = v___x_4485_;
goto v___jp_4314_;
}
}
}
else
{
lean_dec_ref(v_val_4467_);
v___y_4335_ = v_a_4350_;
v___y_4336_ = v___x_4438_;
v___y_4337_ = v___f_4468_;
v___y_4338_ = v___x_4418_;
goto v___jp_4334_;
}
}
}
}
else
{
lean_dec(v___x_4471_);
lean_dec_ref(v_env_4470_);
lean_dec_ref(v_val_4467_);
v___y_4335_ = v_a_4350_;
v___y_4336_ = v___x_4438_;
v___y_4337_ = v___f_4468_;
v___y_4338_ = v___x_4418_;
goto v___jp_4334_;
}
}
case 0:
{
lean_object* v_val_4488_; lean_object* v_toConstantVal_4489_; lean_object* v_name_4490_; lean_object* v___x_4492_; 
lean_dec_ref(v___f_4440_);
v_val_4488_ = lean_ctor_get(v_decl_3776_, 0);
v_toConstantVal_4489_ = lean_ctor_get(v_val_4488_, 0);
v_name_4490_ = lean_ctor_get(v_toConstantVal_4489_, 0);
lean_inc_ref(v_val_4488_);
if (v_isShared_4353_ == 0)
{
lean_ctor_set(v___x_4352_, 0, v_val_4488_);
v___x_4492_ = v___x_4352_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_val_4488_);
v___x_4492_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
uint8_t v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; 
v___x_4493_ = 2;
v___x_4494_ = lean_box(v___x_4493_);
v___x_4495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4495_, 0, v___x_4492_);
lean_ctor_set(v___x_4495_, 1, v___x_4494_);
lean_inc(v_name_4490_);
v___x_4496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4496_, 0, v_name_4490_);
lean_ctor_set(v___x_4496_, 1, v___x_4495_);
v___x_4497_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(v_decl_3776_, v___x_4355_, v_cls_3970_, v___x_4434_, v___x_4438_, v___x_4496_, v___x_4438_, v_a_3778_, v_a_3779_);
v___y_4315_ = v_a_4350_;
v___y_4316_ = v___x_4418_;
v___y_4317_ = v___x_4497_;
goto v___jp_4314_;
}
}
default: 
{
lean_object* v___x_4499_; 
lean_dec_ref(v___f_4440_);
lean_del_object(v___x_4352_);
lean_inc(v_decl_3776_);
v___x_4499_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3776_, v_cls_3970_, v_decl_3776_, v_a_3778_, v_a_3779_);
lean_dec(v_decl_3776_);
v___y_4315_ = v_a_4350_;
v___y_4316_ = v___x_4418_;
v___y_4317_ = v___x_4499_;
goto v___jp_4314_;
}
}
}
}
}
}
}
}
v___jp_3781_:
{
lean_object* v___x_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3792_; 
v___x_3785_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3782_, v___y_3783_);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3792_ == 0)
{
lean_object* v_unused_3793_; 
v_unused_3793_ = lean_ctor_get(v___x_3785_, 0);
lean_dec(v_unused_3793_);
v___x_3787_ = v___x_3785_;
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
else
{
lean_dec(v___x_3785_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3790_; 
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 0, v_a_3784_);
v___x_3790_ = v___x_3787_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_a_3784_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
}
v___jp_3794_:
{
lean_object* v___x_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3805_; 
v___x_3798_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3795_, v___y_3796_);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3798_);
if (v_isSharedCheck_3805_ == 0)
{
lean_object* v_unused_3806_; 
v_unused_3806_ = lean_ctor_get(v___x_3798_, 0);
lean_dec(v_unused_3806_);
v___x_3800_ = v___x_3798_;
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
else
{
lean_dec(v___x_3798_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3803_; 
if (v_isShared_3801_ == 0)
{
lean_ctor_set_tag(v___x_3800_, 1);
lean_ctor_set(v___x_3800_, 0, v_a_3797_);
v___x_3803_ = v___x_3800_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_a_3797_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
v___jp_3807_:
{
lean_object* v___x_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
v___x_3811_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3809_, v___y_3808_);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3811_);
if (v_isSharedCheck_3818_ == 0)
{
lean_object* v_unused_3819_; 
v_unused_3819_ = lean_ctor_get(v___x_3811_, 0);
lean_dec(v_unused_3819_);
v___x_3813_ = v___x_3811_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_dec(v___x_3811_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3816_; 
if (v_isShared_3814_ == 0)
{
lean_ctor_set(v___x_3813_, 0, v_a_3810_);
v___x_3816_ = v___x_3813_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_a_3810_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
v___jp_3820_:
{
lean_object* v___x_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3831_; 
v___x_3824_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3822_, v___y_3821_);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3831_ == 0)
{
lean_object* v_unused_3832_; 
v_unused_3832_ = lean_ctor_get(v___x_3824_, 0);
lean_dec(v_unused_3832_);
v___x_3826_ = v___x_3824_;
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
else
{
lean_dec(v___x_3824_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3829_; 
if (v_isShared_3827_ == 0)
{
lean_ctor_set_tag(v___x_3826_, 1);
lean_ctor_set(v___x_3826_, 0, v_a_3823_);
v___x_3829_ = v___x_3826_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_a_3823_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
v___jp_3837_:
{
lean_object* v___x_3850_; 
lean_inc_ref(v___y_3845_);
v___x_3850_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3841_, v___y_3845_, v___y_3840_, v___y_3849_);
if (lean_obj_tag(v___x_3850_) == 0)
{
lean_object* v___x_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3897_; 
lean_dec_ref_known(v___x_3850_, 1);
lean_dec(v___y_3842_);
lean_inc_ref(v___y_3847_);
v___x_3851_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3847_, v___y_3844_);
v_isSharedCheck_3897_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3897_ == 0)
{
lean_object* v_unused_3898_; 
v_unused_3898_ = lean_ctor_get(v___x_3851_, 0);
lean_dec(v_unused_3898_);
v___x_3853_ = v___x_3851_;
v_isShared_3854_ = v_isSharedCheck_3897_;
goto v_resetjp_3852_;
}
else
{
lean_dec(v___x_3851_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3897_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3855_; lean_object* v___x_3856_; uint8_t v___x_3857_; 
v___x_3855_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3846_);
v___x_3856_ = l_Lean_Elab_async;
v___x_3857_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_3855_, v___x_3856_);
lean_dec_ref(v___x_3855_);
if (v___x_3857_ == 0)
{
lean_object* v___x_3858_; lean_object* v_r_3859_; 
lean_del_object(v___x_3853_);
lean_dec_ref(v___y_3839_);
lean_dec_ref(v___y_3838_);
v___x_3858_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3845_, v___y_3844_);
lean_dec_ref(v___x_3858_);
v_r_3859_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3776_, v___y_3846_, v___y_3844_);
if (lean_obj_tag(v_r_3859_) == 0)
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3869_; 
v_a_3860_ = lean_ctor_get(v_r_3859_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v_r_3859_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3862_ = v_r_3859_;
v_isShared_3863_ = v_isSharedCheck_3869_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v_r_3859_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3869_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
lean_inc(v_a_3860_);
if (v_isShared_3863_ == 0)
{
lean_ctor_set_tag(v___x_3862_, 1);
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
lean_object* v___x_3866_; 
v___x_3866_ = lean_apply_2(v___y_3848_, v___x_3865_, lean_box(0));
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_dec_ref_known(v___x_3866_, 1);
v___y_3808_ = v___y_3844_;
v___y_3809_ = v___y_3847_;
v_a_3810_ = v_a_3860_;
goto v___jp_3807_;
}
else
{
lean_object* v_a_3867_; 
lean_dec(v_a_3860_);
v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
lean_inc(v_a_3867_);
lean_dec_ref_known(v___x_3866_, 1);
v___y_3821_ = v___y_3844_;
v___y_3822_ = v___y_3847_;
v_a_3823_ = v_a_3867_;
goto v___jp_3820_;
}
}
}
}
else
{
lean_object* v_a_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
v_a_3870_ = lean_ctor_get(v_r_3859_, 0);
lean_inc(v_a_3870_);
lean_dec_ref_known(v_r_3859_, 1);
v___x_3871_ = lean_box(0);
v___x_3872_ = lean_apply_2(v___y_3848_, v___x_3871_, lean_box(0));
if (lean_obj_tag(v___x_3872_) == 0)
{
lean_dec_ref_known(v___x_3872_, 1);
v___y_3821_ = v___y_3844_;
v___y_3822_ = v___y_3847_;
v_a_3823_ = v_a_3870_;
goto v___jp_3820_;
}
else
{
lean_object* v_a_3873_; 
lean_dec(v_a_3870_);
v_a_3873_ = lean_ctor_get(v___x_3872_, 0);
lean_inc(v_a_3873_);
lean_dec_ref_known(v___x_3872_, 1);
v___y_3821_ = v___y_3844_;
v___y_3822_ = v___y_3847_;
v_a_3823_ = v_a_3873_;
goto v___jp_3820_;
}
}
}
else
{
lean_object* v___x_3874_; lean_object* v___x_3876_; 
lean_dec_ref(v___y_3848_);
lean_dec_ref(v___y_3847_);
lean_dec_ref(v___y_3845_);
lean_dec(v_decl_3776_);
v___x_3874_ = l_IO_CancelToken_new();
if (v_isShared_3854_ == 0)
{
lean_ctor_set_tag(v___x_3853_, 1);
lean_ctor_set(v___x_3853_, 0, v___x_3874_);
v___x_3876_ = v___x_3853_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v___x_3874_);
v___x_3876_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3877_ = lean_unsigned_to_nat(0u);
v___x_3878_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_3879_ = l_Lean_Name_toString(v___x_3878_, v___y_3843_);
lean_inc_ref(v___x_3876_);
v___x_3880_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3839_, v___x_3876_, v___x_3879_, v___y_3846_, v___y_3844_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v_a_3881_; lean_object* v_checked_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; 
v_a_3881_ = lean_ctor_get(v___x_3880_, 0);
lean_inc(v_a_3881_);
lean_dec_ref_known(v___x_3880_, 1);
v_checked_3882_ = lean_ctor_get(v___y_3838_, 2);
lean_inc_ref(v_checked_3882_);
lean_dec_ref(v___y_3838_);
v___x_3883_ = lean_io_map_task(v_a_3881_, v_checked_3882_, v___x_3877_, v_hasTrace_3836_);
v___x_3884_ = lean_box(0);
v___x_3885_ = lean_box(2);
v___x_3886_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3884_);
lean_ctor_set(v___x_3886_, 1, v___x_3885_);
lean_ctor_set(v___x_3886_, 2, v___x_3876_);
lean_ctor_set(v___x_3886_, 3, v___x_3883_);
v___x_3887_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3886_, v___y_3844_);
return v___x_3887_;
}
else
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
lean_dec_ref(v___x_3876_);
lean_dec_ref(v___y_3838_);
v_a_3888_ = lean_ctor_get(v___x_3880_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3890_ = v___x_3880_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v___x_3880_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
if (v_isShared_3891_ == 0)
{
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3888_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3910_; 
lean_dec_ref(v___y_3848_);
lean_dec_ref(v___y_3847_);
lean_dec_ref(v___y_3845_);
lean_dec_ref(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v_decl_3776_);
v_a_3899_ = lean_ctor_get(v___x_3850_, 0);
v_isSharedCheck_3910_ = !lean_is_exclusive(v___x_3850_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3901_ = v___x_3850_;
v_isShared_3902_ = v_isSharedCheck_3910_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3850_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3910_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3908_; 
v___x_3903_ = lean_io_error_to_string(v_a_3899_);
v___x_3904_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3903_);
v___x_3905_ = l_Lean_MessageData_ofFormat(v___x_3904_);
v___x_3906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3906_, 0, v___y_3842_);
lean_ctor_set(v___x_3906_, 1, v___x_3905_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 0, v___x_3906_);
v___x_3908_ = v___x_3901_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v___x_3906_);
v___x_3908_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
return v___x_3908_;
}
}
}
}
v___jp_3911_:
{
lean_object* v_ref_3920_; uint8_t v___x_3921_; lean_object* v___x_3922_; 
v_ref_3920_ = lean_ctor_get(v___y_3917_, 2);
v___x_3921_ = 1;
lean_inc_ref(v___y_3918_);
v___x_3922_ = l_Lean_Environment_addConstAsync(v___y_3918_, v___y_3915_, v___y_3912_, v___y_3919_, v_hasTrace_3836_, v___x_3921_);
if (lean_obj_tag(v___x_3922_) == 0)
{
lean_object* v_a_3923_; lean_object* v_mainEnv_3924_; lean_object* v_asyncEnv_3925_; lean_object* v___f_3926_; lean_object* v___f_3927_; lean_object* v___x_3928_; 
v_a_3923_ = lean_ctor_get(v___x_3922_, 0);
lean_inc_n(v_a_3923_, 3);
lean_dec_ref_known(v___x_3922_, 1);
v_mainEnv_3924_ = lean_ctor_get(v_a_3923_, 0);
lean_inc_ref(v_mainEnv_3924_);
v_asyncEnv_3925_ = lean_ctor_get(v_a_3923_, 1);
lean_inc_ref_n(v_asyncEnv_3925_, 2);
lean_inc(v_ref_3920_);
lean_inc(v___y_3916_);
v___f_3926_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3926_, 0, v___y_3916_);
lean_closure_set(v___f_3926_, 1, v_a_3923_);
lean_closure_set(v___f_3926_, 2, v_ref_3920_);
lean_inc(v_decl_3776_);
v___f_3927_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3927_, 0, v_a_3923_);
lean_closure_set(v___f_3927_, 1, v_asyncEnv_3925_);
lean_closure_set(v___f_3927_, 2, v_decl_3776_);
v___x_3928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3928_, 0, v___y_3914_);
if (lean_obj_tag(v___y_3913_) == 0)
{
lean_inc(v_ref_3920_);
lean_inc_ref(v___x_3928_);
v___y_3838_ = v___y_3918_;
v___y_3839_ = v___f_3927_;
v___y_3840_ = v___x_3928_;
v___y_3841_ = v_a_3923_;
v___y_3842_ = v_ref_3920_;
v___y_3843_ = v___x_3921_;
v___y_3844_ = v___y_3916_;
v___y_3845_ = v_asyncEnv_3925_;
v___y_3846_ = v___y_3917_;
v___y_3847_ = v_mainEnv_3924_;
v___y_3848_ = v___f_3926_;
v___y_3849_ = v___x_3928_;
goto v___jp_3837_;
}
else
{
lean_inc(v_ref_3920_);
v___y_3838_ = v___y_3918_;
v___y_3839_ = v___f_3927_;
v___y_3840_ = v___x_3928_;
v___y_3841_ = v_a_3923_;
v___y_3842_ = v_ref_3920_;
v___y_3843_ = v___x_3921_;
v___y_3844_ = v___y_3916_;
v___y_3845_ = v_asyncEnv_3925_;
v___y_3846_ = v___y_3917_;
v___y_3847_ = v_mainEnv_3924_;
v___y_3848_ = v___f_3926_;
v___y_3849_ = v___y_3913_;
goto v___jp_3837_;
}
}
else
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3940_; 
lean_dec_ref(v___y_3918_);
lean_dec_ref(v___y_3914_);
lean_dec(v___y_3913_);
lean_dec(v_decl_3776_);
v_a_3929_ = lean_ctor_get(v___x_3922_, 0);
v_isSharedCheck_3940_ = !lean_is_exclusive(v___x_3922_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3931_ = v___x_3922_;
v_isShared_3932_ = v_isSharedCheck_3940_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3922_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3940_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3938_; 
v___x_3933_ = lean_io_error_to_string(v_a_3929_);
v___x_3934_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3933_);
v___x_3935_ = l_Lean_MessageData_ofFormat(v___x_3934_);
lean_inc(v_ref_3920_);
v___x_3936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3936_, 0, v_ref_3920_);
lean_ctor_set(v___x_3936_, 1, v___x_3935_);
if (v_isShared_3932_ == 0)
{
lean_ctor_set(v___x_3931_, 0, v___x_3936_);
v___x_3938_ = v___x_3931_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v___x_3936_);
v___x_3938_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
return v___x_3938_;
}
}
}
}
v___jp_3941_:
{
lean_object* v___x_3948_; 
v___x_3948_ = lean_st_ref_get(v___y_3947_);
if (lean_obj_tag(v_exportedInfo_x3f_3945_) == 0)
{
lean_object* v_env_3949_; lean_object* v___x_3950_; 
v_env_3949_ = lean_ctor_get(v___x_3948_, 0);
lean_inc_ref(v_env_3949_);
lean_dec(v___x_3948_);
v___x_3950_ = lean_box(0);
v___y_3912_ = v___y_3942_;
v___y_3913_ = v_exportedInfo_x3f_3945_;
v___y_3914_ = v___y_3943_;
v___y_3915_ = v___y_3944_;
v___y_3916_ = v___y_3947_;
v___y_3917_ = v___y_3946_;
v___y_3918_ = v_env_3949_;
v___y_3919_ = v___x_3950_;
goto v___jp_3911_;
}
else
{
lean_object* v_env_3951_; lean_object* v_val_3952_; uint8_t v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v_env_3951_ = lean_ctor_get(v___x_3948_, 0);
lean_inc_ref(v_env_3951_);
lean_dec(v___x_3948_);
v_val_3952_ = lean_ctor_get(v_exportedInfo_x3f_3945_, 0);
v___x_3953_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3952_);
v___x_3954_ = lean_box(v___x_3953_);
v___x_3955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3954_);
v___y_3912_ = v___y_3942_;
v___y_3913_ = v_exportedInfo_x3f_3945_;
v___y_3914_ = v___y_3943_;
v___y_3915_ = v___y_3944_;
v___y_3916_ = v___y_3947_;
v___y_3917_ = v___y_3946_;
v___y_3918_ = v_env_3951_;
v___y_3919_ = v___x_3955_;
goto v___jp_3911_;
}
}
v___jp_3956_:
{
lean_object* v___x_3962_; 
lean_inc_ref(v___y_3958_);
v___x_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3962_, 0, v___y_3958_);
v___y_3942_ = v___y_3957_;
v___y_3943_ = v___y_3958_;
v___y_3944_ = v___y_3959_;
v_exportedInfo_x3f_3945_ = v___x_3962_;
v___y_3946_ = v___y_3960_;
v___y_3947_ = v___y_3961_;
goto v___jp_3941_;
}
v___jp_3963_:
{
lean_object* v___x_3969_; 
lean_inc_ref(v___y_3965_);
v___x_3969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3969_, 0, v___y_3965_);
v___y_3942_ = v___y_3964_;
v___y_3943_ = v___y_3965_;
v___y_3944_ = v___y_3966_;
v_exportedInfo_x3f_3945_ = v___x_3969_;
v___y_3946_ = v___y_3967_;
v___y_3947_ = v___y_3968_;
goto v___jp_3941_;
}
v___jp_3971_:
{
lean_object* v___x_3976_; uint8_t v___x_3977_; 
v___x_3976_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_3977_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3974_, v_options_3973_, v___x_3976_);
if (v___x_3977_ == 0)
{
lean_object* v___x_3978_; 
v___x_3978_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3776_, v___y_3972_, v___y_3975_);
return v___x_3978_;
}
else
{
lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3979_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
v___x_3980_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3970_, v___x_3979_, v___y_3972_, v___y_3975_);
if (lean_obj_tag(v___x_3980_) == 0)
{
lean_object* v___x_3981_; 
lean_dec_ref_known(v___x_3980_, 1);
v___x_3981_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3776_, v___y_3972_, v___y_3975_);
return v___x_3981_;
}
else
{
lean_dec(v_decl_3776_);
return v___x_3980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___boxed(lean_object* v_decl_4882_, lean_object* v_forceExpose_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_, lean_object* v_a_4886_){
_start:
{
uint8_t v_forceExpose_boxed_4887_; lean_object* v_res_4888_; 
v_forceExpose_boxed_4887_ = lean_unbox(v_forceExpose_4883_);
v_res_4888_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4882_, v_forceExpose_boxed_4887_, v_a_4884_, v_a_4885_);
lean_dec(v_a_4885_);
lean_dec_ref(v_a_4884_);
return v_res_4888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(lean_object* v_opt_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_){
_start:
{
lean_object* v___x_4893_; 
v___x_4893_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_4889_, v___y_4890_);
return v___x_4893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___boxed(lean_object* v_opt_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_){
_start:
{
lean_object* v_res_4898_; 
v_res_4898_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(v_opt_4894_, v___y_4895_, v___y_4896_);
lean_dec(v___y_4896_);
lean_dec_ref(v___y_4895_);
lean_dec_ref(v_opt_4894_);
return v_res_4898_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0(lean_object* v_x_4899_, lean_object* v_x_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_){
_start:
{
if (lean_obj_tag(v_x_4899_) == 0)
{
lean_object* v___x_4904_; lean_object* v___x_4905_; 
v___x_4904_ = l_List_reverse___redArg(v_x_4900_);
v___x_4905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4905_, 0, v___x_4904_);
return v___x_4905_;
}
else
{
lean_object* v_head_4906_; lean_object* v_tail_4907_; lean_object* v___x_4909_; uint8_t v_isShared_4910_; uint8_t v_isSharedCheck_4925_; 
v_head_4906_ = lean_ctor_get(v_x_4899_, 0);
v_tail_4907_ = lean_ctor_get(v_x_4899_, 1);
v_isSharedCheck_4925_ = !lean_is_exclusive(v_x_4899_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4909_ = v_x_4899_;
v_isShared_4910_ = v_isSharedCheck_4925_;
goto v_resetjp_4908_;
}
else
{
lean_inc(v_tail_4907_);
lean_inc(v_head_4906_);
lean_dec(v_x_4899_);
v___x_4909_ = lean_box(0);
v_isShared_4910_ = v_isSharedCheck_4925_;
goto v_resetjp_4908_;
}
v_resetjp_4908_:
{
lean_object* v___x_4911_; 
v___x_4911_ = l_Lean_snapshotEnvLinterOptions(v_head_4906_, v___y_4901_, v___y_4902_);
if (lean_obj_tag(v___x_4911_) == 0)
{
lean_object* v_a_4912_; lean_object* v___x_4914_; 
v_a_4912_ = lean_ctor_get(v___x_4911_, 0);
lean_inc(v_a_4912_);
lean_dec_ref_known(v___x_4911_, 1);
if (v_isShared_4910_ == 0)
{
lean_ctor_set(v___x_4909_, 1, v_x_4900_);
lean_ctor_set(v___x_4909_, 0, v_a_4912_);
v___x_4914_ = v___x_4909_;
goto v_reusejp_4913_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v_a_4912_);
lean_ctor_set(v_reuseFailAlloc_4916_, 1, v_x_4900_);
v___x_4914_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4913_;
}
v_reusejp_4913_:
{
v_x_4899_ = v_tail_4907_;
v_x_4900_ = v___x_4914_;
goto _start;
}
}
else
{
lean_object* v_a_4917_; lean_object* v___x_4919_; uint8_t v_isShared_4920_; uint8_t v_isSharedCheck_4924_; 
lean_del_object(v___x_4909_);
lean_dec(v_tail_4907_);
lean_dec(v_x_4900_);
v_a_4917_ = lean_ctor_get(v___x_4911_, 0);
v_isSharedCheck_4924_ = !lean_is_exclusive(v___x_4911_);
if (v_isSharedCheck_4924_ == 0)
{
v___x_4919_ = v___x_4911_;
v_isShared_4920_ = v_isSharedCheck_4924_;
goto v_resetjp_4918_;
}
else
{
lean_inc(v_a_4917_);
lean_dec(v___x_4911_);
v___x_4919_ = lean_box(0);
v_isShared_4920_ = v_isSharedCheck_4924_;
goto v_resetjp_4918_;
}
v_resetjp_4918_:
{
lean_object* v___x_4922_; 
if (v_isShared_4920_ == 0)
{
v___x_4922_ = v___x_4919_;
goto v_reusejp_4921_;
}
else
{
lean_object* v_reuseFailAlloc_4923_; 
v_reuseFailAlloc_4923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4923_, 0, v_a_4917_);
v___x_4922_ = v_reuseFailAlloc_4923_;
goto v_reusejp_4921_;
}
v_reusejp_4921_:
{
return v___x_4922_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0___boxed(lean_object* v_x_4926_, lean_object* v_x_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_){
_start:
{
lean_object* v_res_4931_; 
v_res_4931_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v_x_4926_, v_x_4927_, v___y_4928_, v___y_4929_);
lean_dec(v___y_4929_);
lean_dec_ref(v___y_4928_);
return v_res_4931_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object* v_decl_4932_, uint8_t v_forceExpose_4933_, lean_object* v_a_4934_, lean_object* v_a_4935_){
_start:
{
lean_object* v___x_4937_; 
lean_inc(v_decl_4932_);
v___x_4937_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4932_, v_forceExpose_4933_, v_a_4934_, v_a_4935_);
if (lean_obj_tag(v___x_4937_) == 0)
{
lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; 
lean_dec_ref_known(v___x_4937_, 1);
v___x_4938_ = l_Lean_Declaration_getTopLevelNames(v_decl_4932_);
v___x_4939_ = lean_box(0);
v___x_4940_ = lean_box(0);
v___x_4941_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v___x_4938_, v___x_4939_, v_a_4934_, v_a_4935_);
if (lean_obj_tag(v___x_4941_) == 0)
{
lean_object* v___x_4943_; uint8_t v_isShared_4944_; uint8_t v_isSharedCheck_4948_; 
v_isSharedCheck_4948_ = !lean_is_exclusive(v___x_4941_);
if (v_isSharedCheck_4948_ == 0)
{
lean_object* v_unused_4949_; 
v_unused_4949_ = lean_ctor_get(v___x_4941_, 0);
lean_dec(v_unused_4949_);
v___x_4943_ = v___x_4941_;
v_isShared_4944_ = v_isSharedCheck_4948_;
goto v_resetjp_4942_;
}
else
{
lean_dec(v___x_4941_);
v___x_4943_ = lean_box(0);
v_isShared_4944_ = v_isSharedCheck_4948_;
goto v_resetjp_4942_;
}
v_resetjp_4942_:
{
lean_object* v___x_4946_; 
if (v_isShared_4944_ == 0)
{
lean_ctor_set(v___x_4943_, 0, v___x_4940_);
v___x_4946_ = v___x_4943_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4947_; 
v_reuseFailAlloc_4947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4947_, 0, v___x_4940_);
v___x_4946_ = v_reuseFailAlloc_4947_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
return v___x_4946_;
}
}
}
else
{
lean_object* v_a_4950_; lean_object* v___x_4952_; uint8_t v_isShared_4953_; uint8_t v_isSharedCheck_4957_; 
v_a_4950_ = lean_ctor_get(v___x_4941_, 0);
v_isSharedCheck_4957_ = !lean_is_exclusive(v___x_4941_);
if (v_isSharedCheck_4957_ == 0)
{
v___x_4952_ = v___x_4941_;
v_isShared_4953_ = v_isSharedCheck_4957_;
goto v_resetjp_4951_;
}
else
{
lean_inc(v_a_4950_);
lean_dec(v___x_4941_);
v___x_4952_ = lean_box(0);
v_isShared_4953_ = v_isSharedCheck_4957_;
goto v_resetjp_4951_;
}
v_resetjp_4951_:
{
lean_object* v___x_4955_; 
if (v_isShared_4953_ == 0)
{
v___x_4955_ = v___x_4952_;
goto v_reusejp_4954_;
}
else
{
lean_object* v_reuseFailAlloc_4956_; 
v_reuseFailAlloc_4956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4956_, 0, v_a_4950_);
v___x_4955_ = v_reuseFailAlloc_4956_;
goto v_reusejp_4954_;
}
v_reusejp_4954_:
{
return v___x_4955_;
}
}
}
}
else
{
lean_dec(v_decl_4932_);
return v___x_4937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___boxed(lean_object* v_decl_4958_, lean_object* v_forceExpose_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_){
_start:
{
uint8_t v_forceExpose_boxed_4963_; lean_object* v_res_4964_; 
v_forceExpose_boxed_4963_ = lean_unbox(v_forceExpose_4959_);
v_res_4964_ = l_Lean_addDecl(v_decl_4958_, v_forceExpose_boxed_4963_, v_a_4960_, v_a_4961_);
lean_dec(v_a_4961_);
lean_dec_ref(v_a_4960_);
return v_res_4964_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(lean_object* v_as_x27_4965_, lean_object* v_b_4966_, lean_object* v___y_4967_){
_start:
{
if (lean_obj_tag(v_as_x27_4965_) == 0)
{
lean_object* v___x_4969_; 
v___x_4969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4969_, 0, v_b_4966_);
return v___x_4969_;
}
else
{
lean_object* v_head_4970_; lean_object* v_tail_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v_env_4974_; lean_object* v_nextMacroScope_4975_; lean_object* v_ngen_4976_; lean_object* v_auxDeclNGen_4977_; lean_object* v_traceState_4978_; lean_object* v_recordedDeps_4979_; lean_object* v_messages_4980_; lean_object* v_infoState_4981_; lean_object* v_snapshotTasks_4982_; lean_object* v___x_4984_; uint8_t v_isShared_4985_; uint8_t v_isSharedCheck_4993_; 
v_head_4970_ = lean_ctor_get(v_as_x27_4965_, 0);
v_tail_4971_ = lean_ctor_get(v_as_x27_4965_, 1);
v___x_4972_ = lean_box(0);
v___x_4973_ = lean_st_ref_take(v___y_4967_);
v_env_4974_ = lean_ctor_get(v___x_4973_, 0);
v_nextMacroScope_4975_ = lean_ctor_get(v___x_4973_, 1);
v_ngen_4976_ = lean_ctor_get(v___x_4973_, 2);
v_auxDeclNGen_4977_ = lean_ctor_get(v___x_4973_, 3);
v_traceState_4978_ = lean_ctor_get(v___x_4973_, 4);
v_recordedDeps_4979_ = lean_ctor_get(v___x_4973_, 6);
v_messages_4980_ = lean_ctor_get(v___x_4973_, 7);
v_infoState_4981_ = lean_ctor_get(v___x_4973_, 8);
v_snapshotTasks_4982_ = lean_ctor_get(v___x_4973_, 9);
v_isSharedCheck_4993_ = !lean_is_exclusive(v___x_4973_);
if (v_isSharedCheck_4993_ == 0)
{
lean_object* v_unused_4994_; 
v_unused_4994_ = lean_ctor_get(v___x_4973_, 5);
lean_dec(v_unused_4994_);
v___x_4984_ = v___x_4973_;
v_isShared_4985_ = v_isSharedCheck_4993_;
goto v_resetjp_4983_;
}
else
{
lean_inc(v_snapshotTasks_4982_);
lean_inc(v_infoState_4981_);
lean_inc(v_messages_4980_);
lean_inc(v_recordedDeps_4979_);
lean_inc(v_traceState_4978_);
lean_inc(v_auxDeclNGen_4977_);
lean_inc(v_ngen_4976_);
lean_inc(v_nextMacroScope_4975_);
lean_inc(v_env_4974_);
lean_dec(v___x_4973_);
v___x_4984_ = lean_box(0);
v_isShared_4985_ = v_isSharedCheck_4993_;
goto v_resetjp_4983_;
}
v_resetjp_4983_:
{
lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4989_; 
lean_inc(v_head_4970_);
v___x_4986_ = l_Lean_markMeta(v_env_4974_, v_head_4970_);
v___x_4987_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4985_ == 0)
{
lean_ctor_set(v___x_4984_, 5, v___x_4987_);
lean_ctor_set(v___x_4984_, 0, v___x_4986_);
v___x_4989_ = v___x_4984_;
goto v_reusejp_4988_;
}
else
{
lean_object* v_reuseFailAlloc_4992_; 
v_reuseFailAlloc_4992_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4992_, 0, v___x_4986_);
lean_ctor_set(v_reuseFailAlloc_4992_, 1, v_nextMacroScope_4975_);
lean_ctor_set(v_reuseFailAlloc_4992_, 2, v_ngen_4976_);
lean_ctor_set(v_reuseFailAlloc_4992_, 3, v_auxDeclNGen_4977_);
lean_ctor_set(v_reuseFailAlloc_4992_, 4, v_traceState_4978_);
lean_ctor_set(v_reuseFailAlloc_4992_, 5, v___x_4987_);
lean_ctor_set(v_reuseFailAlloc_4992_, 6, v_recordedDeps_4979_);
lean_ctor_set(v_reuseFailAlloc_4992_, 7, v_messages_4980_);
lean_ctor_set(v_reuseFailAlloc_4992_, 8, v_infoState_4981_);
lean_ctor_set(v_reuseFailAlloc_4992_, 9, v_snapshotTasks_4982_);
v___x_4989_ = v_reuseFailAlloc_4992_;
goto v_reusejp_4988_;
}
v_reusejp_4988_:
{
lean_object* v___x_4990_; 
v___x_4990_ = lean_st_ref_put(v___y_4967_, v___x_4989_);
v_as_x27_4965_ = v_tail_4971_;
v_b_4966_ = v___x_4972_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg___boxed(lean_object* v_as_x27_4995_, lean_object* v_b_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_){
_start:
{
lean_object* v_res_4999_; 
v_res_4999_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_4995_, v_b_4996_, v___y_4997_);
lean_dec(v___y_4997_);
lean_dec(v_as_x27_4995_);
return v_res_4999_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object* v_decl_5000_, uint8_t v_logCompileErrors_5001_, uint8_t v_markMeta_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_){
_start:
{
uint8_t v___x_5006_; lean_object* v___x_5007_; 
v___x_5006_ = 0;
lean_inc(v_decl_5000_);
v___x_5007_ = l_Lean_addDecl(v_decl_5000_, v___x_5006_, v_a_5003_, v_a_5004_);
if (lean_obj_tag(v___x_5007_) == 0)
{
lean_dec_ref_known(v___x_5007_, 1);
if (v_markMeta_5002_ == 0)
{
lean_object* v___x_5008_; 
v___x_5008_ = l_Lean_compileDecl(v_decl_5000_, v_logCompileErrors_5001_, v_a_5003_, v_a_5004_);
return v___x_5008_;
}
else
{
lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; 
lean_inc(v_decl_5000_);
v___x_5009_ = l_Lean_Declaration_getNames(v_decl_5000_);
v___x_5010_ = lean_box(0);
v___x_5011_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v___x_5009_, v___x_5010_, v_a_5004_);
lean_dec(v___x_5009_);
lean_dec_ref(v___x_5011_);
v___x_5012_ = l_Lean_compileDecl(v_decl_5000_, v_logCompileErrors_5001_, v_a_5003_, v_a_5004_);
return v___x_5012_;
}
}
else
{
lean_dec(v_decl_5000_);
return v___x_5007_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___boxed(lean_object* v_decl_5013_, lean_object* v_logCompileErrors_5014_, lean_object* v_markMeta_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_){
_start:
{
uint8_t v_logCompileErrors_boxed_5019_; uint8_t v_markMeta_boxed_5020_; lean_object* v_res_5021_; 
v_logCompileErrors_boxed_5019_ = lean_unbox(v_logCompileErrors_5014_);
v_markMeta_boxed_5020_ = lean_unbox(v_markMeta_5015_);
v_res_5021_ = l_Lean_addAndCompile(v_decl_5013_, v_logCompileErrors_boxed_5019_, v_markMeta_boxed_5020_, v_a_5016_, v_a_5017_);
lean_dec(v_a_5017_);
lean_dec_ref(v_a_5016_);
return v_res_5021_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(lean_object* v_as_5022_, lean_object* v_as_x27_5023_, lean_object* v_b_5024_, lean_object* v_a_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_){
_start:
{
lean_object* v___x_5029_; 
v___x_5029_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_5023_, v_b_5024_, v___y_5027_);
return v___x_5029_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___boxed(lean_object* v_as_5030_, lean_object* v_as_x27_5031_, lean_object* v_b_5032_, lean_object* v_a_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_){
_start:
{
lean_object* v_res_5037_; 
v_res_5037_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(v_as_5030_, v_as_x27_5031_, v_b_5032_, v_a_5033_, v___y_5034_, v___y_5035_);
lean_dec(v___y_5035_);
lean_dec_ref(v___y_5034_);
lean_dec(v_as_x27_5031_);
lean_dec(v_as_5030_);
return v_res_5037_;
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
