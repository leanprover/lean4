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
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Declaration_getNames(lean_object*);
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
extern lean_object* l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_recordOriginalConstKind(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_recordOriginalConstKind___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "exporting definition "};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__0 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__0_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " as axiom"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__2 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__2_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(uint8_t v_suppressElabErrors_391_, lean_object* v_x_392_){
_start:
{
if (lean_obj_tag(v_x_392_) == 1)
{
lean_object* v_pre_393_; 
v_pre_393_ = lean_ctor_get(v_x_392_, 0);
switch(lean_obj_tag(v_pre_393_))
{
case 1:
{
lean_object* v_pre_394_; 
v_pre_394_ = lean_ctor_get(v_pre_393_, 0);
switch(lean_obj_tag(v_pre_394_))
{
case 0:
{
lean_object* v_str_395_; lean_object* v_str_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v_str_395_ = lean_ctor_get(v_x_392_, 1);
v_str_396_ = lean_ctor_get(v_pre_393_, 1);
v___x_397_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__0));
v___x_398_ = lean_string_dec_eq(v_str_396_, v___x_397_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_399_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__1));
v___x_400_ = lean_string_dec_eq(v_str_396_, v___x_399_);
if (v___x_400_ == 0)
{
return v___x_400_;
}
else
{
lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_401_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__2));
v___x_402_ = lean_string_dec_eq(v_str_395_, v___x_401_);
if (v___x_402_ == 0)
{
return v___x_402_;
}
else
{
return v_suppressElabErrors_391_;
}
}
}
else
{
lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_403_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__3));
v___x_404_ = lean_string_dec_eq(v_str_395_, v___x_403_);
if (v___x_404_ == 0)
{
return v___x_404_;
}
else
{
return v_suppressElabErrors_391_;
}
}
}
case 1:
{
lean_object* v_pre_405_; 
v_pre_405_ = lean_ctor_get(v_pre_394_, 0);
if (lean_obj_tag(v_pre_405_) == 0)
{
lean_object* v_str_406_; lean_object* v_str_407_; lean_object* v_str_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v_str_406_ = lean_ctor_get(v_x_392_, 1);
v_str_407_ = lean_ctor_get(v_pre_393_, 1);
v_str_408_ = lean_ctor_get(v_pre_394_, 1);
v___x_409_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__4));
v___x_410_ = lean_string_dec_eq(v_str_408_, v___x_409_);
if (v___x_410_ == 0)
{
return v___x_410_;
}
else
{
lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_411_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__5));
v___x_412_ = lean_string_dec_eq(v_str_407_, v___x_411_);
if (v___x_412_ == 0)
{
return v___x_412_;
}
else
{
lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_413_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__6));
v___x_414_ = lean_string_dec_eq(v_str_406_, v___x_413_);
if (v___x_414_ == 0)
{
return v___x_414_;
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
uint8_t v___x_415_; 
v___x_415_ = 0;
return v___x_415_;
}
}
default: 
{
uint8_t v___x_416_; 
v___x_416_ = 0;
return v___x_416_;
}
}
}
case 0:
{
lean_object* v_str_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v_str_417_ = lean_ctor_get(v_x_392_, 1);
v___x_418_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__7));
v___x_419_ = lean_string_dec_eq(v_str_417_, v___x_418_);
if (v___x_419_ == 0)
{
return v___x_419_;
}
else
{
return v_suppressElabErrors_391_;
}
}
default: 
{
uint8_t v___x_420_; 
v___x_420_ = 0;
return v___x_420_;
}
}
}
else
{
uint8_t v___x_421_; 
v___x_421_ = 0;
return v___x_421_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed(lean_object* v_suppressElabErrors_422_, lean_object* v_x_423_){
_start:
{
uint8_t v_suppressElabErrors_boxed_424_; uint8_t v_res_425_; lean_object* v_r_426_; 
v_suppressElabErrors_boxed_424_ = lean_unbox(v_suppressElabErrors_422_);
v_res_425_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(v_suppressElabErrors_boxed_424_, v_x_423_);
lean_dec(v_x_423_);
v_r_426_ = lean_box(v_res_425_);
return v_r_426_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__0, &l_Lean_snapshotEnvLinterOptions___closed__0_once, _init_l_Lean_snapshotEnvLinterOptions___closed__0);
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
return v___x_428_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_429_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_430_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0);
v___x_431_ = lean_unsigned_to_nat(0u);
v___x_432_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
lean_ctor_set(v___x_432_, 2, v___x_431_);
lean_ctor_set(v___x_432_, 3, v___x_431_);
lean_ctor_set(v___x_432_, 4, v___x_430_);
lean_ctor_set(v___x_432_, 5, v___x_430_);
lean_ctor_set(v___x_432_, 6, v___x_430_);
lean_ctor_set(v___x_432_, 7, v___x_430_);
lean_ctor_set(v___x_432_, 8, v___x_430_);
lean_ctor_set(v___x_432_, 9, v___x_430_);
lean_ctor_set(v___x_432_, 10, v___x_430_);
lean_ctor_set(v___x_432_, 11, v___x_429_);
return v___x_432_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_433_ = lean_unsigned_to_nat(32u);
v___x_434_ = lean_mk_empty_array_with_capacity(v___x_433_);
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
return v___x_435_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3(void){
_start:
{
size_t v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_436_ = ((size_t)5ULL);
v___x_437_ = lean_unsigned_to_nat(0u);
v___x_438_ = lean_unsigned_to_nat(32u);
v___x_439_ = lean_mk_empty_array_with_capacity(v___x_438_);
v___x_440_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2);
v___x_441_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_441_, 0, v___x_440_);
lean_ctor_set(v___x_441_, 1, v___x_439_);
lean_ctor_set(v___x_441_, 2, v___x_437_);
lean_ctor_set(v___x_441_, 3, v___x_437_);
lean_ctor_set_usize(v___x_441_, 4, v___x_436_);
return v___x_441_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_442_ = lean_box(1);
v___x_443_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3);
v___x_444_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0);
v___x_445_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set(v___x_445_, 1, v___x_443_);
lean_ctor_set(v___x_445_, 2, v___x_442_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(lean_object* v_msgData_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v___x_450_; lean_object* v_toCold_451_; lean_object* v_env_452_; lean_object* v_options_453_; uint8_t v___x_454_; lean_object* v_env_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_450_ = lean_st_ref_get(v___y_448_);
v_toCold_451_ = lean_ctor_get(v___y_447_, 0);
v_env_452_ = lean_ctor_get(v___x_450_, 0);
lean_inc_ref(v_env_452_);
lean_dec(v___x_450_);
v_options_453_ = lean_ctor_get(v_toCold_451_, 2);
v___x_454_ = 0;
v_env_455_ = l_Lean_Environment_setRecordingDeps(v_env_452_, v___x_454_);
v___x_456_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1);
v___x_457_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
lean_inc_ref(v_options_453_);
v___x_458_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_458_, 0, v_env_455_);
lean_ctor_set(v___x_458_, 1, v___x_456_);
lean_ctor_set(v___x_458_, 2, v___x_457_);
lean_ctor_set(v___x_458_, 3, v_options_453_);
v___x_459_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v_msgData_446_);
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___boxed(lean_object* v_msgData_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msgData_461_, v___y_462_, v___y_463_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(lean_object* v_ref_467_, lean_object* v_msgData_468_, uint8_t v_severity_469_, uint8_t v_isSilent_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
uint8_t v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; uint8_t v___y_481_; lean_object* v_toCold_482_; lean_object* v___y_483_; lean_object* v___y_512_; lean_object* v___y_513_; uint8_t v___y_514_; lean_object* v___y_515_; uint8_t v___y_516_; lean_object* v___y_517_; uint8_t v___y_518_; lean_object* v___y_519_; lean_object* v___y_539_; uint8_t v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; uint8_t v___y_543_; uint8_t v___y_544_; lean_object* v___y_545_; uint8_t v___y_549_; uint8_t v___y_550_; uint8_t v___x_560_; uint8_t v___y_562_; uint8_t v___x_568_; 
v___x_560_ = 2;
v___x_568_ = l_Lean_instBEqMessageSeverity_beq(v_severity_469_, v___x_560_);
if (v___x_568_ == 0)
{
v___y_562_ = v___x_568_;
goto v___jp_561_;
}
else
{
uint8_t v___x_569_; 
lean_inc_ref(v_msgData_468_);
v___x_569_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_468_);
if (v___x_569_ == 0)
{
v___y_562_ = v___x_569_;
goto v___jp_561_;
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec_ref(v_msgData_468_);
v___x_570_ = lean_box(0);
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
return v___x_571_;
}
}
v___jp_474_:
{
lean_object* v_currNamespace_484_; lean_object* v_openDecls_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v_env_490_; lean_object* v_nextMacroScope_491_; lean_object* v_ngen_492_; lean_object* v_auxDeclNGen_493_; lean_object* v_traceState_494_; lean_object* v_cache_495_; lean_object* v_recordedDeps_496_; lean_object* v_messages_497_; lean_object* v_infoState_498_; lean_object* v_snapshotTasks_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_510_; 
v_currNamespace_484_ = lean_ctor_get(v_toCold_482_, 4);
v_openDecls_485_ = lean_ctor_get(v_toCold_482_, 5);
lean_inc(v_openDecls_485_);
lean_inc(v_currNamespace_484_);
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v_currNamespace_484_);
lean_ctor_set(v___x_486_, 1, v_openDecls_485_);
v___x_487_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v___y_476_);
lean_inc_ref(v___y_479_);
lean_inc_ref(v___y_478_);
v___x_488_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_488_, 0, v___y_478_);
lean_ctor_set(v___x_488_, 1, v___y_477_);
lean_ctor_set(v___x_488_, 2, v___y_480_);
lean_ctor_set(v___x_488_, 3, v___y_479_);
lean_ctor_set(v___x_488_, 4, v___x_487_);
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*5, v___y_481_);
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*5 + 1, v___y_475_);
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*5 + 2, v_isSilent_470_);
v___x_489_ = lean_st_ref_take(v___y_483_);
v_env_490_ = lean_ctor_get(v___x_489_, 0);
v_nextMacroScope_491_ = lean_ctor_get(v___x_489_, 1);
v_ngen_492_ = lean_ctor_get(v___x_489_, 2);
v_auxDeclNGen_493_ = lean_ctor_get(v___x_489_, 3);
v_traceState_494_ = lean_ctor_get(v___x_489_, 4);
v_cache_495_ = lean_ctor_get(v___x_489_, 5);
v_recordedDeps_496_ = lean_ctor_get(v___x_489_, 6);
v_messages_497_ = lean_ctor_get(v___x_489_, 7);
v_infoState_498_ = lean_ctor_get(v___x_489_, 8);
v_snapshotTasks_499_ = lean_ctor_get(v___x_489_, 9);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_510_ == 0)
{
v___x_501_ = v___x_489_;
v_isShared_502_ = v_isSharedCheck_510_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_snapshotTasks_499_);
lean_inc(v_infoState_498_);
lean_inc(v_messages_497_);
lean_inc(v_recordedDeps_496_);
lean_inc(v_cache_495_);
lean_inc(v_traceState_494_);
lean_inc(v_auxDeclNGen_493_);
lean_inc(v_ngen_492_);
lean_inc(v_nextMacroScope_491_);
lean_inc(v_env_490_);
lean_dec(v___x_489_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_510_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_503_ = lean_box(0);
v___x_504_ = l_Lean_MessageLog_add(v___x_488_, v_messages_497_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 7, v___x_504_);
v___x_506_ = v___x_501_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_env_490_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_nextMacroScope_491_);
lean_ctor_set(v_reuseFailAlloc_509_, 2, v_ngen_492_);
lean_ctor_set(v_reuseFailAlloc_509_, 3, v_auxDeclNGen_493_);
lean_ctor_set(v_reuseFailAlloc_509_, 4, v_traceState_494_);
lean_ctor_set(v_reuseFailAlloc_509_, 5, v_cache_495_);
lean_ctor_set(v_reuseFailAlloc_509_, 6, v_recordedDeps_496_);
lean_ctor_set(v_reuseFailAlloc_509_, 7, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_509_, 8, v_infoState_498_);
lean_ctor_set(v_reuseFailAlloc_509_, 9, v_snapshotTasks_499_);
v___x_506_ = v_reuseFailAlloc_509_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_st_ref_put(v___y_483_, v___x_506_);
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_503_);
return v___x_508_;
}
}
}
v___jp_511_:
{
lean_object* v_fileName_520_; lean_object* v_fileMap_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_537_; 
v_fileName_520_ = lean_ctor_get(v___y_517_, 0);
v_fileMap_521_ = lean_ctor_get(v___y_517_, 1);
v___x_522_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_468_);
v___x_523_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v___x_522_, v___y_471_, v___y_472_);
v_a_524_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_537_ == 0)
{
v___x_526_ = v___x_523_;
v_isShared_527_ = v_isSharedCheck_537_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_523_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_537_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
lean_inc_ref_n(v_fileMap_521_, 2);
v___x_528_ = l_Lean_FileMap_toPosition(v_fileMap_521_, v___y_515_);
lean_dec(v___y_515_);
v___x_529_ = l_Lean_FileMap_toPosition(v_fileMap_521_, v___y_519_);
lean_dec(v___y_519_);
v___x_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
v___x_531_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
if (v___y_516_ == 0)
{
lean_del_object(v___x_526_);
lean_dec_ref(v___y_513_);
v___y_475_ = v___y_514_;
v___y_476_ = v_a_524_;
v___y_477_ = v___x_528_;
v___y_478_ = v_fileName_520_;
v___y_479_ = v___x_531_;
v___y_480_ = v___x_530_;
v___y_481_ = v___y_518_;
v_toCold_482_ = v___y_512_;
v___y_483_ = v___y_472_;
goto v___jp_474_;
}
else
{
uint8_t v___x_532_; 
lean_inc(v_a_524_);
v___x_532_ = l_Lean_MessageData_hasTag(v___y_513_, v_a_524_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; lean_object* v___x_535_; 
lean_dec_ref_known(v___x_530_, 1);
lean_dec_ref(v___x_528_);
lean_dec(v_a_524_);
v___x_533_ = lean_box(0);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_533_);
v___x_535_ = v___x_526_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
else
{
lean_del_object(v___x_526_);
v___y_475_ = v___y_514_;
v___y_476_ = v_a_524_;
v___y_477_ = v___x_528_;
v___y_478_ = v_fileName_520_;
v___y_479_ = v___x_531_;
v___y_480_ = v___x_530_;
v___y_481_ = v___y_518_;
v_toCold_482_ = v___y_512_;
v___y_483_ = v___y_472_;
goto v___jp_474_;
}
}
}
}
v___jp_538_:
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_Syntax_getTailPos_x3f(v___y_542_, v___y_544_);
lean_dec(v___y_542_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_inc(v___y_545_);
v___y_512_ = v___y_539_;
v___y_513_ = v___y_541_;
v___y_514_ = v___y_543_;
v___y_515_ = v___y_545_;
v___y_516_ = v___y_540_;
v___y_517_ = v___y_539_;
v___y_518_ = v___y_544_;
v___y_519_ = v___y_545_;
goto v___jp_511_;
}
else
{
lean_object* v_val_547_; 
v_val_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_val_547_);
lean_dec_ref_known(v___x_546_, 1);
v___y_512_ = v___y_539_;
v___y_513_ = v___y_541_;
v___y_514_ = v___y_543_;
v___y_515_ = v___y_545_;
v___y_516_ = v___y_540_;
v___y_517_ = v___y_539_;
v___y_518_ = v___y_544_;
v___y_519_ = v_val_547_;
goto v___jp_511_;
}
}
v___jp_548_:
{
lean_object* v_toCold_551_; lean_object* v_ref_552_; uint8_t v_suppressElabErrors_553_; lean_object* v___x_554_; lean_object* v___f_555_; lean_object* v_ref_556_; lean_object* v___x_557_; 
v_toCold_551_ = lean_ctor_get(v___y_471_, 0);
v_ref_552_ = lean_ctor_get(v___y_471_, 2);
v_suppressElabErrors_553_ = lean_ctor_get_uint8(v___y_471_, sizeof(void*)*3 + 2);
v___x_554_ = lean_box(v_suppressElabErrors_553_);
v___f_555_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed), 2, 1);
lean_closure_set(v___f_555_, 0, v___x_554_);
v_ref_556_ = l_Lean_replaceRef(v_ref_467_, v_ref_552_);
v___x_557_ = l_Lean_Syntax_getPos_x3f(v_ref_556_, v___y_549_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v___x_558_; 
v___x_558_ = lean_unsigned_to_nat(0u);
v___y_539_ = v_toCold_551_;
v___y_540_ = v_suppressElabErrors_553_;
v___y_541_ = v___f_555_;
v___y_542_ = v_ref_556_;
v___y_543_ = v___y_550_;
v___y_544_ = v___y_549_;
v___y_545_ = v___x_558_;
goto v___jp_538_;
}
else
{
lean_object* v_val_559_; 
v_val_559_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_val_559_);
lean_dec_ref_known(v___x_557_, 1);
v___y_539_ = v_toCold_551_;
v___y_540_ = v_suppressElabErrors_553_;
v___y_541_ = v___f_555_;
v___y_542_ = v_ref_556_;
v___y_543_ = v___y_550_;
v___y_544_ = v___y_549_;
v___y_545_ = v_val_559_;
goto v___jp_538_;
}
}
v___jp_561_:
{
uint8_t v___x_563_; uint8_t v___x_564_; 
v___x_563_ = 1;
v___x_564_ = l_Lean_instBEqMessageSeverity_beq(v_severity_469_, v___x_563_);
if (v___x_564_ == 0)
{
v___y_549_ = v___y_562_;
v___y_550_ = v_severity_469_;
goto v___jp_548_;
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_565_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_471_);
v___x_566_ = l_Lean_warningAsError;
v___x_567_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_565_, v___x_566_);
lean_dec_ref(v___x_565_);
if (v___x_567_ == 0)
{
v___y_549_ = v___y_562_;
v___y_550_ = v_severity_469_;
goto v___jp_548_;
}
else
{
v___y_549_ = v___y_562_;
v___y_550_ = v___x_560_;
goto v___jp_548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___boxed(lean_object* v_ref_572_, lean_object* v_msgData_573_, lean_object* v_severity_574_, lean_object* v_isSilent_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
uint8_t v_severity_boxed_579_; uint8_t v_isSilent_boxed_580_; lean_object* v_res_581_; 
v_severity_boxed_579_ = lean_unbox(v_severity_574_);
v_isSilent_boxed_580_ = lean_unbox(v_isSilent_575_);
v_res_581_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_572_, v_msgData_573_, v_severity_boxed_579_, v_isSilent_boxed_580_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v_ref_572_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(lean_object* v_msgData_582_, uint8_t v_severity_583_, uint8_t v_isSilent_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v_ref_588_; lean_object* v___x_589_; 
v_ref_588_ = lean_ctor_get(v___y_585_, 2);
v___x_589_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_588_, v_msgData_582_, v_severity_583_, v_isSilent_584_, v___y_585_, v___y_586_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4___boxed(lean_object* v_msgData_590_, lean_object* v_severity_591_, lean_object* v_isSilent_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
uint8_t v_severity_boxed_596_; uint8_t v_isSilent_boxed_597_; lean_object* v_res_598_; 
v_severity_boxed_596_ = lean_unbox(v_severity_591_);
v_isSilent_boxed_597_ = lean_unbox(v_isSilent_592_);
v_res_598_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_590_, v_severity_boxed_596_, v_isSilent_boxed_597_, v___y_593_, v___y_594_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(lean_object* v_msgData_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
uint8_t v___x_603_; uint8_t v___x_604_; lean_object* v___x_605_; 
v___x_603_ = 1;
v___x_604_ = 0;
v___x_605_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_599_, v___x_603_, v___x_604_, v___y_600_, v___y_601_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2___boxed(lean_object* v_msgData_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v_msgData_606_, v___y_607_, v___y_608_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(lean_object* v_as_614_, size_t v_sz_615_, size_t v_i_616_, lean_object* v_b_617_){
_start:
{
uint8_t v___x_618_; 
v___x_618_ = lean_usize_dec_lt(v_i_616_, v_sz_615_);
if (v___x_618_ == 0)
{
lean_inc_ref(v_b_617_);
return v_b_617_;
}
else
{
lean_object* v_a_619_; lean_object* v_fst_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v_a_619_ = lean_array_uget_borrowed(v_as_614_, v_i_616_);
v_fst_620_ = lean_ctor_get(v_a_619_, 0);
v___x_621_ = lean_box(0);
v___x_622_ = lean_unbox(v_fst_620_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; size_t v___x_624_; size_t v___x_625_; 
v___x_623_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___closed__0));
v___x_624_ = ((size_t)1ULL);
v___x_625_ = lean_usize_add(v_i_616_, v___x_624_);
v_i_616_ = v___x_625_;
v_b_617_ = v___x_623_;
goto _start;
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
lean_inc(v_a_619_);
v___x_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_627_, 0, v_a_619_);
v___x_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v___x_621_);
return v___x_629_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___boxed(lean_object* v_as_630_, lean_object* v_sz_631_, lean_object* v_i_632_, lean_object* v_b_633_){
_start:
{
size_t v_sz_boxed_634_; size_t v_i_boxed_635_; lean_object* v_res_636_; 
v_sz_boxed_634_ = lean_unbox_usize(v_sz_631_);
lean_dec(v_sz_631_);
v_i_boxed_635_ = lean_unbox_usize(v_i_632_);
lean_dec(v_i_632_);
v_res_636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v_as_630_, v_sz_boxed_634_, v_i_boxed_635_, v_b_633_);
lean_dec_ref(v_b_633_);
lean_dec_ref(v_as_630_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(lean_object* v_fn_637_, lean_object* v_e_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_Expr_getSorry_x3f(v_e_638_);
if (lean_obj_tag(v___x_645_) == 1)
{
lean_object* v_val_646_; lean_object* v___x_647_; 
v_val_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_val_646_);
lean_dec_ref_known(v___x_645_, 1);
lean_inc(v___y_643_);
lean_inc_ref(v___y_642_);
lean_inc(v___y_641_);
lean_inc_ref(v___y_640_);
lean_inc(v___y_639_);
v___x_647_ = lean_apply_7(v_fn_637_, v_val_646_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, lean_box(0));
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_656_; 
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_656_ == 0)
{
lean_object* v_unused_657_; 
v_unused_657_ = lean_ctor_get(v___x_647_, 0);
lean_dec(v_unused_657_);
v___x_649_ = v___x_647_;
v_isShared_650_ = v_isSharedCheck_656_;
goto v_resetjp_648_;
}
else
{
lean_dec(v___x_647_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_656_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
uint8_t v___x_651_; lean_object* v___x_652_; lean_object* v___x_654_; 
v___x_651_ = 0;
v___x_652_ = lean_box(v___x_651_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_652_);
v___x_654_ = v___x_649_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_652_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
v_a_658_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_647_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_647_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
else
{
uint8_t v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
lean_dec(v___x_645_);
lean_dec_ref(v_fn_637_);
v___x_666_ = 1;
v___x_667_ = lean_box(v___x_666_);
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
return v___x_668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed(lean_object* v_fn_669_, lean_object* v_e_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(v_fn_669_, v_e_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v_e_670_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_object* v_00_u03b1_678_, lean_object* v_x_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_apply_1(v_x_679_, lean_box(0));
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v_00_u03b1_688_, lean_object* v_x_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(v_00_u03b1_688_, v_x_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(lean_object* v_k_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v_b_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v___x_706_; 
lean_inc(v___y_704_);
lean_inc_ref(v___y_703_);
lean_inc(v___y_702_);
lean_inc_ref(v___y_701_);
lean_inc(v___y_699_);
lean_inc(v___y_698_);
v___x_706_ = lean_apply_8(v_k_697_, v_b_700_, v___y_698_, v___y_699_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, lean_box(0));
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed(lean_object* v_k_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v_b_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(v_k_707_, v___y_708_, v___y_709_, v_b_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_709_);
lean_dec(v___y_708_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(lean_object* v_name_717_, lean_object* v_type_718_, lean_object* v_val_719_, lean_object* v_k_720_, uint8_t v_nondep_721_, uint8_t v_kind_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___f_730_; lean_object* v___x_731_; 
lean_inc(v___y_724_);
lean_inc(v___y_723_);
v___f_730_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_730_, 0, v_k_720_);
lean_closure_set(v___f_730_, 1, v___y_723_);
lean_closure_set(v___f_730_, 2, v___y_724_);
v___x_731_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_717_, v_type_718_, v_val_719_, v___f_730_, v_nondep_721_, v_kind_722_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
if (lean_obj_tag(v___x_731_) == 0)
{
return v___x_731_;
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_731_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_731_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg___boxed(lean_object* v_name_740_, lean_object* v_type_741_, lean_object* v_val_742_, lean_object* v_k_743_, lean_object* v_nondep_744_, lean_object* v_kind_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
uint8_t v_nondep_boxed_753_; uint8_t v_kind_boxed_754_; lean_object* v_res_755_; 
v_nondep_boxed_753_ = lean_unbox(v_nondep_744_);
v_kind_boxed_754_ = lean_unbox(v_kind_745_);
v_res_755_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_740_, v_type_741_, v_val_742_, v_k_743_, v_nondep_boxed_753_, v_kind_boxed_754_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec(v___y_746_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed(lean_object* v_fvars_756_, lean_object* v_f_757_, lean_object* v_body_758_, lean_object* v_x_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(v_fvars_756_, v_f_757_, v_body_758_, v_x_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec(v___y_760_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(lean_object* v_f_768_, lean_object* v_fvars_769_, lean_object* v_a_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
if (lean_obj_tag(v_a_770_) == 8)
{
lean_object* v_declName_778_; lean_object* v_type_779_; lean_object* v_value_780_; lean_object* v_body_781_; lean_object* v___f_782_; lean_object* v_d_783_; lean_object* v_v_784_; lean_object* v___x_785_; 
v_declName_778_ = lean_ctor_get(v_a_770_, 0);
lean_inc(v_declName_778_);
v_type_779_ = lean_ctor_get(v_a_770_, 1);
lean_inc_ref(v_type_779_);
v_value_780_ = lean_ctor_get(v_a_770_, 2);
lean_inc_ref(v_value_780_);
v_body_781_ = lean_ctor_get(v_a_770_, 3);
lean_inc_ref(v_body_781_);
lean_dec_ref_known(v_a_770_, 4);
lean_inc_ref_n(v_f_768_, 2);
lean_inc_ref(v_fvars_769_);
v___f_782_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed), 11, 3);
lean_closure_set(v___f_782_, 0, v_fvars_769_);
lean_closure_set(v___f_782_, 1, v_f_768_);
lean_closure_set(v___f_782_, 2, v_body_781_);
v_d_783_ = lean_expr_instantiate_rev(v_type_779_, v_fvars_769_);
lean_dec_ref(v_type_779_);
v_v_784_ = lean_expr_instantiate_rev(v_value_780_, v_fvars_769_);
lean_dec_ref(v_fvars_769_);
lean_dec_ref(v_value_780_);
lean_inc(v___y_776_);
lean_inc_ref(v___y_775_);
lean_inc(v___y_774_);
lean_inc_ref(v___y_773_);
lean_inc(v___y_772_);
lean_inc(v___y_771_);
lean_inc_ref(v_d_783_);
v___x_785_ = lean_apply_8(v_f_768_, v_d_783_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, lean_box(0));
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v___x_786_; 
lean_dec_ref_known(v___x_785_, 1);
lean_inc(v___y_776_);
lean_inc_ref(v___y_775_);
lean_inc(v___y_774_);
lean_inc_ref(v___y_773_);
lean_inc(v___y_772_);
lean_inc(v___y_771_);
lean_inc_ref(v_v_784_);
v___x_786_ = lean_apply_8(v_f_768_, v_v_784_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, lean_box(0));
if (lean_obj_tag(v___x_786_) == 0)
{
uint8_t v___x_787_; uint8_t v___x_788_; lean_object* v___x_789_; 
lean_dec_ref_known(v___x_786_, 1);
v___x_787_ = 0;
v___x_788_ = 0;
v___x_789_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_declName_778_, v_d_783_, v_v_784_, v___f_782_, v___x_787_, v___x_788_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
return v___x_789_;
}
else
{
lean_dec_ref(v_v_784_);
lean_dec_ref(v_d_783_);
lean_dec_ref(v___f_782_);
lean_dec(v_declName_778_);
return v___x_786_;
}
}
else
{
lean_dec_ref(v_v_784_);
lean_dec_ref(v_d_783_);
lean_dec_ref(v___f_782_);
lean_dec(v_declName_778_);
lean_dec_ref(v_f_768_);
return v___x_785_;
}
}
else
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = lean_expr_instantiate_rev(v_a_770_, v_fvars_769_);
lean_dec_ref(v_fvars_769_);
lean_dec_ref(v_a_770_);
lean_inc(v___y_776_);
lean_inc_ref(v___y_775_);
lean_inc(v___y_774_);
lean_inc_ref(v___y_773_);
lean_inc(v___y_772_);
lean_inc(v___y_771_);
v___x_791_ = lean_apply_8(v_f_768_, v___x_790_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, lean_box(0));
return v___x_791_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(lean_object* v_fvars_792_, lean_object* v_f_793_, lean_object* v_body_794_, lean_object* v_x_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_array_push(v_fvars_792_, v_x_795_);
v___x_804_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_793_, v___x_803_, v_body_794_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___boxed(lean_object* v_f_805_, lean_object* v_fvars_806_, lean_object* v_a_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_805_, v_fvars_806_, v_a_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec(v___y_808_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(lean_object* v_f_818_, lean_object* v_e_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_828_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_818_, v___x_827_, v_e_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___boxed(lean_object* v_f_829_, lean_object* v_e_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v_f_829_, v_e_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec(v___y_831_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(lean_object* v_name_839_, uint8_t v_bi_840_, lean_object* v_type_841_, lean_object* v_k_842_, uint8_t v_kind_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v___f_851_; lean_object* v___x_852_; 
lean_inc(v___y_845_);
lean_inc(v___y_844_);
v___f_851_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_851_, 0, v_k_842_);
lean_closure_set(v___f_851_, 1, v___y_844_);
lean_closure_set(v___f_851_, 2, v___y_845_);
v___x_852_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_839_, v_bi_840_, v_type_841_, v___f_851_, v_kind_843_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
if (lean_obj_tag(v___x_852_) == 0)
{
return v___x_852_;
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_852_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_852_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___boxed(lean_object* v_name_861_, lean_object* v_bi_862_, lean_object* v_type_863_, lean_object* v_k_864_, lean_object* v_kind_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
uint8_t v_bi_boxed_873_; uint8_t v_kind_boxed_874_; lean_object* v_res_875_; 
v_bi_boxed_873_ = lean_unbox(v_bi_862_);
v_kind_boxed_874_ = lean_unbox(v_kind_865_);
v_res_875_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_861_, v_bi_boxed_873_, v_type_863_, v_k_864_, v_kind_boxed_874_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec(v___y_866_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed(lean_object* v_fvars_876_, lean_object* v_f_877_, lean_object* v_body_878_, lean_object* v_x_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(v_fvars_876_, v_f_877_, v_body_878_, v_x_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec(v___y_880_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(lean_object* v_f_888_, lean_object* v_fvars_889_, lean_object* v_a_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
if (lean_obj_tag(v_a_890_) == 7)
{
lean_object* v_binderName_898_; lean_object* v_binderType_899_; lean_object* v_body_900_; uint8_t v_binderInfo_901_; lean_object* v___f_902_; lean_object* v_d_903_; lean_object* v___x_904_; 
v_binderName_898_ = lean_ctor_get(v_a_890_, 0);
lean_inc(v_binderName_898_);
v_binderType_899_ = lean_ctor_get(v_a_890_, 1);
lean_inc_ref(v_binderType_899_);
v_body_900_ = lean_ctor_get(v_a_890_, 2);
lean_inc_ref(v_body_900_);
v_binderInfo_901_ = lean_ctor_get_uint8(v_a_890_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_890_, 3);
lean_inc_ref(v_f_888_);
lean_inc_ref(v_fvars_889_);
v___f_902_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed), 11, 3);
lean_closure_set(v___f_902_, 0, v_fvars_889_);
lean_closure_set(v___f_902_, 1, v_f_888_);
lean_closure_set(v___f_902_, 2, v_body_900_);
v_d_903_ = lean_expr_instantiate_rev(v_binderType_899_, v_fvars_889_);
lean_dec_ref(v_fvars_889_);
lean_dec_ref(v_binderType_899_);
lean_inc(v___y_896_);
lean_inc_ref(v___y_895_);
lean_inc(v___y_894_);
lean_inc_ref(v___y_893_);
lean_inc(v___y_892_);
lean_inc(v___y_891_);
lean_inc_ref(v_d_903_);
v___x_904_ = lean_apply_8(v_f_888_, v_d_903_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, lean_box(0));
if (lean_obj_tag(v___x_904_) == 0)
{
uint8_t v___x_905_; lean_object* v___x_906_; 
lean_dec_ref_known(v___x_904_, 1);
v___x_905_ = 0;
v___x_906_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_898_, v_binderInfo_901_, v_d_903_, v___f_902_, v___x_905_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
return v___x_906_;
}
else
{
lean_dec_ref(v_d_903_);
lean_dec_ref(v___f_902_);
lean_dec(v_binderName_898_);
return v___x_904_;
}
}
else
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = lean_expr_instantiate_rev(v_a_890_, v_fvars_889_);
lean_dec_ref(v_fvars_889_);
lean_dec_ref(v_a_890_);
lean_inc(v___y_896_);
lean_inc_ref(v___y_895_);
lean_inc(v___y_894_);
lean_inc_ref(v___y_893_);
lean_inc(v___y_892_);
lean_inc(v___y_891_);
v___x_908_ = lean_apply_8(v_f_888_, v___x_907_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, lean_box(0));
return v___x_908_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(lean_object* v_fvars_909_, lean_object* v_f_910_, lean_object* v_body_911_, lean_object* v_x_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_array_push(v_fvars_909_, v_x_912_);
v___x_921_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_910_, v___x_920_, v_body_911_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___boxed(lean_object* v_f_922_, lean_object* v_fvars_923_, lean_object* v_a_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_922_, v_fvars_923_, v_a_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec(v___y_925_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(lean_object* v_f_933_, lean_object* v_e_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_943_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_933_, v___x_942_, v_e_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10___boxed(lean_object* v_f_944_, lean_object* v_e_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v_f_944_, v_e_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec(v___y_946_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed(lean_object* v_fvars_954_, lean_object* v_f_955_, lean_object* v_body_956_, lean_object* v_x_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(v_fvars_954_, v_f_955_, v_body_956_, v_x_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec(v___y_958_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(lean_object* v_f_966_, lean_object* v_fvars_967_, lean_object* v_a_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
if (lean_obj_tag(v_a_968_) == 6)
{
lean_object* v_binderName_976_; lean_object* v_binderType_977_; lean_object* v_body_978_; uint8_t v_binderInfo_979_; lean_object* v___f_980_; lean_object* v_d_981_; lean_object* v___x_982_; 
v_binderName_976_ = lean_ctor_get(v_a_968_, 0);
lean_inc(v_binderName_976_);
v_binderType_977_ = lean_ctor_get(v_a_968_, 1);
lean_inc_ref(v_binderType_977_);
v_body_978_ = lean_ctor_get(v_a_968_, 2);
lean_inc_ref(v_body_978_);
v_binderInfo_979_ = lean_ctor_get_uint8(v_a_968_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_968_, 3);
lean_inc_ref(v_f_966_);
lean_inc_ref(v_fvars_967_);
v___f_980_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed), 11, 3);
lean_closure_set(v___f_980_, 0, v_fvars_967_);
lean_closure_set(v___f_980_, 1, v_f_966_);
lean_closure_set(v___f_980_, 2, v_body_978_);
v_d_981_ = lean_expr_instantiate_rev(v_binderType_977_, v_fvars_967_);
lean_dec_ref(v_fvars_967_);
lean_dec_ref(v_binderType_977_);
lean_inc(v___y_974_);
lean_inc_ref(v___y_973_);
lean_inc(v___y_972_);
lean_inc_ref(v___y_971_);
lean_inc(v___y_970_);
lean_inc(v___y_969_);
lean_inc_ref(v_d_981_);
v___x_982_ = lean_apply_8(v_f_966_, v_d_981_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, lean_box(0));
if (lean_obj_tag(v___x_982_) == 0)
{
uint8_t v___x_983_; lean_object* v___x_984_; 
lean_dec_ref_known(v___x_982_, 1);
v___x_983_ = 0;
v___x_984_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_976_, v_binderInfo_979_, v_d_981_, v___f_980_, v___x_983_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
return v___x_984_;
}
else
{
lean_dec_ref(v_d_981_);
lean_dec_ref(v___f_980_);
lean_dec(v_binderName_976_);
return v___x_982_;
}
}
else
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_expr_instantiate_rev(v_a_968_, v_fvars_967_);
lean_dec_ref(v_fvars_967_);
lean_dec_ref(v_a_968_);
lean_inc(v___y_974_);
lean_inc_ref(v___y_973_);
lean_inc(v___y_972_);
lean_inc_ref(v___y_971_);
lean_inc(v___y_970_);
lean_inc(v___y_969_);
v___x_986_ = lean_apply_8(v_f_966_, v___x_985_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, lean_box(0));
return v___x_986_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(lean_object* v_fvars_987_, lean_object* v_f_988_, lean_object* v_body_989_, lean_object* v_x_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = lean_array_push(v_fvars_987_, v_x_990_);
v___x_999_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_988_, v___x_998_, v_body_989_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___boxed(lean_object* v_f_1000_, lean_object* v_fvars_1001_, lean_object* v_a_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_1000_, v_fvars_1001_, v_a_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec(v___y_1003_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(lean_object* v_f_1011_, lean_object* v_e_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_1021_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_1011_, v___x_1020_, v_e_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11___boxed(lean_object* v_f_1022_, lean_object* v_e_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v_f_1022_, v_e_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec(v___y_1024_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(lean_object* v_a_1032_, lean_object* v_x_1033_){
_start:
{
if (lean_obj_tag(v_x_1033_) == 0)
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_box(0);
return v___x_1034_;
}
else
{
lean_object* v_key_1035_; lean_object* v_value_1036_; lean_object* v_tail_1037_; uint8_t v___x_1038_; 
v_key_1035_ = lean_ctor_get(v_x_1033_, 0);
v_value_1036_ = lean_ctor_get(v_x_1033_, 1);
v_tail_1037_ = lean_ctor_get(v_x_1033_, 2);
v___x_1038_ = lean_expr_eqv(v_key_1035_, v_a_1032_);
if (v___x_1038_ == 0)
{
v_x_1033_ = v_tail_1037_;
goto _start;
}
else
{
lean_object* v___x_1040_; 
lean_inc(v_value_1036_);
v___x_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1040_, 0, v_value_1036_);
return v___x_1040_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_a_1041_, lean_object* v_x_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1041_, v_x_1042_);
lean_dec(v_x_1042_);
lean_dec_ref(v_a_1041_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_m_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v_buckets_1046_; lean_object* v___x_1047_; uint64_t v___x_1048_; uint64_t v___x_1049_; uint64_t v___x_1050_; uint64_t v_fold_1051_; uint64_t v___x_1052_; uint64_t v___x_1053_; uint64_t v___x_1054_; size_t v___x_1055_; size_t v___x_1056_; size_t v___x_1057_; size_t v___x_1058_; size_t v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v_buckets_1046_ = lean_ctor_get(v_m_1044_, 1);
v___x_1047_ = lean_array_get_size(v_buckets_1046_);
v___x_1048_ = l_Lean_Expr_hash(v_a_1045_);
v___x_1049_ = 32ULL;
v___x_1050_ = lean_uint64_shift_right(v___x_1048_, v___x_1049_);
v_fold_1051_ = lean_uint64_xor(v___x_1048_, v___x_1050_);
v___x_1052_ = 16ULL;
v___x_1053_ = lean_uint64_shift_right(v_fold_1051_, v___x_1052_);
v___x_1054_ = lean_uint64_xor(v_fold_1051_, v___x_1053_);
v___x_1055_ = lean_uint64_to_usize(v___x_1054_);
v___x_1056_ = lean_usize_of_nat(v___x_1047_);
v___x_1057_ = ((size_t)1ULL);
v___x_1058_ = lean_usize_sub(v___x_1056_, v___x_1057_);
v___x_1059_ = lean_usize_land(v___x_1055_, v___x_1058_);
v___x_1060_ = lean_array_uget_borrowed(v_buckets_1046_, v___x_1059_);
v___x_1061_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1045_, v___x_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_m_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1062_, v_a_1063_);
lean_dec_ref(v_a_1063_);
lean_dec_ref(v_m_1062_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_object* v_00_u03b1_1065_, lean_object* v_x_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_apply_1(v_x_1066_, lean_box(0));
v___x_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0___boxed(lean_object* v_00_u03b1_1075_, lean_object* v_x_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(v_00_u03b1_1075_, v_x_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(lean_object* v_x_1084_, lean_object* v_x_1085_){
_start:
{
if (lean_obj_tag(v_x_1085_) == 0)
{
return v_x_1084_;
}
else
{
lean_object* v_key_1086_; lean_object* v_value_1087_; lean_object* v_tail_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1111_; 
v_key_1086_ = lean_ctor_get(v_x_1085_, 0);
v_value_1087_ = lean_ctor_get(v_x_1085_, 1);
v_tail_1088_ = lean_ctor_get(v_x_1085_, 2);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_x_1085_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1090_ = v_x_1085_;
v_isShared_1091_ = v_isSharedCheck_1111_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_tail_1088_);
lean_inc(v_value_1087_);
lean_inc(v_key_1086_);
lean_dec(v_x_1085_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1111_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; uint64_t v___x_1093_; uint64_t v___x_1094_; uint64_t v___x_1095_; uint64_t v_fold_1096_; uint64_t v___x_1097_; uint64_t v___x_1098_; uint64_t v___x_1099_; size_t v___x_1100_; size_t v___x_1101_; size_t v___x_1102_; size_t v___x_1103_; size_t v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1107_; 
v___x_1092_ = lean_array_get_size(v_x_1084_);
v___x_1093_ = l_Lean_Expr_hash(v_key_1086_);
v___x_1094_ = 32ULL;
v___x_1095_ = lean_uint64_shift_right(v___x_1093_, v___x_1094_);
v_fold_1096_ = lean_uint64_xor(v___x_1093_, v___x_1095_);
v___x_1097_ = 16ULL;
v___x_1098_ = lean_uint64_shift_right(v_fold_1096_, v___x_1097_);
v___x_1099_ = lean_uint64_xor(v_fold_1096_, v___x_1098_);
v___x_1100_ = lean_uint64_to_usize(v___x_1099_);
v___x_1101_ = lean_usize_of_nat(v___x_1092_);
v___x_1102_ = ((size_t)1ULL);
v___x_1103_ = lean_usize_sub(v___x_1101_, v___x_1102_);
v___x_1104_ = lean_usize_land(v___x_1100_, v___x_1103_);
v___x_1105_ = lean_array_uget_borrowed(v_x_1084_, v___x_1104_);
lean_inc(v___x_1105_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 2, v___x_1105_);
v___x_1107_ = v___x_1090_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_key_1086_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_value_1087_);
lean_ctor_set(v_reuseFailAlloc_1110_, 2, v___x_1105_);
v___x_1107_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1108_; 
v___x_1108_ = lean_array_uset(v_x_1084_, v___x_1104_, v___x_1107_);
v_x_1084_ = v___x_1108_;
v_x_1085_ = v_tail_1088_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(lean_object* v_i_1112_, lean_object* v_source_1113_, lean_object* v_target_1114_){
_start:
{
lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1115_ = lean_array_get_size(v_source_1113_);
v___x_1116_ = lean_nat_dec_lt(v_i_1112_, v___x_1115_);
if (v___x_1116_ == 0)
{
lean_dec_ref(v_source_1113_);
lean_dec(v_i_1112_);
return v_target_1114_;
}
else
{
lean_object* v_es_1117_; lean_object* v___x_1118_; lean_object* v_source_1119_; lean_object* v_target_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v_es_1117_ = lean_array_fget(v_source_1113_, v_i_1112_);
v___x_1118_ = lean_box(0);
v_source_1119_ = lean_array_fset(v_source_1113_, v_i_1112_, v___x_1118_);
v_target_1120_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_target_1114_, v_es_1117_);
v___x_1121_ = lean_unsigned_to_nat(1u);
v___x_1122_ = lean_nat_add(v_i_1112_, v___x_1121_);
lean_dec(v_i_1112_);
v_i_1112_ = v___x_1122_;
v_source_1113_ = v_source_1119_;
v_target_1114_ = v_target_1120_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(lean_object* v_data_1124_){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v_nbuckets_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1125_ = lean_array_get_size(v_data_1124_);
v___x_1126_ = lean_unsigned_to_nat(2u);
v_nbuckets_1127_ = lean_nat_mul(v___x_1125_, v___x_1126_);
v___x_1128_ = lean_unsigned_to_nat(0u);
v___x_1129_ = lean_box(0);
v___x_1130_ = lean_mk_array(v_nbuckets_1127_, v___x_1129_);
v___x_1131_ = lean_array_propagate_mark(v_data_1124_, v___x_1130_);
v___x_1132_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v___x_1128_, v_data_1124_, v___x_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(lean_object* v_a_1133_, lean_object* v_b_1134_, lean_object* v_x_1135_){
_start:
{
if (lean_obj_tag(v_x_1135_) == 0)
{
lean_dec(v_b_1134_);
lean_dec_ref(v_a_1133_);
return v_x_1135_;
}
else
{
lean_object* v_key_1136_; lean_object* v_value_1137_; lean_object* v_tail_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1150_; 
v_key_1136_ = lean_ctor_get(v_x_1135_, 0);
v_value_1137_ = lean_ctor_get(v_x_1135_, 1);
v_tail_1138_ = lean_ctor_get(v_x_1135_, 2);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_x_1135_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1140_ = v_x_1135_;
v_isShared_1141_ = v_isSharedCheck_1150_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_tail_1138_);
lean_inc(v_value_1137_);
lean_inc(v_key_1136_);
lean_dec(v_x_1135_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1150_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
uint8_t v___x_1142_; 
v___x_1142_ = lean_expr_eqv(v_key_1136_, v_a_1133_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1143_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1133_, v_b_1134_, v_tail_1138_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 2, v___x_1143_);
v___x_1145_ = v___x_1140_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_key_1136_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_value_1137_);
lean_ctor_set(v_reuseFailAlloc_1146_, 2, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
else
{
lean_object* v___x_1148_; 
lean_dec(v_value_1137_);
lean_dec(v_key_1136_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 1, v_b_1134_);
lean_ctor_set(v___x_1140_, 0, v_a_1133_);
v___x_1148_ = v___x_1140_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1133_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_b_1134_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v_tail_1138_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(lean_object* v_a_1151_, lean_object* v_x_1152_){
_start:
{
if (lean_obj_tag(v_x_1152_) == 0)
{
uint8_t v___x_1153_; 
v___x_1153_ = 0;
return v___x_1153_;
}
else
{
lean_object* v_key_1154_; lean_object* v_tail_1155_; uint8_t v___x_1156_; 
v_key_1154_ = lean_ctor_get(v_x_1152_, 0);
v_tail_1155_ = lean_ctor_get(v_x_1152_, 2);
v___x_1156_ = lean_expr_eqv(v_key_1154_, v_a_1151_);
if (v___x_1156_ == 0)
{
v_x_1152_ = v_tail_1155_;
goto _start;
}
else
{
return v___x_1156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg___boxed(lean_object* v_a_1158_, lean_object* v_x_1159_){
_start:
{
uint8_t v_res_1160_; lean_object* v_r_1161_; 
v_res_1160_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1158_, v_x_1159_);
lean_dec(v_x_1159_);
lean_dec_ref(v_a_1158_);
v_r_1161_ = lean_box(v_res_1160_);
return v_r_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(lean_object* v_m_1162_, lean_object* v_a_1163_, lean_object* v_b_1164_){
_start:
{
lean_object* v_size_1165_; lean_object* v_buckets_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1209_; 
v_size_1165_ = lean_ctor_get(v_m_1162_, 0);
v_buckets_1166_ = lean_ctor_get(v_m_1162_, 1);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_m_1162_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1168_ = v_m_1162_;
v_isShared_1169_ = v_isSharedCheck_1209_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_buckets_1166_);
lean_inc(v_size_1165_);
lean_dec(v_m_1162_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1209_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1170_; uint64_t v___x_1171_; uint64_t v___x_1172_; uint64_t v___x_1173_; uint64_t v_fold_1174_; uint64_t v___x_1175_; uint64_t v___x_1176_; uint64_t v___x_1177_; size_t v___x_1178_; size_t v___x_1179_; size_t v___x_1180_; size_t v___x_1181_; size_t v___x_1182_; lean_object* v_bkt_1183_; uint8_t v___x_1184_; 
v___x_1170_ = lean_array_get_size(v_buckets_1166_);
v___x_1171_ = l_Lean_Expr_hash(v_a_1163_);
v___x_1172_ = 32ULL;
v___x_1173_ = lean_uint64_shift_right(v___x_1171_, v___x_1172_);
v_fold_1174_ = lean_uint64_xor(v___x_1171_, v___x_1173_);
v___x_1175_ = 16ULL;
v___x_1176_ = lean_uint64_shift_right(v_fold_1174_, v___x_1175_);
v___x_1177_ = lean_uint64_xor(v_fold_1174_, v___x_1176_);
v___x_1178_ = lean_uint64_to_usize(v___x_1177_);
v___x_1179_ = lean_usize_of_nat(v___x_1170_);
v___x_1180_ = ((size_t)1ULL);
v___x_1181_ = lean_usize_sub(v___x_1179_, v___x_1180_);
v___x_1182_ = lean_usize_land(v___x_1178_, v___x_1181_);
v_bkt_1183_ = lean_array_uget_borrowed(v_buckets_1166_, v___x_1182_);
v___x_1184_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1163_, v_bkt_1183_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; lean_object* v_size_x27_1186_; lean_object* v___x_1187_; lean_object* v_buckets_x27_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; uint8_t v___x_1194_; 
v___x_1185_ = lean_unsigned_to_nat(1u);
v_size_x27_1186_ = lean_nat_add(v_size_1165_, v___x_1185_);
lean_dec(v_size_1165_);
lean_inc(v_bkt_1183_);
v___x_1187_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1187_, 0, v_a_1163_);
lean_ctor_set(v___x_1187_, 1, v_b_1164_);
lean_ctor_set(v___x_1187_, 2, v_bkt_1183_);
v_buckets_x27_1188_ = lean_array_uset(v_buckets_1166_, v___x_1182_, v___x_1187_);
v___x_1189_ = lean_unsigned_to_nat(4u);
v___x_1190_ = lean_nat_mul(v_size_x27_1186_, v___x_1189_);
v___x_1191_ = lean_unsigned_to_nat(3u);
v___x_1192_ = lean_nat_div(v___x_1190_, v___x_1191_);
lean_dec(v___x_1190_);
v___x_1193_ = lean_array_get_size(v_buckets_x27_1188_);
v___x_1194_ = lean_nat_dec_le(v___x_1192_, v___x_1193_);
lean_dec(v___x_1192_);
if (v___x_1194_ == 0)
{
lean_object* v_val_1195_; lean_object* v___x_1197_; 
v_val_1195_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_buckets_x27_1188_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 1, v_val_1195_);
lean_ctor_set(v___x_1168_, 0, v_size_x27_1186_);
v___x_1197_ = v___x_1168_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_size_x27_1186_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v_val_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
else
{
lean_object* v___x_1200_; 
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 1, v_buckets_x27_1188_);
lean_ctor_set(v___x_1168_, 0, v_size_x27_1186_);
v___x_1200_ = v___x_1168_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_size_x27_1186_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_buckets_x27_1188_);
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
lean_object* v___x_1202_; lean_object* v_buckets_x27_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1207_; 
lean_inc(v_bkt_1183_);
v___x_1202_ = lean_box(0);
v_buckets_x27_1203_ = lean_array_uset(v_buckets_1166_, v___x_1182_, v___x_1202_);
v___x_1204_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1163_, v_b_1164_, v_bkt_1183_);
v___x_1205_ = lean_array_uset(v_buckets_x27_1203_, v___x_1182_, v___x_1204_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 1, v___x_1205_);
v___x_1207_ = v___x_1168_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_size_1165_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v___x_1205_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(lean_object* v_a_1210_, lean_object* v_e_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1214_ = lean_st_ref_take(v_a_1210_);
v___x_1215_ = lean_box(0);
v___x_1216_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v___x_1214_, v_e_1211_, v_a_1212_);
v___x_1217_ = lean_st_ref_put(v_a_1210_, v___x_1216_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed(lean_object* v_a_1218_, lean_object* v_e_1219_, lean_object* v_a_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(v_a_1218_, v_e_1219_, v_a_1220_);
lean_dec(v_a_1218_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1223_, lean_object* v_e_1224_, lean_object* v_a_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1223_, v_e_1224_, v_a_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec(v_a_1225_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(lean_object* v_fn_1233_, lean_object* v_e_1234_, lean_object* v_a_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v_a_1243_; lean_object* v___y_1255_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
lean_inc(v_a_1235_);
v___x_1257_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1257_, 0, lean_box(0));
lean_closure_set(v___x_1257_, 1, lean_box(0));
lean_closure_set(v___x_1257_, 2, v_a_1235_);
v___x_1258_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___x_1257_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1295_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1261_ = v___x_1258_;
v_isShared_1262_ = v_isSharedCheck_1295_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1258_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1295_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_a_1259_, v_e_1234_);
lean_dec(v_a_1259_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v___x_1264_; 
lean_del_object(v___x_1261_);
lean_inc_ref(v_fn_1233_);
lean_inc(v___y_1240_);
lean_inc_ref(v___y_1239_);
lean_inc(v___y_1238_);
lean_inc_ref(v___y_1237_);
lean_inc(v___y_1236_);
lean_inc_ref(v_e_1234_);
v___x_1264_ = lean_apply_7(v_fn_1233_, v_e_1234_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, lean_box(0));
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; uint8_t v___x_1266_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_a_1265_);
lean_dec_ref_known(v___x_1264_, 1);
v___x_1266_ = lean_unbox(v_a_1265_);
lean_dec(v_a_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; 
lean_dec_ref(v_fn_1233_);
v___x_1267_ = lean_box(0);
v_a_1243_ = v___x_1267_;
goto v___jp_1242_;
}
else
{
switch(lean_obj_tag(v_e_1234_))
{
case 7:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1268_, 0, v_fn_1233_);
lean_inc_ref(v_e_1234_);
v___x_1269_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v___x_1268_, v_e_1234_, v_a_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
v___y_1255_ = v___x_1269_;
goto v___jp_1254_;
}
case 6:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1270_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1270_, 0, v_fn_1233_);
lean_inc_ref(v_e_1234_);
v___x_1271_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v___x_1270_, v_e_1234_, v_a_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
v___y_1255_ = v___x_1271_;
goto v___jp_1254_;
}
case 8:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1272_, 0, v_fn_1233_);
lean_inc_ref(v_e_1234_);
v___x_1273_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v___x_1272_, v_e_1234_, v_a_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
v___y_1255_ = v___x_1273_;
goto v___jp_1254_;
}
case 5:
{
lean_object* v_fn_1274_; lean_object* v_arg_1275_; lean_object* v___x_1276_; 
v_fn_1274_ = lean_ctor_get(v_e_1234_, 0);
v_arg_1275_ = lean_ctor_get(v_e_1234_, 1);
lean_inc_ref(v_fn_1274_);
lean_inc_ref(v_fn_1233_);
v___x_1276_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1233_, v_fn_1274_, v_a_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v___x_1277_; 
lean_dec_ref_known(v___x_1276_, 1);
lean_inc_ref(v_arg_1275_);
v___x_1277_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1233_, v_arg_1275_, v_a_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
v___y_1255_ = v___x_1277_;
goto v___jp_1254_;
}
else
{
lean_dec_ref_known(v_e_1234_, 2);
lean_dec_ref(v_fn_1233_);
return v___x_1276_;
}
}
case 10:
{
lean_object* v_expr_1278_; lean_object* v___x_1279_; 
v_expr_1278_ = lean_ctor_get(v_e_1234_, 1);
lean_inc_ref(v_expr_1278_);
v___x_1279_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1233_, v_expr_1278_, v_a_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
v___y_1255_ = v___x_1279_;
goto v___jp_1254_;
}
case 11:
{
lean_object* v_struct_1280_; lean_object* v___x_1281_; 
v_struct_1280_ = lean_ctor_get(v_e_1234_, 2);
lean_inc_ref(v_struct_1280_);
v___x_1281_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1233_, v_struct_1280_, v_a_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
v___y_1255_ = v___x_1281_;
goto v___jp_1254_;
}
default: 
{
lean_object* v___x_1282_; 
lean_dec_ref(v_fn_1233_);
v___x_1282_ = lean_box(0);
v_a_1243_ = v___x_1282_;
goto v___jp_1242_;
}
}
}
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec_ref(v_e_1234_);
lean_dec_ref(v_fn_1233_);
v_a_1283_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1264_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1264_);
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
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_val_1291_; lean_object* v___x_1293_; 
lean_dec_ref(v_e_1234_);
lean_dec_ref(v_fn_1233_);
v_val_1291_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_val_1291_);
lean_dec_ref_known(v___x_1263_, 1);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 0, v_val_1291_);
v___x_1293_ = v___x_1261_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_val_1291_);
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
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec_ref(v_e_1234_);
lean_dec_ref(v_fn_1233_);
v_a_1296_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1258_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1258_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
v___jp_1242_:
{
lean_object* v___f_1244_; lean_object* v___x_1245_; 
lean_inc(v_a_1235_);
v___f_1244_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1244_, 0, v_a_1235_);
lean_closure_set(v___f_1244_, 1, v_e_1234_);
lean_closure_set(v___f_1244_, 2, v_a_1243_);
v___x_1245_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___f_1244_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1252_ == 0)
{
lean_object* v_unused_1253_; 
v_unused_1253_ = lean_ctor_get(v___x_1245_, 0);
lean_dec(v_unused_1253_);
v___x_1247_ = v___x_1245_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_dec(v___x_1245_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v_a_1243_);
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1243_);
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
return v___x_1245_;
}
}
v___jp_1254_:
{
if (lean_obj_tag(v___y_1255_) == 0)
{
lean_object* v_a_1256_; 
v_a_1256_ = lean_ctor_get(v___y_1255_, 0);
lean_inc(v_a_1256_);
lean_dec_ref_known(v___y_1255_, 1);
v_a_1243_ = v_a_1256_;
goto v___jp_1242_;
}
else
{
lean_dec_ref(v_e_1234_);
return v___y_1255_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1304_ = lean_box(0);
v___x_1305_ = lean_unsigned_to_nat(16u);
v___x_1306_ = lean_mk_array(v___x_1305_, v___x_1304_);
return v___x_1306_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1307_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0);
v___x_1308_ = lean_unsigned_to_nat(0u);
v___x_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
lean_ctor_set(v___x_1309_, 1, v___x_1307_);
return v___x_1309_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1);
v___x_1311_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1311_, 0, lean_box(0));
lean_closure_set(v___x_1311_, 1, lean_box(0));
lean_closure_set(v___x_1311_, 2, v___x_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(lean_object* v_input_1312_, lean_object* v_fn_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v_a_1322_; lean_object* v___x_1323_; 
v___x_1320_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2);
v___x_1321_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1320_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_a_1322_);
lean_dec_ref(v___x_1321_);
v___x_1323_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1313_, v_input_1312_, v_a_1322_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_a_1324_);
lean_dec_ref_known(v___x_1323_, 1);
v___x_1325_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1325_, 0, lean_box(0));
lean_closure_set(v___x_1325_, 1, lean_box(0));
lean_closure_set(v___x_1325_, 2, v_a_1322_);
v___x_1326_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1325_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1333_ == 0)
{
lean_object* v_unused_1334_; 
v_unused_1334_ = lean_ctor_get(v___x_1326_, 0);
lean_dec(v_unused_1334_);
v___x_1328_ = v___x_1326_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_dec(v___x_1326_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 0, v_a_1324_);
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1324_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
else
{
lean_dec(v_a_1322_);
return v___x_1323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___boxed(lean_object* v_input_1335_, lean_object* v_fn_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1335_, v_fn_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(lean_object* v_input_1344_, lean_object* v_fn_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v___f_1352_; lean_object* v___x_1353_; 
v___f_1352_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1352_, 0, v_fn_1345_);
v___x_1353_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1344_, v___f_1352_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___boxed(lean_object* v_input_1354_, lean_object* v_fn_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_input_1354_, v_fn_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(lean_object* v_fn_1363_, lean_object* v_x_1364_, lean_object* v_x_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
if (lean_obj_tag(v_x_1365_) == 0)
{
lean_object* v___x_1372_; 
lean_dec_ref(v_fn_1363_);
v___x_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1372_, 0, v_x_1364_);
return v___x_1372_;
}
else
{
lean_object* v_head_1373_; lean_object* v_tail_1374_; lean_object* v_type_1375_; lean_object* v___x_1376_; 
v_head_1373_ = lean_ctor_get(v_x_1365_, 0);
lean_inc(v_head_1373_);
v_tail_1374_ = lean_ctor_get(v_x_1365_, 1);
lean_inc(v_tail_1374_);
lean_dec_ref_known(v_x_1365_, 2);
v_type_1375_ = lean_ctor_get(v_head_1373_, 1);
lean_inc_ref(v_type_1375_);
lean_dec(v_head_1373_);
lean_inc_ref(v_fn_1363_);
v___x_1376_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1375_, v_fn_1363_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref_known(v___x_1376_, 1);
v_x_1364_ = v_a_1377_;
v_x_1365_ = v_tail_1374_;
goto _start;
}
else
{
lean_dec(v_tail_1374_);
lean_dec_ref(v_fn_1363_);
return v___x_1376_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4___boxed(lean_object* v_fn_1379_, lean_object* v_x_1380_, lean_object* v_x_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1379_, v_x_1380_, v_x_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(lean_object* v_fn_1389_, lean_object* v_x_1390_, lean_object* v_x_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
if (lean_obj_tag(v_x_1391_) == 0)
{
lean_object* v___x_1398_; 
lean_dec_ref(v_fn_1389_);
v___x_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1398_, 0, v_x_1390_);
return v___x_1398_;
}
else
{
lean_object* v_head_1399_; lean_object* v_tail_1400_; lean_object* v_type_1401_; lean_object* v_ctors_1402_; lean_object* v___x_1403_; 
v_head_1399_ = lean_ctor_get(v_x_1391_, 0);
lean_inc(v_head_1399_);
v_tail_1400_ = lean_ctor_get(v_x_1391_, 1);
lean_inc(v_tail_1400_);
lean_dec_ref_known(v_x_1391_, 2);
v_type_1401_ = lean_ctor_get(v_head_1399_, 1);
lean_inc_ref(v_type_1401_);
v_ctors_1402_ = lean_ctor_get(v_head_1399_, 2);
lean_inc(v_ctors_1402_);
lean_dec(v_head_1399_);
lean_inc_ref(v_fn_1389_);
v___x_1403_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1401_, v_fn_1389_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; lean_object* v___x_1405_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_a_1404_);
lean_dec_ref_known(v___x_1403_, 1);
lean_inc_ref(v_fn_1389_);
v___x_1405_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1389_, v_a_1404_, v_ctors_1402_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_a_1406_);
lean_dec_ref_known(v___x_1405_, 1);
v_x_1390_ = v_a_1406_;
v_x_1391_ = v_tail_1400_;
goto _start;
}
else
{
lean_dec(v_tail_1400_);
lean_dec_ref(v_fn_1389_);
return v___x_1405_;
}
}
else
{
lean_dec(v_ctors_1402_);
lean_dec(v_tail_1400_);
lean_dec_ref(v_fn_1389_);
return v___x_1403_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6___boxed(lean_object* v_fn_1408_, lean_object* v_x_1409_, lean_object* v_x_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1408_, v_x_1409_, v_x_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(lean_object* v_fn_1418_, lean_object* v_x_1419_, lean_object* v_x_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
if (lean_obj_tag(v_x_1420_) == 0)
{
lean_object* v___x_1427_; 
lean_dec_ref(v_fn_1418_);
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v_x_1419_);
return v___x_1427_;
}
else
{
lean_object* v_head_1428_; lean_object* v_toConstantVal_1429_; lean_object* v_tail_1430_; lean_object* v_value_1431_; lean_object* v_type_1432_; lean_object* v___x_1433_; 
v_head_1428_ = lean_ctor_get(v_x_1420_, 0);
lean_inc(v_head_1428_);
v_toConstantVal_1429_ = lean_ctor_get(v_head_1428_, 0);
lean_inc_ref(v_toConstantVal_1429_);
v_tail_1430_ = lean_ctor_get(v_x_1420_, 1);
lean_inc(v_tail_1430_);
lean_dec_ref_known(v_x_1420_, 2);
v_value_1431_ = lean_ctor_get(v_head_1428_, 1);
lean_inc_ref(v_value_1431_);
lean_dec(v_head_1428_);
v_type_1432_ = lean_ctor_get(v_toConstantVal_1429_, 2);
lean_inc_ref(v_type_1432_);
lean_dec_ref(v_toConstantVal_1429_);
lean_inc_ref(v_fn_1418_);
v___x_1433_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1432_, v_fn_1418_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v___x_1434_; 
lean_dec_ref_known(v___x_1433_, 1);
lean_inc_ref(v_fn_1418_);
v___x_1434_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1431_, v_fn_1418_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1435_);
lean_dec_ref_known(v___x_1434_, 1);
v_x_1419_ = v_a_1435_;
v_x_1420_ = v_tail_1430_;
goto _start;
}
else
{
lean_dec(v_tail_1430_);
lean_dec_ref(v_fn_1418_);
return v___x_1434_;
}
}
else
{
lean_dec_ref(v_value_1431_);
lean_dec(v_tail_1430_);
lean_dec_ref(v_fn_1418_);
return v___x_1433_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1437_, lean_object* v_x_1438_, lean_object* v_x_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1437_, v_x_1438_, v_x_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(lean_object* v_fn_1447_, lean_object* v_d_1448_, lean_object* v_a_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
switch(lean_obj_tag(v_d_1448_))
{
case 0:
{
lean_object* v_val_1456_; lean_object* v_toConstantVal_1457_; lean_object* v_type_1458_; lean_object* v___x_1459_; 
v_val_1456_ = lean_ctor_get(v_d_1448_, 0);
lean_inc_ref(v_val_1456_);
lean_dec_ref_known(v_d_1448_, 1);
v_toConstantVal_1457_ = lean_ctor_get(v_val_1456_, 0);
lean_inc_ref(v_toConstantVal_1457_);
lean_dec_ref(v_val_1456_);
v_type_1458_ = lean_ctor_get(v_toConstantVal_1457_, 2);
lean_inc_ref(v_type_1458_);
lean_dec_ref(v_toConstantVal_1457_);
v___x_1459_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1458_, v_fn_1447_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
return v___x_1459_;
}
case 4:
{
lean_object* v___x_1460_; 
lean_dec_ref(v_fn_1447_);
v___x_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1460_, 0, v_a_1449_);
return v___x_1460_;
}
case 5:
{
lean_object* v_defns_1461_; lean_object* v___x_1462_; 
v_defns_1461_ = lean_ctor_get(v_d_1448_, 0);
lean_inc(v_defns_1461_);
lean_dec_ref_known(v_d_1448_, 1);
v___x_1462_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1447_, v_a_1449_, v_defns_1461_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
return v___x_1462_;
}
case 6:
{
lean_object* v_types_1463_; lean_object* v___x_1464_; 
v_types_1463_ = lean_ctor_get(v_d_1448_, 2);
lean_inc(v_types_1463_);
lean_dec_ref_known(v_d_1448_, 3);
v___x_1464_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1447_, v_a_1449_, v_types_1463_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
return v___x_1464_;
}
default: 
{
lean_object* v_val_1465_; lean_object* v_toConstantVal_1466_; lean_object* v_value_1467_; lean_object* v_type_1468_; lean_object* v___x_1469_; 
v_val_1465_ = lean_ctor_get(v_d_1448_, 0);
lean_inc_ref(v_val_1465_);
lean_dec(v_d_1448_);
v_toConstantVal_1466_ = lean_ctor_get(v_val_1465_, 0);
lean_inc_ref(v_toConstantVal_1466_);
v_value_1467_ = lean_ctor_get(v_val_1465_, 1);
lean_inc_ref(v_value_1467_);
lean_dec_ref(v_val_1465_);
v_type_1468_ = lean_ctor_get(v_toConstantVal_1466_, 2);
lean_inc_ref(v_type_1468_);
lean_dec_ref(v_toConstantVal_1466_);
lean_inc_ref(v_fn_1447_);
v___x_1469_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1468_, v_fn_1447_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v___x_1470_; 
lean_dec_ref_known(v___x_1469_, 1);
v___x_1470_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1467_, v_fn_1447_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
return v___x_1470_;
}
else
{
lean_dec_ref(v_value_1467_);
lean_dec_ref(v_fn_1447_);
return v___x_1469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2___boxed(lean_object* v_fn_1471_, lean_object* v_d_1472_, lean_object* v_a_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1471_, v_d_1472_, v_a_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(lean_object* v_decl_1481_, lean_object* v_fn_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = lean_box(0);
v___x_1490_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1482_, v_decl_1481_, v___x_1489_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1___boxed(lean_object* v_decl_1491_, lean_object* v_fn_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1491_, v_fn_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
return v_res_1499_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__2(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__0, &l_Lean_snapshotEnvLinterOptions___closed__0_once, _init_l_Lean_snapshotEnvLinterOptions___closed__0);
v___x_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
return v___x_1504_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__3(void){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1505_ = lean_box(1);
v___x_1506_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3);
v___x_1507_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1508_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
lean_ctor_set(v___x_1508_, 1, v___x_1506_);
lean_ctor_set(v___x_1508_, 2, v___x_1505_);
return v___x_1508_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__4(void){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1509_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1510_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1511_ = lean_unsigned_to_nat(0u);
v___x_1512_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
lean_ctor_set(v___x_1512_, 1, v___x_1511_);
lean_ctor_set(v___x_1512_, 2, v___x_1511_);
lean_ctor_set(v___x_1512_, 3, v___x_1511_);
lean_ctor_set(v___x_1512_, 4, v___x_1510_);
lean_ctor_set(v___x_1512_, 5, v___x_1510_);
lean_ctor_set(v___x_1512_, 6, v___x_1510_);
lean_ctor_set(v___x_1512_, 7, v___x_1510_);
lean_ctor_set(v___x_1512_, 8, v___x_1510_);
lean_ctor_set(v___x_1512_, 9, v___x_1510_);
lean_ctor_set(v___x_1512_, 10, v___x_1510_);
lean_ctor_set(v___x_1512_, 11, v___x_1509_);
return v___x_1512_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__5(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1514_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
lean_ctor_set(v___x_1514_, 2, v___x_1513_);
lean_ctor_set(v___x_1514_, 3, v___x_1513_);
lean_ctor_set(v___x_1514_, 4, v___x_1513_);
lean_ctor_set(v___x_1514_, 5, v___x_1513_);
return v___x_1514_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__6(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
lean_ctor_set(v___x_1516_, 2, v___x_1515_);
lean_ctor_set(v___x_1516_, 3, v___x_1515_);
lean_ctor_set(v___x_1516_, 4, v___x_1515_);
return v___x_1516_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__7(void){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1517_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__6, &l_Lean_warnIfUsesSorry___closed__6_once, _init_l_Lean_warnIfUsesSorry___closed__6);
v___x_1518_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3);
v___x_1519_ = lean_box(1);
v___x_1520_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__5, &l_Lean_warnIfUsesSorry___closed__5_once, _init_l_Lean_warnIfUsesSorry___closed__5);
v___x_1521_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__4, &l_Lean_warnIfUsesSorry___closed__4_once, _init_l_Lean_warnIfUsesSorry___closed__4);
v___x_1522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
lean_ctor_set(v___x_1522_, 1, v___x_1520_);
lean_ctor_set(v___x_1522_, 2, v___x_1519_);
lean_ctor_set(v___x_1522_, 3, v___x_1518_);
lean_ctor_set(v___x_1522_, 4, v___x_1517_);
return v___x_1522_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__11(void){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1527_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__10));
v___x_1528_ = l_Lean_stringToMessageData(v___x_1527_);
return v___x_1528_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__13(void){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__12));
v___x_1531_ = l_Lean_stringToMessageData(v___x_1530_);
return v___x_1531_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__15(void){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__14));
v___x_1534_ = l_Lean_stringToMessageData(v___x_1533_);
return v___x_1534_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__16(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1535_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__15, &l_Lean_warnIfUsesSorry___closed__15_once, _init_l_Lean_warnIfUsesSorry___closed__15);
v___x_1536_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__9));
v___x_1537_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
lean_ctor_set(v___x_1537_, 1, v___x_1535_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry(lean_object* v_decl_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; uint8_t v___x_1547_; 
v___x_1545_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1542_);
v___x_1546_ = l_Lean_warn_sorry;
v___x_1547_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_1545_, v___x_1546_);
lean_dec_ref(v___x_1545_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_dec(v_decl_1541_);
v___x_1548_ = lean_box(0);
v___x_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
return v___x_1549_;
}
else
{
lean_object* v___f_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v_messages_1556_; uint8_t v___x_1557_; 
v___f_1550_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__0));
v___x_1551_ = lean_box(1);
v___x_1552_ = lean_st_ref_get(v_a_1543_);
v_messages_1556_ = lean_ctor_get(v___x_1552_, 7);
lean_inc_ref(v_messages_1556_);
lean_dec(v___x_1552_);
v___x_1557_ = l_Lean_MessageLog_hasErrors(v_messages_1556_);
lean_dec_ref(v_messages_1556_);
if (v___x_1557_ == 0)
{
uint8_t v___x_1558_; 
v___x_1558_ = l_Lean_Declaration_hasSorry(v_decl_1541_);
if (v___x_1558_ == 0)
{
lean_dec(v_decl_1541_);
goto v___jp_1553_;
}
else
{
lean_object* v___x_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; uint8_t v___x_1562_; uint8_t v___x_1563_; lean_object* v___x_1564_; uint64_t v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1559_ = lean_unsigned_to_nat(0u);
v___x_1560_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__1));
v___x_1561_ = 1;
v___x_1562_ = 0;
v___x_1563_ = 2;
v___x_1564_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_1564_, 0, v___x_1557_);
lean_ctor_set_uint8(v___x_1564_, 1, v___x_1557_);
lean_ctor_set_uint8(v___x_1564_, 2, v___x_1557_);
lean_ctor_set_uint8(v___x_1564_, 3, v___x_1557_);
lean_ctor_set_uint8(v___x_1564_, 4, v___x_1557_);
lean_ctor_set_uint8(v___x_1564_, 5, v___x_1558_);
lean_ctor_set_uint8(v___x_1564_, 6, v___x_1558_);
lean_ctor_set_uint8(v___x_1564_, 7, v___x_1557_);
lean_ctor_set_uint8(v___x_1564_, 8, v___x_1558_);
lean_ctor_set_uint8(v___x_1564_, 9, v___x_1561_);
lean_ctor_set_uint8(v___x_1564_, 10, v___x_1562_);
lean_ctor_set_uint8(v___x_1564_, 11, v___x_1558_);
lean_ctor_set_uint8(v___x_1564_, 12, v___x_1558_);
lean_ctor_set_uint8(v___x_1564_, 13, v___x_1558_);
lean_ctor_set_uint8(v___x_1564_, 14, v___x_1563_);
lean_ctor_set_uint8(v___x_1564_, 15, v___x_1558_);
lean_ctor_set_uint8(v___x_1564_, 16, v___x_1558_);
lean_ctor_set_uint8(v___x_1564_, 17, v___x_1558_);
lean_ctor_set_uint8(v___x_1564_, 18, v___x_1558_);
lean_ctor_set_uint8(v___x_1564_, 19, v___x_1557_);
v___x_1565_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1564_);
v___x_1566_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1566_, 0, v___x_1564_);
lean_ctor_set_uint64(v___x_1566_, sizeof(void*)*1, v___x_1565_);
v___x_1567_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__3, &l_Lean_warnIfUsesSorry___closed__3_once, _init_l_Lean_warnIfUsesSorry___closed__3);
v___x_1568_ = lean_box(0);
v___x_1569_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1569_, 0, v___x_1566_);
lean_ctor_set(v___x_1569_, 1, v___x_1551_);
lean_ctor_set(v___x_1569_, 2, v___x_1567_);
lean_ctor_set(v___x_1569_, 3, v___x_1560_);
lean_ctor_set(v___x_1569_, 4, v___x_1568_);
lean_ctor_set(v___x_1569_, 5, v___x_1559_);
lean_ctor_set(v___x_1569_, 6, v___x_1568_);
lean_ctor_set_uint8(v___x_1569_, sizeof(void*)*7, v___x_1557_);
lean_ctor_set_uint8(v___x_1569_, sizeof(void*)*7 + 1, v___x_1557_);
lean_ctor_set_uint8(v___x_1569_, sizeof(void*)*7 + 2, v___x_1557_);
lean_ctor_set_uint8(v___x_1569_, sizeof(void*)*7 + 3, v___x_1547_);
v___x_1570_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__7, &l_Lean_warnIfUsesSorry___closed__7_once, _init_l_Lean_warnIfUsesSorry___closed__7);
v___x_1571_ = lean_st_mk_ref(v___x_1570_);
v___x_1572_ = lean_st_mk_ref(v___x_1560_);
v___x_1573_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1541_, v___f_1550_, v___x_1572_, v___x_1569_, v___x_1571_, v_a_1542_, v_a_1543_);
lean_dec_ref_known(v___x_1569_, 7);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v_val_1577_; lean_object* v___x_1599_; size_t v_sz_1600_; size_t v___x_1601_; lean_object* v___x_1602_; lean_object* v_fst_1603_; 
lean_dec_ref_known(v___x_1573_, 1);
v___x_1574_ = lean_st_ref_get(v___x_1572_);
lean_dec(v___x_1572_);
v___x_1575_ = lean_st_ref_get(v___x_1571_);
lean_dec(v___x_1571_);
lean_dec(v___x_1575_);
v___x_1599_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__17));
v_sz_1600_ = lean_array_size(v___x_1574_);
v___x_1601_ = ((size_t)0ULL);
v___x_1602_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v___x_1574_, v_sz_1600_, v___x_1601_, v___x_1599_);
v_fst_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_fst_1603_);
lean_dec_ref(v___x_1602_);
if (lean_obj_tag(v_fst_1603_) == 0)
{
goto v___jp_1593_;
}
else
{
lean_object* v_val_1604_; 
v_val_1604_ = lean_ctor_get(v_fst_1603_, 0);
lean_inc(v_val_1604_);
lean_dec_ref_known(v_fst_1603_, 1);
if (lean_obj_tag(v_val_1604_) == 0)
{
goto v___jp_1593_;
}
else
{
lean_object* v_val_1605_; 
lean_dec(v___x_1574_);
v_val_1605_ = lean_ctor_get(v_val_1604_, 0);
lean_inc(v_val_1605_);
lean_dec_ref_known(v_val_1604_, 1);
v_val_1577_ = v_val_1605_;
goto v___jp_1576_;
}
}
v___jp_1576_:
{
lean_object* v_snd_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1591_; 
v_snd_1578_ = lean_ctor_get(v_val_1577_, 1);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_val_1577_);
if (v_isSharedCheck_1591_ == 0)
{
lean_object* v_unused_1592_; 
v_unused_1592_ = lean_ctor_get(v_val_1577_, 0);
lean_dec(v_unused_1592_);
v___x_1580_ = v_val_1577_;
v_isShared_1581_ = v_isSharedCheck_1591_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_snd_1578_);
lean_dec(v_val_1577_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1591_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1585_; 
v___x_1582_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__9));
v___x_1583_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__11, &l_Lean_warnIfUsesSorry___closed__11_once, _init_l_Lean_warnIfUsesSorry___closed__11);
if (v_isShared_1581_ == 0)
{
lean_ctor_set_tag(v___x_1580_, 7);
lean_ctor_set(v___x_1580_, 0, v___x_1583_);
v___x_1585_ = v___x_1580_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1583_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_snd_1578_);
v___x_1585_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1586_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__13, &l_Lean_warnIfUsesSorry___closed__13_once, _init_l_Lean_warnIfUsesSorry___closed__13);
v___x_1587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1585_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
v___x_1588_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1582_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1588_, v_a_1542_, v_a_1543_);
return v___x_1589_;
}
}
}
v___jp_1593_:
{
lean_object* v___x_1594_; uint8_t v___x_1595_; 
v___x_1594_ = lean_array_get_size(v___x_1574_);
v___x_1595_ = lean_nat_dec_lt(v___x_1559_, v___x_1594_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
lean_dec(v___x_1574_);
v___x_1596_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__16, &l_Lean_warnIfUsesSorry___closed__16_once, _init_l_Lean_warnIfUsesSorry___closed__16);
v___x_1597_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1596_, v_a_1542_, v_a_1543_);
return v___x_1597_;
}
else
{
lean_object* v___x_1598_; 
v___x_1598_ = lean_array_fget(v___x_1574_, v___x_1559_);
lean_dec(v___x_1574_);
v_val_1577_ = v___x_1598_;
goto v___jp_1576_;
}
}
}
else
{
lean_dec(v___x_1572_);
lean_dec(v___x_1571_);
return v___x_1573_;
}
}
}
else
{
lean_dec(v_decl_1541_);
goto v___jp_1553_;
}
v___jp_1553_:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = lean_box(0);
v___x_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
return v___x_1555_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___boxed(lean_object* v_decl_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_warnIfUsesSorry(v_decl_1606_, v_a_1607_, v_a_1608_);
lean_dec(v_a_1608_);
lean_dec_ref(v_a_1607_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1611_, lean_object* v_m_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1612_, v_a_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1615_, lean_object* v_m_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(v_00_u03b2_1615_, v_m_1616_, v_a_1617_);
lean_dec_ref(v_a_1617_);
lean_dec_ref(v_m_1616_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_1619_, lean_object* v_m_1620_, lean_object* v_a_1621_, lean_object* v_b_1622_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_m_1620_, v_a_1621_, v_b_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_1624_, lean_object* v_a_1625_, lean_object* v_x_1626_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1625_, v_x_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1628_, lean_object* v_a_1629_, lean_object* v_x_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(v_00_u03b2_1628_, v_a_1629_, v_x_1630_);
lean_dec(v_x_1630_);
lean_dec_ref(v_a_1629_);
return v_res_1631_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(lean_object* v_00_u03b2_1632_, lean_object* v_a_1633_, lean_object* v_x_1634_){
_start:
{
uint8_t v___x_1635_; 
v___x_1635_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1633_, v_x_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___boxed(lean_object* v_00_u03b2_1636_, lean_object* v_a_1637_, lean_object* v_x_1638_){
_start:
{
uint8_t v_res_1639_; lean_object* v_r_1640_; 
v_res_1639_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(v_00_u03b2_1636_, v_a_1637_, v_x_1638_);
lean_dec(v_x_1638_);
lean_dec_ref(v_a_1637_);
v_r_1640_ = lean_box(v_res_1639_);
return v_r_1640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17(lean_object* v_00_u03b2_1641_, lean_object* v_data_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_data_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18(lean_object* v_00_u03b2_1644_, lean_object* v_a_1645_, lean_object* v_b_1646_, lean_object* v_x_1647_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1645_, v_b_1646_, v_x_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(lean_object* v_00_u03b1_1649_, lean_object* v_name_1650_, uint8_t v_bi_1651_, lean_object* v_type_1652_, lean_object* v_k_1653_, uint8_t v_kind_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_1650_, v_bi_1651_, v_type_1652_, v_k_1653_, v_kind_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___boxed(lean_object* v_00_u03b1_1663_, lean_object* v_name_1664_, lean_object* v_bi_1665_, lean_object* v_type_1666_, lean_object* v_k_1667_, lean_object* v_kind_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
uint8_t v_bi_boxed_1676_; uint8_t v_kind_boxed_1677_; lean_object* v_res_1678_; 
v_bi_boxed_1676_ = lean_unbox(v_bi_1665_);
v_kind_boxed_1677_ = lean_unbox(v_kind_1668_);
v_res_1678_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(v_00_u03b1_1663_, v_name_1664_, v_bi_boxed_1676_, v_type_1666_, v_k_1667_, v_kind_boxed_1677_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec(v___y_1669_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(lean_object* v_00_u03b1_1679_, lean_object* v_name_1680_, lean_object* v_type_1681_, lean_object* v_val_1682_, lean_object* v_k_1683_, uint8_t v_nondep_1684_, uint8_t v_kind_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_1680_, v_type_1681_, v_val_1682_, v_k_1683_, v_nondep_1684_, v_kind_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___boxed(lean_object* v_00_u03b1_1694_, lean_object* v_name_1695_, lean_object* v_type_1696_, lean_object* v_val_1697_, lean_object* v_k_1698_, lean_object* v_nondep_1699_, lean_object* v_kind_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
uint8_t v_nondep_boxed_1708_; uint8_t v_kind_boxed_1709_; lean_object* v_res_1710_; 
v_nondep_boxed_1708_ = lean_unbox(v_nondep_1699_);
v_kind_boxed_1709_ = lean_unbox(v_kind_1700_);
v_res_1710_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(v_00_u03b1_1694_, v_name_1695_, v_type_1696_, v_val_1697_, v_k_1698_, v_nondep_boxed_1708_, v_kind_boxed_1709_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec(v___y_1701_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18(lean_object* v_00_u03b2_1711_, lean_object* v_i_1712_, lean_object* v_source_1713_, lean_object* v_target_1714_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v_i_1712_, v_source_1713_, v_target_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22(lean_object* v_00_u03b2_1716_, lean_object* v_x_1717_, lean_object* v_x_1718_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_x_1717_, v_x_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1769_; uint8_t v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1769_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1770_ = 0;
v___x_1771_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__20_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1772_ = l_Lean_registerTraceClass(v___x_1769_, v___x_1770_, v___x_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2____boxed(lean_object* v_a_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_();
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordOriginalConstKind(lean_object* v_env_1775_, lean_object* v_declName_1776_, uint8_t v_kind_1777_){
_start:
{
lean_object* v___x_1778_; uint8_t v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1778_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_1779_ = 0;
v___x_1780_ = lean_box(v_kind_1777_);
v___x_1781_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1778_, v_env_1775_, v_declName_1776_, v___x_1780_, v___x_1779_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordOriginalConstKind___boxed(lean_object* v_env_1782_, lean_object* v_declName_1783_, lean_object* v_kind_1784_){
_start:
{
uint8_t v_kind_boxed_1785_; lean_object* v_res_1786_; 
v_kind_boxed_1785_ = lean_unbox(v_kind_1784_);
v_res_1786_ = l_Lean_recordOriginalConstKind(v_env_1782_, v_declName_1783_, v_kind_boxed_1785_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(lean_object* v_env_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v___x_1790_; lean_object* v_nextMacroScope_1791_; lean_object* v_ngen_1792_; lean_object* v_auxDeclNGen_1793_; lean_object* v_traceState_1794_; lean_object* v_recordedDeps_1795_; lean_object* v_messages_1796_; lean_object* v_infoState_1797_; lean_object* v_snapshotTasks_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1809_; 
v___x_1790_ = lean_st_ref_take(v___y_1788_);
v_nextMacroScope_1791_ = lean_ctor_get(v___x_1790_, 1);
v_ngen_1792_ = lean_ctor_get(v___x_1790_, 2);
v_auxDeclNGen_1793_ = lean_ctor_get(v___x_1790_, 3);
v_traceState_1794_ = lean_ctor_get(v___x_1790_, 4);
v_recordedDeps_1795_ = lean_ctor_get(v___x_1790_, 6);
v_messages_1796_ = lean_ctor_get(v___x_1790_, 7);
v_infoState_1797_ = lean_ctor_get(v___x_1790_, 8);
v_snapshotTasks_1798_ = lean_ctor_get(v___x_1790_, 9);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1809_ == 0)
{
lean_object* v_unused_1810_; lean_object* v_unused_1811_; 
v_unused_1810_ = lean_ctor_get(v___x_1790_, 5);
lean_dec(v_unused_1810_);
v_unused_1811_ = lean_ctor_get(v___x_1790_, 0);
lean_dec(v_unused_1811_);
v___x_1800_ = v___x_1790_;
v_isShared_1801_ = v_isSharedCheck_1809_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_snapshotTasks_1798_);
lean_inc(v_infoState_1797_);
lean_inc(v_messages_1796_);
lean_inc(v_recordedDeps_1795_);
lean_inc(v_traceState_1794_);
lean_inc(v_auxDeclNGen_1793_);
lean_inc(v_ngen_1792_);
lean_inc(v_nextMacroScope_1791_);
lean_dec(v___x_1790_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1809_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1805_; 
v___x_1802_ = lean_box(0);
v___x_1803_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 5, v___x_1803_);
lean_ctor_set(v___x_1800_, 0, v_env_1787_);
v___x_1805_ = v___x_1800_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_env_1787_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_nextMacroScope_1791_);
lean_ctor_set(v_reuseFailAlloc_1808_, 2, v_ngen_1792_);
lean_ctor_set(v_reuseFailAlloc_1808_, 3, v_auxDeclNGen_1793_);
lean_ctor_set(v_reuseFailAlloc_1808_, 4, v_traceState_1794_);
lean_ctor_set(v_reuseFailAlloc_1808_, 5, v___x_1803_);
lean_ctor_set(v_reuseFailAlloc_1808_, 6, v_recordedDeps_1795_);
lean_ctor_set(v_reuseFailAlloc_1808_, 7, v_messages_1796_);
lean_ctor_set(v_reuseFailAlloc_1808_, 8, v_infoState_1797_);
lean_ctor_set(v_reuseFailAlloc_1808_, 9, v_snapshotTasks_1798_);
v___x_1805_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = lean_st_ref_put(v___y_1788_, v___x_1805_);
v___x_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1802_);
return v___x_1807_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg___boxed(lean_object* v_env_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1812_, v___y_1813_);
lean_dec(v___y_1813_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(lean_object* v_env_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1816_, v___y_1818_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___boxed(lean_object* v_env_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(v_env_1821_, v___y_1822_, v___y_1823_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
return v_res_1825_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1826_ = lean_box(0);
v___x_1827_ = l_Lean_interruptExceptionId;
v___x_1828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
lean_ctor_set(v___x_1828_, 1, v___x_1826_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg(){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1830_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v___y_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(lean_object* v_msg_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v_ref_1838_; lean_object* v___x_1839_; lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1848_; 
v_ref_1838_ = lean_ctor_get(v___y_1835_, 2);
v___x_1839_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_1834_, v___y_1835_, v___y_1836_);
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1842_ = v___x_1839_;
v_isShared_1843_ = v_isSharedCheck_1848_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1848_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1844_; lean_object* v___x_1846_; 
lean_inc(v_ref_1838_);
v___x_1844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1844_, 0, v_ref_1838_);
lean_ctor_set(v___x_1844_, 1, v_a_1840_);
if (v_isShared_1843_ == 0)
{
lean_ctor_set_tag(v___x_1842_, 1);
lean_ctor_set(v___x_1842_, 0, v___x_1844_);
v___x_1846_ = v___x_1842_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1844_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msg_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_1849_, v___y_1850_, v___y_1851_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(lean_object* v_ex_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v___y_1859_; lean_object* v___y_1860_; 
if (lean_obj_tag(v_ex_1854_) == 16)
{
lean_object* v___x_1864_; lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
v___x_1864_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1864_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1864_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1865_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
else
{
v___y_1859_ = v___y_1855_;
v___y_1860_ = v___y_1856_;
goto v___jp_1858_;
}
v___jp_1858_:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1861_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1859_);
v___x_1862_ = l_Lean_Kernel_Exception_toMessageData(v_ex_1854_, v___x_1861_);
v___x_1863_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v___x_1862_, v___y_1859_, v___y_1860_);
return v___x_1863_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg___boxed(lean_object* v_ex_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_1873_, v___y_1874_, v___y_1875_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(lean_object* v_x_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
if (lean_obj_tag(v_x_1878_) == 0)
{
lean_object* v_a_1882_; lean_object* v___x_1883_; 
v_a_1882_ = lean_ctor_get(v_x_1878_, 0);
lean_inc(v_a_1882_);
lean_dec_ref_known(v_x_1878_, 1);
v___x_1883_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_a_1882_, v___y_1879_, v___y_1880_);
return v___x_1883_;
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
v_a_1884_ = lean_ctor_get(v_x_1878_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v_x_1878_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v_x_1878_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v_x_1878_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
lean_ctor_set_tag(v___x_1886_, 0);
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg___boxed(lean_object* v_x_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_1892_, v___y_1893_, v___y_1894_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
return v_res_1896_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = lean_unsigned_to_nat(1u);
v___x_1904_ = l_Lean_Level_ofNat(v___x_1903_);
return v___x_1904_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1905_ = lean_box(0);
v___x_1906_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3);
v___x_1907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
lean_ctor_set(v___x_1907_, 1, v___x_1905_);
return v___x_1907_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1908_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4);
v___x_1909_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2));
v___x_1910_ = l_Lean_mkConst(v___x_1909_, v___x_1908_);
return v___x_1910_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1911_ = lean_unsigned_to_nat(0u);
v___x_1912_ = l_Lean_Level_ofNat(v___x_1911_);
return v___x_1912_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1913_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6);
v___x_1914_ = l_Lean_mkSort(v___x_1913_);
return v___x_1914_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11(void){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1920_ = lean_box(0);
v___x_1921_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__10));
v___x_1922_ = l_Lean_mkConst(v___x_1921_, v___x_1920_);
return v___x_1922_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12(void){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1923_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11);
v___x_1924_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7);
v___x_1925_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5);
v___x_1926_ = l_Lean_mkAppB(v___x_1925_, v___x_1924_, v___x_1923_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(lean_object* v_as_x27_1932_, lean_object* v_b_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
if (lean_obj_tag(v_as_x27_1932_) == 0)
{
lean_object* v___x_1937_; 
v___x_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1937_, 0, v_b_1933_);
return v___x_1937_;
}
else
{
lean_object* v_head_1938_; lean_object* v_tail_1939_; lean_object* v___x_1940_; lean_object* v_a_1942_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; uint8_t v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v_toCold_1955_; lean_object* v_env_1956_; lean_object* v_cancelTk_x3f_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
lean_dec_ref(v_b_1933_);
v_head_1938_ = lean_ctor_get(v_as_x27_1932_, 0);
v_tail_1939_ = lean_ctor_get(v_as_x27_1932_, 1);
v___x_1940_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0));
v___x_1948_ = lean_box(0);
v___x_1949_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12);
lean_inc(v_head_1938_);
v___x_1950_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1950_, 0, v_head_1938_);
lean_ctor_set(v___x_1950_, 1, v___x_1948_);
lean_ctor_set(v___x_1950_, 2, v___x_1949_);
v___x_1951_ = 0;
v___x_1952_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1952_, 0, v___x_1950_);
lean_ctor_set_uint8(v___x_1952_, sizeof(void*)*1, v___x_1951_);
v___x_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
v___x_1954_ = lean_st_ref_get(v___y_1935_);
v_toCold_1955_ = lean_ctor_get(v___y_1934_, 0);
v_env_1956_ = lean_ctor_get(v___x_1954_, 0);
lean_inc_ref(v_env_1956_);
lean_dec(v___x_1954_);
v_cancelTk_x3f_1957_ = lean_ctor_get(v_toCold_1955_, 10);
v___x_1958_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1934_);
v___x_1959_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_1956_, v___x_1958_, v___x_1953_, v_cancelTk_x3f_1957_);
lean_dec_ref_known(v___x_1953_, 1);
lean_dec_ref(v___x_1958_);
v___x_1960_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_1959_, v___y_1934_, v___y_1935_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; lean_object* v___x_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1970_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1961_);
lean_dec_ref_known(v___x_1960_, 1);
v___x_1962_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_1961_, v___y_1935_);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1970_ == 0)
{
lean_object* v_unused_1971_; 
v_unused_1971_ = lean_ctor_get(v___x_1962_, 0);
lean_dec(v_unused_1971_);
v___x_1964_ = v___x_1962_;
v_isShared_1965_ = v_isSharedCheck_1970_;
goto v_resetjp_1963_;
}
else
{
lean_dec(v___x_1962_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1970_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1966_; lean_object* v___x_1968_; 
v___x_1966_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__14));
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 0, v___x_1966_);
v___x_1968_ = v___x_1964_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1966_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
else
{
lean_object* v_a_1972_; 
v_a_1972_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1972_);
lean_dec_ref_known(v___x_1960_, 1);
v_a_1942_ = v_a_1972_;
goto v___jp_1941_;
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
if (v___x_1944_ == 0)
{
lean_dec_ref(v_a_1942_);
v_as_x27_1932_ = v_tail_1939_;
v_b_1933_ = v___x_1940_;
goto _start;
}
else
{
lean_object* v___x_1946_; 
v___x_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1946_, 0, v_a_1942_);
return v___x_1946_;
}
}
else
{
lean_object* v___x_1947_; 
v___x_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1947_, 0, v_a_1942_);
return v___x_1947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___boxed(lean_object* v_as_x27_1973_, lean_object* v_b_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_1973_, v_b_1974_, v___y_1975_, v___y_1976_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v_as_x27_1973_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(lean_object* v_decl_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_){
_start:
{
lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v_a_2012_; lean_object* v_a_2018_; 
switch(lean_obj_tag(v_decl_1979_))
{
case 1:
{
lean_object* v_val_2023_; lean_object* v_toConstantVal_2024_; uint8_t v___x_2025_; lean_object* v___x_2026_; lean_object* v_fallbackDecl_2027_; lean_object* v___x_2028_; lean_object* v_toCold_2029_; lean_object* v_env_2030_; lean_object* v_cancelTk_x3f_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v_val_2023_ = lean_ctor_get(v_decl_1979_, 0);
v_toConstantVal_2024_ = lean_ctor_get(v_val_2023_, 0);
v___x_2025_ = 0;
lean_inc_ref(v_toConstantVal_2024_);
v___x_2026_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2026_, 0, v_toConstantVal_2024_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*1, v___x_2025_);
v_fallbackDecl_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2027_, 0, v___x_2026_);
v___x_2028_ = lean_st_ref_get(v_a_1981_);
v_toCold_2029_ = lean_ctor_get(v_a_1980_, 0);
v_env_2030_ = lean_ctor_get(v___x_2028_, 0);
lean_inc_ref(v_env_2030_);
lean_dec(v___x_2028_);
v_cancelTk_x3f_2031_ = lean_ctor_get(v_toCold_2029_, 10);
v___x_2032_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1980_);
v___x_2033_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2030_, v___x_2032_, v_fallbackDecl_2027_, v_cancelTk_x3f_2031_);
lean_dec_ref_known(v_fallbackDecl_2027_, 1);
lean_dec_ref(v___x_2032_);
v___x_2034_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2033_, v_a_1980_, v_a_1981_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; lean_object* v___x_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2044_; 
lean_dec_ref_known(v_decl_1979_, 1);
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref_known(v___x_2034_, 1);
v___x_2036_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2035_, v_a_1981_);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2044_ == 0)
{
lean_object* v_unused_2045_; 
v_unused_2045_ = lean_ctor_get(v___x_2036_, 0);
lean_dec(v_unused_2045_);
v___x_2038_ = v___x_2036_;
v_isShared_2039_ = v_isSharedCheck_2044_;
goto v_resetjp_2037_;
}
else
{
lean_dec(v___x_2036_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2044_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2040_; lean_object* v___x_2042_; 
v___x_2040_ = lean_box(0);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 0, v___x_2040_);
v___x_2042_ = v___x_2038_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
else
{
lean_object* v_a_2046_; 
v_a_2046_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2046_);
lean_dec_ref_known(v___x_2034_, 1);
v_a_2012_ = v_a_2046_;
goto v___jp_2011_;
}
}
case 2:
{
lean_object* v_val_2047_; lean_object* v_toConstantVal_2048_; uint8_t v___x_2049_; lean_object* v___x_2050_; lean_object* v_fallbackDecl_2051_; lean_object* v___x_2052_; lean_object* v_toCold_2053_; lean_object* v_env_2054_; lean_object* v_cancelTk_x3f_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v_val_2047_ = lean_ctor_get(v_decl_1979_, 0);
v_toConstantVal_2048_ = lean_ctor_get(v_val_2047_, 0);
v___x_2049_ = 0;
lean_inc_ref(v_toConstantVal_2048_);
v___x_2050_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2050_, 0, v_toConstantVal_2048_);
lean_ctor_set_uint8(v___x_2050_, sizeof(void*)*1, v___x_2049_);
v_fallbackDecl_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2051_, 0, v___x_2050_);
v___x_2052_ = lean_st_ref_get(v_a_1981_);
v_toCold_2053_ = lean_ctor_get(v_a_1980_, 0);
v_env_2054_ = lean_ctor_get(v___x_2052_, 0);
lean_inc_ref(v_env_2054_);
lean_dec(v___x_2052_);
v_cancelTk_x3f_2055_ = lean_ctor_get(v_toCold_2053_, 10);
v___x_2056_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1980_);
v___x_2057_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2054_, v___x_2056_, v_fallbackDecl_2051_, v_cancelTk_x3f_2055_);
lean_dec_ref_known(v_fallbackDecl_2051_, 1);
lean_dec_ref(v___x_2056_);
v___x_2058_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2057_, v_a_1980_, v_a_1981_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v___x_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2068_; 
lean_dec_ref_known(v_decl_1979_, 1);
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2058_, 1);
v___x_2060_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2059_, v_a_1981_);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2068_ == 0)
{
lean_object* v_unused_2069_; 
v_unused_2069_ = lean_ctor_get(v___x_2060_, 0);
lean_dec(v_unused_2069_);
v___x_2062_ = v___x_2060_;
v_isShared_2063_ = v_isSharedCheck_2068_;
goto v_resetjp_2061_;
}
else
{
lean_dec(v___x_2060_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2068_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2064_; lean_object* v___x_2066_; 
v___x_2064_ = lean_box(0);
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 0, v___x_2064_);
v___x_2066_ = v___x_2062_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
else
{
lean_object* v_a_2070_; 
v_a_2070_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2070_);
lean_dec_ref_known(v___x_2058_, 1);
v_a_2018_ = v_a_2070_;
goto v___jp_2017_;
}
}
default: 
{
v___y_1984_ = v_a_1980_;
v___y_1985_ = v_a_1981_;
goto v___jp_1983_;
}
}
v___jp_1983_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1986_ = l_Lean_Declaration_getNames(v_decl_1979_);
v___x_1987_ = lean_box(0);
v___x_1988_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0));
v___x_1989_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v___x_1986_, v___x_1988_, v___y_1984_, v___y_1985_);
lean_dec(v___x_1986_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2002_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1992_ = v___x_1989_;
v_isShared_1993_ = v_isSharedCheck_2002_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1989_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2002_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v_fst_1994_; 
v_fst_1994_ = lean_ctor_get(v_a_1990_, 0);
lean_inc(v_fst_1994_);
lean_dec(v_a_1990_);
if (lean_obj_tag(v_fst_1994_) == 0)
{
lean_object* v___x_1996_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_1987_);
v___x_1996_ = v___x_1992_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1987_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
else
{
lean_object* v_val_1998_; lean_object* v___x_2000_; 
v_val_1998_ = lean_ctor_get(v_fst_1994_, 0);
lean_inc(v_val_1998_);
lean_dec_ref_known(v_fst_1994_, 1);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v_val_1998_);
v___x_2000_ = v___x_1992_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_val_1998_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
else
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
v_a_2003_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2005_ = v___x_1989_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_1989_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2003_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
v___jp_2011_:
{
uint8_t v___x_2013_; 
v___x_2013_ = l_Lean_Exception_isInterrupt(v_a_2012_);
if (v___x_2013_ == 0)
{
uint8_t v___x_2014_; 
lean_inc_ref(v_a_2012_);
v___x_2014_ = l_Lean_Exception_isRuntime(v_a_2012_);
if (v___x_2014_ == 0)
{
lean_dec_ref(v_a_2012_);
v___y_1984_ = v_a_1980_;
v___y_1985_ = v_a_1981_;
goto v___jp_1983_;
}
else
{
lean_object* v___x_2015_; 
lean_dec(v_decl_1979_);
v___x_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2015_, 0, v_a_2012_);
return v___x_2015_;
}
}
else
{
lean_object* v___x_2016_; 
lean_dec(v_decl_1979_);
v___x_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2016_, 0, v_a_2012_);
return v___x_2016_;
}
}
v___jp_2017_:
{
uint8_t v___x_2019_; 
v___x_2019_ = l_Lean_Exception_isInterrupt(v_a_2018_);
if (v___x_2019_ == 0)
{
uint8_t v___x_2020_; 
lean_inc_ref(v_a_2018_);
v___x_2020_ = l_Lean_Exception_isRuntime(v_a_2018_);
if (v___x_2020_ == 0)
{
lean_dec_ref(v_a_2018_);
v___y_1984_ = v_a_1980_;
v___y_1985_ = v_a_1981_;
goto v___jp_1983_;
}
else
{
lean_object* v___x_2021_; 
lean_dec(v_decl_1979_);
v___x_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2021_, 0, v_a_2018_);
return v___x_2021_;
}
}
else
{
lean_object* v___x_2022_; 
lean_dec(v_decl_1979_);
v___x_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2022_, 0, v_a_2018_);
return v___x_2022_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom___boxed(lean_object* v_decl_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2071_, v_a_2072_, v_a_2073_);
lean_dec(v_a_2073_);
lean_dec_ref(v_a_2072_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(lean_object* v_00_u03b1_2076_, lean_object* v_x_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v___x_2081_; 
v___x_2081_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_2077_, v___y_2078_, v___y_2079_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___boxed(lean_object* v_00_u03b1_2082_, lean_object* v_x_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(v_00_u03b1_2082_, v_x_2083_, v___y_2084_, v___y_2085_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(lean_object* v_as_2088_, lean_object* v_as_x27_2089_, lean_object* v_b_2090_, lean_object* v_a_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v___x_2095_; 
v___x_2095_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_2089_, v_b_2090_, v___y_2092_, v___y_2093_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___boxed(lean_object* v_as_2096_, lean_object* v_as_x27_2097_, lean_object* v_b_2098_, lean_object* v_a_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(v_as_2096_, v_as_x27_2097_, v_b_2098_, v_a_2099_, v___y_2100_, v___y_2101_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v_as_x27_2097_);
lean_dec(v_as_2096_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v___x_2108_; 
v___x_2108_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(v_00_u03b1_2109_, v___y_2110_, v___y_2111_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(lean_object* v_00_u03b1_2114_, lean_object* v_ex_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v___x_2119_; 
v___x_2119_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_2115_, v___y_2116_, v___y_2117_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2120_, lean_object* v_ex_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(v_00_u03b1_2120_, v_ex_2121_, v___y_2122_, v___y_2123_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2126_, lean_object* v_msg_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v___x_2131_; 
v___x_2131_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_2127_, v___y_2128_, v___y_2129_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2132_, lean_object* v_msg_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(v_00_u03b1_2132_, v_msg_2133_, v___y_2134_, v___y_2135_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
return v_res_2137_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2138_ = lean_unsigned_to_nat(32u);
v___x_2139_ = lean_mk_empty_array_with_capacity(v___x_2138_);
v___x_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2139_);
return v___x_2140_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2141_ = ((size_t)5ULL);
v___x_2142_ = lean_unsigned_to_nat(0u);
v___x_2143_ = lean_unsigned_to_nat(32u);
v___x_2144_ = lean_mk_empty_array_with_capacity(v___x_2143_);
v___x_2145_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0);
v___x_2146_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
lean_ctor_set(v___x_2146_, 1, v___x_2144_);
lean_ctor_set(v___x_2146_, 2, v___x_2142_);
lean_ctor_set(v___x_2146_, 3, v___x_2142_);
lean_ctor_set_usize(v___x_2146_, 4, v___x_2141_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(lean_object* v___y_2147_){
_start:
{
lean_object* v___x_2149_; lean_object* v_traceState_2150_; lean_object* v_traces_2151_; lean_object* v___x_2152_; lean_object* v_traceState_2153_; lean_object* v_env_2154_; lean_object* v_nextMacroScope_2155_; lean_object* v_ngen_2156_; lean_object* v_auxDeclNGen_2157_; lean_object* v_cache_2158_; lean_object* v_recordedDeps_2159_; lean_object* v_messages_2160_; lean_object* v_infoState_2161_; lean_object* v_snapshotTasks_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2181_; 
v___x_2149_ = lean_st_ref_get(v___y_2147_);
v_traceState_2150_ = lean_ctor_get(v___x_2149_, 4);
lean_inc_ref(v_traceState_2150_);
lean_dec(v___x_2149_);
v_traces_2151_ = lean_ctor_get(v_traceState_2150_, 0);
lean_inc_ref(v_traces_2151_);
lean_dec_ref(v_traceState_2150_);
v___x_2152_ = lean_st_ref_take(v___y_2147_);
v_traceState_2153_ = lean_ctor_get(v___x_2152_, 4);
v_env_2154_ = lean_ctor_get(v___x_2152_, 0);
v_nextMacroScope_2155_ = lean_ctor_get(v___x_2152_, 1);
v_ngen_2156_ = lean_ctor_get(v___x_2152_, 2);
v_auxDeclNGen_2157_ = lean_ctor_get(v___x_2152_, 3);
v_cache_2158_ = lean_ctor_get(v___x_2152_, 5);
v_recordedDeps_2159_ = lean_ctor_get(v___x_2152_, 6);
v_messages_2160_ = lean_ctor_get(v___x_2152_, 7);
v_infoState_2161_ = lean_ctor_get(v___x_2152_, 8);
v_snapshotTasks_2162_ = lean_ctor_get(v___x_2152_, 9);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2164_ = v___x_2152_;
v_isShared_2165_ = v_isSharedCheck_2181_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_snapshotTasks_2162_);
lean_inc(v_infoState_2161_);
lean_inc(v_messages_2160_);
lean_inc(v_recordedDeps_2159_);
lean_inc(v_cache_2158_);
lean_inc(v_traceState_2153_);
lean_inc(v_auxDeclNGen_2157_);
lean_inc(v_ngen_2156_);
lean_inc(v_nextMacroScope_2155_);
lean_inc(v_env_2154_);
lean_dec(v___x_2152_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2181_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
uint64_t v_tid_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2179_; 
v_tid_2166_ = lean_ctor_get_uint64(v_traceState_2153_, sizeof(void*)*1);
v_isSharedCheck_2179_ = !lean_is_exclusive(v_traceState_2153_);
if (v_isSharedCheck_2179_ == 0)
{
lean_object* v_unused_2180_; 
v_unused_2180_ = lean_ctor_get(v_traceState_2153_, 0);
lean_dec(v_unused_2180_);
v___x_2168_ = v_traceState_2153_;
v_isShared_2169_ = v_isSharedCheck_2179_;
goto v_resetjp_2167_;
}
else
{
lean_dec(v_traceState_2153_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2179_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2170_; lean_object* v___x_2172_; 
v___x_2170_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 0, v___x_2170_);
v___x_2172_ = v___x_2168_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2170_);
lean_ctor_set_uint64(v_reuseFailAlloc_2178_, sizeof(void*)*1, v_tid_2166_);
v___x_2172_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
lean_object* v___x_2174_; 
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 4, v___x_2172_);
v___x_2174_ = v___x_2164_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_env_2154_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_nextMacroScope_2155_);
lean_ctor_set(v_reuseFailAlloc_2177_, 2, v_ngen_2156_);
lean_ctor_set(v_reuseFailAlloc_2177_, 3, v_auxDeclNGen_2157_);
lean_ctor_set(v_reuseFailAlloc_2177_, 4, v___x_2172_);
lean_ctor_set(v_reuseFailAlloc_2177_, 5, v_cache_2158_);
lean_ctor_set(v_reuseFailAlloc_2177_, 6, v_recordedDeps_2159_);
lean_ctor_set(v_reuseFailAlloc_2177_, 7, v_messages_2160_);
lean_ctor_set(v_reuseFailAlloc_2177_, 8, v_infoState_2161_);
lean_ctor_set(v_reuseFailAlloc_2177_, 9, v_snapshotTasks_2162_);
v___x_2174_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = lean_st_ref_put(v___y_2147_, v___x_2174_);
v___x_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2176_, 0, v_traces_2151_);
return v___x_2176_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___boxed(lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2182_);
lean_dec(v___y_2182_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v___x_2188_; 
v___x_2188_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2186_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___boxed(lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(v___y_2189_, v___y_2190_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(lean_object* v_category_2193_, lean_object* v_opts_2194_, lean_object* v_act_2195_, lean_object* v_decl_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
lean_inc(v___y_2198_);
lean_inc_ref(v___y_2197_);
v___x_2200_ = lean_apply_2(v_act_2195_, v___y_2197_, v___y_2198_);
v___x_2201_ = l_Lean_profileitIOUnsafe___redArg(v_category_2193_, v_opts_2194_, v___x_2200_, v_decl_2196_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg___boxed(lean_object* v_category_2202_, lean_object* v_opts_2203_, lean_object* v_act_2204_, lean_object* v_decl_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v_category_2202_, v_opts_2203_, v_act_2204_, v_decl_2205_, v___y_2206_, v___y_2207_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec_ref(v_opts_2203_);
lean_dec_ref(v_category_2202_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(lean_object* v_00_u03b1_2210_, lean_object* v_category_2211_, lean_object* v_opts_2212_, lean_object* v_act_2213_, lean_object* v_decl_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v___x_2218_; 
v___x_2218_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v_category_2211_, v_opts_2212_, v_act_2213_, v_decl_2214_, v___y_2215_, v___y_2216_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___boxed(lean_object* v_00_u03b1_2219_, lean_object* v_category_2220_, lean_object* v_opts_2221_, lean_object* v_act_2222_, lean_object* v_decl_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(v_00_u03b1_2219_, v_category_2220_, v_opts_2221_, v_act_2222_, v_decl_2223_, v___y_2224_, v___y_2225_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec_ref(v_opts_2221_);
lean_dec_ref(v_category_2220_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(lean_object* v_a_2228_, lean_object* v_a_2229_){
_start:
{
if (lean_obj_tag(v_a_2228_) == 0)
{
lean_object* v___x_2230_; 
v___x_2230_ = l_List_reverse___redArg(v_a_2229_);
return v___x_2230_;
}
else
{
lean_object* v_head_2231_; lean_object* v_tail_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2241_; 
v_head_2231_ = lean_ctor_get(v_a_2228_, 0);
v_tail_2232_ = lean_ctor_get(v_a_2228_, 1);
v_isSharedCheck_2241_ = !lean_is_exclusive(v_a_2228_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2234_ = v_a_2228_;
v_isShared_2235_ = v_isSharedCheck_2241_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_tail_2232_);
lean_inc(v_head_2231_);
lean_dec(v_a_2228_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2241_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2236_; lean_object* v___x_2238_; 
v___x_2236_ = l_Lean_MessageData_ofName(v_head_2231_);
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 1, v_a_2229_);
lean_ctor_set(v___x_2234_, 0, v___x_2236_);
v___x_2238_ = v___x_2234_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2236_);
lean_ctor_set(v_reuseFailAlloc_2240_, 1, v_a_2229_);
v___x_2238_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
v_a_2228_ = v_tail_2232_;
v_a_2229_ = v___x_2238_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__0));
v___x_2244_ = l_Lean_stringToMessageData(v___x_2243_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(lean_object* v_decl_2245_, lean_object* v_x_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2250_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1);
v___x_2251_ = l_Lean_Declaration_getTopLevelNames(v_decl_2245_);
v___x_2252_ = lean_box(0);
v___x_2253_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2251_, v___x_2252_);
v___x_2254_ = l_Lean_MessageData_ofList(v___x_2253_);
v___x_2255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2250_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
v___x_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed(lean_object* v_decl_2257_, lean_object* v_x_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(v_decl_2257_, v_x_2258_, v___y_2259_, v___y_2260_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec_ref(v_x_2258_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(size_t v_sz_2263_, size_t v_i_2264_, lean_object* v_bs_2265_){
_start:
{
uint8_t v___x_2266_; 
v___x_2266_ = lean_usize_dec_lt(v_i_2264_, v_sz_2263_);
if (v___x_2266_ == 0)
{
return v_bs_2265_;
}
else
{
lean_object* v_v_2267_; lean_object* v_msg_2268_; lean_object* v___x_2269_; lean_object* v_bs_x27_2270_; size_t v___x_2271_; size_t v___x_2272_; lean_object* v___x_2273_; 
v_v_2267_ = lean_array_uget_borrowed(v_bs_2265_, v_i_2264_);
v_msg_2268_ = lean_ctor_get(v_v_2267_, 1);
lean_inc_ref(v_msg_2268_);
v___x_2269_ = lean_unsigned_to_nat(0u);
v_bs_x27_2270_ = lean_array_uset(v_bs_2265_, v_i_2264_, v___x_2269_);
v___x_2271_ = ((size_t)1ULL);
v___x_2272_ = lean_usize_add(v_i_2264_, v___x_2271_);
v___x_2273_ = lean_array_uset(v_bs_x27_2270_, v_i_2264_, v_msg_2268_);
v_i_2264_ = v___x_2272_;
v_bs_2265_ = v___x_2273_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4___boxed(lean_object* v_sz_2275_, lean_object* v_i_2276_, lean_object* v_bs_2277_){
_start:
{
size_t v_sz_boxed_2278_; size_t v_i_boxed_2279_; lean_object* v_res_2280_; 
v_sz_boxed_2278_ = lean_unbox_usize(v_sz_2275_);
lean_dec(v_sz_2275_);
v_i_boxed_2279_ = lean_unbox_usize(v_i_2276_);
lean_dec(v_i_2276_);
v_res_2280_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(v_sz_boxed_2278_, v_i_boxed_2279_, v_bs_2277_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(lean_object* v_oldTraces_2281_, lean_object* v_data_2282_, lean_object* v_ref_2283_, lean_object* v_msg_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v_toCold_2288_; lean_object* v_currRecDepth_2289_; lean_object* v_ref_2290_; uint16_t v_optionFlags_2291_; uint8_t v_suppressElabErrors_2292_; uint8_t v_isRecordingDeps_2293_; lean_object* v_ref_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v_traceState_2297_; lean_object* v_traces_2298_; lean_object* v___x_2299_; size_t v_sz_2300_; size_t v___x_2301_; lean_object* v___x_2302_; lean_object* v_msg_2303_; lean_object* v___x_2304_; lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2343_; 
v_toCold_2288_ = lean_ctor_get(v___y_2285_, 0);
v_currRecDepth_2289_ = lean_ctor_get(v___y_2285_, 1);
v_ref_2290_ = lean_ctor_get(v___y_2285_, 2);
v_optionFlags_2291_ = lean_ctor_get_uint16(v___y_2285_, sizeof(void*)*3);
v_suppressElabErrors_2292_ = lean_ctor_get_uint8(v___y_2285_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2293_ = lean_ctor_get_uint8(v___y_2285_, sizeof(void*)*3 + 3);
v_ref_2294_ = l_Lean_replaceRef(v_ref_2283_, v_ref_2290_);
lean_inc(v_currRecDepth_2289_);
lean_inc_ref(v_toCold_2288_);
v___x_2295_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2295_, 0, v_toCold_2288_);
lean_ctor_set(v___x_2295_, 1, v_currRecDepth_2289_);
lean_ctor_set(v___x_2295_, 2, v_ref_2294_);
lean_ctor_set_uint16(v___x_2295_, sizeof(void*)*3, v_optionFlags_2291_);
lean_ctor_set_uint8(v___x_2295_, sizeof(void*)*3 + 2, v_suppressElabErrors_2292_);
lean_ctor_set_uint8(v___x_2295_, sizeof(void*)*3 + 3, v_isRecordingDeps_2293_);
v___x_2296_ = lean_st_ref_get(v___y_2286_);
v_traceState_2297_ = lean_ctor_get(v___x_2296_, 4);
lean_inc_ref(v_traceState_2297_);
lean_dec(v___x_2296_);
v_traces_2298_ = lean_ctor_get(v_traceState_2297_, 0);
lean_inc_ref(v_traces_2298_);
lean_dec_ref(v_traceState_2297_);
v___x_2299_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2298_);
lean_dec_ref(v_traces_2298_);
v_sz_2300_ = lean_array_size(v___x_2299_);
v___x_2301_ = ((size_t)0ULL);
v___x_2302_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(v_sz_2300_, v___x_2301_, v___x_2299_);
v_msg_2303_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2303_, 0, v_data_2282_);
lean_ctor_set(v_msg_2303_, 1, v_msg_2284_);
lean_ctor_set(v_msg_2303_, 2, v___x_2302_);
v___x_2304_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2303_, v___x_2295_, v___y_2286_);
lean_dec_ref_known(v___x_2295_, 3);
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2307_ = v___x_2304_;
v_isShared_2308_ = v_isSharedCheck_2343_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2304_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2343_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2309_; lean_object* v_traceState_2310_; lean_object* v_env_2311_; lean_object* v_nextMacroScope_2312_; lean_object* v_ngen_2313_; lean_object* v_auxDeclNGen_2314_; lean_object* v_cache_2315_; lean_object* v_recordedDeps_2316_; lean_object* v_messages_2317_; lean_object* v_infoState_2318_; lean_object* v_snapshotTasks_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2342_; 
v___x_2309_ = lean_st_ref_take(v___y_2286_);
v_traceState_2310_ = lean_ctor_get(v___x_2309_, 4);
v_env_2311_ = lean_ctor_get(v___x_2309_, 0);
v_nextMacroScope_2312_ = lean_ctor_get(v___x_2309_, 1);
v_ngen_2313_ = lean_ctor_get(v___x_2309_, 2);
v_auxDeclNGen_2314_ = lean_ctor_get(v___x_2309_, 3);
v_cache_2315_ = lean_ctor_get(v___x_2309_, 5);
v_recordedDeps_2316_ = lean_ctor_get(v___x_2309_, 6);
v_messages_2317_ = lean_ctor_get(v___x_2309_, 7);
v_infoState_2318_ = lean_ctor_get(v___x_2309_, 8);
v_snapshotTasks_2319_ = lean_ctor_get(v___x_2309_, 9);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2321_ = v___x_2309_;
v_isShared_2322_ = v_isSharedCheck_2342_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_snapshotTasks_2319_);
lean_inc(v_infoState_2318_);
lean_inc(v_messages_2317_);
lean_inc(v_recordedDeps_2316_);
lean_inc(v_cache_2315_);
lean_inc(v_traceState_2310_);
lean_inc(v_auxDeclNGen_2314_);
lean_inc(v_ngen_2313_);
lean_inc(v_nextMacroScope_2312_);
lean_inc(v_env_2311_);
lean_dec(v___x_2309_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2342_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
uint64_t v_tid_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2340_; 
v_tid_2323_ = lean_ctor_get_uint64(v_traceState_2310_, sizeof(void*)*1);
v_isSharedCheck_2340_ = !lean_is_exclusive(v_traceState_2310_);
if (v_isSharedCheck_2340_ == 0)
{
lean_object* v_unused_2341_; 
v_unused_2341_ = lean_ctor_get(v_traceState_2310_, 0);
lean_dec(v_unused_2341_);
v___x_2325_ = v_traceState_2310_;
v_isShared_2326_ = v_isSharedCheck_2340_;
goto v_resetjp_2324_;
}
else
{
lean_dec(v_traceState_2310_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2340_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2331_; 
v___x_2327_ = lean_box(0);
v___x_2328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2328_, 0, v_ref_2283_);
lean_ctor_set(v___x_2328_, 1, v_a_2305_);
v___x_2329_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2281_, v___x_2328_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 0, v___x_2329_);
v___x_2331_ = v___x_2325_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2329_);
lean_ctor_set_uint64(v_reuseFailAlloc_2339_, sizeof(void*)*1, v_tid_2323_);
v___x_2331_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2333_; 
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 4, v___x_2331_);
v___x_2333_ = v___x_2321_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_env_2311_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v_nextMacroScope_2312_);
lean_ctor_set(v_reuseFailAlloc_2338_, 2, v_ngen_2313_);
lean_ctor_set(v_reuseFailAlloc_2338_, 3, v_auxDeclNGen_2314_);
lean_ctor_set(v_reuseFailAlloc_2338_, 4, v___x_2331_);
lean_ctor_set(v_reuseFailAlloc_2338_, 5, v_cache_2315_);
lean_ctor_set(v_reuseFailAlloc_2338_, 6, v_recordedDeps_2316_);
lean_ctor_set(v_reuseFailAlloc_2338_, 7, v_messages_2317_);
lean_ctor_set(v_reuseFailAlloc_2338_, 8, v_infoState_2318_);
lean_ctor_set(v_reuseFailAlloc_2338_, 9, v_snapshotTasks_2319_);
v___x_2333_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v___x_2334_; lean_object* v___x_2336_; 
v___x_2334_ = lean_st_ref_put(v___y_2286_, v___x_2333_);
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 0, v___x_2327_);
v___x_2336_ = v___x_2307_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2327_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2___boxed(lean_object* v_oldTraces_2344_, lean_object* v_data_2345_, lean_object* v_ref_2346_, lean_object* v_msg_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_oldTraces_2344_, v_data_2345_, v_ref_2346_, v_msg_2347_, v___y_2348_, v___y_2349_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(lean_object* v_x_2352_){
_start:
{
if (lean_obj_tag(v_x_2352_) == 0)
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
v_a_2354_ = lean_ctor_get(v_x_2352_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v_x_2352_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v_x_2352_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v_x_2352_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
lean_ctor_set_tag(v___x_2356_, 1);
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
v_a_2362_ = lean_ctor_get(v_x_2352_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v_x_2352_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v_x_2352_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v_x_2352_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
lean_ctor_set_tag(v___x_2364_, 0);
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg___boxed(lean_object* v_x_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_x_2370_);
return v_res_2372_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(lean_object* v_e_2373_){
_start:
{
if (lean_obj_tag(v_e_2373_) == 0)
{
uint8_t v___x_2374_; 
v___x_2374_ = 2;
return v___x_2374_;
}
else
{
uint8_t v___x_2375_; 
v___x_2375_ = 0;
return v___x_2375_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4___boxed(lean_object* v_e_2376_){
_start:
{
uint8_t v_res_2377_; lean_object* v_r_2378_; 
v_res_2377_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(v_e_2376_);
lean_dec_ref(v_e_2376_);
v_r_2378_ = lean_box(v_res_2377_);
return v_r_2378_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2379_; double v___x_2380_; 
v___x_2379_ = lean_unsigned_to_nat(0u);
v___x_2380_ = lean_float_of_nat(v___x_2379_);
return v___x_2380_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2(void){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__1));
v___x_2383_ = l_Lean_stringToMessageData(v___x_2382_);
return v___x_2383_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3(void){
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
lean_object* v_fst_2397_; lean_object* v_snd_2398_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v_data_2402_; lean_object* v_fst_2405_; lean_object* v_snd_2406_; lean_object* v___x_2407_; uint8_t v___x_2408_; lean_object* v___y_2410_; lean_object* v_a_2411_; uint8_t v___y_2426_; double v___y_2458_; 
v_fst_2397_ = lean_ctor_get(v_resStartStop_2393_, 0);
lean_inc(v_fst_2397_);
v_snd_2398_ = lean_ctor_get(v_resStartStop_2393_, 1);
lean_inc(v_snd_2398_);
lean_dec_ref(v_resStartStop_2393_);
v_fst_2405_ = lean_ctor_get(v_snd_2398_, 0);
lean_inc(v_fst_2405_);
v_snd_2406_ = lean_ctor_get(v_snd_2398_, 1);
lean_inc(v_snd_2406_);
lean_dec(v_snd_2398_);
v___x_2407_ = l_Lean_trace_profiler;
v___x_2408_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2389_, v___x_2407_);
if (v___x_2408_ == 0)
{
v___y_2426_ = v___x_2408_;
goto v___jp_2425_;
}
else
{
lean_object* v___x_2463_; uint8_t v___x_2464_; 
v___x_2463_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2464_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2389_, v___x_2463_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2465_; lean_object* v___x_2466_; double v___x_2467_; double v___x_2468_; double v___x_2469_; 
v___x_2465_ = l_Lean_trace_profiler_threshold;
v___x_2466_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_2389_, v___x_2465_);
v___x_2467_ = lean_float_of_nat(v___x_2466_);
v___x_2468_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3);
v___x_2469_ = lean_float_div(v___x_2467_, v___x_2468_);
v___y_2458_ = v___x_2469_;
goto v___jp_2457_;
}
else
{
lean_object* v___x_2470_; lean_object* v___x_2471_; double v___x_2472_; 
v___x_2470_ = l_Lean_trace_profiler_threshold;
v___x_2471_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_2389_, v___x_2470_);
v___x_2472_ = lean_float_of_nat(v___x_2471_);
v___y_2458_ = v___x_2472_;
goto v___jp_2457_;
}
}
v___jp_2399_:
{
lean_object* v___x_2403_; 
lean_inc(v___y_2400_);
v___x_2403_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_oldTraces_2391_, v_data_2402_, v___y_2400_, v___y_2401_, v___y_2394_, v___y_2395_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v___x_2404_; 
lean_dec_ref_known(v___x_2403_, 1);
v___x_2404_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_fst_2397_);
return v___x_2404_;
}
else
{
lean_dec(v_fst_2397_);
return v___x_2403_;
}
}
v___jp_2409_:
{
uint8_t v_result_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; double v___x_2415_; lean_object* v_data_2416_; 
v_result_2412_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(v_fst_2397_);
v___x_2413_ = lean_box(v_result_2412_);
v___x_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2413_);
v___x_2415_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0);
lean_inc_ref(v_tag_2388_);
lean_inc_ref(v___x_2414_);
lean_inc(v_cls_2386_);
v_data_2416_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2416_, 0, v_cls_2386_);
lean_ctor_set(v_data_2416_, 1, v___x_2414_);
lean_ctor_set(v_data_2416_, 2, v_tag_2388_);
lean_ctor_set_float(v_data_2416_, sizeof(void*)*3, v___x_2415_);
lean_ctor_set_float(v_data_2416_, sizeof(void*)*3 + 8, v___x_2415_);
lean_ctor_set_uint8(v_data_2416_, sizeof(void*)*3 + 16, v_collapsed_2387_);
if (v___x_2408_ == 0)
{
lean_dec_ref_known(v___x_2414_, 1);
lean_dec(v_snd_2406_);
lean_dec(v_fst_2405_);
lean_dec_ref(v_tag_2388_);
lean_dec(v_cls_2386_);
v___y_2400_ = v___y_2410_;
v___y_2401_ = v_a_2411_;
v_data_2402_ = v_data_2416_;
goto v___jp_2399_;
}
else
{
lean_object* v_data_2417_; double v___x_2418_; double v___x_2419_; 
lean_dec_ref_known(v_data_2416_, 3);
v_data_2417_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2417_, 0, v_cls_2386_);
lean_ctor_set(v_data_2417_, 1, v___x_2414_);
lean_ctor_set(v_data_2417_, 2, v_tag_2388_);
v___x_2418_ = lean_unbox_float(v_fst_2405_);
lean_dec(v_fst_2405_);
lean_ctor_set_float(v_data_2417_, sizeof(void*)*3, v___x_2418_);
v___x_2419_ = lean_unbox_float(v_snd_2406_);
lean_dec(v_snd_2406_);
lean_ctor_set_float(v_data_2417_, sizeof(void*)*3 + 8, v___x_2419_);
lean_ctor_set_uint8(v_data_2417_, sizeof(void*)*3 + 16, v_collapsed_2387_);
v___y_2400_ = v___y_2410_;
v___y_2401_ = v_a_2411_;
v_data_2402_ = v_data_2417_;
goto v___jp_2399_;
}
}
v___jp_2420_:
{
lean_object* v_ref_2421_; lean_object* v___x_2422_; 
v_ref_2421_ = lean_ctor_get(v___y_2394_, 2);
lean_inc(v___y_2395_);
lean_inc_ref(v___y_2394_);
lean_inc(v_fst_2397_);
v___x_2422_ = lean_apply_4(v_msg_2392_, v_fst_2397_, v___y_2394_, v___y_2395_, lean_box(0));
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2423_; 
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_a_2423_);
lean_dec_ref_known(v___x_2422_, 1);
v___y_2410_ = v_ref_2421_;
v_a_2411_ = v_a_2423_;
goto v___jp_2409_;
}
else
{
lean_object* v___x_2424_; 
lean_dec_ref_known(v___x_2422_, 1);
v___x_2424_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2);
v___y_2410_ = v_ref_2421_;
v_a_2411_ = v___x_2424_;
goto v___jp_2409_;
}
}
v___jp_2425_:
{
if (v_clsEnabled_2390_ == 0)
{
if (v___y_2426_ == 0)
{
lean_object* v___x_2427_; lean_object* v_traceState_2428_; lean_object* v_env_2429_; lean_object* v_nextMacroScope_2430_; lean_object* v_ngen_2431_; lean_object* v_auxDeclNGen_2432_; lean_object* v_cache_2433_; lean_object* v_recordedDeps_2434_; lean_object* v_messages_2435_; lean_object* v_infoState_2436_; lean_object* v_snapshotTasks_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2456_; 
lean_dec(v_snd_2406_);
lean_dec(v_fst_2405_);
lean_dec_ref(v_msg_2392_);
lean_dec_ref(v_tag_2388_);
lean_dec(v_cls_2386_);
v___x_2427_ = lean_st_ref_take(v___y_2395_);
v_traceState_2428_ = lean_ctor_get(v___x_2427_, 4);
v_env_2429_ = lean_ctor_get(v___x_2427_, 0);
v_nextMacroScope_2430_ = lean_ctor_get(v___x_2427_, 1);
v_ngen_2431_ = lean_ctor_get(v___x_2427_, 2);
v_auxDeclNGen_2432_ = lean_ctor_get(v___x_2427_, 3);
v_cache_2433_ = lean_ctor_get(v___x_2427_, 5);
v_recordedDeps_2434_ = lean_ctor_get(v___x_2427_, 6);
v_messages_2435_ = lean_ctor_get(v___x_2427_, 7);
v_infoState_2436_ = lean_ctor_get(v___x_2427_, 8);
v_snapshotTasks_2437_ = lean_ctor_get(v___x_2427_, 9);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2439_ = v___x_2427_;
v_isShared_2440_ = v_isSharedCheck_2456_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_snapshotTasks_2437_);
lean_inc(v_infoState_2436_);
lean_inc(v_messages_2435_);
lean_inc(v_recordedDeps_2434_);
lean_inc(v_cache_2433_);
lean_inc(v_traceState_2428_);
lean_inc(v_auxDeclNGen_2432_);
lean_inc(v_ngen_2431_);
lean_inc(v_nextMacroScope_2430_);
lean_inc(v_env_2429_);
lean_dec(v___x_2427_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2456_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
uint64_t v_tid_2441_; lean_object* v_traces_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2455_; 
v_tid_2441_ = lean_ctor_get_uint64(v_traceState_2428_, sizeof(void*)*1);
v_traces_2442_ = lean_ctor_get(v_traceState_2428_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v_traceState_2428_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2444_ = v_traceState_2428_;
v_isShared_2445_ = v_isSharedCheck_2455_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_traces_2442_);
lean_dec(v_traceState_2428_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2455_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2446_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2391_, v_traces_2442_);
lean_dec_ref(v_traces_2442_);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 0, v___x_2446_);
v___x_2448_ = v___x_2444_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2446_);
lean_ctor_set_uint64(v_reuseFailAlloc_2454_, sizeof(void*)*1, v_tid_2441_);
v___x_2448_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v___x_2450_; 
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 4, v___x_2448_);
v___x_2450_ = v___x_2439_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_env_2429_);
lean_ctor_set(v_reuseFailAlloc_2453_, 1, v_nextMacroScope_2430_);
lean_ctor_set(v_reuseFailAlloc_2453_, 2, v_ngen_2431_);
lean_ctor_set(v_reuseFailAlloc_2453_, 3, v_auxDeclNGen_2432_);
lean_ctor_set(v_reuseFailAlloc_2453_, 4, v___x_2448_);
lean_ctor_set(v_reuseFailAlloc_2453_, 5, v_cache_2433_);
lean_ctor_set(v_reuseFailAlloc_2453_, 6, v_recordedDeps_2434_);
lean_ctor_set(v_reuseFailAlloc_2453_, 7, v_messages_2435_);
lean_ctor_set(v_reuseFailAlloc_2453_, 8, v_infoState_2436_);
lean_ctor_set(v_reuseFailAlloc_2453_, 9, v_snapshotTasks_2437_);
v___x_2450_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = lean_st_ref_put(v___y_2395_, v___x_2450_);
v___x_2452_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_fst_2397_);
return v___x_2452_;
}
}
}
}
}
else
{
goto v___jp_2420_;
}
}
else
{
goto v___jp_2420_;
}
}
v___jp_2457_:
{
double v___x_2459_; double v___x_2460_; double v___x_2461_; uint8_t v___x_2462_; 
v___x_2459_ = lean_unbox_float(v_snd_2406_);
v___x_2460_ = lean_unbox_float(v_fst_2405_);
v___x_2461_ = lean_float_sub(v___x_2459_, v___x_2460_);
v___x_2462_ = lean_float_decLt(v___y_2458_, v___x_2461_);
v___y_2426_ = v___x_2462_;
goto v___jp_2425_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___boxed(lean_object* v_cls_2473_, lean_object* v_collapsed_2474_, lean_object* v_tag_2475_, lean_object* v_opts_2476_, lean_object* v_clsEnabled_2477_, lean_object* v_oldTraces_2478_, lean_object* v_msg_2479_, lean_object* v_resStartStop_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
uint8_t v_collapsed_boxed_2484_; uint8_t v_clsEnabled_boxed_2485_; lean_object* v_res_2486_; 
v_collapsed_boxed_2484_ = lean_unbox(v_collapsed_2474_);
v_clsEnabled_boxed_2485_ = lean_unbox(v_clsEnabled_2477_);
v_res_2486_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_2473_, v_collapsed_boxed_2484_, v_tag_2475_, v_opts_2476_, v_clsEnabled_boxed_2485_, v_oldTraces_2478_, v_msg_2479_, v_resStartStop_2480_, v___y_2481_, v___y_2482_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec_ref(v_opts_2476_);
return v_res_2486_;
}
}
static double _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2489_; double v___x_2490_; 
v___x_2489_ = lean_unsigned_to_nat(1000000000u);
v___x_2490_ = lean_float_of_nat(v___x_2489_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(lean_object* v_decl_2491_, lean_object* v___x_2492_, uint8_t v___x_2493_, lean_object* v___x_2494_, lean_object* v___f_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v___y_2500_; lean_object* v_a_2501_; lean_object* v___y_2514_; lean_object* v_a_2515_; lean_object* v_toCold_2527_; lean_object* v_options_2528_; uint8_t v_hasTrace_2529_; 
v_toCold_2527_ = lean_ctor_get(v___y_2496_, 0);
v_options_2528_ = lean_ctor_get(v_toCold_2527_, 2);
v_hasTrace_2529_ = lean_ctor_get_uint8(v_options_2528_, sizeof(void*)*1);
if (v_hasTrace_2529_ == 0)
{
lean_object* v_cancelTk_x3f_2530_; lean_object* v___x_2531_; 
lean_dec_ref(v___f_2495_);
lean_dec_ref(v___x_2494_);
lean_dec(v___x_2492_);
v_cancelTk_x3f_2530_ = lean_ctor_get(v_toCold_2527_, 10);
lean_inc(v_decl_2491_);
v___x_2531_ = l_Lean_warnIfUsesSorry(v_decl_2491_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v___x_2532_; lean_object* v_env_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
lean_dec_ref_known(v___x_2531_, 1);
v___x_2532_ = lean_st_ref_get(v___y_2497_);
v_env_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc_ref(v_env_2533_);
lean_dec(v___x_2532_);
v___x_2534_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2496_);
v___x_2535_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2533_, v___x_2534_, v_decl_2491_, v_cancelTk_x3f_2530_);
lean_dec_ref(v___x_2534_);
v___x_2536_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2535_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; lean_object* v___x_2538_; 
lean_dec(v_decl_2491_);
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_a_2537_);
lean_dec_ref_known(v___x_2536_, 1);
v___x_2538_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2537_, v___y_2497_);
return v___x_2538_;
}
else
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2546_; 
v_a_2539_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2541_ = v___x_2536_;
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2536_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2544_; 
lean_inc(v_a_2539_);
if (v_isShared_2542_ == 0)
{
v___x_2544_ = v___x_2541_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_a_2539_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
v___y_2514_ = v___x_2544_;
v_a_2515_ = v_a_2539_;
goto v___jp_2513_;
}
}
}
}
else
{
lean_dec(v_decl_2491_);
return v___x_2531_;
}
}
else
{
lean_object* v_cancelTk_x3f_2547_; lean_object* v_inheritedTraceOptions_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; uint8_t v___x_2551_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v_a_2555_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v_a_2570_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v_a_2575_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v_a_2583_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v_a_2595_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v_a_2600_; 
v_cancelTk_x3f_2547_ = lean_ctor_get(v_toCold_2527_, 10);
v_inheritedTraceOptions_2548_ = lean_ctor_get(v_toCold_2527_, 11);
v___x_2549_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v___x_2492_);
v___x_2550_ = l_Lean_Name_append(v___x_2549_, v___x_2492_);
v___x_2551_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2548_, v_options_2528_, v___x_2550_);
lean_dec(v___x_2550_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2648_; uint8_t v___x_2649_; 
v___x_2648_ = l_Lean_trace_profiler;
v___x_2649_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2528_, v___x_2648_);
if (v___x_2649_ == 0)
{
lean_object* v___x_2650_; 
lean_dec_ref(v___f_2495_);
lean_dec_ref(v___x_2494_);
lean_dec(v___x_2492_);
lean_inc(v_decl_2491_);
v___x_2650_ = l_Lean_warnIfUsesSorry(v_decl_2491_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v___x_2651_; lean_object* v_env_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
lean_dec_ref_known(v___x_2650_, 1);
v___x_2651_ = lean_st_ref_get(v___y_2497_);
v_env_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc_ref(v_env_2652_);
lean_dec(v___x_2651_);
v___x_2653_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2496_);
v___x_2654_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2652_, v___x_2653_, v_decl_2491_, v_cancelTk_x3f_2547_);
lean_dec_ref(v___x_2653_);
v___x_2655_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2654_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; lean_object* v___x_2657_; 
lean_dec(v_decl_2491_);
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2656_);
lean_dec_ref_known(v___x_2655_, 1);
v___x_2657_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2656_, v___y_2497_);
return v___x_2657_;
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
v_a_2658_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2660_ = v___x_2655_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2655_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
lean_inc(v_a_2658_);
if (v_isShared_2661_ == 0)
{
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2658_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
v___y_2500_ = v___x_2663_;
v_a_2501_ = v_a_2658_;
goto v___jp_2499_;
}
}
}
}
else
{
lean_dec(v_decl_2491_);
return v___x_2650_;
}
}
else
{
goto v___jp_2605_;
}
}
else
{
goto v___jp_2605_;
}
v___jp_2552_:
{
lean_object* v___x_2556_; double v___x_2557_; double v___x_2558_; double v___x_2559_; double v___x_2560_; double v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2556_ = lean_io_mono_nanos_now();
v___x_2557_ = lean_float_of_nat(v___y_2553_);
v___x_2558_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_2559_ = lean_float_div(v___x_2557_, v___x_2558_);
v___x_2560_ = lean_float_of_nat(v___x_2556_);
v___x_2561_ = lean_float_div(v___x_2560_, v___x_2558_);
v___x_2562_ = lean_box_float(v___x_2559_);
v___x_2563_ = lean_box_float(v___x_2561_);
v___x_2564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2562_);
lean_ctor_set(v___x_2564_, 1, v___x_2563_);
v___x_2565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2565_, 0, v_a_2555_);
lean_ctor_set(v___x_2565_, 1, v___x_2564_);
v___x_2566_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2492_, v___x_2493_, v___x_2494_, v_options_2528_, v___x_2551_, v___y_2554_, v___f_2495_, v___x_2565_, v___y_2496_, v___y_2497_);
return v___x_2566_;
}
v___jp_2567_:
{
lean_object* v___x_2571_; 
v___x_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2571_, 0, v_a_2570_);
v___y_2553_ = v___y_2568_;
v___y_2554_ = v___y_2569_;
v_a_2555_ = v___x_2571_;
goto v___jp_2552_;
}
v___jp_2572_:
{
uint8_t v___x_2576_; 
v___x_2576_ = l_Lean_Exception_isInterrupt(v_a_2575_);
if (v___x_2576_ == 0)
{
uint8_t v___x_2577_; 
lean_inc_ref(v_a_2575_);
v___x_2577_ = l_Lean_Exception_isRuntime(v_a_2575_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2578_; 
v___x_2578_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2491_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_dec_ref_known(v___x_2578_, 1);
v___y_2568_ = v___y_2573_;
v___y_2569_ = v___y_2574_;
v_a_2570_ = v_a_2575_;
goto v___jp_2567_;
}
else
{
lean_object* v_a_2579_; 
lean_dec_ref(v_a_2575_);
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
lean_inc(v_a_2579_);
lean_dec_ref_known(v___x_2578_, 1);
v___y_2568_ = v___y_2573_;
v___y_2569_ = v___y_2574_;
v_a_2570_ = v_a_2579_;
goto v___jp_2567_;
}
}
else
{
lean_dec(v_decl_2491_);
v___y_2568_ = v___y_2573_;
v___y_2569_ = v___y_2574_;
v_a_2570_ = v_a_2575_;
goto v___jp_2567_;
}
}
else
{
lean_dec(v_decl_2491_);
v___y_2568_ = v___y_2573_;
v___y_2569_ = v___y_2574_;
v_a_2570_ = v_a_2575_;
goto v___jp_2567_;
}
}
v___jp_2580_:
{
lean_object* v___x_2584_; double v___x_2585_; double v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2584_ = lean_io_get_num_heartbeats();
v___x_2585_ = lean_float_of_nat(v___y_2581_);
v___x_2586_ = lean_float_of_nat(v___x_2584_);
v___x_2587_ = lean_box_float(v___x_2585_);
v___x_2588_ = lean_box_float(v___x_2586_);
v___x_2589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2587_);
lean_ctor_set(v___x_2589_, 1, v___x_2588_);
v___x_2590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2590_, 0, v_a_2583_);
lean_ctor_set(v___x_2590_, 1, v___x_2589_);
v___x_2591_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2492_, v___x_2493_, v___x_2494_, v_options_2528_, v___x_2551_, v___y_2582_, v___f_2495_, v___x_2590_, v___y_2496_, v___y_2497_);
return v___x_2591_;
}
v___jp_2592_:
{
lean_object* v___x_2596_; 
v___x_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2596_, 0, v_a_2595_);
v___y_2581_ = v___y_2593_;
v___y_2582_ = v___y_2594_;
v_a_2583_ = v___x_2596_;
goto v___jp_2580_;
}
v___jp_2597_:
{
uint8_t v___x_2601_; 
v___x_2601_ = l_Lean_Exception_isInterrupt(v_a_2600_);
if (v___x_2601_ == 0)
{
uint8_t v___x_2602_; 
lean_inc_ref(v_a_2600_);
v___x_2602_ = l_Lean_Exception_isRuntime(v_a_2600_);
if (v___x_2602_ == 0)
{
lean_object* v___x_2603_; 
v___x_2603_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2491_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_dec_ref_known(v___x_2603_, 1);
v___y_2593_ = v___y_2598_;
v___y_2594_ = v___y_2599_;
v_a_2595_ = v_a_2600_;
goto v___jp_2592_;
}
else
{
lean_object* v_a_2604_; 
lean_dec_ref(v_a_2600_);
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_a_2604_);
lean_dec_ref_known(v___x_2603_, 1);
v___y_2593_ = v___y_2598_;
v___y_2594_ = v___y_2599_;
v_a_2595_ = v_a_2604_;
goto v___jp_2592_;
}
}
else
{
lean_dec(v_decl_2491_);
v___y_2593_ = v___y_2598_;
v___y_2594_ = v___y_2599_;
v_a_2595_ = v_a_2600_;
goto v___jp_2592_;
}
}
else
{
lean_dec(v_decl_2491_);
v___y_2593_ = v___y_2598_;
v___y_2594_ = v___y_2599_;
v_a_2595_ = v_a_2600_;
goto v___jp_2592_;
}
}
v___jp_2605_:
{
lean_object* v___x_2606_; lean_object* v_a_2607_; lean_object* v___x_2608_; uint8_t v___x_2609_; 
v___x_2606_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2497_);
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2607_);
lean_dec_ref(v___x_2606_);
v___x_2608_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2609_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2528_, v___x_2608_);
if (v___x_2609_ == 0)
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = lean_io_mono_nanos_now();
lean_inc(v_decl_2491_);
v___x_2611_ = l_Lean_warnIfUsesSorry(v_decl_2491_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v___x_2612_; lean_object* v_env_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
lean_dec_ref_known(v___x_2611_, 1);
v___x_2612_ = lean_st_ref_get(v___y_2497_);
v_env_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc_ref(v_env_2613_);
lean_dec(v___x_2612_);
v___x_2614_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2496_);
v___x_2615_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2613_, v___x_2614_, v_decl_2491_, v_cancelTk_x3f_2547_);
lean_dec_ref(v___x_2614_);
v___x_2616_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2615_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; lean_object* v___x_2618_; lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_dec(v_decl_2491_);
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2617_);
lean_dec_ref_known(v___x_2616_, 1);
v___x_2618_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2617_, v___y_2497_);
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2618_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2618_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
lean_ctor_set_tag(v___x_2621_, 1);
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
v___y_2553_ = v___x_2610_;
v___y_2554_ = v_a_2607_;
v_a_2555_ = v___x_2624_;
goto v___jp_2552_;
}
}
}
else
{
lean_object* v_a_2627_; 
v_a_2627_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2627_);
lean_dec_ref_known(v___x_2616_, 1);
v___y_2573_ = v___x_2610_;
v___y_2574_ = v_a_2607_;
v_a_2575_ = v_a_2627_;
goto v___jp_2572_;
}
}
else
{
lean_object* v_a_2628_; 
lean_dec(v_decl_2491_);
v_a_2628_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_a_2628_);
lean_dec_ref_known(v___x_2611_, 1);
v___y_2568_ = v___x_2610_;
v___y_2569_ = v_a_2607_;
v_a_2570_ = v_a_2628_;
goto v___jp_2567_;
}
}
else
{
lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2629_ = lean_io_get_num_heartbeats();
lean_inc(v_decl_2491_);
v___x_2630_ = l_Lean_warnIfUsesSorry(v_decl_2491_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v___x_2631_; lean_object* v_env_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
lean_dec_ref_known(v___x_2630_, 1);
v___x_2631_ = lean_st_ref_get(v___y_2497_);
v_env_2632_ = lean_ctor_get(v___x_2631_, 0);
lean_inc_ref(v_env_2632_);
lean_dec(v___x_2631_);
v___x_2633_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2496_);
v___x_2634_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2632_, v___x_2633_, v_decl_2491_, v_cancelTk_x3f_2547_);
lean_dec_ref(v___x_2633_);
v___x_2635_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2634_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v_a_2636_; lean_object* v___x_2637_; lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_dec(v_decl_2491_);
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_a_2636_);
lean_dec_ref_known(v___x_2635_, 1);
v___x_2637_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2636_, v___y_2497_);
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2637_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2637_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
lean_ctor_set_tag(v___x_2640_, 1);
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
v___y_2581_ = v___x_2629_;
v___y_2582_ = v_a_2607_;
v_a_2583_ = v___x_2643_;
goto v___jp_2580_;
}
}
}
else
{
lean_object* v_a_2646_; 
v_a_2646_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_a_2646_);
lean_dec_ref_known(v___x_2635_, 1);
v___y_2598_ = v___x_2629_;
v___y_2599_ = v_a_2607_;
v_a_2600_ = v_a_2646_;
goto v___jp_2597_;
}
}
else
{
lean_object* v_a_2647_; 
lean_dec(v_decl_2491_);
v_a_2647_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2647_);
lean_dec_ref_known(v___x_2630_, 1);
v___y_2593_ = v___x_2629_;
v___y_2594_ = v_a_2607_;
v_a_2595_ = v_a_2647_;
goto v___jp_2592_;
}
}
}
}
v___jp_2499_:
{
uint8_t v___x_2502_; 
v___x_2502_ = l_Lean_Exception_isInterrupt(v_a_2501_);
if (v___x_2502_ == 0)
{
uint8_t v___x_2503_; 
lean_inc_ref(v_a_2501_);
v___x_2503_ = l_Lean_Exception_isRuntime(v_a_2501_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2504_; 
lean_dec_ref(v___y_2500_);
v___x_2504_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2491_, v___y_2496_, v___y_2497_);
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
lean_ctor_set(v___x_2506_, 0, v_a_2501_);
v___x_2509_ = v___x_2506_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2501_);
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
lean_dec_ref(v_a_2501_);
return v___x_2504_;
}
}
else
{
lean_dec_ref(v_a_2501_);
lean_dec(v_decl_2491_);
return v___y_2500_;
}
}
else
{
lean_dec_ref(v_a_2501_);
lean_dec(v_decl_2491_);
return v___y_2500_;
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
if (v___x_2517_ == 0)
{
lean_object* v___x_2518_; 
lean_dec_ref(v___y_2514_);
v___x_2518_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2491_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2525_ == 0)
{
lean_object* v_unused_2526_; 
v_unused_2526_ = lean_ctor_get(v___x_2518_, 0);
lean_dec(v_unused_2526_);
v___x_2520_ = v___x_2518_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_dec(v___x_2518_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
lean_ctor_set_tag(v___x_2520_, 1);
lean_ctor_set(v___x_2520_, 0, v_a_2515_);
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2515_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
else
{
lean_dec_ref(v_a_2515_);
return v___x_2518_;
}
}
else
{
lean_dec_ref(v_a_2515_);
lean_dec(v_decl_2491_);
return v___y_2514_;
}
}
else
{
lean_dec_ref(v_a_2515_);
lean_dec(v_decl_2491_);
return v___y_2514_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed(lean_object* v_decl_2666_, lean_object* v___x_2667_, lean_object* v___x_2668_, lean_object* v___x_2669_, lean_object* v___f_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
uint8_t v___x_7773__boxed_2674_; lean_object* v_res_2675_; 
v___x_7773__boxed_2674_ = lean_unbox(v___x_2668_);
v_res_2675_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(v_decl_2666_, v___x_2667_, v___x_7773__boxed_2674_, v___x_2669_, v___f_2670_, v___y_2671_, v___y_2672_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(lean_object* v_decl_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_){
_start:
{
lean_object* v___f_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; uint8_t v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___f_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
lean_inc(v_decl_2680_);
v___f_2684_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2684_, 0, v_decl_2680_);
v___x_2685_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2681_);
v___x_2686_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__0));
v___x_2687_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__2));
v___x_2688_ = 1;
v___x_2689_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2690_ = lean_box(v___x_2688_);
v___f_2691_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed), 8, 5);
lean_closure_set(v___f_2691_, 0, v_decl_2680_);
lean_closure_set(v___f_2691_, 1, v___x_2687_);
lean_closure_set(v___f_2691_, 2, v___x_2690_);
lean_closure_set(v___f_2691_, 3, v___x_2689_);
lean_closure_set(v___f_2691_, 4, v___f_2684_);
v___x_2692_ = lean_box(0);
v___x_2693_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v___x_2686_, v___x_2685_, v___f_2691_, v___x_2692_, v_a_2681_, v_a_2682_);
lean_dec_ref(v___x_2685_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___boxed(lean_object* v_decl_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2694_, v_a_2695_, v_a_2696_);
lean_dec(v_a_2696_);
lean_dec_ref(v_a_2695_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(lean_object* v_00_u03b1_2699_, lean_object* v_x_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
lean_object* v___x_2704_; 
v___x_2704_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_x_2700_);
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2705_, lean_object* v_x_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(v_00_u03b1_2705_, v_x_2706_, v___y_2707_, v___y_2708_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(lean_object* v___y_2711_, lean_object* v_a_2712_, lean_object* v_ref_2713_, lean_object* v_a_x3f_2714_){
_start:
{
lean_object* v___x_2716_; lean_object* v_env_2717_; lean_object* v___x_2718_; 
v___x_2716_ = lean_st_ref_get(v___y_2711_);
v_env_2717_ = lean_ctor_get(v___x_2716_, 0);
lean_inc_ref(v_env_2717_);
lean_dec(v___x_2716_);
v___x_2718_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2712_, v_env_2717_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
lean_dec(v_ref_2713_);
v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2718_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2718_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
else
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2738_; 
v_a_2727_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2729_ = v___x_2718_;
v_isShared_2730_ = v_isSharedCheck_2738_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2718_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2738_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2736_; 
v___x_2731_ = lean_io_error_to_string(v_a_2727_);
v___x_2732_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2731_);
v___x_2733_ = l_Lean_MessageData_ofFormat(v___x_2732_);
v___x_2734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2734_, 0, v_ref_2713_);
lean_ctor_set(v___x_2734_, 1, v___x_2733_);
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 0, v___x_2734_);
v___x_2736_ = v___x_2729_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2734_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed(lean_object* v___y_2739_, lean_object* v_a_2740_, lean_object* v_ref_2741_, lean_object* v_a_x3f_2742_, lean_object* v___y_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2739_, v_a_2740_, v_ref_2741_, v_a_x3f_2742_);
lean_dec(v_a_x3f_2742_);
lean_dec(v___y_2739_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v_a_2747_, lean_object* v_a_x3f_2748_){
_start:
{
lean_object* v___x_2750_; lean_object* v_env_2751_; lean_object* v_ref_2752_; lean_object* v___x_2753_; 
v___x_2750_ = lean_st_ref_get(v___y_2745_);
v_env_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc_ref(v_env_2751_);
lean_dec(v___x_2750_);
v_ref_2752_ = lean_ctor_get(v___y_2746_, 2);
v___x_2753_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2747_, v_env_2751_);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2761_; 
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2756_ = v___x_2753_;
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2753_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2759_; 
if (v_isShared_2757_ == 0)
{
v___x_2759_ = v___x_2756_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2754_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2773_; 
v_a_2762_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2764_ = v___x_2753_;
v_isShared_2765_ = v_isSharedCheck_2773_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2753_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2773_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2771_; 
v___x_2766_ = lean_io_error_to_string(v_a_2762_);
v___x_2767_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
v___x_2768_ = l_Lean_MessageData_ofFormat(v___x_2767_);
lean_inc(v_ref_2752_);
v___x_2769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2769_, 0, v_ref_2752_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v___x_2769_);
v___x_2771_ = v___x_2764_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v___x_2769_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___boxed(lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v_a_2776_, lean_object* v_a_x3f_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v___y_2774_, v___y_2775_, v_a_2776_, v_a_x3f_2777_);
lean_dec(v_a_x3f_2777_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(lean_object* v_a_2780_, lean_object* v_asyncEnv_2781_, lean_object* v_decl_2782_, lean_object* v_x_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
lean_object* v___x_2787_; lean_object* v_r_2788_; 
v___x_2787_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_asyncEnv_2781_, v___y_2785_);
lean_dec_ref(v___x_2787_);
v_r_2788_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2782_, v___y_2784_, v___y_2785_);
if (lean_obj_tag(v_r_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2805_; 
v_a_2789_ = lean_ctor_get(v_r_2788_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v_r_2788_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2791_ = v_r_2788_;
v_isShared_2792_ = v_isSharedCheck_2805_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v_r_2788_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2805_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
lean_inc(v_a_2789_);
if (v_isShared_2792_ == 0)
{
lean_ctor_set_tag(v___x_2791_, 1);
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_a_2789_);
v___x_2794_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
lean_object* v___x_2795_; 
v___x_2795_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v___y_2785_, v___y_2784_, v_a_2780_, v___x_2794_);
lean_dec_ref(v___x_2794_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2802_ == 0)
{
lean_object* v_unused_2803_; 
v_unused_2803_ = lean_ctor_get(v___x_2795_, 0);
lean_dec(v_unused_2803_);
v___x_2797_ = v___x_2795_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_dec(v___x_2795_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 0, v_a_2789_);
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2789_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
else
{
lean_dec(v_a_2789_);
return v___x_2795_;
}
}
}
}
else
{
lean_object* v_a_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v_a_2806_ = lean_ctor_get(v_r_2788_, 0);
lean_inc(v_a_2806_);
lean_dec_ref_known(v_r_2788_, 1);
v___x_2807_ = lean_box(0);
v___x_2808_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v___y_2785_, v___y_2784_, v_a_2780_, v___x_2807_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2815_ == 0)
{
lean_object* v_unused_2816_; 
v_unused_2816_ = lean_ctor_get(v___x_2808_, 0);
lean_dec(v_unused_2816_);
v___x_2810_ = v___x_2808_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_dec(v___x_2808_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
lean_ctor_set_tag(v___x_2810_, 1);
lean_ctor_set(v___x_2810_, 0, v_a_2806_);
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2806_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
else
{
lean_dec(v_a_2806_);
return v___x_2808_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed(lean_object* v_a_2817_, lean_object* v_asyncEnv_2818_, lean_object* v_decl_2819_, lean_object* v_x_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(v_a_2817_, v_asyncEnv_2818_, v_decl_2819_, v_x_2820_, v___y_2821_, v___y_2822_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
lean_dec_ref(v_x_2820_);
return v_res_2824_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__0));
v___x_2827_ = l_Lean_stringToMessageData(v___x_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(lean_object* v_decl_2828_, lean_object* v_x_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2833_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1);
v___x_2834_ = l_Lean_Declaration_getNames(v_decl_2828_);
v___x_2835_ = lean_box(0);
v___x_2836_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2834_, v___x_2835_);
v___x_2837_ = l_Lean_MessageData_ofList(v___x_2836_);
v___x_2838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2833_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
v___x_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2838_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed(lean_object* v_decl_2840_, lean_object* v_x_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_2840_, v_x_2841_, v___y_2842_, v___y_2843_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec_ref(v_x_2841_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(lean_object* v_cls_2848_, lean_object* v_msg_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v_ref_2853_; lean_object* v___x_2854_; lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2900_; 
v_ref_2853_ = lean_ctor_get(v___y_2850_, 2);
v___x_2854_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2849_, v___y_2850_, v___y_2851_);
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2857_ = v___x_2854_;
v_isShared_2858_ = v_isSharedCheck_2900_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2854_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2900_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2859_; lean_object* v_traceState_2860_; lean_object* v_env_2861_; lean_object* v_nextMacroScope_2862_; lean_object* v_ngen_2863_; lean_object* v_auxDeclNGen_2864_; lean_object* v_cache_2865_; lean_object* v_recordedDeps_2866_; lean_object* v_messages_2867_; lean_object* v_infoState_2868_; lean_object* v_snapshotTasks_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2899_; 
v___x_2859_ = lean_st_ref_take(v___y_2851_);
v_traceState_2860_ = lean_ctor_get(v___x_2859_, 4);
v_env_2861_ = lean_ctor_get(v___x_2859_, 0);
v_nextMacroScope_2862_ = lean_ctor_get(v___x_2859_, 1);
v_ngen_2863_ = lean_ctor_get(v___x_2859_, 2);
v_auxDeclNGen_2864_ = lean_ctor_get(v___x_2859_, 3);
v_cache_2865_ = lean_ctor_get(v___x_2859_, 5);
v_recordedDeps_2866_ = lean_ctor_get(v___x_2859_, 6);
v_messages_2867_ = lean_ctor_get(v___x_2859_, 7);
v_infoState_2868_ = lean_ctor_get(v___x_2859_, 8);
v_snapshotTasks_2869_ = lean_ctor_get(v___x_2859_, 9);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2871_ = v___x_2859_;
v_isShared_2872_ = v_isSharedCheck_2899_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_snapshotTasks_2869_);
lean_inc(v_infoState_2868_);
lean_inc(v_messages_2867_);
lean_inc(v_recordedDeps_2866_);
lean_inc(v_cache_2865_);
lean_inc(v_traceState_2860_);
lean_inc(v_auxDeclNGen_2864_);
lean_inc(v_ngen_2863_);
lean_inc(v_nextMacroScope_2862_);
lean_inc(v_env_2861_);
lean_dec(v___x_2859_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2899_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
uint64_t v_tid_2873_; lean_object* v_traces_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2898_; 
v_tid_2873_ = lean_ctor_get_uint64(v_traceState_2860_, sizeof(void*)*1);
v_traces_2874_ = lean_ctor_get(v_traceState_2860_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v_traceState_2860_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2876_ = v_traceState_2860_;
v_isShared_2877_ = v_isSharedCheck_2898_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_traces_2874_);
lean_dec(v_traceState_2860_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2898_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; double v___x_2880_; uint8_t v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2889_; 
v___x_2878_ = lean_box(0);
v___x_2879_ = lean_box(0);
v___x_2880_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0);
v___x_2881_ = 0;
v___x_2882_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2883_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2883_, 0, v_cls_2848_);
lean_ctor_set(v___x_2883_, 1, v___x_2879_);
lean_ctor_set(v___x_2883_, 2, v___x_2882_);
lean_ctor_set_float(v___x_2883_, sizeof(void*)*3, v___x_2880_);
lean_ctor_set_float(v___x_2883_, sizeof(void*)*3 + 8, v___x_2880_);
lean_ctor_set_uint8(v___x_2883_, sizeof(void*)*3 + 16, v___x_2881_);
v___x_2884_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___closed__0));
v___x_2885_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2883_);
lean_ctor_set(v___x_2885_, 1, v_a_2855_);
lean_ctor_set(v___x_2885_, 2, v___x_2884_);
lean_inc(v_ref_2853_);
v___x_2886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2886_, 0, v_ref_2853_);
lean_ctor_set(v___x_2886_, 1, v___x_2885_);
v___x_2887_ = l_Lean_PersistentArray_push___redArg(v_traces_2874_, v___x_2886_);
if (v_isShared_2877_ == 0)
{
lean_ctor_set(v___x_2876_, 0, v___x_2887_);
v___x_2889_ = v___x_2876_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v___x_2887_);
lean_ctor_set_uint64(v_reuseFailAlloc_2897_, sizeof(void*)*1, v_tid_2873_);
v___x_2889_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
lean_object* v___x_2891_; 
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 4, v___x_2889_);
v___x_2891_ = v___x_2871_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_env_2861_);
lean_ctor_set(v_reuseFailAlloc_2896_, 1, v_nextMacroScope_2862_);
lean_ctor_set(v_reuseFailAlloc_2896_, 2, v_ngen_2863_);
lean_ctor_set(v_reuseFailAlloc_2896_, 3, v_auxDeclNGen_2864_);
lean_ctor_set(v_reuseFailAlloc_2896_, 4, v___x_2889_);
lean_ctor_set(v_reuseFailAlloc_2896_, 5, v_cache_2865_);
lean_ctor_set(v_reuseFailAlloc_2896_, 6, v_recordedDeps_2866_);
lean_ctor_set(v_reuseFailAlloc_2896_, 7, v_messages_2867_);
lean_ctor_set(v_reuseFailAlloc_2896_, 8, v_infoState_2868_);
lean_ctor_set(v_reuseFailAlloc_2896_, 9, v_snapshotTasks_2869_);
v___x_2891_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
lean_object* v___x_2892_; lean_object* v___x_2894_; 
v___x_2892_ = lean_st_ref_put(v___y_2851_, v___x_2891_);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 0, v___x_2878_);
v___x_2894_ = v___x_2857_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2878_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___boxed(lean_object* v_cls_2901_, lean_object* v_msg_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2901_, v_msg_2902_, v___y_2903_, v___y_2904_);
lean_dec(v___y_2904_);
lean_dec_ref(v___y_2903_);
return v_res_2906_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1(void){
_start:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2908_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__0));
v___x_2909_ = l_Lean_stringToMessageData(v___x_2908_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(lean_object* v_decl_2910_, lean_object* v_cls_2911_, lean_object* v_x_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
lean_object* v_toCold_2916_; lean_object* v_options_2917_; uint8_t v_hasTrace_2918_; 
v_toCold_2916_ = lean_ctor_get(v___y_2913_, 0);
v_options_2917_ = lean_ctor_get(v_toCold_2916_, 2);
v_hasTrace_2918_ = lean_ctor_get_uint8(v_options_2917_, sizeof(void*)*1);
if (v_hasTrace_2918_ == 0)
{
lean_object* v___x_2919_; 
lean_dec(v_cls_2911_);
v___x_2919_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2910_, v___y_2913_, v___y_2914_);
return v___x_2919_;
}
else
{
lean_object* v_inheritedTraceOptions_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; uint8_t v___x_2923_; 
v_inheritedTraceOptions_2920_ = lean_ctor_get(v_toCold_2916_, 11);
v___x_2921_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2911_);
v___x_2922_ = l_Lean_Name_append(v___x_2921_, v_cls_2911_);
v___x_2923_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2920_, v_options_2917_, v___x_2922_);
lean_dec(v___x_2922_);
if (v___x_2923_ == 0)
{
lean_object* v___x_2924_; 
lean_dec(v_cls_2911_);
v___x_2924_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2910_, v___y_2913_, v___y_2914_);
return v___x_2924_;
}
else
{
lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2925_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
v___x_2926_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2911_, v___x_2925_, v___y_2913_, v___y_2914_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v___x_2927_; 
lean_dec_ref_known(v___x_2926_, 1);
v___x_2927_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2910_, v___y_2913_, v___y_2914_);
return v___x_2927_;
}
else
{
lean_dec(v_decl_2910_);
return v___x_2926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___boxed(lean_object* v_decl_2928_, lean_object* v_cls_2929_, lean_object* v_x_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_2928_, v_cls_2929_, v_x_2930_, v___y_2931_, v___y_2932_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v_x_2930_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(lean_object* v_opt_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v___x_2938_; uint8_t v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2938_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2936_);
v___x_2939_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_2938_, v_opt_2935_);
lean_dec_ref(v___x_2938_);
v___x_2940_ = lean_box(v___x_2939_);
v___x_2941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg___boxed(lean_object* v_opt_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_2942_, v___y_2943_);
lean_dec_ref(v___y_2943_);
lean_dec_ref(v_opt_2942_);
return v_res_2945_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(lean_object* v_x_2946_){
_start:
{
if (lean_obj_tag(v_x_2946_) == 0)
{
uint8_t v___x_2947_; 
v___x_2947_ = 1;
return v___x_2947_;
}
else
{
lean_object* v_head_2948_; lean_object* v_tail_2949_; uint8_t v___x_2950_; 
v_head_2948_ = lean_ctor_get(v_x_2946_, 0);
v_tail_2949_ = lean_ctor_get(v_x_2946_, 1);
v___x_2950_ = l_Lean_isPrivateName(v_head_2948_);
if (v___x_2950_ == 0)
{
return v___x_2950_;
}
else
{
v_x_2946_ = v_tail_2949_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2___boxed(lean_object* v_x_2952_){
_start:
{
uint8_t v_res_2953_; lean_object* v_r_2954_; 
v_res_2953_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v_x_2952_);
lean_dec(v_x_2952_);
v_r_2954_ = lean_box(v_res_2953_);
return v_r_2954_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3(void){
_start:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2960_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__2));
v___x_2961_ = l_Lean_stringToMessageData(v___x_2960_);
return v___x_2961_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5(void){
_start:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2963_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__4));
v___x_2964_ = l_Lean_stringToMessageData(v___x_2963_);
return v___x_2964_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7(void){
_start:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2966_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__6));
v___x_2967_ = l_Lean_stringToMessageData(v___x_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(lean_object* v_decl_2968_, uint8_t v_hasTrace_2969_, uint8_t v___x_2970_, lean_object* v_cls_2971_, uint8_t v___x_2972_, lean_object* v___x_2973_, lean_object* v___x_2974_, lean_object* v_____x_2975_, lean_object* v_exportedInfo_x3f_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v_a_2983_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v_snd_3075_; lean_object* v_fst_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3208_; 
v_snd_3075_ = lean_ctor_get(v_____x_2975_, 1);
v_fst_3076_ = lean_ctor_get(v_____x_2975_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v_____x_2975_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3078_ = v_____x_2975_;
v_isShared_3079_ = v_isSharedCheck_3208_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_snd_3075_);
lean_inc(v_fst_3076_);
lean_dec(v_____x_2975_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3208_;
goto v_resetjp_3077_;
}
v___jp_2980_:
{
lean_object* v___x_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
v___x_2984_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2981_, v___y_2982_);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_2991_ == 0)
{
lean_object* v_unused_2992_; 
v_unused_2992_ = lean_ctor_get(v___x_2984_, 0);
lean_dec(v_unused_2992_);
v___x_2986_ = v___x_2984_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_dec(v___x_2984_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
if (v_isShared_2987_ == 0)
{
lean_ctor_set_tag(v___x_2986_, 1);
lean_ctor_set(v___x_2986_, 0, v_a_2983_);
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_a_2983_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
v___jp_2993_:
{
lean_object* v___x_3005_; 
lean_inc_ref(v___y_2997_);
v___x_3005_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_2995_, v___y_2997_, v___y_2994_, v___y_3004_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v___x_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3061_; 
lean_dec_ref_known(v___x_3005_, 1);
lean_dec(v___y_2998_);
lean_inc_ref(v___y_2996_);
v___x_3006_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2996_, v___y_2999_);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3061_ == 0)
{
lean_object* v_unused_3062_; 
v_unused_3062_ = lean_ctor_get(v___x_3006_, 0);
lean_dec(v_unused_3062_);
v___x_3008_ = v___x_3006_;
v_isShared_3009_ = v_isSharedCheck_3061_;
goto v_resetjp_3007_;
}
else
{
lean_dec(v___x_3006_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3061_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; uint8_t v___x_3012_; 
v___x_3010_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3000_);
v___x_3011_ = l_Lean_Elab_async;
v___x_3012_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_3010_, v___x_3011_);
lean_dec_ref(v___x_3010_);
if (v___x_3012_ == 0)
{
lean_object* v___x_3013_; lean_object* v_r_3014_; 
lean_del_object(v___x_3008_);
lean_dec_ref(v___y_3002_);
lean_dec_ref(v___y_3001_);
v___x_3013_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2997_, v___y_2999_);
lean_dec_ref(v___x_3013_);
v_r_3014_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2968_, v___y_3000_, v___y_2999_);
if (lean_obj_tag(v_r_3014_) == 0)
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3033_; 
v_a_3015_ = lean_ctor_get(v_r_3014_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v_r_3014_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3017_ = v_r_3014_;
v_isShared_3018_ = v_isSharedCheck_3033_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v_r_3014_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3033_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
lean_inc(v_a_3015_);
if (v_isShared_3018_ == 0)
{
lean_ctor_set_tag(v___x_3017_, 1);
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3015_);
v___x_3020_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
lean_object* v___x_3021_; 
v___x_3021_ = lean_apply_2(v___y_3003_, v___x_3020_, lean_box(0));
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v___x_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
lean_dec_ref_known(v___x_3021_, 1);
v___x_3022_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2996_, v___y_2999_);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3029_ == 0)
{
lean_object* v_unused_3030_; 
v_unused_3030_ = lean_ctor_get(v___x_3022_, 0);
lean_dec(v_unused_3030_);
v___x_3024_ = v___x_3022_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_dec(v___x_3022_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3027_; 
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 0, v_a_3015_);
v___x_3027_ = v___x_3024_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_a_3015_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
else
{
lean_object* v_a_3031_; 
lean_dec(v_a_3015_);
v_a_3031_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3031_);
lean_dec_ref_known(v___x_3021_, 1);
v___y_2981_ = v___y_2996_;
v___y_2982_ = v___y_2999_;
v_a_2983_ = v_a_3031_;
goto v___jp_2980_;
}
}
}
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v_a_3034_ = lean_ctor_get(v_r_3014_, 0);
lean_inc(v_a_3034_);
lean_dec_ref_known(v_r_3014_, 1);
v___x_3035_ = lean_box(0);
v___x_3036_ = lean_apply_2(v___y_3003_, v___x_3035_, lean_box(0));
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_dec_ref_known(v___x_3036_, 1);
v___y_2981_ = v___y_2996_;
v___y_2982_ = v___y_2999_;
v_a_2983_ = v_a_3034_;
goto v___jp_2980_;
}
else
{
lean_object* v_a_3037_; 
lean_dec(v_a_3034_);
v_a_3037_ = lean_ctor_get(v___x_3036_, 0);
lean_inc(v_a_3037_);
lean_dec_ref_known(v___x_3036_, 1);
v___y_2981_ = v___y_2996_;
v___y_2982_ = v___y_2999_;
v_a_2983_ = v_a_3037_;
goto v___jp_2980_;
}
}
}
else
{
lean_object* v___x_3038_; lean_object* v___x_3040_; 
lean_dec_ref(v___y_3003_);
lean_dec_ref(v___y_2997_);
lean_dec_ref(v___y_2996_);
lean_dec(v_decl_2968_);
v___x_3038_ = l_IO_CancelToken_new();
if (v_isShared_3009_ == 0)
{
lean_ctor_set_tag(v___x_3008_, 1);
lean_ctor_set(v___x_3008_, 0, v___x_3038_);
v___x_3040_ = v___x_3008_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v___x_3038_);
v___x_3040_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3041_ = lean_unsigned_to_nat(0u);
v___x_3042_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_3043_ = l_Lean_Name_toString(v___x_3042_, v_hasTrace_2969_);
lean_inc_ref(v___x_3040_);
v___x_3044_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3002_, v___x_3040_, v___x_3043_, v___y_3000_, v___y_2999_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v_checked_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc(v_a_3045_);
lean_dec_ref_known(v___x_3044_, 1);
v_checked_3046_ = lean_ctor_get(v___y_3001_, 2);
lean_inc_ref(v_checked_3046_);
lean_dec_ref(v___y_3001_);
v___x_3047_ = lean_io_map_task(v_a_3045_, v_checked_3046_, v___x_3041_, v___x_2970_);
v___x_3048_ = lean_box(0);
v___x_3049_ = lean_box(2);
v___x_3050_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3048_);
lean_ctor_set(v___x_3050_, 1, v___x_3049_);
lean_ctor_set(v___x_3050_, 2, v___x_3040_);
lean_ctor_set(v___x_3050_, 3, v___x_3047_);
v___x_3051_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3050_, v___y_2999_);
return v___x_3051_;
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
lean_dec_ref(v___x_3040_);
lean_dec_ref(v___y_3001_);
v_a_3052_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3054_ = v___x_3044_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_3044_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3052_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3074_; 
lean_dec_ref(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec_ref(v___y_3001_);
lean_dec_ref(v___y_2997_);
lean_dec_ref(v___y_2996_);
lean_dec(v_decl_2968_);
v_a_3063_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3065_ = v___x_3005_;
v_isShared_3066_ = v_isSharedCheck_3074_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_3005_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3074_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3072_; 
v___x_3067_ = lean_io_error_to_string(v_a_3063_);
v___x_3068_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
v___x_3069_ = l_Lean_MessageData_ofFormat(v___x_3068_);
v___x_3070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___y_2998_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 0, v___x_3070_);
v___x_3072_ = v___x_3065_;
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
lean_object* v_fst_3080_; lean_object* v_snd_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3207_; 
v_fst_3080_ = lean_ctor_get(v_snd_3075_, 0);
v_snd_3081_ = lean_ctor_get(v_snd_3075_, 1);
v_isSharedCheck_3207_ = !lean_is_exclusive(v_snd_3075_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3083_ = v_snd_3075_;
v_isShared_3084_ = v_isSharedCheck_3207_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_snd_3081_);
lean_inc(v_fst_3080_);
lean_dec(v_snd_3075_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3207_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v_exportedInfo_x3f_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___x_3197_; lean_object* v_env_3198_; uint8_t v___x_3199_; 
v___x_3197_ = lean_st_ref_get(v___y_2978_);
v_env_3198_ = lean_ctor_get(v___x_3197_, 0);
lean_inc_ref(v_env_3198_);
lean_dec(v___x_3197_);
v___x_3199_ = l_Lean_Environment_containsOnBranch(v_env_3198_, v_fst_3076_);
lean_dec_ref(v_env_3198_);
if (v___x_3199_ == 0)
{
lean_del_object(v___x_3078_);
v___y_3135_ = v___y_2977_;
v___y_3136_ = v___y_2978_;
goto v___jp_3134_;
}
else
{
lean_object* v___x_3200_; lean_object* v_env_3201_; lean_object* v___x_3202_; lean_object* v___x_3204_; 
lean_del_object(v___x_3083_);
lean_dec(v_snd_3081_);
lean_dec(v_fst_3080_);
lean_dec(v_exportedInfo_x3f_2976_);
lean_dec(v___x_2974_);
lean_dec_ref(v___x_2973_);
lean_dec(v_cls_2971_);
lean_dec(v_decl_2968_);
v___x_3200_ = lean_st_ref_get(v___y_2978_);
v_env_3201_ = lean_ctor_get(v___x_3200_, 0);
lean_inc_ref(v_env_3201_);
lean_dec(v___x_3200_);
v___x_3202_ = lean_elab_environment_to_kernel_env(v_env_3201_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set_tag(v___x_3078_, 1);
lean_ctor_set(v___x_3078_, 1, v_fst_3076_);
lean_ctor_set(v___x_3078_, 0, v___x_3202_);
v___x_3204_ = v___x_3078_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3202_);
lean_ctor_set(v_reuseFailAlloc_3206_, 1, v_fst_3076_);
v___x_3204_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
lean_object* v___x_3205_; 
v___x_3205_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3204_, v___y_2977_, v___y_2978_);
return v___x_3205_;
}
}
v___jp_3085_:
{
lean_object* v_ref_3091_; uint8_t v___x_3092_; lean_object* v___x_3093_; 
v_ref_3091_ = lean_ctor_get(v___y_3088_, 2);
v___x_3092_ = lean_unbox(v_snd_3081_);
lean_dec(v_snd_3081_);
lean_inc_ref(v___y_3089_);
v___x_3093_ = l_Lean_Environment_addConstAsync(v___y_3089_, v_fst_3076_, v___x_3092_, v___y_3090_, v___x_2970_, v_hasTrace_2969_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3094_; lean_object* v_mainEnv_3095_; lean_object* v_asyncEnv_3096_; lean_object* v___f_3097_; lean_object* v___f_3098_; lean_object* v___x_3099_; 
lean_del_object(v___x_3083_);
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
lean_inc_n(v_a_3094_, 3);
lean_dec_ref_known(v___x_3093_, 1);
v_mainEnv_3095_ = lean_ctor_get(v_a_3094_, 0);
lean_inc_ref(v_mainEnv_3095_);
v_asyncEnv_3096_ = lean_ctor_get(v_a_3094_, 1);
lean_inc_ref_n(v_asyncEnv_3096_, 2);
lean_inc(v_ref_3091_);
lean_inc(v___y_3086_);
v___f_3097_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3097_, 0, v___y_3086_);
lean_closure_set(v___f_3097_, 1, v_a_3094_);
lean_closure_set(v___f_3097_, 2, v_ref_3091_);
lean_inc(v_decl_2968_);
v___f_3098_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3098_, 0, v_a_3094_);
lean_closure_set(v___f_3098_, 1, v_asyncEnv_3096_);
lean_closure_set(v___f_3098_, 2, v_decl_2968_);
v___x_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3099_, 0, v_fst_3080_);
if (lean_obj_tag(v___y_3087_) == 0)
{
lean_inc(v_ref_3091_);
lean_inc_ref(v___x_3099_);
v___y_2994_ = v___x_3099_;
v___y_2995_ = v_a_3094_;
v___y_2996_ = v_mainEnv_3095_;
v___y_2997_ = v_asyncEnv_3096_;
v___y_2998_ = v_ref_3091_;
v___y_2999_ = v___y_3086_;
v___y_3000_ = v___y_3088_;
v___y_3001_ = v___y_3089_;
v___y_3002_ = v___f_3098_;
v___y_3003_ = v___f_3097_;
v___y_3004_ = v___x_3099_;
goto v___jp_2993_;
}
else
{
lean_inc(v_ref_3091_);
v___y_2994_ = v___x_3099_;
v___y_2995_ = v_a_3094_;
v___y_2996_ = v_mainEnv_3095_;
v___y_2997_ = v_asyncEnv_3096_;
v___y_2998_ = v_ref_3091_;
v___y_2999_ = v___y_3086_;
v___y_3000_ = v___y_3088_;
v___y_3001_ = v___y_3089_;
v___y_3002_ = v___f_3098_;
v___y_3003_ = v___f_3097_;
v___y_3004_ = v___y_3087_;
goto v___jp_2993_;
}
}
else
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3113_; 
lean_dec_ref(v___y_3089_);
lean_dec(v___y_3087_);
lean_dec(v_fst_3080_);
lean_dec(v_decl_2968_);
v_a_3100_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3102_ = v___x_3093_;
v_isShared_3103_ = v_isSharedCheck_3113_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3093_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3113_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3108_; 
v___x_3104_ = lean_io_error_to_string(v_a_3100_);
v___x_3105_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3104_);
v___x_3106_ = l_Lean_MessageData_ofFormat(v___x_3105_);
lean_inc(v_ref_3091_);
if (v_isShared_3084_ == 0)
{
lean_ctor_set(v___x_3083_, 1, v___x_3106_);
lean_ctor_set(v___x_3083_, 0, v_ref_3091_);
v___x_3108_ = v___x_3083_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_ref_3091_);
lean_ctor_set(v_reuseFailAlloc_3112_, 1, v___x_3106_);
v___x_3108_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
lean_object* v___x_3110_; 
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 0, v___x_3108_);
v___x_3110_ = v___x_3102_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3108_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
}
v___jp_3114_:
{
lean_object* v___x_3118_; 
v___x_3118_ = lean_st_ref_get(v___y_3117_);
if (lean_obj_tag(v_exportedInfo_x3f_3115_) == 0)
{
lean_object* v_env_3119_; lean_object* v___x_3120_; 
v_env_3119_ = lean_ctor_get(v___x_3118_, 0);
lean_inc_ref(v_env_3119_);
lean_dec(v___x_3118_);
v___x_3120_ = lean_box(0);
v___y_3086_ = v___y_3117_;
v___y_3087_ = v_exportedInfo_x3f_3115_;
v___y_3088_ = v___y_3116_;
v___y_3089_ = v_env_3119_;
v___y_3090_ = v___x_3120_;
goto v___jp_3085_;
}
else
{
lean_object* v_env_3121_; lean_object* v_val_3122_; uint8_t v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v_env_3121_ = lean_ctor_get(v___x_3118_, 0);
lean_inc_ref(v_env_3121_);
lean_dec(v___x_3118_);
v_val_3122_ = lean_ctor_get(v_exportedInfo_x3f_3115_, 0);
v___x_3123_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3122_);
v___x_3124_ = lean_box(v___x_3123_);
v___x_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3124_);
v___y_3086_ = v___y_3117_;
v___y_3087_ = v_exportedInfo_x3f_3115_;
v___y_3088_ = v___y_3116_;
v___y_3089_ = v_env_3121_;
v___y_3090_ = v___x_3125_;
goto v___jp_3085_;
}
}
v___jp_3126_:
{
lean_object* v___x_3129_; 
lean_inc(v_fst_3080_);
v___x_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3129_, 0, v_fst_3080_);
v_exportedInfo_x3f_3115_ = v___x_3129_;
v___y_3116_ = v___y_3127_;
v___y_3117_ = v___y_3128_;
goto v___jp_3114_;
}
v___jp_3130_:
{
lean_object* v___x_3133_; 
lean_inc(v_fst_3080_);
v___x_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3133_, 0, v_fst_3080_);
v_exportedInfo_x3f_3115_ = v___x_3133_;
v___y_3116_ = v___y_3131_;
v___y_3117_ = v___y_3132_;
goto v___jp_3114_;
}
v___jp_3134_:
{
lean_object* v___x_3137_; uint8_t v___x_3138_; 
lean_inc(v_decl_2968_);
v___x_3137_ = l_Lean_Declaration_getTopLevelNames(v_decl_2968_);
v___x_3138_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3137_);
lean_dec(v___x_3137_);
if (v___x_3138_ == 0)
{
lean_dec(v___x_2974_);
if (lean_obj_tag(v_exportedInfo_x3f_2976_) == 0)
{
lean_object* v_toCold_3139_; lean_object* v_options_3140_; uint8_t v_hasTrace_3141_; 
lean_dec_ref(v___x_2973_);
v_toCold_3139_ = lean_ctor_get(v___y_3135_, 0);
v_options_3140_ = lean_ctor_get(v_toCold_3139_, 2);
v_hasTrace_3141_ = lean_ctor_get_uint8(v_options_3140_, sizeof(void*)*1);
if (v_hasTrace_3141_ == 0)
{
lean_dec(v_cls_2971_);
v___y_3127_ = v___y_3135_;
v___y_3128_ = v___y_3136_;
goto v___jp_3126_;
}
else
{
lean_object* v_inheritedTraceOptions_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; uint8_t v___x_3145_; 
v_inheritedTraceOptions_3142_ = lean_ctor_get(v_toCold_3139_, 11);
v___x_3143_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2971_);
v___x_3144_ = l_Lean_Name_append(v___x_3143_, v_cls_2971_);
v___x_3145_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3142_, v_options_3140_, v___x_3144_);
lean_dec(v___x_3144_);
if (v___x_3145_ == 0)
{
lean_dec(v_cls_2971_);
v___y_3127_ = v___y_3135_;
v___y_3128_ = v___y_3136_;
goto v___jp_3126_;
}
else
{
lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3146_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_3147_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2971_, v___x_3146_, v___y_3135_, v___y_3136_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_dec_ref_known(v___x_3147_, 1);
v___y_3127_ = v___y_3135_;
v___y_3128_ = v___y_3136_;
goto v___jp_3126_;
}
else
{
lean_del_object(v___x_3083_);
lean_dec(v_snd_3081_);
lean_dec(v_fst_3080_);
lean_dec(v_fst_3076_);
lean_dec(v_decl_2968_);
return v___x_3147_;
}
}
}
}
else
{
lean_object* v___x_3148_; lean_object* v_env_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; uint8_t v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
lean_dec(v_cls_2971_);
v___x_3148_ = lean_st_ref_get(v___y_3136_);
v_env_3149_ = lean_ctor_get(v___x_3148_, 0);
lean_inc_ref(v_env_3149_);
lean_dec(v___x_3148_);
v___x_3150_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_3151_ = lean_box(1);
v___x_3152_ = 0;
v___x_3153_ = lean_box(v___x_2972_);
lean_inc(v_fst_3076_);
v___x_3154_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3153_, v___x_3150_, v_env_3149_, v_fst_3076_, v___x_3151_, v___x_3152_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v___x_3155_; lean_object* v_env_3156_; lean_object* v_nextMacroScope_3157_; lean_object* v_ngen_3158_; lean_object* v_auxDeclNGen_3159_; lean_object* v_traceState_3160_; lean_object* v_recordedDeps_3161_; lean_object* v_messages_3162_; lean_object* v_infoState_3163_; lean_object* v_snapshotTasks_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3173_; 
v___x_3155_ = lean_st_ref_take(v___y_3136_);
v_env_3156_ = lean_ctor_get(v___x_3155_, 0);
v_nextMacroScope_3157_ = lean_ctor_get(v___x_3155_, 1);
v_ngen_3158_ = lean_ctor_get(v___x_3155_, 2);
v_auxDeclNGen_3159_ = lean_ctor_get(v___x_3155_, 3);
v_traceState_3160_ = lean_ctor_get(v___x_3155_, 4);
v_recordedDeps_3161_ = lean_ctor_get(v___x_3155_, 6);
v_messages_3162_ = lean_ctor_get(v___x_3155_, 7);
v_infoState_3163_ = lean_ctor_get(v___x_3155_, 8);
v_snapshotTasks_3164_ = lean_ctor_get(v___x_3155_, 9);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3155_);
if (v_isSharedCheck_3173_ == 0)
{
lean_object* v_unused_3174_; 
v_unused_3174_ = lean_ctor_get(v___x_3155_, 5);
lean_dec(v_unused_3174_);
v___x_3166_ = v___x_3155_;
v_isShared_3167_ = v_isSharedCheck_3173_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_snapshotTasks_3164_);
lean_inc(v_infoState_3163_);
lean_inc(v_messages_3162_);
lean_inc(v_recordedDeps_3161_);
lean_inc(v_traceState_3160_);
lean_inc(v_auxDeclNGen_3159_);
lean_inc(v_ngen_3158_);
lean_inc(v_nextMacroScope_3157_);
lean_inc(v_env_3156_);
lean_dec(v___x_3155_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3173_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3168_; lean_object* v___x_3170_; 
lean_inc(v_snd_3081_);
lean_inc(v_fst_3076_);
v___x_3168_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3150_, v_env_3156_, v_fst_3076_, v_snd_3081_, v___x_3138_);
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 5, v___x_2973_);
lean_ctor_set(v___x_3166_, 0, v___x_3168_);
v___x_3170_ = v___x_3166_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3168_);
lean_ctor_set(v_reuseFailAlloc_3172_, 1, v_nextMacroScope_3157_);
lean_ctor_set(v_reuseFailAlloc_3172_, 2, v_ngen_3158_);
lean_ctor_set(v_reuseFailAlloc_3172_, 3, v_auxDeclNGen_3159_);
lean_ctor_set(v_reuseFailAlloc_3172_, 4, v_traceState_3160_);
lean_ctor_set(v_reuseFailAlloc_3172_, 5, v___x_2973_);
lean_ctor_set(v_reuseFailAlloc_3172_, 6, v_recordedDeps_3161_);
lean_ctor_set(v_reuseFailAlloc_3172_, 7, v_messages_3162_);
lean_ctor_set(v_reuseFailAlloc_3172_, 8, v_infoState_3163_);
lean_ctor_set(v_reuseFailAlloc_3172_, 9, v_snapshotTasks_3164_);
v___x_3170_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
lean_object* v___x_3171_; 
v___x_3171_ = lean_st_ref_put(v___y_3136_, v___x_3170_);
v_exportedInfo_x3f_3115_ = v_exportedInfo_x3f_2976_;
v___y_3116_ = v___y_3135_;
v___y_3117_ = v___y_3136_;
goto v___jp_3114_;
}
}
}
else
{
lean_dec_ref_known(v___x_3154_, 1);
lean_dec_ref(v___x_2973_);
v_exportedInfo_x3f_3115_ = v_exportedInfo_x3f_2976_;
v___y_3116_ = v___y_3135_;
v___y_3117_ = v___y_3136_;
goto v___jp_3114_;
}
}
}
else
{
lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v_a_3177_; uint8_t v___x_3178_; 
lean_dec(v_exportedInfo_x3f_2976_);
lean_dec_ref(v___x_2973_);
v___x_3175_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3176_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3175_, v___y_3135_);
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
lean_inc(v_a_3177_);
lean_dec_ref(v___x_3176_);
v___x_3178_ = lean_unbox(v_a_3177_);
lean_dec(v_a_3177_);
if (v___x_3178_ == 0)
{
lean_object* v_toCold_3179_; lean_object* v_options_3180_; uint8_t v_hasTrace_3181_; 
v_toCold_3179_ = lean_ctor_get(v___y_3135_, 0);
v_options_3180_ = lean_ctor_get(v_toCold_3179_, 2);
v_hasTrace_3181_ = lean_ctor_get_uint8(v_options_3180_, sizeof(void*)*1);
if (v_hasTrace_3181_ == 0)
{
lean_dec(v_cls_2971_);
v_exportedInfo_x3f_3115_ = v___x_2974_;
v___y_3116_ = v___y_3135_;
v___y_3117_ = v___y_3136_;
goto v___jp_3114_;
}
else
{
lean_object* v_inheritedTraceOptions_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; uint8_t v___x_3185_; 
v_inheritedTraceOptions_3182_ = lean_ctor_get(v_toCold_3179_, 11);
v___x_3183_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2971_);
v___x_3184_ = l_Lean_Name_append(v___x_3183_, v_cls_2971_);
v___x_3185_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3182_, v_options_3180_, v___x_3184_);
lean_dec(v___x_3184_);
if (v___x_3185_ == 0)
{
lean_dec(v_cls_2971_);
v_exportedInfo_x3f_3115_ = v___x_2974_;
v___y_3116_ = v___y_3135_;
v___y_3117_ = v___y_3136_;
goto v___jp_3114_;
}
else
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_3187_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2971_, v___x_3186_, v___y_3135_, v___y_3136_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_dec_ref_known(v___x_3187_, 1);
v_exportedInfo_x3f_3115_ = v___x_2974_;
v___y_3116_ = v___y_3135_;
v___y_3117_ = v___y_3136_;
goto v___jp_3114_;
}
else
{
lean_del_object(v___x_3083_);
lean_dec(v_snd_3081_);
lean_dec(v_fst_3080_);
lean_dec(v_fst_3076_);
lean_dec(v___x_2974_);
lean_dec(v_decl_2968_);
return v___x_3187_;
}
}
}
}
else
{
lean_object* v_toCold_3188_; lean_object* v_options_3189_; uint8_t v_hasTrace_3190_; 
lean_dec(v___x_2974_);
v_toCold_3188_ = lean_ctor_get(v___y_3135_, 0);
v_options_3189_ = lean_ctor_get(v_toCold_3188_, 2);
v_hasTrace_3190_ = lean_ctor_get_uint8(v_options_3189_, sizeof(void*)*1);
if (v_hasTrace_3190_ == 0)
{
lean_dec(v_cls_2971_);
v___y_3131_ = v___y_3135_;
v___y_3132_ = v___y_3136_;
goto v___jp_3130_;
}
else
{
lean_object* v_inheritedTraceOptions_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; uint8_t v___x_3194_; 
v_inheritedTraceOptions_3191_ = lean_ctor_get(v_toCold_3188_, 11);
v___x_3192_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2971_);
v___x_3193_ = l_Lean_Name_append(v___x_3192_, v_cls_2971_);
v___x_3194_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3191_, v_options_3189_, v___x_3193_);
lean_dec(v___x_3193_);
if (v___x_3194_ == 0)
{
lean_dec(v_cls_2971_);
v___y_3131_ = v___y_3135_;
v___y_3132_ = v___y_3136_;
goto v___jp_3130_;
}
else
{
lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3195_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_3196_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2971_, v___x_3195_, v___y_3135_, v___y_3136_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_dec_ref_known(v___x_3196_, 1);
v___y_3131_ = v___y_3135_;
v___y_3132_ = v___y_3136_;
goto v___jp_3130_;
}
else
{
lean_del_object(v___x_3083_);
lean_dec(v_snd_3081_);
lean_dec(v_fst_3080_);
lean_dec(v_fst_3076_);
lean_dec(v_decl_2968_);
return v___x_3196_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed(lean_object* v_decl_3209_, lean_object* v_hasTrace_3210_, lean_object* v___x_3211_, lean_object* v_cls_3212_, lean_object* v___x_3213_, lean_object* v___x_3214_, lean_object* v___x_3215_, lean_object* v_____x_3216_, lean_object* v_exportedInfo_x3f_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
uint8_t v_hasTrace_boxed_3221_; uint8_t v___x_54787__boxed_3222_; uint8_t v___x_54789__boxed_3223_; lean_object* v_res_3224_; 
v_hasTrace_boxed_3221_ = lean_unbox(v_hasTrace_3210_);
v___x_54787__boxed_3222_ = lean_unbox(v___x_3211_);
v___x_54789__boxed_3223_ = lean_unbox(v___x_3213_);
v_res_3224_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_decl_3209_, v_hasTrace_boxed_3221_, v___x_54787__boxed_3222_, v_cls_3212_, v___x_54789__boxed_3223_, v___x_3214_, v___x_3215_, v_____x_3216_, v_exportedInfo_x3f_3217_, v___y_3218_, v___y_3219_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
return v_res_3224_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1(void){
_start:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3226_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__0));
v___x_3227_ = l_Lean_stringToMessageData(v___x_3226_);
return v___x_3227_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3(void){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3229_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__2));
v___x_3230_ = l_Lean_stringToMessageData(v___x_3229_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(lean_object* v___f_3231_, uint8_t v___x_3232_, uint8_t v_forceExpose_3233_, lean_object* v___x_3234_, lean_object* v_cls_3235_, lean_object* v_defn_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
lean_object* v_exportedInfo_x3f_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; uint8_t v___y_3256_; uint8_t v___y_3261_; lean_object* v___x_3266_; lean_object* v_env_3267_; lean_object* v___x_3268_; 
v___x_3266_ = lean_st_ref_get(v___y_3238_);
v_env_3267_ = lean_ctor_get(v___x_3266_, 0);
lean_inc_ref(v_env_3267_);
lean_dec(v___x_3266_);
v___x_3268_ = lean_st_ref_get(v___y_3238_);
if (v_forceExpose_3233_ == 0)
{
lean_object* v_env_3269_; lean_object* v___x_3270_; uint8_t v_isModule_3271_; 
v_env_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc_ref(v_env_3269_);
lean_dec(v___x_3268_);
v___x_3270_ = l_Lean_Environment_header(v_env_3267_);
lean_dec_ref(v_env_3267_);
v_isModule_3271_ = lean_ctor_get_uint8(v___x_3270_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_3270_);
if (v_isModule_3271_ == 0)
{
lean_dec_ref(v_env_3269_);
lean_dec(v_cls_3235_);
v_exportedInfo_x3f_3241_ = v___x_3234_;
v___y_3242_ = v___y_3237_;
v___y_3243_ = v___y_3238_;
goto v___jp_3240_;
}
else
{
uint8_t v_isExporting_3272_; 
v_isExporting_3272_ = lean_ctor_get_uint8(v_env_3269_, sizeof(void*)*13);
lean_dec_ref(v_env_3269_);
if (v_isExporting_3272_ == 0)
{
lean_object* v_toCold_3273_; lean_object* v_options_3274_; uint8_t v_hasTrace_3275_; 
lean_dec(v___x_3234_);
v_toCold_3273_ = lean_ctor_get(v___y_3237_, 0);
v_options_3274_ = lean_ctor_get(v_toCold_3273_, 2);
v_hasTrace_3275_ = lean_ctor_get_uint8(v_options_3274_, sizeof(void*)*1);
if (v_hasTrace_3275_ == 0)
{
lean_dec(v_cls_3235_);
v___y_3261_ = v_isModule_3271_;
goto v___jp_3260_;
}
else
{
lean_object* v_inheritedTraceOptions_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; uint8_t v___x_3279_; 
v_inheritedTraceOptions_3276_ = lean_ctor_get(v_toCold_3273_, 11);
v___x_3277_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3235_);
v___x_3278_ = l_Lean_Name_append(v___x_3277_, v_cls_3235_);
v___x_3279_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3276_, v_options_3274_, v___x_3278_);
lean_dec(v___x_3278_);
if (v___x_3279_ == 0)
{
lean_dec(v_cls_3235_);
v___y_3261_ = v_isModule_3271_;
goto v___jp_3260_;
}
else
{
lean_object* v_toConstantVal_3280_; lean_object* v_name_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v_toConstantVal_3280_ = lean_ctor_get(v_defn_3236_, 0);
v_name_3281_ = lean_ctor_get(v_toConstantVal_3280_, 0);
v___x_3282_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_3281_);
v___x_3283_ = l_Lean_MessageData_ofName(v_name_3281_);
v___x_3284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3282_);
lean_ctor_set(v___x_3284_, 1, v___x_3283_);
v___x_3285_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_3286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3284_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
v___x_3287_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3235_, v___x_3286_, v___y_3237_, v___y_3238_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_dec_ref_known(v___x_3287_, 1);
v___y_3261_ = v_isModule_3271_;
goto v___jp_3260_;
}
else
{
lean_dec_ref(v_defn_3236_);
lean_dec_ref(v___f_3231_);
return v___x_3287_;
}
}
}
}
else
{
lean_dec(v_cls_3235_);
v_exportedInfo_x3f_3241_ = v___x_3234_;
v___y_3242_ = v___y_3237_;
v___y_3243_ = v___y_3238_;
goto v___jp_3240_;
}
}
}
else
{
lean_dec(v___x_3268_);
lean_dec_ref(v_env_3267_);
lean_dec(v_cls_3235_);
v_exportedInfo_x3f_3241_ = v___x_3234_;
v___y_3242_ = v___y_3237_;
v___y_3243_ = v___y_3238_;
goto v___jp_3240_;
}
v___jp_3240_:
{
lean_object* v_toConstantVal_3244_; lean_object* v_name_3245_; lean_object* v___x_3246_; uint8_t v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v_toConstantVal_3244_ = lean_ctor_get(v_defn_3236_, 0);
v_name_3245_ = lean_ctor_get(v_toConstantVal_3244_, 0);
lean_inc(v_name_3245_);
v___x_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3246_, 0, v_defn_3236_);
v___x_3247_ = 0;
v___x_3248_ = lean_box(v___x_3247_);
v___x_3249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3246_);
lean_ctor_set(v___x_3249_, 1, v___x_3248_);
v___x_3250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3250_, 0, v_name_3245_);
lean_ctor_set(v___x_3250_, 1, v___x_3249_);
lean_inc(v___y_3243_);
lean_inc_ref(v___y_3242_);
v___x_3251_ = lean_apply_5(v___f_3231_, v___x_3250_, v_exportedInfo_x3f_3241_, v___y_3242_, v___y_3243_, lean_box(0));
return v___x_3251_;
}
v___jp_3252_:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3257_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3257_, 0, v___y_3253_);
lean_ctor_set_uint8(v___x_3257_, sizeof(void*)*1, v___y_3256_);
v___x_3258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3257_);
v___x_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3258_);
v_exportedInfo_x3f_3241_ = v___x_3259_;
v___y_3242_ = v___y_3254_;
v___y_3243_ = v___y_3255_;
goto v___jp_3240_;
}
v___jp_3260_:
{
lean_object* v_toConstantVal_3262_; uint8_t v_safety_3263_; uint8_t v___x_3264_; uint8_t v___x_3265_; 
v_toConstantVal_3262_ = lean_ctor_get(v_defn_3236_, 0);
v_safety_3263_ = lean_ctor_get_uint8(v_defn_3236_, sizeof(void*)*4);
v___x_3264_ = 1;
v___x_3265_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3263_, v___x_3264_);
if (v___x_3265_ == 0)
{
lean_inc_ref(v_toConstantVal_3262_);
v___y_3253_ = v_toConstantVal_3262_;
v___y_3254_ = v___y_3237_;
v___y_3255_ = v___y_3238_;
v___y_3256_ = v___y_3261_;
goto v___jp_3252_;
}
else
{
lean_inc_ref(v_toConstantVal_3262_);
v___y_3253_ = v_toConstantVal_3262_;
v___y_3254_ = v___y_3237_;
v___y_3255_ = v___y_3238_;
v___y_3256_ = v___x_3232_;
goto v___jp_3252_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed(lean_object* v___f_3288_, lean_object* v___x_3289_, lean_object* v_forceExpose_3290_, lean_object* v___x_3291_, lean_object* v_cls_3292_, lean_object* v_defn_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
uint8_t v___x_55260__boxed_3297_; uint8_t v_forceExpose_boxed_3298_; lean_object* v_res_3299_; 
v___x_55260__boxed_3297_ = lean_unbox(v___x_3289_);
v_forceExpose_boxed_3298_ = lean_unbox(v_forceExpose_3290_);
v_res_3299_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v___f_3288_, v___x_55260__boxed_3297_, v_forceExpose_boxed_3298_, v___x_3291_, v_cls_3292_, v_defn_3293_, v___y_3294_, v___y_3295_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(lean_object* v_val_3300_, lean_object* v___f_3301_, lean_object* v_____r_3302_, lean_object* v_exportedInfo_x3f_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_){
_start:
{
lean_object* v_toConstantVal_3307_; lean_object* v_name_3308_; lean_object* v___x_3309_; uint8_t v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v_toConstantVal_3307_ = lean_ctor_get(v_val_3300_, 0);
v_name_3308_ = lean_ctor_get(v_toConstantVal_3307_, 0);
lean_inc(v_name_3308_);
v___x_3309_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3309_, 0, v_val_3300_);
v___x_3310_ = 1;
v___x_3311_ = lean_box(v___x_3310_);
v___x_3312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3309_);
lean_ctor_set(v___x_3312_, 1, v___x_3311_);
v___x_3313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3313_, 0, v_name_3308_);
lean_ctor_set(v___x_3313_, 1, v___x_3312_);
lean_inc(v___y_3305_);
lean_inc_ref(v___y_3304_);
v___x_3314_ = lean_apply_5(v___f_3301_, v___x_3313_, v_exportedInfo_x3f_3303_, v___y_3304_, v___y_3305_, lean_box(0));
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed(lean_object* v_val_3315_, lean_object* v___f_3316_, lean_object* v_____r_3317_, lean_object* v_exportedInfo_x3f_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(v_val_3315_, v___f_3316_, v_____r_3317_, v_exportedInfo_x3f_3318_, v___y_3319_, v___y_3320_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(lean_object* v_val_3323_, uint8_t v___x_3324_, lean_object* v___f_3325_, lean_object* v_____r_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
lean_object* v_toConstantVal_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v_toConstantVal_3330_ = lean_ctor_get(v_val_3323_, 0);
lean_inc_ref(v_toConstantVal_3330_);
v___x_3331_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3331_, 0, v_toConstantVal_3330_);
lean_ctor_set_uint8(v___x_3331_, sizeof(void*)*1, v___x_3324_);
v___x_3332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3331_);
v___x_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3332_);
v___x_3334_ = lean_box(0);
lean_inc(v___y_3328_);
lean_inc_ref(v___y_3327_);
v___x_3335_ = lean_apply_5(v___f_3325_, v___x_3334_, v___x_3333_, v___y_3327_, v___y_3328_, lean_box(0));
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed(lean_object* v_val_3336_, lean_object* v___x_3337_, lean_object* v___f_3338_, lean_object* v_____r_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
uint8_t v___x_55385__boxed_3343_; lean_object* v_res_3344_; 
v___x_55385__boxed_3343_ = lean_unbox(v___x_3337_);
v_res_3344_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(v_val_3336_, v___x_55385__boxed_3343_, v___f_3338_, v_____r_3339_, v___y_3340_, v___y_3341_);
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
lean_dec_ref(v_val_3336_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(lean_object* v_val_3345_, lean_object* v___f_3346_, lean_object* v_____r_3347_, lean_object* v_exportedInfo_x3f_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
lean_object* v_toConstantVal_3352_; lean_object* v_name_3353_; lean_object* v___x_3354_; uint8_t v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v_toConstantVal_3352_ = lean_ctor_get(v_val_3345_, 0);
v_name_3353_ = lean_ctor_get(v_toConstantVal_3352_, 0);
lean_inc(v_name_3353_);
v___x_3354_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3354_, 0, v_val_3345_);
v___x_3355_ = 3;
v___x_3356_ = lean_box(v___x_3355_);
v___x_3357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3354_);
lean_ctor_set(v___x_3357_, 1, v___x_3356_);
v___x_3358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3358_, 0, v_name_3353_);
lean_ctor_set(v___x_3358_, 1, v___x_3357_);
lean_inc(v___y_3350_);
lean_inc_ref(v___y_3349_);
v___x_3359_ = lean_apply_5(v___f_3346_, v___x_3358_, v_exportedInfo_x3f_3348_, v___y_3349_, v___y_3350_, lean_box(0));
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed(lean_object* v_val_3360_, lean_object* v___f_3361_, lean_object* v_____r_3362_, lean_object* v_exportedInfo_x3f_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(v_val_3360_, v___f_3361_, v_____r_3362_, v_exportedInfo_x3f_3363_, v___y_3364_, v___y_3365_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(lean_object* v_val_3368_, lean_object* v___f_3369_, lean_object* v_____r_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
lean_object* v_toConstantVal_3374_; uint8_t v_isUnsafe_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
v_toConstantVal_3374_ = lean_ctor_get(v_val_3368_, 0);
v_isUnsafe_3375_ = lean_ctor_get_uint8(v_val_3368_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_3374_);
v___x_3376_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3376_, 0, v_toConstantVal_3374_);
lean_ctor_set_uint8(v___x_3376_, sizeof(void*)*1, v_isUnsafe_3375_);
v___x_3377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3376_);
v___x_3378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3377_);
v___x_3379_ = lean_box(0);
lean_inc(v___y_3372_);
lean_inc_ref(v___y_3371_);
v___x_3380_ = lean_apply_5(v___f_3369_, v___x_3379_, v___x_3378_, v___y_3371_, v___y_3372_, lean_box(0));
return v___x_3380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10___boxed(lean_object* v_val_3381_, lean_object* v___f_3382_, lean_object* v_____r_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_3381_, v___f_3382_, v_____r_3383_, v___y_3384_, v___y_3385_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec_ref(v_val_3381_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(lean_object* v_decl_3388_, uint8_t v___x_3389_, lean_object* v_cls_3390_, uint8_t v___x_3391_, lean_object* v___x_3392_, lean_object* v___x_3393_, lean_object* v_____x_3394_, lean_object* v_exportedInfo_x3f_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v_a_3402_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; uint8_t v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v_snd_3495_; lean_object* v_fst_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3629_; 
v_snd_3495_ = lean_ctor_get(v_____x_3394_, 1);
v_fst_3496_ = lean_ctor_get(v_____x_3394_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v_____x_3394_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3498_ = v_____x_3394_;
v_isShared_3499_ = v_isSharedCheck_3629_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_snd_3495_);
lean_inc(v_fst_3496_);
lean_dec(v_____x_3394_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3629_;
goto v_resetjp_3497_;
}
v___jp_3399_:
{
lean_object* v___x_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
v___x_3403_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3401_, v___y_3400_);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3410_ == 0)
{
lean_object* v_unused_3411_; 
v_unused_3411_ = lean_ctor_get(v___x_3403_, 0);
lean_dec(v_unused_3411_);
v___x_3405_ = v___x_3403_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_dec(v___x_3403_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
lean_ctor_set_tag(v___x_3405_, 1);
lean_ctor_set(v___x_3405_, 0, v_a_3402_);
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3402_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
v___jp_3412_:
{
lean_object* v___x_3425_; 
lean_inc_ref(v___y_3418_);
v___x_3425_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3419_, v___y_3418_, v___y_3414_, v___y_3424_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v___x_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3481_; 
lean_dec_ref_known(v___x_3425_, 1);
lean_dec(v___y_3416_);
lean_inc_ref(v___y_3420_);
v___x_3426_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3420_, v___y_3421_);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3481_ == 0)
{
lean_object* v_unused_3482_; 
v_unused_3482_ = lean_ctor_get(v___x_3426_, 0);
lean_dec(v_unused_3482_);
v___x_3428_ = v___x_3426_;
v_isShared_3429_ = v_isSharedCheck_3481_;
goto v_resetjp_3427_;
}
else
{
lean_dec(v___x_3426_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3481_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; uint8_t v___x_3432_; 
v___x_3430_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3423_);
v___x_3431_ = l_Lean_Elab_async;
v___x_3432_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_3430_, v___x_3431_);
lean_dec_ref(v___x_3430_);
if (v___x_3432_ == 0)
{
lean_object* v___x_3433_; lean_object* v_r_3434_; 
lean_del_object(v___x_3428_);
lean_dec_ref(v___y_3422_);
lean_dec_ref(v___y_3413_);
v___x_3433_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3418_, v___y_3421_);
lean_dec_ref(v___x_3433_);
v_r_3434_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3388_, v___y_3423_, v___y_3421_);
if (lean_obj_tag(v_r_3434_) == 0)
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3453_; 
v_a_3435_ = lean_ctor_get(v_r_3434_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v_r_3434_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3437_ = v_r_3434_;
v_isShared_3438_ = v_isSharedCheck_3453_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v_r_3434_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3453_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
lean_inc(v_a_3435_);
if (v_isShared_3438_ == 0)
{
lean_ctor_set_tag(v___x_3437_, 1);
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3435_);
v___x_3440_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
lean_object* v___x_3441_; 
v___x_3441_ = lean_apply_2(v___y_3415_, v___x_3440_, lean_box(0));
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v___x_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3449_; 
lean_dec_ref_known(v___x_3441_, 1);
v___x_3442_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3420_, v___y_3421_);
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
lean_ctor_set(v___x_3444_, 0, v_a_3435_);
v___x_3447_ = v___x_3444_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_a_3435_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
else
{
lean_object* v_a_3451_; 
lean_dec(v_a_3435_);
v_a_3451_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_a_3451_);
lean_dec_ref_known(v___x_3441_, 1);
v___y_3400_ = v___y_3421_;
v___y_3401_ = v___y_3420_;
v_a_3402_ = v_a_3451_;
goto v___jp_3399_;
}
}
}
}
else
{
lean_object* v_a_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v_a_3454_ = lean_ctor_get(v_r_3434_, 0);
lean_inc(v_a_3454_);
lean_dec_ref_known(v_r_3434_, 1);
v___x_3455_ = lean_box(0);
v___x_3456_ = lean_apply_2(v___y_3415_, v___x_3455_, lean_box(0));
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_dec_ref_known(v___x_3456_, 1);
v___y_3400_ = v___y_3421_;
v___y_3401_ = v___y_3420_;
v_a_3402_ = v_a_3454_;
goto v___jp_3399_;
}
else
{
lean_object* v_a_3457_; 
lean_dec(v_a_3454_);
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
lean_inc(v_a_3457_);
lean_dec_ref_known(v___x_3456_, 1);
v___y_3400_ = v___y_3421_;
v___y_3401_ = v___y_3420_;
v_a_3402_ = v_a_3457_;
goto v___jp_3399_;
}
}
}
else
{
lean_object* v___x_3458_; lean_object* v___x_3460_; 
lean_dec_ref(v___y_3420_);
lean_dec_ref(v___y_3418_);
lean_dec_ref(v___y_3415_);
lean_dec(v_decl_3388_);
v___x_3458_ = l_IO_CancelToken_new();
if (v_isShared_3429_ == 0)
{
lean_ctor_set_tag(v___x_3428_, 1);
lean_ctor_set(v___x_3428_, 0, v___x_3458_);
v___x_3460_ = v___x_3428_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v___x_3458_);
v___x_3460_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; 
v___x_3461_ = lean_unsigned_to_nat(0u);
v___x_3462_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_3463_ = l_Lean_Name_toString(v___x_3462_, v___x_3389_);
lean_inc_ref(v___x_3460_);
v___x_3464_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3413_, v___x_3460_, v___x_3463_, v___y_3423_, v___y_3421_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v_checked_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
lean_inc(v_a_3465_);
lean_dec_ref_known(v___x_3464_, 1);
v_checked_3466_ = lean_ctor_get(v___y_3422_, 2);
lean_inc_ref(v_checked_3466_);
lean_dec_ref(v___y_3422_);
v___x_3467_ = lean_io_map_task(v_a_3465_, v_checked_3466_, v___x_3461_, v___y_3417_);
v___x_3468_ = lean_box(0);
v___x_3469_ = lean_box(2);
v___x_3470_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3468_);
lean_ctor_set(v___x_3470_, 1, v___x_3469_);
lean_ctor_set(v___x_3470_, 2, v___x_3460_);
lean_ctor_set(v___x_3470_, 3, v___x_3467_);
v___x_3471_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3470_, v___y_3421_);
return v___x_3471_;
}
else
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3479_; 
lean_dec_ref(v___x_3460_);
lean_dec_ref(v___y_3422_);
v_a_3472_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3474_ = v___x_3464_;
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3464_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3477_; 
if (v_isShared_3475_ == 0)
{
v___x_3477_ = v___x_3474_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_a_3472_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3494_; 
lean_dec_ref(v___y_3422_);
lean_dec_ref(v___y_3420_);
lean_dec_ref(v___y_3418_);
lean_dec_ref(v___y_3415_);
lean_dec_ref(v___y_3413_);
lean_dec(v_decl_3388_);
v_a_3483_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3485_ = v___x_3425_;
v_isShared_3486_ = v_isSharedCheck_3494_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3425_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3494_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3492_; 
v___x_3487_ = lean_io_error_to_string(v_a_3483_);
v___x_3488_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
v___x_3489_ = l_Lean_MessageData_ofFormat(v___x_3488_);
v___x_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3490_, 0, v___y_3416_);
lean_ctor_set(v___x_3490_, 1, v___x_3489_);
if (v_isShared_3486_ == 0)
{
lean_ctor_set(v___x_3485_, 0, v___x_3490_);
v___x_3492_ = v___x_3485_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v___x_3490_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
v_resetjp_3497_:
{
lean_object* v_fst_3500_; lean_object* v_snd_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3628_; 
v_fst_3500_ = lean_ctor_get(v_snd_3495_, 0);
v_snd_3501_ = lean_ctor_get(v_snd_3495_, 1);
v_isSharedCheck_3628_ = !lean_is_exclusive(v_snd_3495_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3503_ = v_snd_3495_;
v_isShared_3504_ = v_isSharedCheck_3628_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_snd_3501_);
lean_inc(v_fst_3500_);
lean_dec(v_snd_3495_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3628_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v_exportedInfo_x3f_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___x_3618_; lean_object* v_env_3619_; uint8_t v___x_3620_; 
v___x_3618_ = lean_st_ref_get(v___y_3397_);
v_env_3619_ = lean_ctor_get(v___x_3618_, 0);
lean_inc_ref(v_env_3619_);
lean_dec(v___x_3618_);
v___x_3620_ = l_Lean_Environment_containsOnBranch(v_env_3619_, v_fst_3496_);
lean_dec_ref(v_env_3619_);
if (v___x_3620_ == 0)
{
lean_del_object(v___x_3498_);
v___y_3556_ = v___y_3396_;
v___y_3557_ = v___y_3397_;
goto v___jp_3555_;
}
else
{
lean_object* v___x_3621_; lean_object* v_env_3622_; lean_object* v___x_3623_; lean_object* v___x_3625_; 
lean_del_object(v___x_3503_);
lean_dec(v_snd_3501_);
lean_dec(v_fst_3500_);
lean_dec(v_exportedInfo_x3f_3395_);
lean_dec(v___x_3393_);
lean_dec_ref(v___x_3392_);
lean_dec(v_cls_3390_);
lean_dec(v_decl_3388_);
v___x_3621_ = lean_st_ref_get(v___y_3397_);
v_env_3622_ = lean_ctor_get(v___x_3621_, 0);
lean_inc_ref(v_env_3622_);
lean_dec(v___x_3621_);
v___x_3623_ = lean_elab_environment_to_kernel_env(v_env_3622_);
if (v_isShared_3499_ == 0)
{
lean_ctor_set_tag(v___x_3498_, 1);
lean_ctor_set(v___x_3498_, 1, v_fst_3496_);
lean_ctor_set(v___x_3498_, 0, v___x_3623_);
v___x_3625_ = v___x_3498_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3623_);
lean_ctor_set(v_reuseFailAlloc_3627_, 1, v_fst_3496_);
v___x_3625_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
lean_object* v___x_3626_; 
v___x_3626_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3625_, v___y_3396_, v___y_3397_);
return v___x_3626_;
}
}
v___jp_3505_:
{
lean_object* v_ref_3511_; uint8_t v___x_3512_; uint8_t v___x_3513_; lean_object* v___x_3514_; 
v_ref_3511_ = lean_ctor_get(v___y_3507_, 2);
v___x_3512_ = 0;
v___x_3513_ = lean_unbox(v_snd_3501_);
lean_dec(v_snd_3501_);
lean_inc_ref(v___y_3509_);
v___x_3514_ = l_Lean_Environment_addConstAsync(v___y_3509_, v_fst_3496_, v___x_3513_, v___y_3510_, v___x_3512_, v___x_3389_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v_a_3515_; lean_object* v_mainEnv_3516_; lean_object* v_asyncEnv_3517_; lean_object* v___f_3518_; lean_object* v___f_3519_; lean_object* v___x_3520_; 
lean_del_object(v___x_3503_);
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc_n(v_a_3515_, 3);
lean_dec_ref_known(v___x_3514_, 1);
v_mainEnv_3516_ = lean_ctor_get(v_a_3515_, 0);
lean_inc_ref(v_mainEnv_3516_);
v_asyncEnv_3517_ = lean_ctor_get(v_a_3515_, 1);
lean_inc_ref_n(v_asyncEnv_3517_, 2);
lean_inc(v_ref_3511_);
lean_inc(v___y_3508_);
v___f_3518_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3518_, 0, v___y_3508_);
lean_closure_set(v___f_3518_, 1, v_a_3515_);
lean_closure_set(v___f_3518_, 2, v_ref_3511_);
lean_inc(v_decl_3388_);
v___f_3519_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3519_, 0, v_a_3515_);
lean_closure_set(v___f_3519_, 1, v_asyncEnv_3517_);
lean_closure_set(v___f_3519_, 2, v_decl_3388_);
v___x_3520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3520_, 0, v_fst_3500_);
if (lean_obj_tag(v___y_3506_) == 0)
{
lean_inc(v_ref_3511_);
lean_inc_ref(v___x_3520_);
v___y_3413_ = v___f_3519_;
v___y_3414_ = v___x_3520_;
v___y_3415_ = v___f_3518_;
v___y_3416_ = v_ref_3511_;
v___y_3417_ = v___x_3512_;
v___y_3418_ = v_asyncEnv_3517_;
v___y_3419_ = v_a_3515_;
v___y_3420_ = v_mainEnv_3516_;
v___y_3421_ = v___y_3508_;
v___y_3422_ = v___y_3509_;
v___y_3423_ = v___y_3507_;
v___y_3424_ = v___x_3520_;
goto v___jp_3412_;
}
else
{
lean_inc(v_ref_3511_);
v___y_3413_ = v___f_3519_;
v___y_3414_ = v___x_3520_;
v___y_3415_ = v___f_3518_;
v___y_3416_ = v_ref_3511_;
v___y_3417_ = v___x_3512_;
v___y_3418_ = v_asyncEnv_3517_;
v___y_3419_ = v_a_3515_;
v___y_3420_ = v_mainEnv_3516_;
v___y_3421_ = v___y_3508_;
v___y_3422_ = v___y_3509_;
v___y_3423_ = v___y_3507_;
v___y_3424_ = v___y_3506_;
goto v___jp_3412_;
}
}
else
{
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3534_; 
lean_dec_ref(v___y_3509_);
lean_dec(v___y_3506_);
lean_dec(v_fst_3500_);
lean_dec(v_decl_3388_);
v_a_3521_ = lean_ctor_get(v___x_3514_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3523_ = v___x_3514_;
v_isShared_3524_ = v_isSharedCheck_3534_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v___x_3514_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3534_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3529_; 
v___x_3525_ = lean_io_error_to_string(v_a_3521_);
v___x_3526_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3525_);
v___x_3527_ = l_Lean_MessageData_ofFormat(v___x_3526_);
lean_inc(v_ref_3511_);
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 1, v___x_3527_);
lean_ctor_set(v___x_3503_, 0, v_ref_3511_);
v___x_3529_ = v___x_3503_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_ref_3511_);
lean_ctor_set(v_reuseFailAlloc_3533_, 1, v___x_3527_);
v___x_3529_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
lean_object* v___x_3531_; 
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 0, v___x_3529_);
v___x_3531_ = v___x_3523_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3529_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
}
v___jp_3535_:
{
lean_object* v___x_3539_; 
v___x_3539_ = lean_st_ref_get(v___y_3538_);
if (lean_obj_tag(v_exportedInfo_x3f_3536_) == 0)
{
lean_object* v_env_3540_; lean_object* v___x_3541_; 
v_env_3540_ = lean_ctor_get(v___x_3539_, 0);
lean_inc_ref(v_env_3540_);
lean_dec(v___x_3539_);
v___x_3541_ = lean_box(0);
v___y_3506_ = v_exportedInfo_x3f_3536_;
v___y_3507_ = v___y_3537_;
v___y_3508_ = v___y_3538_;
v___y_3509_ = v_env_3540_;
v___y_3510_ = v___x_3541_;
goto v___jp_3505_;
}
else
{
lean_object* v_env_3542_; lean_object* v_val_3543_; uint8_t v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
v_env_3542_ = lean_ctor_get(v___x_3539_, 0);
lean_inc_ref(v_env_3542_);
lean_dec(v___x_3539_);
v_val_3543_ = lean_ctor_get(v_exportedInfo_x3f_3536_, 0);
v___x_3544_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3543_);
v___x_3545_ = lean_box(v___x_3544_);
v___x_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3545_);
v___y_3506_ = v_exportedInfo_x3f_3536_;
v___y_3507_ = v___y_3537_;
v___y_3508_ = v___y_3538_;
v___y_3509_ = v_env_3542_;
v___y_3510_ = v___x_3546_;
goto v___jp_3505_;
}
}
v___jp_3547_:
{
lean_object* v___x_3550_; 
lean_inc(v_fst_3500_);
v___x_3550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3550_, 0, v_fst_3500_);
v_exportedInfo_x3f_3536_ = v___x_3550_;
v___y_3537_ = v___y_3548_;
v___y_3538_ = v___y_3549_;
goto v___jp_3535_;
}
v___jp_3551_:
{
lean_object* v___x_3554_; 
lean_inc(v_fst_3500_);
v___x_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3554_, 0, v_fst_3500_);
v_exportedInfo_x3f_3536_ = v___x_3554_;
v___y_3537_ = v___y_3552_;
v___y_3538_ = v___y_3553_;
goto v___jp_3535_;
}
v___jp_3555_:
{
lean_object* v___x_3558_; uint8_t v___x_3559_; 
lean_inc(v_decl_3388_);
v___x_3558_ = l_Lean_Declaration_getTopLevelNames(v_decl_3388_);
v___x_3559_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3558_);
lean_dec(v___x_3558_);
if (v___x_3559_ == 0)
{
lean_dec(v___x_3393_);
if (lean_obj_tag(v_exportedInfo_x3f_3395_) == 0)
{
lean_object* v_toCold_3560_; lean_object* v_options_3561_; uint8_t v_hasTrace_3562_; 
lean_dec_ref(v___x_3392_);
v_toCold_3560_ = lean_ctor_get(v___y_3556_, 0);
v_options_3561_ = lean_ctor_get(v_toCold_3560_, 2);
v_hasTrace_3562_ = lean_ctor_get_uint8(v_options_3561_, sizeof(void*)*1);
if (v_hasTrace_3562_ == 0)
{
lean_dec(v_cls_3390_);
v___y_3548_ = v___y_3556_;
v___y_3549_ = v___y_3557_;
goto v___jp_3547_;
}
else
{
lean_object* v_inheritedTraceOptions_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; uint8_t v___x_3566_; 
v_inheritedTraceOptions_3563_ = lean_ctor_get(v_toCold_3560_, 11);
v___x_3564_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3390_);
v___x_3565_ = l_Lean_Name_append(v___x_3564_, v_cls_3390_);
v___x_3566_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3563_, v_options_3561_, v___x_3565_);
lean_dec(v___x_3565_);
if (v___x_3566_ == 0)
{
lean_dec(v_cls_3390_);
v___y_3548_ = v___y_3556_;
v___y_3549_ = v___y_3557_;
goto v___jp_3547_;
}
else
{
lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3567_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_3568_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3390_, v___x_3567_, v___y_3556_, v___y_3557_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_dec_ref_known(v___x_3568_, 1);
v___y_3548_ = v___y_3556_;
v___y_3549_ = v___y_3557_;
goto v___jp_3547_;
}
else
{
lean_del_object(v___x_3503_);
lean_dec(v_snd_3501_);
lean_dec(v_fst_3500_);
lean_dec(v_fst_3496_);
lean_dec(v_decl_3388_);
return v___x_3568_;
}
}
}
}
else
{
lean_object* v___x_3569_; lean_object* v_env_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; uint8_t v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
lean_dec(v_cls_3390_);
v___x_3569_ = lean_st_ref_get(v___y_3557_);
v_env_3570_ = lean_ctor_get(v___x_3569_, 0);
lean_inc_ref(v_env_3570_);
lean_dec(v___x_3569_);
v___x_3571_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_3572_ = lean_box(1);
v___x_3573_ = 0;
v___x_3574_ = lean_box(v___x_3391_);
lean_inc(v_fst_3496_);
v___x_3575_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3574_, v___x_3571_, v_env_3570_, v_fst_3496_, v___x_3572_, v___x_3573_);
if (lean_obj_tag(v___x_3575_) == 0)
{
lean_object* v___x_3576_; lean_object* v_env_3577_; lean_object* v_nextMacroScope_3578_; lean_object* v_ngen_3579_; lean_object* v_auxDeclNGen_3580_; lean_object* v_traceState_3581_; lean_object* v_recordedDeps_3582_; lean_object* v_messages_3583_; lean_object* v_infoState_3584_; lean_object* v_snapshotTasks_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3594_; 
v___x_3576_ = lean_st_ref_take(v___y_3557_);
v_env_3577_ = lean_ctor_get(v___x_3576_, 0);
v_nextMacroScope_3578_ = lean_ctor_get(v___x_3576_, 1);
v_ngen_3579_ = lean_ctor_get(v___x_3576_, 2);
v_auxDeclNGen_3580_ = lean_ctor_get(v___x_3576_, 3);
v_traceState_3581_ = lean_ctor_get(v___x_3576_, 4);
v_recordedDeps_3582_ = lean_ctor_get(v___x_3576_, 6);
v_messages_3583_ = lean_ctor_get(v___x_3576_, 7);
v_infoState_3584_ = lean_ctor_get(v___x_3576_, 8);
v_snapshotTasks_3585_ = lean_ctor_get(v___x_3576_, 9);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3594_ == 0)
{
lean_object* v_unused_3595_; 
v_unused_3595_ = lean_ctor_get(v___x_3576_, 5);
lean_dec(v_unused_3595_);
v___x_3587_ = v___x_3576_;
v_isShared_3588_ = v_isSharedCheck_3594_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_snapshotTasks_3585_);
lean_inc(v_infoState_3584_);
lean_inc(v_messages_3583_);
lean_inc(v_recordedDeps_3582_);
lean_inc(v_traceState_3581_);
lean_inc(v_auxDeclNGen_3580_);
lean_inc(v_ngen_3579_);
lean_inc(v_nextMacroScope_3578_);
lean_inc(v_env_3577_);
lean_dec(v___x_3576_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3594_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3589_; lean_object* v___x_3591_; 
lean_inc(v_snd_3501_);
lean_inc(v_fst_3496_);
v___x_3589_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3571_, v_env_3577_, v_fst_3496_, v_snd_3501_, v___x_3559_);
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 5, v___x_3392_);
lean_ctor_set(v___x_3587_, 0, v___x_3589_);
v___x_3591_ = v___x_3587_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3589_);
lean_ctor_set(v_reuseFailAlloc_3593_, 1, v_nextMacroScope_3578_);
lean_ctor_set(v_reuseFailAlloc_3593_, 2, v_ngen_3579_);
lean_ctor_set(v_reuseFailAlloc_3593_, 3, v_auxDeclNGen_3580_);
lean_ctor_set(v_reuseFailAlloc_3593_, 4, v_traceState_3581_);
lean_ctor_set(v_reuseFailAlloc_3593_, 5, v___x_3392_);
lean_ctor_set(v_reuseFailAlloc_3593_, 6, v_recordedDeps_3582_);
lean_ctor_set(v_reuseFailAlloc_3593_, 7, v_messages_3583_);
lean_ctor_set(v_reuseFailAlloc_3593_, 8, v_infoState_3584_);
lean_ctor_set(v_reuseFailAlloc_3593_, 9, v_snapshotTasks_3585_);
v___x_3591_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
lean_object* v___x_3592_; 
v___x_3592_ = lean_st_ref_put(v___y_3557_, v___x_3591_);
v_exportedInfo_x3f_3536_ = v_exportedInfo_x3f_3395_;
v___y_3537_ = v___y_3556_;
v___y_3538_ = v___y_3557_;
goto v___jp_3535_;
}
}
}
else
{
lean_dec_ref_known(v___x_3575_, 1);
lean_dec_ref(v___x_3392_);
v_exportedInfo_x3f_3536_ = v_exportedInfo_x3f_3395_;
v___y_3537_ = v___y_3556_;
v___y_3538_ = v___y_3557_;
goto v___jp_3535_;
}
}
}
else
{
lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v_a_3598_; uint8_t v___x_3599_; 
lean_dec(v_exportedInfo_x3f_3395_);
lean_dec_ref(v___x_3392_);
v___x_3596_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3597_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3596_, v___y_3556_);
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_a_3598_);
lean_dec_ref(v___x_3597_);
v___x_3599_ = lean_unbox(v_a_3598_);
lean_dec(v_a_3598_);
if (v___x_3599_ == 0)
{
lean_object* v_toCold_3600_; lean_object* v_options_3601_; uint8_t v_hasTrace_3602_; 
v_toCold_3600_ = lean_ctor_get(v___y_3556_, 0);
v_options_3601_ = lean_ctor_get(v_toCold_3600_, 2);
v_hasTrace_3602_ = lean_ctor_get_uint8(v_options_3601_, sizeof(void*)*1);
if (v_hasTrace_3602_ == 0)
{
lean_dec(v_cls_3390_);
v_exportedInfo_x3f_3536_ = v___x_3393_;
v___y_3537_ = v___y_3556_;
v___y_3538_ = v___y_3557_;
goto v___jp_3535_;
}
else
{
lean_object* v_inheritedTraceOptions_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; uint8_t v___x_3606_; 
v_inheritedTraceOptions_3603_ = lean_ctor_get(v_toCold_3600_, 11);
v___x_3604_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3390_);
v___x_3605_ = l_Lean_Name_append(v___x_3604_, v_cls_3390_);
v___x_3606_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3603_, v_options_3601_, v___x_3605_);
lean_dec(v___x_3605_);
if (v___x_3606_ == 0)
{
lean_dec(v_cls_3390_);
v_exportedInfo_x3f_3536_ = v___x_3393_;
v___y_3537_ = v___y_3556_;
v___y_3538_ = v___y_3557_;
goto v___jp_3535_;
}
else
{
lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3607_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_3608_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3390_, v___x_3607_, v___y_3556_, v___y_3557_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_dec_ref_known(v___x_3608_, 1);
v_exportedInfo_x3f_3536_ = v___x_3393_;
v___y_3537_ = v___y_3556_;
v___y_3538_ = v___y_3557_;
goto v___jp_3535_;
}
else
{
lean_del_object(v___x_3503_);
lean_dec(v_snd_3501_);
lean_dec(v_fst_3500_);
lean_dec(v_fst_3496_);
lean_dec(v___x_3393_);
lean_dec(v_decl_3388_);
return v___x_3608_;
}
}
}
}
else
{
lean_object* v_toCold_3609_; lean_object* v_options_3610_; uint8_t v_hasTrace_3611_; 
lean_dec(v___x_3393_);
v_toCold_3609_ = lean_ctor_get(v___y_3556_, 0);
v_options_3610_ = lean_ctor_get(v_toCold_3609_, 2);
v_hasTrace_3611_ = lean_ctor_get_uint8(v_options_3610_, sizeof(void*)*1);
if (v_hasTrace_3611_ == 0)
{
lean_dec(v_cls_3390_);
v___y_3552_ = v___y_3556_;
v___y_3553_ = v___y_3557_;
goto v___jp_3551_;
}
else
{
lean_object* v_inheritedTraceOptions_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; uint8_t v___x_3615_; 
v_inheritedTraceOptions_3612_ = lean_ctor_get(v_toCold_3609_, 11);
v___x_3613_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3390_);
v___x_3614_ = l_Lean_Name_append(v___x_3613_, v_cls_3390_);
v___x_3615_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3612_, v_options_3610_, v___x_3614_);
lean_dec(v___x_3614_);
if (v___x_3615_ == 0)
{
lean_dec(v_cls_3390_);
v___y_3552_ = v___y_3556_;
v___y_3553_ = v___y_3557_;
goto v___jp_3551_;
}
else
{
lean_object* v___x_3616_; lean_object* v___x_3617_; 
v___x_3616_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_3617_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3390_, v___x_3616_, v___y_3556_, v___y_3557_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_dec_ref_known(v___x_3617_, 1);
v___y_3552_ = v___y_3556_;
v___y_3553_ = v___y_3557_;
goto v___jp_3551_;
}
else
{
lean_del_object(v___x_3503_);
lean_dec(v_snd_3501_);
lean_dec(v_fst_3500_);
lean_dec(v_fst_3496_);
lean_dec(v_decl_3388_);
return v___x_3617_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14___boxed(lean_object* v_decl_3630_, lean_object* v___x_3631_, lean_object* v_cls_3632_, lean_object* v___x_3633_, lean_object* v___x_3634_, lean_object* v___x_3635_, lean_object* v_____x_3636_, lean_object* v_exportedInfo_x3f_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
uint8_t v___x_55516__boxed_3641_; uint8_t v___x_55518__boxed_3642_; lean_object* v_res_3643_; 
v___x_55516__boxed_3641_ = lean_unbox(v___x_3631_);
v___x_55518__boxed_3642_ = lean_unbox(v___x_3633_);
v_res_3643_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(v_decl_3630_, v___x_55516__boxed_3641_, v_cls_3632_, v___x_55518__boxed_3642_, v___x_3634_, v___x_3635_, v_____x_3636_, v_exportedInfo_x3f_3637_, v___y_3638_, v___y_3639_);
lean_dec(v___y_3639_);
lean_dec_ref(v___y_3638_);
return v_res_3643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(lean_object* v___f_3644_, uint8_t v_forceExpose_3645_, lean_object* v___x_3646_, lean_object* v_cls_3647_, lean_object* v_defn_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
lean_object* v_exportedInfo_x3f_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3665_; lean_object* v___y_3666_; lean_object* v___y_3667_; uint8_t v___y_3668_; lean_object* v___x_3672_; lean_object* v_env_3673_; lean_object* v___x_3674_; 
v___x_3672_ = lean_st_ref_get(v___y_3650_);
v_env_3673_ = lean_ctor_get(v___x_3672_, 0);
lean_inc_ref(v_env_3673_);
lean_dec(v___x_3672_);
v___x_3674_ = lean_st_ref_get(v___y_3650_);
if (v_forceExpose_3645_ == 0)
{
lean_object* v_env_3675_; lean_object* v___x_3676_; uint8_t v_isModule_3677_; 
v_env_3675_ = lean_ctor_get(v___x_3674_, 0);
lean_inc_ref(v_env_3675_);
lean_dec(v___x_3674_);
v___x_3676_ = l_Lean_Environment_header(v_env_3673_);
lean_dec_ref(v_env_3673_);
v_isModule_3677_ = lean_ctor_get_uint8(v___x_3676_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_3676_);
if (v_isModule_3677_ == 0)
{
lean_dec_ref(v_env_3675_);
lean_dec(v_cls_3647_);
v_exportedInfo_x3f_3653_ = v___x_3646_;
v___y_3654_ = v___y_3649_;
v___y_3655_ = v___y_3650_;
goto v___jp_3652_;
}
else
{
uint8_t v_isExporting_3678_; lean_object* v___y_3680_; lean_object* v___y_3681_; 
v_isExporting_3678_ = lean_ctor_get_uint8(v_env_3675_, sizeof(void*)*13);
lean_dec_ref(v_env_3675_);
if (v_isExporting_3678_ == 0)
{
lean_object* v_toCold_3686_; lean_object* v_options_3687_; uint8_t v_hasTrace_3688_; 
lean_dec(v___x_3646_);
v_toCold_3686_ = lean_ctor_get(v___y_3649_, 0);
v_options_3687_ = lean_ctor_get(v_toCold_3686_, 2);
v_hasTrace_3688_ = lean_ctor_get_uint8(v_options_3687_, sizeof(void*)*1);
if (v_hasTrace_3688_ == 0)
{
lean_dec(v_cls_3647_);
v___y_3680_ = v___y_3649_;
v___y_3681_ = v___y_3650_;
goto v___jp_3679_;
}
else
{
lean_object* v_inheritedTraceOptions_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; uint8_t v___x_3692_; 
v_inheritedTraceOptions_3689_ = lean_ctor_get(v_toCold_3686_, 11);
v___x_3690_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3647_);
v___x_3691_ = l_Lean_Name_append(v___x_3690_, v_cls_3647_);
v___x_3692_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3689_, v_options_3687_, v___x_3691_);
lean_dec(v___x_3691_);
if (v___x_3692_ == 0)
{
lean_dec(v_cls_3647_);
v___y_3680_ = v___y_3649_;
v___y_3681_ = v___y_3650_;
goto v___jp_3679_;
}
else
{
lean_object* v_toConstantVal_3693_; lean_object* v_name_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
v_toConstantVal_3693_ = lean_ctor_get(v_defn_3648_, 0);
v_name_3694_ = lean_ctor_get(v_toConstantVal_3693_, 0);
v___x_3695_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_3694_);
v___x_3696_ = l_Lean_MessageData_ofName(v_name_3694_);
v___x_3697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3695_);
lean_ctor_set(v___x_3697_, 1, v___x_3696_);
v___x_3698_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_3699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3697_);
lean_ctor_set(v___x_3699_, 1, v___x_3698_);
v___x_3700_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3647_, v___x_3699_, v___y_3649_, v___y_3650_);
if (lean_obj_tag(v___x_3700_) == 0)
{
lean_dec_ref_known(v___x_3700_, 1);
v___y_3680_ = v___y_3649_;
v___y_3681_ = v___y_3650_;
goto v___jp_3679_;
}
else
{
lean_dec_ref(v_defn_3648_);
lean_dec_ref(v___f_3644_);
return v___x_3700_;
}
}
}
}
else
{
lean_dec(v_cls_3647_);
v_exportedInfo_x3f_3653_ = v___x_3646_;
v___y_3654_ = v___y_3649_;
v___y_3655_ = v___y_3650_;
goto v___jp_3652_;
}
v___jp_3679_:
{
lean_object* v_toConstantVal_3682_; uint8_t v_safety_3683_; uint8_t v___x_3684_; uint8_t v___x_3685_; 
v_toConstantVal_3682_ = lean_ctor_get(v_defn_3648_, 0);
v_safety_3683_ = lean_ctor_get_uint8(v_defn_3648_, sizeof(void*)*4);
v___x_3684_ = 1;
v___x_3685_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3683_, v___x_3684_);
if (v___x_3685_ == 0)
{
lean_inc_ref(v_toConstantVal_3682_);
v___y_3665_ = v_toConstantVal_3682_;
v___y_3666_ = v___y_3680_;
v___y_3667_ = v___y_3681_;
v___y_3668_ = v_isModule_3677_;
goto v___jp_3664_;
}
else
{
lean_inc_ref(v_toConstantVal_3682_);
v___y_3665_ = v_toConstantVal_3682_;
v___y_3666_ = v___y_3680_;
v___y_3667_ = v___y_3681_;
v___y_3668_ = v_isExporting_3678_;
goto v___jp_3664_;
}
}
}
}
else
{
lean_dec(v___x_3674_);
lean_dec_ref(v_env_3673_);
lean_dec(v_cls_3647_);
v_exportedInfo_x3f_3653_ = v___x_3646_;
v___y_3654_ = v___y_3649_;
v___y_3655_ = v___y_3650_;
goto v___jp_3652_;
}
v___jp_3652_:
{
lean_object* v_toConstantVal_3656_; lean_object* v_name_3657_; lean_object* v___x_3658_; uint8_t v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v_toConstantVal_3656_ = lean_ctor_get(v_defn_3648_, 0);
v_name_3657_ = lean_ctor_get(v_toConstantVal_3656_, 0);
lean_inc(v_name_3657_);
v___x_3658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3658_, 0, v_defn_3648_);
v___x_3659_ = 0;
v___x_3660_ = lean_box(v___x_3659_);
v___x_3661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3658_);
lean_ctor_set(v___x_3661_, 1, v___x_3660_);
v___x_3662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3662_, 0, v_name_3657_);
lean_ctor_set(v___x_3662_, 1, v___x_3661_);
lean_inc(v___y_3655_);
lean_inc_ref(v___y_3654_);
v___x_3663_ = lean_apply_5(v___f_3644_, v___x_3662_, v_exportedInfo_x3f_3653_, v___y_3654_, v___y_3655_, lean_box(0));
return v___x_3663_;
}
v___jp_3664_:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3669_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3669_, 0, v___y_3665_);
lean_ctor_set_uint8(v___x_3669_, sizeof(void*)*1, v___y_3668_);
v___x_3670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3669_);
v___x_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3670_);
v_exportedInfo_x3f_3653_ = v___x_3671_;
v___y_3654_ = v___y_3666_;
v___y_3655_ = v___y_3667_;
goto v___jp_3652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11___boxed(lean_object* v___f_3701_, lean_object* v_forceExpose_3702_, lean_object* v___x_3703_, lean_object* v_cls_3704_, lean_object* v_defn_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_){
_start:
{
uint8_t v_forceExpose_boxed_3709_; lean_object* v_res_3710_; 
v_forceExpose_boxed_3709_ = lean_unbox(v_forceExpose_3702_);
v_res_3710_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(v___f_3701_, v_forceExpose_boxed_3709_, v___x_3703_, v_cls_3704_, v_defn_3705_, v___y_3706_, v___y_3707_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(lean_object* v_val_3711_, lean_object* v___f_3712_, lean_object* v_____r_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_){
_start:
{
lean_object* v_toConstantVal_3717_; uint8_t v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
v_toConstantVal_3717_ = lean_ctor_get(v_val_3711_, 0);
v___x_3718_ = 0;
lean_inc_ref(v_toConstantVal_3717_);
v___x_3719_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3719_, 0, v_toConstantVal_3717_);
lean_ctor_set_uint8(v___x_3719_, sizeof(void*)*1, v___x_3718_);
v___x_3720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3719_);
v___x_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3720_);
v___x_3722_ = lean_box(0);
lean_inc(v___y_3715_);
lean_inc_ref(v___y_3714_);
v___x_3723_ = lean_apply_5(v___f_3712_, v___x_3722_, v___x_3721_, v___y_3714_, v___y_3715_, lean_box(0));
return v___x_3723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed(lean_object* v_val_3724_, lean_object* v___f_3725_, lean_object* v_____r_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_val_3724_, v___f_3725_, v_____r_3726_, v___y_3727_, v___y_3728_);
lean_dec(v___y_3728_);
lean_dec_ref(v___y_3727_);
lean_dec_ref(v_val_3724_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(lean_object* v_x_3731_, lean_object* v_x_3732_){
_start:
{
if (lean_obj_tag(v_x_3732_) == 0)
{
return v_x_3731_;
}
else
{
lean_object* v_head_3733_; lean_object* v_tail_3734_; lean_object* v___x_3735_; 
v_head_3733_ = lean_ctor_get(v_x_3732_, 0);
lean_inc(v_head_3733_);
v_tail_3734_ = lean_ctor_get(v_x_3732_, 1);
lean_inc(v_tail_3734_);
lean_dec_ref_known(v_x_3732_, 2);
v___x_3735_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(v_x_3731_, v_head_3733_);
v_x_3731_ = v___x_3735_;
v_x_3732_ = v_tail_3734_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0(void){
_start:
{
lean_object* v_cls_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; 
v_cls_3737_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_3738_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
v___x_3739_ = l_Lean_Name_append(v___x_3738_, v_cls_3737_);
return v___x_3739_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2(void){
_start:
{
lean_object* v___x_3741_; lean_object* v___x_3742_; 
v___x_3741_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1));
v___x_3742_ = l_Lean_stringToMessageData(v___x_3741_);
return v___x_3742_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4(void){
_start:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; 
v___x_3744_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3));
v___x_3745_ = l_Lean_stringToMessageData(v___x_3744_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore(lean_object* v_decl_3746_, uint8_t v_forceExpose_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_){
_start:
{
lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v_a_3754_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v_a_3767_; lean_object* v_toCold_3777_; lean_object* v_options_3778_; lean_object* v_inheritedTraceOptions_3779_; uint8_t v_hasTrace_3780_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; uint8_t v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; uint8_t v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; uint8_t v___y_3895_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v_exportedInfo_x3f_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; uint8_t v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; uint8_t v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; uint8_t v___x_3923_; lean_object* v_cls_3924_; lean_object* v___y_3926_; lean_object* v_options_3927_; lean_object* v_inheritedTraceOptions_3928_; lean_object* v___y_3929_; 
v_toCold_3777_ = lean_ctor_get(v_a_3748_, 0);
v_options_3778_ = lean_ctor_get(v_toCold_3777_, 2);
v_inheritedTraceOptions_3779_ = lean_ctor_get(v_toCold_3777_, 11);
v_hasTrace_3780_ = lean_ctor_get_uint8(v_options_3778_, sizeof(void*)*1);
v___x_3923_ = 0;
v_cls_3924_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
if (v_hasTrace_3780_ == 0)
{
lean_object* v___x_3936_; lean_object* v_env_3937_; lean_object* v_nextMacroScope_3938_; lean_object* v_ngen_3939_; lean_object* v_auxDeclNGen_3940_; lean_object* v_traceState_3941_; lean_object* v_recordedDeps_3942_; lean_object* v_messages_3943_; lean_object* v_infoState_3944_; lean_object* v_snapshotTasks_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_4146_; 
v___x_3936_ = lean_st_ref_take(v_a_3749_);
v_env_3937_ = lean_ctor_get(v___x_3936_, 0);
v_nextMacroScope_3938_ = lean_ctor_get(v___x_3936_, 1);
v_ngen_3939_ = lean_ctor_get(v___x_3936_, 2);
v_auxDeclNGen_3940_ = lean_ctor_get(v___x_3936_, 3);
v_traceState_3941_ = lean_ctor_get(v___x_3936_, 4);
v_recordedDeps_3942_ = lean_ctor_get(v___x_3936_, 6);
v_messages_3943_ = lean_ctor_get(v___x_3936_, 7);
v_infoState_3944_ = lean_ctor_get(v___x_3936_, 8);
v_snapshotTasks_3945_ = lean_ctor_get(v___x_3936_, 9);
v_isSharedCheck_4146_ = !lean_is_exclusive(v___x_3936_);
if (v_isSharedCheck_4146_ == 0)
{
lean_object* v_unused_4147_; 
v_unused_4147_ = lean_ctor_get(v___x_3936_, 5);
lean_dec(v_unused_4147_);
v___x_3947_ = v___x_3936_;
v_isShared_3948_ = v_isSharedCheck_4146_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_snapshotTasks_3945_);
lean_inc(v_infoState_3944_);
lean_inc(v_messages_3943_);
lean_inc(v_recordedDeps_3942_);
lean_inc(v_traceState_3941_);
lean_inc(v_auxDeclNGen_3940_);
lean_inc(v_ngen_3939_);
lean_inc(v_nextMacroScope_3938_);
lean_inc(v_env_3937_);
lean_dec(v___x_3936_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_4146_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3953_; 
lean_inc(v_decl_3746_);
v___x_3949_ = l_Lean_Declaration_getNames(v_decl_3746_);
v___x_3950_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_3937_, v___x_3949_);
v___x_3951_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_3948_ == 0)
{
lean_ctor_set(v___x_3947_, 5, v___x_3951_);
lean_ctor_set(v___x_3947_, 0, v___x_3950_);
v___x_3953_ = v___x_3947_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v___x_3950_);
lean_ctor_set(v_reuseFailAlloc_4145_, 1, v_nextMacroScope_3938_);
lean_ctor_set(v_reuseFailAlloc_4145_, 2, v_ngen_3939_);
lean_ctor_set(v_reuseFailAlloc_4145_, 3, v_auxDeclNGen_3940_);
lean_ctor_set(v_reuseFailAlloc_4145_, 4, v_traceState_3941_);
lean_ctor_set(v_reuseFailAlloc_4145_, 5, v___x_3951_);
lean_ctor_set(v_reuseFailAlloc_4145_, 6, v_recordedDeps_3942_);
lean_ctor_set(v_reuseFailAlloc_4145_, 7, v_messages_3943_);
lean_ctor_set(v_reuseFailAlloc_4145_, 8, v_infoState_3944_);
lean_ctor_set(v_reuseFailAlloc_4145_, 9, v_snapshotTasks_3945_);
v___x_3953_ = v_reuseFailAlloc_4145_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
lean_object* v___x_3954_; lean_object* v___x_3955_; uint8_t v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v_fst_4022_; lean_object* v_fst_4023_; uint8_t v_snd_4024_; lean_object* v_exportedInfo_x3f_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4037_; lean_object* v_exportedInfo_x3f_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; uint8_t v___y_4049_; uint8_t v___y_4054_; lean_object* v___y_4055_; lean_object* v_toConstantVal_4056_; uint8_t v_safety_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; uint8_t v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v_defn_4070_; lean_object* v___y_4071_; lean_object* v___y_4072_; 
v___x_3954_ = lean_st_ref_put(v_a_3749_, v___x_3953_);
v___x_3955_ = lean_box(0);
switch(lean_obj_tag(v_decl_3746_))
{
case 2:
{
lean_object* v_val_4095_; lean_object* v_exportedInfo_x3f_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___x_4104_; 
v_val_4095_ = lean_ctor_get(v_decl_3746_, 0);
v___x_4104_ = lean_st_ref_get(v_a_3749_);
if (v_forceExpose_3747_ == 0)
{
lean_object* v_env_4105_; lean_object* v___x_4106_; uint8_t v_isModule_4107_; 
v_env_4105_ = lean_ctor_get(v___x_4104_, 0);
lean_inc_ref(v_env_4105_);
lean_dec(v___x_4104_);
v___x_4106_ = l_Lean_Environment_header(v_env_4105_);
lean_dec_ref(v_env_4105_);
v_isModule_4107_ = lean_ctor_get_uint8(v___x_4106_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4106_);
if (v_isModule_4107_ == 0)
{
v_exportedInfo_x3f_4097_ = v___x_3955_;
v___y_4098_ = v_a_3748_;
v___y_4099_ = v_a_3749_;
goto v___jp_4096_;
}
else
{
lean_object* v_toConstantVal_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
v_toConstantVal_4108_ = lean_ctor_get(v_val_4095_, 0);
lean_inc_ref(v_toConstantVal_4108_);
v___x_4109_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4109_, 0, v_toConstantVal_4108_);
lean_ctor_set_uint8(v___x_4109_, sizeof(void*)*1, v_hasTrace_3780_);
v___x_4110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4109_);
v___x_4111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4111_, 0, v___x_4110_);
v_exportedInfo_x3f_4097_ = v___x_4111_;
v___y_4098_ = v_a_3748_;
v___y_4099_ = v_a_3749_;
goto v___jp_4096_;
}
}
else
{
lean_dec(v___x_4104_);
v_exportedInfo_x3f_4097_ = v___x_3955_;
v___y_4098_ = v_a_3748_;
v___y_4099_ = v_a_3749_;
goto v___jp_4096_;
}
v___jp_4096_:
{
lean_object* v_toConstantVal_4100_; lean_object* v_name_4101_; lean_object* v___x_4102_; uint8_t v___x_4103_; 
v_toConstantVal_4100_ = lean_ctor_get(v_val_4095_, 0);
v_name_4101_ = lean_ctor_get(v_toConstantVal_4100_, 0);
lean_inc_ref(v_val_4095_);
v___x_4102_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4102_, 0, v_val_4095_);
v___x_4103_ = 1;
lean_inc(v_name_4101_);
v_fst_4022_ = v_name_4101_;
v_fst_4023_ = v___x_4102_;
v_snd_4024_ = v___x_4103_;
v_exportedInfo_x3f_4025_ = v_exportedInfo_x3f_4097_;
v___y_4026_ = v___y_4098_;
v___y_4027_ = v___y_4099_;
goto v___jp_4021_;
}
}
case 1:
{
lean_object* v_val_4112_; 
v_val_4112_ = lean_ctor_get(v_decl_3746_, 0);
lean_inc_ref(v_val_4112_);
v_defn_4070_ = v_val_4112_;
v___y_4071_ = v_a_3748_;
v___y_4072_ = v_a_3749_;
goto v___jp_4069_;
}
case 5:
{
lean_object* v_defns_4113_; 
v_defns_4113_ = lean_ctor_get(v_decl_3746_, 0);
if (lean_obj_tag(v_defns_4113_) == 1)
{
lean_object* v_tail_4114_; 
v_tail_4114_ = lean_ctor_get(v_defns_4113_, 1);
if (lean_obj_tag(v_tail_4114_) == 0)
{
lean_object* v_head_4115_; 
v_head_4115_ = lean_ctor_get(v_defns_4113_, 0);
lean_inc(v_head_4115_);
v_defn_4070_ = v_head_4115_;
v___y_4071_ = v_a_3748_;
v___y_4072_ = v_a_3749_;
goto v___jp_4069_;
}
else
{
lean_object* v___x_4116_; 
v___x_4116_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3746_, v_a_3748_, v_a_3749_);
return v___x_4116_;
}
}
else
{
lean_object* v___x_4117_; 
v___x_4117_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3746_, v_a_3748_, v_a_3749_);
return v___x_4117_;
}
}
case 3:
{
lean_object* v_val_4118_; lean_object* v_exportedInfo_x3f_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___x_4127_; lean_object* v_env_4128_; lean_object* v___x_4129_; 
v_val_4118_ = lean_ctor_get(v_decl_3746_, 0);
v___x_4127_ = lean_st_ref_get(v_a_3749_);
v_env_4128_ = lean_ctor_get(v___x_4127_, 0);
lean_inc_ref(v_env_4128_);
lean_dec(v___x_4127_);
v___x_4129_ = lean_st_ref_get(v_a_3749_);
if (v_forceExpose_3747_ == 0)
{
lean_object* v_env_4130_; lean_object* v___x_4131_; uint8_t v_isModule_4132_; 
v_env_4130_ = lean_ctor_get(v___x_4129_, 0);
lean_inc_ref(v_env_4130_);
lean_dec(v___x_4129_);
v___x_4131_ = l_Lean_Environment_header(v_env_4128_);
lean_dec_ref(v_env_4128_);
v_isModule_4132_ = lean_ctor_get_uint8(v___x_4131_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4131_);
if (v_isModule_4132_ == 0)
{
lean_dec_ref(v_env_4130_);
v_exportedInfo_x3f_4120_ = v___x_3955_;
v___y_4121_ = v_a_3748_;
v___y_4122_ = v_a_3749_;
goto v___jp_4119_;
}
else
{
uint8_t v_isExporting_4133_; 
v_isExporting_4133_ = lean_ctor_get_uint8(v_env_4130_, sizeof(void*)*13);
lean_dec_ref(v_env_4130_);
if (v_isExporting_4133_ == 0)
{
lean_object* v_toConstantVal_4134_; uint8_t v_isUnsafe_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; 
v_toConstantVal_4134_ = lean_ctor_get(v_val_4118_, 0);
v_isUnsafe_4135_ = lean_ctor_get_uint8(v_val_4118_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4134_);
v___x_4136_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4136_, 0, v_toConstantVal_4134_);
lean_ctor_set_uint8(v___x_4136_, sizeof(void*)*1, v_isUnsafe_4135_);
v___x_4137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4137_, 0, v___x_4136_);
v___x_4138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4137_);
v_exportedInfo_x3f_4120_ = v___x_4138_;
v___y_4121_ = v_a_3748_;
v___y_4122_ = v_a_3749_;
goto v___jp_4119_;
}
else
{
v_exportedInfo_x3f_4120_ = v___x_3955_;
v___y_4121_ = v_a_3748_;
v___y_4122_ = v_a_3749_;
goto v___jp_4119_;
}
}
}
else
{
lean_dec(v___x_4129_);
lean_dec_ref(v_env_4128_);
v_exportedInfo_x3f_4120_ = v___x_3955_;
v___y_4121_ = v_a_3748_;
v___y_4122_ = v_a_3749_;
goto v___jp_4119_;
}
v___jp_4119_:
{
lean_object* v_toConstantVal_4123_; lean_object* v_name_4124_; lean_object* v___x_4125_; uint8_t v___x_4126_; 
v_toConstantVal_4123_ = lean_ctor_get(v_val_4118_, 0);
v_name_4124_ = lean_ctor_get(v_toConstantVal_4123_, 0);
lean_inc_ref(v_val_4118_);
v___x_4125_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4125_, 0, v_val_4118_);
v___x_4126_ = 3;
lean_inc(v_name_4124_);
v_fst_4022_ = v_name_4124_;
v_fst_4023_ = v___x_4125_;
v_snd_4024_ = v___x_4126_;
v_exportedInfo_x3f_4025_ = v_exportedInfo_x3f_4120_;
v___y_4026_ = v___y_4121_;
v___y_4027_ = v___y_4122_;
goto v___jp_4021_;
}
}
case 0:
{
lean_object* v_val_4139_; lean_object* v_toConstantVal_4140_; lean_object* v_name_4141_; lean_object* v___x_4142_; uint8_t v___x_4143_; 
v_val_4139_ = lean_ctor_get(v_decl_3746_, 0);
v_toConstantVal_4140_ = lean_ctor_get(v_val_4139_, 0);
v_name_4141_ = lean_ctor_get(v_toConstantVal_4140_, 0);
lean_inc_ref(v_val_4139_);
v___x_4142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4142_, 0, v_val_4139_);
v___x_4143_ = 2;
lean_inc(v_name_4141_);
v_fst_4022_ = v_name_4141_;
v_fst_4023_ = v___x_4142_;
v_snd_4024_ = v___x_4143_;
v_exportedInfo_x3f_4025_ = v___x_3955_;
v___y_4026_ = v_a_3748_;
v___y_4027_ = v_a_3749_;
goto v___jp_4021_;
}
default: 
{
lean_object* v___x_4144_; 
v___x_4144_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3746_, v_a_3748_, v_a_3749_);
return v___x_4144_;
}
}
v___jp_3956_:
{
lean_object* v___x_3963_; uint8_t v___x_3964_; 
lean_inc(v_decl_3746_);
v___x_3963_ = l_Lean_Declaration_getTopLevelNames(v_decl_3746_);
v___x_3964_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3963_);
lean_dec(v___x_3963_);
if (v___x_3964_ == 0)
{
if (lean_obj_tag(v___y_3960_) == 0)
{
lean_object* v_toCold_3965_; lean_object* v_options_3966_; uint8_t v_hasTrace_3967_; 
v_toCold_3965_ = lean_ctor_get(v___y_3961_, 0);
v_options_3966_ = lean_ctor_get(v_toCold_3965_, 2);
v_hasTrace_3967_ = lean_ctor_get_uint8(v_options_3966_, sizeof(void*)*1);
if (v_hasTrace_3967_ == 0)
{
v___y_3917_ = v___y_3957_;
v___y_3918_ = v___y_3958_;
v___y_3919_ = v___y_3959_;
v___y_3920_ = v___y_3961_;
v___y_3921_ = v___y_3962_;
goto v___jp_3916_;
}
else
{
lean_object* v_inheritedTraceOptions_3968_; lean_object* v___x_3969_; uint8_t v___x_3970_; 
v_inheritedTraceOptions_3968_ = lean_ctor_get(v_toCold_3965_, 11);
v___x_3969_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_3970_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3968_, v_options_3966_, v___x_3969_);
if (v___x_3970_ == 0)
{
v___y_3917_ = v___y_3957_;
v___y_3918_ = v___y_3958_;
v___y_3919_ = v___y_3959_;
v___y_3920_ = v___y_3961_;
v___y_3921_ = v___y_3962_;
goto v___jp_3916_;
}
else
{
lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3971_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_3972_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3924_, v___x_3971_, v___y_3961_, v___y_3962_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_dec_ref_known(v___x_3972_, 1);
v___y_3917_ = v___y_3957_;
v___y_3918_ = v___y_3958_;
v___y_3919_ = v___y_3959_;
v___y_3920_ = v___y_3961_;
v___y_3921_ = v___y_3962_;
goto v___jp_3916_;
}
else
{
lean_dec_ref(v___y_3959_);
lean_dec(v___y_3958_);
lean_dec(v_decl_3746_);
return v___x_3972_;
}
}
}
}
else
{
lean_object* v___x_3973_; lean_object* v_env_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; uint8_t v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
v___x_3973_ = lean_st_ref_get(v___y_3962_);
v_env_3974_ = lean_ctor_get(v___x_3973_, 0);
lean_inc_ref(v_env_3974_);
lean_dec(v___x_3973_);
v___x_3975_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_3976_ = lean_box(1);
v___x_3977_ = 0;
v___x_3978_ = lean_box(v___x_3923_);
lean_inc(v___y_3958_);
v___x_3979_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3978_, v___x_3975_, v_env_3974_, v___y_3958_, v___x_3976_, v___x_3977_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v___x_3980_; lean_object* v_env_3981_; lean_object* v_nextMacroScope_3982_; lean_object* v_ngen_3983_; lean_object* v_auxDeclNGen_3984_; lean_object* v_traceState_3985_; lean_object* v_recordedDeps_3986_; lean_object* v_messages_3987_; lean_object* v_infoState_3988_; lean_object* v_snapshotTasks_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_3999_; 
v___x_3980_ = lean_st_ref_take(v___y_3962_);
v_env_3981_ = lean_ctor_get(v___x_3980_, 0);
v_nextMacroScope_3982_ = lean_ctor_get(v___x_3980_, 1);
v_ngen_3983_ = lean_ctor_get(v___x_3980_, 2);
v_auxDeclNGen_3984_ = lean_ctor_get(v___x_3980_, 3);
v_traceState_3985_ = lean_ctor_get(v___x_3980_, 4);
v_recordedDeps_3986_ = lean_ctor_get(v___x_3980_, 6);
v_messages_3987_ = lean_ctor_get(v___x_3980_, 7);
v_infoState_3988_ = lean_ctor_get(v___x_3980_, 8);
v_snapshotTasks_3989_ = lean_ctor_get(v___x_3980_, 9);
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3980_);
if (v_isSharedCheck_3999_ == 0)
{
lean_object* v_unused_4000_; 
v_unused_4000_ = lean_ctor_get(v___x_3980_, 5);
lean_dec(v_unused_4000_);
v___x_3991_ = v___x_3980_;
v_isShared_3992_ = v_isSharedCheck_3999_;
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
v_isShared_3992_ = v_isSharedCheck_3999_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3996_; 
v___x_3993_ = lean_box(v___y_3957_);
lean_inc(v___y_3958_);
v___x_3994_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3975_, v_env_3981_, v___y_3958_, v___x_3993_, v___x_3964_);
if (v_isShared_3992_ == 0)
{
lean_ctor_set(v___x_3991_, 5, v___x_3951_);
lean_ctor_set(v___x_3991_, 0, v___x_3994_);
v___x_3996_ = v___x_3991_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v___x_3994_);
lean_ctor_set(v_reuseFailAlloc_3998_, 1, v_nextMacroScope_3982_);
lean_ctor_set(v_reuseFailAlloc_3998_, 2, v_ngen_3983_);
lean_ctor_set(v_reuseFailAlloc_3998_, 3, v_auxDeclNGen_3984_);
lean_ctor_set(v_reuseFailAlloc_3998_, 4, v_traceState_3985_);
lean_ctor_set(v_reuseFailAlloc_3998_, 5, v___x_3951_);
lean_ctor_set(v_reuseFailAlloc_3998_, 6, v_recordedDeps_3986_);
lean_ctor_set(v_reuseFailAlloc_3998_, 7, v_messages_3987_);
lean_ctor_set(v_reuseFailAlloc_3998_, 8, v_infoState_3988_);
lean_ctor_set(v_reuseFailAlloc_3998_, 9, v_snapshotTasks_3989_);
v___x_3996_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
lean_object* v___x_3997_; 
v___x_3997_ = lean_st_ref_put(v___y_3962_, v___x_3996_);
v___y_3895_ = v___y_3957_;
v___y_3896_ = v___y_3958_;
v___y_3897_ = v___y_3959_;
v_exportedInfo_x3f_3898_ = v___y_3960_;
v___y_3899_ = v___y_3961_;
v___y_3900_ = v___y_3962_;
goto v___jp_3894_;
}
}
}
else
{
lean_dec_ref_known(v___x_3979_, 1);
v___y_3895_ = v___y_3957_;
v___y_3896_ = v___y_3958_;
v___y_3897_ = v___y_3959_;
v_exportedInfo_x3f_3898_ = v___y_3960_;
v___y_3899_ = v___y_3961_;
v___y_3900_ = v___y_3962_;
goto v___jp_3894_;
}
}
}
else
{
lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v_a_4003_; uint8_t v___x_4004_; 
lean_dec(v___y_3960_);
v___x_4001_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4002_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4001_, v___y_3961_);
v_a_4003_ = lean_ctor_get(v___x_4002_, 0);
lean_inc(v_a_4003_);
lean_dec_ref(v___x_4002_);
v___x_4004_ = lean_unbox(v_a_4003_);
lean_dec(v_a_4003_);
if (v___x_4004_ == 0)
{
lean_object* v_toCold_4005_; lean_object* v_options_4006_; uint8_t v_hasTrace_4007_; 
v_toCold_4005_ = lean_ctor_get(v___y_3961_, 0);
v_options_4006_ = lean_ctor_get(v_toCold_4005_, 2);
v_hasTrace_4007_ = lean_ctor_get_uint8(v_options_4006_, sizeof(void*)*1);
if (v_hasTrace_4007_ == 0)
{
v___y_3895_ = v___y_3957_;
v___y_3896_ = v___y_3958_;
v___y_3897_ = v___y_3959_;
v_exportedInfo_x3f_3898_ = v___x_3955_;
v___y_3899_ = v___y_3961_;
v___y_3900_ = v___y_3962_;
goto v___jp_3894_;
}
else
{
lean_object* v_inheritedTraceOptions_4008_; lean_object* v___x_4009_; uint8_t v___x_4010_; 
v_inheritedTraceOptions_4008_ = lean_ctor_get(v_toCold_4005_, 11);
v___x_4009_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4010_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4008_, v_options_4006_, v___x_4009_);
if (v___x_4010_ == 0)
{
v___y_3895_ = v___y_3957_;
v___y_3896_ = v___y_3958_;
v___y_3897_ = v___y_3959_;
v_exportedInfo_x3f_3898_ = v___x_3955_;
v___y_3899_ = v___y_3961_;
v___y_3900_ = v___y_3962_;
goto v___jp_3894_;
}
else
{
lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4011_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_4012_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3924_, v___x_4011_, v___y_3961_, v___y_3962_);
if (lean_obj_tag(v___x_4012_) == 0)
{
lean_dec_ref_known(v___x_4012_, 1);
v___y_3895_ = v___y_3957_;
v___y_3896_ = v___y_3958_;
v___y_3897_ = v___y_3959_;
v_exportedInfo_x3f_3898_ = v___x_3955_;
v___y_3899_ = v___y_3961_;
v___y_3900_ = v___y_3962_;
goto v___jp_3894_;
}
else
{
lean_dec_ref(v___y_3959_);
lean_dec(v___y_3958_);
lean_dec(v_decl_3746_);
return v___x_4012_;
}
}
}
}
else
{
lean_object* v_toCold_4013_; lean_object* v_options_4014_; uint8_t v_hasTrace_4015_; 
v_toCold_4013_ = lean_ctor_get(v___y_3961_, 0);
v_options_4014_ = lean_ctor_get(v_toCold_4013_, 2);
v_hasTrace_4015_ = lean_ctor_get_uint8(v_options_4014_, sizeof(void*)*1);
if (v_hasTrace_4015_ == 0)
{
v___y_3910_ = v___y_3957_;
v___y_3911_ = v___y_3958_;
v___y_3912_ = v___y_3959_;
v___y_3913_ = v___y_3961_;
v___y_3914_ = v___y_3962_;
goto v___jp_3909_;
}
else
{
lean_object* v_inheritedTraceOptions_4016_; lean_object* v___x_4017_; uint8_t v___x_4018_; 
v_inheritedTraceOptions_4016_ = lean_ctor_get(v_toCold_4013_, 11);
v___x_4017_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4018_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4016_, v_options_4014_, v___x_4017_);
if (v___x_4018_ == 0)
{
v___y_3910_ = v___y_3957_;
v___y_3911_ = v___y_3958_;
v___y_3912_ = v___y_3959_;
v___y_3913_ = v___y_3961_;
v___y_3914_ = v___y_3962_;
goto v___jp_3909_;
}
else
{
lean_object* v___x_4019_; lean_object* v___x_4020_; 
v___x_4019_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_4020_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3924_, v___x_4019_, v___y_3961_, v___y_3962_);
if (lean_obj_tag(v___x_4020_) == 0)
{
lean_dec_ref_known(v___x_4020_, 1);
v___y_3910_ = v___y_3957_;
v___y_3911_ = v___y_3958_;
v___y_3912_ = v___y_3959_;
v___y_3913_ = v___y_3961_;
v___y_3914_ = v___y_3962_;
goto v___jp_3909_;
}
else
{
lean_dec_ref(v___y_3959_);
lean_dec(v___y_3958_);
lean_dec(v_decl_3746_);
return v___x_4020_;
}
}
}
}
}
}
v___jp_4021_:
{
lean_object* v___x_4028_; lean_object* v_env_4029_; uint8_t v___x_4030_; 
v___x_4028_ = lean_st_ref_get(v___y_4027_);
v_env_4029_ = lean_ctor_get(v___x_4028_, 0);
lean_inc_ref(v_env_4029_);
lean_dec(v___x_4028_);
v___x_4030_ = l_Lean_Environment_containsOnBranch(v_env_4029_, v_fst_4022_);
lean_dec_ref(v_env_4029_);
if (v___x_4030_ == 0)
{
v___y_3957_ = v_snd_4024_;
v___y_3958_ = v_fst_4022_;
v___y_3959_ = v_fst_4023_;
v___y_3960_ = v_exportedInfo_x3f_4025_;
v___y_3961_ = v___y_4026_;
v___y_3962_ = v___y_4027_;
goto v___jp_3956_;
}
else
{
lean_object* v___x_4031_; lean_object* v_env_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; 
lean_dec(v_exportedInfo_x3f_4025_);
lean_dec_ref(v_fst_4023_);
lean_dec(v_decl_3746_);
v___x_4031_ = lean_st_ref_get(v___y_4027_);
v_env_4032_ = lean_ctor_get(v___x_4031_, 0);
lean_inc_ref(v_env_4032_);
lean_dec(v___x_4031_);
v___x_4033_ = lean_elab_environment_to_kernel_env(v_env_4032_);
v___x_4034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4034_, 0, v___x_4033_);
lean_ctor_set(v___x_4034_, 1, v_fst_4022_);
v___x_4035_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4034_, v___y_4026_, v___y_4027_);
return v___x_4035_;
}
}
v___jp_4036_:
{
lean_object* v_toConstantVal_4041_; lean_object* v_name_4042_; lean_object* v___x_4043_; 
v_toConstantVal_4041_ = lean_ctor_get(v___y_4037_, 0);
v_name_4042_ = lean_ctor_get(v_toConstantVal_4041_, 0);
lean_inc(v_name_4042_);
v___x_4043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4043_, 0, v___y_4037_);
v_fst_4022_ = v_name_4042_;
v_fst_4023_ = v___x_4043_;
v_snd_4024_ = v___x_3923_;
v_exportedInfo_x3f_4025_ = v_exportedInfo_x3f_4038_;
v___y_4026_ = v___y_4039_;
v___y_4027_ = v___y_4040_;
goto v___jp_4021_;
}
v___jp_4044_:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; 
v___x_4050_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4050_, 0, v___y_4045_);
lean_ctor_set_uint8(v___x_4050_, sizeof(void*)*1, v___y_4049_);
v___x_4051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4050_);
v___x_4052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4051_);
v___y_4037_ = v___y_4047_;
v_exportedInfo_x3f_4038_ = v___x_4052_;
v___y_4039_ = v___y_4046_;
v___y_4040_ = v___y_4048_;
goto v___jp_4036_;
}
v___jp_4053_:
{
uint8_t v___x_4060_; uint8_t v___x_4061_; 
v___x_4060_ = 1;
v___x_4061_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4057_, v___x_4060_);
if (v___x_4061_ == 0)
{
v___y_4045_ = v_toConstantVal_4056_;
v___y_4046_ = v___y_4058_;
v___y_4047_ = v___y_4055_;
v___y_4048_ = v___y_4059_;
v___y_4049_ = v___y_4054_;
goto v___jp_4044_;
}
else
{
v___y_4045_ = v_toConstantVal_4056_;
v___y_4046_ = v___y_4058_;
v___y_4047_ = v___y_4055_;
v___y_4048_ = v___y_4059_;
v___y_4049_ = v_hasTrace_3780_;
goto v___jp_4044_;
}
}
v___jp_4062_:
{
lean_object* v_toConstantVal_4067_; uint8_t v_safety_4068_; 
v_toConstantVal_4067_ = lean_ctor_get(v___y_4064_, 0);
lean_inc_ref(v_toConstantVal_4067_);
v_safety_4068_ = lean_ctor_get_uint8(v___y_4064_, sizeof(void*)*4);
v___y_4054_ = v___y_4063_;
v___y_4055_ = v___y_4064_;
v_toConstantVal_4056_ = v_toConstantVal_4067_;
v_safety_4057_ = v_safety_4068_;
v___y_4058_ = v___y_4065_;
v___y_4059_ = v___y_4066_;
goto v___jp_4053_;
}
v___jp_4069_:
{
lean_object* v___x_4073_; lean_object* v_env_4074_; lean_object* v___x_4075_; 
v___x_4073_ = lean_st_ref_get(v___y_4072_);
v_env_4074_ = lean_ctor_get(v___x_4073_, 0);
lean_inc_ref(v_env_4074_);
lean_dec(v___x_4073_);
v___x_4075_ = lean_st_ref_get(v___y_4072_);
if (v_forceExpose_3747_ == 0)
{
lean_object* v_env_4076_; lean_object* v___x_4077_; uint8_t v_isModule_4078_; 
v_env_4076_ = lean_ctor_get(v___x_4075_, 0);
lean_inc_ref(v_env_4076_);
lean_dec(v___x_4075_);
v___x_4077_ = l_Lean_Environment_header(v_env_4074_);
lean_dec_ref(v_env_4074_);
v_isModule_4078_ = lean_ctor_get_uint8(v___x_4077_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4077_);
if (v_isModule_4078_ == 0)
{
lean_dec_ref(v_env_4076_);
v___y_4037_ = v_defn_4070_;
v_exportedInfo_x3f_4038_ = v___x_3955_;
v___y_4039_ = v___y_4071_;
v___y_4040_ = v___y_4072_;
goto v___jp_4036_;
}
else
{
uint8_t v_isExporting_4079_; 
v_isExporting_4079_ = lean_ctor_get_uint8(v_env_4076_, sizeof(void*)*13);
lean_dec_ref(v_env_4076_);
if (v_isExporting_4079_ == 0)
{
lean_object* v_toCold_4080_; lean_object* v_options_4081_; uint8_t v_hasTrace_4082_; 
v_toCold_4080_ = lean_ctor_get(v___y_4071_, 0);
v_options_4081_ = lean_ctor_get(v_toCold_4080_, 2);
v_hasTrace_4082_ = lean_ctor_get_uint8(v_options_4081_, sizeof(void*)*1);
if (v_hasTrace_4082_ == 0)
{
v___y_4063_ = v_isModule_4078_;
v___y_4064_ = v_defn_4070_;
v___y_4065_ = v___y_4071_;
v___y_4066_ = v___y_4072_;
goto v___jp_4062_;
}
else
{
lean_object* v_inheritedTraceOptions_4083_; lean_object* v___x_4084_; uint8_t v___x_4085_; 
v_inheritedTraceOptions_4083_ = lean_ctor_get(v_toCold_4080_, 11);
v___x_4084_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4085_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4083_, v_options_4081_, v___x_4084_);
if (v___x_4085_ == 0)
{
v___y_4063_ = v_isModule_4078_;
v___y_4064_ = v_defn_4070_;
v___y_4065_ = v___y_4071_;
v___y_4066_ = v___y_4072_;
goto v___jp_4062_;
}
else
{
lean_object* v_toConstantVal_4086_; uint8_t v_safety_4087_; lean_object* v_name_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
v_toConstantVal_4086_ = lean_ctor_get(v_defn_4070_, 0);
lean_inc_ref(v_toConstantVal_4086_);
v_safety_4087_ = lean_ctor_get_uint8(v_defn_4070_, sizeof(void*)*4);
v_name_4088_ = lean_ctor_get(v_toConstantVal_4086_, 0);
v___x_4089_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_4088_);
v___x_4090_ = l_Lean_MessageData_ofName(v_name_4088_);
v___x_4091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4091_, 0, v___x_4089_);
lean_ctor_set(v___x_4091_, 1, v___x_4090_);
v___x_4092_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4091_);
lean_ctor_set(v___x_4093_, 1, v___x_4092_);
v___x_4094_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3924_, v___x_4093_, v___y_4071_, v___y_4072_);
if (lean_obj_tag(v___x_4094_) == 0)
{
lean_dec_ref_known(v___x_4094_, 1);
v___y_4054_ = v_isModule_4078_;
v___y_4055_ = v_defn_4070_;
v_toConstantVal_4056_ = v_toConstantVal_4086_;
v_safety_4057_ = v_safety_4087_;
v___y_4058_ = v___y_4071_;
v___y_4059_ = v___y_4072_;
goto v___jp_4053_;
}
else
{
lean_dec_ref(v_toConstantVal_4086_);
lean_dec_ref(v_defn_4070_);
lean_dec(v_decl_3746_);
return v___x_4094_;
}
}
}
}
else
{
v___y_4037_ = v_defn_4070_;
v_exportedInfo_x3f_4038_ = v___x_3955_;
v___y_4039_ = v___y_4071_;
v___y_4040_ = v___y_4072_;
goto v___jp_4036_;
}
}
}
else
{
lean_dec(v___x_4075_);
lean_dec_ref(v_env_4074_);
v___y_4037_ = v_defn_4070_;
v_exportedInfo_x3f_4038_ = v___x_3955_;
v___y_4039_ = v___y_4071_;
v___y_4040_ = v___y_4072_;
goto v___jp_4036_;
}
}
}
}
}
else
{
lean_object* v___f_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; uint8_t v___x_4151_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v_a_4155_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v_a_4170_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v_a_4202_; lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v_a_4214_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; 
lean_inc(v_decl_3746_);
v___f_4148_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed), 5, 1);
lean_closure_set(v___f_4148_, 0, v_decl_3746_);
v___x_4149_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_4150_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4151_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3779_, v_options_3778_, v___x_4150_);
if (v___x_4151_ == 0)
{
lean_object* v___x_4429_; uint8_t v___x_4430_; lean_object* v___y_4432_; lean_object* v___y_4433_; lean_object* v___y_4434_; lean_object* v___y_4435_; lean_object* v___y_4436_; lean_object* v___y_4437_; lean_object* v___y_4438_; lean_object* v___y_4439_; lean_object* v___y_4440_; lean_object* v___y_4441_; lean_object* v___y_4442_; lean_object* v___y_4514_; lean_object* v___y_4515_; lean_object* v___y_4516_; lean_object* v___y_4517_; uint8_t v___y_4518_; lean_object* v___y_4519_; lean_object* v___y_4520_; lean_object* v___y_4521_; lean_object* v___y_4543_; uint8_t v___y_4544_; lean_object* v___y_4545_; lean_object* v_exportedInfo_x3f_4546_; lean_object* v___y_4547_; lean_object* v___y_4548_; lean_object* v___y_4558_; uint8_t v___y_4559_; lean_object* v___y_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4565_; uint8_t v___y_4566_; lean_object* v___y_4567_; lean_object* v___y_4568_; lean_object* v___y_4569_; 
v___x_4429_ = l_Lean_trace_profiler;
v___x_4430_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3778_, v___x_4429_);
if (v___x_4430_ == 0)
{
lean_object* v___x_4571_; lean_object* v_env_4572_; lean_object* v_nextMacroScope_4573_; lean_object* v_ngen_4574_; lean_object* v_auxDeclNGen_4575_; lean_object* v_traceState_4576_; lean_object* v_recordedDeps_4577_; lean_object* v_messages_4578_; lean_object* v_infoState_4579_; lean_object* v_snapshotTasks_4580_; lean_object* v___x_4582_; uint8_t v_isShared_4583_; uint8_t v_isSharedCheck_4796_; 
lean_dec_ref(v___f_4148_);
v___x_4571_ = lean_st_ref_take(v_a_3749_);
v_env_4572_ = lean_ctor_get(v___x_4571_, 0);
v_nextMacroScope_4573_ = lean_ctor_get(v___x_4571_, 1);
v_ngen_4574_ = lean_ctor_get(v___x_4571_, 2);
v_auxDeclNGen_4575_ = lean_ctor_get(v___x_4571_, 3);
v_traceState_4576_ = lean_ctor_get(v___x_4571_, 4);
v_recordedDeps_4577_ = lean_ctor_get(v___x_4571_, 6);
v_messages_4578_ = lean_ctor_get(v___x_4571_, 7);
v_infoState_4579_ = lean_ctor_get(v___x_4571_, 8);
v_snapshotTasks_4580_ = lean_ctor_get(v___x_4571_, 9);
v_isSharedCheck_4796_ = !lean_is_exclusive(v___x_4571_);
if (v_isSharedCheck_4796_ == 0)
{
lean_object* v_unused_4797_; 
v_unused_4797_ = lean_ctor_get(v___x_4571_, 5);
lean_dec(v_unused_4797_);
v___x_4582_ = v___x_4571_;
v_isShared_4583_ = v_isSharedCheck_4796_;
goto v_resetjp_4581_;
}
else
{
lean_inc(v_snapshotTasks_4580_);
lean_inc(v_infoState_4579_);
lean_inc(v_messages_4578_);
lean_inc(v_recordedDeps_4577_);
lean_inc(v_traceState_4576_);
lean_inc(v_auxDeclNGen_4575_);
lean_inc(v_ngen_4574_);
lean_inc(v_nextMacroScope_4573_);
lean_inc(v_env_4572_);
lean_dec(v___x_4571_);
v___x_4582_ = lean_box(0);
v_isShared_4583_ = v_isSharedCheck_4796_;
goto v_resetjp_4581_;
}
v_resetjp_4581_:
{
lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4588_; 
lean_inc(v_decl_3746_);
v___x_4584_ = l_Lean_Declaration_getNames(v_decl_3746_);
v___x_4585_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4572_, v___x_4584_);
v___x_4586_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4583_ == 0)
{
lean_ctor_set(v___x_4582_, 5, v___x_4586_);
lean_ctor_set(v___x_4582_, 0, v___x_4585_);
v___x_4588_ = v___x_4582_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4795_; 
v_reuseFailAlloc_4795_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4795_, 0, v___x_4585_);
lean_ctor_set(v_reuseFailAlloc_4795_, 1, v_nextMacroScope_4573_);
lean_ctor_set(v_reuseFailAlloc_4795_, 2, v_ngen_4574_);
lean_ctor_set(v_reuseFailAlloc_4795_, 3, v_auxDeclNGen_4575_);
lean_ctor_set(v_reuseFailAlloc_4795_, 4, v_traceState_4576_);
lean_ctor_set(v_reuseFailAlloc_4795_, 5, v___x_4586_);
lean_ctor_set(v_reuseFailAlloc_4795_, 6, v_recordedDeps_4577_);
lean_ctor_set(v_reuseFailAlloc_4795_, 7, v_messages_4578_);
lean_ctor_set(v_reuseFailAlloc_4795_, 8, v_infoState_4579_);
lean_ctor_set(v_reuseFailAlloc_4795_, 9, v_snapshotTasks_4580_);
v___x_4588_ = v_reuseFailAlloc_4795_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___y_4592_; lean_object* v___y_4593_; lean_object* v___y_4594_; uint8_t v___y_4595_; lean_object* v___y_4596_; lean_object* v___y_4597_; lean_object* v_fst_4654_; lean_object* v_fst_4655_; uint8_t v_snd_4656_; lean_object* v_exportedInfo_x3f_4657_; lean_object* v___y_4658_; lean_object* v___y_4659_; lean_object* v___y_4669_; lean_object* v_exportedInfo_x3f_4670_; lean_object* v___y_4671_; lean_object* v___y_4672_; lean_object* v___y_4677_; lean_object* v___y_4678_; lean_object* v___y_4679_; lean_object* v___y_4680_; uint8_t v___y_4681_; lean_object* v___y_4686_; lean_object* v_toConstantVal_4687_; uint8_t v_safety_4688_; uint8_t v___y_4689_; lean_object* v___y_4690_; lean_object* v___y_4691_; lean_object* v___y_4695_; uint8_t v___y_4696_; lean_object* v___y_4697_; lean_object* v___y_4698_; lean_object* v_defn_4702_; lean_object* v___y_4703_; lean_object* v___y_4704_; 
v___x_4589_ = lean_st_ref_put(v_a_3749_, v___x_4588_);
v___x_4590_ = lean_box(0);
switch(lean_obj_tag(v_decl_3746_))
{
case 2:
{
lean_object* v_val_4726_; lean_object* v_exportedInfo_x3f_4728_; lean_object* v___y_4729_; lean_object* v___y_4730_; lean_object* v___y_4736_; lean_object* v___y_4737_; lean_object* v___x_4742_; 
v_val_4726_ = lean_ctor_get(v_decl_3746_, 0);
v___x_4742_ = lean_st_ref_get(v_a_3749_);
if (v_forceExpose_3747_ == 0)
{
lean_object* v_env_4743_; lean_object* v___x_4744_; uint8_t v_isModule_4745_; 
v_env_4743_ = lean_ctor_get(v___x_4742_, 0);
lean_inc_ref(v_env_4743_);
lean_dec(v___x_4742_);
v___x_4744_ = l_Lean_Environment_header(v_env_4743_);
lean_dec_ref(v_env_4743_);
v_isModule_4745_ = lean_ctor_get_uint8(v___x_4744_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4744_);
if (v_isModule_4745_ == 0)
{
v_exportedInfo_x3f_4728_ = v___x_4590_;
v___y_4729_ = v_a_3748_;
v___y_4730_ = v_a_3749_;
goto v___jp_4727_;
}
else
{
if (v___x_4151_ == 0)
{
v___y_4736_ = v_a_3748_;
v___y_4737_ = v_a_3749_;
goto v___jp_4735_;
}
else
{
lean_object* v_toConstantVal_4746_; lean_object* v_name_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; 
v_toConstantVal_4746_ = lean_ctor_get(v_val_4726_, 0);
v_name_4747_ = lean_ctor_get(v_toConstantVal_4746_, 0);
v___x_4748_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4747_);
v___x_4749_ = l_Lean_MessageData_ofName(v_name_4747_);
v___x_4750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4750_, 0, v___x_4748_);
lean_ctor_set(v___x_4750_, 1, v___x_4749_);
v___x_4751_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4752_, 0, v___x_4750_);
lean_ctor_set(v___x_4752_, 1, v___x_4751_);
v___x_4753_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3924_, v___x_4752_, v_a_3748_, v_a_3749_);
if (lean_obj_tag(v___x_4753_) == 0)
{
lean_dec_ref_known(v___x_4753_, 1);
v___y_4736_ = v_a_3748_;
v___y_4737_ = v_a_3749_;
goto v___jp_4735_;
}
else
{
lean_dec_ref_known(v_decl_3746_, 1);
return v___x_4753_;
}
}
}
}
else
{
lean_dec(v___x_4742_);
v_exportedInfo_x3f_4728_ = v___x_4590_;
v___y_4729_ = v_a_3748_;
v___y_4730_ = v_a_3749_;
goto v___jp_4727_;
}
v___jp_4727_:
{
lean_object* v_toConstantVal_4731_; lean_object* v_name_4732_; lean_object* v___x_4733_; uint8_t v___x_4734_; 
v_toConstantVal_4731_ = lean_ctor_get(v_val_4726_, 0);
v_name_4732_ = lean_ctor_get(v_toConstantVal_4731_, 0);
lean_inc_ref(v_val_4726_);
v___x_4733_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4733_, 0, v_val_4726_);
v___x_4734_ = 1;
lean_inc(v_name_4732_);
v_fst_4654_ = v_name_4732_;
v_fst_4655_ = v___x_4733_;
v_snd_4656_ = v___x_4734_;
v_exportedInfo_x3f_4657_ = v_exportedInfo_x3f_4728_;
v___y_4658_ = v___y_4729_;
v___y_4659_ = v___y_4730_;
goto v___jp_4653_;
}
v___jp_4735_:
{
lean_object* v_toConstantVal_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; 
v_toConstantVal_4738_ = lean_ctor_get(v_val_4726_, 0);
lean_inc_ref(v_toConstantVal_4738_);
v___x_4739_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4739_, 0, v_toConstantVal_4738_);
lean_ctor_set_uint8(v___x_4739_, sizeof(void*)*1, v___x_4430_);
v___x_4740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4740_, 0, v___x_4739_);
v___x_4741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4741_, 0, v___x_4740_);
v_exportedInfo_x3f_4728_ = v___x_4741_;
v___y_4729_ = v___y_4736_;
v___y_4730_ = v___y_4737_;
goto v___jp_4727_;
}
}
case 1:
{
lean_object* v_val_4754_; 
v_val_4754_ = lean_ctor_get(v_decl_3746_, 0);
lean_inc_ref(v_val_4754_);
v_defn_4702_ = v_val_4754_;
v___y_4703_ = v_a_3748_;
v___y_4704_ = v_a_3749_;
goto v___jp_4701_;
}
case 5:
{
lean_object* v_defns_4755_; 
v_defns_4755_ = lean_ctor_get(v_decl_3746_, 0);
if (lean_obj_tag(v_defns_4755_) == 1)
{
lean_object* v_tail_4756_; 
v_tail_4756_ = lean_ctor_get(v_defns_4755_, 1);
if (lean_obj_tag(v_tail_4756_) == 0)
{
lean_object* v_head_4757_; 
v_head_4757_ = lean_ctor_get(v_defns_4755_, 0);
lean_inc(v_head_4757_);
v_defn_4702_ = v_head_4757_;
v___y_4703_ = v_a_3748_;
v___y_4704_ = v_a_3749_;
goto v___jp_4701_;
}
else
{
v___y_3926_ = v_a_3748_;
v_options_3927_ = v_options_3778_;
v_inheritedTraceOptions_3928_ = v_inheritedTraceOptions_3779_;
v___y_3929_ = v_a_3749_;
goto v___jp_3925_;
}
}
else
{
v___y_3926_ = v_a_3748_;
v_options_3927_ = v_options_3778_;
v_inheritedTraceOptions_3928_ = v_inheritedTraceOptions_3779_;
v___y_3929_ = v_a_3749_;
goto v___jp_3925_;
}
}
case 3:
{
lean_object* v_val_4758_; lean_object* v_exportedInfo_x3f_4760_; lean_object* v___y_4761_; lean_object* v___y_4762_; lean_object* v___y_4768_; lean_object* v___y_4769_; lean_object* v___x_4775_; lean_object* v_env_4776_; lean_object* v___x_4777_; 
v_val_4758_ = lean_ctor_get(v_decl_3746_, 0);
v___x_4775_ = lean_st_ref_get(v_a_3749_);
v_env_4776_ = lean_ctor_get(v___x_4775_, 0);
lean_inc_ref(v_env_4776_);
lean_dec(v___x_4775_);
v___x_4777_ = lean_st_ref_get(v_a_3749_);
if (v_forceExpose_3747_ == 0)
{
lean_object* v_env_4778_; lean_object* v___x_4779_; uint8_t v_isModule_4780_; 
v_env_4778_ = lean_ctor_get(v___x_4777_, 0);
lean_inc_ref(v_env_4778_);
lean_dec(v___x_4777_);
v___x_4779_ = l_Lean_Environment_header(v_env_4776_);
lean_dec_ref(v_env_4776_);
v_isModule_4780_ = lean_ctor_get_uint8(v___x_4779_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4779_);
if (v_isModule_4780_ == 0)
{
lean_dec_ref(v_env_4778_);
v_exportedInfo_x3f_4760_ = v___x_4590_;
v___y_4761_ = v_a_3748_;
v___y_4762_ = v_a_3749_;
goto v___jp_4759_;
}
else
{
uint8_t v_isExporting_4781_; 
v_isExporting_4781_ = lean_ctor_get_uint8(v_env_4778_, sizeof(void*)*13);
lean_dec_ref(v_env_4778_);
if (v_isExporting_4781_ == 0)
{
if (v___x_4151_ == 0)
{
v___y_4768_ = v_a_3748_;
v___y_4769_ = v_a_3749_;
goto v___jp_4767_;
}
else
{
lean_object* v_toConstantVal_4782_; lean_object* v_name_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; 
v_toConstantVal_4782_ = lean_ctor_get(v_val_4758_, 0);
v_name_4783_ = lean_ctor_get(v_toConstantVal_4782_, 0);
v___x_4784_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4783_);
v___x_4785_ = l_Lean_MessageData_ofName(v_name_4783_);
v___x_4786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4786_, 0, v___x_4784_);
lean_ctor_set(v___x_4786_, 1, v___x_4785_);
v___x_4787_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4788_, 0, v___x_4786_);
lean_ctor_set(v___x_4788_, 1, v___x_4787_);
v___x_4789_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3924_, v___x_4788_, v_a_3748_, v_a_3749_);
if (lean_obj_tag(v___x_4789_) == 0)
{
lean_dec_ref_known(v___x_4789_, 1);
v___y_4768_ = v_a_3748_;
v___y_4769_ = v_a_3749_;
goto v___jp_4767_;
}
else
{
lean_dec_ref_known(v_decl_3746_, 1);
return v___x_4789_;
}
}
}
else
{
v_exportedInfo_x3f_4760_ = v___x_4590_;
v___y_4761_ = v_a_3748_;
v___y_4762_ = v_a_3749_;
goto v___jp_4759_;
}
}
}
else
{
lean_dec(v___x_4777_);
lean_dec_ref(v_env_4776_);
v_exportedInfo_x3f_4760_ = v___x_4590_;
v___y_4761_ = v_a_3748_;
v___y_4762_ = v_a_3749_;
goto v___jp_4759_;
}
v___jp_4759_:
{
lean_object* v_toConstantVal_4763_; lean_object* v_name_4764_; lean_object* v___x_4765_; uint8_t v___x_4766_; 
v_toConstantVal_4763_ = lean_ctor_get(v_val_4758_, 0);
v_name_4764_ = lean_ctor_get(v_toConstantVal_4763_, 0);
lean_inc_ref(v_val_4758_);
v___x_4765_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4765_, 0, v_val_4758_);
v___x_4766_ = 3;
lean_inc(v_name_4764_);
v_fst_4654_ = v_name_4764_;
v_fst_4655_ = v___x_4765_;
v_snd_4656_ = v___x_4766_;
v_exportedInfo_x3f_4657_ = v_exportedInfo_x3f_4760_;
v___y_4658_ = v___y_4761_;
v___y_4659_ = v___y_4762_;
goto v___jp_4653_;
}
v___jp_4767_:
{
lean_object* v_toConstantVal_4770_; uint8_t v_isUnsafe_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; 
v_toConstantVal_4770_ = lean_ctor_get(v_val_4758_, 0);
v_isUnsafe_4771_ = lean_ctor_get_uint8(v_val_4758_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4770_);
v___x_4772_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4772_, 0, v_toConstantVal_4770_);
lean_ctor_set_uint8(v___x_4772_, sizeof(void*)*1, v_isUnsafe_4771_);
v___x_4773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4773_, 0, v___x_4772_);
v___x_4774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4774_, 0, v___x_4773_);
v_exportedInfo_x3f_4760_ = v___x_4774_;
v___y_4761_ = v___y_4768_;
v___y_4762_ = v___y_4769_;
goto v___jp_4759_;
}
}
case 0:
{
lean_object* v_val_4790_; lean_object* v_toConstantVal_4791_; lean_object* v_name_4792_; lean_object* v___x_4793_; uint8_t v___x_4794_; 
v_val_4790_ = lean_ctor_get(v_decl_3746_, 0);
v_toConstantVal_4791_ = lean_ctor_get(v_val_4790_, 0);
v_name_4792_ = lean_ctor_get(v_toConstantVal_4791_, 0);
lean_inc_ref(v_val_4790_);
v___x_4793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4793_, 0, v_val_4790_);
v___x_4794_ = 2;
lean_inc(v_name_4792_);
v_fst_4654_ = v_name_4792_;
v_fst_4655_ = v___x_4793_;
v_snd_4656_ = v___x_4794_;
v_exportedInfo_x3f_4657_ = v___x_4590_;
v___y_4658_ = v_a_3748_;
v___y_4659_ = v_a_3749_;
goto v___jp_4653_;
}
default: 
{
v___y_3926_ = v_a_3748_;
v_options_3927_ = v_options_3778_;
v_inheritedTraceOptions_3928_ = v_inheritedTraceOptions_3779_;
v___y_3929_ = v_a_3749_;
goto v___jp_3925_;
}
}
v___jp_4591_:
{
lean_object* v___x_4598_; uint8_t v___x_4599_; 
lean_inc(v_decl_3746_);
v___x_4598_ = l_Lean_Declaration_getTopLevelNames(v_decl_3746_);
v___x_4599_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_4598_);
lean_dec(v___x_4598_);
if (v___x_4599_ == 0)
{
if (lean_obj_tag(v___y_4593_) == 0)
{
lean_object* v_toCold_4600_; lean_object* v_options_4601_; uint8_t v_hasTrace_4602_; 
v_toCold_4600_ = lean_ctor_get(v___y_4596_, 0);
v_options_4601_ = lean_ctor_get(v_toCold_4600_, 2);
v_hasTrace_4602_ = lean_ctor_get_uint8(v_options_4601_, sizeof(void*)*1);
if (v_hasTrace_4602_ == 0)
{
v___y_4565_ = v___y_4592_;
v___y_4566_ = v___y_4595_;
v___y_4567_ = v___y_4594_;
v___y_4568_ = v___y_4596_;
v___y_4569_ = v___y_4597_;
goto v___jp_4564_;
}
else
{
lean_object* v_inheritedTraceOptions_4603_; uint8_t v___x_4604_; 
v_inheritedTraceOptions_4603_ = lean_ctor_get(v_toCold_4600_, 11);
v___x_4604_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4603_, v_options_4601_, v___x_4150_);
if (v___x_4604_ == 0)
{
v___y_4565_ = v___y_4592_;
v___y_4566_ = v___y_4595_;
v___y_4567_ = v___y_4594_;
v___y_4568_ = v___y_4596_;
v___y_4569_ = v___y_4597_;
goto v___jp_4564_;
}
else
{
lean_object* v___x_4605_; lean_object* v___x_4606_; 
v___x_4605_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_4606_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3924_, v___x_4605_, v___y_4596_, v___y_4597_);
if (lean_obj_tag(v___x_4606_) == 0)
{
lean_dec_ref_known(v___x_4606_, 1);
v___y_4565_ = v___y_4592_;
v___y_4566_ = v___y_4595_;
v___y_4567_ = v___y_4594_;
v___y_4568_ = v___y_4596_;
v___y_4569_ = v___y_4597_;
goto v___jp_4564_;
}
else
{
lean_dec_ref(v___y_4594_);
lean_dec(v___y_4592_);
lean_dec(v_decl_3746_);
return v___x_4606_;
}
}
}
}
else
{
lean_object* v___x_4607_; lean_object* v_env_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; uint8_t v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; 
v___x_4607_ = lean_st_ref_get(v___y_4597_);
v_env_4608_ = lean_ctor_get(v___x_4607_, 0);
lean_inc_ref(v_env_4608_);
lean_dec(v___x_4607_);
v___x_4609_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4610_ = lean_box(1);
v___x_4611_ = 0;
v___x_4612_ = lean_box(v___x_3923_);
lean_inc(v___y_4592_);
v___x_4613_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_4612_, v___x_4609_, v_env_4608_, v___y_4592_, v___x_4610_, v___x_4611_);
if (lean_obj_tag(v___x_4613_) == 0)
{
lean_object* v___x_4614_; lean_object* v_env_4615_; lean_object* v_nextMacroScope_4616_; lean_object* v_ngen_4617_; lean_object* v_auxDeclNGen_4618_; lean_object* v_traceState_4619_; lean_object* v_recordedDeps_4620_; lean_object* v_messages_4621_; lean_object* v_infoState_4622_; lean_object* v_snapshotTasks_4623_; lean_object* v___x_4625_; uint8_t v_isShared_4626_; uint8_t v_isSharedCheck_4633_; 
v___x_4614_ = lean_st_ref_take(v___y_4597_);
v_env_4615_ = lean_ctor_get(v___x_4614_, 0);
v_nextMacroScope_4616_ = lean_ctor_get(v___x_4614_, 1);
v_ngen_4617_ = lean_ctor_get(v___x_4614_, 2);
v_auxDeclNGen_4618_ = lean_ctor_get(v___x_4614_, 3);
v_traceState_4619_ = lean_ctor_get(v___x_4614_, 4);
v_recordedDeps_4620_ = lean_ctor_get(v___x_4614_, 6);
v_messages_4621_ = lean_ctor_get(v___x_4614_, 7);
v_infoState_4622_ = lean_ctor_get(v___x_4614_, 8);
v_snapshotTasks_4623_ = lean_ctor_get(v___x_4614_, 9);
v_isSharedCheck_4633_ = !lean_is_exclusive(v___x_4614_);
if (v_isSharedCheck_4633_ == 0)
{
lean_object* v_unused_4634_; 
v_unused_4634_ = lean_ctor_get(v___x_4614_, 5);
lean_dec(v_unused_4634_);
v___x_4625_ = v___x_4614_;
v_isShared_4626_ = v_isSharedCheck_4633_;
goto v_resetjp_4624_;
}
else
{
lean_inc(v_snapshotTasks_4623_);
lean_inc(v_infoState_4622_);
lean_inc(v_messages_4621_);
lean_inc(v_recordedDeps_4620_);
lean_inc(v_traceState_4619_);
lean_inc(v_auxDeclNGen_4618_);
lean_inc(v_ngen_4617_);
lean_inc(v_nextMacroScope_4616_);
lean_inc(v_env_4615_);
lean_dec(v___x_4614_);
v___x_4625_ = lean_box(0);
v_isShared_4626_ = v_isSharedCheck_4633_;
goto v_resetjp_4624_;
}
v_resetjp_4624_:
{
lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4630_; 
v___x_4627_ = lean_box(v___y_4595_);
lean_inc(v___y_4592_);
v___x_4628_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4609_, v_env_4615_, v___y_4592_, v___x_4627_, v___x_4599_);
if (v_isShared_4626_ == 0)
{
lean_ctor_set(v___x_4625_, 5, v___x_4586_);
lean_ctor_set(v___x_4625_, 0, v___x_4628_);
v___x_4630_ = v___x_4625_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4632_; 
v_reuseFailAlloc_4632_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4632_, 0, v___x_4628_);
lean_ctor_set(v_reuseFailAlloc_4632_, 1, v_nextMacroScope_4616_);
lean_ctor_set(v_reuseFailAlloc_4632_, 2, v_ngen_4617_);
lean_ctor_set(v_reuseFailAlloc_4632_, 3, v_auxDeclNGen_4618_);
lean_ctor_set(v_reuseFailAlloc_4632_, 4, v_traceState_4619_);
lean_ctor_set(v_reuseFailAlloc_4632_, 5, v___x_4586_);
lean_ctor_set(v_reuseFailAlloc_4632_, 6, v_recordedDeps_4620_);
lean_ctor_set(v_reuseFailAlloc_4632_, 7, v_messages_4621_);
lean_ctor_set(v_reuseFailAlloc_4632_, 8, v_infoState_4622_);
lean_ctor_set(v_reuseFailAlloc_4632_, 9, v_snapshotTasks_4623_);
v___x_4630_ = v_reuseFailAlloc_4632_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
lean_object* v___x_4631_; 
v___x_4631_ = lean_st_ref_put(v___y_4597_, v___x_4630_);
v___y_4543_ = v___y_4592_;
v___y_4544_ = v___y_4595_;
v___y_4545_ = v___y_4594_;
v_exportedInfo_x3f_4546_ = v___y_4593_;
v___y_4547_ = v___y_4596_;
v___y_4548_ = v___y_4597_;
goto v___jp_4542_;
}
}
}
else
{
lean_dec_ref_known(v___x_4613_, 1);
v___y_4543_ = v___y_4592_;
v___y_4544_ = v___y_4595_;
v___y_4545_ = v___y_4594_;
v_exportedInfo_x3f_4546_ = v___y_4593_;
v___y_4547_ = v___y_4596_;
v___y_4548_ = v___y_4597_;
goto v___jp_4542_;
}
}
}
else
{
lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v_a_4637_; uint8_t v___x_4638_; 
lean_dec(v___y_4593_);
v___x_4635_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4636_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4635_, v___y_4596_);
v_a_4637_ = lean_ctor_get(v___x_4636_, 0);
lean_inc(v_a_4637_);
lean_dec_ref(v___x_4636_);
v___x_4638_ = lean_unbox(v_a_4637_);
lean_dec(v_a_4637_);
if (v___x_4638_ == 0)
{
lean_object* v_toCold_4639_; lean_object* v_options_4640_; uint8_t v_hasTrace_4641_; 
v_toCold_4639_ = lean_ctor_get(v___y_4596_, 0);
v_options_4640_ = lean_ctor_get(v_toCold_4639_, 2);
v_hasTrace_4641_ = lean_ctor_get_uint8(v_options_4640_, sizeof(void*)*1);
if (v_hasTrace_4641_ == 0)
{
v___y_4543_ = v___y_4592_;
v___y_4544_ = v___y_4595_;
v___y_4545_ = v___y_4594_;
v_exportedInfo_x3f_4546_ = v___x_4590_;
v___y_4547_ = v___y_4596_;
v___y_4548_ = v___y_4597_;
goto v___jp_4542_;
}
else
{
lean_object* v_inheritedTraceOptions_4642_; uint8_t v___x_4643_; 
v_inheritedTraceOptions_4642_ = lean_ctor_get(v_toCold_4639_, 11);
v___x_4643_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4642_, v_options_4640_, v___x_4150_);
if (v___x_4643_ == 0)
{
v___y_4543_ = v___y_4592_;
v___y_4544_ = v___y_4595_;
v___y_4545_ = v___y_4594_;
v_exportedInfo_x3f_4546_ = v___x_4590_;
v___y_4547_ = v___y_4596_;
v___y_4548_ = v___y_4597_;
goto v___jp_4542_;
}
else
{
lean_object* v___x_4644_; lean_object* v___x_4645_; 
v___x_4644_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_4645_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3924_, v___x_4644_, v___y_4596_, v___y_4597_);
if (lean_obj_tag(v___x_4645_) == 0)
{
lean_dec_ref_known(v___x_4645_, 1);
v___y_4543_ = v___y_4592_;
v___y_4544_ = v___y_4595_;
v___y_4545_ = v___y_4594_;
v_exportedInfo_x3f_4546_ = v___x_4590_;
v___y_4547_ = v___y_4596_;
v___y_4548_ = v___y_4597_;
goto v___jp_4542_;
}
else
{
lean_dec_ref(v___y_4594_);
lean_dec(v___y_4592_);
lean_dec(v_decl_3746_);
return v___x_4645_;
}
}
}
}
else
{
lean_object* v_toCold_4646_; lean_object* v_options_4647_; uint8_t v_hasTrace_4648_; 
v_toCold_4646_ = lean_ctor_get(v___y_4596_, 0);
v_options_4647_ = lean_ctor_get(v_toCold_4646_, 2);
v_hasTrace_4648_ = lean_ctor_get_uint8(v_options_4647_, sizeof(void*)*1);
if (v_hasTrace_4648_ == 0)
{
v___y_4558_ = v___y_4592_;
v___y_4559_ = v___y_4595_;
v___y_4560_ = v___y_4594_;
v___y_4561_ = v___y_4596_;
v___y_4562_ = v___y_4597_;
goto v___jp_4557_;
}
else
{
lean_object* v_inheritedTraceOptions_4649_; uint8_t v___x_4650_; 
v_inheritedTraceOptions_4649_ = lean_ctor_get(v_toCold_4646_, 11);
v___x_4650_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4649_, v_options_4647_, v___x_4150_);
if (v___x_4650_ == 0)
{
v___y_4558_ = v___y_4592_;
v___y_4559_ = v___y_4595_;
v___y_4560_ = v___y_4594_;
v___y_4561_ = v___y_4596_;
v___y_4562_ = v___y_4597_;
goto v___jp_4557_;
}
else
{
lean_object* v___x_4651_; lean_object* v___x_4652_; 
v___x_4651_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_4652_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3924_, v___x_4651_, v___y_4596_, v___y_4597_);
if (lean_obj_tag(v___x_4652_) == 0)
{
lean_dec_ref_known(v___x_4652_, 1);
v___y_4558_ = v___y_4592_;
v___y_4559_ = v___y_4595_;
v___y_4560_ = v___y_4594_;
v___y_4561_ = v___y_4596_;
v___y_4562_ = v___y_4597_;
goto v___jp_4557_;
}
else
{
lean_dec_ref(v___y_4594_);
lean_dec(v___y_4592_);
lean_dec(v_decl_3746_);
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
v___y_4592_ = v_fst_4654_;
v___y_4593_ = v_exportedInfo_x3f_4657_;
v___y_4594_ = v_fst_4655_;
v___y_4595_ = v_snd_4656_;
v___y_4596_ = v___y_4658_;
v___y_4597_ = v___y_4659_;
goto v___jp_4591_;
}
else
{
lean_object* v___x_4663_; lean_object* v_env_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; 
lean_dec(v_exportedInfo_x3f_4657_);
lean_dec_ref(v_fst_4655_);
lean_dec(v_decl_3746_);
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
lean_object* v_toConstantVal_4673_; lean_object* v_name_4674_; lean_object* v___x_4675_; 
v_toConstantVal_4673_ = lean_ctor_get(v___y_4669_, 0);
v_name_4674_ = lean_ctor_get(v_toConstantVal_4673_, 0);
lean_inc(v_name_4674_);
v___x_4675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4675_, 0, v___y_4669_);
v_fst_4654_ = v_name_4674_;
v_fst_4655_ = v___x_4675_;
v_snd_4656_ = v___x_3923_;
v_exportedInfo_x3f_4657_ = v_exportedInfo_x3f_4670_;
v___y_4658_ = v___y_4671_;
v___y_4659_ = v___y_4672_;
goto v___jp_4653_;
}
v___jp_4676_:
{
lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; 
v___x_4682_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4682_, 0, v___y_4679_);
lean_ctor_set_uint8(v___x_4682_, sizeof(void*)*1, v___y_4681_);
v___x_4683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4683_, 0, v___x_4682_);
v___x_4684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4684_, 0, v___x_4683_);
v___y_4669_ = v___y_4678_;
v_exportedInfo_x3f_4670_ = v___x_4684_;
v___y_4671_ = v___y_4677_;
v___y_4672_ = v___y_4680_;
goto v___jp_4668_;
}
v___jp_4685_:
{
uint8_t v___x_4692_; uint8_t v___x_4693_; 
v___x_4692_ = 1;
v___x_4693_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4688_, v___x_4692_);
if (v___x_4693_ == 0)
{
v___y_4677_ = v___y_4690_;
v___y_4678_ = v___y_4686_;
v___y_4679_ = v_toConstantVal_4687_;
v___y_4680_ = v___y_4691_;
v___y_4681_ = v___y_4689_;
goto v___jp_4676_;
}
else
{
v___y_4677_ = v___y_4690_;
v___y_4678_ = v___y_4686_;
v___y_4679_ = v_toConstantVal_4687_;
v___y_4680_ = v___y_4691_;
v___y_4681_ = v___x_4430_;
goto v___jp_4676_;
}
}
v___jp_4694_:
{
lean_object* v_toConstantVal_4699_; uint8_t v_safety_4700_; 
v_toConstantVal_4699_ = lean_ctor_get(v___y_4695_, 0);
lean_inc_ref(v_toConstantVal_4699_);
v_safety_4700_ = lean_ctor_get_uint8(v___y_4695_, sizeof(void*)*4);
v___y_4686_ = v___y_4695_;
v_toConstantVal_4687_ = v_toConstantVal_4699_;
v_safety_4688_ = v_safety_4700_;
v___y_4689_ = v___y_4696_;
v___y_4690_ = v___y_4697_;
v___y_4691_ = v___y_4698_;
goto v___jp_4685_;
}
v___jp_4701_:
{
lean_object* v___x_4705_; lean_object* v_env_4706_; lean_object* v___x_4707_; 
v___x_4705_ = lean_st_ref_get(v___y_4704_);
v_env_4706_ = lean_ctor_get(v___x_4705_, 0);
lean_inc_ref(v_env_4706_);
lean_dec(v___x_4705_);
v___x_4707_ = lean_st_ref_get(v___y_4704_);
if (v_forceExpose_3747_ == 0)
{
lean_object* v_env_4708_; lean_object* v___x_4709_; uint8_t v_isModule_4710_; 
v_env_4708_ = lean_ctor_get(v___x_4707_, 0);
lean_inc_ref(v_env_4708_);
lean_dec(v___x_4707_);
v___x_4709_ = l_Lean_Environment_header(v_env_4706_);
lean_dec_ref(v_env_4706_);
v_isModule_4710_ = lean_ctor_get_uint8(v___x_4709_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4709_);
if (v_isModule_4710_ == 0)
{
lean_dec_ref(v_env_4708_);
v___y_4669_ = v_defn_4702_;
v_exportedInfo_x3f_4670_ = v___x_4590_;
v___y_4671_ = v___y_4703_;
v___y_4672_ = v___y_4704_;
goto v___jp_4668_;
}
else
{
uint8_t v_isExporting_4711_; 
v_isExporting_4711_ = lean_ctor_get_uint8(v_env_4708_, sizeof(void*)*13);
lean_dec_ref(v_env_4708_);
if (v_isExporting_4711_ == 0)
{
lean_object* v_toCold_4712_; lean_object* v_options_4713_; uint8_t v_hasTrace_4714_; 
v_toCold_4712_ = lean_ctor_get(v___y_4703_, 0);
v_options_4713_ = lean_ctor_get(v_toCold_4712_, 2);
v_hasTrace_4714_ = lean_ctor_get_uint8(v_options_4713_, sizeof(void*)*1);
if (v_hasTrace_4714_ == 0)
{
v___y_4695_ = v_defn_4702_;
v___y_4696_ = v_isModule_4710_;
v___y_4697_ = v___y_4703_;
v___y_4698_ = v___y_4704_;
goto v___jp_4694_;
}
else
{
lean_object* v_inheritedTraceOptions_4715_; uint8_t v___x_4716_; 
v_inheritedTraceOptions_4715_ = lean_ctor_get(v_toCold_4712_, 11);
v___x_4716_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4715_, v_options_4713_, v___x_4150_);
if (v___x_4716_ == 0)
{
v___y_4695_ = v_defn_4702_;
v___y_4696_ = v_isModule_4710_;
v___y_4697_ = v___y_4703_;
v___y_4698_ = v___y_4704_;
goto v___jp_4694_;
}
else
{
lean_object* v_toConstantVal_4717_; uint8_t v_safety_4718_; lean_object* v_name_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; 
v_toConstantVal_4717_ = lean_ctor_get(v_defn_4702_, 0);
lean_inc_ref(v_toConstantVal_4717_);
v_safety_4718_ = lean_ctor_get_uint8(v_defn_4702_, sizeof(void*)*4);
v_name_4719_ = lean_ctor_get(v_toConstantVal_4717_, 0);
v___x_4720_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_4719_);
v___x_4721_ = l_Lean_MessageData_ofName(v_name_4719_);
v___x_4722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4722_, 0, v___x_4720_);
lean_ctor_set(v___x_4722_, 1, v___x_4721_);
v___x_4723_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4724_, 0, v___x_4722_);
lean_ctor_set(v___x_4724_, 1, v___x_4723_);
v___x_4725_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3924_, v___x_4724_, v___y_4703_, v___y_4704_);
if (lean_obj_tag(v___x_4725_) == 0)
{
lean_dec_ref_known(v___x_4725_, 1);
v___y_4686_ = v_defn_4702_;
v_toConstantVal_4687_ = v_toConstantVal_4717_;
v_safety_4688_ = v_safety_4718_;
v___y_4689_ = v_isModule_4710_;
v___y_4690_ = v___y_4703_;
v___y_4691_ = v___y_4704_;
goto v___jp_4685_;
}
else
{
lean_dec_ref(v_toConstantVal_4717_);
lean_dec_ref(v_defn_4702_);
lean_dec(v_decl_3746_);
return v___x_4725_;
}
}
}
}
else
{
v___y_4669_ = v_defn_4702_;
v_exportedInfo_x3f_4670_ = v___x_4590_;
v___y_4671_ = v___y_4703_;
v___y_4672_ = v___y_4704_;
goto v___jp_4668_;
}
}
}
else
{
lean_dec(v___x_4707_);
lean_dec_ref(v_env_4706_);
v___y_4669_ = v_defn_4702_;
v_exportedInfo_x3f_4670_ = v___x_4590_;
v___y_4671_ = v___y_4703_;
v___y_4672_ = v___y_4704_;
goto v___jp_4668_;
}
}
}
}
}
else
{
goto v___jp_4243_;
}
v___jp_4431_:
{
lean_object* v___x_4443_; 
lean_inc_ref(v___y_4441_);
v___x_4443_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_4432_, v___y_4441_, v___y_4434_, v___y_4442_);
if (lean_obj_tag(v___x_4443_) == 0)
{
lean_object* v___x_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4499_; 
lean_dec_ref_known(v___x_4443_, 1);
lean_dec(v___y_4436_);
lean_inc_ref(v___y_4437_);
v___x_4444_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4437_, v___y_4439_);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4499_ == 0)
{
lean_object* v_unused_4500_; 
v_unused_4500_ = lean_ctor_get(v___x_4444_, 0);
lean_dec(v_unused_4500_);
v___x_4446_ = v___x_4444_;
v_isShared_4447_ = v_isSharedCheck_4499_;
goto v_resetjp_4445_;
}
else
{
lean_dec(v___x_4444_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4499_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v___x_4448_; lean_object* v___x_4449_; uint8_t v___x_4450_; 
v___x_4448_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4433_);
v___x_4449_ = l_Lean_Elab_async;
v___x_4450_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_4448_, v___x_4449_);
lean_dec_ref(v___x_4448_);
if (v___x_4450_ == 0)
{
lean_object* v___x_4451_; lean_object* v_r_4452_; 
lean_del_object(v___x_4446_);
lean_dec_ref(v___y_4440_);
lean_dec_ref(v___y_4435_);
v___x_4451_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4441_, v___y_4439_);
lean_dec_ref(v___x_4451_);
v_r_4452_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3746_, v___y_4433_, v___y_4439_);
if (lean_obj_tag(v_r_4452_) == 0)
{
lean_object* v_a_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4471_; 
v_a_4453_ = lean_ctor_get(v_r_4452_, 0);
v_isSharedCheck_4471_ = !lean_is_exclusive(v_r_4452_);
if (v_isSharedCheck_4471_ == 0)
{
v___x_4455_ = v_r_4452_;
v_isShared_4456_ = v_isSharedCheck_4471_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_a_4453_);
lean_dec(v_r_4452_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4471_;
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
lean_object* v_reuseFailAlloc_4470_; 
v_reuseFailAlloc_4470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4470_, 0, v_a_4453_);
v___x_4458_ = v_reuseFailAlloc_4470_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
lean_object* v___x_4459_; 
v___x_4459_ = lean_apply_2(v___y_4438_, v___x_4458_, lean_box(0));
if (lean_obj_tag(v___x_4459_) == 0)
{
lean_object* v___x_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4467_; 
lean_dec_ref_known(v___x_4459_, 1);
v___x_4460_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4437_, v___y_4439_);
v_isSharedCheck_4467_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4467_ == 0)
{
lean_object* v_unused_4468_; 
v_unused_4468_ = lean_ctor_get(v___x_4460_, 0);
lean_dec(v_unused_4468_);
v___x_4462_ = v___x_4460_;
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
else
{
lean_dec(v___x_4460_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4465_; 
if (v_isShared_4463_ == 0)
{
lean_ctor_set(v___x_4462_, 0, v_a_4453_);
v___x_4465_ = v___x_4462_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v_a_4453_);
v___x_4465_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
return v___x_4465_;
}
}
}
else
{
lean_object* v_a_4469_; 
lean_dec(v_a_4453_);
v_a_4469_ = lean_ctor_get(v___x_4459_, 0);
lean_inc(v_a_4469_);
lean_dec_ref_known(v___x_4459_, 1);
v___y_3752_ = v___y_4437_;
v___y_3753_ = v___y_4439_;
v_a_3754_ = v_a_4469_;
goto v___jp_3751_;
}
}
}
}
else
{
lean_object* v_a_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; 
v_a_4472_ = lean_ctor_get(v_r_4452_, 0);
lean_inc(v_a_4472_);
lean_dec_ref_known(v_r_4452_, 1);
v___x_4473_ = lean_box(0);
v___x_4474_ = lean_apply_2(v___y_4438_, v___x_4473_, lean_box(0));
if (lean_obj_tag(v___x_4474_) == 0)
{
lean_dec_ref_known(v___x_4474_, 1);
v___y_3752_ = v___y_4437_;
v___y_3753_ = v___y_4439_;
v_a_3754_ = v_a_4472_;
goto v___jp_3751_;
}
else
{
lean_object* v_a_4475_; 
lean_dec(v_a_4472_);
v_a_4475_ = lean_ctor_get(v___x_4474_, 0);
lean_inc(v_a_4475_);
lean_dec_ref_known(v___x_4474_, 1);
v___y_3752_ = v___y_4437_;
v___y_3753_ = v___y_4439_;
v_a_3754_ = v_a_4475_;
goto v___jp_3751_;
}
}
}
else
{
lean_object* v___x_4476_; lean_object* v___x_4478_; 
lean_dec_ref(v___y_4441_);
lean_dec_ref(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec(v_decl_3746_);
v___x_4476_ = l_IO_CancelToken_new();
if (v_isShared_4447_ == 0)
{
lean_ctor_set_tag(v___x_4446_, 1);
lean_ctor_set(v___x_4446_, 0, v___x_4476_);
v___x_4478_ = v___x_4446_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v___x_4476_);
v___x_4478_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; 
v___x_4479_ = lean_unsigned_to_nat(0u);
v___x_4480_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_4481_ = l_Lean_Name_toString(v___x_4480_, v_hasTrace_3780_);
lean_inc_ref(v___x_4478_);
v___x_4482_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_4435_, v___x_4478_, v___x_4481_, v___y_4433_, v___y_4439_);
if (lean_obj_tag(v___x_4482_) == 0)
{
lean_object* v_a_4483_; lean_object* v_checked_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; 
v_a_4483_ = lean_ctor_get(v___x_4482_, 0);
lean_inc(v_a_4483_);
lean_dec_ref_known(v___x_4482_, 1);
v_checked_4484_ = lean_ctor_get(v___y_4440_, 2);
lean_inc_ref(v_checked_4484_);
lean_dec_ref(v___y_4440_);
v___x_4485_ = lean_io_map_task(v_a_4483_, v_checked_4484_, v___x_4479_, v___x_4430_);
v___x_4486_ = lean_box(0);
v___x_4487_ = lean_box(2);
v___x_4488_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4488_, 0, v___x_4486_);
lean_ctor_set(v___x_4488_, 1, v___x_4487_);
lean_ctor_set(v___x_4488_, 2, v___x_4478_);
lean_ctor_set(v___x_4488_, 3, v___x_4485_);
v___x_4489_ = l_Lean_Core_logSnapshotTask___redArg(v___x_4488_, v___y_4439_);
return v___x_4489_;
}
else
{
lean_object* v_a_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4497_; 
lean_dec_ref(v___x_4478_);
lean_dec_ref(v___y_4440_);
v_a_4490_ = lean_ctor_get(v___x_4482_, 0);
v_isSharedCheck_4497_ = !lean_is_exclusive(v___x_4482_);
if (v_isSharedCheck_4497_ == 0)
{
v___x_4492_ = v___x_4482_;
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_a_4490_);
lean_dec(v___x_4482_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4495_; 
if (v_isShared_4493_ == 0)
{
v___x_4495_ = v___x_4492_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_a_4490_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4512_; 
lean_dec_ref(v___y_4441_);
lean_dec_ref(v___y_4440_);
lean_dec_ref(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec_ref(v___y_4435_);
lean_dec(v_decl_3746_);
v_a_4501_ = lean_ctor_get(v___x_4443_, 0);
v_isSharedCheck_4512_ = !lean_is_exclusive(v___x_4443_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4503_ = v___x_4443_;
v_isShared_4504_ = v_isSharedCheck_4512_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_a_4501_);
lean_dec(v___x_4443_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4512_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4510_; 
v___x_4505_ = lean_io_error_to_string(v_a_4501_);
v___x_4506_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4506_, 0, v___x_4505_);
v___x_4507_ = l_Lean_MessageData_ofFormat(v___x_4506_);
v___x_4508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4508_, 0, v___y_4436_);
lean_ctor_set(v___x_4508_, 1, v___x_4507_);
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 0, v___x_4508_);
v___x_4510_ = v___x_4503_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v___x_4508_);
v___x_4510_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
return v___x_4510_;
}
}
}
}
v___jp_4513_:
{
lean_object* v_ref_4522_; lean_object* v___x_4523_; 
v_ref_4522_ = lean_ctor_get(v___y_4516_, 2);
lean_inc_ref(v___y_4520_);
v___x_4523_ = l_Lean_Environment_addConstAsync(v___y_4520_, v___y_4515_, v___y_4518_, v___y_4521_, v___x_4430_, v_hasTrace_3780_);
if (lean_obj_tag(v___x_4523_) == 0)
{
lean_object* v_a_4524_; lean_object* v_mainEnv_4525_; lean_object* v_asyncEnv_4526_; lean_object* v___f_4527_; lean_object* v___f_4528_; lean_object* v___x_4529_; 
v_a_4524_ = lean_ctor_get(v___x_4523_, 0);
lean_inc_n(v_a_4524_, 3);
lean_dec_ref_known(v___x_4523_, 1);
v_mainEnv_4525_ = lean_ctor_get(v_a_4524_, 0);
lean_inc_ref(v_mainEnv_4525_);
v_asyncEnv_4526_ = lean_ctor_get(v_a_4524_, 1);
lean_inc_ref_n(v_asyncEnv_4526_, 2);
lean_inc(v_ref_4522_);
lean_inc(v___y_4517_);
v___f_4527_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4527_, 0, v___y_4517_);
lean_closure_set(v___f_4527_, 1, v_a_4524_);
lean_closure_set(v___f_4527_, 2, v_ref_4522_);
lean_inc(v_decl_3746_);
v___f_4528_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4528_, 0, v_a_4524_);
lean_closure_set(v___f_4528_, 1, v_asyncEnv_4526_);
lean_closure_set(v___f_4528_, 2, v_decl_3746_);
v___x_4529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4529_, 0, v___y_4514_);
if (lean_obj_tag(v___y_4519_) == 0)
{
lean_inc(v_ref_4522_);
lean_inc_ref(v___x_4529_);
v___y_4432_ = v_a_4524_;
v___y_4433_ = v___y_4516_;
v___y_4434_ = v___x_4529_;
v___y_4435_ = v___f_4528_;
v___y_4436_ = v_ref_4522_;
v___y_4437_ = v_mainEnv_4525_;
v___y_4438_ = v___f_4527_;
v___y_4439_ = v___y_4517_;
v___y_4440_ = v___y_4520_;
v___y_4441_ = v_asyncEnv_4526_;
v___y_4442_ = v___x_4529_;
goto v___jp_4431_;
}
else
{
lean_inc(v_ref_4522_);
v___y_4432_ = v_a_4524_;
v___y_4433_ = v___y_4516_;
v___y_4434_ = v___x_4529_;
v___y_4435_ = v___f_4528_;
v___y_4436_ = v_ref_4522_;
v___y_4437_ = v_mainEnv_4525_;
v___y_4438_ = v___f_4527_;
v___y_4439_ = v___y_4517_;
v___y_4440_ = v___y_4520_;
v___y_4441_ = v_asyncEnv_4526_;
v___y_4442_ = v___y_4519_;
goto v___jp_4431_;
}
}
else
{
lean_object* v_a_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4541_; 
lean_dec_ref(v___y_4520_);
lean_dec(v___y_4519_);
lean_dec_ref(v___y_4514_);
lean_dec(v_decl_3746_);
v_a_4530_ = lean_ctor_get(v___x_4523_, 0);
v_isSharedCheck_4541_ = !lean_is_exclusive(v___x_4523_);
if (v_isSharedCheck_4541_ == 0)
{
v___x_4532_ = v___x_4523_;
v_isShared_4533_ = v_isSharedCheck_4541_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_a_4530_);
lean_dec(v___x_4523_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4541_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4539_; 
v___x_4534_ = lean_io_error_to_string(v_a_4530_);
v___x_4535_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4535_, 0, v___x_4534_);
v___x_4536_ = l_Lean_MessageData_ofFormat(v___x_4535_);
lean_inc(v_ref_4522_);
v___x_4537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4537_, 0, v_ref_4522_);
lean_ctor_set(v___x_4537_, 1, v___x_4536_);
if (v_isShared_4533_ == 0)
{
lean_ctor_set(v___x_4532_, 0, v___x_4537_);
v___x_4539_ = v___x_4532_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4540_; 
v_reuseFailAlloc_4540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4540_, 0, v___x_4537_);
v___x_4539_ = v_reuseFailAlloc_4540_;
goto v_reusejp_4538_;
}
v_reusejp_4538_:
{
return v___x_4539_;
}
}
}
}
v___jp_4542_:
{
lean_object* v___x_4549_; 
v___x_4549_ = lean_st_ref_get(v___y_4548_);
if (lean_obj_tag(v_exportedInfo_x3f_4546_) == 0)
{
lean_object* v_env_4550_; lean_object* v___x_4551_; 
v_env_4550_ = lean_ctor_get(v___x_4549_, 0);
lean_inc_ref(v_env_4550_);
lean_dec(v___x_4549_);
v___x_4551_ = lean_box(0);
v___y_4514_ = v___y_4545_;
v___y_4515_ = v___y_4543_;
v___y_4516_ = v___y_4547_;
v___y_4517_ = v___y_4548_;
v___y_4518_ = v___y_4544_;
v___y_4519_ = v_exportedInfo_x3f_4546_;
v___y_4520_ = v_env_4550_;
v___y_4521_ = v___x_4551_;
goto v___jp_4513_;
}
else
{
lean_object* v_env_4552_; lean_object* v_val_4553_; uint8_t v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; 
v_env_4552_ = lean_ctor_get(v___x_4549_, 0);
lean_inc_ref(v_env_4552_);
lean_dec(v___x_4549_);
v_val_4553_ = lean_ctor_get(v_exportedInfo_x3f_4546_, 0);
v___x_4554_ = l_Lean_ConstantKind_ofConstantInfo(v_val_4553_);
v___x_4555_ = lean_box(v___x_4554_);
v___x_4556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4556_, 0, v___x_4555_);
v___y_4514_ = v___y_4545_;
v___y_4515_ = v___y_4543_;
v___y_4516_ = v___y_4547_;
v___y_4517_ = v___y_4548_;
v___y_4518_ = v___y_4544_;
v___y_4519_ = v_exportedInfo_x3f_4546_;
v___y_4520_ = v_env_4552_;
v___y_4521_ = v___x_4556_;
goto v___jp_4513_;
}
}
v___jp_4557_:
{
lean_object* v___x_4563_; 
lean_inc_ref(v___y_4560_);
v___x_4563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4563_, 0, v___y_4560_);
v___y_4543_ = v___y_4558_;
v___y_4544_ = v___y_4559_;
v___y_4545_ = v___y_4560_;
v_exportedInfo_x3f_4546_ = v___x_4563_;
v___y_4547_ = v___y_4561_;
v___y_4548_ = v___y_4562_;
goto v___jp_4542_;
}
v___jp_4564_:
{
lean_object* v___x_4570_; 
lean_inc_ref(v___y_4567_);
v___x_4570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4570_, 0, v___y_4567_);
v___y_4543_ = v___y_4565_;
v___y_4544_ = v___y_4566_;
v___y_4545_ = v___y_4567_;
v_exportedInfo_x3f_4546_ = v___x_4570_;
v___y_4547_ = v___y_4568_;
v___y_4548_ = v___y_4569_;
goto v___jp_4542_;
}
}
else
{
goto v___jp_4243_;
}
v___jp_4152_:
{
lean_object* v___x_4156_; double v___x_4157_; double v___x_4158_; double v___x_4159_; double v___x_4160_; double v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; 
v___x_4156_ = lean_io_mono_nanos_now();
v___x_4157_ = lean_float_of_nat(v___y_4153_);
v___x_4158_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_4159_ = lean_float_div(v___x_4157_, v___x_4158_);
v___x_4160_ = lean_float_of_nat(v___x_4156_);
v___x_4161_ = lean_float_div(v___x_4160_, v___x_4158_);
v___x_4162_ = lean_box_float(v___x_4159_);
v___x_4163_ = lean_box_float(v___x_4161_);
v___x_4164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4162_);
lean_ctor_set(v___x_4164_, 1, v___x_4163_);
v___x_4165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4165_, 0, v_a_4155_);
lean_ctor_set(v___x_4165_, 1, v___x_4164_);
v___x_4166_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3924_, v_hasTrace_3780_, v___x_4149_, v_options_3778_, v___x_4151_, v___y_4154_, v___f_4148_, v___x_4165_, v_a_3748_, v_a_3749_);
return v___x_4166_;
}
v___jp_4167_:
{
lean_object* v___x_4171_; 
v___x_4171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4171_, 0, v_a_4170_);
v___y_4153_ = v___y_4168_;
v___y_4154_ = v___y_4169_;
v_a_4155_ = v___x_4171_;
goto v___jp_4152_;
}
v___jp_4172_:
{
if (lean_obj_tag(v___y_4175_) == 0)
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4183_; 
v_a_4176_ = lean_ctor_get(v___y_4175_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___y_4175_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4178_ = v___y_4175_;
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___y_4175_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v___x_4181_; 
if (v_isShared_4179_ == 0)
{
lean_ctor_set_tag(v___x_4178_, 1);
v___x_4181_ = v___x_4178_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_a_4176_);
v___x_4181_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
v___y_4153_ = v___y_4173_;
v___y_4154_ = v___y_4174_;
v_a_4155_ = v___x_4181_;
goto v___jp_4152_;
}
}
}
else
{
lean_object* v_a_4184_; 
v_a_4184_ = lean_ctor_get(v___y_4175_, 0);
lean_inc(v_a_4184_);
lean_dec_ref_known(v___y_4175_, 1);
v___y_4168_ = v___y_4173_;
v___y_4169_ = v___y_4174_;
v_a_4170_ = v_a_4184_;
goto v___jp_4167_;
}
}
v___jp_4185_:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4190_ = lean_box(0);
lean_inc(v_a_3749_);
lean_inc_ref(v_a_3748_);
v___x_4191_ = lean_apply_5(v___y_4187_, v___x_4190_, v___y_4186_, v_a_3748_, v_a_3749_, lean_box(0));
v___y_4173_ = v___y_4188_;
v___y_4174_ = v___y_4189_;
v___y_4175_ = v___x_4191_;
goto v___jp_4172_;
}
v___jp_4192_:
{
lean_object* v___x_4197_; lean_object* v___x_4198_; 
v___x_4197_ = lean_box(0);
lean_inc(v_a_3749_);
lean_inc_ref(v_a_3748_);
v___x_4198_ = lean_apply_5(v___y_4195_, v___x_4197_, v___y_4193_, v_a_3748_, v_a_3749_, lean_box(0));
v___y_4173_ = v___y_4194_;
v___y_4174_ = v___y_4196_;
v___y_4175_ = v___x_4198_;
goto v___jp_4172_;
}
v___jp_4199_:
{
lean_object* v___x_4203_; double v___x_4204_; double v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; 
v___x_4203_ = lean_io_get_num_heartbeats();
v___x_4204_ = lean_float_of_nat(v___y_4200_);
v___x_4205_ = lean_float_of_nat(v___x_4203_);
v___x_4206_ = lean_box_float(v___x_4204_);
v___x_4207_ = lean_box_float(v___x_4205_);
v___x_4208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4208_, 0, v___x_4206_);
lean_ctor_set(v___x_4208_, 1, v___x_4207_);
v___x_4209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4209_, 0, v_a_4202_);
lean_ctor_set(v___x_4209_, 1, v___x_4208_);
v___x_4210_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3924_, v_hasTrace_3780_, v___x_4149_, v_options_3778_, v___x_4151_, v___y_4201_, v___f_4148_, v___x_4209_, v_a_3748_, v_a_3749_);
return v___x_4210_;
}
v___jp_4211_:
{
lean_object* v___x_4215_; 
v___x_4215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4215_, 0, v_a_4214_);
v___y_4200_ = v___y_4212_;
v___y_4201_ = v___y_4213_;
v_a_4202_ = v___x_4215_;
goto v___jp_4199_;
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
v___y_4200_ = v___y_4217_;
v___y_4201_ = v___y_4218_;
v_a_4202_ = v___x_4225_;
goto v___jp_4199_;
}
}
}
else
{
lean_object* v_a_4228_; 
v_a_4228_ = lean_ctor_get(v___y_4219_, 0);
lean_inc(v_a_4228_);
lean_dec_ref_known(v___y_4219_, 1);
v___y_4212_ = v___y_4217_;
v___y_4213_ = v___y_4218_;
v_a_4214_ = v_a_4228_;
goto v___jp_4211_;
}
}
v___jp_4229_:
{
lean_object* v___x_4234_; lean_object* v___x_4235_; 
v___x_4234_ = lean_box(0);
lean_inc(v_a_3749_);
lean_inc_ref(v_a_3748_);
v___x_4235_ = lean_apply_5(v___y_4230_, v___x_4234_, v___y_4232_, v_a_3748_, v_a_3749_, lean_box(0));
v___y_4217_ = v___y_4231_;
v___y_4218_ = v___y_4233_;
v___y_4219_ = v___x_4235_;
goto v___jp_4216_;
}
v___jp_4236_:
{
lean_object* v___x_4241_; lean_object* v___x_4242_; 
v___x_4241_ = lean_box(0);
lean_inc(v_a_3749_);
lean_inc_ref(v_a_3748_);
v___x_4242_ = lean_apply_5(v___y_4238_, v___x_4241_, v___y_4239_, v_a_3748_, v_a_3749_, lean_box(0));
v___y_4217_ = v___y_4237_;
v___y_4218_ = v___y_4240_;
v___y_4219_ = v___x_4242_;
goto v___jp_4216_;
}
v___jp_4243_:
{
lean_object* v___x_4244_; lean_object* v_a_4245_; lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4428_; 
v___x_4244_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v_a_3749_);
v_a_4245_ = lean_ctor_get(v___x_4244_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4244_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4247_ = v___x_4244_;
v_isShared_4248_ = v_isSharedCheck_4428_;
goto v_resetjp_4246_;
}
else
{
lean_inc(v_a_4245_);
lean_dec(v___x_4244_);
v___x_4247_ = lean_box(0);
v_isShared_4248_ = v_isSharedCheck_4428_;
goto v_resetjp_4246_;
}
v_resetjp_4246_:
{
lean_object* v___x_4249_; uint8_t v___x_4250_; 
v___x_4249_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4250_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3778_, v___x_4249_);
if (v___x_4250_ == 0)
{
lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v_env_4253_; lean_object* v_nextMacroScope_4254_; lean_object* v_ngen_4255_; lean_object* v_auxDeclNGen_4256_; lean_object* v_traceState_4257_; lean_object* v_recordedDeps_4258_; lean_object* v_messages_4259_; lean_object* v_infoState_4260_; lean_object* v_snapshotTasks_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4338_; 
v___x_4251_ = lean_io_mono_nanos_now();
v___x_4252_ = lean_st_ref_take(v_a_3749_);
v_env_4253_ = lean_ctor_get(v___x_4252_, 0);
v_nextMacroScope_4254_ = lean_ctor_get(v___x_4252_, 1);
v_ngen_4255_ = lean_ctor_get(v___x_4252_, 2);
v_auxDeclNGen_4256_ = lean_ctor_get(v___x_4252_, 3);
v_traceState_4257_ = lean_ctor_get(v___x_4252_, 4);
v_recordedDeps_4258_ = lean_ctor_get(v___x_4252_, 6);
v_messages_4259_ = lean_ctor_get(v___x_4252_, 7);
v_infoState_4260_ = lean_ctor_get(v___x_4252_, 8);
v_snapshotTasks_4261_ = lean_ctor_get(v___x_4252_, 9);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4252_);
if (v_isSharedCheck_4338_ == 0)
{
lean_object* v_unused_4339_; 
v_unused_4339_ = lean_ctor_get(v___x_4252_, 5);
lean_dec(v_unused_4339_);
v___x_4263_ = v___x_4252_;
v_isShared_4264_ = v_isSharedCheck_4338_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_snapshotTasks_4261_);
lean_inc(v_infoState_4260_);
lean_inc(v_messages_4259_);
lean_inc(v_recordedDeps_4258_);
lean_inc(v_traceState_4257_);
lean_inc(v_auxDeclNGen_4256_);
lean_inc(v_ngen_4255_);
lean_inc(v_nextMacroScope_4254_);
lean_inc(v_env_4253_);
lean_dec(v___x_4252_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4338_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4269_; 
lean_inc(v_decl_3746_);
v___x_4265_ = l_Lean_Declaration_getNames(v_decl_3746_);
v___x_4266_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4253_, v___x_4265_);
v___x_4267_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4264_ == 0)
{
lean_ctor_set(v___x_4263_, 5, v___x_4267_);
lean_ctor_set(v___x_4263_, 0, v___x_4266_);
v___x_4269_ = v___x_4263_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v___x_4266_);
lean_ctor_set(v_reuseFailAlloc_4337_, 1, v_nextMacroScope_4254_);
lean_ctor_set(v_reuseFailAlloc_4337_, 2, v_ngen_4255_);
lean_ctor_set(v_reuseFailAlloc_4337_, 3, v_auxDeclNGen_4256_);
lean_ctor_set(v_reuseFailAlloc_4337_, 4, v_traceState_4257_);
lean_ctor_set(v_reuseFailAlloc_4337_, 5, v___x_4267_);
lean_ctor_set(v_reuseFailAlloc_4337_, 6, v_recordedDeps_4258_);
lean_ctor_set(v_reuseFailAlloc_4337_, 7, v_messages_4259_);
lean_ctor_set(v_reuseFailAlloc_4337_, 8, v_infoState_4260_);
lean_ctor_set(v_reuseFailAlloc_4337_, 9, v_snapshotTasks_4261_);
v___x_4269_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___f_4275_; 
v___x_4270_ = lean_st_ref_put(v_a_3749_, v___x_4269_);
v___x_4271_ = lean_box(0);
v___x_4272_ = lean_box(v_hasTrace_3780_);
v___x_4273_ = lean_box(v___x_4250_);
v___x_4274_ = lean_box(v___x_3923_);
lean_inc(v_decl_3746_);
v___f_4275_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed), 12, 7);
lean_closure_set(v___f_4275_, 0, v_decl_3746_);
lean_closure_set(v___f_4275_, 1, v___x_4272_);
lean_closure_set(v___f_4275_, 2, v___x_4273_);
lean_closure_set(v___f_4275_, 3, v_cls_3924_);
lean_closure_set(v___f_4275_, 4, v___x_4274_);
lean_closure_set(v___f_4275_, 5, v___x_4267_);
lean_closure_set(v___f_4275_, 6, v___x_4271_);
switch(lean_obj_tag(v_decl_3746_))
{
case 2:
{
lean_object* v_val_4276_; lean_object* v___f_4277_; lean_object* v___x_4278_; 
lean_del_object(v___x_4247_);
v_val_4276_ = lean_ctor_get(v_decl_3746_, 0);
lean_inc_ref_n(v_val_4276_, 2);
lean_dec_ref_known(v_decl_3746_, 1);
v___f_4277_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed), 7, 2);
lean_closure_set(v___f_4277_, 0, v_val_4276_);
lean_closure_set(v___f_4277_, 1, v___f_4275_);
v___x_4278_ = lean_st_ref_get(v_a_3749_);
if (v_forceExpose_3747_ == 0)
{
lean_object* v_env_4279_; lean_object* v___x_4280_; uint8_t v_isModule_4281_; 
v_env_4279_ = lean_ctor_get(v___x_4278_, 0);
lean_inc_ref(v_env_4279_);
lean_dec(v___x_4278_);
v___x_4280_ = l_Lean_Environment_header(v_env_4279_);
lean_dec_ref(v_env_4279_);
v_isModule_4281_ = lean_ctor_get_uint8(v___x_4280_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4280_);
if (v_isModule_4281_ == 0)
{
lean_dec_ref(v_val_4276_);
v___y_4186_ = v___x_4271_;
v___y_4187_ = v___f_4277_;
v___y_4188_ = v___x_4251_;
v___y_4189_ = v_a_4245_;
goto v___jp_4185_;
}
else
{
if (v___x_4151_ == 0)
{
lean_object* v___x_4282_; lean_object* v___x_4283_; 
v___x_4282_ = lean_box(0);
v___x_4283_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(v_val_4276_, v___x_4250_, v___f_4277_, v___x_4282_, v_a_3748_, v_a_3749_);
lean_dec_ref(v_val_4276_);
v___y_4173_ = v___x_4251_;
v___y_4174_ = v_a_4245_;
v___y_4175_ = v___x_4283_;
goto v___jp_4172_;
}
else
{
lean_object* v_toConstantVal_4284_; lean_object* v_name_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; 
v_toConstantVal_4284_ = lean_ctor_get(v_val_4276_, 0);
v_name_4285_ = lean_ctor_get(v_toConstantVal_4284_, 0);
v___x_4286_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4285_);
v___x_4287_ = l_Lean_MessageData_ofName(v_name_4285_);
v___x_4288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4288_, 0, v___x_4286_);
lean_ctor_set(v___x_4288_, 1, v___x_4287_);
v___x_4289_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4290_, 0, v___x_4288_);
lean_ctor_set(v___x_4290_, 1, v___x_4289_);
v___x_4291_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3924_, v___x_4290_, v_a_3748_, v_a_3749_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v_a_4292_; lean_object* v___x_4293_; 
v_a_4292_ = lean_ctor_get(v___x_4291_, 0);
lean_inc(v_a_4292_);
lean_dec_ref_known(v___x_4291_, 1);
v___x_4293_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(v_val_4276_, v___x_4250_, v___f_4277_, v_a_4292_, v_a_3748_, v_a_3749_);
lean_dec_ref(v_val_4276_);
v___y_4173_ = v___x_4251_;
v___y_4174_ = v_a_4245_;
v___y_4175_ = v___x_4293_;
goto v___jp_4172_;
}
else
{
lean_object* v_a_4294_; 
lean_dec_ref(v___f_4277_);
lean_dec_ref(v_val_4276_);
v_a_4294_ = lean_ctor_get(v___x_4291_, 0);
lean_inc(v_a_4294_);
lean_dec_ref_known(v___x_4291_, 1);
v___y_4168_ = v___x_4251_;
v___y_4169_ = v_a_4245_;
v_a_4170_ = v_a_4294_;
goto v___jp_4167_;
}
}
}
}
else
{
lean_dec(v___x_4278_);
lean_dec_ref(v_val_4276_);
v___y_4186_ = v___x_4271_;
v___y_4187_ = v___f_4277_;
v___y_4188_ = v___x_4251_;
v___y_4189_ = v_a_4245_;
goto v___jp_4185_;
}
}
case 1:
{
lean_object* v_val_4295_; lean_object* v___x_4296_; 
lean_del_object(v___x_4247_);
v_val_4295_ = lean_ctor_get(v_decl_3746_, 0);
lean_inc_ref(v_val_4295_);
lean_dec_ref_known(v_decl_3746_, 1);
v___x_4296_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v___f_4275_, v___x_4250_, v_forceExpose_3747_, v___x_4271_, v_cls_3924_, v_val_4295_, v_a_3748_, v_a_3749_);
v___y_4173_ = v___x_4251_;
v___y_4174_ = v_a_4245_;
v___y_4175_ = v___x_4296_;
goto v___jp_4172_;
}
case 5:
{
lean_object* v_defns_4297_; 
lean_del_object(v___x_4247_);
v_defns_4297_ = lean_ctor_get(v_decl_3746_, 0);
if (lean_obj_tag(v_defns_4297_) == 1)
{
lean_object* v_tail_4298_; 
v_tail_4298_ = lean_ctor_get(v_defns_4297_, 1);
if (lean_obj_tag(v_tail_4298_) == 0)
{
lean_object* v_head_4299_; lean_object* v___x_4300_; 
lean_inc_ref(v_defns_4297_);
lean_dec_ref_known(v_decl_3746_, 1);
v_head_4299_ = lean_ctor_get(v_defns_4297_, 0);
lean_inc(v_head_4299_);
lean_dec_ref_known(v_defns_4297_, 2);
v___x_4300_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v___f_4275_, v___x_4250_, v_forceExpose_3747_, v___x_4271_, v_cls_3924_, v_head_4299_, v_a_3748_, v_a_3749_);
v___y_4173_ = v___x_4251_;
v___y_4174_ = v_a_4245_;
v___y_4175_ = v___x_4300_;
goto v___jp_4172_;
}
else
{
lean_object* v___x_4301_; 
lean_dec_ref(v___f_4275_);
lean_inc_ref(v_decl_3746_);
v___x_4301_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3746_, v_cls_3924_, v_decl_3746_, v_a_3748_, v_a_3749_);
lean_dec_ref_known(v_decl_3746_, 1);
v___y_4173_ = v___x_4251_;
v___y_4174_ = v_a_4245_;
v___y_4175_ = v___x_4301_;
goto v___jp_4172_;
}
}
else
{
lean_object* v___x_4302_; 
lean_dec_ref(v___f_4275_);
lean_inc_ref(v_decl_3746_);
v___x_4302_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3746_, v_cls_3924_, v_decl_3746_, v_a_3748_, v_a_3749_);
lean_dec_ref_known(v_decl_3746_, 1);
v___y_4173_ = v___x_4251_;
v___y_4174_ = v_a_4245_;
v___y_4175_ = v___x_4302_;
goto v___jp_4172_;
}
}
case 3:
{
lean_object* v_val_4303_; lean_object* v___f_4304_; lean_object* v___x_4305_; lean_object* v_env_4306_; lean_object* v___x_4307_; 
lean_del_object(v___x_4247_);
v_val_4303_ = lean_ctor_get(v_decl_3746_, 0);
lean_inc_ref_n(v_val_4303_, 2);
lean_dec_ref_known(v_decl_3746_, 1);
v___f_4304_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed), 7, 2);
lean_closure_set(v___f_4304_, 0, v_val_4303_);
lean_closure_set(v___f_4304_, 1, v___f_4275_);
v___x_4305_ = lean_st_ref_get(v_a_3749_);
v_env_4306_ = lean_ctor_get(v___x_4305_, 0);
lean_inc_ref(v_env_4306_);
lean_dec(v___x_4305_);
v___x_4307_ = lean_st_ref_get(v_a_3749_);
if (v_forceExpose_3747_ == 0)
{
lean_object* v_env_4308_; lean_object* v___x_4309_; uint8_t v_isModule_4310_; 
v_env_4308_ = lean_ctor_get(v___x_4307_, 0);
lean_inc_ref(v_env_4308_);
lean_dec(v___x_4307_);
v___x_4309_ = l_Lean_Environment_header(v_env_4306_);
lean_dec_ref(v_env_4306_);
v_isModule_4310_ = lean_ctor_get_uint8(v___x_4309_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4309_);
if (v_isModule_4310_ == 0)
{
lean_dec_ref(v_env_4308_);
lean_dec_ref(v_val_4303_);
v___y_4193_ = v___x_4271_;
v___y_4194_ = v___x_4251_;
v___y_4195_ = v___f_4304_;
v___y_4196_ = v_a_4245_;
goto v___jp_4192_;
}
else
{
uint8_t v_isExporting_4311_; 
v_isExporting_4311_ = lean_ctor_get_uint8(v_env_4308_, sizeof(void*)*13);
lean_dec_ref(v_env_4308_);
if (v_isExporting_4311_ == 0)
{
if (v___x_4151_ == 0)
{
lean_object* v___x_4312_; lean_object* v___x_4313_; 
v___x_4312_ = lean_box(0);
v___x_4313_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_4303_, v___f_4304_, v___x_4312_, v_a_3748_, v_a_3749_);
lean_dec_ref(v_val_4303_);
v___y_4173_ = v___x_4251_;
v___y_4174_ = v_a_4245_;
v___y_4175_ = v___x_4313_;
goto v___jp_4172_;
}
else
{
lean_object* v_toConstantVal_4314_; lean_object* v_name_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; 
v_toConstantVal_4314_ = lean_ctor_get(v_val_4303_, 0);
v_name_4315_ = lean_ctor_get(v_toConstantVal_4314_, 0);
v___x_4316_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4315_);
v___x_4317_ = l_Lean_MessageData_ofName(v_name_4315_);
v___x_4318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4318_, 0, v___x_4316_);
lean_ctor_set(v___x_4318_, 1, v___x_4317_);
v___x_4319_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4320_, 0, v___x_4318_);
lean_ctor_set(v___x_4320_, 1, v___x_4319_);
v___x_4321_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3924_, v___x_4320_, v_a_3748_, v_a_3749_);
if (lean_obj_tag(v___x_4321_) == 0)
{
lean_object* v_a_4322_; lean_object* v___x_4323_; 
v_a_4322_ = lean_ctor_get(v___x_4321_, 0);
lean_inc(v_a_4322_);
lean_dec_ref_known(v___x_4321_, 1);
v___x_4323_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_4303_, v___f_4304_, v_a_4322_, v_a_3748_, v_a_3749_);
lean_dec_ref(v_val_4303_);
v___y_4173_ = v___x_4251_;
v___y_4174_ = v_a_4245_;
v___y_4175_ = v___x_4323_;
goto v___jp_4172_;
}
else
{
lean_object* v_a_4324_; 
lean_dec_ref(v___f_4304_);
lean_dec_ref(v_val_4303_);
v_a_4324_ = lean_ctor_get(v___x_4321_, 0);
lean_inc(v_a_4324_);
lean_dec_ref_known(v___x_4321_, 1);
v___y_4168_ = v___x_4251_;
v___y_4169_ = v_a_4245_;
v_a_4170_ = v_a_4324_;
goto v___jp_4167_;
}
}
}
else
{
lean_dec_ref(v_val_4303_);
v___y_4193_ = v___x_4271_;
v___y_4194_ = v___x_4251_;
v___y_4195_ = v___f_4304_;
v___y_4196_ = v_a_4245_;
goto v___jp_4192_;
}
}
}
else
{
lean_dec(v___x_4307_);
lean_dec_ref(v_env_4306_);
lean_dec_ref(v_val_4303_);
v___y_4193_ = v___x_4271_;
v___y_4194_ = v___x_4251_;
v___y_4195_ = v___f_4304_;
v___y_4196_ = v_a_4245_;
goto v___jp_4192_;
}
}
case 0:
{
lean_object* v_val_4325_; lean_object* v_toConstantVal_4326_; lean_object* v_name_4327_; lean_object* v___x_4329_; 
lean_dec_ref(v___f_4275_);
v_val_4325_ = lean_ctor_get(v_decl_3746_, 0);
v_toConstantVal_4326_ = lean_ctor_get(v_val_4325_, 0);
v_name_4327_ = lean_ctor_get(v_toConstantVal_4326_, 0);
lean_inc_ref(v_val_4325_);
if (v_isShared_4248_ == 0)
{
lean_ctor_set(v___x_4247_, 0, v_val_4325_);
v___x_4329_ = v___x_4247_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_val_4325_);
v___x_4329_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
uint8_t v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4330_ = 2;
v___x_4331_ = lean_box(v___x_4330_);
v___x_4332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4332_, 0, v___x_4329_);
lean_ctor_set(v___x_4332_, 1, v___x_4331_);
lean_inc(v_name_4327_);
v___x_4333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4333_, 0, v_name_4327_);
lean_ctor_set(v___x_4333_, 1, v___x_4332_);
v___x_4334_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_decl_3746_, v_hasTrace_3780_, v___x_4250_, v_cls_3924_, v___x_3923_, v___x_4267_, v___x_4271_, v___x_4333_, v___x_4271_, v_a_3748_, v_a_3749_);
v___y_4173_ = v___x_4251_;
v___y_4174_ = v_a_4245_;
v___y_4175_ = v___x_4334_;
goto v___jp_4172_;
}
}
default: 
{
lean_object* v___x_4336_; 
lean_dec_ref(v___f_4275_);
lean_del_object(v___x_4247_);
lean_inc(v_decl_3746_);
v___x_4336_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3746_, v_cls_3924_, v_decl_3746_, v_a_3748_, v_a_3749_);
lean_dec(v_decl_3746_);
v___y_4173_ = v___x_4251_;
v___y_4174_ = v_a_4245_;
v___y_4175_ = v___x_4336_;
goto v___jp_4172_;
}
}
}
}
}
else
{
lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v_env_4342_; lean_object* v_nextMacroScope_4343_; lean_object* v_ngen_4344_; lean_object* v_auxDeclNGen_4345_; lean_object* v_traceState_4346_; lean_object* v_recordedDeps_4347_; lean_object* v_messages_4348_; lean_object* v_infoState_4349_; lean_object* v_snapshotTasks_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4426_; 
v___x_4340_ = lean_io_get_num_heartbeats();
v___x_4341_ = lean_st_ref_take(v_a_3749_);
v_env_4342_ = lean_ctor_get(v___x_4341_, 0);
v_nextMacroScope_4343_ = lean_ctor_get(v___x_4341_, 1);
v_ngen_4344_ = lean_ctor_get(v___x_4341_, 2);
v_auxDeclNGen_4345_ = lean_ctor_get(v___x_4341_, 3);
v_traceState_4346_ = lean_ctor_get(v___x_4341_, 4);
v_recordedDeps_4347_ = lean_ctor_get(v___x_4341_, 6);
v_messages_4348_ = lean_ctor_get(v___x_4341_, 7);
v_infoState_4349_ = lean_ctor_get(v___x_4341_, 8);
v_snapshotTasks_4350_ = lean_ctor_get(v___x_4341_, 9);
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4341_);
if (v_isSharedCheck_4426_ == 0)
{
lean_object* v_unused_4427_; 
v_unused_4427_ = lean_ctor_get(v___x_4341_, 5);
lean_dec(v_unused_4427_);
v___x_4352_ = v___x_4341_;
v_isShared_4353_ = v_isSharedCheck_4426_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_snapshotTasks_4350_);
lean_inc(v_infoState_4349_);
lean_inc(v_messages_4348_);
lean_inc(v_recordedDeps_4347_);
lean_inc(v_traceState_4346_);
lean_inc(v_auxDeclNGen_4345_);
lean_inc(v_ngen_4344_);
lean_inc(v_nextMacroScope_4343_);
lean_inc(v_env_4342_);
lean_dec(v___x_4341_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4426_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4358_; 
lean_inc(v_decl_3746_);
v___x_4354_ = l_Lean_Declaration_getNames(v_decl_3746_);
v___x_4355_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4342_, v___x_4354_);
v___x_4356_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4353_ == 0)
{
lean_ctor_set(v___x_4352_, 5, v___x_4356_);
lean_ctor_set(v___x_4352_, 0, v___x_4355_);
v___x_4358_ = v___x_4352_;
goto v_reusejp_4357_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4355_);
lean_ctor_set(v_reuseFailAlloc_4425_, 1, v_nextMacroScope_4343_);
lean_ctor_set(v_reuseFailAlloc_4425_, 2, v_ngen_4344_);
lean_ctor_set(v_reuseFailAlloc_4425_, 3, v_auxDeclNGen_4345_);
lean_ctor_set(v_reuseFailAlloc_4425_, 4, v_traceState_4346_);
lean_ctor_set(v_reuseFailAlloc_4425_, 5, v___x_4356_);
lean_ctor_set(v_reuseFailAlloc_4425_, 6, v_recordedDeps_4347_);
lean_ctor_set(v_reuseFailAlloc_4425_, 7, v_messages_4348_);
lean_ctor_set(v_reuseFailAlloc_4425_, 8, v_infoState_4349_);
lean_ctor_set(v_reuseFailAlloc_4425_, 9, v_snapshotTasks_4350_);
v___x_4358_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4357_;
}
v_reusejp_4357_:
{
lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___f_4363_; 
v___x_4359_ = lean_st_ref_put(v_a_3749_, v___x_4358_);
v___x_4360_ = lean_box(0);
v___x_4361_ = lean_box(v___x_4250_);
v___x_4362_ = lean_box(v___x_3923_);
lean_inc(v_decl_3746_);
v___f_4363_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14___boxed), 11, 6);
lean_closure_set(v___f_4363_, 0, v_decl_3746_);
lean_closure_set(v___f_4363_, 1, v___x_4361_);
lean_closure_set(v___f_4363_, 2, v_cls_3924_);
lean_closure_set(v___f_4363_, 3, v___x_4362_);
lean_closure_set(v___f_4363_, 4, v___x_4356_);
lean_closure_set(v___f_4363_, 5, v___x_4360_);
switch(lean_obj_tag(v_decl_3746_))
{
case 2:
{
lean_object* v_val_4364_; lean_object* v___f_4365_; lean_object* v___x_4366_; 
lean_del_object(v___x_4247_);
v_val_4364_ = lean_ctor_get(v_decl_3746_, 0);
lean_inc_ref_n(v_val_4364_, 2);
lean_dec_ref_known(v_decl_3746_, 1);
v___f_4365_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed), 7, 2);
lean_closure_set(v___f_4365_, 0, v_val_4364_);
lean_closure_set(v___f_4365_, 1, v___f_4363_);
v___x_4366_ = lean_st_ref_get(v_a_3749_);
if (v_forceExpose_3747_ == 0)
{
lean_object* v_env_4367_; lean_object* v___x_4368_; uint8_t v_isModule_4369_; 
v_env_4367_ = lean_ctor_get(v___x_4366_, 0);
lean_inc_ref(v_env_4367_);
lean_dec(v___x_4366_);
v___x_4368_ = l_Lean_Environment_header(v_env_4367_);
lean_dec_ref(v_env_4367_);
v_isModule_4369_ = lean_ctor_get_uint8(v___x_4368_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4368_);
if (v_isModule_4369_ == 0)
{
lean_dec_ref(v_val_4364_);
v___y_4237_ = v___x_4340_;
v___y_4238_ = v___f_4365_;
v___y_4239_ = v___x_4360_;
v___y_4240_ = v_a_4245_;
goto v___jp_4236_;
}
else
{
if (v___x_4151_ == 0)
{
lean_object* v___x_4370_; lean_object* v___x_4371_; 
v___x_4370_ = lean_box(0);
v___x_4371_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_val_4364_, v___f_4365_, v___x_4370_, v_a_3748_, v_a_3749_);
lean_dec_ref(v_val_4364_);
v___y_4217_ = v___x_4340_;
v___y_4218_ = v_a_4245_;
v___y_4219_ = v___x_4371_;
goto v___jp_4216_;
}
else
{
lean_object* v_toConstantVal_4372_; lean_object* v_name_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; 
v_toConstantVal_4372_ = lean_ctor_get(v_val_4364_, 0);
v_name_4373_ = lean_ctor_get(v_toConstantVal_4372_, 0);
v___x_4374_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4373_);
v___x_4375_ = l_Lean_MessageData_ofName(v_name_4373_);
v___x_4376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4376_, 0, v___x_4374_);
lean_ctor_set(v___x_4376_, 1, v___x_4375_);
v___x_4377_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4378_, 0, v___x_4376_);
lean_ctor_set(v___x_4378_, 1, v___x_4377_);
v___x_4379_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3924_, v___x_4378_, v_a_3748_, v_a_3749_);
if (lean_obj_tag(v___x_4379_) == 0)
{
lean_object* v_a_4380_; lean_object* v___x_4381_; 
v_a_4380_ = lean_ctor_get(v___x_4379_, 0);
lean_inc(v_a_4380_);
lean_dec_ref_known(v___x_4379_, 1);
v___x_4381_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_val_4364_, v___f_4365_, v_a_4380_, v_a_3748_, v_a_3749_);
lean_dec_ref(v_val_4364_);
v___y_4217_ = v___x_4340_;
v___y_4218_ = v_a_4245_;
v___y_4219_ = v___x_4381_;
goto v___jp_4216_;
}
else
{
lean_object* v_a_4382_; 
lean_dec_ref(v___f_4365_);
lean_dec_ref(v_val_4364_);
v_a_4382_ = lean_ctor_get(v___x_4379_, 0);
lean_inc(v_a_4382_);
lean_dec_ref_known(v___x_4379_, 1);
v___y_4212_ = v___x_4340_;
v___y_4213_ = v_a_4245_;
v_a_4214_ = v_a_4382_;
goto v___jp_4211_;
}
}
}
}
else
{
lean_dec(v___x_4366_);
lean_dec_ref(v_val_4364_);
v___y_4237_ = v___x_4340_;
v___y_4238_ = v___f_4365_;
v___y_4239_ = v___x_4360_;
v___y_4240_ = v_a_4245_;
goto v___jp_4236_;
}
}
case 1:
{
lean_object* v_val_4383_; lean_object* v___x_4384_; 
lean_del_object(v___x_4247_);
v_val_4383_ = lean_ctor_get(v_decl_3746_, 0);
lean_inc_ref(v_val_4383_);
lean_dec_ref_known(v_decl_3746_, 1);
v___x_4384_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(v___f_4363_, v_forceExpose_3747_, v___x_4360_, v_cls_3924_, v_val_4383_, v_a_3748_, v_a_3749_);
v___y_4217_ = v___x_4340_;
v___y_4218_ = v_a_4245_;
v___y_4219_ = v___x_4384_;
goto v___jp_4216_;
}
case 5:
{
lean_object* v_defns_4385_; 
lean_del_object(v___x_4247_);
v_defns_4385_ = lean_ctor_get(v_decl_3746_, 0);
if (lean_obj_tag(v_defns_4385_) == 1)
{
lean_object* v_tail_4386_; 
v_tail_4386_ = lean_ctor_get(v_defns_4385_, 1);
if (lean_obj_tag(v_tail_4386_) == 0)
{
lean_object* v_head_4387_; lean_object* v___x_4388_; 
lean_inc_ref(v_defns_4385_);
lean_dec_ref_known(v_decl_3746_, 1);
v_head_4387_ = lean_ctor_get(v_defns_4385_, 0);
lean_inc(v_head_4387_);
lean_dec_ref_known(v_defns_4385_, 2);
v___x_4388_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(v___f_4363_, v_forceExpose_3747_, v___x_4360_, v_cls_3924_, v_head_4387_, v_a_3748_, v_a_3749_);
v___y_4217_ = v___x_4340_;
v___y_4218_ = v_a_4245_;
v___y_4219_ = v___x_4388_;
goto v___jp_4216_;
}
else
{
lean_object* v___x_4389_; 
lean_dec_ref(v___f_4363_);
lean_inc_ref(v_decl_3746_);
v___x_4389_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3746_, v_cls_3924_, v_decl_3746_, v_a_3748_, v_a_3749_);
lean_dec_ref_known(v_decl_3746_, 1);
v___y_4217_ = v___x_4340_;
v___y_4218_ = v_a_4245_;
v___y_4219_ = v___x_4389_;
goto v___jp_4216_;
}
}
else
{
lean_object* v___x_4390_; 
lean_dec_ref(v___f_4363_);
lean_inc_ref(v_decl_3746_);
v___x_4390_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3746_, v_cls_3924_, v_decl_3746_, v_a_3748_, v_a_3749_);
lean_dec_ref_known(v_decl_3746_, 1);
v___y_4217_ = v___x_4340_;
v___y_4218_ = v_a_4245_;
v___y_4219_ = v___x_4390_;
goto v___jp_4216_;
}
}
case 3:
{
lean_object* v_val_4391_; lean_object* v___f_4392_; lean_object* v___x_4393_; lean_object* v_env_4394_; lean_object* v___x_4395_; 
lean_del_object(v___x_4247_);
v_val_4391_ = lean_ctor_get(v_decl_3746_, 0);
lean_inc_ref_n(v_val_4391_, 2);
lean_dec_ref_known(v_decl_3746_, 1);
v___f_4392_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed), 7, 2);
lean_closure_set(v___f_4392_, 0, v_val_4391_);
lean_closure_set(v___f_4392_, 1, v___f_4363_);
v___x_4393_ = lean_st_ref_get(v_a_3749_);
v_env_4394_ = lean_ctor_get(v___x_4393_, 0);
lean_inc_ref(v_env_4394_);
lean_dec(v___x_4393_);
v___x_4395_ = lean_st_ref_get(v_a_3749_);
if (v_forceExpose_3747_ == 0)
{
lean_object* v_env_4396_; lean_object* v___x_4397_; uint8_t v_isModule_4398_; 
v_env_4396_ = lean_ctor_get(v___x_4395_, 0);
lean_inc_ref(v_env_4396_);
lean_dec(v___x_4395_);
v___x_4397_ = l_Lean_Environment_header(v_env_4394_);
lean_dec_ref(v_env_4394_);
v_isModule_4398_ = lean_ctor_get_uint8(v___x_4397_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4397_);
if (v_isModule_4398_ == 0)
{
lean_dec_ref(v_env_4396_);
lean_dec_ref(v_val_4391_);
v___y_4230_ = v___f_4392_;
v___y_4231_ = v___x_4340_;
v___y_4232_ = v___x_4360_;
v___y_4233_ = v_a_4245_;
goto v___jp_4229_;
}
else
{
uint8_t v_isExporting_4399_; 
v_isExporting_4399_ = lean_ctor_get_uint8(v_env_4396_, sizeof(void*)*13);
lean_dec_ref(v_env_4396_);
if (v_isExporting_4399_ == 0)
{
if (v___x_4151_ == 0)
{
lean_object* v___x_4400_; lean_object* v___x_4401_; 
v___x_4400_ = lean_box(0);
v___x_4401_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_4391_, v___f_4392_, v___x_4400_, v_a_3748_, v_a_3749_);
lean_dec_ref(v_val_4391_);
v___y_4217_ = v___x_4340_;
v___y_4218_ = v_a_4245_;
v___y_4219_ = v___x_4401_;
goto v___jp_4216_;
}
else
{
lean_object* v_toConstantVal_4402_; lean_object* v_name_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; 
v_toConstantVal_4402_ = lean_ctor_get(v_val_4391_, 0);
v_name_4403_ = lean_ctor_get(v_toConstantVal_4402_, 0);
v___x_4404_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4403_);
v___x_4405_ = l_Lean_MessageData_ofName(v_name_4403_);
v___x_4406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4406_, 0, v___x_4404_);
lean_ctor_set(v___x_4406_, 1, v___x_4405_);
v___x_4407_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4408_, 0, v___x_4406_);
lean_ctor_set(v___x_4408_, 1, v___x_4407_);
v___x_4409_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3924_, v___x_4408_, v_a_3748_, v_a_3749_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; lean_object* v___x_4411_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_a_4410_);
lean_dec_ref_known(v___x_4409_, 1);
v___x_4411_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_4391_, v___f_4392_, v_a_4410_, v_a_3748_, v_a_3749_);
lean_dec_ref(v_val_4391_);
v___y_4217_ = v___x_4340_;
v___y_4218_ = v_a_4245_;
v___y_4219_ = v___x_4411_;
goto v___jp_4216_;
}
else
{
lean_object* v_a_4412_; 
lean_dec_ref(v___f_4392_);
lean_dec_ref(v_val_4391_);
v_a_4412_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_a_4412_);
lean_dec_ref_known(v___x_4409_, 1);
v___y_4212_ = v___x_4340_;
v___y_4213_ = v_a_4245_;
v_a_4214_ = v_a_4412_;
goto v___jp_4211_;
}
}
}
else
{
lean_dec_ref(v_val_4391_);
v___y_4230_ = v___f_4392_;
v___y_4231_ = v___x_4340_;
v___y_4232_ = v___x_4360_;
v___y_4233_ = v_a_4245_;
goto v___jp_4229_;
}
}
}
else
{
lean_dec(v___x_4395_);
lean_dec_ref(v_env_4394_);
lean_dec_ref(v_val_4391_);
v___y_4230_ = v___f_4392_;
v___y_4231_ = v___x_4340_;
v___y_4232_ = v___x_4360_;
v___y_4233_ = v_a_4245_;
goto v___jp_4229_;
}
}
case 0:
{
lean_object* v_val_4413_; lean_object* v_toConstantVal_4414_; lean_object* v_name_4415_; lean_object* v___x_4417_; 
lean_dec_ref(v___f_4363_);
v_val_4413_ = lean_ctor_get(v_decl_3746_, 0);
v_toConstantVal_4414_ = lean_ctor_get(v_val_4413_, 0);
v_name_4415_ = lean_ctor_get(v_toConstantVal_4414_, 0);
lean_inc_ref(v_val_4413_);
if (v_isShared_4248_ == 0)
{
lean_ctor_set(v___x_4247_, 0, v_val_4413_);
v___x_4417_ = v___x_4247_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v_val_4413_);
v___x_4417_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
uint8_t v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; 
v___x_4418_ = 2;
v___x_4419_ = lean_box(v___x_4418_);
v___x_4420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4420_, 0, v___x_4417_);
lean_ctor_set(v___x_4420_, 1, v___x_4419_);
lean_inc(v_name_4415_);
v___x_4421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4421_, 0, v_name_4415_);
lean_ctor_set(v___x_4421_, 1, v___x_4420_);
v___x_4422_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(v_decl_3746_, v___x_4250_, v_cls_3924_, v___x_3923_, v___x_4356_, v___x_4360_, v___x_4421_, v___x_4360_, v_a_3748_, v_a_3749_);
v___y_4217_ = v___x_4340_;
v___y_4218_ = v_a_4245_;
v___y_4219_ = v___x_4422_;
goto v___jp_4216_;
}
}
default: 
{
lean_object* v___x_4424_; 
lean_dec_ref(v___f_4363_);
lean_del_object(v___x_4247_);
lean_inc(v_decl_3746_);
v___x_4424_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3746_, v_cls_3924_, v_decl_3746_, v_a_3748_, v_a_3749_);
lean_dec(v_decl_3746_);
v___y_4217_ = v___x_4340_;
v___y_4218_ = v_a_4245_;
v___y_4219_ = v___x_4424_;
goto v___jp_4216_;
}
}
}
}
}
}
}
}
v___jp_3751_:
{
lean_object* v___x_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3762_; 
v___x_3755_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3752_, v___y_3753_);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3762_ == 0)
{
lean_object* v_unused_3763_; 
v_unused_3763_ = lean_ctor_get(v___x_3755_, 0);
lean_dec(v_unused_3763_);
v___x_3757_ = v___x_3755_;
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
else
{
lean_dec(v___x_3755_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3758_ == 0)
{
lean_ctor_set_tag(v___x_3757_, 1);
lean_ctor_set(v___x_3757_, 0, v_a_3754_);
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_a_3754_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
v___jp_3764_:
{
lean_object* v___x_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
v___x_3768_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3766_, v___y_3765_);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3775_ == 0)
{
lean_object* v_unused_3776_; 
v_unused_3776_ = lean_ctor_get(v___x_3768_, 0);
lean_dec(v_unused_3776_);
v___x_3770_ = v___x_3768_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_dec(v___x_3768_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
lean_ctor_set_tag(v___x_3770_, 1);
lean_ctor_set(v___x_3770_, 0, v_a_3767_);
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3767_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
v___jp_3781_:
{
lean_object* v___x_3794_; 
lean_inc_ref(v___y_3784_);
v___x_3794_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3787_, v___y_3784_, v___y_3792_, v___y_3793_);
if (lean_obj_tag(v___x_3794_) == 0)
{
lean_object* v___x_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3850_; 
lean_dec_ref_known(v___x_3794_, 1);
lean_dec(v___y_3788_);
lean_inc_ref(v___y_3790_);
v___x_3795_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3790_, v___y_3783_);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3850_ == 0)
{
lean_object* v_unused_3851_; 
v_unused_3851_ = lean_ctor_get(v___x_3795_, 0);
lean_dec(v_unused_3851_);
v___x_3797_ = v___x_3795_;
v_isShared_3798_ = v_isSharedCheck_3850_;
goto v_resetjp_3796_;
}
else
{
lean_dec(v___x_3795_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3850_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v___x_3799_; lean_object* v___x_3800_; uint8_t v___x_3801_; 
v___x_3799_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3786_);
v___x_3800_ = l_Lean_Elab_async;
v___x_3801_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_3799_, v___x_3800_);
lean_dec_ref(v___x_3799_);
if (v___x_3801_ == 0)
{
lean_object* v___x_3802_; lean_object* v_r_3803_; 
lean_del_object(v___x_3797_);
lean_dec_ref(v___y_3789_);
lean_dec_ref(v___y_3782_);
v___x_3802_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3784_, v___y_3783_);
lean_dec_ref(v___x_3802_);
v_r_3803_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3746_, v___y_3786_, v___y_3783_);
if (lean_obj_tag(v_r_3803_) == 0)
{
lean_object* v_a_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3822_; 
v_a_3804_ = lean_ctor_get(v_r_3803_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v_r_3803_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3806_ = v_r_3803_;
v_isShared_3807_ = v_isSharedCheck_3822_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_a_3804_);
lean_dec(v_r_3803_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3822_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3809_; 
lean_inc(v_a_3804_);
if (v_isShared_3807_ == 0)
{
lean_ctor_set_tag(v___x_3806_, 1);
v___x_3809_ = v___x_3806_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_a_3804_);
v___x_3809_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
lean_object* v___x_3810_; 
v___x_3810_ = lean_apply_2(v___y_3791_, v___x_3809_, lean_box(0));
if (lean_obj_tag(v___x_3810_) == 0)
{
lean_object* v___x_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
lean_dec_ref_known(v___x_3810_, 1);
v___x_3811_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3790_, v___y_3783_);
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
lean_ctor_set(v___x_3813_, 0, v_a_3804_);
v___x_3816_ = v___x_3813_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_a_3804_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
else
{
lean_object* v_a_3820_; 
lean_dec(v_a_3804_);
v_a_3820_ = lean_ctor_get(v___x_3810_, 0);
lean_inc(v_a_3820_);
lean_dec_ref_known(v___x_3810_, 1);
v___y_3765_ = v___y_3783_;
v___y_3766_ = v___y_3790_;
v_a_3767_ = v_a_3820_;
goto v___jp_3764_;
}
}
}
}
else
{
lean_object* v_a_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; 
v_a_3823_ = lean_ctor_get(v_r_3803_, 0);
lean_inc(v_a_3823_);
lean_dec_ref_known(v_r_3803_, 1);
v___x_3824_ = lean_box(0);
v___x_3825_ = lean_apply_2(v___y_3791_, v___x_3824_, lean_box(0));
if (lean_obj_tag(v___x_3825_) == 0)
{
lean_dec_ref_known(v___x_3825_, 1);
v___y_3765_ = v___y_3783_;
v___y_3766_ = v___y_3790_;
v_a_3767_ = v_a_3823_;
goto v___jp_3764_;
}
else
{
lean_object* v_a_3826_; 
lean_dec(v_a_3823_);
v_a_3826_ = lean_ctor_get(v___x_3825_, 0);
lean_inc(v_a_3826_);
lean_dec_ref_known(v___x_3825_, 1);
v___y_3765_ = v___y_3783_;
v___y_3766_ = v___y_3790_;
v_a_3767_ = v_a_3826_;
goto v___jp_3764_;
}
}
}
else
{
lean_object* v___x_3827_; lean_object* v___x_3829_; 
lean_dec_ref(v___y_3791_);
lean_dec_ref(v___y_3790_);
lean_dec_ref(v___y_3784_);
lean_dec(v_decl_3746_);
v___x_3827_ = l_IO_CancelToken_new();
if (v_isShared_3798_ == 0)
{
lean_ctor_set_tag(v___x_3797_, 1);
lean_ctor_set(v___x_3797_, 0, v___x_3827_);
v___x_3829_ = v___x_3797_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v___x_3827_);
v___x_3829_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; 
v___x_3830_ = lean_unsigned_to_nat(0u);
v___x_3831_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_3832_ = l_Lean_Name_toString(v___x_3831_, v___y_3785_);
lean_inc_ref(v___x_3829_);
v___x_3833_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3789_, v___x_3829_, v___x_3832_, v___y_3786_, v___y_3783_);
if (lean_obj_tag(v___x_3833_) == 0)
{
lean_object* v_a_3834_; lean_object* v_checked_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; 
v_a_3834_ = lean_ctor_get(v___x_3833_, 0);
lean_inc(v_a_3834_);
lean_dec_ref_known(v___x_3833_, 1);
v_checked_3835_ = lean_ctor_get(v___y_3782_, 2);
lean_inc_ref(v_checked_3835_);
lean_dec_ref(v___y_3782_);
v___x_3836_ = lean_io_map_task(v_a_3834_, v_checked_3835_, v___x_3830_, v_hasTrace_3780_);
v___x_3837_ = lean_box(0);
v___x_3838_ = lean_box(2);
v___x_3839_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3839_, 0, v___x_3837_);
lean_ctor_set(v___x_3839_, 1, v___x_3838_);
lean_ctor_set(v___x_3839_, 2, v___x_3829_);
lean_ctor_set(v___x_3839_, 3, v___x_3836_);
v___x_3840_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3839_, v___y_3783_);
return v___x_3840_;
}
else
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3848_; 
lean_dec_ref(v___x_3829_);
lean_dec_ref(v___y_3782_);
v_a_3841_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3843_ = v___x_3833_;
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3833_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
if (v_isShared_3844_ == 0)
{
v___x_3846_ = v___x_3843_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_a_3841_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3863_; 
lean_dec_ref(v___y_3791_);
lean_dec_ref(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec_ref(v___y_3784_);
lean_dec_ref(v___y_3782_);
lean_dec(v_decl_3746_);
v_a_3852_ = lean_ctor_get(v___x_3794_, 0);
v_isSharedCheck_3863_ = !lean_is_exclusive(v___x_3794_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3854_ = v___x_3794_;
v_isShared_3855_ = v_isSharedCheck_3863_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v___x_3794_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3863_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3861_; 
v___x_3856_ = lean_io_error_to_string(v_a_3852_);
v___x_3857_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3856_);
v___x_3858_ = l_Lean_MessageData_ofFormat(v___x_3857_);
v___x_3859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3859_, 0, v___y_3788_);
lean_ctor_set(v___x_3859_, 1, v___x_3858_);
if (v_isShared_3855_ == 0)
{
lean_ctor_set(v___x_3854_, 0, v___x_3859_);
v___x_3861_ = v___x_3854_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v___x_3859_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
return v___x_3861_;
}
}
}
}
v___jp_3864_:
{
lean_object* v_ref_3873_; uint8_t v___x_3874_; lean_object* v___x_3875_; 
v_ref_3873_ = lean_ctor_get(v___y_3867_, 2);
v___x_3874_ = 1;
lean_inc_ref(v___y_3871_);
v___x_3875_ = l_Lean_Environment_addConstAsync(v___y_3871_, v___y_3870_, v___y_3869_, v___y_3872_, v_hasTrace_3780_, v___x_3874_);
if (lean_obj_tag(v___x_3875_) == 0)
{
lean_object* v_a_3876_; lean_object* v_mainEnv_3877_; lean_object* v_asyncEnv_3878_; lean_object* v___f_3879_; lean_object* v___f_3880_; lean_object* v___x_3881_; 
v_a_3876_ = lean_ctor_get(v___x_3875_, 0);
lean_inc_n(v_a_3876_, 3);
lean_dec_ref_known(v___x_3875_, 1);
v_mainEnv_3877_ = lean_ctor_get(v_a_3876_, 0);
lean_inc_ref(v_mainEnv_3877_);
v_asyncEnv_3878_ = lean_ctor_get(v_a_3876_, 1);
lean_inc_ref_n(v_asyncEnv_3878_, 2);
lean_inc(v_ref_3873_);
lean_inc(v___y_3865_);
v___f_3879_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3879_, 0, v___y_3865_);
lean_closure_set(v___f_3879_, 1, v_a_3876_);
lean_closure_set(v___f_3879_, 2, v_ref_3873_);
lean_inc(v_decl_3746_);
v___f_3880_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3880_, 0, v_a_3876_);
lean_closure_set(v___f_3880_, 1, v_asyncEnv_3878_);
lean_closure_set(v___f_3880_, 2, v_decl_3746_);
v___x_3881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3881_, 0, v___y_3866_);
if (lean_obj_tag(v___y_3868_) == 0)
{
lean_inc_ref(v___x_3881_);
lean_inc(v_ref_3873_);
v___y_3782_ = v___y_3871_;
v___y_3783_ = v___y_3865_;
v___y_3784_ = v_asyncEnv_3878_;
v___y_3785_ = v___x_3874_;
v___y_3786_ = v___y_3867_;
v___y_3787_ = v_a_3876_;
v___y_3788_ = v_ref_3873_;
v___y_3789_ = v___f_3880_;
v___y_3790_ = v_mainEnv_3877_;
v___y_3791_ = v___f_3879_;
v___y_3792_ = v___x_3881_;
v___y_3793_ = v___x_3881_;
goto v___jp_3781_;
}
else
{
lean_inc(v_ref_3873_);
v___y_3782_ = v___y_3871_;
v___y_3783_ = v___y_3865_;
v___y_3784_ = v_asyncEnv_3878_;
v___y_3785_ = v___x_3874_;
v___y_3786_ = v___y_3867_;
v___y_3787_ = v_a_3876_;
v___y_3788_ = v_ref_3873_;
v___y_3789_ = v___f_3880_;
v___y_3790_ = v_mainEnv_3877_;
v___y_3791_ = v___f_3879_;
v___y_3792_ = v___x_3881_;
v___y_3793_ = v___y_3868_;
goto v___jp_3781_;
}
}
else
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3893_; 
lean_dec_ref(v___y_3871_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3866_);
lean_dec(v_decl_3746_);
v_a_3882_ = lean_ctor_get(v___x_3875_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v___x_3875_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3884_ = v___x_3875_;
v_isShared_3885_ = v_isSharedCheck_3893_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3875_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3893_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3891_; 
v___x_3886_ = lean_io_error_to_string(v_a_3882_);
v___x_3887_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3886_);
v___x_3888_ = l_Lean_MessageData_ofFormat(v___x_3887_);
lean_inc(v_ref_3873_);
v___x_3889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3889_, 0, v_ref_3873_);
lean_ctor_set(v___x_3889_, 1, v___x_3888_);
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 0, v___x_3889_);
v___x_3891_ = v___x_3884_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v___x_3889_);
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
v___jp_3894_:
{
lean_object* v___x_3901_; 
v___x_3901_ = lean_st_ref_get(v___y_3900_);
if (lean_obj_tag(v_exportedInfo_x3f_3898_) == 0)
{
lean_object* v_env_3902_; lean_object* v___x_3903_; 
v_env_3902_ = lean_ctor_get(v___x_3901_, 0);
lean_inc_ref(v_env_3902_);
lean_dec(v___x_3901_);
v___x_3903_ = lean_box(0);
v___y_3865_ = v___y_3900_;
v___y_3866_ = v___y_3897_;
v___y_3867_ = v___y_3899_;
v___y_3868_ = v_exportedInfo_x3f_3898_;
v___y_3869_ = v___y_3895_;
v___y_3870_ = v___y_3896_;
v___y_3871_ = v_env_3902_;
v___y_3872_ = v___x_3903_;
goto v___jp_3864_;
}
else
{
lean_object* v_env_3904_; lean_object* v_val_3905_; uint8_t v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; 
v_env_3904_ = lean_ctor_get(v___x_3901_, 0);
lean_inc_ref(v_env_3904_);
lean_dec(v___x_3901_);
v_val_3905_ = lean_ctor_get(v_exportedInfo_x3f_3898_, 0);
v___x_3906_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3905_);
v___x_3907_ = lean_box(v___x_3906_);
v___x_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3907_);
v___y_3865_ = v___y_3900_;
v___y_3866_ = v___y_3897_;
v___y_3867_ = v___y_3899_;
v___y_3868_ = v_exportedInfo_x3f_3898_;
v___y_3869_ = v___y_3895_;
v___y_3870_ = v___y_3896_;
v___y_3871_ = v_env_3904_;
v___y_3872_ = v___x_3908_;
goto v___jp_3864_;
}
}
v___jp_3909_:
{
lean_object* v___x_3915_; 
lean_inc_ref(v___y_3912_);
v___x_3915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3915_, 0, v___y_3912_);
v___y_3895_ = v___y_3910_;
v___y_3896_ = v___y_3911_;
v___y_3897_ = v___y_3912_;
v_exportedInfo_x3f_3898_ = v___x_3915_;
v___y_3899_ = v___y_3913_;
v___y_3900_ = v___y_3914_;
goto v___jp_3894_;
}
v___jp_3916_:
{
lean_object* v___x_3922_; 
lean_inc_ref(v___y_3919_);
v___x_3922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3922_, 0, v___y_3919_);
v___y_3895_ = v___y_3917_;
v___y_3896_ = v___y_3918_;
v___y_3897_ = v___y_3919_;
v_exportedInfo_x3f_3898_ = v___x_3922_;
v___y_3899_ = v___y_3920_;
v___y_3900_ = v___y_3921_;
goto v___jp_3894_;
}
v___jp_3925_:
{
lean_object* v___x_3930_; uint8_t v___x_3931_; 
v___x_3930_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_3931_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3928_, v_options_3927_, v___x_3930_);
if (v___x_3931_ == 0)
{
lean_object* v___x_3932_; 
v___x_3932_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3746_, v___y_3926_, v___y_3929_);
return v___x_3932_;
}
else
{
lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3933_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
v___x_3934_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3924_, v___x_3933_, v___y_3926_, v___y_3929_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v___x_3935_; 
lean_dec_ref_known(v___x_3934_, 1);
v___x_3935_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3746_, v___y_3926_, v___y_3929_);
return v___x_3935_;
}
else
{
lean_dec(v_decl_3746_);
return v___x_3934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___boxed(lean_object* v_decl_4798_, lean_object* v_forceExpose_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_){
_start:
{
uint8_t v_forceExpose_boxed_4803_; lean_object* v_res_4804_; 
v_forceExpose_boxed_4803_ = lean_unbox(v_forceExpose_4799_);
v_res_4804_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4798_, v_forceExpose_boxed_4803_, v_a_4800_, v_a_4801_);
lean_dec(v_a_4801_);
lean_dec_ref(v_a_4800_);
return v_res_4804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(lean_object* v_opt_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_){
_start:
{
lean_object* v___x_4809_; 
v___x_4809_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_4805_, v___y_4806_);
return v___x_4809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___boxed(lean_object* v_opt_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_){
_start:
{
lean_object* v_res_4814_; 
v_res_4814_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(v_opt_4810_, v___y_4811_, v___y_4812_);
lean_dec(v___y_4812_);
lean_dec_ref(v___y_4811_);
lean_dec_ref(v_opt_4810_);
return v_res_4814_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0(lean_object* v_x_4815_, lean_object* v_x_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_){
_start:
{
if (lean_obj_tag(v_x_4815_) == 0)
{
lean_object* v___x_4820_; lean_object* v___x_4821_; 
v___x_4820_ = l_List_reverse___redArg(v_x_4816_);
v___x_4821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4821_, 0, v___x_4820_);
return v___x_4821_;
}
else
{
lean_object* v_head_4822_; lean_object* v_tail_4823_; lean_object* v___x_4825_; uint8_t v_isShared_4826_; uint8_t v_isSharedCheck_4841_; 
v_head_4822_ = lean_ctor_get(v_x_4815_, 0);
v_tail_4823_ = lean_ctor_get(v_x_4815_, 1);
v_isSharedCheck_4841_ = !lean_is_exclusive(v_x_4815_);
if (v_isSharedCheck_4841_ == 0)
{
v___x_4825_ = v_x_4815_;
v_isShared_4826_ = v_isSharedCheck_4841_;
goto v_resetjp_4824_;
}
else
{
lean_inc(v_tail_4823_);
lean_inc(v_head_4822_);
lean_dec(v_x_4815_);
v___x_4825_ = lean_box(0);
v_isShared_4826_ = v_isSharedCheck_4841_;
goto v_resetjp_4824_;
}
v_resetjp_4824_:
{
lean_object* v___x_4827_; 
v___x_4827_ = l_Lean_snapshotEnvLinterOptions(v_head_4822_, v___y_4817_, v___y_4818_);
if (lean_obj_tag(v___x_4827_) == 0)
{
lean_object* v_a_4828_; lean_object* v___x_4830_; 
v_a_4828_ = lean_ctor_get(v___x_4827_, 0);
lean_inc(v_a_4828_);
lean_dec_ref_known(v___x_4827_, 1);
if (v_isShared_4826_ == 0)
{
lean_ctor_set(v___x_4825_, 1, v_x_4816_);
lean_ctor_set(v___x_4825_, 0, v_a_4828_);
v___x_4830_ = v___x_4825_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v_a_4828_);
lean_ctor_set(v_reuseFailAlloc_4832_, 1, v_x_4816_);
v___x_4830_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
v_x_4815_ = v_tail_4823_;
v_x_4816_ = v___x_4830_;
goto _start;
}
}
else
{
lean_object* v_a_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4840_; 
lean_del_object(v___x_4825_);
lean_dec(v_tail_4823_);
lean_dec(v_x_4816_);
v_a_4833_ = lean_ctor_get(v___x_4827_, 0);
v_isSharedCheck_4840_ = !lean_is_exclusive(v___x_4827_);
if (v_isSharedCheck_4840_ == 0)
{
v___x_4835_ = v___x_4827_;
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_a_4833_);
lean_dec(v___x_4827_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
lean_object* v___x_4838_; 
if (v_isShared_4836_ == 0)
{
v___x_4838_ = v___x_4835_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v_a_4833_);
v___x_4838_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
return v___x_4838_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0___boxed(lean_object* v_x_4842_, lean_object* v_x_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_){
_start:
{
lean_object* v_res_4847_; 
v_res_4847_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v_x_4842_, v_x_4843_, v___y_4844_, v___y_4845_);
lean_dec(v___y_4845_);
lean_dec_ref(v___y_4844_);
return v_res_4847_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object* v_decl_4848_, uint8_t v_forceExpose_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_){
_start:
{
lean_object* v___x_4853_; 
lean_inc(v_decl_4848_);
v___x_4853_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4848_, v_forceExpose_4849_, v_a_4850_, v_a_4851_);
if (lean_obj_tag(v___x_4853_) == 0)
{
lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; 
lean_dec_ref_known(v___x_4853_, 1);
v___x_4854_ = l_Lean_Declaration_getTopLevelNames(v_decl_4848_);
v___x_4855_ = lean_box(0);
v___x_4856_ = lean_box(0);
v___x_4857_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v___x_4854_, v___x_4855_, v_a_4850_, v_a_4851_);
if (lean_obj_tag(v___x_4857_) == 0)
{
lean_object* v___x_4859_; uint8_t v_isShared_4860_; uint8_t v_isSharedCheck_4864_; 
v_isSharedCheck_4864_ = !lean_is_exclusive(v___x_4857_);
if (v_isSharedCheck_4864_ == 0)
{
lean_object* v_unused_4865_; 
v_unused_4865_ = lean_ctor_get(v___x_4857_, 0);
lean_dec(v_unused_4865_);
v___x_4859_ = v___x_4857_;
v_isShared_4860_ = v_isSharedCheck_4864_;
goto v_resetjp_4858_;
}
else
{
lean_dec(v___x_4857_);
v___x_4859_ = lean_box(0);
v_isShared_4860_ = v_isSharedCheck_4864_;
goto v_resetjp_4858_;
}
v_resetjp_4858_:
{
lean_object* v___x_4862_; 
if (v_isShared_4860_ == 0)
{
lean_ctor_set(v___x_4859_, 0, v___x_4856_);
v___x_4862_ = v___x_4859_;
goto v_reusejp_4861_;
}
else
{
lean_object* v_reuseFailAlloc_4863_; 
v_reuseFailAlloc_4863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4863_, 0, v___x_4856_);
v___x_4862_ = v_reuseFailAlloc_4863_;
goto v_reusejp_4861_;
}
v_reusejp_4861_:
{
return v___x_4862_;
}
}
}
else
{
lean_object* v_a_4866_; lean_object* v___x_4868_; uint8_t v_isShared_4869_; uint8_t v_isSharedCheck_4873_; 
v_a_4866_ = lean_ctor_get(v___x_4857_, 0);
v_isSharedCheck_4873_ = !lean_is_exclusive(v___x_4857_);
if (v_isSharedCheck_4873_ == 0)
{
v___x_4868_ = v___x_4857_;
v_isShared_4869_ = v_isSharedCheck_4873_;
goto v_resetjp_4867_;
}
else
{
lean_inc(v_a_4866_);
lean_dec(v___x_4857_);
v___x_4868_ = lean_box(0);
v_isShared_4869_ = v_isSharedCheck_4873_;
goto v_resetjp_4867_;
}
v_resetjp_4867_:
{
lean_object* v___x_4871_; 
if (v_isShared_4869_ == 0)
{
v___x_4871_ = v___x_4868_;
goto v_reusejp_4870_;
}
else
{
lean_object* v_reuseFailAlloc_4872_; 
v_reuseFailAlloc_4872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4872_, 0, v_a_4866_);
v___x_4871_ = v_reuseFailAlloc_4872_;
goto v_reusejp_4870_;
}
v_reusejp_4870_:
{
return v___x_4871_;
}
}
}
}
else
{
lean_dec(v_decl_4848_);
return v___x_4853_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___boxed(lean_object* v_decl_4874_, lean_object* v_forceExpose_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_){
_start:
{
uint8_t v_forceExpose_boxed_4879_; lean_object* v_res_4880_; 
v_forceExpose_boxed_4879_ = lean_unbox(v_forceExpose_4875_);
v_res_4880_ = l_Lean_addDecl(v_decl_4874_, v_forceExpose_boxed_4879_, v_a_4876_, v_a_4877_);
lean_dec(v_a_4877_);
lean_dec_ref(v_a_4876_);
return v_res_4880_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(lean_object* v_as_x27_4881_, lean_object* v_b_4882_, lean_object* v___y_4883_){
_start:
{
if (lean_obj_tag(v_as_x27_4881_) == 0)
{
lean_object* v___x_4885_; 
v___x_4885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4885_, 0, v_b_4882_);
return v___x_4885_;
}
else
{
lean_object* v_head_4886_; lean_object* v_tail_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v_env_4890_; lean_object* v_nextMacroScope_4891_; lean_object* v_ngen_4892_; lean_object* v_auxDeclNGen_4893_; lean_object* v_traceState_4894_; lean_object* v_recordedDeps_4895_; lean_object* v_messages_4896_; lean_object* v_infoState_4897_; lean_object* v_snapshotTasks_4898_; lean_object* v___x_4900_; uint8_t v_isShared_4901_; uint8_t v_isSharedCheck_4909_; 
v_head_4886_ = lean_ctor_get(v_as_x27_4881_, 0);
v_tail_4887_ = lean_ctor_get(v_as_x27_4881_, 1);
v___x_4888_ = lean_box(0);
v___x_4889_ = lean_st_ref_take(v___y_4883_);
v_env_4890_ = lean_ctor_get(v___x_4889_, 0);
v_nextMacroScope_4891_ = lean_ctor_get(v___x_4889_, 1);
v_ngen_4892_ = lean_ctor_get(v___x_4889_, 2);
v_auxDeclNGen_4893_ = lean_ctor_get(v___x_4889_, 3);
v_traceState_4894_ = lean_ctor_get(v___x_4889_, 4);
v_recordedDeps_4895_ = lean_ctor_get(v___x_4889_, 6);
v_messages_4896_ = lean_ctor_get(v___x_4889_, 7);
v_infoState_4897_ = lean_ctor_get(v___x_4889_, 8);
v_snapshotTasks_4898_ = lean_ctor_get(v___x_4889_, 9);
v_isSharedCheck_4909_ = !lean_is_exclusive(v___x_4889_);
if (v_isSharedCheck_4909_ == 0)
{
lean_object* v_unused_4910_; 
v_unused_4910_ = lean_ctor_get(v___x_4889_, 5);
lean_dec(v_unused_4910_);
v___x_4900_ = v___x_4889_;
v_isShared_4901_ = v_isSharedCheck_4909_;
goto v_resetjp_4899_;
}
else
{
lean_inc(v_snapshotTasks_4898_);
lean_inc(v_infoState_4897_);
lean_inc(v_messages_4896_);
lean_inc(v_recordedDeps_4895_);
lean_inc(v_traceState_4894_);
lean_inc(v_auxDeclNGen_4893_);
lean_inc(v_ngen_4892_);
lean_inc(v_nextMacroScope_4891_);
lean_inc(v_env_4890_);
lean_dec(v___x_4889_);
v___x_4900_ = lean_box(0);
v_isShared_4901_ = v_isSharedCheck_4909_;
goto v_resetjp_4899_;
}
v_resetjp_4899_:
{
lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4905_; 
lean_inc(v_head_4886_);
v___x_4902_ = l_Lean_markMeta(v_env_4890_, v_head_4886_);
v___x_4903_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4901_ == 0)
{
lean_ctor_set(v___x_4900_, 5, v___x_4903_);
lean_ctor_set(v___x_4900_, 0, v___x_4902_);
v___x_4905_ = v___x_4900_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4908_; 
v_reuseFailAlloc_4908_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4908_, 0, v___x_4902_);
lean_ctor_set(v_reuseFailAlloc_4908_, 1, v_nextMacroScope_4891_);
lean_ctor_set(v_reuseFailAlloc_4908_, 2, v_ngen_4892_);
lean_ctor_set(v_reuseFailAlloc_4908_, 3, v_auxDeclNGen_4893_);
lean_ctor_set(v_reuseFailAlloc_4908_, 4, v_traceState_4894_);
lean_ctor_set(v_reuseFailAlloc_4908_, 5, v___x_4903_);
lean_ctor_set(v_reuseFailAlloc_4908_, 6, v_recordedDeps_4895_);
lean_ctor_set(v_reuseFailAlloc_4908_, 7, v_messages_4896_);
lean_ctor_set(v_reuseFailAlloc_4908_, 8, v_infoState_4897_);
lean_ctor_set(v_reuseFailAlloc_4908_, 9, v_snapshotTasks_4898_);
v___x_4905_ = v_reuseFailAlloc_4908_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
lean_object* v___x_4906_; 
v___x_4906_ = lean_st_ref_put(v___y_4883_, v___x_4905_);
v_as_x27_4881_ = v_tail_4887_;
v_b_4882_ = v___x_4888_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg___boxed(lean_object* v_as_x27_4911_, lean_object* v_b_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_){
_start:
{
lean_object* v_res_4915_; 
v_res_4915_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_4911_, v_b_4912_, v___y_4913_);
lean_dec(v___y_4913_);
lean_dec(v_as_x27_4911_);
return v_res_4915_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object* v_decl_4916_, uint8_t v_logCompileErrors_4917_, uint8_t v_markMeta_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_){
_start:
{
uint8_t v___x_4922_; lean_object* v___x_4923_; 
v___x_4922_ = 0;
lean_inc(v_decl_4916_);
v___x_4923_ = l_Lean_addDecl(v_decl_4916_, v___x_4922_, v_a_4919_, v_a_4920_);
if (lean_obj_tag(v___x_4923_) == 0)
{
lean_dec_ref_known(v___x_4923_, 1);
if (v_markMeta_4918_ == 0)
{
lean_object* v___x_4924_; 
v___x_4924_ = l_Lean_compileDecl(v_decl_4916_, v_logCompileErrors_4917_, v_a_4919_, v_a_4920_);
return v___x_4924_;
}
else
{
lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; 
lean_inc(v_decl_4916_);
v___x_4925_ = l_Lean_Declaration_getNames(v_decl_4916_);
v___x_4926_ = lean_box(0);
v___x_4927_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v___x_4925_, v___x_4926_, v_a_4920_);
lean_dec(v___x_4925_);
lean_dec_ref(v___x_4927_);
v___x_4928_ = l_Lean_compileDecl(v_decl_4916_, v_logCompileErrors_4917_, v_a_4919_, v_a_4920_);
return v___x_4928_;
}
}
else
{
lean_dec(v_decl_4916_);
return v___x_4923_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___boxed(lean_object* v_decl_4929_, lean_object* v_logCompileErrors_4930_, lean_object* v_markMeta_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_){
_start:
{
uint8_t v_logCompileErrors_boxed_4935_; uint8_t v_markMeta_boxed_4936_; lean_object* v_res_4937_; 
v_logCompileErrors_boxed_4935_ = lean_unbox(v_logCompileErrors_4930_);
v_markMeta_boxed_4936_ = lean_unbox(v_markMeta_4931_);
v_res_4937_ = l_Lean_addAndCompile(v_decl_4929_, v_logCompileErrors_boxed_4935_, v_markMeta_boxed_4936_, v_a_4932_, v_a_4933_);
lean_dec(v_a_4933_);
lean_dec_ref(v_a_4932_);
return v_res_4937_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(lean_object* v_as_4938_, lean_object* v_as_x27_4939_, lean_object* v_b_4940_, lean_object* v_a_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_){
_start:
{
lean_object* v___x_4945_; 
v___x_4945_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_4939_, v_b_4940_, v___y_4943_);
return v___x_4945_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___boxed(lean_object* v_as_4946_, lean_object* v_as_x27_4947_, lean_object* v_b_4948_, lean_object* v_a_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_){
_start:
{
lean_object* v_res_4953_; 
v_res_4953_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(v_as_4946_, v_as_x27_4947_, v_b_4948_, v_a_4949_, v___y_4950_, v___y_4951_);
lean_dec(v___y_4951_);
lean_dec_ref(v___y_4950_);
lean_dec(v_as_x27_4947_);
lean_dec(v_as_4946_);
return v_res_4953_;
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
