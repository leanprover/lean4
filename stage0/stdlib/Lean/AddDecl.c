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
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___y_479_; uint8_t v___y_480_; lean_object* v___y_481_; lean_object* v_toCold_482_; lean_object* v___y_483_; lean_object* v___y_512_; lean_object* v___y_513_; uint8_t v___y_514_; lean_object* v___y_515_; uint8_t v___y_516_; lean_object* v___y_517_; uint8_t v___y_518_; lean_object* v___y_519_; lean_object* v___y_539_; lean_object* v___y_540_; uint8_t v___y_541_; lean_object* v___y_542_; uint8_t v___y_543_; uint8_t v___y_544_; lean_object* v___y_545_; uint8_t v___y_549_; uint8_t v___y_550_; uint8_t v___x_560_; uint8_t v___y_562_; uint8_t v___x_568_; 
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
lean_ctor_set(v___x_487_, 1, v___y_477_);
lean_inc_ref(v___y_479_);
lean_inc_ref(v___y_478_);
v___x_488_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_488_, 0, v___y_478_);
lean_ctor_set(v___x_488_, 1, v___y_476_);
lean_ctor_set(v___x_488_, 2, v___y_481_);
lean_ctor_set(v___x_488_, 3, v___y_479_);
lean_ctor_set(v___x_488_, 4, v___x_487_);
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*5, v___y_475_);
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*5 + 1, v___y_480_);
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
v_fileName_520_ = lean_ctor_get(v___y_515_, 0);
v_fileMap_521_ = lean_ctor_get(v___y_515_, 1);
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
v___x_528_ = l_Lean_FileMap_toPosition(v_fileMap_521_, v___y_517_);
lean_dec(v___y_517_);
v___x_529_ = l_Lean_FileMap_toPosition(v_fileMap_521_, v___y_519_);
lean_dec(v___y_519_);
v___x_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
v___x_531_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
if (v___y_518_ == 0)
{
lean_del_object(v___x_526_);
lean_dec_ref(v___y_512_);
v___y_475_ = v___y_514_;
v___y_476_ = v___x_528_;
v___y_477_ = v_a_524_;
v___y_478_ = v_fileName_520_;
v___y_479_ = v___x_531_;
v___y_480_ = v___y_516_;
v___y_481_ = v___x_530_;
v_toCold_482_ = v___y_513_;
v___y_483_ = v___y_472_;
goto v___jp_474_;
}
else
{
uint8_t v___x_532_; 
lean_inc(v_a_524_);
v___x_532_ = l_Lean_MessageData_hasTag(v___y_512_, v_a_524_);
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
v___y_476_ = v___x_528_;
v___y_477_ = v_a_524_;
v___y_478_ = v_fileName_520_;
v___y_479_ = v___x_531_;
v___y_480_ = v___y_516_;
v___y_481_ = v___x_530_;
v_toCold_482_ = v___y_513_;
v___y_483_ = v___y_472_;
goto v___jp_474_;
}
}
}
}
v___jp_538_:
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_Syntax_getTailPos_x3f(v___y_542_, v___y_543_);
lean_dec(v___y_542_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_inc(v___y_545_);
v___y_512_ = v___y_539_;
v___y_513_ = v___y_540_;
v___y_514_ = v___y_543_;
v___y_515_ = v___y_540_;
v___y_516_ = v___y_544_;
v___y_517_ = v___y_545_;
v___y_518_ = v___y_541_;
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
v___y_513_ = v___y_540_;
v___y_514_ = v___y_543_;
v___y_515_ = v___y_540_;
v___y_516_ = v___y_544_;
v___y_517_ = v___y_545_;
v___y_518_ = v___y_541_;
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
v___y_539_ = v___f_555_;
v___y_540_ = v_toCold_551_;
v___y_541_ = v_suppressElabErrors_553_;
v___y_542_ = v_ref_556_;
v___y_543_ = v___y_549_;
v___y_544_ = v___y_550_;
v___y_545_ = v___x_558_;
goto v___jp_538_;
}
else
{
lean_object* v_val_559_; 
v_val_559_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_val_559_);
lean_dec_ref_known(v___x_557_, 1);
v___y_539_ = v___f_555_;
v___y_540_ = v_toCold_551_;
v___y_541_ = v_suppressElabErrors_553_;
v___y_542_ = v_ref_556_;
v___y_543_ = v___y_549_;
v___y_544_ = v___y_550_;
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
v___x_1514_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
lean_ctor_set(v___x_1514_, 2, v___x_1513_);
lean_ctor_set(v___x_1514_, 3, v___x_1513_);
lean_ctor_set(v___x_1514_, 4, v___x_1513_);
lean_ctor_set(v___x_1514_, 5, v___x_1513_);
lean_ctor_set(v___x_1514_, 6, v___x_1513_);
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
lean_object* v_toCold_2288_; lean_object* v_currRecDepth_2289_; lean_object* v_ref_2290_; uint16_t v_optionFlags_2291_; uint8_t v_suppressElabErrors_2292_; uint8_t v_checkDeprecated_2293_; uint8_t v_isRecordingDeps_2294_; lean_object* v_ref_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v_traceState_2298_; lean_object* v_traces_2299_; lean_object* v___x_2300_; size_t v_sz_2301_; size_t v___x_2302_; lean_object* v___x_2303_; lean_object* v_msg_2304_; lean_object* v___x_2305_; lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2344_; 
v_toCold_2288_ = lean_ctor_get(v___y_2285_, 0);
v_currRecDepth_2289_ = lean_ctor_get(v___y_2285_, 1);
v_ref_2290_ = lean_ctor_get(v___y_2285_, 2);
v_optionFlags_2291_ = lean_ctor_get_uint16(v___y_2285_, sizeof(void*)*3);
v_suppressElabErrors_2292_ = lean_ctor_get_uint8(v___y_2285_, sizeof(void*)*3 + 2);
v_checkDeprecated_2293_ = lean_ctor_get_uint8(v___y_2285_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2294_ = lean_ctor_get_uint8(v___y_2285_, sizeof(void*)*3 + 4);
v_ref_2295_ = l_Lean_replaceRef(v_ref_2283_, v_ref_2290_);
lean_inc(v_currRecDepth_2289_);
lean_inc_ref(v_toCold_2288_);
v___x_2296_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2296_, 0, v_toCold_2288_);
lean_ctor_set(v___x_2296_, 1, v_currRecDepth_2289_);
lean_ctor_set(v___x_2296_, 2, v_ref_2295_);
lean_ctor_set_uint16(v___x_2296_, sizeof(void*)*3, v_optionFlags_2291_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*3 + 2, v_suppressElabErrors_2292_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*3 + 3, v_checkDeprecated_2293_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*3 + 4, v_isRecordingDeps_2294_);
v___x_2297_ = lean_st_ref_get(v___y_2286_);
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
lean_ctor_set(v_msg_2304_, 0, v_data_2282_);
lean_ctor_set(v_msg_2304_, 1, v_msg_2284_);
lean_ctor_set(v_msg_2304_, 2, v___x_2303_);
v___x_2305_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2304_, v___x_2296_, v___y_2286_);
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
v___x_2310_ = lean_st_ref_take(v___y_2286_);
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
lean_ctor_set(v___x_2329_, 0, v_ref_2283_);
lean_ctor_set(v___x_2329_, 1, v_a_2306_);
v___x_2330_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2281_, v___x_2329_);
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
v___x_2335_ = lean_st_ref_put(v___y_2286_, v___x_2334_);
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
lean_inc(v___y_2402_);
v___x_2404_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_oldTraces_2392_, v_data_2403_, v___y_2402_, v___y_2401_, v___y_2395_, v___y_2396_);
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
v___y_2401_ = v_a_2412_;
v___y_2402_ = v___y_2411_;
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
v___y_2401_ = v_a_2412_;
v___y_2402_ = v___y_2411_;
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
lean_object* v___y_2501_; lean_object* v_a_2502_; lean_object* v___y_2515_; lean_object* v_a_2516_; lean_object* v_toCold_2528_; lean_object* v_options_2529_; uint8_t v_hasTrace_2530_; 
v_toCold_2528_ = lean_ctor_get(v___y_2497_, 0);
v_options_2529_ = lean_ctor_get(v_toCold_2528_, 2);
v_hasTrace_2530_ = lean_ctor_get_uint8(v_options_2529_, sizeof(void*)*1);
if (v_hasTrace_2530_ == 0)
{
lean_object* v_cancelTk_x3f_2531_; lean_object* v___x_2532_; 
lean_dec_ref(v___f_2496_);
lean_dec_ref(v___x_2495_);
lean_dec(v___x_2493_);
v_cancelTk_x3f_2531_ = lean_ctor_get(v_toCold_2528_, 10);
lean_inc(v_decl_2492_);
v___x_2532_ = l_Lean_warnIfUsesSorry(v_decl_2492_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v___x_2533_; lean_object* v_env_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
lean_dec_ref_known(v___x_2532_, 1);
v___x_2533_ = lean_st_ref_get(v___y_2498_);
v_env_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc_ref(v_env_2534_);
lean_dec(v___x_2533_);
v___x_2535_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2497_);
v___x_2536_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2534_, v___x_2535_, v_decl_2492_, v_cancelTk_x3f_2531_);
lean_dec_ref(v___x_2535_);
v___x_2537_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2536_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v_a_2538_; lean_object* v___x_2539_; 
lean_dec(v_decl_2492_);
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc(v_a_2538_);
lean_dec_ref_known(v___x_2537_, 1);
v___x_2539_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2538_, v___y_2498_);
return v___x_2539_;
}
else
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
v_a_2540_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2537_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2537_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
lean_inc(v_a_2540_);
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
v___y_2515_ = v___x_2545_;
v_a_2516_ = v_a_2540_;
goto v___jp_2514_;
}
}
}
}
else
{
lean_dec(v_decl_2492_);
return v___x_2532_;
}
}
else
{
lean_object* v_cancelTk_x3f_2548_; lean_object* v_inheritedTraceOptions_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; uint8_t v___x_2552_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v_a_2556_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v_a_2571_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v_a_2576_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v_a_2584_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v_a_2596_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v_a_2601_; 
v_cancelTk_x3f_2548_ = lean_ctor_get(v_toCold_2528_, 10);
v_inheritedTraceOptions_2549_ = lean_ctor_get(v_toCold_2528_, 11);
v___x_2550_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v___x_2493_);
v___x_2551_ = l_Lean_Name_append(v___x_2550_, v___x_2493_);
v___x_2552_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2549_, v_options_2529_, v___x_2551_);
lean_dec(v___x_2551_);
if (v___x_2552_ == 0)
{
lean_object* v___x_2649_; uint8_t v___x_2650_; 
v___x_2649_ = l_Lean_trace_profiler;
v___x_2650_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2529_, v___x_2649_);
if (v___x_2650_ == 0)
{
lean_object* v___x_2651_; 
lean_dec_ref(v___f_2496_);
lean_dec_ref(v___x_2495_);
lean_dec(v___x_2493_);
lean_inc(v_decl_2492_);
v___x_2651_ = l_Lean_warnIfUsesSorry(v_decl_2492_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v___x_2652_; lean_object* v_env_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
lean_dec_ref_known(v___x_2651_, 1);
v___x_2652_ = lean_st_ref_get(v___y_2498_);
v_env_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc_ref(v_env_2653_);
lean_dec(v___x_2652_);
v___x_2654_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2497_);
v___x_2655_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2653_, v___x_2654_, v_decl_2492_, v_cancelTk_x3f_2548_);
lean_dec_ref(v___x_2654_);
v___x_2656_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2655_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2658_; 
lean_dec(v_decl_2492_);
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___x_2656_, 1);
v___x_2658_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2657_, v___y_2498_);
return v___x_2658_;
}
else
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
v_a_2659_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2661_ = v___x_2656_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2656_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
lean_inc(v_a_2659_);
if (v_isShared_2662_ == 0)
{
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2659_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
v___y_2501_ = v___x_2664_;
v_a_2502_ = v_a_2659_;
goto v___jp_2500_;
}
}
}
}
else
{
lean_dec(v_decl_2492_);
return v___x_2651_;
}
}
else
{
goto v___jp_2606_;
}
}
else
{
goto v___jp_2606_;
}
v___jp_2553_:
{
lean_object* v___x_2557_; double v___x_2558_; double v___x_2559_; double v___x_2560_; double v___x_2561_; double v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2557_ = lean_io_mono_nanos_now();
v___x_2558_ = lean_float_of_nat(v___y_2555_);
v___x_2559_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_2560_ = lean_float_div(v___x_2558_, v___x_2559_);
v___x_2561_ = lean_float_of_nat(v___x_2557_);
v___x_2562_ = lean_float_div(v___x_2561_, v___x_2559_);
v___x_2563_ = lean_box_float(v___x_2560_);
v___x_2564_ = lean_box_float(v___x_2562_);
v___x_2565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2563_);
lean_ctor_set(v___x_2565_, 1, v___x_2564_);
v___x_2566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2566_, 0, v_a_2556_);
lean_ctor_set(v___x_2566_, 1, v___x_2565_);
v___x_2567_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2493_, v___x_2494_, v___x_2495_, v_options_2529_, v___x_2552_, v___y_2554_, v___f_2496_, v___x_2566_, v___y_2497_, v___y_2498_);
return v___x_2567_;
}
v___jp_2568_:
{
lean_object* v___x_2572_; 
v___x_2572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2572_, 0, v_a_2571_);
v___y_2554_ = v___y_2569_;
v___y_2555_ = v___y_2570_;
v_a_2556_ = v___x_2572_;
goto v___jp_2553_;
}
v___jp_2573_:
{
uint8_t v___x_2577_; 
v___x_2577_ = l_Lean_Exception_isInterrupt(v_a_2576_);
if (v___x_2577_ == 0)
{
uint8_t v___x_2578_; 
lean_inc_ref(v_a_2576_);
v___x_2578_ = l_Lean_Exception_isRuntime(v_a_2576_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2579_; 
v___x_2579_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2492_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_dec_ref_known(v___x_2579_, 1);
v___y_2569_ = v___y_2574_;
v___y_2570_ = v___y_2575_;
v_a_2571_ = v_a_2576_;
goto v___jp_2568_;
}
else
{
lean_object* v_a_2580_; 
lean_dec_ref(v_a_2576_);
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2580_);
lean_dec_ref_known(v___x_2579_, 1);
v___y_2569_ = v___y_2574_;
v___y_2570_ = v___y_2575_;
v_a_2571_ = v_a_2580_;
goto v___jp_2568_;
}
}
else
{
lean_dec(v_decl_2492_);
v___y_2569_ = v___y_2574_;
v___y_2570_ = v___y_2575_;
v_a_2571_ = v_a_2576_;
goto v___jp_2568_;
}
}
else
{
lean_dec(v_decl_2492_);
v___y_2569_ = v___y_2574_;
v___y_2570_ = v___y_2575_;
v_a_2571_ = v_a_2576_;
goto v___jp_2568_;
}
}
v___jp_2581_:
{
lean_object* v___x_2585_; double v___x_2586_; double v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2585_ = lean_io_get_num_heartbeats();
v___x_2586_ = lean_float_of_nat(v___y_2583_);
v___x_2587_ = lean_float_of_nat(v___x_2585_);
v___x_2588_ = lean_box_float(v___x_2586_);
v___x_2589_ = lean_box_float(v___x_2587_);
v___x_2590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2588_);
lean_ctor_set(v___x_2590_, 1, v___x_2589_);
v___x_2591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2591_, 0, v_a_2584_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
v___x_2592_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2493_, v___x_2494_, v___x_2495_, v_options_2529_, v___x_2552_, v___y_2582_, v___f_2496_, v___x_2591_, v___y_2497_, v___y_2498_);
return v___x_2592_;
}
v___jp_2593_:
{
lean_object* v___x_2597_; 
v___x_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2597_, 0, v_a_2596_);
v___y_2582_ = v___y_2594_;
v___y_2583_ = v___y_2595_;
v_a_2584_ = v___x_2597_;
goto v___jp_2581_;
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
if (v___x_2603_ == 0)
{
lean_object* v___x_2604_; 
v___x_2604_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2492_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_dec_ref_known(v___x_2604_, 1);
v___y_2594_ = v___y_2599_;
v___y_2595_ = v___y_2600_;
v_a_2596_ = v_a_2601_;
goto v___jp_2593_;
}
else
{
lean_object* v_a_2605_; 
lean_dec_ref(v_a_2601_);
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_a_2605_);
lean_dec_ref_known(v___x_2604_, 1);
v___y_2594_ = v___y_2599_;
v___y_2595_ = v___y_2600_;
v_a_2596_ = v_a_2605_;
goto v___jp_2593_;
}
}
else
{
lean_dec(v_decl_2492_);
v___y_2594_ = v___y_2599_;
v___y_2595_ = v___y_2600_;
v_a_2596_ = v_a_2601_;
goto v___jp_2593_;
}
}
else
{
lean_dec(v_decl_2492_);
v___y_2594_ = v___y_2599_;
v___y_2595_ = v___y_2600_;
v_a_2596_ = v_a_2601_;
goto v___jp_2593_;
}
}
v___jp_2606_:
{
lean_object* v___x_2607_; lean_object* v_a_2608_; lean_object* v___x_2609_; uint8_t v___x_2610_; 
v___x_2607_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2498_);
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_a_2608_);
lean_dec_ref(v___x_2607_);
v___x_2609_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2610_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2529_, v___x_2609_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2611_ = lean_io_mono_nanos_now();
lean_inc(v_decl_2492_);
v___x_2612_ = l_Lean_warnIfUsesSorry(v_decl_2492_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v___x_2613_; lean_object* v_env_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
lean_dec_ref_known(v___x_2612_, 1);
v___x_2613_ = lean_st_ref_get(v___y_2498_);
v_env_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc_ref(v_env_2614_);
lean_dec(v___x_2613_);
v___x_2615_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2497_);
v___x_2616_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2614_, v___x_2615_, v_decl_2492_, v_cancelTk_x3f_2548_);
lean_dec_ref(v___x_2615_);
v___x_2617_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2616_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; lean_object* v___x_2619_; lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_dec(v_decl_2492_);
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_a_2618_);
lean_dec_ref_known(v___x_2617_, 1);
v___x_2619_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2618_, v___y_2498_);
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2619_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2619_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
lean_ctor_set_tag(v___x_2622_, 1);
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
v___y_2554_ = v_a_2608_;
v___y_2555_ = v___x_2611_;
v_a_2556_ = v___x_2625_;
goto v___jp_2553_;
}
}
}
else
{
lean_object* v_a_2628_; 
v_a_2628_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_a_2628_);
lean_dec_ref_known(v___x_2617_, 1);
v___y_2574_ = v_a_2608_;
v___y_2575_ = v___x_2611_;
v_a_2576_ = v_a_2628_;
goto v___jp_2573_;
}
}
else
{
lean_object* v_a_2629_; 
lean_dec(v_decl_2492_);
v_a_2629_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_a_2629_);
lean_dec_ref_known(v___x_2612_, 1);
v___y_2569_ = v_a_2608_;
v___y_2570_ = v___x_2611_;
v_a_2571_ = v_a_2629_;
goto v___jp_2568_;
}
}
else
{
lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2630_ = lean_io_get_num_heartbeats();
lean_inc(v_decl_2492_);
v___x_2631_ = l_Lean_warnIfUsesSorry(v_decl_2492_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v___x_2632_; lean_object* v_env_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
lean_dec_ref_known(v___x_2631_, 1);
v___x_2632_ = lean_st_ref_get(v___y_2498_);
v_env_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc_ref(v_env_2633_);
lean_dec(v___x_2632_);
v___x_2634_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2497_);
v___x_2635_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2633_, v___x_2634_, v_decl_2492_, v_cancelTk_x3f_2548_);
lean_dec_ref(v___x_2634_);
v___x_2636_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2635_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; lean_object* v___x_2638_; lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
lean_dec(v_decl_2492_);
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_a_2637_);
lean_dec_ref_known(v___x_2636_, 1);
v___x_2638_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2637_, v___y_2498_);
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2638_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2638_);
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
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2639_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
v___y_2582_ = v_a_2608_;
v___y_2583_ = v___x_2630_;
v_a_2584_ = v___x_2644_;
goto v___jp_2581_;
}
}
}
else
{
lean_object* v_a_2647_; 
v_a_2647_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_a_2647_);
lean_dec_ref_known(v___x_2636_, 1);
v___y_2599_ = v_a_2608_;
v___y_2600_ = v___x_2630_;
v_a_2601_ = v_a_2647_;
goto v___jp_2598_;
}
}
else
{
lean_object* v_a_2648_; 
lean_dec(v_decl_2492_);
v_a_2648_ = lean_ctor_get(v___x_2631_, 0);
lean_inc(v_a_2648_);
lean_dec_ref_known(v___x_2631_, 1);
v___y_2594_ = v_a_2608_;
v___y_2595_ = v___x_2630_;
v_a_2596_ = v_a_2648_;
goto v___jp_2593_;
}
}
}
}
v___jp_2500_:
{
uint8_t v___x_2503_; 
v___x_2503_ = l_Lean_Exception_isInterrupt(v_a_2502_);
if (v___x_2503_ == 0)
{
uint8_t v___x_2504_; 
lean_inc_ref(v_a_2502_);
v___x_2504_ = l_Lean_Exception_isRuntime(v_a_2502_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2505_; 
lean_dec_ref(v___y_2501_);
v___x_2505_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2492_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2512_ == 0)
{
lean_object* v_unused_2513_; 
v_unused_2513_ = lean_ctor_get(v___x_2505_, 0);
lean_dec(v_unused_2513_);
v___x_2507_ = v___x_2505_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_dec(v___x_2505_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
lean_ctor_set_tag(v___x_2507_, 1);
lean_ctor_set(v___x_2507_, 0, v_a_2502_);
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2502_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
else
{
lean_dec_ref(v_a_2502_);
return v___x_2505_;
}
}
else
{
lean_dec_ref(v_a_2502_);
lean_dec(v_decl_2492_);
return v___y_2501_;
}
}
else
{
lean_dec_ref(v_a_2502_);
lean_dec(v_decl_2492_);
return v___y_2501_;
}
}
v___jp_2514_:
{
uint8_t v___x_2517_; 
v___x_2517_ = l_Lean_Exception_isInterrupt(v_a_2516_);
if (v___x_2517_ == 0)
{
uint8_t v___x_2518_; 
lean_inc_ref(v_a_2516_);
v___x_2518_ = l_Lean_Exception_isRuntime(v_a_2516_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2519_; 
lean_dec_ref(v___y_2515_);
v___x_2519_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2492_, v___y_2497_, v___y_2498_);
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
lean_ctor_set(v___x_2521_, 0, v_a_2516_);
v___x_2524_ = v___x_2521_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2516_);
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
lean_dec_ref(v_a_2516_);
return v___x_2519_;
}
}
else
{
lean_dec_ref(v_a_2516_);
lean_dec(v_decl_2492_);
return v___y_2515_;
}
}
else
{
lean_dec_ref(v_a_2516_);
lean_dec(v_decl_2492_);
return v___y_2515_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed(lean_object* v_decl_2667_, lean_object* v___x_2668_, lean_object* v___x_2669_, lean_object* v___x_2670_, lean_object* v___f_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
uint8_t v___x_7780__boxed_2675_; lean_object* v_res_2676_; 
v___x_7780__boxed_2675_ = lean_unbox(v___x_2669_);
v_res_2676_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(v_decl_2667_, v___x_2668_, v___x_7780__boxed_2675_, v___x_2670_, v___f_2671_, v___y_2672_, v___y_2673_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(lean_object* v_decl_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_){
_start:
{
lean_object* v___f_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; uint8_t v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___f_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
lean_inc(v_decl_2681_);
v___f_2685_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2685_, 0, v_decl_2681_);
v___x_2686_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2682_);
v___x_2687_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__0));
v___x_2688_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__2));
v___x_2689_ = 1;
v___x_2690_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2691_ = lean_box(v___x_2689_);
v___f_2692_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed), 8, 5);
lean_closure_set(v___f_2692_, 0, v_decl_2681_);
lean_closure_set(v___f_2692_, 1, v___x_2688_);
lean_closure_set(v___f_2692_, 2, v___x_2691_);
lean_closure_set(v___f_2692_, 3, v___x_2690_);
lean_closure_set(v___f_2692_, 4, v___f_2685_);
v___x_2693_ = lean_box(0);
v___x_2694_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v___x_2687_, v___x_2686_, v___f_2692_, v___x_2693_, v_a_2682_, v_a_2683_);
lean_dec_ref(v___x_2686_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___boxed(lean_object* v_decl_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2695_, v_a_2696_, v_a_2697_);
lean_dec(v_a_2697_);
lean_dec_ref(v_a_2696_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(lean_object* v_00_u03b1_2700_, lean_object* v_x_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v___x_2705_; 
v___x_2705_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_x_2701_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2706_, lean_object* v_x_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(v_00_u03b1_2706_, v_x_2707_, v___y_2708_, v___y_2709_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(lean_object* v___y_2712_, lean_object* v_a_2713_, lean_object* v_ref_2714_, lean_object* v_a_x3f_2715_){
_start:
{
lean_object* v___x_2717_; lean_object* v_env_2718_; lean_object* v___x_2719_; 
v___x_2717_ = lean_st_ref_get(v___y_2712_);
v_env_2718_ = lean_ctor_get(v___x_2717_, 0);
lean_inc_ref(v_env_2718_);
lean_dec(v___x_2717_);
v___x_2719_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2713_, v_env_2718_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_dec(v_ref_2714_);
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2719_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2719_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2739_; 
v_a_2728_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2730_ = v___x_2719_;
v_isShared_2731_ = v_isSharedCheck_2739_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2719_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2739_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2737_; 
v___x_2732_ = lean_io_error_to_string(v_a_2728_);
v___x_2733_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2732_);
v___x_2734_ = l_Lean_MessageData_ofFormat(v___x_2733_);
v___x_2735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2735_, 0, v_ref_2714_);
lean_ctor_set(v___x_2735_, 1, v___x_2734_);
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 0, v___x_2735_);
v___x_2737_ = v___x_2730_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v___x_2735_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed(lean_object* v___y_2740_, lean_object* v_a_2741_, lean_object* v_ref_2742_, lean_object* v_a_x3f_2743_, lean_object* v___y_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2740_, v_a_2741_, v_ref_2742_, v_a_x3f_2743_);
lean_dec(v_a_x3f_2743_);
lean_dec(v___y_2740_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v_a_2748_, lean_object* v_a_x3f_2749_){
_start:
{
lean_object* v___x_2751_; lean_object* v_env_2752_; lean_object* v_ref_2753_; lean_object* v___x_2754_; 
v___x_2751_ = lean_st_ref_get(v___y_2746_);
v_env_2752_ = lean_ctor_get(v___x_2751_, 0);
lean_inc_ref(v_env_2752_);
lean_dec(v___x_2751_);
v_ref_2753_ = lean_ctor_get(v___y_2747_, 2);
v___x_2754_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2748_, v_env_2752_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2754_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2754_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2774_; 
v_a_2763_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2765_ = v___x_2754_;
v_isShared_2766_ = v_isSharedCheck_2774_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2754_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2774_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2772_; 
v___x_2767_ = lean_io_error_to_string(v_a_2763_);
v___x_2768_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2767_);
v___x_2769_ = l_Lean_MessageData_ofFormat(v___x_2768_);
lean_inc(v_ref_2753_);
v___x_2770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2770_, 0, v_ref_2753_);
lean_ctor_set(v___x_2770_, 1, v___x_2769_);
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 0, v___x_2770_);
v___x_2772_ = v___x_2765_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2770_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___boxed(lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v_a_2777_, lean_object* v_a_x3f_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v___y_2775_, v___y_2776_, v_a_2777_, v_a_x3f_2778_);
lean_dec(v_a_x3f_2778_);
lean_dec_ref(v___y_2776_);
lean_dec(v___y_2775_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(lean_object* v_a_2781_, lean_object* v_asyncEnv_2782_, lean_object* v_decl_2783_, lean_object* v_x_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v___x_2788_; lean_object* v_r_2789_; 
v___x_2788_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_asyncEnv_2782_, v___y_2786_);
lean_dec_ref(v___x_2788_);
v_r_2789_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2783_, v___y_2785_, v___y_2786_);
if (lean_obj_tag(v_r_2789_) == 0)
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2806_; 
v_a_2790_ = lean_ctor_get(v_r_2789_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v_r_2789_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2792_ = v_r_2789_;
v_isShared_2793_ = v_isSharedCheck_2806_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v_r_2789_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2806_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2795_; 
lean_inc(v_a_2790_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set_tag(v___x_2792_, 1);
v___x_2795_ = v___x_2792_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2790_);
v___x_2795_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
lean_object* v___x_2796_; 
v___x_2796_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v___y_2786_, v___y_2785_, v_a_2781_, v___x_2795_);
lean_dec_ref(v___x_2795_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2803_ == 0)
{
lean_object* v_unused_2804_; 
v_unused_2804_ = lean_ctor_get(v___x_2796_, 0);
lean_dec(v_unused_2804_);
v___x_2798_ = v___x_2796_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_dec(v___x_2796_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 0, v_a_2790_);
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2790_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
else
{
lean_dec(v_a_2790_);
return v___x_2796_;
}
}
}
}
else
{
lean_object* v_a_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v_a_2807_ = lean_ctor_get(v_r_2789_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v_r_2789_, 1);
v___x_2808_ = lean_box(0);
v___x_2809_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v___y_2786_, v___y_2785_, v_a_2781_, v___x_2808_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
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
lean_ctor_set(v___x_2811_, 0, v_a_2807_);
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2807_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
else
{
lean_dec(v_a_2807_);
return v___x_2809_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed(lean_object* v_a_2818_, lean_object* v_asyncEnv_2819_, lean_object* v_decl_2820_, lean_object* v_x_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(v_a_2818_, v_asyncEnv_2819_, v_decl_2820_, v_x_2821_, v___y_2822_, v___y_2823_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec_ref(v_x_2821_);
return v_res_2825_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__0));
v___x_2828_ = l_Lean_stringToMessageData(v___x_2827_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(lean_object* v_decl_2829_, lean_object* v_x_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2834_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1);
v___x_2835_ = l_Lean_Declaration_getNames(v_decl_2829_);
v___x_2836_ = lean_box(0);
v___x_2837_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2835_, v___x_2836_);
v___x_2838_ = l_Lean_MessageData_ofList(v___x_2837_);
v___x_2839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2834_);
lean_ctor_set(v___x_2839_, 1, v___x_2838_);
v___x_2840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2839_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed(lean_object* v_decl_2841_, lean_object* v_x_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_2841_, v_x_2842_, v___y_2843_, v___y_2844_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec_ref(v_x_2842_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(lean_object* v_cls_2849_, lean_object* v_msg_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v_ref_2854_; lean_object* v___x_2855_; lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2901_; 
v_ref_2854_ = lean_ctor_get(v___y_2851_, 2);
v___x_2855_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2850_, v___y_2851_, v___y_2852_);
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2858_ = v___x_2855_;
v_isShared_2859_ = v_isSharedCheck_2901_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2855_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2901_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2860_; lean_object* v_traceState_2861_; lean_object* v_env_2862_; lean_object* v_nextMacroScope_2863_; lean_object* v_ngen_2864_; lean_object* v_auxDeclNGen_2865_; lean_object* v_cache_2866_; lean_object* v_recordedDeps_2867_; lean_object* v_messages_2868_; lean_object* v_infoState_2869_; lean_object* v_snapshotTasks_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2900_; 
v___x_2860_ = lean_st_ref_take(v___y_2852_);
v_traceState_2861_ = lean_ctor_get(v___x_2860_, 4);
v_env_2862_ = lean_ctor_get(v___x_2860_, 0);
v_nextMacroScope_2863_ = lean_ctor_get(v___x_2860_, 1);
v_ngen_2864_ = lean_ctor_get(v___x_2860_, 2);
v_auxDeclNGen_2865_ = lean_ctor_get(v___x_2860_, 3);
v_cache_2866_ = lean_ctor_get(v___x_2860_, 5);
v_recordedDeps_2867_ = lean_ctor_get(v___x_2860_, 6);
v_messages_2868_ = lean_ctor_get(v___x_2860_, 7);
v_infoState_2869_ = lean_ctor_get(v___x_2860_, 8);
v_snapshotTasks_2870_ = lean_ctor_get(v___x_2860_, 9);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2872_ = v___x_2860_;
v_isShared_2873_ = v_isSharedCheck_2900_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_snapshotTasks_2870_);
lean_inc(v_infoState_2869_);
lean_inc(v_messages_2868_);
lean_inc(v_recordedDeps_2867_);
lean_inc(v_cache_2866_);
lean_inc(v_traceState_2861_);
lean_inc(v_auxDeclNGen_2865_);
lean_inc(v_ngen_2864_);
lean_inc(v_nextMacroScope_2863_);
lean_inc(v_env_2862_);
lean_dec(v___x_2860_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2900_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
uint64_t v_tid_2874_; lean_object* v_traces_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2899_; 
v_tid_2874_ = lean_ctor_get_uint64(v_traceState_2861_, sizeof(void*)*1);
v_traces_2875_ = lean_ctor_get(v_traceState_2861_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v_traceState_2861_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2877_ = v_traceState_2861_;
v_isShared_2878_ = v_isSharedCheck_2899_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_traces_2875_);
lean_dec(v_traceState_2861_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2899_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; double v___x_2881_; uint8_t v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2890_; 
v___x_2879_ = lean_box(0);
v___x_2880_ = lean_box(0);
v___x_2881_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0);
v___x_2882_ = 0;
v___x_2883_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2884_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2884_, 0, v_cls_2849_);
lean_ctor_set(v___x_2884_, 1, v___x_2880_);
lean_ctor_set(v___x_2884_, 2, v___x_2883_);
lean_ctor_set_float(v___x_2884_, sizeof(void*)*3, v___x_2881_);
lean_ctor_set_float(v___x_2884_, sizeof(void*)*3 + 8, v___x_2881_);
lean_ctor_set_uint8(v___x_2884_, sizeof(void*)*3 + 16, v___x_2882_);
v___x_2885_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___closed__0));
v___x_2886_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2884_);
lean_ctor_set(v___x_2886_, 1, v_a_2856_);
lean_ctor_set(v___x_2886_, 2, v___x_2885_);
lean_inc(v_ref_2854_);
v___x_2887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2887_, 0, v_ref_2854_);
lean_ctor_set(v___x_2887_, 1, v___x_2886_);
v___x_2888_ = l_Lean_PersistentArray_push___redArg(v_traces_2875_, v___x_2887_);
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 0, v___x_2888_);
v___x_2890_ = v___x_2877_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v___x_2888_);
lean_ctor_set_uint64(v_reuseFailAlloc_2898_, sizeof(void*)*1, v_tid_2874_);
v___x_2890_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
lean_object* v___x_2892_; 
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 4, v___x_2890_);
v___x_2892_ = v___x_2872_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_env_2862_);
lean_ctor_set(v_reuseFailAlloc_2897_, 1, v_nextMacroScope_2863_);
lean_ctor_set(v_reuseFailAlloc_2897_, 2, v_ngen_2864_);
lean_ctor_set(v_reuseFailAlloc_2897_, 3, v_auxDeclNGen_2865_);
lean_ctor_set(v_reuseFailAlloc_2897_, 4, v___x_2890_);
lean_ctor_set(v_reuseFailAlloc_2897_, 5, v_cache_2866_);
lean_ctor_set(v_reuseFailAlloc_2897_, 6, v_recordedDeps_2867_);
lean_ctor_set(v_reuseFailAlloc_2897_, 7, v_messages_2868_);
lean_ctor_set(v_reuseFailAlloc_2897_, 8, v_infoState_2869_);
lean_ctor_set(v_reuseFailAlloc_2897_, 9, v_snapshotTasks_2870_);
v___x_2892_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
lean_object* v___x_2893_; lean_object* v___x_2895_; 
v___x_2893_ = lean_st_ref_put(v___y_2852_, v___x_2892_);
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 0, v___x_2879_);
v___x_2895_ = v___x_2858_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v___x_2879_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___boxed(lean_object* v_cls_2902_, lean_object* v_msg_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2902_, v_msg_2903_, v___y_2904_, v___y_2905_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
return v_res_2907_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1(void){
_start:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; 
v___x_2909_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__0));
v___x_2910_ = l_Lean_stringToMessageData(v___x_2909_);
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(lean_object* v_decl_2911_, lean_object* v_cls_2912_, lean_object* v_x_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v_toCold_2917_; lean_object* v_options_2918_; uint8_t v_hasTrace_2919_; 
v_toCold_2917_ = lean_ctor_get(v___y_2914_, 0);
v_options_2918_ = lean_ctor_get(v_toCold_2917_, 2);
v_hasTrace_2919_ = lean_ctor_get_uint8(v_options_2918_, sizeof(void*)*1);
if (v_hasTrace_2919_ == 0)
{
lean_object* v___x_2920_; 
lean_dec(v_cls_2912_);
v___x_2920_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2911_, v___y_2914_, v___y_2915_);
return v___x_2920_;
}
else
{
lean_object* v_inheritedTraceOptions_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; uint8_t v___x_2924_; 
v_inheritedTraceOptions_2921_ = lean_ctor_get(v_toCold_2917_, 11);
v___x_2922_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2912_);
v___x_2923_ = l_Lean_Name_append(v___x_2922_, v_cls_2912_);
v___x_2924_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2921_, v_options_2918_, v___x_2923_);
lean_dec(v___x_2923_);
if (v___x_2924_ == 0)
{
lean_object* v___x_2925_; 
lean_dec(v_cls_2912_);
v___x_2925_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2911_, v___y_2914_, v___y_2915_);
return v___x_2925_;
}
else
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2926_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
v___x_2927_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2912_, v___x_2926_, v___y_2914_, v___y_2915_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v___x_2928_; 
lean_dec_ref_known(v___x_2927_, 1);
v___x_2928_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2911_, v___y_2914_, v___y_2915_);
return v___x_2928_;
}
else
{
lean_dec(v_decl_2911_);
return v___x_2927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___boxed(lean_object* v_decl_2929_, lean_object* v_cls_2930_, lean_object* v_x_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_2929_, v_cls_2930_, v_x_2931_, v___y_2932_, v___y_2933_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v_x_2931_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(lean_object* v_opt_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v___x_2939_; uint8_t v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2939_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2937_);
v___x_2940_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_2939_, v_opt_2936_);
lean_dec_ref(v___x_2939_);
v___x_2941_ = lean_box(v___x_2940_);
v___x_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg___boxed(lean_object* v_opt_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_2943_, v___y_2944_);
lean_dec_ref(v___y_2944_);
lean_dec_ref(v_opt_2943_);
return v_res_2946_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(lean_object* v_x_2947_){
_start:
{
if (lean_obj_tag(v_x_2947_) == 0)
{
uint8_t v___x_2948_; 
v___x_2948_ = 1;
return v___x_2948_;
}
else
{
lean_object* v_head_2949_; lean_object* v_tail_2950_; uint8_t v___x_2951_; 
v_head_2949_ = lean_ctor_get(v_x_2947_, 0);
v_tail_2950_ = lean_ctor_get(v_x_2947_, 1);
v___x_2951_ = l_Lean_isPrivateName(v_head_2949_);
if (v___x_2951_ == 0)
{
return v___x_2951_;
}
else
{
v_x_2947_ = v_tail_2950_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2___boxed(lean_object* v_x_2953_){
_start:
{
uint8_t v_res_2954_; lean_object* v_r_2955_; 
v_res_2954_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v_x_2953_);
lean_dec(v_x_2953_);
v_r_2955_ = lean_box(v_res_2954_);
return v_r_2955_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3(void){
_start:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2961_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__2));
v___x_2962_ = l_Lean_stringToMessageData(v___x_2961_);
return v___x_2962_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5(void){
_start:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2964_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__4));
v___x_2965_ = l_Lean_stringToMessageData(v___x_2964_);
return v___x_2965_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7(void){
_start:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2967_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__6));
v___x_2968_ = l_Lean_stringToMessageData(v___x_2967_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(lean_object* v_decl_2969_, uint8_t v_hasTrace_2970_, uint8_t v___x_2971_, lean_object* v_cls_2972_, lean_object* v___x_2973_, lean_object* v___x_2974_, lean_object* v_____x_2975_, lean_object* v_exportedInfo_x3f_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v_a_2983_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v_snd_3075_; lean_object* v_fst_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3207_; 
v_snd_3075_ = lean_ctor_get(v_____x_2975_, 1);
v_fst_3076_ = lean_ctor_get(v_____x_2975_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v_____x_2975_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3078_ = v_____x_2975_;
v_isShared_3079_ = v_isSharedCheck_3207_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_snd_3075_);
lean_inc(v_fst_3076_);
lean_dec(v_____x_2975_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3207_;
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
lean_inc_ref(v___y_3002_);
v___x_3005_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3000_, v___y_3002_, v___y_2995_, v___y_3004_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v___x_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3061_; 
lean_dec_ref_known(v___x_3005_, 1);
lean_dec(v___y_3003_);
lean_inc_ref(v___y_2994_);
v___x_3006_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2994_, v___y_2997_);
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
v___x_3010_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2999_);
v___x_3011_ = l_Lean_Elab_async;
v___x_3012_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_3010_, v___x_3011_);
lean_dec_ref(v___x_3010_);
if (v___x_3012_ == 0)
{
lean_object* v___x_3013_; lean_object* v_r_3014_; 
lean_del_object(v___x_3008_);
lean_dec_ref(v___y_3001_);
lean_dec_ref(v___y_2998_);
v___x_3013_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3002_, v___y_2997_);
lean_dec_ref(v___x_3013_);
v_r_3014_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2969_, v___y_2999_, v___y_2997_);
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
v___x_3021_ = lean_apply_2(v___y_2996_, v___x_3020_, lean_box(0));
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v___x_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
lean_dec_ref_known(v___x_3021_, 1);
v___x_3022_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2994_, v___y_2997_);
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
v___y_2981_ = v___y_2994_;
v___y_2982_ = v___y_2997_;
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
v___x_3036_ = lean_apply_2(v___y_2996_, v___x_3035_, lean_box(0));
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_dec_ref_known(v___x_3036_, 1);
v___y_2981_ = v___y_2994_;
v___y_2982_ = v___y_2997_;
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
v___y_2981_ = v___y_2994_;
v___y_2982_ = v___y_2997_;
v_a_2983_ = v_a_3037_;
goto v___jp_2980_;
}
}
}
else
{
lean_object* v___x_3038_; lean_object* v___x_3040_; 
lean_dec_ref(v___y_3002_);
lean_dec_ref(v___y_2996_);
lean_dec_ref(v___y_2994_);
lean_dec(v_decl_2969_);
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
v___x_3043_ = l_Lean_Name_toString(v___x_3042_, v_hasTrace_2970_);
lean_inc_ref(v___x_3040_);
v___x_3044_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3001_, v___x_3040_, v___x_3043_, v___y_2999_, v___y_2997_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v_checked_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc(v_a_3045_);
lean_dec_ref_known(v___x_3044_, 1);
v_checked_3046_ = lean_ctor_get(v___y_2998_, 2);
lean_inc_ref(v_checked_3046_);
lean_dec_ref(v___y_2998_);
v___x_3047_ = lean_io_map_task(v_a_3045_, v_checked_3046_, v___x_3041_, v___x_2971_);
v___x_3048_ = lean_box(0);
v___x_3049_ = lean_box(2);
v___x_3050_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3048_);
lean_ctor_set(v___x_3050_, 1, v___x_3049_);
lean_ctor_set(v___x_3050_, 2, v___x_3040_);
lean_ctor_set(v___x_3050_, 3, v___x_3047_);
v___x_3051_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3050_, v___y_2997_);
return v___x_3051_;
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
lean_dec_ref(v___x_3040_);
lean_dec_ref(v___y_2998_);
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
lean_dec_ref(v___y_3002_);
lean_dec_ref(v___y_3001_);
lean_dec_ref(v___y_2998_);
lean_dec_ref(v___y_2996_);
lean_dec_ref(v___y_2994_);
lean_dec(v_decl_2969_);
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
lean_ctor_set(v___x_3070_, 0, v___y_3003_);
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
lean_object* v_fst_3080_; lean_object* v_snd_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3206_; 
v_fst_3080_ = lean_ctor_get(v_snd_3075_, 0);
v_snd_3081_ = lean_ctor_get(v_snd_3075_, 1);
v_isSharedCheck_3206_ = !lean_is_exclusive(v_snd_3075_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3083_ = v_snd_3075_;
v_isShared_3084_ = v_isSharedCheck_3206_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_snd_3081_);
lean_inc(v_fst_3080_);
lean_dec(v_snd_3075_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3206_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v_exportedInfo_x3f_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___x_3196_; lean_object* v_env_3197_; uint8_t v___x_3198_; 
v___x_3196_ = lean_st_ref_get(v___y_2978_);
v_env_3197_ = lean_ctor_get(v___x_3196_, 0);
lean_inc_ref(v_env_3197_);
lean_dec(v___x_3196_);
v___x_3198_ = l_Lean_Environment_containsOnBranch(v_env_3197_, v_fst_3076_);
lean_dec_ref(v_env_3197_);
if (v___x_3198_ == 0)
{
lean_del_object(v___x_3078_);
v___y_3135_ = v___y_2977_;
v___y_3136_ = v___y_2978_;
goto v___jp_3134_;
}
else
{
lean_object* v___x_3199_; lean_object* v_env_3200_; lean_object* v___x_3201_; lean_object* v___x_3203_; 
lean_del_object(v___x_3083_);
lean_dec(v_snd_3081_);
lean_dec(v_fst_3080_);
lean_dec(v_exportedInfo_x3f_2976_);
lean_dec(v___x_2974_);
lean_dec_ref(v___x_2973_);
lean_dec(v_cls_2972_);
lean_dec(v_decl_2969_);
v___x_3199_ = lean_st_ref_get(v___y_2978_);
v_env_3200_ = lean_ctor_get(v___x_3199_, 0);
lean_inc_ref(v_env_3200_);
lean_dec(v___x_3199_);
v___x_3201_ = lean_elab_environment_to_kernel_env(v_env_3200_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set_tag(v___x_3078_, 1);
lean_ctor_set(v___x_3078_, 1, v_fst_3076_);
lean_ctor_set(v___x_3078_, 0, v___x_3201_);
v___x_3203_ = v___x_3078_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3201_);
lean_ctor_set(v_reuseFailAlloc_3205_, 1, v_fst_3076_);
v___x_3203_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
lean_object* v___x_3204_; 
v___x_3204_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3203_, v___y_2977_, v___y_2978_);
return v___x_3204_;
}
}
v___jp_3085_:
{
lean_object* v_ref_3091_; uint8_t v___x_3092_; lean_object* v___x_3093_; 
v_ref_3091_ = lean_ctor_get(v___y_3086_, 2);
v___x_3092_ = lean_unbox(v_snd_3081_);
lean_dec(v_snd_3081_);
lean_inc_ref(v___y_3089_);
v___x_3093_ = l_Lean_Environment_addConstAsync(v___y_3089_, v_fst_3076_, v___x_3092_, v___y_3090_, v___x_2971_, v_hasTrace_2970_);
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
lean_inc(v___y_3088_);
v___f_3097_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3097_, 0, v___y_3088_);
lean_closure_set(v___f_3097_, 1, v_a_3094_);
lean_closure_set(v___f_3097_, 2, v_ref_3091_);
lean_inc(v_decl_2969_);
v___f_3098_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3098_, 0, v_a_3094_);
lean_closure_set(v___f_3098_, 1, v_asyncEnv_3096_);
lean_closure_set(v___f_3098_, 2, v_decl_2969_);
v___x_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3099_, 0, v_fst_3080_);
if (lean_obj_tag(v___y_3087_) == 0)
{
lean_inc(v_ref_3091_);
lean_inc_ref(v___x_3099_);
v___y_2994_ = v_mainEnv_3095_;
v___y_2995_ = v___x_3099_;
v___y_2996_ = v___f_3097_;
v___y_2997_ = v___y_3088_;
v___y_2998_ = v___y_3089_;
v___y_2999_ = v___y_3086_;
v___y_3000_ = v_a_3094_;
v___y_3001_ = v___f_3098_;
v___y_3002_ = v_asyncEnv_3096_;
v___y_3003_ = v_ref_3091_;
v___y_3004_ = v___x_3099_;
goto v___jp_2993_;
}
else
{
lean_inc(v_ref_3091_);
v___y_2994_ = v_mainEnv_3095_;
v___y_2995_ = v___x_3099_;
v___y_2996_ = v___f_3097_;
v___y_2997_ = v___y_3088_;
v___y_2998_ = v___y_3089_;
v___y_2999_ = v___y_3086_;
v___y_3000_ = v_a_3094_;
v___y_3001_ = v___f_3098_;
v___y_3002_ = v_asyncEnv_3096_;
v___y_3003_ = v_ref_3091_;
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
lean_dec(v_decl_2969_);
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
v___y_3086_ = v___y_3116_;
v___y_3087_ = v_exportedInfo_x3f_3115_;
v___y_3088_ = v___y_3117_;
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
v___y_3086_ = v___y_3116_;
v___y_3087_ = v_exportedInfo_x3f_3115_;
v___y_3088_ = v___y_3117_;
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
lean_inc(v_decl_2969_);
v___x_3137_ = l_Lean_Declaration_getTopLevelNames(v_decl_2969_);
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
lean_dec(v_cls_2972_);
v___y_3127_ = v___y_3135_;
v___y_3128_ = v___y_3136_;
goto v___jp_3126_;
}
else
{
lean_object* v_inheritedTraceOptions_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; uint8_t v___x_3145_; 
v_inheritedTraceOptions_3142_ = lean_ctor_get(v_toCold_3139_, 11);
v___x_3143_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2972_);
v___x_3144_ = l_Lean_Name_append(v___x_3143_, v_cls_2972_);
v___x_3145_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3142_, v_options_3140_, v___x_3144_);
lean_dec(v___x_3144_);
if (v___x_3145_ == 0)
{
lean_dec(v_cls_2972_);
v___y_3127_ = v___y_3135_;
v___y_3128_ = v___y_3136_;
goto v___jp_3126_;
}
else
{
lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3146_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_3147_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2972_, v___x_3146_, v___y_3135_, v___y_3136_);
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
lean_dec(v_decl_2969_);
return v___x_3147_;
}
}
}
}
else
{
lean_object* v___x_3148_; lean_object* v_env_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; uint8_t v___x_3152_; lean_object* v___x_3153_; 
lean_dec(v_cls_2972_);
v___x_3148_ = lean_st_ref_get(v___y_3136_);
v_env_3149_ = lean_ctor_get(v___x_3148_, 0);
lean_inc_ref(v_env_3149_);
lean_dec(v___x_3148_);
v___x_3150_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_3151_ = lean_box(1);
v___x_3152_ = 0;
lean_inc(v_fst_3076_);
v___x_3153_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3150_, v_env_3149_, v_fst_3076_, v___x_3151_, v___x_3152_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v___x_3154_; lean_object* v_env_3155_; lean_object* v_nextMacroScope_3156_; lean_object* v_ngen_3157_; lean_object* v_auxDeclNGen_3158_; lean_object* v_traceState_3159_; lean_object* v_recordedDeps_3160_; lean_object* v_messages_3161_; lean_object* v_infoState_3162_; lean_object* v_snapshotTasks_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3172_; 
v___x_3154_ = lean_st_ref_take(v___y_3136_);
v_env_3155_ = lean_ctor_get(v___x_3154_, 0);
v_nextMacroScope_3156_ = lean_ctor_get(v___x_3154_, 1);
v_ngen_3157_ = lean_ctor_get(v___x_3154_, 2);
v_auxDeclNGen_3158_ = lean_ctor_get(v___x_3154_, 3);
v_traceState_3159_ = lean_ctor_get(v___x_3154_, 4);
v_recordedDeps_3160_ = lean_ctor_get(v___x_3154_, 6);
v_messages_3161_ = lean_ctor_get(v___x_3154_, 7);
v_infoState_3162_ = lean_ctor_get(v___x_3154_, 8);
v_snapshotTasks_3163_ = lean_ctor_get(v___x_3154_, 9);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3172_ == 0)
{
lean_object* v_unused_3173_; 
v_unused_3173_ = lean_ctor_get(v___x_3154_, 5);
lean_dec(v_unused_3173_);
v___x_3165_ = v___x_3154_;
v_isShared_3166_ = v_isSharedCheck_3172_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_snapshotTasks_3163_);
lean_inc(v_infoState_3162_);
lean_inc(v_messages_3161_);
lean_inc(v_recordedDeps_3160_);
lean_inc(v_traceState_3159_);
lean_inc(v_auxDeclNGen_3158_);
lean_inc(v_ngen_3157_);
lean_inc(v_nextMacroScope_3156_);
lean_inc(v_env_3155_);
lean_dec(v___x_3154_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3172_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3167_; lean_object* v___x_3169_; 
lean_inc(v_snd_3081_);
lean_inc(v_fst_3076_);
v___x_3167_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3150_, v_env_3155_, v_fst_3076_, v_snd_3081_, v___x_3138_);
if (v_isShared_3166_ == 0)
{
lean_ctor_set(v___x_3165_, 5, v___x_2973_);
lean_ctor_set(v___x_3165_, 0, v___x_3167_);
v___x_3169_ = v___x_3165_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v___x_3167_);
lean_ctor_set(v_reuseFailAlloc_3171_, 1, v_nextMacroScope_3156_);
lean_ctor_set(v_reuseFailAlloc_3171_, 2, v_ngen_3157_);
lean_ctor_set(v_reuseFailAlloc_3171_, 3, v_auxDeclNGen_3158_);
lean_ctor_set(v_reuseFailAlloc_3171_, 4, v_traceState_3159_);
lean_ctor_set(v_reuseFailAlloc_3171_, 5, v___x_2973_);
lean_ctor_set(v_reuseFailAlloc_3171_, 6, v_recordedDeps_3160_);
lean_ctor_set(v_reuseFailAlloc_3171_, 7, v_messages_3161_);
lean_ctor_set(v_reuseFailAlloc_3171_, 8, v_infoState_3162_);
lean_ctor_set(v_reuseFailAlloc_3171_, 9, v_snapshotTasks_3163_);
v___x_3169_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
lean_object* v___x_3170_; 
v___x_3170_ = lean_st_ref_put(v___y_3136_, v___x_3169_);
v_exportedInfo_x3f_3115_ = v_exportedInfo_x3f_2976_;
v___y_3116_ = v___y_3135_;
v___y_3117_ = v___y_3136_;
goto v___jp_3114_;
}
}
}
else
{
lean_dec_ref_known(v___x_3153_, 1);
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
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v_a_3176_; uint8_t v___x_3177_; 
lean_dec(v_exportedInfo_x3f_2976_);
lean_dec_ref(v___x_2973_);
v___x_3174_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3175_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3174_, v___y_3135_);
v_a_3176_ = lean_ctor_get(v___x_3175_, 0);
lean_inc(v_a_3176_);
lean_dec_ref(v___x_3175_);
v___x_3177_ = lean_unbox(v_a_3176_);
lean_dec(v_a_3176_);
if (v___x_3177_ == 0)
{
lean_object* v_toCold_3178_; lean_object* v_options_3179_; uint8_t v_hasTrace_3180_; 
v_toCold_3178_ = lean_ctor_get(v___y_3135_, 0);
v_options_3179_ = lean_ctor_get(v_toCold_3178_, 2);
v_hasTrace_3180_ = lean_ctor_get_uint8(v_options_3179_, sizeof(void*)*1);
if (v_hasTrace_3180_ == 0)
{
lean_dec(v_cls_2972_);
v_exportedInfo_x3f_3115_ = v___x_2974_;
v___y_3116_ = v___y_3135_;
v___y_3117_ = v___y_3136_;
goto v___jp_3114_;
}
else
{
lean_object* v_inheritedTraceOptions_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; uint8_t v___x_3184_; 
v_inheritedTraceOptions_3181_ = lean_ctor_get(v_toCold_3178_, 11);
v___x_3182_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2972_);
v___x_3183_ = l_Lean_Name_append(v___x_3182_, v_cls_2972_);
v___x_3184_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3181_, v_options_3179_, v___x_3183_);
lean_dec(v___x_3183_);
if (v___x_3184_ == 0)
{
lean_dec(v_cls_2972_);
v_exportedInfo_x3f_3115_ = v___x_2974_;
v___y_3116_ = v___y_3135_;
v___y_3117_ = v___y_3136_;
goto v___jp_3114_;
}
else
{
lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3185_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_3186_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2972_, v___x_3185_, v___y_3135_, v___y_3136_);
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_dec_ref_known(v___x_3186_, 1);
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
lean_dec(v_decl_2969_);
return v___x_3186_;
}
}
}
}
else
{
lean_object* v_toCold_3187_; lean_object* v_options_3188_; uint8_t v_hasTrace_3189_; 
lean_dec(v___x_2974_);
v_toCold_3187_ = lean_ctor_get(v___y_3135_, 0);
v_options_3188_ = lean_ctor_get(v_toCold_3187_, 2);
v_hasTrace_3189_ = lean_ctor_get_uint8(v_options_3188_, sizeof(void*)*1);
if (v_hasTrace_3189_ == 0)
{
lean_dec(v_cls_2972_);
v___y_3131_ = v___y_3135_;
v___y_3132_ = v___y_3136_;
goto v___jp_3130_;
}
else
{
lean_object* v_inheritedTraceOptions_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; uint8_t v___x_3193_; 
v_inheritedTraceOptions_3190_ = lean_ctor_get(v_toCold_3187_, 11);
v___x_3191_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2972_);
v___x_3192_ = l_Lean_Name_append(v___x_3191_, v_cls_2972_);
v___x_3193_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3190_, v_options_3188_, v___x_3192_);
lean_dec(v___x_3192_);
if (v___x_3193_ == 0)
{
lean_dec(v_cls_2972_);
v___y_3131_ = v___y_3135_;
v___y_3132_ = v___y_3136_;
goto v___jp_3130_;
}
else
{
lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3194_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_3195_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2972_, v___x_3194_, v___y_3135_, v___y_3136_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_dec_ref_known(v___x_3195_, 1);
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
lean_dec(v_decl_2969_);
return v___x_3195_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed(lean_object* v_decl_3208_, lean_object* v_hasTrace_3209_, lean_object* v___x_3210_, lean_object* v_cls_3211_, lean_object* v___x_3212_, lean_object* v___x_3213_, lean_object* v_____x_3214_, lean_object* v_exportedInfo_x3f_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
uint8_t v_hasTrace_boxed_3219_; uint8_t v___x_54786__boxed_3220_; lean_object* v_res_3221_; 
v_hasTrace_boxed_3219_ = lean_unbox(v_hasTrace_3209_);
v___x_54786__boxed_3220_ = lean_unbox(v___x_3210_);
v_res_3221_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_decl_3208_, v_hasTrace_boxed_3219_, v___x_54786__boxed_3220_, v_cls_3211_, v___x_3212_, v___x_3213_, v_____x_3214_, v_exportedInfo_x3f_3215_, v___y_3216_, v___y_3217_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
return v_res_3221_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1(void){
_start:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3223_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__0));
v___x_3224_ = l_Lean_stringToMessageData(v___x_3223_);
return v___x_3224_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3(void){
_start:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3226_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__2));
v___x_3227_ = l_Lean_stringToMessageData(v___x_3226_);
return v___x_3227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(lean_object* v___f_3228_, uint8_t v___x_3229_, uint8_t v_forceExpose_3230_, lean_object* v___x_3231_, lean_object* v_cls_3232_, lean_object* v_defn_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
lean_object* v_exportedInfo_x3f_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; uint8_t v___y_3253_; uint8_t v___y_3258_; lean_object* v___x_3263_; lean_object* v_env_3264_; lean_object* v___x_3265_; 
v___x_3263_ = lean_st_ref_get(v___y_3235_);
v_env_3264_ = lean_ctor_get(v___x_3263_, 0);
lean_inc_ref(v_env_3264_);
lean_dec(v___x_3263_);
v___x_3265_ = lean_st_ref_get(v___y_3235_);
if (v_forceExpose_3230_ == 0)
{
lean_object* v_env_3266_; lean_object* v___x_3267_; uint8_t v_isModule_3268_; 
v_env_3266_ = lean_ctor_get(v___x_3265_, 0);
lean_inc_ref(v_env_3266_);
lean_dec(v___x_3265_);
v___x_3267_ = l_Lean_Environment_header(v_env_3264_);
lean_dec_ref(v_env_3264_);
v_isModule_3268_ = lean_ctor_get_uint8(v___x_3267_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_3267_);
if (v_isModule_3268_ == 0)
{
lean_dec_ref(v_env_3266_);
lean_dec(v_cls_3232_);
v_exportedInfo_x3f_3238_ = v___x_3231_;
v___y_3239_ = v___y_3234_;
v___y_3240_ = v___y_3235_;
goto v___jp_3237_;
}
else
{
uint8_t v_isExporting_3269_; 
v_isExporting_3269_ = lean_ctor_get_uint8(v_env_3266_, sizeof(void*)*13);
lean_dec_ref(v_env_3266_);
if (v_isExporting_3269_ == 0)
{
lean_object* v_toCold_3270_; lean_object* v_options_3271_; uint8_t v_hasTrace_3272_; 
lean_dec(v___x_3231_);
v_toCold_3270_ = lean_ctor_get(v___y_3234_, 0);
v_options_3271_ = lean_ctor_get(v_toCold_3270_, 2);
v_hasTrace_3272_ = lean_ctor_get_uint8(v_options_3271_, sizeof(void*)*1);
if (v_hasTrace_3272_ == 0)
{
lean_dec(v_cls_3232_);
v___y_3258_ = v_isModule_3268_;
goto v___jp_3257_;
}
else
{
lean_object* v_inheritedTraceOptions_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; uint8_t v___x_3276_; 
v_inheritedTraceOptions_3273_ = lean_ctor_get(v_toCold_3270_, 11);
v___x_3274_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3232_);
v___x_3275_ = l_Lean_Name_append(v___x_3274_, v_cls_3232_);
v___x_3276_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3273_, v_options_3271_, v___x_3275_);
lean_dec(v___x_3275_);
if (v___x_3276_ == 0)
{
lean_dec(v_cls_3232_);
v___y_3258_ = v_isModule_3268_;
goto v___jp_3257_;
}
else
{
lean_object* v_toConstantVal_3277_; lean_object* v_name_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v_toConstantVal_3277_ = lean_ctor_get(v_defn_3233_, 0);
v_name_3278_ = lean_ctor_get(v_toConstantVal_3277_, 0);
v___x_3279_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_3278_);
v___x_3280_ = l_Lean_MessageData_ofName(v_name_3278_);
v___x_3281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3279_);
lean_ctor_set(v___x_3281_, 1, v___x_3280_);
v___x_3282_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_3283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3281_);
lean_ctor_set(v___x_3283_, 1, v___x_3282_);
v___x_3284_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3232_, v___x_3283_, v___y_3234_, v___y_3235_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_dec_ref_known(v___x_3284_, 1);
v___y_3258_ = v_isModule_3268_;
goto v___jp_3257_;
}
else
{
lean_dec_ref(v_defn_3233_);
lean_dec_ref(v___f_3228_);
return v___x_3284_;
}
}
}
}
else
{
lean_dec(v_cls_3232_);
v_exportedInfo_x3f_3238_ = v___x_3231_;
v___y_3239_ = v___y_3234_;
v___y_3240_ = v___y_3235_;
goto v___jp_3237_;
}
}
}
else
{
lean_dec(v___x_3265_);
lean_dec_ref(v_env_3264_);
lean_dec(v_cls_3232_);
v_exportedInfo_x3f_3238_ = v___x_3231_;
v___y_3239_ = v___y_3234_;
v___y_3240_ = v___y_3235_;
goto v___jp_3237_;
}
v___jp_3237_:
{
lean_object* v_toConstantVal_3241_; lean_object* v_name_3242_; lean_object* v___x_3243_; uint8_t v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v_toConstantVal_3241_ = lean_ctor_get(v_defn_3233_, 0);
v_name_3242_ = lean_ctor_get(v_toConstantVal_3241_, 0);
lean_inc(v_name_3242_);
v___x_3243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3243_, 0, v_defn_3233_);
v___x_3244_ = 0;
v___x_3245_ = lean_box(v___x_3244_);
v___x_3246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3243_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
v___x_3247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3247_, 0, v_name_3242_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
lean_inc(v___y_3240_);
lean_inc_ref(v___y_3239_);
v___x_3248_ = lean_apply_5(v___f_3228_, v___x_3247_, v_exportedInfo_x3f_3238_, v___y_3239_, v___y_3240_, lean_box(0));
return v___x_3248_;
}
v___jp_3249_:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3254_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3254_, 0, v___y_3250_);
lean_ctor_set_uint8(v___x_3254_, sizeof(void*)*1, v___y_3253_);
v___x_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3254_);
v___x_3256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3255_);
v_exportedInfo_x3f_3238_ = v___x_3256_;
v___y_3239_ = v___y_3251_;
v___y_3240_ = v___y_3252_;
goto v___jp_3237_;
}
v___jp_3257_:
{
lean_object* v_toConstantVal_3259_; uint8_t v_safety_3260_; uint8_t v___x_3261_; uint8_t v___x_3262_; 
v_toConstantVal_3259_ = lean_ctor_get(v_defn_3233_, 0);
v_safety_3260_ = lean_ctor_get_uint8(v_defn_3233_, sizeof(void*)*4);
v___x_3261_ = 1;
v___x_3262_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3260_, v___x_3261_);
if (v___x_3262_ == 0)
{
lean_inc_ref(v_toConstantVal_3259_);
v___y_3250_ = v_toConstantVal_3259_;
v___y_3251_ = v___y_3234_;
v___y_3252_ = v___y_3235_;
v___y_3253_ = v___y_3258_;
goto v___jp_3249_;
}
else
{
lean_inc_ref(v_toConstantVal_3259_);
v___y_3250_ = v_toConstantVal_3259_;
v___y_3251_ = v___y_3234_;
v___y_3252_ = v___y_3235_;
v___y_3253_ = v___x_3229_;
goto v___jp_3249_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed(lean_object* v___f_3285_, lean_object* v___x_3286_, lean_object* v_forceExpose_3287_, lean_object* v___x_3288_, lean_object* v_cls_3289_, lean_object* v_defn_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
uint8_t v___x_55254__boxed_3294_; uint8_t v_forceExpose_boxed_3295_; lean_object* v_res_3296_; 
v___x_55254__boxed_3294_ = lean_unbox(v___x_3286_);
v_forceExpose_boxed_3295_ = lean_unbox(v_forceExpose_3287_);
v_res_3296_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v___f_3285_, v___x_55254__boxed_3294_, v_forceExpose_boxed_3295_, v___x_3288_, v_cls_3289_, v_defn_3290_, v___y_3291_, v___y_3292_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(lean_object* v_val_3297_, lean_object* v___f_3298_, lean_object* v_____r_3299_, lean_object* v_exportedInfo_x3f_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_){
_start:
{
lean_object* v_toConstantVal_3304_; lean_object* v_name_3305_; lean_object* v___x_3306_; uint8_t v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v_toConstantVal_3304_ = lean_ctor_get(v_val_3297_, 0);
v_name_3305_ = lean_ctor_get(v_toConstantVal_3304_, 0);
lean_inc(v_name_3305_);
v___x_3306_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3306_, 0, v_val_3297_);
v___x_3307_ = 1;
v___x_3308_ = lean_box(v___x_3307_);
v___x_3309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3306_);
lean_ctor_set(v___x_3309_, 1, v___x_3308_);
v___x_3310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3310_, 0, v_name_3305_);
lean_ctor_set(v___x_3310_, 1, v___x_3309_);
lean_inc(v___y_3302_);
lean_inc_ref(v___y_3301_);
v___x_3311_ = lean_apply_5(v___f_3298_, v___x_3310_, v_exportedInfo_x3f_3300_, v___y_3301_, v___y_3302_, lean_box(0));
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed(lean_object* v_val_3312_, lean_object* v___f_3313_, lean_object* v_____r_3314_, lean_object* v_exportedInfo_x3f_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_){
_start:
{
lean_object* v_res_3319_; 
v_res_3319_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(v_val_3312_, v___f_3313_, v_____r_3314_, v_exportedInfo_x3f_3315_, v___y_3316_, v___y_3317_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(lean_object* v_val_3320_, uint8_t v___x_3321_, lean_object* v___f_3322_, lean_object* v_____r_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_){
_start:
{
lean_object* v_toConstantVal_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v_toConstantVal_3327_ = lean_ctor_get(v_val_3320_, 0);
lean_inc_ref(v_toConstantVal_3327_);
v___x_3328_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3328_, 0, v_toConstantVal_3327_);
lean_ctor_set_uint8(v___x_3328_, sizeof(void*)*1, v___x_3321_);
v___x_3329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3328_);
v___x_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3329_);
v___x_3331_ = lean_box(0);
lean_inc(v___y_3325_);
lean_inc_ref(v___y_3324_);
v___x_3332_ = lean_apply_5(v___f_3322_, v___x_3331_, v___x_3330_, v___y_3324_, v___y_3325_, lean_box(0));
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed(lean_object* v_val_3333_, lean_object* v___x_3334_, lean_object* v___f_3335_, lean_object* v_____r_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
uint8_t v___x_55379__boxed_3340_; lean_object* v_res_3341_; 
v___x_55379__boxed_3340_ = lean_unbox(v___x_3334_);
v_res_3341_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(v_val_3333_, v___x_55379__boxed_3340_, v___f_3335_, v_____r_3336_, v___y_3337_, v___y_3338_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec_ref(v_val_3333_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(lean_object* v_val_3342_, lean_object* v___f_3343_, lean_object* v_____r_3344_, lean_object* v_exportedInfo_x3f_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_){
_start:
{
lean_object* v_toConstantVal_3349_; lean_object* v_name_3350_; lean_object* v___x_3351_; uint8_t v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v_toConstantVal_3349_ = lean_ctor_get(v_val_3342_, 0);
v_name_3350_ = lean_ctor_get(v_toConstantVal_3349_, 0);
lean_inc(v_name_3350_);
v___x_3351_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3351_, 0, v_val_3342_);
v___x_3352_ = 3;
v___x_3353_ = lean_box(v___x_3352_);
v___x_3354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3351_);
lean_ctor_set(v___x_3354_, 1, v___x_3353_);
v___x_3355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3355_, 0, v_name_3350_);
lean_ctor_set(v___x_3355_, 1, v___x_3354_);
lean_inc(v___y_3347_);
lean_inc_ref(v___y_3346_);
v___x_3356_ = lean_apply_5(v___f_3343_, v___x_3355_, v_exportedInfo_x3f_3345_, v___y_3346_, v___y_3347_, lean_box(0));
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed(lean_object* v_val_3357_, lean_object* v___f_3358_, lean_object* v_____r_3359_, lean_object* v_exportedInfo_x3f_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(v_val_3357_, v___f_3358_, v_____r_3359_, v_exportedInfo_x3f_3360_, v___y_3361_, v___y_3362_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(lean_object* v_val_3365_, lean_object* v___f_3366_, lean_object* v_____r_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
lean_object* v_toConstantVal_3371_; uint8_t v_isUnsafe_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
v_toConstantVal_3371_ = lean_ctor_get(v_val_3365_, 0);
v_isUnsafe_3372_ = lean_ctor_get_uint8(v_val_3365_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_3371_);
v___x_3373_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3373_, 0, v_toConstantVal_3371_);
lean_ctor_set_uint8(v___x_3373_, sizeof(void*)*1, v_isUnsafe_3372_);
v___x_3374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3373_);
v___x_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3374_);
v___x_3376_ = lean_box(0);
lean_inc(v___y_3369_);
lean_inc_ref(v___y_3368_);
v___x_3377_ = lean_apply_5(v___f_3366_, v___x_3376_, v___x_3375_, v___y_3368_, v___y_3369_, lean_box(0));
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10___boxed(lean_object* v_val_3378_, lean_object* v___f_3379_, lean_object* v_____r_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_){
_start:
{
lean_object* v_res_3384_; 
v_res_3384_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_3378_, v___f_3379_, v_____r_3380_, v___y_3381_, v___y_3382_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
lean_dec_ref(v_val_3378_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(lean_object* v_decl_3385_, uint8_t v___x_3386_, lean_object* v_cls_3387_, lean_object* v___x_3388_, lean_object* v___x_3389_, lean_object* v_____x_3390_, lean_object* v_exportedInfo_x3f_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v_a_3398_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; uint8_t v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v_snd_3491_; lean_object* v_fst_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3624_; 
v_snd_3491_ = lean_ctor_get(v_____x_3390_, 1);
v_fst_3492_ = lean_ctor_get(v_____x_3390_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v_____x_3390_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3494_ = v_____x_3390_;
v_isShared_3495_ = v_isSharedCheck_3624_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_snd_3491_);
lean_inc(v_fst_3492_);
lean_dec(v_____x_3390_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3624_;
goto v_resetjp_3493_;
}
v___jp_3395_:
{
lean_object* v___x_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
v___x_3399_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3397_, v___y_3396_);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3406_ == 0)
{
lean_object* v_unused_3407_; 
v_unused_3407_ = lean_ctor_get(v___x_3399_, 0);
lean_dec(v_unused_3407_);
v___x_3401_ = v___x_3399_;
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
else
{
lean_dec(v___x_3399_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
lean_ctor_set_tag(v___x_3401_, 1);
lean_ctor_set(v___x_3401_, 0, v_a_3398_);
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3398_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
v___jp_3408_:
{
lean_object* v___x_3421_; 
lean_inc_ref(v___y_3409_);
v___x_3421_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3418_, v___y_3409_, v___y_3411_, v___y_3420_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v___x_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3477_; 
lean_dec_ref_known(v___x_3421_, 1);
lean_dec(v___y_3414_);
lean_inc_ref(v___y_3419_);
v___x_3422_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3419_, v___y_3413_);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3477_ == 0)
{
lean_object* v_unused_3478_; 
v_unused_3478_ = lean_ctor_get(v___x_3422_, 0);
lean_dec(v_unused_3478_);
v___x_3424_ = v___x_3422_;
v_isShared_3425_ = v_isSharedCheck_3477_;
goto v_resetjp_3423_;
}
else
{
lean_dec(v___x_3422_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3477_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; uint8_t v___x_3428_; 
v___x_3426_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3410_);
v___x_3427_ = l_Lean_Elab_async;
v___x_3428_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_3426_, v___x_3427_);
lean_dec_ref(v___x_3426_);
if (v___x_3428_ == 0)
{
lean_object* v___x_3429_; lean_object* v_r_3430_; 
lean_del_object(v___x_3424_);
lean_dec_ref(v___y_3416_);
lean_dec_ref(v___y_3415_);
v___x_3429_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3409_, v___y_3413_);
lean_dec_ref(v___x_3429_);
v_r_3430_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3385_, v___y_3410_, v___y_3413_);
if (lean_obj_tag(v_r_3430_) == 0)
{
lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3449_; 
v_a_3431_ = lean_ctor_get(v_r_3430_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v_r_3430_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3433_ = v_r_3430_;
v_isShared_3434_ = v_isSharedCheck_3449_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v_r_3430_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3449_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3436_; 
lean_inc(v_a_3431_);
if (v_isShared_3434_ == 0)
{
lean_ctor_set_tag(v___x_3433_, 1);
v___x_3436_ = v___x_3433_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_a_3431_);
v___x_3436_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
lean_object* v___x_3437_; 
v___x_3437_ = lean_apply_2(v___y_3412_, v___x_3436_, lean_box(0));
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v___x_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
lean_dec_ref_known(v___x_3437_, 1);
v___x_3438_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3419_, v___y_3413_);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3445_ == 0)
{
lean_object* v_unused_3446_; 
v_unused_3446_ = lean_ctor_get(v___x_3438_, 0);
lean_dec(v_unused_3446_);
v___x_3440_ = v___x_3438_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_dec(v___x_3438_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 0, v_a_3431_);
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3431_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
else
{
lean_object* v_a_3447_; 
lean_dec(v_a_3431_);
v_a_3447_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3447_);
lean_dec_ref_known(v___x_3437_, 1);
v___y_3396_ = v___y_3413_;
v___y_3397_ = v___y_3419_;
v_a_3398_ = v_a_3447_;
goto v___jp_3395_;
}
}
}
}
else
{
lean_object* v_a_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
v_a_3450_ = lean_ctor_get(v_r_3430_, 0);
lean_inc(v_a_3450_);
lean_dec_ref_known(v_r_3430_, 1);
v___x_3451_ = lean_box(0);
v___x_3452_ = lean_apply_2(v___y_3412_, v___x_3451_, lean_box(0));
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_dec_ref_known(v___x_3452_, 1);
v___y_3396_ = v___y_3413_;
v___y_3397_ = v___y_3419_;
v_a_3398_ = v_a_3450_;
goto v___jp_3395_;
}
else
{
lean_object* v_a_3453_; 
lean_dec(v_a_3450_);
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_a_3453_);
lean_dec_ref_known(v___x_3452_, 1);
v___y_3396_ = v___y_3413_;
v___y_3397_ = v___y_3419_;
v_a_3398_ = v_a_3453_;
goto v___jp_3395_;
}
}
}
else
{
lean_object* v___x_3454_; lean_object* v___x_3456_; 
lean_dec_ref(v___y_3419_);
lean_dec_ref(v___y_3412_);
lean_dec_ref(v___y_3409_);
lean_dec(v_decl_3385_);
v___x_3454_ = l_IO_CancelToken_new();
if (v_isShared_3425_ == 0)
{
lean_ctor_set_tag(v___x_3424_, 1);
lean_ctor_set(v___x_3424_, 0, v___x_3454_);
v___x_3456_ = v___x_3424_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3454_);
v___x_3456_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3457_ = lean_unsigned_to_nat(0u);
v___x_3458_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_3459_ = l_Lean_Name_toString(v___x_3458_, v___x_3386_);
lean_inc_ref(v___x_3456_);
v___x_3460_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3416_, v___x_3456_, v___x_3459_, v___y_3410_, v___y_3413_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; lean_object* v_checked_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3461_);
lean_dec_ref_known(v___x_3460_, 1);
v_checked_3462_ = lean_ctor_get(v___y_3415_, 2);
lean_inc_ref(v_checked_3462_);
lean_dec_ref(v___y_3415_);
v___x_3463_ = lean_io_map_task(v_a_3461_, v_checked_3462_, v___x_3457_, v___y_3417_);
v___x_3464_ = lean_box(0);
v___x_3465_ = lean_box(2);
v___x_3466_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3464_);
lean_ctor_set(v___x_3466_, 1, v___x_3465_);
lean_ctor_set(v___x_3466_, 2, v___x_3456_);
lean_ctor_set(v___x_3466_, 3, v___x_3463_);
v___x_3467_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3466_, v___y_3413_);
return v___x_3467_;
}
else
{
lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3475_; 
lean_dec_ref(v___x_3456_);
lean_dec_ref(v___y_3415_);
v_a_3468_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3470_ = v___x_3460_;
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_a_3468_);
lean_dec(v___x_3460_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3473_; 
if (v_isShared_3471_ == 0)
{
v___x_3473_ = v___x_3470_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_a_3468_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3490_; 
lean_dec_ref(v___y_3419_);
lean_dec_ref(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec_ref(v___y_3412_);
lean_dec_ref(v___y_3409_);
lean_dec(v_decl_3385_);
v_a_3479_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3481_ = v___x_3421_;
v_isShared_3482_ = v_isSharedCheck_3490_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3421_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3490_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3488_; 
v___x_3483_ = lean_io_error_to_string(v_a_3479_);
v___x_3484_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3483_);
v___x_3485_ = l_Lean_MessageData_ofFormat(v___x_3484_);
v___x_3486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3486_, 0, v___y_3414_);
lean_ctor_set(v___x_3486_, 1, v___x_3485_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 0, v___x_3486_);
v___x_3488_ = v___x_3481_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v___x_3486_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
v_resetjp_3493_:
{
lean_object* v_fst_3496_; lean_object* v_snd_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3623_; 
v_fst_3496_ = lean_ctor_get(v_snd_3491_, 0);
v_snd_3497_ = lean_ctor_get(v_snd_3491_, 1);
v_isSharedCheck_3623_ = !lean_is_exclusive(v_snd_3491_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3499_ = v_snd_3491_;
v_isShared_3500_ = v_isSharedCheck_3623_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_snd_3497_);
lean_inc(v_fst_3496_);
lean_dec(v_snd_3491_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3623_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v_exportedInfo_x3f_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___x_3613_; lean_object* v_env_3614_; uint8_t v___x_3615_; 
v___x_3613_ = lean_st_ref_get(v___y_3393_);
v_env_3614_ = lean_ctor_get(v___x_3613_, 0);
lean_inc_ref(v_env_3614_);
lean_dec(v___x_3613_);
v___x_3615_ = l_Lean_Environment_containsOnBranch(v_env_3614_, v_fst_3492_);
lean_dec_ref(v_env_3614_);
if (v___x_3615_ == 0)
{
lean_del_object(v___x_3494_);
v___y_3552_ = v___y_3392_;
v___y_3553_ = v___y_3393_;
goto v___jp_3551_;
}
else
{
lean_object* v___x_3616_; lean_object* v_env_3617_; lean_object* v___x_3618_; lean_object* v___x_3620_; 
lean_del_object(v___x_3499_);
lean_dec(v_snd_3497_);
lean_dec(v_fst_3496_);
lean_dec(v_exportedInfo_x3f_3391_);
lean_dec(v___x_3389_);
lean_dec_ref(v___x_3388_);
lean_dec(v_cls_3387_);
lean_dec(v_decl_3385_);
v___x_3616_ = lean_st_ref_get(v___y_3393_);
v_env_3617_ = lean_ctor_get(v___x_3616_, 0);
lean_inc_ref(v_env_3617_);
lean_dec(v___x_3616_);
v___x_3618_ = lean_elab_environment_to_kernel_env(v_env_3617_);
if (v_isShared_3495_ == 0)
{
lean_ctor_set_tag(v___x_3494_, 1);
lean_ctor_set(v___x_3494_, 1, v_fst_3492_);
lean_ctor_set(v___x_3494_, 0, v___x_3618_);
v___x_3620_ = v___x_3494_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v___x_3618_);
lean_ctor_set(v_reuseFailAlloc_3622_, 1, v_fst_3492_);
v___x_3620_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
lean_object* v___x_3621_; 
v___x_3621_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3620_, v___y_3392_, v___y_3393_);
return v___x_3621_;
}
}
v___jp_3501_:
{
lean_object* v_ref_3507_; uint8_t v___x_3508_; uint8_t v___x_3509_; lean_object* v___x_3510_; 
v_ref_3507_ = lean_ctor_get(v___y_3503_, 2);
v___x_3508_ = 0;
v___x_3509_ = lean_unbox(v_snd_3497_);
lean_dec(v_snd_3497_);
lean_inc_ref(v___y_3505_);
v___x_3510_ = l_Lean_Environment_addConstAsync(v___y_3505_, v_fst_3492_, v___x_3509_, v___y_3506_, v___x_3508_, v___x_3386_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v_a_3511_; lean_object* v_mainEnv_3512_; lean_object* v_asyncEnv_3513_; lean_object* v___f_3514_; lean_object* v___f_3515_; lean_object* v___x_3516_; 
lean_del_object(v___x_3499_);
v_a_3511_ = lean_ctor_get(v___x_3510_, 0);
lean_inc_n(v_a_3511_, 3);
lean_dec_ref_known(v___x_3510_, 1);
v_mainEnv_3512_ = lean_ctor_get(v_a_3511_, 0);
lean_inc_ref(v_mainEnv_3512_);
v_asyncEnv_3513_ = lean_ctor_get(v_a_3511_, 1);
lean_inc_ref_n(v_asyncEnv_3513_, 2);
lean_inc(v_ref_3507_);
lean_inc(v___y_3502_);
v___f_3514_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3514_, 0, v___y_3502_);
lean_closure_set(v___f_3514_, 1, v_a_3511_);
lean_closure_set(v___f_3514_, 2, v_ref_3507_);
lean_inc(v_decl_3385_);
v___f_3515_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3515_, 0, v_a_3511_);
lean_closure_set(v___f_3515_, 1, v_asyncEnv_3513_);
lean_closure_set(v___f_3515_, 2, v_decl_3385_);
v___x_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3516_, 0, v_fst_3496_);
if (lean_obj_tag(v___y_3504_) == 0)
{
lean_inc(v_ref_3507_);
lean_inc_ref(v___x_3516_);
v___y_3409_ = v_asyncEnv_3513_;
v___y_3410_ = v___y_3503_;
v___y_3411_ = v___x_3516_;
v___y_3412_ = v___f_3514_;
v___y_3413_ = v___y_3502_;
v___y_3414_ = v_ref_3507_;
v___y_3415_ = v___y_3505_;
v___y_3416_ = v___f_3515_;
v___y_3417_ = v___x_3508_;
v___y_3418_ = v_a_3511_;
v___y_3419_ = v_mainEnv_3512_;
v___y_3420_ = v___x_3516_;
goto v___jp_3408_;
}
else
{
lean_inc(v_ref_3507_);
v___y_3409_ = v_asyncEnv_3513_;
v___y_3410_ = v___y_3503_;
v___y_3411_ = v___x_3516_;
v___y_3412_ = v___f_3514_;
v___y_3413_ = v___y_3502_;
v___y_3414_ = v_ref_3507_;
v___y_3415_ = v___y_3505_;
v___y_3416_ = v___f_3515_;
v___y_3417_ = v___x_3508_;
v___y_3418_ = v_a_3511_;
v___y_3419_ = v_mainEnv_3512_;
v___y_3420_ = v___y_3504_;
goto v___jp_3408_;
}
}
else
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3530_; 
lean_dec_ref(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec(v_fst_3496_);
lean_dec(v_decl_3385_);
v_a_3517_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3519_ = v___x_3510_;
v_isShared_3520_ = v_isSharedCheck_3530_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3510_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3530_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3525_; 
v___x_3521_ = lean_io_error_to_string(v_a_3517_);
v___x_3522_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3521_);
v___x_3523_ = l_Lean_MessageData_ofFormat(v___x_3522_);
lean_inc(v_ref_3507_);
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 1, v___x_3523_);
lean_ctor_set(v___x_3499_, 0, v_ref_3507_);
v___x_3525_ = v___x_3499_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_ref_3507_);
lean_ctor_set(v_reuseFailAlloc_3529_, 1, v___x_3523_);
v___x_3525_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
lean_object* v___x_3527_; 
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 0, v___x_3525_);
v___x_3527_ = v___x_3519_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3525_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
}
}
}
v___jp_3531_:
{
lean_object* v___x_3535_; 
v___x_3535_ = lean_st_ref_get(v___y_3534_);
if (lean_obj_tag(v_exportedInfo_x3f_3532_) == 0)
{
lean_object* v_env_3536_; lean_object* v___x_3537_; 
v_env_3536_ = lean_ctor_get(v___x_3535_, 0);
lean_inc_ref(v_env_3536_);
lean_dec(v___x_3535_);
v___x_3537_ = lean_box(0);
v___y_3502_ = v___y_3534_;
v___y_3503_ = v___y_3533_;
v___y_3504_ = v_exportedInfo_x3f_3532_;
v___y_3505_ = v_env_3536_;
v___y_3506_ = v___x_3537_;
goto v___jp_3501_;
}
else
{
lean_object* v_env_3538_; lean_object* v_val_3539_; uint8_t v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; 
v_env_3538_ = lean_ctor_get(v___x_3535_, 0);
lean_inc_ref(v_env_3538_);
lean_dec(v___x_3535_);
v_val_3539_ = lean_ctor_get(v_exportedInfo_x3f_3532_, 0);
v___x_3540_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3539_);
v___x_3541_ = lean_box(v___x_3540_);
v___x_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3541_);
v___y_3502_ = v___y_3534_;
v___y_3503_ = v___y_3533_;
v___y_3504_ = v_exportedInfo_x3f_3532_;
v___y_3505_ = v_env_3538_;
v___y_3506_ = v___x_3542_;
goto v___jp_3501_;
}
}
v___jp_3543_:
{
lean_object* v___x_3546_; 
lean_inc(v_fst_3496_);
v___x_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3546_, 0, v_fst_3496_);
v_exportedInfo_x3f_3532_ = v___x_3546_;
v___y_3533_ = v___y_3544_;
v___y_3534_ = v___y_3545_;
goto v___jp_3531_;
}
v___jp_3547_:
{
lean_object* v___x_3550_; 
lean_inc(v_fst_3496_);
v___x_3550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3550_, 0, v_fst_3496_);
v_exportedInfo_x3f_3532_ = v___x_3550_;
v___y_3533_ = v___y_3548_;
v___y_3534_ = v___y_3549_;
goto v___jp_3531_;
}
v___jp_3551_:
{
lean_object* v___x_3554_; uint8_t v___x_3555_; 
lean_inc(v_decl_3385_);
v___x_3554_ = l_Lean_Declaration_getTopLevelNames(v_decl_3385_);
v___x_3555_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3554_);
lean_dec(v___x_3554_);
if (v___x_3555_ == 0)
{
lean_dec(v___x_3389_);
if (lean_obj_tag(v_exportedInfo_x3f_3391_) == 0)
{
lean_object* v_toCold_3556_; lean_object* v_options_3557_; uint8_t v_hasTrace_3558_; 
lean_dec_ref(v___x_3388_);
v_toCold_3556_ = lean_ctor_get(v___y_3552_, 0);
v_options_3557_ = lean_ctor_get(v_toCold_3556_, 2);
v_hasTrace_3558_ = lean_ctor_get_uint8(v_options_3557_, sizeof(void*)*1);
if (v_hasTrace_3558_ == 0)
{
lean_dec(v_cls_3387_);
v___y_3544_ = v___y_3552_;
v___y_3545_ = v___y_3553_;
goto v___jp_3543_;
}
else
{
lean_object* v_inheritedTraceOptions_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; uint8_t v___x_3562_; 
v_inheritedTraceOptions_3559_ = lean_ctor_get(v_toCold_3556_, 11);
v___x_3560_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3387_);
v___x_3561_ = l_Lean_Name_append(v___x_3560_, v_cls_3387_);
v___x_3562_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3559_, v_options_3557_, v___x_3561_);
lean_dec(v___x_3561_);
if (v___x_3562_ == 0)
{
lean_dec(v_cls_3387_);
v___y_3544_ = v___y_3552_;
v___y_3545_ = v___y_3553_;
goto v___jp_3543_;
}
else
{
lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3563_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_3564_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3387_, v___x_3563_, v___y_3552_, v___y_3553_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_dec_ref_known(v___x_3564_, 1);
v___y_3544_ = v___y_3552_;
v___y_3545_ = v___y_3553_;
goto v___jp_3543_;
}
else
{
lean_del_object(v___x_3499_);
lean_dec(v_snd_3497_);
lean_dec(v_fst_3496_);
lean_dec(v_fst_3492_);
lean_dec(v_decl_3385_);
return v___x_3564_;
}
}
}
}
else
{
lean_object* v___x_3565_; lean_object* v_env_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; uint8_t v___x_3569_; lean_object* v___x_3570_; 
lean_dec(v_cls_3387_);
v___x_3565_ = lean_st_ref_get(v___y_3553_);
v_env_3566_ = lean_ctor_get(v___x_3565_, 0);
lean_inc_ref(v_env_3566_);
lean_dec(v___x_3565_);
v___x_3567_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_3568_ = lean_box(1);
v___x_3569_ = 0;
lean_inc(v_fst_3492_);
v___x_3570_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3567_, v_env_3566_, v_fst_3492_, v___x_3568_, v___x_3569_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v___x_3571_; lean_object* v_env_3572_; lean_object* v_nextMacroScope_3573_; lean_object* v_ngen_3574_; lean_object* v_auxDeclNGen_3575_; lean_object* v_traceState_3576_; lean_object* v_recordedDeps_3577_; lean_object* v_messages_3578_; lean_object* v_infoState_3579_; lean_object* v_snapshotTasks_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3589_; 
v___x_3571_ = lean_st_ref_take(v___y_3553_);
v_env_3572_ = lean_ctor_get(v___x_3571_, 0);
v_nextMacroScope_3573_ = lean_ctor_get(v___x_3571_, 1);
v_ngen_3574_ = lean_ctor_get(v___x_3571_, 2);
v_auxDeclNGen_3575_ = lean_ctor_get(v___x_3571_, 3);
v_traceState_3576_ = lean_ctor_get(v___x_3571_, 4);
v_recordedDeps_3577_ = lean_ctor_get(v___x_3571_, 6);
v_messages_3578_ = lean_ctor_get(v___x_3571_, 7);
v_infoState_3579_ = lean_ctor_get(v___x_3571_, 8);
v_snapshotTasks_3580_ = lean_ctor_get(v___x_3571_, 9);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3589_ == 0)
{
lean_object* v_unused_3590_; 
v_unused_3590_ = lean_ctor_get(v___x_3571_, 5);
lean_dec(v_unused_3590_);
v___x_3582_ = v___x_3571_;
v_isShared_3583_ = v_isSharedCheck_3589_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_snapshotTasks_3580_);
lean_inc(v_infoState_3579_);
lean_inc(v_messages_3578_);
lean_inc(v_recordedDeps_3577_);
lean_inc(v_traceState_3576_);
lean_inc(v_auxDeclNGen_3575_);
lean_inc(v_ngen_3574_);
lean_inc(v_nextMacroScope_3573_);
lean_inc(v_env_3572_);
lean_dec(v___x_3571_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3589_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3584_; lean_object* v___x_3586_; 
lean_inc(v_snd_3497_);
lean_inc(v_fst_3492_);
v___x_3584_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3567_, v_env_3572_, v_fst_3492_, v_snd_3497_, v___x_3555_);
if (v_isShared_3583_ == 0)
{
lean_ctor_set(v___x_3582_, 5, v___x_3388_);
lean_ctor_set(v___x_3582_, 0, v___x_3584_);
v___x_3586_ = v___x_3582_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3584_);
lean_ctor_set(v_reuseFailAlloc_3588_, 1, v_nextMacroScope_3573_);
lean_ctor_set(v_reuseFailAlloc_3588_, 2, v_ngen_3574_);
lean_ctor_set(v_reuseFailAlloc_3588_, 3, v_auxDeclNGen_3575_);
lean_ctor_set(v_reuseFailAlloc_3588_, 4, v_traceState_3576_);
lean_ctor_set(v_reuseFailAlloc_3588_, 5, v___x_3388_);
lean_ctor_set(v_reuseFailAlloc_3588_, 6, v_recordedDeps_3577_);
lean_ctor_set(v_reuseFailAlloc_3588_, 7, v_messages_3578_);
lean_ctor_set(v_reuseFailAlloc_3588_, 8, v_infoState_3579_);
lean_ctor_set(v_reuseFailAlloc_3588_, 9, v_snapshotTasks_3580_);
v___x_3586_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
lean_object* v___x_3587_; 
v___x_3587_ = lean_st_ref_put(v___y_3553_, v___x_3586_);
v_exportedInfo_x3f_3532_ = v_exportedInfo_x3f_3391_;
v___y_3533_ = v___y_3552_;
v___y_3534_ = v___y_3553_;
goto v___jp_3531_;
}
}
}
else
{
lean_dec_ref_known(v___x_3570_, 1);
lean_dec_ref(v___x_3388_);
v_exportedInfo_x3f_3532_ = v_exportedInfo_x3f_3391_;
v___y_3533_ = v___y_3552_;
v___y_3534_ = v___y_3553_;
goto v___jp_3531_;
}
}
}
else
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v_a_3593_; uint8_t v___x_3594_; 
lean_dec(v_exportedInfo_x3f_3391_);
lean_dec_ref(v___x_3388_);
v___x_3591_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3592_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3591_, v___y_3552_);
v_a_3593_ = lean_ctor_get(v___x_3592_, 0);
lean_inc(v_a_3593_);
lean_dec_ref(v___x_3592_);
v___x_3594_ = lean_unbox(v_a_3593_);
lean_dec(v_a_3593_);
if (v___x_3594_ == 0)
{
lean_object* v_toCold_3595_; lean_object* v_options_3596_; uint8_t v_hasTrace_3597_; 
v_toCold_3595_ = lean_ctor_get(v___y_3552_, 0);
v_options_3596_ = lean_ctor_get(v_toCold_3595_, 2);
v_hasTrace_3597_ = lean_ctor_get_uint8(v_options_3596_, sizeof(void*)*1);
if (v_hasTrace_3597_ == 0)
{
lean_dec(v_cls_3387_);
v_exportedInfo_x3f_3532_ = v___x_3389_;
v___y_3533_ = v___y_3552_;
v___y_3534_ = v___y_3553_;
goto v___jp_3531_;
}
else
{
lean_object* v_inheritedTraceOptions_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; uint8_t v___x_3601_; 
v_inheritedTraceOptions_3598_ = lean_ctor_get(v_toCold_3595_, 11);
v___x_3599_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3387_);
v___x_3600_ = l_Lean_Name_append(v___x_3599_, v_cls_3387_);
v___x_3601_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3598_, v_options_3596_, v___x_3600_);
lean_dec(v___x_3600_);
if (v___x_3601_ == 0)
{
lean_dec(v_cls_3387_);
v_exportedInfo_x3f_3532_ = v___x_3389_;
v___y_3533_ = v___y_3552_;
v___y_3534_ = v___y_3553_;
goto v___jp_3531_;
}
else
{
lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3602_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_3603_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3387_, v___x_3602_, v___y_3552_, v___y_3553_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_dec_ref_known(v___x_3603_, 1);
v_exportedInfo_x3f_3532_ = v___x_3389_;
v___y_3533_ = v___y_3552_;
v___y_3534_ = v___y_3553_;
goto v___jp_3531_;
}
else
{
lean_del_object(v___x_3499_);
lean_dec(v_snd_3497_);
lean_dec(v_fst_3496_);
lean_dec(v_fst_3492_);
lean_dec(v___x_3389_);
lean_dec(v_decl_3385_);
return v___x_3603_;
}
}
}
}
else
{
lean_object* v_toCold_3604_; lean_object* v_options_3605_; uint8_t v_hasTrace_3606_; 
lean_dec(v___x_3389_);
v_toCold_3604_ = lean_ctor_get(v___y_3552_, 0);
v_options_3605_ = lean_ctor_get(v_toCold_3604_, 2);
v_hasTrace_3606_ = lean_ctor_get_uint8(v_options_3605_, sizeof(void*)*1);
if (v_hasTrace_3606_ == 0)
{
lean_dec(v_cls_3387_);
v___y_3548_ = v___y_3552_;
v___y_3549_ = v___y_3553_;
goto v___jp_3547_;
}
else
{
lean_object* v_inheritedTraceOptions_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; uint8_t v___x_3610_; 
v_inheritedTraceOptions_3607_ = lean_ctor_get(v_toCold_3604_, 11);
v___x_3608_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3387_);
v___x_3609_ = l_Lean_Name_append(v___x_3608_, v_cls_3387_);
v___x_3610_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3607_, v_options_3605_, v___x_3609_);
lean_dec(v___x_3609_);
if (v___x_3610_ == 0)
{
lean_dec(v_cls_3387_);
v___y_3548_ = v___y_3552_;
v___y_3549_ = v___y_3553_;
goto v___jp_3547_;
}
else
{
lean_object* v___x_3611_; lean_object* v___x_3612_; 
v___x_3611_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_3612_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3387_, v___x_3611_, v___y_3552_, v___y_3553_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_dec_ref_known(v___x_3612_, 1);
v___y_3548_ = v___y_3552_;
v___y_3549_ = v___y_3553_;
goto v___jp_3547_;
}
else
{
lean_del_object(v___x_3499_);
lean_dec(v_snd_3497_);
lean_dec(v_fst_3496_);
lean_dec(v_fst_3492_);
lean_dec(v_decl_3385_);
return v___x_3612_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14___boxed(lean_object* v_decl_3625_, lean_object* v___x_3626_, lean_object* v_cls_3627_, lean_object* v___x_3628_, lean_object* v___x_3629_, lean_object* v_____x_3630_, lean_object* v_exportedInfo_x3f_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
uint8_t v___x_55510__boxed_3635_; lean_object* v_res_3636_; 
v___x_55510__boxed_3635_ = lean_unbox(v___x_3626_);
v_res_3636_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(v_decl_3625_, v___x_55510__boxed_3635_, v_cls_3627_, v___x_3628_, v___x_3629_, v_____x_3630_, v_exportedInfo_x3f_3631_, v___y_3632_, v___y_3633_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(lean_object* v___f_3637_, uint8_t v_forceExpose_3638_, lean_object* v___x_3639_, lean_object* v_cls_3640_, lean_object* v_defn_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
lean_object* v_exportedInfo_x3f_3646_; lean_object* v___y_3647_; lean_object* v___y_3648_; lean_object* v___y_3658_; lean_object* v___y_3659_; lean_object* v___y_3660_; uint8_t v___y_3661_; lean_object* v___x_3665_; lean_object* v_env_3666_; lean_object* v___x_3667_; 
v___x_3665_ = lean_st_ref_get(v___y_3643_);
v_env_3666_ = lean_ctor_get(v___x_3665_, 0);
lean_inc_ref(v_env_3666_);
lean_dec(v___x_3665_);
v___x_3667_ = lean_st_ref_get(v___y_3643_);
if (v_forceExpose_3638_ == 0)
{
lean_object* v_env_3668_; lean_object* v___x_3669_; uint8_t v_isModule_3670_; 
v_env_3668_ = lean_ctor_get(v___x_3667_, 0);
lean_inc_ref(v_env_3668_);
lean_dec(v___x_3667_);
v___x_3669_ = l_Lean_Environment_header(v_env_3666_);
lean_dec_ref(v_env_3666_);
v_isModule_3670_ = lean_ctor_get_uint8(v___x_3669_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_3669_);
if (v_isModule_3670_ == 0)
{
lean_dec_ref(v_env_3668_);
lean_dec(v_cls_3640_);
v_exportedInfo_x3f_3646_ = v___x_3639_;
v___y_3647_ = v___y_3642_;
v___y_3648_ = v___y_3643_;
goto v___jp_3645_;
}
else
{
uint8_t v_isExporting_3671_; lean_object* v___y_3673_; lean_object* v___y_3674_; 
v_isExporting_3671_ = lean_ctor_get_uint8(v_env_3668_, sizeof(void*)*13);
lean_dec_ref(v_env_3668_);
if (v_isExporting_3671_ == 0)
{
lean_object* v_toCold_3679_; lean_object* v_options_3680_; uint8_t v_hasTrace_3681_; 
lean_dec(v___x_3639_);
v_toCold_3679_ = lean_ctor_get(v___y_3642_, 0);
v_options_3680_ = lean_ctor_get(v_toCold_3679_, 2);
v_hasTrace_3681_ = lean_ctor_get_uint8(v_options_3680_, sizeof(void*)*1);
if (v_hasTrace_3681_ == 0)
{
lean_dec(v_cls_3640_);
v___y_3673_ = v___y_3642_;
v___y_3674_ = v___y_3643_;
goto v___jp_3672_;
}
else
{
lean_object* v_inheritedTraceOptions_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; uint8_t v___x_3685_; 
v_inheritedTraceOptions_3682_ = lean_ctor_get(v_toCold_3679_, 11);
v___x_3683_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3640_);
v___x_3684_ = l_Lean_Name_append(v___x_3683_, v_cls_3640_);
v___x_3685_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3682_, v_options_3680_, v___x_3684_);
lean_dec(v___x_3684_);
if (v___x_3685_ == 0)
{
lean_dec(v_cls_3640_);
v___y_3673_ = v___y_3642_;
v___y_3674_ = v___y_3643_;
goto v___jp_3672_;
}
else
{
lean_object* v_toConstantVal_3686_; lean_object* v_name_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
v_toConstantVal_3686_ = lean_ctor_get(v_defn_3641_, 0);
v_name_3687_ = lean_ctor_get(v_toConstantVal_3686_, 0);
v___x_3688_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_3687_);
v___x_3689_ = l_Lean_MessageData_ofName(v_name_3687_);
v___x_3690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3688_);
lean_ctor_set(v___x_3690_, 1, v___x_3689_);
v___x_3691_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_3692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3690_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
v___x_3693_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3640_, v___x_3692_, v___y_3642_, v___y_3643_);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_dec_ref_known(v___x_3693_, 1);
v___y_3673_ = v___y_3642_;
v___y_3674_ = v___y_3643_;
goto v___jp_3672_;
}
else
{
lean_dec_ref(v_defn_3641_);
lean_dec_ref(v___f_3637_);
return v___x_3693_;
}
}
}
}
else
{
lean_dec(v_cls_3640_);
v_exportedInfo_x3f_3646_ = v___x_3639_;
v___y_3647_ = v___y_3642_;
v___y_3648_ = v___y_3643_;
goto v___jp_3645_;
}
v___jp_3672_:
{
lean_object* v_toConstantVal_3675_; uint8_t v_safety_3676_; uint8_t v___x_3677_; uint8_t v___x_3678_; 
v_toConstantVal_3675_ = lean_ctor_get(v_defn_3641_, 0);
v_safety_3676_ = lean_ctor_get_uint8(v_defn_3641_, sizeof(void*)*4);
v___x_3677_ = 1;
v___x_3678_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3676_, v___x_3677_);
if (v___x_3678_ == 0)
{
lean_inc_ref(v_toConstantVal_3675_);
v___y_3658_ = v___y_3674_;
v___y_3659_ = v___y_3673_;
v___y_3660_ = v_toConstantVal_3675_;
v___y_3661_ = v_isModule_3670_;
goto v___jp_3657_;
}
else
{
lean_inc_ref(v_toConstantVal_3675_);
v___y_3658_ = v___y_3674_;
v___y_3659_ = v___y_3673_;
v___y_3660_ = v_toConstantVal_3675_;
v___y_3661_ = v_isExporting_3671_;
goto v___jp_3657_;
}
}
}
}
else
{
lean_dec(v___x_3667_);
lean_dec_ref(v_env_3666_);
lean_dec(v_cls_3640_);
v_exportedInfo_x3f_3646_ = v___x_3639_;
v___y_3647_ = v___y_3642_;
v___y_3648_ = v___y_3643_;
goto v___jp_3645_;
}
v___jp_3645_:
{
lean_object* v_toConstantVal_3649_; lean_object* v_name_3650_; lean_object* v___x_3651_; uint8_t v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
v_toConstantVal_3649_ = lean_ctor_get(v_defn_3641_, 0);
v_name_3650_ = lean_ctor_get(v_toConstantVal_3649_, 0);
lean_inc(v_name_3650_);
v___x_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3651_, 0, v_defn_3641_);
v___x_3652_ = 0;
v___x_3653_ = lean_box(v___x_3652_);
v___x_3654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3651_);
lean_ctor_set(v___x_3654_, 1, v___x_3653_);
v___x_3655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3655_, 0, v_name_3650_);
lean_ctor_set(v___x_3655_, 1, v___x_3654_);
lean_inc(v___y_3648_);
lean_inc_ref(v___y_3647_);
v___x_3656_ = lean_apply_5(v___f_3637_, v___x_3655_, v_exportedInfo_x3f_3646_, v___y_3647_, v___y_3648_, lean_box(0));
return v___x_3656_;
}
v___jp_3657_:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3662_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3662_, 0, v___y_3660_);
lean_ctor_set_uint8(v___x_3662_, sizeof(void*)*1, v___y_3661_);
v___x_3663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3662_);
v___x_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3663_);
v_exportedInfo_x3f_3646_ = v___x_3664_;
v___y_3647_ = v___y_3659_;
v___y_3648_ = v___y_3658_;
goto v___jp_3645_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11___boxed(lean_object* v___f_3694_, lean_object* v_forceExpose_3695_, lean_object* v___x_3696_, lean_object* v_cls_3697_, lean_object* v_defn_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_){
_start:
{
uint8_t v_forceExpose_boxed_3702_; lean_object* v_res_3703_; 
v_forceExpose_boxed_3702_ = lean_unbox(v_forceExpose_3695_);
v_res_3703_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(v___f_3694_, v_forceExpose_boxed_3702_, v___x_3696_, v_cls_3697_, v_defn_3698_, v___y_3699_, v___y_3700_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
return v_res_3703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(lean_object* v_val_3704_, lean_object* v___f_3705_, lean_object* v_____r_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_){
_start:
{
lean_object* v_toConstantVal_3710_; uint8_t v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; 
v_toConstantVal_3710_ = lean_ctor_get(v_val_3704_, 0);
v___x_3711_ = 0;
lean_inc_ref(v_toConstantVal_3710_);
v___x_3712_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3712_, 0, v_toConstantVal_3710_);
lean_ctor_set_uint8(v___x_3712_, sizeof(void*)*1, v___x_3711_);
v___x_3713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3712_);
v___x_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3713_);
v___x_3715_ = lean_box(0);
lean_inc(v___y_3708_);
lean_inc_ref(v___y_3707_);
v___x_3716_ = lean_apply_5(v___f_3705_, v___x_3715_, v___x_3714_, v___y_3707_, v___y_3708_, lean_box(0));
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed(lean_object* v_val_3717_, lean_object* v___f_3718_, lean_object* v_____r_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_){
_start:
{
lean_object* v_res_3723_; 
v_res_3723_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_val_3717_, v___f_3718_, v_____r_3719_, v___y_3720_, v___y_3721_);
lean_dec(v___y_3721_);
lean_dec_ref(v___y_3720_);
lean_dec_ref(v_val_3717_);
return v_res_3723_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(lean_object* v_x_3724_, lean_object* v_x_3725_){
_start:
{
if (lean_obj_tag(v_x_3725_) == 0)
{
return v_x_3724_;
}
else
{
lean_object* v_head_3726_; lean_object* v_tail_3727_; lean_object* v___x_3728_; 
v_head_3726_ = lean_ctor_get(v_x_3725_, 0);
lean_inc(v_head_3726_);
v_tail_3727_ = lean_ctor_get(v_x_3725_, 1);
lean_inc(v_tail_3727_);
lean_dec_ref_known(v_x_3725_, 2);
v___x_3728_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(v_x_3724_, v_head_3726_);
v_x_3724_ = v___x_3728_;
v_x_3725_ = v_tail_3727_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0(void){
_start:
{
lean_object* v_cls_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; 
v_cls_3730_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_3731_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
v___x_3732_ = l_Lean_Name_append(v___x_3731_, v_cls_3730_);
return v___x_3732_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2(void){
_start:
{
lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3734_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1));
v___x_3735_ = l_Lean_stringToMessageData(v___x_3734_);
return v___x_3735_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4(void){
_start:
{
lean_object* v___x_3737_; lean_object* v___x_3738_; 
v___x_3737_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3));
v___x_3738_ = l_Lean_stringToMessageData(v___x_3737_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore(lean_object* v_decl_3739_, uint8_t v_forceExpose_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_){
_start:
{
lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v_a_3747_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v_a_3760_; lean_object* v_toCold_3770_; lean_object* v_options_3771_; lean_object* v_inheritedTraceOptions_3772_; uint8_t v_hasTrace_3773_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; uint8_t v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; uint8_t v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3888_; lean_object* v___y_3889_; uint8_t v___y_3890_; lean_object* v_exportedInfo_x3f_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3903_; uint8_t v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3910_; uint8_t v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v_cls_3916_; lean_object* v___y_3918_; lean_object* v_options_3919_; lean_object* v_inheritedTraceOptions_3920_; lean_object* v___y_3921_; 
v_toCold_3770_ = lean_ctor_get(v_a_3741_, 0);
v_options_3771_ = lean_ctor_get(v_toCold_3770_, 2);
v_inheritedTraceOptions_3772_ = lean_ctor_get(v_toCold_3770_, 11);
v_hasTrace_3773_ = lean_ctor_get_uint8(v_options_3771_, sizeof(void*)*1);
v_cls_3916_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
if (v_hasTrace_3773_ == 0)
{
lean_object* v___x_3928_; lean_object* v_env_3929_; lean_object* v_nextMacroScope_3930_; lean_object* v_ngen_3931_; lean_object* v_auxDeclNGen_3932_; lean_object* v_traceState_3933_; lean_object* v_recordedDeps_3934_; lean_object* v_messages_3935_; lean_object* v_infoState_3936_; lean_object* v_snapshotTasks_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_4138_; 
v___x_3928_ = lean_st_ref_take(v_a_3742_);
v_env_3929_ = lean_ctor_get(v___x_3928_, 0);
v_nextMacroScope_3930_ = lean_ctor_get(v___x_3928_, 1);
v_ngen_3931_ = lean_ctor_get(v___x_3928_, 2);
v_auxDeclNGen_3932_ = lean_ctor_get(v___x_3928_, 3);
v_traceState_3933_ = lean_ctor_get(v___x_3928_, 4);
v_recordedDeps_3934_ = lean_ctor_get(v___x_3928_, 6);
v_messages_3935_ = lean_ctor_get(v___x_3928_, 7);
v_infoState_3936_ = lean_ctor_get(v___x_3928_, 8);
v_snapshotTasks_3937_ = lean_ctor_get(v___x_3928_, 9);
v_isSharedCheck_4138_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_4138_ == 0)
{
lean_object* v_unused_4139_; 
v_unused_4139_ = lean_ctor_get(v___x_3928_, 5);
lean_dec(v_unused_4139_);
v___x_3939_ = v___x_3928_;
v_isShared_3940_ = v_isSharedCheck_4138_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_snapshotTasks_3937_);
lean_inc(v_infoState_3936_);
lean_inc(v_messages_3935_);
lean_inc(v_recordedDeps_3934_);
lean_inc(v_traceState_3933_);
lean_inc(v_auxDeclNGen_3932_);
lean_inc(v_ngen_3931_);
lean_inc(v_nextMacroScope_3930_);
lean_inc(v_env_3929_);
lean_dec(v___x_3928_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_4138_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3945_; 
lean_inc(v_decl_3739_);
v___x_3941_ = l_Lean_Declaration_getNames(v_decl_3739_);
v___x_3942_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_3929_, v___x_3941_);
v___x_3943_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_3940_ == 0)
{
lean_ctor_set(v___x_3939_, 5, v___x_3943_);
lean_ctor_set(v___x_3939_, 0, v___x_3942_);
v___x_3945_ = v___x_3939_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v___x_3942_);
lean_ctor_set(v_reuseFailAlloc_4137_, 1, v_nextMacroScope_3930_);
lean_ctor_set(v_reuseFailAlloc_4137_, 2, v_ngen_3931_);
lean_ctor_set(v_reuseFailAlloc_4137_, 3, v_auxDeclNGen_3932_);
lean_ctor_set(v_reuseFailAlloc_4137_, 4, v_traceState_3933_);
lean_ctor_set(v_reuseFailAlloc_4137_, 5, v___x_3943_);
lean_ctor_set(v_reuseFailAlloc_4137_, 6, v_recordedDeps_3934_);
lean_ctor_set(v_reuseFailAlloc_4137_, 7, v_messages_3935_);
lean_ctor_set(v_reuseFailAlloc_4137_, 8, v_infoState_3936_);
lean_ctor_set(v_reuseFailAlloc_4137_, 9, v_snapshotTasks_3937_);
v___x_3945_ = v_reuseFailAlloc_4137_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; uint8_t v___y_3952_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v_fst_4013_; lean_object* v_fst_4014_; uint8_t v_snd_4015_; lean_object* v_exportedInfo_x3f_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4028_; lean_object* v_exportedInfo_x3f_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; uint8_t v___y_4041_; uint8_t v___y_4046_; lean_object* v___y_4047_; lean_object* v_toConstantVal_4048_; uint8_t v_safety_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; uint8_t v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v_defn_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; 
v___x_3946_ = lean_st_ref_put(v_a_3742_, v___x_3945_);
v___x_3947_ = lean_box(0);
switch(lean_obj_tag(v_decl_3739_))
{
case 2:
{
lean_object* v_val_4087_; lean_object* v_exportedInfo_x3f_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___x_4096_; 
v_val_4087_ = lean_ctor_get(v_decl_3739_, 0);
v___x_4096_ = lean_st_ref_get(v_a_3742_);
if (v_forceExpose_3740_ == 0)
{
lean_object* v_env_4097_; lean_object* v___x_4098_; uint8_t v_isModule_4099_; 
v_env_4097_ = lean_ctor_get(v___x_4096_, 0);
lean_inc_ref(v_env_4097_);
lean_dec(v___x_4096_);
v___x_4098_ = l_Lean_Environment_header(v_env_4097_);
lean_dec_ref(v_env_4097_);
v_isModule_4099_ = lean_ctor_get_uint8(v___x_4098_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4098_);
if (v_isModule_4099_ == 0)
{
v_exportedInfo_x3f_4089_ = v___x_3947_;
v___y_4090_ = v_a_3741_;
v___y_4091_ = v_a_3742_;
goto v___jp_4088_;
}
else
{
lean_object* v_toConstantVal_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; 
v_toConstantVal_4100_ = lean_ctor_get(v_val_4087_, 0);
lean_inc_ref(v_toConstantVal_4100_);
v___x_4101_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4101_, 0, v_toConstantVal_4100_);
lean_ctor_set_uint8(v___x_4101_, sizeof(void*)*1, v_hasTrace_3773_);
v___x_4102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4101_);
v___x_4103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4103_, 0, v___x_4102_);
v_exportedInfo_x3f_4089_ = v___x_4103_;
v___y_4090_ = v_a_3741_;
v___y_4091_ = v_a_3742_;
goto v___jp_4088_;
}
}
else
{
lean_dec(v___x_4096_);
v_exportedInfo_x3f_4089_ = v___x_3947_;
v___y_4090_ = v_a_3741_;
v___y_4091_ = v_a_3742_;
goto v___jp_4088_;
}
v___jp_4088_:
{
lean_object* v_toConstantVal_4092_; lean_object* v_name_4093_; lean_object* v___x_4094_; uint8_t v___x_4095_; 
v_toConstantVal_4092_ = lean_ctor_get(v_val_4087_, 0);
v_name_4093_ = lean_ctor_get(v_toConstantVal_4092_, 0);
lean_inc_ref(v_val_4087_);
v___x_4094_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4094_, 0, v_val_4087_);
v___x_4095_ = 1;
lean_inc(v_name_4093_);
v_fst_4013_ = v_name_4093_;
v_fst_4014_ = v___x_4094_;
v_snd_4015_ = v___x_4095_;
v_exportedInfo_x3f_4016_ = v_exportedInfo_x3f_4089_;
v___y_4017_ = v___y_4090_;
v___y_4018_ = v___y_4091_;
goto v___jp_4012_;
}
}
case 1:
{
lean_object* v_val_4104_; 
v_val_4104_ = lean_ctor_get(v_decl_3739_, 0);
lean_inc_ref(v_val_4104_);
v_defn_4062_ = v_val_4104_;
v___y_4063_ = v_a_3741_;
v___y_4064_ = v_a_3742_;
goto v___jp_4061_;
}
case 5:
{
lean_object* v_defns_4105_; 
v_defns_4105_ = lean_ctor_get(v_decl_3739_, 0);
if (lean_obj_tag(v_defns_4105_) == 1)
{
lean_object* v_tail_4106_; 
v_tail_4106_ = lean_ctor_get(v_defns_4105_, 1);
if (lean_obj_tag(v_tail_4106_) == 0)
{
lean_object* v_head_4107_; 
v_head_4107_ = lean_ctor_get(v_defns_4105_, 0);
lean_inc(v_head_4107_);
v_defn_4062_ = v_head_4107_;
v___y_4063_ = v_a_3741_;
v___y_4064_ = v_a_3742_;
goto v___jp_4061_;
}
else
{
lean_object* v___x_4108_; 
v___x_4108_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3739_, v_a_3741_, v_a_3742_);
return v___x_4108_;
}
}
else
{
lean_object* v___x_4109_; 
v___x_4109_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3739_, v_a_3741_, v_a_3742_);
return v___x_4109_;
}
}
case 3:
{
lean_object* v_val_4110_; lean_object* v_exportedInfo_x3f_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___x_4119_; lean_object* v_env_4120_; lean_object* v___x_4121_; 
v_val_4110_ = lean_ctor_get(v_decl_3739_, 0);
v___x_4119_ = lean_st_ref_get(v_a_3742_);
v_env_4120_ = lean_ctor_get(v___x_4119_, 0);
lean_inc_ref(v_env_4120_);
lean_dec(v___x_4119_);
v___x_4121_ = lean_st_ref_get(v_a_3742_);
if (v_forceExpose_3740_ == 0)
{
lean_object* v_env_4122_; lean_object* v___x_4123_; uint8_t v_isModule_4124_; 
v_env_4122_ = lean_ctor_get(v___x_4121_, 0);
lean_inc_ref(v_env_4122_);
lean_dec(v___x_4121_);
v___x_4123_ = l_Lean_Environment_header(v_env_4120_);
lean_dec_ref(v_env_4120_);
v_isModule_4124_ = lean_ctor_get_uint8(v___x_4123_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4123_);
if (v_isModule_4124_ == 0)
{
lean_dec_ref(v_env_4122_);
v_exportedInfo_x3f_4112_ = v___x_3947_;
v___y_4113_ = v_a_3741_;
v___y_4114_ = v_a_3742_;
goto v___jp_4111_;
}
else
{
uint8_t v_isExporting_4125_; 
v_isExporting_4125_ = lean_ctor_get_uint8(v_env_4122_, sizeof(void*)*13);
lean_dec_ref(v_env_4122_);
if (v_isExporting_4125_ == 0)
{
lean_object* v_toConstantVal_4126_; uint8_t v_isUnsafe_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
v_toConstantVal_4126_ = lean_ctor_get(v_val_4110_, 0);
v_isUnsafe_4127_ = lean_ctor_get_uint8(v_val_4110_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4126_);
v___x_4128_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4128_, 0, v_toConstantVal_4126_);
lean_ctor_set_uint8(v___x_4128_, sizeof(void*)*1, v_isUnsafe_4127_);
v___x_4129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4129_, 0, v___x_4128_);
v___x_4130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4130_, 0, v___x_4129_);
v_exportedInfo_x3f_4112_ = v___x_4130_;
v___y_4113_ = v_a_3741_;
v___y_4114_ = v_a_3742_;
goto v___jp_4111_;
}
else
{
v_exportedInfo_x3f_4112_ = v___x_3947_;
v___y_4113_ = v_a_3741_;
v___y_4114_ = v_a_3742_;
goto v___jp_4111_;
}
}
}
else
{
lean_dec(v___x_4121_);
lean_dec_ref(v_env_4120_);
v_exportedInfo_x3f_4112_ = v___x_3947_;
v___y_4113_ = v_a_3741_;
v___y_4114_ = v_a_3742_;
goto v___jp_4111_;
}
v___jp_4111_:
{
lean_object* v_toConstantVal_4115_; lean_object* v_name_4116_; lean_object* v___x_4117_; uint8_t v___x_4118_; 
v_toConstantVal_4115_ = lean_ctor_get(v_val_4110_, 0);
v_name_4116_ = lean_ctor_get(v_toConstantVal_4115_, 0);
lean_inc_ref(v_val_4110_);
v___x_4117_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4117_, 0, v_val_4110_);
v___x_4118_ = 3;
lean_inc(v_name_4116_);
v_fst_4013_ = v_name_4116_;
v_fst_4014_ = v___x_4117_;
v_snd_4015_ = v___x_4118_;
v_exportedInfo_x3f_4016_ = v_exportedInfo_x3f_4112_;
v___y_4017_ = v___y_4113_;
v___y_4018_ = v___y_4114_;
goto v___jp_4012_;
}
}
case 0:
{
lean_object* v_val_4131_; lean_object* v_toConstantVal_4132_; lean_object* v_name_4133_; lean_object* v___x_4134_; uint8_t v___x_4135_; 
v_val_4131_ = lean_ctor_get(v_decl_3739_, 0);
v_toConstantVal_4132_ = lean_ctor_get(v_val_4131_, 0);
v_name_4133_ = lean_ctor_get(v_toConstantVal_4132_, 0);
lean_inc_ref(v_val_4131_);
v___x_4134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4134_, 0, v_val_4131_);
v___x_4135_ = 2;
lean_inc(v_name_4133_);
v_fst_4013_ = v_name_4133_;
v_fst_4014_ = v___x_4134_;
v_snd_4015_ = v___x_4135_;
v_exportedInfo_x3f_4016_ = v___x_3947_;
v___y_4017_ = v_a_3741_;
v___y_4018_ = v_a_3742_;
goto v___jp_4012_;
}
default: 
{
lean_object* v___x_4136_; 
v___x_4136_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3739_, v_a_3741_, v_a_3742_);
return v___x_4136_;
}
}
v___jp_3948_:
{
lean_object* v___x_3955_; uint8_t v___x_3956_; 
lean_inc(v_decl_3739_);
v___x_3955_ = l_Lean_Declaration_getTopLevelNames(v_decl_3739_);
v___x_3956_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3955_);
lean_dec(v___x_3955_);
if (v___x_3956_ == 0)
{
if (lean_obj_tag(v___y_3950_) == 0)
{
lean_object* v_toCold_3957_; lean_object* v_options_3958_; uint8_t v_hasTrace_3959_; 
v_toCold_3957_ = lean_ctor_get(v___y_3953_, 0);
v_options_3958_ = lean_ctor_get(v_toCold_3957_, 2);
v_hasTrace_3959_ = lean_ctor_get_uint8(v_options_3958_, sizeof(void*)*1);
if (v_hasTrace_3959_ == 0)
{
v___y_3910_ = v___y_3949_;
v___y_3911_ = v___y_3952_;
v___y_3912_ = v___y_3951_;
v___y_3913_ = v___y_3953_;
v___y_3914_ = v___y_3954_;
goto v___jp_3909_;
}
else
{
lean_object* v_inheritedTraceOptions_3960_; lean_object* v___x_3961_; uint8_t v___x_3962_; 
v_inheritedTraceOptions_3960_ = lean_ctor_get(v_toCold_3957_, 11);
v___x_3961_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_3962_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3960_, v_options_3958_, v___x_3961_);
if (v___x_3962_ == 0)
{
v___y_3910_ = v___y_3949_;
v___y_3911_ = v___y_3952_;
v___y_3912_ = v___y_3951_;
v___y_3913_ = v___y_3953_;
v___y_3914_ = v___y_3954_;
goto v___jp_3909_;
}
else
{
lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3963_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_3964_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3916_, v___x_3963_, v___y_3953_, v___y_3954_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_dec_ref_known(v___x_3964_, 1);
v___y_3910_ = v___y_3949_;
v___y_3911_ = v___y_3952_;
v___y_3912_ = v___y_3951_;
v___y_3913_ = v___y_3953_;
v___y_3914_ = v___y_3954_;
goto v___jp_3909_;
}
else
{
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3949_);
lean_dec(v_decl_3739_);
return v___x_3964_;
}
}
}
}
else
{
lean_object* v___x_3965_; lean_object* v_env_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; uint8_t v___x_3969_; lean_object* v___x_3970_; 
v___x_3965_ = lean_st_ref_get(v___y_3954_);
v_env_3966_ = lean_ctor_get(v___x_3965_, 0);
lean_inc_ref(v_env_3966_);
lean_dec(v___x_3965_);
v___x_3967_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_3968_ = lean_box(1);
v___x_3969_ = 0;
lean_inc(v___y_3951_);
v___x_3970_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3967_, v_env_3966_, v___y_3951_, v___x_3968_, v___x_3969_);
if (lean_obj_tag(v___x_3970_) == 0)
{
lean_object* v___x_3971_; lean_object* v_env_3972_; lean_object* v_nextMacroScope_3973_; lean_object* v_ngen_3974_; lean_object* v_auxDeclNGen_3975_; lean_object* v_traceState_3976_; lean_object* v_recordedDeps_3977_; lean_object* v_messages_3978_; lean_object* v_infoState_3979_; lean_object* v_snapshotTasks_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3990_; 
v___x_3971_ = lean_st_ref_take(v___y_3954_);
v_env_3972_ = lean_ctor_get(v___x_3971_, 0);
v_nextMacroScope_3973_ = lean_ctor_get(v___x_3971_, 1);
v_ngen_3974_ = lean_ctor_get(v___x_3971_, 2);
v_auxDeclNGen_3975_ = lean_ctor_get(v___x_3971_, 3);
v_traceState_3976_ = lean_ctor_get(v___x_3971_, 4);
v_recordedDeps_3977_ = lean_ctor_get(v___x_3971_, 6);
v_messages_3978_ = lean_ctor_get(v___x_3971_, 7);
v_infoState_3979_ = lean_ctor_get(v___x_3971_, 8);
v_snapshotTasks_3980_ = lean_ctor_get(v___x_3971_, 9);
v_isSharedCheck_3990_ = !lean_is_exclusive(v___x_3971_);
if (v_isSharedCheck_3990_ == 0)
{
lean_object* v_unused_3991_; 
v_unused_3991_ = lean_ctor_get(v___x_3971_, 5);
lean_dec(v_unused_3991_);
v___x_3982_ = v___x_3971_;
v_isShared_3983_ = v_isSharedCheck_3990_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_snapshotTasks_3980_);
lean_inc(v_infoState_3979_);
lean_inc(v_messages_3978_);
lean_inc(v_recordedDeps_3977_);
lean_inc(v_traceState_3976_);
lean_inc(v_auxDeclNGen_3975_);
lean_inc(v_ngen_3974_);
lean_inc(v_nextMacroScope_3973_);
lean_inc(v_env_3972_);
lean_dec(v___x_3971_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3990_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3987_; 
v___x_3984_ = lean_box(v___y_3952_);
lean_inc(v___y_3951_);
v___x_3985_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3967_, v_env_3972_, v___y_3951_, v___x_3984_, v___x_3956_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 5, v___x_3943_);
lean_ctor_set(v___x_3982_, 0, v___x_3985_);
v___x_3987_ = v___x_3982_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3989_; 
v_reuseFailAlloc_3989_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3989_, 0, v___x_3985_);
lean_ctor_set(v_reuseFailAlloc_3989_, 1, v_nextMacroScope_3973_);
lean_ctor_set(v_reuseFailAlloc_3989_, 2, v_ngen_3974_);
lean_ctor_set(v_reuseFailAlloc_3989_, 3, v_auxDeclNGen_3975_);
lean_ctor_set(v_reuseFailAlloc_3989_, 4, v_traceState_3976_);
lean_ctor_set(v_reuseFailAlloc_3989_, 5, v___x_3943_);
lean_ctor_set(v_reuseFailAlloc_3989_, 6, v_recordedDeps_3977_);
lean_ctor_set(v_reuseFailAlloc_3989_, 7, v_messages_3978_);
lean_ctor_set(v_reuseFailAlloc_3989_, 8, v_infoState_3979_);
lean_ctor_set(v_reuseFailAlloc_3989_, 9, v_snapshotTasks_3980_);
v___x_3987_ = v_reuseFailAlloc_3989_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
lean_object* v___x_3988_; 
v___x_3988_ = lean_st_ref_put(v___y_3954_, v___x_3987_);
v___y_3888_ = v___y_3949_;
v___y_3889_ = v___y_3951_;
v___y_3890_ = v___y_3952_;
v_exportedInfo_x3f_3891_ = v___y_3950_;
v___y_3892_ = v___y_3953_;
v___y_3893_ = v___y_3954_;
goto v___jp_3887_;
}
}
}
else
{
lean_dec_ref_known(v___x_3970_, 1);
v___y_3888_ = v___y_3949_;
v___y_3889_ = v___y_3951_;
v___y_3890_ = v___y_3952_;
v_exportedInfo_x3f_3891_ = v___y_3950_;
v___y_3892_ = v___y_3953_;
v___y_3893_ = v___y_3954_;
goto v___jp_3887_;
}
}
}
else
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v_a_3994_; uint8_t v___x_3995_; 
lean_dec(v___y_3950_);
v___x_3992_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3993_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3992_, v___y_3953_);
v_a_3994_ = lean_ctor_get(v___x_3993_, 0);
lean_inc(v_a_3994_);
lean_dec_ref(v___x_3993_);
v___x_3995_ = lean_unbox(v_a_3994_);
lean_dec(v_a_3994_);
if (v___x_3995_ == 0)
{
lean_object* v_toCold_3996_; lean_object* v_options_3997_; uint8_t v_hasTrace_3998_; 
v_toCold_3996_ = lean_ctor_get(v___y_3953_, 0);
v_options_3997_ = lean_ctor_get(v_toCold_3996_, 2);
v_hasTrace_3998_ = lean_ctor_get_uint8(v_options_3997_, sizeof(void*)*1);
if (v_hasTrace_3998_ == 0)
{
v___y_3888_ = v___y_3949_;
v___y_3889_ = v___y_3951_;
v___y_3890_ = v___y_3952_;
v_exportedInfo_x3f_3891_ = v___x_3947_;
v___y_3892_ = v___y_3953_;
v___y_3893_ = v___y_3954_;
goto v___jp_3887_;
}
else
{
lean_object* v_inheritedTraceOptions_3999_; lean_object* v___x_4000_; uint8_t v___x_4001_; 
v_inheritedTraceOptions_3999_ = lean_ctor_get(v_toCold_3996_, 11);
v___x_4000_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4001_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3999_, v_options_3997_, v___x_4000_);
if (v___x_4001_ == 0)
{
v___y_3888_ = v___y_3949_;
v___y_3889_ = v___y_3951_;
v___y_3890_ = v___y_3952_;
v_exportedInfo_x3f_3891_ = v___x_3947_;
v___y_3892_ = v___y_3953_;
v___y_3893_ = v___y_3954_;
goto v___jp_3887_;
}
else
{
lean_object* v___x_4002_; lean_object* v___x_4003_; 
v___x_4002_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_4003_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3916_, v___x_4002_, v___y_3953_, v___y_3954_);
if (lean_obj_tag(v___x_4003_) == 0)
{
lean_dec_ref_known(v___x_4003_, 1);
v___y_3888_ = v___y_3949_;
v___y_3889_ = v___y_3951_;
v___y_3890_ = v___y_3952_;
v_exportedInfo_x3f_3891_ = v___x_3947_;
v___y_3892_ = v___y_3953_;
v___y_3893_ = v___y_3954_;
goto v___jp_3887_;
}
else
{
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3949_);
lean_dec(v_decl_3739_);
return v___x_4003_;
}
}
}
}
else
{
lean_object* v_toCold_4004_; lean_object* v_options_4005_; uint8_t v_hasTrace_4006_; 
v_toCold_4004_ = lean_ctor_get(v___y_3953_, 0);
v_options_4005_ = lean_ctor_get(v_toCold_4004_, 2);
v_hasTrace_4006_ = lean_ctor_get_uint8(v_options_4005_, sizeof(void*)*1);
if (v_hasTrace_4006_ == 0)
{
v___y_3903_ = v___y_3949_;
v___y_3904_ = v___y_3952_;
v___y_3905_ = v___y_3951_;
v___y_3906_ = v___y_3953_;
v___y_3907_ = v___y_3954_;
goto v___jp_3902_;
}
else
{
lean_object* v_inheritedTraceOptions_4007_; lean_object* v___x_4008_; uint8_t v___x_4009_; 
v_inheritedTraceOptions_4007_ = lean_ctor_get(v_toCold_4004_, 11);
v___x_4008_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4009_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4007_, v_options_4005_, v___x_4008_);
if (v___x_4009_ == 0)
{
v___y_3903_ = v___y_3949_;
v___y_3904_ = v___y_3952_;
v___y_3905_ = v___y_3951_;
v___y_3906_ = v___y_3953_;
v___y_3907_ = v___y_3954_;
goto v___jp_3902_;
}
else
{
lean_object* v___x_4010_; lean_object* v___x_4011_; 
v___x_4010_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_4011_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3916_, v___x_4010_, v___y_3953_, v___y_3954_);
if (lean_obj_tag(v___x_4011_) == 0)
{
lean_dec_ref_known(v___x_4011_, 1);
v___y_3903_ = v___y_3949_;
v___y_3904_ = v___y_3952_;
v___y_3905_ = v___y_3951_;
v___y_3906_ = v___y_3953_;
v___y_3907_ = v___y_3954_;
goto v___jp_3902_;
}
else
{
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3949_);
lean_dec(v_decl_3739_);
return v___x_4011_;
}
}
}
}
}
}
v___jp_4012_:
{
lean_object* v___x_4019_; lean_object* v_env_4020_; uint8_t v___x_4021_; 
v___x_4019_ = lean_st_ref_get(v___y_4018_);
v_env_4020_ = lean_ctor_get(v___x_4019_, 0);
lean_inc_ref(v_env_4020_);
lean_dec(v___x_4019_);
v___x_4021_ = l_Lean_Environment_containsOnBranch(v_env_4020_, v_fst_4013_);
lean_dec_ref(v_env_4020_);
if (v___x_4021_ == 0)
{
v___y_3949_ = v_fst_4014_;
v___y_3950_ = v_exportedInfo_x3f_4016_;
v___y_3951_ = v_fst_4013_;
v___y_3952_ = v_snd_4015_;
v___y_3953_ = v___y_4017_;
v___y_3954_ = v___y_4018_;
goto v___jp_3948_;
}
else
{
lean_object* v___x_4022_; lean_object* v_env_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
lean_dec(v_exportedInfo_x3f_4016_);
lean_dec_ref(v_fst_4014_);
lean_dec(v_decl_3739_);
v___x_4022_ = lean_st_ref_get(v___y_4018_);
v_env_4023_ = lean_ctor_get(v___x_4022_, 0);
lean_inc_ref(v_env_4023_);
lean_dec(v___x_4022_);
v___x_4024_ = lean_elab_environment_to_kernel_env(v_env_4023_);
v___x_4025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4025_, 0, v___x_4024_);
lean_ctor_set(v___x_4025_, 1, v_fst_4013_);
v___x_4026_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4025_, v___y_4017_, v___y_4018_);
return v___x_4026_;
}
}
v___jp_4027_:
{
lean_object* v_toConstantVal_4032_; lean_object* v_name_4033_; lean_object* v___x_4034_; uint8_t v___x_4035_; 
v_toConstantVal_4032_ = lean_ctor_get(v___y_4028_, 0);
v_name_4033_ = lean_ctor_get(v_toConstantVal_4032_, 0);
lean_inc(v_name_4033_);
v___x_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4034_, 0, v___y_4028_);
v___x_4035_ = 0;
v_fst_4013_ = v_name_4033_;
v_fst_4014_ = v___x_4034_;
v_snd_4015_ = v___x_4035_;
v_exportedInfo_x3f_4016_ = v_exportedInfo_x3f_4029_;
v___y_4017_ = v___y_4030_;
v___y_4018_ = v___y_4031_;
goto v___jp_4012_;
}
v___jp_4036_:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4042_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4042_, 0, v___y_4040_);
lean_ctor_set_uint8(v___x_4042_, sizeof(void*)*1, v___y_4041_);
v___x_4043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4042_);
v___x_4044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4043_);
v___y_4028_ = v___y_4038_;
v_exportedInfo_x3f_4029_ = v___x_4044_;
v___y_4030_ = v___y_4037_;
v___y_4031_ = v___y_4039_;
goto v___jp_4027_;
}
v___jp_4045_:
{
uint8_t v___x_4052_; uint8_t v___x_4053_; 
v___x_4052_ = 1;
v___x_4053_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4049_, v___x_4052_);
if (v___x_4053_ == 0)
{
v___y_4037_ = v___y_4050_;
v___y_4038_ = v___y_4047_;
v___y_4039_ = v___y_4051_;
v___y_4040_ = v_toConstantVal_4048_;
v___y_4041_ = v___y_4046_;
goto v___jp_4036_;
}
else
{
v___y_4037_ = v___y_4050_;
v___y_4038_ = v___y_4047_;
v___y_4039_ = v___y_4051_;
v___y_4040_ = v_toConstantVal_4048_;
v___y_4041_ = v_hasTrace_3773_;
goto v___jp_4036_;
}
}
v___jp_4054_:
{
lean_object* v_toConstantVal_4059_; uint8_t v_safety_4060_; 
v_toConstantVal_4059_ = lean_ctor_get(v___y_4056_, 0);
lean_inc_ref(v_toConstantVal_4059_);
v_safety_4060_ = lean_ctor_get_uint8(v___y_4056_, sizeof(void*)*4);
v___y_4046_ = v___y_4055_;
v___y_4047_ = v___y_4056_;
v_toConstantVal_4048_ = v_toConstantVal_4059_;
v_safety_4049_ = v_safety_4060_;
v___y_4050_ = v___y_4057_;
v___y_4051_ = v___y_4058_;
goto v___jp_4045_;
}
v___jp_4061_:
{
lean_object* v___x_4065_; lean_object* v_env_4066_; lean_object* v___x_4067_; 
v___x_4065_ = lean_st_ref_get(v___y_4064_);
v_env_4066_ = lean_ctor_get(v___x_4065_, 0);
lean_inc_ref(v_env_4066_);
lean_dec(v___x_4065_);
v___x_4067_ = lean_st_ref_get(v___y_4064_);
if (v_forceExpose_3740_ == 0)
{
lean_object* v_env_4068_; lean_object* v___x_4069_; uint8_t v_isModule_4070_; 
v_env_4068_ = lean_ctor_get(v___x_4067_, 0);
lean_inc_ref(v_env_4068_);
lean_dec(v___x_4067_);
v___x_4069_ = l_Lean_Environment_header(v_env_4066_);
lean_dec_ref(v_env_4066_);
v_isModule_4070_ = lean_ctor_get_uint8(v___x_4069_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4069_);
if (v_isModule_4070_ == 0)
{
lean_dec_ref(v_env_4068_);
v___y_4028_ = v_defn_4062_;
v_exportedInfo_x3f_4029_ = v___x_3947_;
v___y_4030_ = v___y_4063_;
v___y_4031_ = v___y_4064_;
goto v___jp_4027_;
}
else
{
uint8_t v_isExporting_4071_; 
v_isExporting_4071_ = lean_ctor_get_uint8(v_env_4068_, sizeof(void*)*13);
lean_dec_ref(v_env_4068_);
if (v_isExporting_4071_ == 0)
{
lean_object* v_toCold_4072_; lean_object* v_options_4073_; uint8_t v_hasTrace_4074_; 
v_toCold_4072_ = lean_ctor_get(v___y_4063_, 0);
v_options_4073_ = lean_ctor_get(v_toCold_4072_, 2);
v_hasTrace_4074_ = lean_ctor_get_uint8(v_options_4073_, sizeof(void*)*1);
if (v_hasTrace_4074_ == 0)
{
v___y_4055_ = v_isModule_4070_;
v___y_4056_ = v_defn_4062_;
v___y_4057_ = v___y_4063_;
v___y_4058_ = v___y_4064_;
goto v___jp_4054_;
}
else
{
lean_object* v_inheritedTraceOptions_4075_; lean_object* v___x_4076_; uint8_t v___x_4077_; 
v_inheritedTraceOptions_4075_ = lean_ctor_get(v_toCold_4072_, 11);
v___x_4076_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4077_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4075_, v_options_4073_, v___x_4076_);
if (v___x_4077_ == 0)
{
v___y_4055_ = v_isModule_4070_;
v___y_4056_ = v_defn_4062_;
v___y_4057_ = v___y_4063_;
v___y_4058_ = v___y_4064_;
goto v___jp_4054_;
}
else
{
lean_object* v_toConstantVal_4078_; uint8_t v_safety_4079_; lean_object* v_name_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
v_toConstantVal_4078_ = lean_ctor_get(v_defn_4062_, 0);
lean_inc_ref(v_toConstantVal_4078_);
v_safety_4079_ = lean_ctor_get_uint8(v_defn_4062_, sizeof(void*)*4);
v_name_4080_ = lean_ctor_get(v_toConstantVal_4078_, 0);
v___x_4081_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_4080_);
v___x_4082_ = l_Lean_MessageData_ofName(v_name_4080_);
v___x_4083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4083_, 0, v___x_4081_);
lean_ctor_set(v___x_4083_, 1, v___x_4082_);
v___x_4084_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4083_);
lean_ctor_set(v___x_4085_, 1, v___x_4084_);
v___x_4086_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3916_, v___x_4085_, v___y_4063_, v___y_4064_);
if (lean_obj_tag(v___x_4086_) == 0)
{
lean_dec_ref_known(v___x_4086_, 1);
v___y_4046_ = v_isModule_4070_;
v___y_4047_ = v_defn_4062_;
v_toConstantVal_4048_ = v_toConstantVal_4078_;
v_safety_4049_ = v_safety_4079_;
v___y_4050_ = v___y_4063_;
v___y_4051_ = v___y_4064_;
goto v___jp_4045_;
}
else
{
lean_dec_ref(v_toConstantVal_4078_);
lean_dec_ref(v_defn_4062_);
lean_dec(v_decl_3739_);
return v___x_4086_;
}
}
}
}
else
{
v___y_4028_ = v_defn_4062_;
v_exportedInfo_x3f_4029_ = v___x_3947_;
v___y_4030_ = v___y_4063_;
v___y_4031_ = v___y_4064_;
goto v___jp_4027_;
}
}
}
else
{
lean_dec(v___x_4067_);
lean_dec_ref(v_env_4066_);
v___y_4028_ = v_defn_4062_;
v_exportedInfo_x3f_4029_ = v___x_3947_;
v___y_4030_ = v___y_4063_;
v___y_4031_ = v___y_4064_;
goto v___jp_4027_;
}
}
}
}
}
else
{
lean_object* v___f_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; uint8_t v___x_4143_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v_a_4147_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v_a_4162_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v_a_4194_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v_a_4206_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4211_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; 
lean_inc(v_decl_3739_);
v___f_4140_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed), 5, 1);
lean_closure_set(v___f_4140_, 0, v_decl_3739_);
v___x_4141_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_4142_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4143_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3772_, v_options_3771_, v___x_4142_);
if (v___x_4143_ == 0)
{
lean_object* v___x_4419_; uint8_t v___x_4420_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v___y_4428_; lean_object* v___y_4429_; lean_object* v___y_4430_; lean_object* v___y_4431_; lean_object* v___y_4432_; lean_object* v___y_4504_; uint8_t v___y_4505_; lean_object* v___y_4506_; lean_object* v___y_4507_; lean_object* v___y_4508_; lean_object* v___y_4509_; lean_object* v___y_4510_; lean_object* v___y_4511_; lean_object* v___y_4533_; uint8_t v___y_4534_; lean_object* v___y_4535_; lean_object* v_exportedInfo_x3f_4536_; lean_object* v___y_4537_; lean_object* v___y_4538_; uint8_t v___y_4548_; lean_object* v___y_4549_; lean_object* v___y_4550_; lean_object* v___y_4551_; lean_object* v___y_4552_; uint8_t v___y_4555_; lean_object* v___y_4556_; lean_object* v___y_4557_; lean_object* v___y_4558_; lean_object* v___y_4559_; 
v___x_4419_ = l_Lean_trace_profiler;
v___x_4420_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3771_, v___x_4419_);
if (v___x_4420_ == 0)
{
lean_object* v___x_4561_; lean_object* v_env_4562_; lean_object* v_nextMacroScope_4563_; lean_object* v_ngen_4564_; lean_object* v_auxDeclNGen_4565_; lean_object* v_traceState_4566_; lean_object* v_recordedDeps_4567_; lean_object* v_messages_4568_; lean_object* v_infoState_4569_; lean_object* v_snapshotTasks_4570_; lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4786_; 
lean_dec_ref(v___f_4140_);
v___x_4561_ = lean_st_ref_take(v_a_3742_);
v_env_4562_ = lean_ctor_get(v___x_4561_, 0);
v_nextMacroScope_4563_ = lean_ctor_get(v___x_4561_, 1);
v_ngen_4564_ = lean_ctor_get(v___x_4561_, 2);
v_auxDeclNGen_4565_ = lean_ctor_get(v___x_4561_, 3);
v_traceState_4566_ = lean_ctor_get(v___x_4561_, 4);
v_recordedDeps_4567_ = lean_ctor_get(v___x_4561_, 6);
v_messages_4568_ = lean_ctor_get(v___x_4561_, 7);
v_infoState_4569_ = lean_ctor_get(v___x_4561_, 8);
v_snapshotTasks_4570_ = lean_ctor_get(v___x_4561_, 9);
v_isSharedCheck_4786_ = !lean_is_exclusive(v___x_4561_);
if (v_isSharedCheck_4786_ == 0)
{
lean_object* v_unused_4787_; 
v_unused_4787_ = lean_ctor_get(v___x_4561_, 5);
lean_dec(v_unused_4787_);
v___x_4572_ = v___x_4561_;
v_isShared_4573_ = v_isSharedCheck_4786_;
goto v_resetjp_4571_;
}
else
{
lean_inc(v_snapshotTasks_4570_);
lean_inc(v_infoState_4569_);
lean_inc(v_messages_4568_);
lean_inc(v_recordedDeps_4567_);
lean_inc(v_traceState_4566_);
lean_inc(v_auxDeclNGen_4565_);
lean_inc(v_ngen_4564_);
lean_inc(v_nextMacroScope_4563_);
lean_inc(v_env_4562_);
lean_dec(v___x_4561_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4786_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4578_; 
lean_inc(v_decl_3739_);
v___x_4574_ = l_Lean_Declaration_getNames(v_decl_3739_);
v___x_4575_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4562_, v___x_4574_);
v___x_4576_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4573_ == 0)
{
lean_ctor_set(v___x_4572_, 5, v___x_4576_);
lean_ctor_set(v___x_4572_, 0, v___x_4575_);
v___x_4578_ = v___x_4572_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4785_; 
v_reuseFailAlloc_4785_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4785_, 0, v___x_4575_);
lean_ctor_set(v_reuseFailAlloc_4785_, 1, v_nextMacroScope_4563_);
lean_ctor_set(v_reuseFailAlloc_4785_, 2, v_ngen_4564_);
lean_ctor_set(v_reuseFailAlloc_4785_, 3, v_auxDeclNGen_4565_);
lean_ctor_set(v_reuseFailAlloc_4785_, 4, v_traceState_4566_);
lean_ctor_set(v_reuseFailAlloc_4785_, 5, v___x_4576_);
lean_ctor_set(v_reuseFailAlloc_4785_, 6, v_recordedDeps_4567_);
lean_ctor_set(v_reuseFailAlloc_4785_, 7, v_messages_4568_);
lean_ctor_set(v_reuseFailAlloc_4785_, 8, v_infoState_4569_);
lean_ctor_set(v_reuseFailAlloc_4785_, 9, v_snapshotTasks_4570_);
v___x_4578_ = v_reuseFailAlloc_4785_;
goto v_reusejp_4577_;
}
v_reusejp_4577_:
{
lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___y_4582_; uint8_t v___y_4583_; lean_object* v___y_4584_; lean_object* v___y_4585_; lean_object* v___y_4586_; lean_object* v___y_4587_; lean_object* v_fst_4643_; lean_object* v_fst_4644_; uint8_t v_snd_4645_; lean_object* v_exportedInfo_x3f_4646_; lean_object* v___y_4647_; lean_object* v___y_4648_; lean_object* v___y_4658_; lean_object* v_exportedInfo_x3f_4659_; lean_object* v___y_4660_; lean_object* v___y_4661_; lean_object* v___y_4667_; lean_object* v___y_4668_; lean_object* v___y_4669_; lean_object* v___y_4670_; uint8_t v___y_4671_; uint8_t v___y_4676_; lean_object* v___y_4677_; lean_object* v_toConstantVal_4678_; uint8_t v_safety_4679_; lean_object* v___y_4680_; lean_object* v___y_4681_; uint8_t v___y_4685_; lean_object* v___y_4686_; lean_object* v___y_4687_; lean_object* v___y_4688_; lean_object* v_defn_4692_; lean_object* v___y_4693_; lean_object* v___y_4694_; 
v___x_4579_ = lean_st_ref_put(v_a_3742_, v___x_4578_);
v___x_4580_ = lean_box(0);
switch(lean_obj_tag(v_decl_3739_))
{
case 2:
{
lean_object* v_val_4716_; lean_object* v_exportedInfo_x3f_4718_; lean_object* v___y_4719_; lean_object* v___y_4720_; lean_object* v___y_4726_; lean_object* v___y_4727_; lean_object* v___x_4732_; 
v_val_4716_ = lean_ctor_get(v_decl_3739_, 0);
v___x_4732_ = lean_st_ref_get(v_a_3742_);
if (v_forceExpose_3740_ == 0)
{
lean_object* v_env_4733_; lean_object* v___x_4734_; uint8_t v_isModule_4735_; 
v_env_4733_ = lean_ctor_get(v___x_4732_, 0);
lean_inc_ref(v_env_4733_);
lean_dec(v___x_4732_);
v___x_4734_ = l_Lean_Environment_header(v_env_4733_);
lean_dec_ref(v_env_4733_);
v_isModule_4735_ = lean_ctor_get_uint8(v___x_4734_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4734_);
if (v_isModule_4735_ == 0)
{
v_exportedInfo_x3f_4718_ = v___x_4580_;
v___y_4719_ = v_a_3741_;
v___y_4720_ = v_a_3742_;
goto v___jp_4717_;
}
else
{
if (v___x_4143_ == 0)
{
v___y_4726_ = v_a_3741_;
v___y_4727_ = v_a_3742_;
goto v___jp_4725_;
}
else
{
lean_object* v_toConstantVal_4736_; lean_object* v_name_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; 
v_toConstantVal_4736_ = lean_ctor_get(v_val_4716_, 0);
v_name_4737_ = lean_ctor_get(v_toConstantVal_4736_, 0);
v___x_4738_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4737_);
v___x_4739_ = l_Lean_MessageData_ofName(v_name_4737_);
v___x_4740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4740_, 0, v___x_4738_);
lean_ctor_set(v___x_4740_, 1, v___x_4739_);
v___x_4741_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4742_, 0, v___x_4740_);
lean_ctor_set(v___x_4742_, 1, v___x_4741_);
v___x_4743_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3916_, v___x_4742_, v_a_3741_, v_a_3742_);
if (lean_obj_tag(v___x_4743_) == 0)
{
lean_dec_ref_known(v___x_4743_, 1);
v___y_4726_ = v_a_3741_;
v___y_4727_ = v_a_3742_;
goto v___jp_4725_;
}
else
{
lean_dec_ref_known(v_decl_3739_, 1);
return v___x_4743_;
}
}
}
}
else
{
lean_dec(v___x_4732_);
v_exportedInfo_x3f_4718_ = v___x_4580_;
v___y_4719_ = v_a_3741_;
v___y_4720_ = v_a_3742_;
goto v___jp_4717_;
}
v___jp_4717_:
{
lean_object* v_toConstantVal_4721_; lean_object* v_name_4722_; lean_object* v___x_4723_; uint8_t v___x_4724_; 
v_toConstantVal_4721_ = lean_ctor_get(v_val_4716_, 0);
v_name_4722_ = lean_ctor_get(v_toConstantVal_4721_, 0);
lean_inc_ref(v_val_4716_);
v___x_4723_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4723_, 0, v_val_4716_);
v___x_4724_ = 1;
lean_inc(v_name_4722_);
v_fst_4643_ = v_name_4722_;
v_fst_4644_ = v___x_4723_;
v_snd_4645_ = v___x_4724_;
v_exportedInfo_x3f_4646_ = v_exportedInfo_x3f_4718_;
v___y_4647_ = v___y_4719_;
v___y_4648_ = v___y_4720_;
goto v___jp_4642_;
}
v___jp_4725_:
{
lean_object* v_toConstantVal_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; 
v_toConstantVal_4728_ = lean_ctor_get(v_val_4716_, 0);
lean_inc_ref(v_toConstantVal_4728_);
v___x_4729_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4729_, 0, v_toConstantVal_4728_);
lean_ctor_set_uint8(v___x_4729_, sizeof(void*)*1, v___x_4420_);
v___x_4730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4730_, 0, v___x_4729_);
v___x_4731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4731_, 0, v___x_4730_);
v_exportedInfo_x3f_4718_ = v___x_4731_;
v___y_4719_ = v___y_4726_;
v___y_4720_ = v___y_4727_;
goto v___jp_4717_;
}
}
case 1:
{
lean_object* v_val_4744_; 
v_val_4744_ = lean_ctor_get(v_decl_3739_, 0);
lean_inc_ref(v_val_4744_);
v_defn_4692_ = v_val_4744_;
v___y_4693_ = v_a_3741_;
v___y_4694_ = v_a_3742_;
goto v___jp_4691_;
}
case 5:
{
lean_object* v_defns_4745_; 
v_defns_4745_ = lean_ctor_get(v_decl_3739_, 0);
if (lean_obj_tag(v_defns_4745_) == 1)
{
lean_object* v_tail_4746_; 
v_tail_4746_ = lean_ctor_get(v_defns_4745_, 1);
if (lean_obj_tag(v_tail_4746_) == 0)
{
lean_object* v_head_4747_; 
v_head_4747_ = lean_ctor_get(v_defns_4745_, 0);
lean_inc(v_head_4747_);
v_defn_4692_ = v_head_4747_;
v___y_4693_ = v_a_3741_;
v___y_4694_ = v_a_3742_;
goto v___jp_4691_;
}
else
{
v___y_3918_ = v_a_3741_;
v_options_3919_ = v_options_3771_;
v_inheritedTraceOptions_3920_ = v_inheritedTraceOptions_3772_;
v___y_3921_ = v_a_3742_;
goto v___jp_3917_;
}
}
else
{
v___y_3918_ = v_a_3741_;
v_options_3919_ = v_options_3771_;
v_inheritedTraceOptions_3920_ = v_inheritedTraceOptions_3772_;
v___y_3921_ = v_a_3742_;
goto v___jp_3917_;
}
}
case 3:
{
lean_object* v_val_4748_; lean_object* v_exportedInfo_x3f_4750_; lean_object* v___y_4751_; lean_object* v___y_4752_; lean_object* v___y_4758_; lean_object* v___y_4759_; lean_object* v___x_4765_; lean_object* v_env_4766_; lean_object* v___x_4767_; 
v_val_4748_ = lean_ctor_get(v_decl_3739_, 0);
v___x_4765_ = lean_st_ref_get(v_a_3742_);
v_env_4766_ = lean_ctor_get(v___x_4765_, 0);
lean_inc_ref(v_env_4766_);
lean_dec(v___x_4765_);
v___x_4767_ = lean_st_ref_get(v_a_3742_);
if (v_forceExpose_3740_ == 0)
{
lean_object* v_env_4768_; lean_object* v___x_4769_; uint8_t v_isModule_4770_; 
v_env_4768_ = lean_ctor_get(v___x_4767_, 0);
lean_inc_ref(v_env_4768_);
lean_dec(v___x_4767_);
v___x_4769_ = l_Lean_Environment_header(v_env_4766_);
lean_dec_ref(v_env_4766_);
v_isModule_4770_ = lean_ctor_get_uint8(v___x_4769_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4769_);
if (v_isModule_4770_ == 0)
{
lean_dec_ref(v_env_4768_);
v_exportedInfo_x3f_4750_ = v___x_4580_;
v___y_4751_ = v_a_3741_;
v___y_4752_ = v_a_3742_;
goto v___jp_4749_;
}
else
{
uint8_t v_isExporting_4771_; 
v_isExporting_4771_ = lean_ctor_get_uint8(v_env_4768_, sizeof(void*)*13);
lean_dec_ref(v_env_4768_);
if (v_isExporting_4771_ == 0)
{
if (v___x_4143_ == 0)
{
v___y_4758_ = v_a_3741_;
v___y_4759_ = v_a_3742_;
goto v___jp_4757_;
}
else
{
lean_object* v_toConstantVal_4772_; lean_object* v_name_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; 
v_toConstantVal_4772_ = lean_ctor_get(v_val_4748_, 0);
v_name_4773_ = lean_ctor_get(v_toConstantVal_4772_, 0);
v___x_4774_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4773_);
v___x_4775_ = l_Lean_MessageData_ofName(v_name_4773_);
v___x_4776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4776_, 0, v___x_4774_);
lean_ctor_set(v___x_4776_, 1, v___x_4775_);
v___x_4777_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4778_, 0, v___x_4776_);
lean_ctor_set(v___x_4778_, 1, v___x_4777_);
v___x_4779_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3916_, v___x_4778_, v_a_3741_, v_a_3742_);
if (lean_obj_tag(v___x_4779_) == 0)
{
lean_dec_ref_known(v___x_4779_, 1);
v___y_4758_ = v_a_3741_;
v___y_4759_ = v_a_3742_;
goto v___jp_4757_;
}
else
{
lean_dec_ref_known(v_decl_3739_, 1);
return v___x_4779_;
}
}
}
else
{
v_exportedInfo_x3f_4750_ = v___x_4580_;
v___y_4751_ = v_a_3741_;
v___y_4752_ = v_a_3742_;
goto v___jp_4749_;
}
}
}
else
{
lean_dec(v___x_4767_);
lean_dec_ref(v_env_4766_);
v_exportedInfo_x3f_4750_ = v___x_4580_;
v___y_4751_ = v_a_3741_;
v___y_4752_ = v_a_3742_;
goto v___jp_4749_;
}
v___jp_4749_:
{
lean_object* v_toConstantVal_4753_; lean_object* v_name_4754_; lean_object* v___x_4755_; uint8_t v___x_4756_; 
v_toConstantVal_4753_ = lean_ctor_get(v_val_4748_, 0);
v_name_4754_ = lean_ctor_get(v_toConstantVal_4753_, 0);
lean_inc_ref(v_val_4748_);
v___x_4755_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4755_, 0, v_val_4748_);
v___x_4756_ = 3;
lean_inc(v_name_4754_);
v_fst_4643_ = v_name_4754_;
v_fst_4644_ = v___x_4755_;
v_snd_4645_ = v___x_4756_;
v_exportedInfo_x3f_4646_ = v_exportedInfo_x3f_4750_;
v___y_4647_ = v___y_4751_;
v___y_4648_ = v___y_4752_;
goto v___jp_4642_;
}
v___jp_4757_:
{
lean_object* v_toConstantVal_4760_; uint8_t v_isUnsafe_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; 
v_toConstantVal_4760_ = lean_ctor_get(v_val_4748_, 0);
v_isUnsafe_4761_ = lean_ctor_get_uint8(v_val_4748_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4760_);
v___x_4762_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4762_, 0, v_toConstantVal_4760_);
lean_ctor_set_uint8(v___x_4762_, sizeof(void*)*1, v_isUnsafe_4761_);
v___x_4763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4763_, 0, v___x_4762_);
v___x_4764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4764_, 0, v___x_4763_);
v_exportedInfo_x3f_4750_ = v___x_4764_;
v___y_4751_ = v___y_4758_;
v___y_4752_ = v___y_4759_;
goto v___jp_4749_;
}
}
case 0:
{
lean_object* v_val_4780_; lean_object* v_toConstantVal_4781_; lean_object* v_name_4782_; lean_object* v___x_4783_; uint8_t v___x_4784_; 
v_val_4780_ = lean_ctor_get(v_decl_3739_, 0);
v_toConstantVal_4781_ = lean_ctor_get(v_val_4780_, 0);
v_name_4782_ = lean_ctor_get(v_toConstantVal_4781_, 0);
lean_inc_ref(v_val_4780_);
v___x_4783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4783_, 0, v_val_4780_);
v___x_4784_ = 2;
lean_inc(v_name_4782_);
v_fst_4643_ = v_name_4782_;
v_fst_4644_ = v___x_4783_;
v_snd_4645_ = v___x_4784_;
v_exportedInfo_x3f_4646_ = v___x_4580_;
v___y_4647_ = v_a_3741_;
v___y_4648_ = v_a_3742_;
goto v___jp_4642_;
}
default: 
{
v___y_3918_ = v_a_3741_;
v_options_3919_ = v_options_3771_;
v_inheritedTraceOptions_3920_ = v_inheritedTraceOptions_3772_;
v___y_3921_ = v_a_3742_;
goto v___jp_3917_;
}
}
v___jp_4581_:
{
lean_object* v___x_4588_; uint8_t v___x_4589_; 
lean_inc(v_decl_3739_);
v___x_4588_ = l_Lean_Declaration_getTopLevelNames(v_decl_3739_);
v___x_4589_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_4588_);
lean_dec(v___x_4588_);
if (v___x_4589_ == 0)
{
if (lean_obj_tag(v___y_4585_) == 0)
{
lean_object* v_toCold_4590_; lean_object* v_options_4591_; uint8_t v_hasTrace_4592_; 
v_toCold_4590_ = lean_ctor_get(v___y_4586_, 0);
v_options_4591_ = lean_ctor_get(v_toCold_4590_, 2);
v_hasTrace_4592_ = lean_ctor_get_uint8(v_options_4591_, sizeof(void*)*1);
if (v_hasTrace_4592_ == 0)
{
v___y_4555_ = v___y_4583_;
v___y_4556_ = v___y_4582_;
v___y_4557_ = v___y_4584_;
v___y_4558_ = v___y_4586_;
v___y_4559_ = v___y_4587_;
goto v___jp_4554_;
}
else
{
lean_object* v_inheritedTraceOptions_4593_; uint8_t v___x_4594_; 
v_inheritedTraceOptions_4593_ = lean_ctor_get(v_toCold_4590_, 11);
v___x_4594_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4593_, v_options_4591_, v___x_4142_);
if (v___x_4594_ == 0)
{
v___y_4555_ = v___y_4583_;
v___y_4556_ = v___y_4582_;
v___y_4557_ = v___y_4584_;
v___y_4558_ = v___y_4586_;
v___y_4559_ = v___y_4587_;
goto v___jp_4554_;
}
else
{
lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4595_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_4596_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3916_, v___x_4595_, v___y_4586_, v___y_4587_);
if (lean_obj_tag(v___x_4596_) == 0)
{
lean_dec_ref_known(v___x_4596_, 1);
v___y_4555_ = v___y_4583_;
v___y_4556_ = v___y_4582_;
v___y_4557_ = v___y_4584_;
v___y_4558_ = v___y_4586_;
v___y_4559_ = v___y_4587_;
goto v___jp_4554_;
}
else
{
lean_dec_ref(v___y_4584_);
lean_dec(v___y_4582_);
lean_dec(v_decl_3739_);
return v___x_4596_;
}
}
}
}
else
{
lean_object* v___x_4597_; lean_object* v_env_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; uint8_t v___x_4601_; lean_object* v___x_4602_; 
v___x_4597_ = lean_st_ref_get(v___y_4587_);
v_env_4598_ = lean_ctor_get(v___x_4597_, 0);
lean_inc_ref(v_env_4598_);
lean_dec(v___x_4597_);
v___x_4599_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4600_ = lean_box(1);
v___x_4601_ = 0;
lean_inc(v___y_4582_);
v___x_4602_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_4599_, v_env_4598_, v___y_4582_, v___x_4600_, v___x_4601_);
if (lean_obj_tag(v___x_4602_) == 0)
{
lean_object* v___x_4603_; lean_object* v_env_4604_; lean_object* v_nextMacroScope_4605_; lean_object* v_ngen_4606_; lean_object* v_auxDeclNGen_4607_; lean_object* v_traceState_4608_; lean_object* v_recordedDeps_4609_; lean_object* v_messages_4610_; lean_object* v_infoState_4611_; lean_object* v_snapshotTasks_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4622_; 
v___x_4603_ = lean_st_ref_take(v___y_4587_);
v_env_4604_ = lean_ctor_get(v___x_4603_, 0);
v_nextMacroScope_4605_ = lean_ctor_get(v___x_4603_, 1);
v_ngen_4606_ = lean_ctor_get(v___x_4603_, 2);
v_auxDeclNGen_4607_ = lean_ctor_get(v___x_4603_, 3);
v_traceState_4608_ = lean_ctor_get(v___x_4603_, 4);
v_recordedDeps_4609_ = lean_ctor_get(v___x_4603_, 6);
v_messages_4610_ = lean_ctor_get(v___x_4603_, 7);
v_infoState_4611_ = lean_ctor_get(v___x_4603_, 8);
v_snapshotTasks_4612_ = lean_ctor_get(v___x_4603_, 9);
v_isSharedCheck_4622_ = !lean_is_exclusive(v___x_4603_);
if (v_isSharedCheck_4622_ == 0)
{
lean_object* v_unused_4623_; 
v_unused_4623_ = lean_ctor_get(v___x_4603_, 5);
lean_dec(v_unused_4623_);
v___x_4614_ = v___x_4603_;
v_isShared_4615_ = v_isSharedCheck_4622_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_snapshotTasks_4612_);
lean_inc(v_infoState_4611_);
lean_inc(v_messages_4610_);
lean_inc(v_recordedDeps_4609_);
lean_inc(v_traceState_4608_);
lean_inc(v_auxDeclNGen_4607_);
lean_inc(v_ngen_4606_);
lean_inc(v_nextMacroScope_4605_);
lean_inc(v_env_4604_);
lean_dec(v___x_4603_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4622_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4619_; 
v___x_4616_ = lean_box(v___y_4583_);
lean_inc(v___y_4582_);
v___x_4617_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4599_, v_env_4604_, v___y_4582_, v___x_4616_, v___x_4589_);
if (v_isShared_4615_ == 0)
{
lean_ctor_set(v___x_4614_, 5, v___x_4576_);
lean_ctor_set(v___x_4614_, 0, v___x_4617_);
v___x_4619_ = v___x_4614_;
goto v_reusejp_4618_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v___x_4617_);
lean_ctor_set(v_reuseFailAlloc_4621_, 1, v_nextMacroScope_4605_);
lean_ctor_set(v_reuseFailAlloc_4621_, 2, v_ngen_4606_);
lean_ctor_set(v_reuseFailAlloc_4621_, 3, v_auxDeclNGen_4607_);
lean_ctor_set(v_reuseFailAlloc_4621_, 4, v_traceState_4608_);
lean_ctor_set(v_reuseFailAlloc_4621_, 5, v___x_4576_);
lean_ctor_set(v_reuseFailAlloc_4621_, 6, v_recordedDeps_4609_);
lean_ctor_set(v_reuseFailAlloc_4621_, 7, v_messages_4610_);
lean_ctor_set(v_reuseFailAlloc_4621_, 8, v_infoState_4611_);
lean_ctor_set(v_reuseFailAlloc_4621_, 9, v_snapshotTasks_4612_);
v___x_4619_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4618_;
}
v_reusejp_4618_:
{
lean_object* v___x_4620_; 
v___x_4620_ = lean_st_ref_put(v___y_4587_, v___x_4619_);
v___y_4533_ = v___y_4582_;
v___y_4534_ = v___y_4583_;
v___y_4535_ = v___y_4584_;
v_exportedInfo_x3f_4536_ = v___y_4585_;
v___y_4537_ = v___y_4586_;
v___y_4538_ = v___y_4587_;
goto v___jp_4532_;
}
}
}
else
{
lean_dec_ref_known(v___x_4602_, 1);
v___y_4533_ = v___y_4582_;
v___y_4534_ = v___y_4583_;
v___y_4535_ = v___y_4584_;
v_exportedInfo_x3f_4536_ = v___y_4585_;
v___y_4537_ = v___y_4586_;
v___y_4538_ = v___y_4587_;
goto v___jp_4532_;
}
}
}
else
{
lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v_a_4626_; uint8_t v___x_4627_; 
lean_dec(v___y_4585_);
v___x_4624_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4625_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4624_, v___y_4586_);
v_a_4626_ = lean_ctor_get(v___x_4625_, 0);
lean_inc(v_a_4626_);
lean_dec_ref(v___x_4625_);
v___x_4627_ = lean_unbox(v_a_4626_);
lean_dec(v_a_4626_);
if (v___x_4627_ == 0)
{
lean_object* v_toCold_4628_; lean_object* v_options_4629_; uint8_t v_hasTrace_4630_; 
v_toCold_4628_ = lean_ctor_get(v___y_4586_, 0);
v_options_4629_ = lean_ctor_get(v_toCold_4628_, 2);
v_hasTrace_4630_ = lean_ctor_get_uint8(v_options_4629_, sizeof(void*)*1);
if (v_hasTrace_4630_ == 0)
{
v___y_4533_ = v___y_4582_;
v___y_4534_ = v___y_4583_;
v___y_4535_ = v___y_4584_;
v_exportedInfo_x3f_4536_ = v___x_4580_;
v___y_4537_ = v___y_4586_;
v___y_4538_ = v___y_4587_;
goto v___jp_4532_;
}
else
{
lean_object* v_inheritedTraceOptions_4631_; uint8_t v___x_4632_; 
v_inheritedTraceOptions_4631_ = lean_ctor_get(v_toCold_4628_, 11);
v___x_4632_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4631_, v_options_4629_, v___x_4142_);
if (v___x_4632_ == 0)
{
v___y_4533_ = v___y_4582_;
v___y_4534_ = v___y_4583_;
v___y_4535_ = v___y_4584_;
v_exportedInfo_x3f_4536_ = v___x_4580_;
v___y_4537_ = v___y_4586_;
v___y_4538_ = v___y_4587_;
goto v___jp_4532_;
}
else
{
lean_object* v___x_4633_; lean_object* v___x_4634_; 
v___x_4633_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_4634_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3916_, v___x_4633_, v___y_4586_, v___y_4587_);
if (lean_obj_tag(v___x_4634_) == 0)
{
lean_dec_ref_known(v___x_4634_, 1);
v___y_4533_ = v___y_4582_;
v___y_4534_ = v___y_4583_;
v___y_4535_ = v___y_4584_;
v_exportedInfo_x3f_4536_ = v___x_4580_;
v___y_4537_ = v___y_4586_;
v___y_4538_ = v___y_4587_;
goto v___jp_4532_;
}
else
{
lean_dec_ref(v___y_4584_);
lean_dec(v___y_4582_);
lean_dec(v_decl_3739_);
return v___x_4634_;
}
}
}
}
else
{
lean_object* v_toCold_4635_; lean_object* v_options_4636_; uint8_t v_hasTrace_4637_; 
v_toCold_4635_ = lean_ctor_get(v___y_4586_, 0);
v_options_4636_ = lean_ctor_get(v_toCold_4635_, 2);
v_hasTrace_4637_ = lean_ctor_get_uint8(v_options_4636_, sizeof(void*)*1);
if (v_hasTrace_4637_ == 0)
{
v___y_4548_ = v___y_4583_;
v___y_4549_ = v___y_4582_;
v___y_4550_ = v___y_4584_;
v___y_4551_ = v___y_4586_;
v___y_4552_ = v___y_4587_;
goto v___jp_4547_;
}
else
{
lean_object* v_inheritedTraceOptions_4638_; uint8_t v___x_4639_; 
v_inheritedTraceOptions_4638_ = lean_ctor_get(v_toCold_4635_, 11);
v___x_4639_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4638_, v_options_4636_, v___x_4142_);
if (v___x_4639_ == 0)
{
v___y_4548_ = v___y_4583_;
v___y_4549_ = v___y_4582_;
v___y_4550_ = v___y_4584_;
v___y_4551_ = v___y_4586_;
v___y_4552_ = v___y_4587_;
goto v___jp_4547_;
}
else
{
lean_object* v___x_4640_; lean_object* v___x_4641_; 
v___x_4640_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_4641_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3916_, v___x_4640_, v___y_4586_, v___y_4587_);
if (lean_obj_tag(v___x_4641_) == 0)
{
lean_dec_ref_known(v___x_4641_, 1);
v___y_4548_ = v___y_4583_;
v___y_4549_ = v___y_4582_;
v___y_4550_ = v___y_4584_;
v___y_4551_ = v___y_4586_;
v___y_4552_ = v___y_4587_;
goto v___jp_4547_;
}
else
{
lean_dec_ref(v___y_4584_);
lean_dec(v___y_4582_);
lean_dec(v_decl_3739_);
return v___x_4641_;
}
}
}
}
}
}
v___jp_4642_:
{
lean_object* v___x_4649_; lean_object* v_env_4650_; uint8_t v___x_4651_; 
v___x_4649_ = lean_st_ref_get(v___y_4648_);
v_env_4650_ = lean_ctor_get(v___x_4649_, 0);
lean_inc_ref(v_env_4650_);
lean_dec(v___x_4649_);
v___x_4651_ = l_Lean_Environment_containsOnBranch(v_env_4650_, v_fst_4643_);
lean_dec_ref(v_env_4650_);
if (v___x_4651_ == 0)
{
v___y_4582_ = v_fst_4643_;
v___y_4583_ = v_snd_4645_;
v___y_4584_ = v_fst_4644_;
v___y_4585_ = v_exportedInfo_x3f_4646_;
v___y_4586_ = v___y_4647_;
v___y_4587_ = v___y_4648_;
goto v___jp_4581_;
}
else
{
lean_object* v___x_4652_; lean_object* v_env_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; 
lean_dec(v_exportedInfo_x3f_4646_);
lean_dec_ref(v_fst_4644_);
lean_dec(v_decl_3739_);
v___x_4652_ = lean_st_ref_get(v___y_4648_);
v_env_4653_ = lean_ctor_get(v___x_4652_, 0);
lean_inc_ref(v_env_4653_);
lean_dec(v___x_4652_);
v___x_4654_ = lean_elab_environment_to_kernel_env(v_env_4653_);
v___x_4655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4655_, 0, v___x_4654_);
lean_ctor_set(v___x_4655_, 1, v_fst_4643_);
v___x_4656_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4655_, v___y_4647_, v___y_4648_);
return v___x_4656_;
}
}
v___jp_4657_:
{
lean_object* v_toConstantVal_4662_; lean_object* v_name_4663_; lean_object* v___x_4664_; uint8_t v___x_4665_; 
v_toConstantVal_4662_ = lean_ctor_get(v___y_4658_, 0);
v_name_4663_ = lean_ctor_get(v_toConstantVal_4662_, 0);
lean_inc(v_name_4663_);
v___x_4664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4664_, 0, v___y_4658_);
v___x_4665_ = 0;
v_fst_4643_ = v_name_4663_;
v_fst_4644_ = v___x_4664_;
v_snd_4645_ = v___x_4665_;
v_exportedInfo_x3f_4646_ = v_exportedInfo_x3f_4659_;
v___y_4647_ = v___y_4660_;
v___y_4648_ = v___y_4661_;
goto v___jp_4642_;
}
v___jp_4666_:
{
lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; 
v___x_4672_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4672_, 0, v___y_4668_);
lean_ctor_set_uint8(v___x_4672_, sizeof(void*)*1, v___y_4671_);
v___x_4673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4673_, 0, v___x_4672_);
v___x_4674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4674_, 0, v___x_4673_);
v___y_4658_ = v___y_4669_;
v_exportedInfo_x3f_4659_ = v___x_4674_;
v___y_4660_ = v___y_4667_;
v___y_4661_ = v___y_4670_;
goto v___jp_4657_;
}
v___jp_4675_:
{
uint8_t v___x_4682_; uint8_t v___x_4683_; 
v___x_4682_ = 1;
v___x_4683_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4679_, v___x_4682_);
if (v___x_4683_ == 0)
{
v___y_4667_ = v___y_4680_;
v___y_4668_ = v_toConstantVal_4678_;
v___y_4669_ = v___y_4677_;
v___y_4670_ = v___y_4681_;
v___y_4671_ = v___y_4676_;
goto v___jp_4666_;
}
else
{
v___y_4667_ = v___y_4680_;
v___y_4668_ = v_toConstantVal_4678_;
v___y_4669_ = v___y_4677_;
v___y_4670_ = v___y_4681_;
v___y_4671_ = v___x_4420_;
goto v___jp_4666_;
}
}
v___jp_4684_:
{
lean_object* v_toConstantVal_4689_; uint8_t v_safety_4690_; 
v_toConstantVal_4689_ = lean_ctor_get(v___y_4686_, 0);
lean_inc_ref(v_toConstantVal_4689_);
v_safety_4690_ = lean_ctor_get_uint8(v___y_4686_, sizeof(void*)*4);
v___y_4676_ = v___y_4685_;
v___y_4677_ = v___y_4686_;
v_toConstantVal_4678_ = v_toConstantVal_4689_;
v_safety_4679_ = v_safety_4690_;
v___y_4680_ = v___y_4687_;
v___y_4681_ = v___y_4688_;
goto v___jp_4675_;
}
v___jp_4691_:
{
lean_object* v___x_4695_; lean_object* v_env_4696_; lean_object* v___x_4697_; 
v___x_4695_ = lean_st_ref_get(v___y_4694_);
v_env_4696_ = lean_ctor_get(v___x_4695_, 0);
lean_inc_ref(v_env_4696_);
lean_dec(v___x_4695_);
v___x_4697_ = lean_st_ref_get(v___y_4694_);
if (v_forceExpose_3740_ == 0)
{
lean_object* v_env_4698_; lean_object* v___x_4699_; uint8_t v_isModule_4700_; 
v_env_4698_ = lean_ctor_get(v___x_4697_, 0);
lean_inc_ref(v_env_4698_);
lean_dec(v___x_4697_);
v___x_4699_ = l_Lean_Environment_header(v_env_4696_);
lean_dec_ref(v_env_4696_);
v_isModule_4700_ = lean_ctor_get_uint8(v___x_4699_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4699_);
if (v_isModule_4700_ == 0)
{
lean_dec_ref(v_env_4698_);
v___y_4658_ = v_defn_4692_;
v_exportedInfo_x3f_4659_ = v___x_4580_;
v___y_4660_ = v___y_4693_;
v___y_4661_ = v___y_4694_;
goto v___jp_4657_;
}
else
{
uint8_t v_isExporting_4701_; 
v_isExporting_4701_ = lean_ctor_get_uint8(v_env_4698_, sizeof(void*)*13);
lean_dec_ref(v_env_4698_);
if (v_isExporting_4701_ == 0)
{
lean_object* v_toCold_4702_; lean_object* v_options_4703_; uint8_t v_hasTrace_4704_; 
v_toCold_4702_ = lean_ctor_get(v___y_4693_, 0);
v_options_4703_ = lean_ctor_get(v_toCold_4702_, 2);
v_hasTrace_4704_ = lean_ctor_get_uint8(v_options_4703_, sizeof(void*)*1);
if (v_hasTrace_4704_ == 0)
{
v___y_4685_ = v_isModule_4700_;
v___y_4686_ = v_defn_4692_;
v___y_4687_ = v___y_4693_;
v___y_4688_ = v___y_4694_;
goto v___jp_4684_;
}
else
{
lean_object* v_inheritedTraceOptions_4705_; uint8_t v___x_4706_; 
v_inheritedTraceOptions_4705_ = lean_ctor_get(v_toCold_4702_, 11);
v___x_4706_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4705_, v_options_4703_, v___x_4142_);
if (v___x_4706_ == 0)
{
v___y_4685_ = v_isModule_4700_;
v___y_4686_ = v_defn_4692_;
v___y_4687_ = v___y_4693_;
v___y_4688_ = v___y_4694_;
goto v___jp_4684_;
}
else
{
lean_object* v_toConstantVal_4707_; uint8_t v_safety_4708_; lean_object* v_name_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; 
v_toConstantVal_4707_ = lean_ctor_get(v_defn_4692_, 0);
lean_inc_ref(v_toConstantVal_4707_);
v_safety_4708_ = lean_ctor_get_uint8(v_defn_4692_, sizeof(void*)*4);
v_name_4709_ = lean_ctor_get(v_toConstantVal_4707_, 0);
v___x_4710_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_4709_);
v___x_4711_ = l_Lean_MessageData_ofName(v_name_4709_);
v___x_4712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4712_, 0, v___x_4710_);
lean_ctor_set(v___x_4712_, 1, v___x_4711_);
v___x_4713_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4714_, 0, v___x_4712_);
lean_ctor_set(v___x_4714_, 1, v___x_4713_);
v___x_4715_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3916_, v___x_4714_, v___y_4693_, v___y_4694_);
if (lean_obj_tag(v___x_4715_) == 0)
{
lean_dec_ref_known(v___x_4715_, 1);
v___y_4676_ = v_isModule_4700_;
v___y_4677_ = v_defn_4692_;
v_toConstantVal_4678_ = v_toConstantVal_4707_;
v_safety_4679_ = v_safety_4708_;
v___y_4680_ = v___y_4693_;
v___y_4681_ = v___y_4694_;
goto v___jp_4675_;
}
else
{
lean_dec_ref(v_toConstantVal_4707_);
lean_dec_ref(v_defn_4692_);
lean_dec(v_decl_3739_);
return v___x_4715_;
}
}
}
}
else
{
v___y_4658_ = v_defn_4692_;
v_exportedInfo_x3f_4659_ = v___x_4580_;
v___y_4660_ = v___y_4693_;
v___y_4661_ = v___y_4694_;
goto v___jp_4657_;
}
}
}
else
{
lean_dec(v___x_4697_);
lean_dec_ref(v_env_4696_);
v___y_4658_ = v_defn_4692_;
v_exportedInfo_x3f_4659_ = v___x_4580_;
v___y_4660_ = v___y_4693_;
v___y_4661_ = v___y_4694_;
goto v___jp_4657_;
}
}
}
}
}
else
{
goto v___jp_4235_;
}
v___jp_4421_:
{
lean_object* v___x_4433_; 
lean_inc_ref(v___y_4422_);
v___x_4433_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_4428_, v___y_4422_, v___y_4423_, v___y_4432_);
if (lean_obj_tag(v___x_4433_) == 0)
{
lean_object* v___x_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4489_; 
lean_dec_ref_known(v___x_4433_, 1);
lean_dec(v___y_4430_);
lean_inc_ref(v___y_4431_);
v___x_4434_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4431_, v___y_4426_);
v_isSharedCheck_4489_ = !lean_is_exclusive(v___x_4434_);
if (v_isSharedCheck_4489_ == 0)
{
lean_object* v_unused_4490_; 
v_unused_4490_ = lean_ctor_get(v___x_4434_, 0);
lean_dec(v_unused_4490_);
v___x_4436_ = v___x_4434_;
v_isShared_4437_ = v_isSharedCheck_4489_;
goto v_resetjp_4435_;
}
else
{
lean_dec(v___x_4434_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4489_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v___x_4438_; lean_object* v___x_4439_; uint8_t v___x_4440_; 
v___x_4438_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4429_);
v___x_4439_ = l_Lean_Elab_async;
v___x_4440_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_4438_, v___x_4439_);
lean_dec_ref(v___x_4438_);
if (v___x_4440_ == 0)
{
lean_object* v___x_4441_; lean_object* v_r_4442_; 
lean_del_object(v___x_4436_);
lean_dec_ref(v___y_4427_);
lean_dec_ref(v___y_4425_);
v___x_4441_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4422_, v___y_4426_);
lean_dec_ref(v___x_4441_);
v_r_4442_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3739_, v___y_4429_, v___y_4426_);
if (lean_obj_tag(v_r_4442_) == 0)
{
lean_object* v_a_4443_; lean_object* v___x_4445_; uint8_t v_isShared_4446_; uint8_t v_isSharedCheck_4461_; 
v_a_4443_ = lean_ctor_get(v_r_4442_, 0);
v_isSharedCheck_4461_ = !lean_is_exclusive(v_r_4442_);
if (v_isSharedCheck_4461_ == 0)
{
v___x_4445_ = v_r_4442_;
v_isShared_4446_ = v_isSharedCheck_4461_;
goto v_resetjp_4444_;
}
else
{
lean_inc(v_a_4443_);
lean_dec(v_r_4442_);
v___x_4445_ = lean_box(0);
v_isShared_4446_ = v_isSharedCheck_4461_;
goto v_resetjp_4444_;
}
v_resetjp_4444_:
{
lean_object* v___x_4448_; 
lean_inc(v_a_4443_);
if (v_isShared_4446_ == 0)
{
lean_ctor_set_tag(v___x_4445_, 1);
v___x_4448_ = v___x_4445_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v_a_4443_);
v___x_4448_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
lean_object* v___x_4449_; 
v___x_4449_ = lean_apply_2(v___y_4424_, v___x_4448_, lean_box(0));
if (lean_obj_tag(v___x_4449_) == 0)
{
lean_object* v___x_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4457_; 
lean_dec_ref_known(v___x_4449_, 1);
v___x_4450_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4431_, v___y_4426_);
v_isSharedCheck_4457_ = !lean_is_exclusive(v___x_4450_);
if (v_isSharedCheck_4457_ == 0)
{
lean_object* v_unused_4458_; 
v_unused_4458_ = lean_ctor_get(v___x_4450_, 0);
lean_dec(v_unused_4458_);
v___x_4452_ = v___x_4450_;
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
else
{
lean_dec(v___x_4450_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v___x_4455_; 
if (v_isShared_4453_ == 0)
{
lean_ctor_set(v___x_4452_, 0, v_a_4443_);
v___x_4455_ = v___x_4452_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v_a_4443_);
v___x_4455_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
return v___x_4455_;
}
}
}
else
{
lean_object* v_a_4459_; 
lean_dec(v_a_4443_);
v_a_4459_ = lean_ctor_get(v___x_4449_, 0);
lean_inc(v_a_4459_);
lean_dec_ref_known(v___x_4449_, 1);
v___y_3745_ = v___y_4426_;
v___y_3746_ = v___y_4431_;
v_a_3747_ = v_a_4459_;
goto v___jp_3744_;
}
}
}
}
else
{
lean_object* v_a_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; 
v_a_4462_ = lean_ctor_get(v_r_4442_, 0);
lean_inc(v_a_4462_);
lean_dec_ref_known(v_r_4442_, 1);
v___x_4463_ = lean_box(0);
v___x_4464_ = lean_apply_2(v___y_4424_, v___x_4463_, lean_box(0));
if (lean_obj_tag(v___x_4464_) == 0)
{
lean_dec_ref_known(v___x_4464_, 1);
v___y_3745_ = v___y_4426_;
v___y_3746_ = v___y_4431_;
v_a_3747_ = v_a_4462_;
goto v___jp_3744_;
}
else
{
lean_object* v_a_4465_; 
lean_dec(v_a_4462_);
v_a_4465_ = lean_ctor_get(v___x_4464_, 0);
lean_inc(v_a_4465_);
lean_dec_ref_known(v___x_4464_, 1);
v___y_3745_ = v___y_4426_;
v___y_3746_ = v___y_4431_;
v_a_3747_ = v_a_4465_;
goto v___jp_3744_;
}
}
}
else
{
lean_object* v___x_4466_; lean_object* v___x_4468_; 
lean_dec_ref(v___y_4431_);
lean_dec_ref(v___y_4424_);
lean_dec_ref(v___y_4422_);
lean_dec(v_decl_3739_);
v___x_4466_ = l_IO_CancelToken_new();
if (v_isShared_4437_ == 0)
{
lean_ctor_set_tag(v___x_4436_, 1);
lean_ctor_set(v___x_4436_, 0, v___x_4466_);
v___x_4468_ = v___x_4436_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v___x_4466_);
v___x_4468_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; 
v___x_4469_ = lean_unsigned_to_nat(0u);
v___x_4470_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_4471_ = l_Lean_Name_toString(v___x_4470_, v_hasTrace_3773_);
lean_inc_ref(v___x_4468_);
v___x_4472_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_4427_, v___x_4468_, v___x_4471_, v___y_4429_, v___y_4426_);
if (lean_obj_tag(v___x_4472_) == 0)
{
lean_object* v_a_4473_; lean_object* v_checked_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; 
v_a_4473_ = lean_ctor_get(v___x_4472_, 0);
lean_inc(v_a_4473_);
lean_dec_ref_known(v___x_4472_, 1);
v_checked_4474_ = lean_ctor_get(v___y_4425_, 2);
lean_inc_ref(v_checked_4474_);
lean_dec_ref(v___y_4425_);
v___x_4475_ = lean_io_map_task(v_a_4473_, v_checked_4474_, v___x_4469_, v___x_4420_);
v___x_4476_ = lean_box(0);
v___x_4477_ = lean_box(2);
v___x_4478_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4478_, 0, v___x_4476_);
lean_ctor_set(v___x_4478_, 1, v___x_4477_);
lean_ctor_set(v___x_4478_, 2, v___x_4468_);
lean_ctor_set(v___x_4478_, 3, v___x_4475_);
v___x_4479_ = l_Lean_Core_logSnapshotTask___redArg(v___x_4478_, v___y_4426_);
return v___x_4479_;
}
else
{
lean_object* v_a_4480_; lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4487_; 
lean_dec_ref(v___x_4468_);
lean_dec_ref(v___y_4425_);
v_a_4480_ = lean_ctor_get(v___x_4472_, 0);
v_isSharedCheck_4487_ = !lean_is_exclusive(v___x_4472_);
if (v_isSharedCheck_4487_ == 0)
{
v___x_4482_ = v___x_4472_;
v_isShared_4483_ = v_isSharedCheck_4487_;
goto v_resetjp_4481_;
}
else
{
lean_inc(v_a_4480_);
lean_dec(v___x_4472_);
v___x_4482_ = lean_box(0);
v_isShared_4483_ = v_isSharedCheck_4487_;
goto v_resetjp_4481_;
}
v_resetjp_4481_:
{
lean_object* v___x_4485_; 
if (v_isShared_4483_ == 0)
{
v___x_4485_ = v___x_4482_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4486_; 
v_reuseFailAlloc_4486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4486_, 0, v_a_4480_);
v___x_4485_ = v_reuseFailAlloc_4486_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
return v___x_4485_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4502_; 
lean_dec_ref(v___y_4431_);
lean_dec_ref(v___y_4427_);
lean_dec_ref(v___y_4425_);
lean_dec_ref(v___y_4424_);
lean_dec_ref(v___y_4422_);
lean_dec(v_decl_3739_);
v_a_4491_ = lean_ctor_get(v___x_4433_, 0);
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4433_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4493_ = v___x_4433_;
v_isShared_4494_ = v_isSharedCheck_4502_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_a_4491_);
lean_dec(v___x_4433_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4502_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4500_; 
v___x_4495_ = lean_io_error_to_string(v_a_4491_);
v___x_4496_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4496_, 0, v___x_4495_);
v___x_4497_ = l_Lean_MessageData_ofFormat(v___x_4496_);
v___x_4498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4498_, 0, v___y_4430_);
lean_ctor_set(v___x_4498_, 1, v___x_4497_);
if (v_isShared_4494_ == 0)
{
lean_ctor_set(v___x_4493_, 0, v___x_4498_);
v___x_4500_ = v___x_4493_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v___x_4498_);
v___x_4500_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
return v___x_4500_;
}
}
}
}
v___jp_4503_:
{
lean_object* v_ref_4512_; lean_object* v___x_4513_; 
v_ref_4512_ = lean_ctor_get(v___y_4508_, 2);
lean_inc_ref(v___y_4510_);
v___x_4513_ = l_Lean_Environment_addConstAsync(v___y_4510_, v___y_4509_, v___y_4505_, v___y_4511_, v___x_4420_, v_hasTrace_3773_);
if (lean_obj_tag(v___x_4513_) == 0)
{
lean_object* v_a_4514_; lean_object* v_mainEnv_4515_; lean_object* v_asyncEnv_4516_; lean_object* v___f_4517_; lean_object* v___f_4518_; lean_object* v___x_4519_; 
v_a_4514_ = lean_ctor_get(v___x_4513_, 0);
lean_inc_n(v_a_4514_, 3);
lean_dec_ref_known(v___x_4513_, 1);
v_mainEnv_4515_ = lean_ctor_get(v_a_4514_, 0);
lean_inc_ref(v_mainEnv_4515_);
v_asyncEnv_4516_ = lean_ctor_get(v_a_4514_, 1);
lean_inc_ref_n(v_asyncEnv_4516_, 2);
lean_inc(v_ref_4512_);
lean_inc(v___y_4507_);
v___f_4517_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4517_, 0, v___y_4507_);
lean_closure_set(v___f_4517_, 1, v_a_4514_);
lean_closure_set(v___f_4517_, 2, v_ref_4512_);
lean_inc(v_decl_3739_);
v___f_4518_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4518_, 0, v_a_4514_);
lean_closure_set(v___f_4518_, 1, v_asyncEnv_4516_);
lean_closure_set(v___f_4518_, 2, v_decl_3739_);
v___x_4519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4519_, 0, v___y_4504_);
if (lean_obj_tag(v___y_4506_) == 0)
{
lean_inc(v_ref_4512_);
lean_inc_ref(v___x_4519_);
v___y_4422_ = v_asyncEnv_4516_;
v___y_4423_ = v___x_4519_;
v___y_4424_ = v___f_4517_;
v___y_4425_ = v___y_4510_;
v___y_4426_ = v___y_4507_;
v___y_4427_ = v___f_4518_;
v___y_4428_ = v_a_4514_;
v___y_4429_ = v___y_4508_;
v___y_4430_ = v_ref_4512_;
v___y_4431_ = v_mainEnv_4515_;
v___y_4432_ = v___x_4519_;
goto v___jp_4421_;
}
else
{
lean_inc(v_ref_4512_);
v___y_4422_ = v_asyncEnv_4516_;
v___y_4423_ = v___x_4519_;
v___y_4424_ = v___f_4517_;
v___y_4425_ = v___y_4510_;
v___y_4426_ = v___y_4507_;
v___y_4427_ = v___f_4518_;
v___y_4428_ = v_a_4514_;
v___y_4429_ = v___y_4508_;
v___y_4430_ = v_ref_4512_;
v___y_4431_ = v_mainEnv_4515_;
v___y_4432_ = v___y_4506_;
goto v___jp_4421_;
}
}
else
{
lean_object* v_a_4520_; lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4531_; 
lean_dec_ref(v___y_4510_);
lean_dec(v___y_4506_);
lean_dec_ref(v___y_4504_);
lean_dec(v_decl_3739_);
v_a_4520_ = lean_ctor_get(v___x_4513_, 0);
v_isSharedCheck_4531_ = !lean_is_exclusive(v___x_4513_);
if (v_isSharedCheck_4531_ == 0)
{
v___x_4522_ = v___x_4513_;
v_isShared_4523_ = v_isSharedCheck_4531_;
goto v_resetjp_4521_;
}
else
{
lean_inc(v_a_4520_);
lean_dec(v___x_4513_);
v___x_4522_ = lean_box(0);
v_isShared_4523_ = v_isSharedCheck_4531_;
goto v_resetjp_4521_;
}
v_resetjp_4521_:
{
lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4529_; 
v___x_4524_ = lean_io_error_to_string(v_a_4520_);
v___x_4525_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4525_, 0, v___x_4524_);
v___x_4526_ = l_Lean_MessageData_ofFormat(v___x_4525_);
lean_inc(v_ref_4512_);
v___x_4527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4527_, 0, v_ref_4512_);
lean_ctor_set(v___x_4527_, 1, v___x_4526_);
if (v_isShared_4523_ == 0)
{
lean_ctor_set(v___x_4522_, 0, v___x_4527_);
v___x_4529_ = v___x_4522_;
goto v_reusejp_4528_;
}
else
{
lean_object* v_reuseFailAlloc_4530_; 
v_reuseFailAlloc_4530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4530_, 0, v___x_4527_);
v___x_4529_ = v_reuseFailAlloc_4530_;
goto v_reusejp_4528_;
}
v_reusejp_4528_:
{
return v___x_4529_;
}
}
}
}
v___jp_4532_:
{
lean_object* v___x_4539_; 
v___x_4539_ = lean_st_ref_get(v___y_4538_);
if (lean_obj_tag(v_exportedInfo_x3f_4536_) == 0)
{
lean_object* v_env_4540_; lean_object* v___x_4541_; 
v_env_4540_ = lean_ctor_get(v___x_4539_, 0);
lean_inc_ref(v_env_4540_);
lean_dec(v___x_4539_);
v___x_4541_ = lean_box(0);
v___y_4504_ = v___y_4535_;
v___y_4505_ = v___y_4534_;
v___y_4506_ = v_exportedInfo_x3f_4536_;
v___y_4507_ = v___y_4538_;
v___y_4508_ = v___y_4537_;
v___y_4509_ = v___y_4533_;
v___y_4510_ = v_env_4540_;
v___y_4511_ = v___x_4541_;
goto v___jp_4503_;
}
else
{
lean_object* v_env_4542_; lean_object* v_val_4543_; uint8_t v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; 
v_env_4542_ = lean_ctor_get(v___x_4539_, 0);
lean_inc_ref(v_env_4542_);
lean_dec(v___x_4539_);
v_val_4543_ = lean_ctor_get(v_exportedInfo_x3f_4536_, 0);
v___x_4544_ = l_Lean_ConstantKind_ofConstantInfo(v_val_4543_);
v___x_4545_ = lean_box(v___x_4544_);
v___x_4546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4546_, 0, v___x_4545_);
v___y_4504_ = v___y_4535_;
v___y_4505_ = v___y_4534_;
v___y_4506_ = v_exportedInfo_x3f_4536_;
v___y_4507_ = v___y_4538_;
v___y_4508_ = v___y_4537_;
v___y_4509_ = v___y_4533_;
v___y_4510_ = v_env_4542_;
v___y_4511_ = v___x_4546_;
goto v___jp_4503_;
}
}
v___jp_4547_:
{
lean_object* v___x_4553_; 
lean_inc_ref(v___y_4550_);
v___x_4553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4553_, 0, v___y_4550_);
v___y_4533_ = v___y_4549_;
v___y_4534_ = v___y_4548_;
v___y_4535_ = v___y_4550_;
v_exportedInfo_x3f_4536_ = v___x_4553_;
v___y_4537_ = v___y_4551_;
v___y_4538_ = v___y_4552_;
goto v___jp_4532_;
}
v___jp_4554_:
{
lean_object* v___x_4560_; 
lean_inc_ref(v___y_4557_);
v___x_4560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4560_, 0, v___y_4557_);
v___y_4533_ = v___y_4556_;
v___y_4534_ = v___y_4555_;
v___y_4535_ = v___y_4557_;
v_exportedInfo_x3f_4536_ = v___x_4560_;
v___y_4537_ = v___y_4558_;
v___y_4538_ = v___y_4559_;
goto v___jp_4532_;
}
}
else
{
goto v___jp_4235_;
}
v___jp_4144_:
{
lean_object* v___x_4148_; double v___x_4149_; double v___x_4150_; double v___x_4151_; double v___x_4152_; double v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
v___x_4148_ = lean_io_mono_nanos_now();
v___x_4149_ = lean_float_of_nat(v___y_4145_);
v___x_4150_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_4151_ = lean_float_div(v___x_4149_, v___x_4150_);
v___x_4152_ = lean_float_of_nat(v___x_4148_);
v___x_4153_ = lean_float_div(v___x_4152_, v___x_4150_);
v___x_4154_ = lean_box_float(v___x_4151_);
v___x_4155_ = lean_box_float(v___x_4153_);
v___x_4156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4154_);
lean_ctor_set(v___x_4156_, 1, v___x_4155_);
v___x_4157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4157_, 0, v_a_4147_);
lean_ctor_set(v___x_4157_, 1, v___x_4156_);
v___x_4158_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3916_, v_hasTrace_3773_, v___x_4141_, v_options_3771_, v___x_4143_, v___y_4146_, v___f_4140_, v___x_4157_, v_a_3741_, v_a_3742_);
return v___x_4158_;
}
v___jp_4159_:
{
lean_object* v___x_4163_; 
v___x_4163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4163_, 0, v_a_4162_);
v___y_4145_ = v___y_4160_;
v___y_4146_ = v___y_4161_;
v_a_4147_ = v___x_4163_;
goto v___jp_4144_;
}
v___jp_4164_:
{
if (lean_obj_tag(v___y_4167_) == 0)
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4175_; 
v_a_4168_ = lean_ctor_get(v___y_4167_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___y_4167_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4170_ = v___y_4167_;
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___y_4167_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4173_; 
if (v_isShared_4171_ == 0)
{
lean_ctor_set_tag(v___x_4170_, 1);
v___x_4173_ = v___x_4170_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_a_4168_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
v___y_4145_ = v___y_4165_;
v___y_4146_ = v___y_4166_;
v_a_4147_ = v___x_4173_;
goto v___jp_4144_;
}
}
}
else
{
lean_object* v_a_4176_; 
v_a_4176_ = lean_ctor_get(v___y_4167_, 0);
lean_inc(v_a_4176_);
lean_dec_ref_known(v___y_4167_, 1);
v___y_4160_ = v___y_4165_;
v___y_4161_ = v___y_4166_;
v_a_4162_ = v_a_4176_;
goto v___jp_4159_;
}
}
v___jp_4177_:
{
lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4182_ = lean_box(0);
lean_inc(v_a_3742_);
lean_inc_ref(v_a_3741_);
v___x_4183_ = lean_apply_5(v___y_4179_, v___x_4182_, v___y_4180_, v_a_3741_, v_a_3742_, lean_box(0));
v___y_4165_ = v___y_4178_;
v___y_4166_ = v___y_4181_;
v___y_4167_ = v___x_4183_;
goto v___jp_4164_;
}
v___jp_4184_:
{
lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4189_ = lean_box(0);
lean_inc(v_a_3742_);
lean_inc_ref(v_a_3741_);
v___x_4190_ = lean_apply_5(v___y_4185_, v___x_4189_, v___y_4187_, v_a_3741_, v_a_3742_, lean_box(0));
v___y_4165_ = v___y_4186_;
v___y_4166_ = v___y_4188_;
v___y_4167_ = v___x_4190_;
goto v___jp_4164_;
}
v___jp_4191_:
{
lean_object* v___x_4195_; double v___x_4196_; double v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; 
v___x_4195_ = lean_io_get_num_heartbeats();
v___x_4196_ = lean_float_of_nat(v___y_4192_);
v___x_4197_ = lean_float_of_nat(v___x_4195_);
v___x_4198_ = lean_box_float(v___x_4196_);
v___x_4199_ = lean_box_float(v___x_4197_);
v___x_4200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4200_, 0, v___x_4198_);
lean_ctor_set(v___x_4200_, 1, v___x_4199_);
v___x_4201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4201_, 0, v_a_4194_);
lean_ctor_set(v___x_4201_, 1, v___x_4200_);
v___x_4202_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3916_, v_hasTrace_3773_, v___x_4141_, v_options_3771_, v___x_4143_, v___y_4193_, v___f_4140_, v___x_4201_, v_a_3741_, v_a_3742_);
return v___x_4202_;
}
v___jp_4203_:
{
lean_object* v___x_4207_; 
v___x_4207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4207_, 0, v_a_4206_);
v___y_4192_ = v___y_4204_;
v___y_4193_ = v___y_4205_;
v_a_4194_ = v___x_4207_;
goto v___jp_4191_;
}
v___jp_4208_:
{
if (lean_obj_tag(v___y_4211_) == 0)
{
lean_object* v_a_4212_; lean_object* v___x_4214_; uint8_t v_isShared_4215_; uint8_t v_isSharedCheck_4219_; 
v_a_4212_ = lean_ctor_get(v___y_4211_, 0);
v_isSharedCheck_4219_ = !lean_is_exclusive(v___y_4211_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4214_ = v___y_4211_;
v_isShared_4215_ = v_isSharedCheck_4219_;
goto v_resetjp_4213_;
}
else
{
lean_inc(v_a_4212_);
lean_dec(v___y_4211_);
v___x_4214_ = lean_box(0);
v_isShared_4215_ = v_isSharedCheck_4219_;
goto v_resetjp_4213_;
}
v_resetjp_4213_:
{
lean_object* v___x_4217_; 
if (v_isShared_4215_ == 0)
{
lean_ctor_set_tag(v___x_4214_, 1);
v___x_4217_ = v___x_4214_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_a_4212_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
v___y_4192_ = v___y_4209_;
v___y_4193_ = v___y_4210_;
v_a_4194_ = v___x_4217_;
goto v___jp_4191_;
}
}
}
else
{
lean_object* v_a_4220_; 
v_a_4220_ = lean_ctor_get(v___y_4211_, 0);
lean_inc(v_a_4220_);
lean_dec_ref_known(v___y_4211_, 1);
v___y_4204_ = v___y_4209_;
v___y_4205_ = v___y_4210_;
v_a_4206_ = v_a_4220_;
goto v___jp_4203_;
}
}
v___jp_4221_:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4226_ = lean_box(0);
lean_inc(v_a_3742_);
lean_inc_ref(v_a_3741_);
v___x_4227_ = lean_apply_5(v___y_4224_, v___x_4226_, v___y_4222_, v_a_3741_, v_a_3742_, lean_box(0));
v___y_4209_ = v___y_4223_;
v___y_4210_ = v___y_4225_;
v___y_4211_ = v___x_4227_;
goto v___jp_4208_;
}
v___jp_4228_:
{
lean_object* v___x_4233_; lean_object* v___x_4234_; 
v___x_4233_ = lean_box(0);
lean_inc(v_a_3742_);
lean_inc_ref(v_a_3741_);
v___x_4234_ = lean_apply_5(v___y_4229_, v___x_4233_, v___y_4230_, v_a_3741_, v_a_3742_, lean_box(0));
v___y_4209_ = v___y_4231_;
v___y_4210_ = v___y_4232_;
v___y_4211_ = v___x_4234_;
goto v___jp_4208_;
}
v___jp_4235_:
{
lean_object* v___x_4236_; lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4418_; 
v___x_4236_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v_a_3742_);
v_a_4237_ = lean_ctor_get(v___x_4236_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4236_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4239_ = v___x_4236_;
v_isShared_4240_ = v_isSharedCheck_4418_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_dec(v___x_4236_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4418_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4241_; uint8_t v___x_4242_; 
v___x_4241_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4242_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3771_, v___x_4241_);
if (v___x_4242_ == 0)
{
lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v_env_4245_; lean_object* v_nextMacroScope_4246_; lean_object* v_ngen_4247_; lean_object* v_auxDeclNGen_4248_; lean_object* v_traceState_4249_; lean_object* v_recordedDeps_4250_; lean_object* v_messages_4251_; lean_object* v_infoState_4252_; lean_object* v_snapshotTasks_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4329_; 
v___x_4243_ = lean_io_mono_nanos_now();
v___x_4244_ = lean_st_ref_take(v_a_3742_);
v_env_4245_ = lean_ctor_get(v___x_4244_, 0);
v_nextMacroScope_4246_ = lean_ctor_get(v___x_4244_, 1);
v_ngen_4247_ = lean_ctor_get(v___x_4244_, 2);
v_auxDeclNGen_4248_ = lean_ctor_get(v___x_4244_, 3);
v_traceState_4249_ = lean_ctor_get(v___x_4244_, 4);
v_recordedDeps_4250_ = lean_ctor_get(v___x_4244_, 6);
v_messages_4251_ = lean_ctor_get(v___x_4244_, 7);
v_infoState_4252_ = lean_ctor_get(v___x_4244_, 8);
v_snapshotTasks_4253_ = lean_ctor_get(v___x_4244_, 9);
v_isSharedCheck_4329_ = !lean_is_exclusive(v___x_4244_);
if (v_isSharedCheck_4329_ == 0)
{
lean_object* v_unused_4330_; 
v_unused_4330_ = lean_ctor_get(v___x_4244_, 5);
lean_dec(v_unused_4330_);
v___x_4255_ = v___x_4244_;
v_isShared_4256_ = v_isSharedCheck_4329_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_snapshotTasks_4253_);
lean_inc(v_infoState_4252_);
lean_inc(v_messages_4251_);
lean_inc(v_recordedDeps_4250_);
lean_inc(v_traceState_4249_);
lean_inc(v_auxDeclNGen_4248_);
lean_inc(v_ngen_4247_);
lean_inc(v_nextMacroScope_4246_);
lean_inc(v_env_4245_);
lean_dec(v___x_4244_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4329_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4261_; 
lean_inc(v_decl_3739_);
v___x_4257_ = l_Lean_Declaration_getNames(v_decl_3739_);
v___x_4258_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4245_, v___x_4257_);
v___x_4259_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4256_ == 0)
{
lean_ctor_set(v___x_4255_, 5, v___x_4259_);
lean_ctor_set(v___x_4255_, 0, v___x_4258_);
v___x_4261_ = v___x_4255_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v___x_4258_);
lean_ctor_set(v_reuseFailAlloc_4328_, 1, v_nextMacroScope_4246_);
lean_ctor_set(v_reuseFailAlloc_4328_, 2, v_ngen_4247_);
lean_ctor_set(v_reuseFailAlloc_4328_, 3, v_auxDeclNGen_4248_);
lean_ctor_set(v_reuseFailAlloc_4328_, 4, v_traceState_4249_);
lean_ctor_set(v_reuseFailAlloc_4328_, 5, v___x_4259_);
lean_ctor_set(v_reuseFailAlloc_4328_, 6, v_recordedDeps_4250_);
lean_ctor_set(v_reuseFailAlloc_4328_, 7, v_messages_4251_);
lean_ctor_set(v_reuseFailAlloc_4328_, 8, v_infoState_4252_);
lean_ctor_set(v_reuseFailAlloc_4328_, 9, v_snapshotTasks_4253_);
v___x_4261_ = v_reuseFailAlloc_4328_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___f_4266_; 
v___x_4262_ = lean_st_ref_put(v_a_3742_, v___x_4261_);
v___x_4263_ = lean_box(0);
v___x_4264_ = lean_box(v_hasTrace_3773_);
v___x_4265_ = lean_box(v___x_4242_);
lean_inc(v_decl_3739_);
v___f_4266_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed), 11, 6);
lean_closure_set(v___f_4266_, 0, v_decl_3739_);
lean_closure_set(v___f_4266_, 1, v___x_4264_);
lean_closure_set(v___f_4266_, 2, v___x_4265_);
lean_closure_set(v___f_4266_, 3, v_cls_3916_);
lean_closure_set(v___f_4266_, 4, v___x_4259_);
lean_closure_set(v___f_4266_, 5, v___x_4263_);
switch(lean_obj_tag(v_decl_3739_))
{
case 2:
{
lean_object* v_val_4267_; lean_object* v___f_4268_; lean_object* v___x_4269_; 
lean_del_object(v___x_4239_);
v_val_4267_ = lean_ctor_get(v_decl_3739_, 0);
lean_inc_ref_n(v_val_4267_, 2);
lean_dec_ref_known(v_decl_3739_, 1);
v___f_4268_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed), 7, 2);
lean_closure_set(v___f_4268_, 0, v_val_4267_);
lean_closure_set(v___f_4268_, 1, v___f_4266_);
v___x_4269_ = lean_st_ref_get(v_a_3742_);
if (v_forceExpose_3740_ == 0)
{
lean_object* v_env_4270_; lean_object* v___x_4271_; uint8_t v_isModule_4272_; 
v_env_4270_ = lean_ctor_get(v___x_4269_, 0);
lean_inc_ref(v_env_4270_);
lean_dec(v___x_4269_);
v___x_4271_ = l_Lean_Environment_header(v_env_4270_);
lean_dec_ref(v_env_4270_);
v_isModule_4272_ = lean_ctor_get_uint8(v___x_4271_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4271_);
if (v_isModule_4272_ == 0)
{
lean_dec_ref(v_val_4267_);
v___y_4178_ = v___x_4243_;
v___y_4179_ = v___f_4268_;
v___y_4180_ = v___x_4263_;
v___y_4181_ = v_a_4237_;
goto v___jp_4177_;
}
else
{
if (v___x_4143_ == 0)
{
lean_object* v___x_4273_; lean_object* v___x_4274_; 
v___x_4273_ = lean_box(0);
v___x_4274_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(v_val_4267_, v___x_4242_, v___f_4268_, v___x_4273_, v_a_3741_, v_a_3742_);
lean_dec_ref(v_val_4267_);
v___y_4165_ = v___x_4243_;
v___y_4166_ = v_a_4237_;
v___y_4167_ = v___x_4274_;
goto v___jp_4164_;
}
else
{
lean_object* v_toConstantVal_4275_; lean_object* v_name_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; 
v_toConstantVal_4275_ = lean_ctor_get(v_val_4267_, 0);
v_name_4276_ = lean_ctor_get(v_toConstantVal_4275_, 0);
v___x_4277_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4276_);
v___x_4278_ = l_Lean_MessageData_ofName(v_name_4276_);
v___x_4279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4279_, 0, v___x_4277_);
lean_ctor_set(v___x_4279_, 1, v___x_4278_);
v___x_4280_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4281_, 0, v___x_4279_);
lean_ctor_set(v___x_4281_, 1, v___x_4280_);
v___x_4282_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3916_, v___x_4281_, v_a_3741_, v_a_3742_);
if (lean_obj_tag(v___x_4282_) == 0)
{
lean_object* v_a_4283_; lean_object* v___x_4284_; 
v_a_4283_ = lean_ctor_get(v___x_4282_, 0);
lean_inc(v_a_4283_);
lean_dec_ref_known(v___x_4282_, 1);
v___x_4284_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(v_val_4267_, v___x_4242_, v___f_4268_, v_a_4283_, v_a_3741_, v_a_3742_);
lean_dec_ref(v_val_4267_);
v___y_4165_ = v___x_4243_;
v___y_4166_ = v_a_4237_;
v___y_4167_ = v___x_4284_;
goto v___jp_4164_;
}
else
{
lean_object* v_a_4285_; 
lean_dec_ref(v___f_4268_);
lean_dec_ref(v_val_4267_);
v_a_4285_ = lean_ctor_get(v___x_4282_, 0);
lean_inc(v_a_4285_);
lean_dec_ref_known(v___x_4282_, 1);
v___y_4160_ = v___x_4243_;
v___y_4161_ = v_a_4237_;
v_a_4162_ = v_a_4285_;
goto v___jp_4159_;
}
}
}
}
else
{
lean_dec(v___x_4269_);
lean_dec_ref(v_val_4267_);
v___y_4178_ = v___x_4243_;
v___y_4179_ = v___f_4268_;
v___y_4180_ = v___x_4263_;
v___y_4181_ = v_a_4237_;
goto v___jp_4177_;
}
}
case 1:
{
lean_object* v_val_4286_; lean_object* v___x_4287_; 
lean_del_object(v___x_4239_);
v_val_4286_ = lean_ctor_get(v_decl_3739_, 0);
lean_inc_ref(v_val_4286_);
lean_dec_ref_known(v_decl_3739_, 1);
v___x_4287_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v___f_4266_, v___x_4242_, v_forceExpose_3740_, v___x_4263_, v_cls_3916_, v_val_4286_, v_a_3741_, v_a_3742_);
v___y_4165_ = v___x_4243_;
v___y_4166_ = v_a_4237_;
v___y_4167_ = v___x_4287_;
goto v___jp_4164_;
}
case 5:
{
lean_object* v_defns_4288_; 
lean_del_object(v___x_4239_);
v_defns_4288_ = lean_ctor_get(v_decl_3739_, 0);
if (lean_obj_tag(v_defns_4288_) == 1)
{
lean_object* v_tail_4289_; 
v_tail_4289_ = lean_ctor_get(v_defns_4288_, 1);
if (lean_obj_tag(v_tail_4289_) == 0)
{
lean_object* v_head_4290_; lean_object* v___x_4291_; 
lean_inc_ref(v_defns_4288_);
lean_dec_ref_known(v_decl_3739_, 1);
v_head_4290_ = lean_ctor_get(v_defns_4288_, 0);
lean_inc(v_head_4290_);
lean_dec_ref_known(v_defns_4288_, 2);
v___x_4291_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v___f_4266_, v___x_4242_, v_forceExpose_3740_, v___x_4263_, v_cls_3916_, v_head_4290_, v_a_3741_, v_a_3742_);
v___y_4165_ = v___x_4243_;
v___y_4166_ = v_a_4237_;
v___y_4167_ = v___x_4291_;
goto v___jp_4164_;
}
else
{
lean_object* v___x_4292_; 
lean_dec_ref(v___f_4266_);
lean_inc_ref(v_decl_3739_);
v___x_4292_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3739_, v_cls_3916_, v_decl_3739_, v_a_3741_, v_a_3742_);
lean_dec_ref_known(v_decl_3739_, 1);
v___y_4165_ = v___x_4243_;
v___y_4166_ = v_a_4237_;
v___y_4167_ = v___x_4292_;
goto v___jp_4164_;
}
}
else
{
lean_object* v___x_4293_; 
lean_dec_ref(v___f_4266_);
lean_inc_ref(v_decl_3739_);
v___x_4293_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3739_, v_cls_3916_, v_decl_3739_, v_a_3741_, v_a_3742_);
lean_dec_ref_known(v_decl_3739_, 1);
v___y_4165_ = v___x_4243_;
v___y_4166_ = v_a_4237_;
v___y_4167_ = v___x_4293_;
goto v___jp_4164_;
}
}
case 3:
{
lean_object* v_val_4294_; lean_object* v___f_4295_; lean_object* v___x_4296_; lean_object* v_env_4297_; lean_object* v___x_4298_; 
lean_del_object(v___x_4239_);
v_val_4294_ = lean_ctor_get(v_decl_3739_, 0);
lean_inc_ref_n(v_val_4294_, 2);
lean_dec_ref_known(v_decl_3739_, 1);
v___f_4295_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed), 7, 2);
lean_closure_set(v___f_4295_, 0, v_val_4294_);
lean_closure_set(v___f_4295_, 1, v___f_4266_);
v___x_4296_ = lean_st_ref_get(v_a_3742_);
v_env_4297_ = lean_ctor_get(v___x_4296_, 0);
lean_inc_ref(v_env_4297_);
lean_dec(v___x_4296_);
v___x_4298_ = lean_st_ref_get(v_a_3742_);
if (v_forceExpose_3740_ == 0)
{
lean_object* v_env_4299_; lean_object* v___x_4300_; uint8_t v_isModule_4301_; 
v_env_4299_ = lean_ctor_get(v___x_4298_, 0);
lean_inc_ref(v_env_4299_);
lean_dec(v___x_4298_);
v___x_4300_ = l_Lean_Environment_header(v_env_4297_);
lean_dec_ref(v_env_4297_);
v_isModule_4301_ = lean_ctor_get_uint8(v___x_4300_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4300_);
if (v_isModule_4301_ == 0)
{
lean_dec_ref(v_env_4299_);
lean_dec_ref(v_val_4294_);
v___y_4185_ = v___f_4295_;
v___y_4186_ = v___x_4243_;
v___y_4187_ = v___x_4263_;
v___y_4188_ = v_a_4237_;
goto v___jp_4184_;
}
else
{
uint8_t v_isExporting_4302_; 
v_isExporting_4302_ = lean_ctor_get_uint8(v_env_4299_, sizeof(void*)*13);
lean_dec_ref(v_env_4299_);
if (v_isExporting_4302_ == 0)
{
if (v___x_4143_ == 0)
{
lean_object* v___x_4303_; lean_object* v___x_4304_; 
v___x_4303_ = lean_box(0);
v___x_4304_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_4294_, v___f_4295_, v___x_4303_, v_a_3741_, v_a_3742_);
lean_dec_ref(v_val_4294_);
v___y_4165_ = v___x_4243_;
v___y_4166_ = v_a_4237_;
v___y_4167_ = v___x_4304_;
goto v___jp_4164_;
}
else
{
lean_object* v_toConstantVal_4305_; lean_object* v_name_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; 
v_toConstantVal_4305_ = lean_ctor_get(v_val_4294_, 0);
v_name_4306_ = lean_ctor_get(v_toConstantVal_4305_, 0);
v___x_4307_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4306_);
v___x_4308_ = l_Lean_MessageData_ofName(v_name_4306_);
v___x_4309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4309_, 0, v___x_4307_);
lean_ctor_set(v___x_4309_, 1, v___x_4308_);
v___x_4310_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4311_, 0, v___x_4309_);
lean_ctor_set(v___x_4311_, 1, v___x_4310_);
v___x_4312_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3916_, v___x_4311_, v_a_3741_, v_a_3742_);
if (lean_obj_tag(v___x_4312_) == 0)
{
lean_object* v_a_4313_; lean_object* v___x_4314_; 
v_a_4313_ = lean_ctor_get(v___x_4312_, 0);
lean_inc(v_a_4313_);
lean_dec_ref_known(v___x_4312_, 1);
v___x_4314_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_4294_, v___f_4295_, v_a_4313_, v_a_3741_, v_a_3742_);
lean_dec_ref(v_val_4294_);
v___y_4165_ = v___x_4243_;
v___y_4166_ = v_a_4237_;
v___y_4167_ = v___x_4314_;
goto v___jp_4164_;
}
else
{
lean_object* v_a_4315_; 
lean_dec_ref(v___f_4295_);
lean_dec_ref(v_val_4294_);
v_a_4315_ = lean_ctor_get(v___x_4312_, 0);
lean_inc(v_a_4315_);
lean_dec_ref_known(v___x_4312_, 1);
v___y_4160_ = v___x_4243_;
v___y_4161_ = v_a_4237_;
v_a_4162_ = v_a_4315_;
goto v___jp_4159_;
}
}
}
else
{
lean_dec_ref(v_val_4294_);
v___y_4185_ = v___f_4295_;
v___y_4186_ = v___x_4243_;
v___y_4187_ = v___x_4263_;
v___y_4188_ = v_a_4237_;
goto v___jp_4184_;
}
}
}
else
{
lean_dec(v___x_4298_);
lean_dec_ref(v_env_4297_);
lean_dec_ref(v_val_4294_);
v___y_4185_ = v___f_4295_;
v___y_4186_ = v___x_4243_;
v___y_4187_ = v___x_4263_;
v___y_4188_ = v_a_4237_;
goto v___jp_4184_;
}
}
case 0:
{
lean_object* v_val_4316_; lean_object* v_toConstantVal_4317_; lean_object* v_name_4318_; lean_object* v___x_4320_; 
lean_dec_ref(v___f_4266_);
v_val_4316_ = lean_ctor_get(v_decl_3739_, 0);
v_toConstantVal_4317_ = lean_ctor_get(v_val_4316_, 0);
v_name_4318_ = lean_ctor_get(v_toConstantVal_4317_, 0);
lean_inc_ref(v_val_4316_);
if (v_isShared_4240_ == 0)
{
lean_ctor_set(v___x_4239_, 0, v_val_4316_);
v___x_4320_ = v___x_4239_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_val_4316_);
v___x_4320_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
uint8_t v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; 
v___x_4321_ = 2;
v___x_4322_ = lean_box(v___x_4321_);
v___x_4323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4323_, 0, v___x_4320_);
lean_ctor_set(v___x_4323_, 1, v___x_4322_);
lean_inc(v_name_4318_);
v___x_4324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4324_, 0, v_name_4318_);
lean_ctor_set(v___x_4324_, 1, v___x_4323_);
v___x_4325_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_decl_3739_, v_hasTrace_3773_, v___x_4242_, v_cls_3916_, v___x_4259_, v___x_4263_, v___x_4324_, v___x_4263_, v_a_3741_, v_a_3742_);
v___y_4165_ = v___x_4243_;
v___y_4166_ = v_a_4237_;
v___y_4167_ = v___x_4325_;
goto v___jp_4164_;
}
}
default: 
{
lean_object* v___x_4327_; 
lean_dec_ref(v___f_4266_);
lean_del_object(v___x_4239_);
lean_inc(v_decl_3739_);
v___x_4327_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3739_, v_cls_3916_, v_decl_3739_, v_a_3741_, v_a_3742_);
lean_dec(v_decl_3739_);
v___y_4165_ = v___x_4243_;
v___y_4166_ = v_a_4237_;
v___y_4167_ = v___x_4327_;
goto v___jp_4164_;
}
}
}
}
}
else
{
lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v_env_4333_; lean_object* v_nextMacroScope_4334_; lean_object* v_ngen_4335_; lean_object* v_auxDeclNGen_4336_; lean_object* v_traceState_4337_; lean_object* v_recordedDeps_4338_; lean_object* v_messages_4339_; lean_object* v_infoState_4340_; lean_object* v_snapshotTasks_4341_; lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4416_; 
v___x_4331_ = lean_io_get_num_heartbeats();
v___x_4332_ = lean_st_ref_take(v_a_3742_);
v_env_4333_ = lean_ctor_get(v___x_4332_, 0);
v_nextMacroScope_4334_ = lean_ctor_get(v___x_4332_, 1);
v_ngen_4335_ = lean_ctor_get(v___x_4332_, 2);
v_auxDeclNGen_4336_ = lean_ctor_get(v___x_4332_, 3);
v_traceState_4337_ = lean_ctor_get(v___x_4332_, 4);
v_recordedDeps_4338_ = lean_ctor_get(v___x_4332_, 6);
v_messages_4339_ = lean_ctor_get(v___x_4332_, 7);
v_infoState_4340_ = lean_ctor_get(v___x_4332_, 8);
v_snapshotTasks_4341_ = lean_ctor_get(v___x_4332_, 9);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4332_);
if (v_isSharedCheck_4416_ == 0)
{
lean_object* v_unused_4417_; 
v_unused_4417_ = lean_ctor_get(v___x_4332_, 5);
lean_dec(v_unused_4417_);
v___x_4343_ = v___x_4332_;
v_isShared_4344_ = v_isSharedCheck_4416_;
goto v_resetjp_4342_;
}
else
{
lean_inc(v_snapshotTasks_4341_);
lean_inc(v_infoState_4340_);
lean_inc(v_messages_4339_);
lean_inc(v_recordedDeps_4338_);
lean_inc(v_traceState_4337_);
lean_inc(v_auxDeclNGen_4336_);
lean_inc(v_ngen_4335_);
lean_inc(v_nextMacroScope_4334_);
lean_inc(v_env_4333_);
lean_dec(v___x_4332_);
v___x_4343_ = lean_box(0);
v_isShared_4344_ = v_isSharedCheck_4416_;
goto v_resetjp_4342_;
}
v_resetjp_4342_:
{
lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4349_; 
lean_inc(v_decl_3739_);
v___x_4345_ = l_Lean_Declaration_getNames(v_decl_3739_);
v___x_4346_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4333_, v___x_4345_);
v___x_4347_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4344_ == 0)
{
lean_ctor_set(v___x_4343_, 5, v___x_4347_);
lean_ctor_set(v___x_4343_, 0, v___x_4346_);
v___x_4349_ = v___x_4343_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v___x_4346_);
lean_ctor_set(v_reuseFailAlloc_4415_, 1, v_nextMacroScope_4334_);
lean_ctor_set(v_reuseFailAlloc_4415_, 2, v_ngen_4335_);
lean_ctor_set(v_reuseFailAlloc_4415_, 3, v_auxDeclNGen_4336_);
lean_ctor_set(v_reuseFailAlloc_4415_, 4, v_traceState_4337_);
lean_ctor_set(v_reuseFailAlloc_4415_, 5, v___x_4347_);
lean_ctor_set(v_reuseFailAlloc_4415_, 6, v_recordedDeps_4338_);
lean_ctor_set(v_reuseFailAlloc_4415_, 7, v_messages_4339_);
lean_ctor_set(v_reuseFailAlloc_4415_, 8, v_infoState_4340_);
lean_ctor_set(v_reuseFailAlloc_4415_, 9, v_snapshotTasks_4341_);
v___x_4349_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___f_4353_; 
v___x_4350_ = lean_st_ref_put(v_a_3742_, v___x_4349_);
v___x_4351_ = lean_box(0);
v___x_4352_ = lean_box(v___x_4242_);
lean_inc(v_decl_3739_);
v___f_4353_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14___boxed), 10, 5);
lean_closure_set(v___f_4353_, 0, v_decl_3739_);
lean_closure_set(v___f_4353_, 1, v___x_4352_);
lean_closure_set(v___f_4353_, 2, v_cls_3916_);
lean_closure_set(v___f_4353_, 3, v___x_4347_);
lean_closure_set(v___f_4353_, 4, v___x_4351_);
switch(lean_obj_tag(v_decl_3739_))
{
case 2:
{
lean_object* v_val_4354_; lean_object* v___f_4355_; lean_object* v___x_4356_; 
lean_del_object(v___x_4239_);
v_val_4354_ = lean_ctor_get(v_decl_3739_, 0);
lean_inc_ref_n(v_val_4354_, 2);
lean_dec_ref_known(v_decl_3739_, 1);
v___f_4355_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed), 7, 2);
lean_closure_set(v___f_4355_, 0, v_val_4354_);
lean_closure_set(v___f_4355_, 1, v___f_4353_);
v___x_4356_ = lean_st_ref_get(v_a_3742_);
if (v_forceExpose_3740_ == 0)
{
lean_object* v_env_4357_; lean_object* v___x_4358_; uint8_t v_isModule_4359_; 
v_env_4357_ = lean_ctor_get(v___x_4356_, 0);
lean_inc_ref(v_env_4357_);
lean_dec(v___x_4356_);
v___x_4358_ = l_Lean_Environment_header(v_env_4357_);
lean_dec_ref(v_env_4357_);
v_isModule_4359_ = lean_ctor_get_uint8(v___x_4358_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4358_);
if (v_isModule_4359_ == 0)
{
lean_dec_ref(v_val_4354_);
v___y_4229_ = v___f_4355_;
v___y_4230_ = v___x_4351_;
v___y_4231_ = v___x_4331_;
v___y_4232_ = v_a_4237_;
goto v___jp_4228_;
}
else
{
if (v___x_4143_ == 0)
{
lean_object* v___x_4360_; lean_object* v___x_4361_; 
v___x_4360_ = lean_box(0);
v___x_4361_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_val_4354_, v___f_4355_, v___x_4360_, v_a_3741_, v_a_3742_);
lean_dec_ref(v_val_4354_);
v___y_4209_ = v___x_4331_;
v___y_4210_ = v_a_4237_;
v___y_4211_ = v___x_4361_;
goto v___jp_4208_;
}
else
{
lean_object* v_toConstantVal_4362_; lean_object* v_name_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; 
v_toConstantVal_4362_ = lean_ctor_get(v_val_4354_, 0);
v_name_4363_ = lean_ctor_get(v_toConstantVal_4362_, 0);
v___x_4364_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4363_);
v___x_4365_ = l_Lean_MessageData_ofName(v_name_4363_);
v___x_4366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4366_, 0, v___x_4364_);
lean_ctor_set(v___x_4366_, 1, v___x_4365_);
v___x_4367_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4368_, 0, v___x_4366_);
lean_ctor_set(v___x_4368_, 1, v___x_4367_);
v___x_4369_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3916_, v___x_4368_, v_a_3741_, v_a_3742_);
if (lean_obj_tag(v___x_4369_) == 0)
{
lean_object* v_a_4370_; lean_object* v___x_4371_; 
v_a_4370_ = lean_ctor_get(v___x_4369_, 0);
lean_inc(v_a_4370_);
lean_dec_ref_known(v___x_4369_, 1);
v___x_4371_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_val_4354_, v___f_4355_, v_a_4370_, v_a_3741_, v_a_3742_);
lean_dec_ref(v_val_4354_);
v___y_4209_ = v___x_4331_;
v___y_4210_ = v_a_4237_;
v___y_4211_ = v___x_4371_;
goto v___jp_4208_;
}
else
{
lean_object* v_a_4372_; 
lean_dec_ref(v___f_4355_);
lean_dec_ref(v_val_4354_);
v_a_4372_ = lean_ctor_get(v___x_4369_, 0);
lean_inc(v_a_4372_);
lean_dec_ref_known(v___x_4369_, 1);
v___y_4204_ = v___x_4331_;
v___y_4205_ = v_a_4237_;
v_a_4206_ = v_a_4372_;
goto v___jp_4203_;
}
}
}
}
else
{
lean_dec(v___x_4356_);
lean_dec_ref(v_val_4354_);
v___y_4229_ = v___f_4355_;
v___y_4230_ = v___x_4351_;
v___y_4231_ = v___x_4331_;
v___y_4232_ = v_a_4237_;
goto v___jp_4228_;
}
}
case 1:
{
lean_object* v_val_4373_; lean_object* v___x_4374_; 
lean_del_object(v___x_4239_);
v_val_4373_ = lean_ctor_get(v_decl_3739_, 0);
lean_inc_ref(v_val_4373_);
lean_dec_ref_known(v_decl_3739_, 1);
v___x_4374_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(v___f_4353_, v_forceExpose_3740_, v___x_4351_, v_cls_3916_, v_val_4373_, v_a_3741_, v_a_3742_);
v___y_4209_ = v___x_4331_;
v___y_4210_ = v_a_4237_;
v___y_4211_ = v___x_4374_;
goto v___jp_4208_;
}
case 5:
{
lean_object* v_defns_4375_; 
lean_del_object(v___x_4239_);
v_defns_4375_ = lean_ctor_get(v_decl_3739_, 0);
if (lean_obj_tag(v_defns_4375_) == 1)
{
lean_object* v_tail_4376_; 
v_tail_4376_ = lean_ctor_get(v_defns_4375_, 1);
if (lean_obj_tag(v_tail_4376_) == 0)
{
lean_object* v_head_4377_; lean_object* v___x_4378_; 
lean_inc_ref(v_defns_4375_);
lean_dec_ref_known(v_decl_3739_, 1);
v_head_4377_ = lean_ctor_get(v_defns_4375_, 0);
lean_inc(v_head_4377_);
lean_dec_ref_known(v_defns_4375_, 2);
v___x_4378_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(v___f_4353_, v_forceExpose_3740_, v___x_4351_, v_cls_3916_, v_head_4377_, v_a_3741_, v_a_3742_);
v___y_4209_ = v___x_4331_;
v___y_4210_ = v_a_4237_;
v___y_4211_ = v___x_4378_;
goto v___jp_4208_;
}
else
{
lean_object* v___x_4379_; 
lean_dec_ref(v___f_4353_);
lean_inc_ref(v_decl_3739_);
v___x_4379_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3739_, v_cls_3916_, v_decl_3739_, v_a_3741_, v_a_3742_);
lean_dec_ref_known(v_decl_3739_, 1);
v___y_4209_ = v___x_4331_;
v___y_4210_ = v_a_4237_;
v___y_4211_ = v___x_4379_;
goto v___jp_4208_;
}
}
else
{
lean_object* v___x_4380_; 
lean_dec_ref(v___f_4353_);
lean_inc_ref(v_decl_3739_);
v___x_4380_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3739_, v_cls_3916_, v_decl_3739_, v_a_3741_, v_a_3742_);
lean_dec_ref_known(v_decl_3739_, 1);
v___y_4209_ = v___x_4331_;
v___y_4210_ = v_a_4237_;
v___y_4211_ = v___x_4380_;
goto v___jp_4208_;
}
}
case 3:
{
lean_object* v_val_4381_; lean_object* v___f_4382_; lean_object* v___x_4383_; lean_object* v_env_4384_; lean_object* v___x_4385_; 
lean_del_object(v___x_4239_);
v_val_4381_ = lean_ctor_get(v_decl_3739_, 0);
lean_inc_ref_n(v_val_4381_, 2);
lean_dec_ref_known(v_decl_3739_, 1);
v___f_4382_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed), 7, 2);
lean_closure_set(v___f_4382_, 0, v_val_4381_);
lean_closure_set(v___f_4382_, 1, v___f_4353_);
v___x_4383_ = lean_st_ref_get(v_a_3742_);
v_env_4384_ = lean_ctor_get(v___x_4383_, 0);
lean_inc_ref(v_env_4384_);
lean_dec(v___x_4383_);
v___x_4385_ = lean_st_ref_get(v_a_3742_);
if (v_forceExpose_3740_ == 0)
{
lean_object* v_env_4386_; lean_object* v___x_4387_; uint8_t v_isModule_4388_; 
v_env_4386_ = lean_ctor_get(v___x_4385_, 0);
lean_inc_ref(v_env_4386_);
lean_dec(v___x_4385_);
v___x_4387_ = l_Lean_Environment_header(v_env_4384_);
lean_dec_ref(v_env_4384_);
v_isModule_4388_ = lean_ctor_get_uint8(v___x_4387_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4387_);
if (v_isModule_4388_ == 0)
{
lean_dec_ref(v_env_4386_);
lean_dec_ref(v_val_4381_);
v___y_4222_ = v___x_4351_;
v___y_4223_ = v___x_4331_;
v___y_4224_ = v___f_4382_;
v___y_4225_ = v_a_4237_;
goto v___jp_4221_;
}
else
{
uint8_t v_isExporting_4389_; 
v_isExporting_4389_ = lean_ctor_get_uint8(v_env_4386_, sizeof(void*)*13);
lean_dec_ref(v_env_4386_);
if (v_isExporting_4389_ == 0)
{
if (v___x_4143_ == 0)
{
lean_object* v___x_4390_; lean_object* v___x_4391_; 
v___x_4390_ = lean_box(0);
v___x_4391_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_4381_, v___f_4382_, v___x_4390_, v_a_3741_, v_a_3742_);
lean_dec_ref(v_val_4381_);
v___y_4209_ = v___x_4331_;
v___y_4210_ = v_a_4237_;
v___y_4211_ = v___x_4391_;
goto v___jp_4208_;
}
else
{
lean_object* v_toConstantVal_4392_; lean_object* v_name_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; 
v_toConstantVal_4392_ = lean_ctor_get(v_val_4381_, 0);
v_name_4393_ = lean_ctor_get(v_toConstantVal_4392_, 0);
v___x_4394_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4393_);
v___x_4395_ = l_Lean_MessageData_ofName(v_name_4393_);
v___x_4396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4396_, 0, v___x_4394_);
lean_ctor_set(v___x_4396_, 1, v___x_4395_);
v___x_4397_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4398_, 0, v___x_4396_);
lean_ctor_set(v___x_4398_, 1, v___x_4397_);
v___x_4399_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3916_, v___x_4398_, v_a_3741_, v_a_3742_);
if (lean_obj_tag(v___x_4399_) == 0)
{
lean_object* v_a_4400_; lean_object* v___x_4401_; 
v_a_4400_ = lean_ctor_get(v___x_4399_, 0);
lean_inc(v_a_4400_);
lean_dec_ref_known(v___x_4399_, 1);
v___x_4401_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_4381_, v___f_4382_, v_a_4400_, v_a_3741_, v_a_3742_);
lean_dec_ref(v_val_4381_);
v___y_4209_ = v___x_4331_;
v___y_4210_ = v_a_4237_;
v___y_4211_ = v___x_4401_;
goto v___jp_4208_;
}
else
{
lean_object* v_a_4402_; 
lean_dec_ref(v___f_4382_);
lean_dec_ref(v_val_4381_);
v_a_4402_ = lean_ctor_get(v___x_4399_, 0);
lean_inc(v_a_4402_);
lean_dec_ref_known(v___x_4399_, 1);
v___y_4204_ = v___x_4331_;
v___y_4205_ = v_a_4237_;
v_a_4206_ = v_a_4402_;
goto v___jp_4203_;
}
}
}
else
{
lean_dec_ref(v_val_4381_);
v___y_4222_ = v___x_4351_;
v___y_4223_ = v___x_4331_;
v___y_4224_ = v___f_4382_;
v___y_4225_ = v_a_4237_;
goto v___jp_4221_;
}
}
}
else
{
lean_dec(v___x_4385_);
lean_dec_ref(v_env_4384_);
lean_dec_ref(v_val_4381_);
v___y_4222_ = v___x_4351_;
v___y_4223_ = v___x_4331_;
v___y_4224_ = v___f_4382_;
v___y_4225_ = v_a_4237_;
goto v___jp_4221_;
}
}
case 0:
{
lean_object* v_val_4403_; lean_object* v_toConstantVal_4404_; lean_object* v_name_4405_; lean_object* v___x_4407_; 
lean_dec_ref(v___f_4353_);
v_val_4403_ = lean_ctor_get(v_decl_3739_, 0);
v_toConstantVal_4404_ = lean_ctor_get(v_val_4403_, 0);
v_name_4405_ = lean_ctor_get(v_toConstantVal_4404_, 0);
lean_inc_ref(v_val_4403_);
if (v_isShared_4240_ == 0)
{
lean_ctor_set(v___x_4239_, 0, v_val_4403_);
v___x_4407_ = v___x_4239_;
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
v___x_4412_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(v_decl_3739_, v___x_4242_, v_cls_3916_, v___x_4347_, v___x_4351_, v___x_4411_, v___x_4351_, v_a_3741_, v_a_3742_);
v___y_4209_ = v___x_4331_;
v___y_4210_ = v_a_4237_;
v___y_4211_ = v___x_4412_;
goto v___jp_4208_;
}
}
default: 
{
lean_object* v___x_4414_; 
lean_dec_ref(v___f_4353_);
lean_del_object(v___x_4239_);
lean_inc(v_decl_3739_);
v___x_4414_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3739_, v_cls_3916_, v_decl_3739_, v_a_3741_, v_a_3742_);
lean_dec(v_decl_3739_);
v___y_4209_ = v___x_4331_;
v___y_4210_ = v_a_4237_;
v___y_4211_ = v___x_4414_;
goto v___jp_4208_;
}
}
}
}
}
}
}
}
v___jp_3744_:
{
lean_object* v___x_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
v___x_3748_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3746_, v___y_3745_);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3748_);
if (v_isSharedCheck_3755_ == 0)
{
lean_object* v_unused_3756_; 
v_unused_3756_ = lean_ctor_get(v___x_3748_, 0);
lean_dec(v_unused_3756_);
v___x_3750_ = v___x_3748_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_dec(v___x_3748_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
lean_ctor_set_tag(v___x_3750_, 1);
lean_ctor_set(v___x_3750_, 0, v_a_3747_);
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3747_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
v___jp_3757_:
{
lean_object* v___x_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
v___x_3761_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3758_, v___y_3759_);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3768_ == 0)
{
lean_object* v_unused_3769_; 
v_unused_3769_ = lean_ctor_get(v___x_3761_, 0);
lean_dec(v_unused_3769_);
v___x_3763_ = v___x_3761_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_dec(v___x_3761_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
lean_ctor_set_tag(v___x_3763_, 1);
lean_ctor_set(v___x_3763_, 0, v_a_3760_);
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3760_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
v___jp_3774_:
{
lean_object* v___x_3787_; 
lean_inc_ref(v___y_3784_);
v___x_3787_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3776_, v___y_3784_, v___y_3783_, v___y_3786_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_object* v___x_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3843_; 
lean_dec_ref_known(v___x_3787_, 1);
lean_dec(v___y_3778_);
lean_inc_ref(v___y_3775_);
v___x_3788_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3775_, v___y_3782_);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3843_ == 0)
{
lean_object* v_unused_3844_; 
v_unused_3844_ = lean_ctor_get(v___x_3788_, 0);
lean_dec(v_unused_3844_);
v___x_3790_ = v___x_3788_;
v_isShared_3791_ = v_isSharedCheck_3843_;
goto v_resetjp_3789_;
}
else
{
lean_dec(v___x_3788_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3843_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3792_; lean_object* v___x_3793_; uint8_t v___x_3794_; 
v___x_3792_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3785_);
v___x_3793_ = l_Lean_Elab_async;
v___x_3794_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_3792_, v___x_3793_);
lean_dec_ref(v___x_3792_);
if (v___x_3794_ == 0)
{
lean_object* v___x_3795_; lean_object* v_r_3796_; 
lean_del_object(v___x_3790_);
lean_dec_ref(v___y_3781_);
lean_dec_ref(v___y_3777_);
v___x_3795_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3784_, v___y_3782_);
lean_dec_ref(v___x_3795_);
v_r_3796_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3739_, v___y_3785_, v___y_3782_);
if (lean_obj_tag(v_r_3796_) == 0)
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3815_; 
v_a_3797_ = lean_ctor_get(v_r_3796_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v_r_3796_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3799_ = v_r_3796_;
v_isShared_3800_ = v_isSharedCheck_3815_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v_r_3796_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3815_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
lean_inc(v_a_3797_);
if (v_isShared_3800_ == 0)
{
lean_ctor_set_tag(v___x_3799_, 1);
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3797_);
v___x_3802_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
lean_object* v___x_3803_; 
v___x_3803_ = lean_apply_2(v___y_3779_, v___x_3802_, lean_box(0));
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v___x_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3811_; 
lean_dec_ref_known(v___x_3803_, 1);
v___x_3804_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3775_, v___y_3782_);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3811_ == 0)
{
lean_object* v_unused_3812_; 
v_unused_3812_ = lean_ctor_get(v___x_3804_, 0);
lean_dec(v_unused_3812_);
v___x_3806_ = v___x_3804_;
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
else
{
lean_dec(v___x_3804_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3809_; 
if (v_isShared_3807_ == 0)
{
lean_ctor_set(v___x_3806_, 0, v_a_3797_);
v___x_3809_ = v___x_3806_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_a_3797_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
}
else
{
lean_object* v_a_3813_; 
lean_dec(v_a_3797_);
v_a_3813_ = lean_ctor_get(v___x_3803_, 0);
lean_inc(v_a_3813_);
lean_dec_ref_known(v___x_3803_, 1);
v___y_3758_ = v___y_3775_;
v___y_3759_ = v___y_3782_;
v_a_3760_ = v_a_3813_;
goto v___jp_3757_;
}
}
}
}
else
{
lean_object* v_a_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; 
v_a_3816_ = lean_ctor_get(v_r_3796_, 0);
lean_inc(v_a_3816_);
lean_dec_ref_known(v_r_3796_, 1);
v___x_3817_ = lean_box(0);
v___x_3818_ = lean_apply_2(v___y_3779_, v___x_3817_, lean_box(0));
if (lean_obj_tag(v___x_3818_) == 0)
{
lean_dec_ref_known(v___x_3818_, 1);
v___y_3758_ = v___y_3775_;
v___y_3759_ = v___y_3782_;
v_a_3760_ = v_a_3816_;
goto v___jp_3757_;
}
else
{
lean_object* v_a_3819_; 
lean_dec(v_a_3816_);
v_a_3819_ = lean_ctor_get(v___x_3818_, 0);
lean_inc(v_a_3819_);
lean_dec_ref_known(v___x_3818_, 1);
v___y_3758_ = v___y_3775_;
v___y_3759_ = v___y_3782_;
v_a_3760_ = v_a_3819_;
goto v___jp_3757_;
}
}
}
else
{
lean_object* v___x_3820_; lean_object* v___x_3822_; 
lean_dec_ref(v___y_3784_);
lean_dec_ref(v___y_3779_);
lean_dec_ref(v___y_3775_);
lean_dec(v_decl_3739_);
v___x_3820_ = l_IO_CancelToken_new();
if (v_isShared_3791_ == 0)
{
lean_ctor_set_tag(v___x_3790_, 1);
lean_ctor_set(v___x_3790_, 0, v___x_3820_);
v___x_3822_ = v___x_3790_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v___x_3820_);
v___x_3822_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; 
v___x_3823_ = lean_unsigned_to_nat(0u);
v___x_3824_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_3825_ = l_Lean_Name_toString(v___x_3824_, v___y_3780_);
lean_inc_ref(v___x_3822_);
v___x_3826_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3781_, v___x_3822_, v___x_3825_, v___y_3785_, v___y_3782_);
if (lean_obj_tag(v___x_3826_) == 0)
{
lean_object* v_a_3827_; lean_object* v_checked_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; 
v_a_3827_ = lean_ctor_get(v___x_3826_, 0);
lean_inc(v_a_3827_);
lean_dec_ref_known(v___x_3826_, 1);
v_checked_3828_ = lean_ctor_get(v___y_3777_, 2);
lean_inc_ref(v_checked_3828_);
lean_dec_ref(v___y_3777_);
v___x_3829_ = lean_io_map_task(v_a_3827_, v_checked_3828_, v___x_3823_, v_hasTrace_3773_);
v___x_3830_ = lean_box(0);
v___x_3831_ = lean_box(2);
v___x_3832_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3830_);
lean_ctor_set(v___x_3832_, 1, v___x_3831_);
lean_ctor_set(v___x_3832_, 2, v___x_3822_);
lean_ctor_set(v___x_3832_, 3, v___x_3829_);
v___x_3833_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3832_, v___y_3782_);
return v___x_3833_;
}
else
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3841_; 
lean_dec_ref(v___x_3822_);
lean_dec_ref(v___y_3777_);
v_a_3834_ = lean_ctor_get(v___x_3826_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3826_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3836_ = v___x_3826_;
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3826_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
if (v_isShared_3837_ == 0)
{
v___x_3839_ = v___x_3836_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3834_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3856_; 
lean_dec_ref(v___y_3784_);
lean_dec_ref(v___y_3781_);
lean_dec_ref(v___y_3779_);
lean_dec_ref(v___y_3777_);
lean_dec_ref(v___y_3775_);
lean_dec(v_decl_3739_);
v_a_3845_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3847_ = v___x_3787_;
v_isShared_3848_ = v_isSharedCheck_3856_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3787_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3856_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3854_; 
v___x_3849_ = lean_io_error_to_string(v_a_3845_);
v___x_3850_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3849_);
v___x_3851_ = l_Lean_MessageData_ofFormat(v___x_3850_);
v___x_3852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3852_, 0, v___y_3778_);
lean_ctor_set(v___x_3852_, 1, v___x_3851_);
if (v_isShared_3848_ == 0)
{
lean_ctor_set(v___x_3847_, 0, v___x_3852_);
v___x_3854_ = v___x_3847_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v___x_3852_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
}
v___jp_3857_:
{
lean_object* v_ref_3866_; uint8_t v___x_3867_; lean_object* v___x_3868_; 
v_ref_3866_ = lean_ctor_get(v___y_3863_, 2);
v___x_3867_ = 1;
lean_inc_ref(v___y_3864_);
v___x_3868_ = l_Lean_Environment_addConstAsync(v___y_3864_, v___y_3860_, v___y_3858_, v___y_3865_, v_hasTrace_3773_, v___x_3867_);
if (lean_obj_tag(v___x_3868_) == 0)
{
lean_object* v_a_3869_; lean_object* v_mainEnv_3870_; lean_object* v_asyncEnv_3871_; lean_object* v___f_3872_; lean_object* v___f_3873_; lean_object* v___x_3874_; 
v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
lean_inc_n(v_a_3869_, 3);
lean_dec_ref_known(v___x_3868_, 1);
v_mainEnv_3870_ = lean_ctor_get(v_a_3869_, 0);
lean_inc_ref(v_mainEnv_3870_);
v_asyncEnv_3871_ = lean_ctor_get(v_a_3869_, 1);
lean_inc_ref_n(v_asyncEnv_3871_, 2);
lean_inc(v_ref_3866_);
lean_inc(v___y_3861_);
v___f_3872_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3872_, 0, v___y_3861_);
lean_closure_set(v___f_3872_, 1, v_a_3869_);
lean_closure_set(v___f_3872_, 2, v_ref_3866_);
lean_inc(v_decl_3739_);
v___f_3873_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3873_, 0, v_a_3869_);
lean_closure_set(v___f_3873_, 1, v_asyncEnv_3871_);
lean_closure_set(v___f_3873_, 2, v_decl_3739_);
v___x_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3874_, 0, v___y_3859_);
if (lean_obj_tag(v___y_3862_) == 0)
{
lean_inc_ref(v___x_3874_);
lean_inc(v_ref_3866_);
v___y_3775_ = v_mainEnv_3870_;
v___y_3776_ = v_a_3869_;
v___y_3777_ = v___y_3864_;
v___y_3778_ = v_ref_3866_;
v___y_3779_ = v___f_3872_;
v___y_3780_ = v___x_3867_;
v___y_3781_ = v___f_3873_;
v___y_3782_ = v___y_3861_;
v___y_3783_ = v___x_3874_;
v___y_3784_ = v_asyncEnv_3871_;
v___y_3785_ = v___y_3863_;
v___y_3786_ = v___x_3874_;
goto v___jp_3774_;
}
else
{
lean_inc(v_ref_3866_);
v___y_3775_ = v_mainEnv_3870_;
v___y_3776_ = v_a_3869_;
v___y_3777_ = v___y_3864_;
v___y_3778_ = v_ref_3866_;
v___y_3779_ = v___f_3872_;
v___y_3780_ = v___x_3867_;
v___y_3781_ = v___f_3873_;
v___y_3782_ = v___y_3861_;
v___y_3783_ = v___x_3874_;
v___y_3784_ = v_asyncEnv_3871_;
v___y_3785_ = v___y_3863_;
v___y_3786_ = v___y_3862_;
goto v___jp_3774_;
}
}
else
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3886_; 
lean_dec_ref(v___y_3864_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3859_);
lean_dec(v_decl_3739_);
v_a_3875_ = lean_ctor_get(v___x_3868_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v___x_3868_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3877_ = v___x_3868_;
v_isShared_3878_ = v_isSharedCheck_3886_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v___x_3868_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3886_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3884_; 
v___x_3879_ = lean_io_error_to_string(v_a_3875_);
v___x_3880_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3879_);
v___x_3881_ = l_Lean_MessageData_ofFormat(v___x_3880_);
lean_inc(v_ref_3866_);
v___x_3882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3882_, 0, v_ref_3866_);
lean_ctor_set(v___x_3882_, 1, v___x_3881_);
if (v_isShared_3878_ == 0)
{
lean_ctor_set(v___x_3877_, 0, v___x_3882_);
v___x_3884_ = v___x_3877_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v___x_3882_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
}
v___jp_3887_:
{
lean_object* v___x_3894_; 
v___x_3894_ = lean_st_ref_get(v___y_3893_);
if (lean_obj_tag(v_exportedInfo_x3f_3891_) == 0)
{
lean_object* v_env_3895_; lean_object* v___x_3896_; 
v_env_3895_ = lean_ctor_get(v___x_3894_, 0);
lean_inc_ref(v_env_3895_);
lean_dec(v___x_3894_);
v___x_3896_ = lean_box(0);
v___y_3858_ = v___y_3890_;
v___y_3859_ = v___y_3888_;
v___y_3860_ = v___y_3889_;
v___y_3861_ = v___y_3893_;
v___y_3862_ = v_exportedInfo_x3f_3891_;
v___y_3863_ = v___y_3892_;
v___y_3864_ = v_env_3895_;
v___y_3865_ = v___x_3896_;
goto v___jp_3857_;
}
else
{
lean_object* v_env_3897_; lean_object* v_val_3898_; uint8_t v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
v_env_3897_ = lean_ctor_get(v___x_3894_, 0);
lean_inc_ref(v_env_3897_);
lean_dec(v___x_3894_);
v_val_3898_ = lean_ctor_get(v_exportedInfo_x3f_3891_, 0);
v___x_3899_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3898_);
v___x_3900_ = lean_box(v___x_3899_);
v___x_3901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3900_);
v___y_3858_ = v___y_3890_;
v___y_3859_ = v___y_3888_;
v___y_3860_ = v___y_3889_;
v___y_3861_ = v___y_3893_;
v___y_3862_ = v_exportedInfo_x3f_3891_;
v___y_3863_ = v___y_3892_;
v___y_3864_ = v_env_3897_;
v___y_3865_ = v___x_3901_;
goto v___jp_3857_;
}
}
v___jp_3902_:
{
lean_object* v___x_3908_; 
lean_inc_ref(v___y_3903_);
v___x_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3908_, 0, v___y_3903_);
v___y_3888_ = v___y_3903_;
v___y_3889_ = v___y_3905_;
v___y_3890_ = v___y_3904_;
v_exportedInfo_x3f_3891_ = v___x_3908_;
v___y_3892_ = v___y_3906_;
v___y_3893_ = v___y_3907_;
goto v___jp_3887_;
}
v___jp_3909_:
{
lean_object* v___x_3915_; 
lean_inc_ref(v___y_3910_);
v___x_3915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3915_, 0, v___y_3910_);
v___y_3888_ = v___y_3910_;
v___y_3889_ = v___y_3912_;
v___y_3890_ = v___y_3911_;
v_exportedInfo_x3f_3891_ = v___x_3915_;
v___y_3892_ = v___y_3913_;
v___y_3893_ = v___y_3914_;
goto v___jp_3887_;
}
v___jp_3917_:
{
lean_object* v___x_3922_; uint8_t v___x_3923_; 
v___x_3922_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_3923_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3920_, v_options_3919_, v___x_3922_);
if (v___x_3923_ == 0)
{
lean_object* v___x_3924_; 
v___x_3924_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3739_, v___y_3918_, v___y_3921_);
return v___x_3924_;
}
else
{
lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3925_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
v___x_3926_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3916_, v___x_3925_, v___y_3918_, v___y_3921_);
if (lean_obj_tag(v___x_3926_) == 0)
{
lean_object* v___x_3927_; 
lean_dec_ref_known(v___x_3926_, 1);
v___x_3927_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3739_, v___y_3918_, v___y_3921_);
return v___x_3927_;
}
else
{
lean_dec(v_decl_3739_);
return v___x_3926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___boxed(lean_object* v_decl_4788_, lean_object* v_forceExpose_4789_, lean_object* v_a_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_){
_start:
{
uint8_t v_forceExpose_boxed_4793_; lean_object* v_res_4794_; 
v_forceExpose_boxed_4793_ = lean_unbox(v_forceExpose_4789_);
v_res_4794_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4788_, v_forceExpose_boxed_4793_, v_a_4790_, v_a_4791_);
lean_dec(v_a_4791_);
lean_dec_ref(v_a_4790_);
return v_res_4794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(lean_object* v_opt_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_){
_start:
{
lean_object* v___x_4799_; 
v___x_4799_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_4795_, v___y_4796_);
return v___x_4799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___boxed(lean_object* v_opt_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_){
_start:
{
lean_object* v_res_4804_; 
v_res_4804_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(v_opt_4800_, v___y_4801_, v___y_4802_);
lean_dec(v___y_4802_);
lean_dec_ref(v___y_4801_);
lean_dec_ref(v_opt_4800_);
return v_res_4804_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0(lean_object* v_x_4805_, lean_object* v_x_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_){
_start:
{
if (lean_obj_tag(v_x_4805_) == 0)
{
lean_object* v___x_4810_; lean_object* v___x_4811_; 
v___x_4810_ = l_List_reverse___redArg(v_x_4806_);
v___x_4811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4811_, 0, v___x_4810_);
return v___x_4811_;
}
else
{
lean_object* v_head_4812_; lean_object* v_tail_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4831_; 
v_head_4812_ = lean_ctor_get(v_x_4805_, 0);
v_tail_4813_ = lean_ctor_get(v_x_4805_, 1);
v_isSharedCheck_4831_ = !lean_is_exclusive(v_x_4805_);
if (v_isSharedCheck_4831_ == 0)
{
v___x_4815_ = v_x_4805_;
v_isShared_4816_ = v_isSharedCheck_4831_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_tail_4813_);
lean_inc(v_head_4812_);
lean_dec(v_x_4805_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4831_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
lean_object* v___x_4817_; 
v___x_4817_ = l_Lean_snapshotEnvLinterOptions(v_head_4812_, v___y_4807_, v___y_4808_);
if (lean_obj_tag(v___x_4817_) == 0)
{
lean_object* v_a_4818_; lean_object* v___x_4820_; 
v_a_4818_ = lean_ctor_get(v___x_4817_, 0);
lean_inc(v_a_4818_);
lean_dec_ref_known(v___x_4817_, 1);
if (v_isShared_4816_ == 0)
{
lean_ctor_set(v___x_4815_, 1, v_x_4806_);
lean_ctor_set(v___x_4815_, 0, v_a_4818_);
v___x_4820_ = v___x_4815_;
goto v_reusejp_4819_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v_a_4818_);
lean_ctor_set(v_reuseFailAlloc_4822_, 1, v_x_4806_);
v___x_4820_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4819_;
}
v_reusejp_4819_:
{
v_x_4805_ = v_tail_4813_;
v_x_4806_ = v___x_4820_;
goto _start;
}
}
else
{
lean_object* v_a_4823_; lean_object* v___x_4825_; uint8_t v_isShared_4826_; uint8_t v_isSharedCheck_4830_; 
lean_del_object(v___x_4815_);
lean_dec(v_tail_4813_);
lean_dec(v_x_4806_);
v_a_4823_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4830_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4830_ == 0)
{
v___x_4825_ = v___x_4817_;
v_isShared_4826_ = v_isSharedCheck_4830_;
goto v_resetjp_4824_;
}
else
{
lean_inc(v_a_4823_);
lean_dec(v___x_4817_);
v___x_4825_ = lean_box(0);
v_isShared_4826_ = v_isSharedCheck_4830_;
goto v_resetjp_4824_;
}
v_resetjp_4824_:
{
lean_object* v___x_4828_; 
if (v_isShared_4826_ == 0)
{
v___x_4828_ = v___x_4825_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4829_; 
v_reuseFailAlloc_4829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4829_, 0, v_a_4823_);
v___x_4828_ = v_reuseFailAlloc_4829_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
return v___x_4828_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0___boxed(lean_object* v_x_4832_, lean_object* v_x_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_){
_start:
{
lean_object* v_res_4837_; 
v_res_4837_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v_x_4832_, v_x_4833_, v___y_4834_, v___y_4835_);
lean_dec(v___y_4835_);
lean_dec_ref(v___y_4834_);
return v_res_4837_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object* v_decl_4838_, uint8_t v_forceExpose_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_){
_start:
{
lean_object* v___x_4843_; 
lean_inc(v_decl_4838_);
v___x_4843_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4838_, v_forceExpose_4839_, v_a_4840_, v_a_4841_);
if (lean_obj_tag(v___x_4843_) == 0)
{
lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; 
lean_dec_ref_known(v___x_4843_, 1);
v___x_4844_ = l_Lean_Declaration_getTopLevelNames(v_decl_4838_);
v___x_4845_ = lean_box(0);
v___x_4846_ = lean_box(0);
v___x_4847_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v___x_4844_, v___x_4845_, v_a_4840_, v_a_4841_);
if (lean_obj_tag(v___x_4847_) == 0)
{
lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4854_; 
v_isSharedCheck_4854_ = !lean_is_exclusive(v___x_4847_);
if (v_isSharedCheck_4854_ == 0)
{
lean_object* v_unused_4855_; 
v_unused_4855_ = lean_ctor_get(v___x_4847_, 0);
lean_dec(v_unused_4855_);
v___x_4849_ = v___x_4847_;
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
else
{
lean_dec(v___x_4847_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v___x_4852_; 
if (v_isShared_4850_ == 0)
{
lean_ctor_set(v___x_4849_, 0, v___x_4846_);
v___x_4852_ = v___x_4849_;
goto v_reusejp_4851_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v___x_4846_);
v___x_4852_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4851_;
}
v_reusejp_4851_:
{
return v___x_4852_;
}
}
}
else
{
lean_object* v_a_4856_; lean_object* v___x_4858_; uint8_t v_isShared_4859_; uint8_t v_isSharedCheck_4863_; 
v_a_4856_ = lean_ctor_get(v___x_4847_, 0);
v_isSharedCheck_4863_ = !lean_is_exclusive(v___x_4847_);
if (v_isSharedCheck_4863_ == 0)
{
v___x_4858_ = v___x_4847_;
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
else
{
lean_inc(v_a_4856_);
lean_dec(v___x_4847_);
v___x_4858_ = lean_box(0);
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
v_resetjp_4857_:
{
lean_object* v___x_4861_; 
if (v_isShared_4859_ == 0)
{
v___x_4861_ = v___x_4858_;
goto v_reusejp_4860_;
}
else
{
lean_object* v_reuseFailAlloc_4862_; 
v_reuseFailAlloc_4862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4862_, 0, v_a_4856_);
v___x_4861_ = v_reuseFailAlloc_4862_;
goto v_reusejp_4860_;
}
v_reusejp_4860_:
{
return v___x_4861_;
}
}
}
}
else
{
lean_dec(v_decl_4838_);
return v___x_4843_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___boxed(lean_object* v_decl_4864_, lean_object* v_forceExpose_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_){
_start:
{
uint8_t v_forceExpose_boxed_4869_; lean_object* v_res_4870_; 
v_forceExpose_boxed_4869_ = lean_unbox(v_forceExpose_4865_);
v_res_4870_ = l_Lean_addDecl(v_decl_4864_, v_forceExpose_boxed_4869_, v_a_4866_, v_a_4867_);
lean_dec(v_a_4867_);
lean_dec_ref(v_a_4866_);
return v_res_4870_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(lean_object* v_as_x27_4871_, lean_object* v_b_4872_, lean_object* v___y_4873_){
_start:
{
if (lean_obj_tag(v_as_x27_4871_) == 0)
{
lean_object* v___x_4875_; 
v___x_4875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4875_, 0, v_b_4872_);
return v___x_4875_;
}
else
{
lean_object* v_head_4876_; lean_object* v_tail_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v_env_4880_; lean_object* v_nextMacroScope_4881_; lean_object* v_ngen_4882_; lean_object* v_auxDeclNGen_4883_; lean_object* v_traceState_4884_; lean_object* v_recordedDeps_4885_; lean_object* v_messages_4886_; lean_object* v_infoState_4887_; lean_object* v_snapshotTasks_4888_; lean_object* v___x_4890_; uint8_t v_isShared_4891_; uint8_t v_isSharedCheck_4899_; 
v_head_4876_ = lean_ctor_get(v_as_x27_4871_, 0);
v_tail_4877_ = lean_ctor_get(v_as_x27_4871_, 1);
v___x_4878_ = lean_box(0);
v___x_4879_ = lean_st_ref_take(v___y_4873_);
v_env_4880_ = lean_ctor_get(v___x_4879_, 0);
v_nextMacroScope_4881_ = lean_ctor_get(v___x_4879_, 1);
v_ngen_4882_ = lean_ctor_get(v___x_4879_, 2);
v_auxDeclNGen_4883_ = lean_ctor_get(v___x_4879_, 3);
v_traceState_4884_ = lean_ctor_get(v___x_4879_, 4);
v_recordedDeps_4885_ = lean_ctor_get(v___x_4879_, 6);
v_messages_4886_ = lean_ctor_get(v___x_4879_, 7);
v_infoState_4887_ = lean_ctor_get(v___x_4879_, 8);
v_snapshotTasks_4888_ = lean_ctor_get(v___x_4879_, 9);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_4899_ == 0)
{
lean_object* v_unused_4900_; 
v_unused_4900_ = lean_ctor_get(v___x_4879_, 5);
lean_dec(v_unused_4900_);
v___x_4890_ = v___x_4879_;
v_isShared_4891_ = v_isSharedCheck_4899_;
goto v_resetjp_4889_;
}
else
{
lean_inc(v_snapshotTasks_4888_);
lean_inc(v_infoState_4887_);
lean_inc(v_messages_4886_);
lean_inc(v_recordedDeps_4885_);
lean_inc(v_traceState_4884_);
lean_inc(v_auxDeclNGen_4883_);
lean_inc(v_ngen_4882_);
lean_inc(v_nextMacroScope_4881_);
lean_inc(v_env_4880_);
lean_dec(v___x_4879_);
v___x_4890_ = lean_box(0);
v_isShared_4891_ = v_isSharedCheck_4899_;
goto v_resetjp_4889_;
}
v_resetjp_4889_:
{
lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4895_; 
lean_inc(v_head_4876_);
v___x_4892_ = l_Lean_markMeta(v_env_4880_, v_head_4876_);
v___x_4893_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4891_ == 0)
{
lean_ctor_set(v___x_4890_, 5, v___x_4893_);
lean_ctor_set(v___x_4890_, 0, v___x_4892_);
v___x_4895_ = v___x_4890_;
goto v_reusejp_4894_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v___x_4892_);
lean_ctor_set(v_reuseFailAlloc_4898_, 1, v_nextMacroScope_4881_);
lean_ctor_set(v_reuseFailAlloc_4898_, 2, v_ngen_4882_);
lean_ctor_set(v_reuseFailAlloc_4898_, 3, v_auxDeclNGen_4883_);
lean_ctor_set(v_reuseFailAlloc_4898_, 4, v_traceState_4884_);
lean_ctor_set(v_reuseFailAlloc_4898_, 5, v___x_4893_);
lean_ctor_set(v_reuseFailAlloc_4898_, 6, v_recordedDeps_4885_);
lean_ctor_set(v_reuseFailAlloc_4898_, 7, v_messages_4886_);
lean_ctor_set(v_reuseFailAlloc_4898_, 8, v_infoState_4887_);
lean_ctor_set(v_reuseFailAlloc_4898_, 9, v_snapshotTasks_4888_);
v___x_4895_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4894_;
}
v_reusejp_4894_:
{
lean_object* v___x_4896_; 
v___x_4896_ = lean_st_ref_put(v___y_4873_, v___x_4895_);
v_as_x27_4871_ = v_tail_4877_;
v_b_4872_ = v___x_4878_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg___boxed(lean_object* v_as_x27_4901_, lean_object* v_b_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_){
_start:
{
lean_object* v_res_4905_; 
v_res_4905_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_4901_, v_b_4902_, v___y_4903_);
lean_dec(v___y_4903_);
lean_dec(v_as_x27_4901_);
return v_res_4905_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object* v_decl_4906_, uint8_t v_logCompileErrors_4907_, uint8_t v_markMeta_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_){
_start:
{
uint8_t v___x_4912_; lean_object* v___x_4913_; 
v___x_4912_ = 0;
lean_inc(v_decl_4906_);
v___x_4913_ = l_Lean_addDecl(v_decl_4906_, v___x_4912_, v_a_4909_, v_a_4910_);
if (lean_obj_tag(v___x_4913_) == 0)
{
lean_dec_ref_known(v___x_4913_, 1);
if (v_markMeta_4908_ == 0)
{
lean_object* v___x_4914_; 
v___x_4914_ = l_Lean_compileDecl(v_decl_4906_, v_logCompileErrors_4907_, v_a_4909_, v_a_4910_);
return v___x_4914_;
}
else
{
lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; 
lean_inc(v_decl_4906_);
v___x_4915_ = l_Lean_Declaration_getNames(v_decl_4906_);
v___x_4916_ = lean_box(0);
v___x_4917_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v___x_4915_, v___x_4916_, v_a_4910_);
lean_dec(v___x_4915_);
lean_dec_ref(v___x_4917_);
v___x_4918_ = l_Lean_compileDecl(v_decl_4906_, v_logCompileErrors_4907_, v_a_4909_, v_a_4910_);
return v___x_4918_;
}
}
else
{
lean_dec(v_decl_4906_);
return v___x_4913_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___boxed(lean_object* v_decl_4919_, lean_object* v_logCompileErrors_4920_, lean_object* v_markMeta_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_){
_start:
{
uint8_t v_logCompileErrors_boxed_4925_; uint8_t v_markMeta_boxed_4926_; lean_object* v_res_4927_; 
v_logCompileErrors_boxed_4925_ = lean_unbox(v_logCompileErrors_4920_);
v_markMeta_boxed_4926_ = lean_unbox(v_markMeta_4921_);
v_res_4927_ = l_Lean_addAndCompile(v_decl_4919_, v_logCompileErrors_boxed_4925_, v_markMeta_boxed_4926_, v_a_4922_, v_a_4923_);
lean_dec(v_a_4923_);
lean_dec_ref(v_a_4922_);
return v_res_4927_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(lean_object* v_as_4928_, lean_object* v_as_x27_4929_, lean_object* v_b_4930_, lean_object* v_a_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_){
_start:
{
lean_object* v___x_4935_; 
v___x_4935_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_4929_, v_b_4930_, v___y_4933_);
return v___x_4935_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___boxed(lean_object* v_as_4936_, lean_object* v_as_x27_4937_, lean_object* v_b_4938_, lean_object* v_a_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_){
_start:
{
lean_object* v_res_4943_; 
v_res_4943_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(v_as_4936_, v_as_x27_4937_, v_b_4938_, v_a_4939_, v___y_4940_, v___y_4941_);
lean_dec(v___y_4941_);
lean_dec_ref(v___y_4940_);
lean_dec(v_as_x27_4937_);
lean_dec(v_as_4936_);
return v_res_4943_;
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
